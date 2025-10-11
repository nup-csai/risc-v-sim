//! The shell is a collection of wrapper code on top of
//! the kernel to provide risc-v-sim's interface.

use std::{
    io::Read,
    path::{Path, PathBuf},
};

use elf::ElfBytes;
use elf::endian::AnyEndian;
use serde::Serialize;
use thiserror::Error;

use crate::kernel::{
    InstrVal, Instruction, InstructionDecodeError, Kernel, KernelError, KernelStep, Memory,
    MemoryError, MemorySegment, Program, RegVal,
};

#[derive(Debug, Error)]
pub enum ShellError {
    #[error("Failed to load the .elf file: {0}")]
    Load(#[source] std::io::Error),
    #[error("Failed to parse the .elf file: {0}")]
    ElfHead(#[source] elf::ParseError),
    #[error("The .elf file is not little-endian")]
    ElfNotLittleEndian,
    #[error("Failed to parse a section from the .elf file: {0}")]
    ElfSection(#[source] elf::ParseError),
    #[error("The .elf file does not have a .text section")]
    NoText,
    /// This error may happen if the .text section is compressed
    /// and the compression header is malformed.
    #[error("Failed to read .text section data")]
    TextData(#[source] elf::ParseError),
    #[error("Compressed .text is not supported")]
    CompressedText,
    #[error("The .text section is not a multiple of 4")]
    UnalignedText,
    #[error("Failed to decode the .text section: {0}")]
    InstructionDecoderError(#[source] InstructionDecodeError),
    #[error("Failed to load the program into memory: {0}")]
    LoadingProramIntoMemory(#[source] MemoryError),
    #[error("Failed to load segment bytes from {path:?}: {error}")]
    LoadingInputSegment {
        path: PathBuf,
        #[source]
        error: std::io::Error,
    },
    #[error("Failed to add a segment to memory: {0}")]
    AddingSegmentToMemory(#[source] MemoryError),
    #[error("Failed to write segment bytes to {path:?}: {error}")]
    WritingOutputSegment {
        path: PathBuf,
        #[source]
        error: std::io::Error,
    },
    #[error("Kernel error: {0}")]
    KernelError(#[source] KernelError),
}

type Result<T> = std::result::Result<T, ShellError>;

/// Reads a program from an `.elf` file.
///
/// The elf file must satisfy the following constraints:
/// * The elf file must be for a little-endian architecture
/// * The elf file must have .text section
/// * The .text section offset must be aligned to 4 bytes
/// * The .text section is not compressed
/// * The .text section must contain supported `RiscV` instructions
///
/// # Errors
///
/// 1. Returns [`ShellError::Load`] if an IO error happens during program load.
/// 2. Returns an error if `data` doesn't contain valid elf file bytes
///    or the elf file doesn't satisfy the constraints
pub fn load_program_from_file(path: impl AsRef<Path>) -> Result<Program> {
    let elf_bytes = std::fs::read(path).map_err(ShellError::Load)?;
    let file = ElfBytes::<AnyEndian>::minimal_parse(&elf_bytes).map_err(ShellError::ElfHead)?;

    if file.ehdr.endianness != AnyEndian::Little {
        return Err(ShellError::ElfNotLittleEndian);
    }

    let text_header = file
        .section_header_by_name(".text")
        .map_err(ShellError::ElfSection)?
        .ok_or(ShellError::NoText)?;
    let (text, compression_header) = file
        .section_data(&text_header)
        .map_err(ShellError::TextData)?;
    if compression_header.is_some() {
        return Err(ShellError::CompressedText);
    }

    let (chunks, tail) = text.as_chunks::<4>();
    if !tail.is_empty() {
        return Err(ShellError::UnalignedText);
    }

    let raw_stream = chunks.iter().copied().map(InstrVal::from_le_bytes);

    Program::from_raw_instructions(raw_stream, text_header.sh_addr, file.ehdr.e_entry)
        .map_err(ShellError::InstructionDecoderError)
}

/// Status of a kernel run. Contains a trace with an error
/// if one happened during execution.
#[derive(Debug, Serialize)]
pub struct RunResult {
    pub steps: Vec<KernelStep>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub err: Option<RunError>,
}

#[derive(Debug, Serialize)]
pub struct RunError {
    pub msg: String,
    pub detail: KernelError,
}

/// Specification for constructing a memory segment.
#[derive(Debug, Clone)]
pub struct MemorySegmentDef {
    pub off: RegVal,
    pub len: RegVal,
    pub is_read: bool,
    pub is_write: bool,
    pub is_execute: bool,
    pub path: PathBuf,
}

impl MemorySegmentDef {
    /// Construct a segment according to def.
    pub fn to_segment(&self, mem: impl Into<Box<[u8]>>) -> MemorySegment {
        let mem = mem.into();
        assert_eq!(mem.len(), self.len as usize);

        MemorySegment {
            is_read: self.is_read,
            is_write: self.is_write,
            is_execute: self.is_execute,
            off: self.off,
            mem,
        }
    }
}

/// Specification for constructing and running a kernel.
///
/// The specification should be passed to [`run_from_spec()`],
/// however you may also use it to build a kernel.
#[derive(Debug)]
pub struct KernelDef {
    /// The .elf file path to use
    pub elfpath: PathBuf,
    /// The input segments.
    pub inputs: Vec<MemorySegmentDef>,
    /// The output segments.
    pub outputs: Vec<MemorySegmentDef>,
}

impl KernelDef {
    /// Construct a kernel according to the def.
    ///
    /// * Segments declared in `inputs` will be construced from bytes
    ///   specified stored files specified by their `path` field. Extra
    ///   space will be zero-padded.
    /// * Segments declared in `outputs` will be constructed from zeroes
    pub fn build_kernel(&self) -> Result<Kernel> {
        let program = load_program_from_file(&self.elfpath)?;
        let mut kernel = Kernel::from_program(&program);

        for def in &self.inputs {
            let bytes = Self::read_file(&def.path, def.len)?;
            kernel
                .memory
                .add_segment(def.to_segment(bytes))
                .map_err(ShellError::AddingSegmentToMemory)?;
        }

        for def in &self.outputs {
            let bytes = vec![0u8; def.len as usize].into_boxed_slice();
            kernel
                .memory
                .add_segment(def.to_segment(bytes))
                .map_err(ShellError::AddingSegmentToMemory)?;
        }

        Ok(kernel)
    }

    fn read_file(path: &PathBuf, amount: u64) -> Result<Vec<u8>> {
        let make_err =
            |error: std::io::Error| ShellError::LoadingInputSegment { path: path.clone(), error };

        let mut bytes = Vec::with_capacity(amount as usize);
        let file = std::fs::File::open(path).map_err(make_err)?;
        file.take(amount)
            .read_to_end(&mut bytes)
            .map_err(make_err)?;
        Ok(bytes)
    }
}

/// Runs a kernel for `step_count` steps, returning the result.
///
/// The kernel is constructed from [`KernelDef`]. The kernel
/// is run with [`run_kernel()`]. See that function for more information.
///
/// Segments specified in spec's `outputs` field, wil have their bytes
/// written to files specified by their paths.
pub fn run_from_spec(spec: KernelDef, step_count: usize) -> Result<RunResult> {
    let mut kernel = spec.build_kernel()?;
    let run_result = run_kernel(&mut kernel, step_count);

    for def in &spec.outputs {
        let path = def.path.clone();
        let segment = find_segment_for_def(&kernel.memory, def);
        std::fs::write(&path, segment.as_bytes())
            .map_err(|error| ShellError::WritingOutputSegment { path, error })?;
    }

    Ok(run_result)
}

fn find_segment_for_def<'a>(memory: &'a Memory, def: &MemorySegmentDef) -> &'a MemorySegment {
    memory
        .segments()
        .iter()
        .find(|s| s.contains_address(def.off))
        .expect("memory segment disappeared")
}

/// Runs the kernel for `step_count` steps, returning the result.
///
/// The execution will terminate early if the kernel executes
/// [`Instruction::Ebreak`].
///
/// The result is a special struct, which serializes into a machine-friendly
/// shaped JSON.
pub fn run_kernel(kernel: &mut Kernel, step_count: usize) -> RunResult {
    let mut kern_err = None;
    let mut steps = Vec::new();
    for _ in 0..step_count {
        let step = match kernel.step() {
            Ok(x) => x,
            Err(e) => {
                kern_err = Some(e);
                break;
            }
        };

        steps.push(step);
        if matches!(step.instruction, Instruction::Ebreak) {
            break;
        }
    }
    let err = kern_err.map(kernel_error_to_run_error);
    RunResult { steps, err }
}

fn kernel_error_to_run_error(kern_err: KernelError) -> RunError {
    RunError { msg: kern_err.to_string(), detail: kern_err }
}
