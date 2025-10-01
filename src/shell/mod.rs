//! The shell is a collection of wrapper code on top of
//! the kernel to provide risc-v-sim's interface.

use std::path::{Path, PathBuf};

use elf::ElfBytes;
use elf::endian::AnyEndian;
use serde::Serialize;
use thiserror::Error;

use crate::kernel::{
    InstrVal, Instruction, InstructionDecodeError, Kernel, KernelError, KernelStep, MemoryError,
    Program,
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
    #[error("Failed to write segment bytes to {file:?}: {error}")]
    WritingOutputSegment {
        file: PathBuf,
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
    pub err: Option<String>,
}

/// Runs the kernel for `step_count` steps, returning the result.
///
/// The execution will terminate early if the kernel executes
/// [`Instruction::Ebreak`].
///
/// The result is a special struct, which serializes into a machine-friendly
/// shaped JSON.
pub fn run_kernel(kernel: &mut Kernel, step_count: usize) -> RunResult {
    let mut err = None;
    let mut steps = Vec::new();
    for _ in 0..step_count {
        let step = match kernel.step() {
            Ok(x) => x,
            Err(e) => {
                err = Some(e);
                break;
            }
        };

        steps.push(step);
        if matches!(step.instruction, Instruction::Ebreak) {
            break;
        }
    }

    RunResult { steps, err: err.as_ref().map(KernelError::to_string) }
}
