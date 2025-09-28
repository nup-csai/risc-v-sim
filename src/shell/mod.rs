//! The shell is a collection of wrapper code on top of
//! the kernel to provide risc-v-sim's interface.

use std::{
    io::Write,
    path::{Path, PathBuf},
};

use elf::endian::AnyEndian;
use elf::ElfBytes;
use serde::Serialize;
use thiserror::Error;

use crate::kernel::{
    InstrVal, InstructionDecodeError, Kernel, KernelError, KernelStep, Memory, MemoryError,
    MemorySegment, Program, RegVal,
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
    #[error("Failed to write run result: {cause}. Original result: {actual_result:?}")]
    ResultReportError {
        #[source]
        cause: serde_json::Error,
        actual_result: std::result::Result<(), Box<ShellError>>,
    },
}

type Result<T> = std::result::Result<T, ShellError>;

#[derive(Debug, Clone)]
pub struct ProgramInfo {
    pub program: Program,
    pub entry: RegVal,
    pub load_address: RegVal,
}

impl ProgramInfo {
    /// Adds the program to the memory with specified extra
    /// permissions.
    ///
    /// # Errors
    ///
    /// Returns an error if adding the program segment to memory
    /// leads to a memory error. For more information, see
    /// [`Memory::add_segment`].
    pub fn load_into_memory(
        self,
        memory: &mut Memory,
        is_read: bool,
        is_write: bool,
    ) -> std::result::Result<(), MemoryError> {
        let program_bytes = self.program.into_bytes().into_iter().collect();
        memory.add_segment(MemorySegment {
            is_read,
            is_write,
            is_execute: true,
            off: self.load_address,
            mem: program_bytes,
        })
    }
}

/// Reads progra info from an `.elf` file.
///
/// # Errors
///
/// Returns [`ShellError::Load`] if an IO error happens during program load.
/// Returns same errors as [`load_program_from_elf`].
pub fn load_program_from_file(path: impl AsRef<Path>) -> Result<ProgramInfo> {
    let file_data = std::fs::read(path).map_err(ShellError::Load)?;
    load_program_from_elf(&file_data)
}

/// Reads progra info from bytes, that represent an `.elf` file.
/// The elf file must satisfy the following constraints:
/// * The elf file must be for a little-endian architecture
/// * The elf file must have .text section
/// * The .text section offset must be aligned to 4 bytes
/// * The .text section is not compressed
/// * The .text section must contain supported `RiscV` instructions
///
/// # Errors
///
/// Returns an error if `data` doesn't contain valid elf file bytes
/// or the elf file doesn't satisfy the constraints
pub fn load_program_from_elf(data: &[u8]) -> Result<ProgramInfo> {
    let file = ElfBytes::<AnyEndian>::minimal_parse(data).map_err(ShellError::ElfHead)?;

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
    let program =
        Program::from_raw_instructions(raw_stream).map_err(ShellError::InstructionDecoderError)?;

    Ok(ProgramInfo { program, load_address: text_header.sh_addr, entry: file.ehdr.e_entry })
}

/// Status of a kernel run. Contains a trace with an error
/// if one happened during execution.
#[derive(Debug, Serialize)]
pub struct RunResult {
    pub steps: Vec<KernelStep>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub err: Option<String>,
}

/// Runs a kernel for `step_count` steps, writing the trace to `out` together
/// with the status.
///
/// # Errors
///
/// Returns an error if an IO error happens or if an error during kernel stepping happens.
/// If the execution is unfortunate enough to have both kernel and IO error, the two
/// errors are bundled with [`ShellError::ResultReportError`].
pub fn run_kernel(kernel: &mut Kernel, step_count: usize, out: &mut dyn Write) -> Result<()> {
    let mut err = None;
    let mut steps = Vec::new();
    for _ in 0..step_count {
        match kernel.step() {
            Ok(x) => steps.push(x),
            Err(e) => {
                err = Some(e);
                break;
            }
        }
    }

    let result = match err {
        Some(e) => Err(ShellError::KernelError(e)),
        None => Ok(()),
    };
    let write_result = serde_json::to_writer(
        out,
        &RunResult { steps, err: err.as_ref().map(KernelError::to_string) },
    );

    if let Err(cause) = write_result {
        return Err(ShellError::ResultReportError {
            cause,
            actual_result: result.map_err(Box::new),
        });
    }

    result
}
