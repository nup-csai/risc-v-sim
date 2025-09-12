use std::path::{Path, PathBuf};

use elf::endian::AnyEndian;
use elf::ElfBytes;
use thiserror::Error;

use crate::kernel::{
    InstructionDecodeError, InstructionVal, KernelError, Memory, MemoryError, MemorySegment,
    Program, RegisterVal,
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
    #[error("Failed to load segment bytes from {file:?}: {error}")]
    LoadingInputSegment {
        file: PathBuf,
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

#[derive(Debug, Clone)]
pub struct ProgramInfo {
    pub program: Program,
    pub entry: RegisterVal,
    pub load_address: RegisterVal,
}

impl ProgramInfo {
    /// Adds the program to the memory with specified extra
    /// permissions.
    pub fn load_into_memory(
        self,
        memory: &mut Memory,
        is_read: bool,
        is_write: bool,
    ) -> Result<(), MemoryError> {
        let program_bytes = self.program.into_bytes().into_iter().collect();
        memory.add_segment(MemorySegment {
            is_read,
            is_write,
            is_execute: true,
            offset: self.load_address,
            mem: program_bytes,
        })
    }
}

pub fn load_program_from_file(path: impl AsRef<Path>) -> Result<ProgramInfo, ShellError> {
    let file_data = std::fs::read(path).map_err(ShellError::Load)?;
    load_program_from_elf(&file_data)
}

pub fn load_program_from_elf(data: &[u8]) -> Result<ProgramInfo, ShellError> {
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
    if text.len() % 4 != 0 {
        return Err(ShellError::UnalignedText);
    }

    let raw_stream = text
        .chunks(4)
        .map(|x| <[u8; 4]>::try_from(x).unwrap())
        .map(InstructionVal::from_le_bytes);
    let program =
        Program::from_raw_instructions(raw_stream).map_err(ShellError::InstructionDecoderError)?;

    Ok(ProgramInfo {
        program,
        load_address: text_header.sh_addr,
        entry: file.ehdr.e_entry,
    })
}
