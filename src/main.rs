mod kernel;

use clap::Parser;
use elf::endian::AnyEndian;
use elf::ElfBytes;
use kernel::{InstructionDecodeError, Kernel, KernelError, Program};
use thiserror::Error;

/// MVP of RVsim!
#[derive(Parser, Debug)]
struct Args {
    /// Path to the .elf file
    #[arg(short, long)]
    path: String,
}

const MAX_STEPS: usize = 10;

#[derive(Debug, Error)]
enum ShellError {
    #[error("Failed to load the .elf file")]
    Load(#[source] std::io::Error),
    #[error("Failed to parse the .elf file")]
    ElfHead(#[source] elf::ParseError),
    #[error("The .elf file is not little-endian")]
    ElfNotLittleEndian,
    #[error("Failed to parse a section from the .elf file")]
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
    #[error("Failed to decode the .text section")]
    InstructionDecoderError(#[source] InstructionDecodeError),
    #[error("Kernel error")]
    KernelError(#[source] KernelError),
}

fn main() -> Result<(), ShellError> {
    let args = Args::parse();
    let path = std::path::PathBuf::from(args.path);
    let file_data = std::fs::read(path).map_err(ShellError::Load)?;
    let slice = file_data.as_slice();
    let file = ElfBytes::<AnyEndian>::minimal_parse(slice).map_err(ShellError::ElfHead)?;

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
        .map(u32::from_le_bytes);
    let program =
        Program::from_raw_instructions(raw_stream).map_err(ShellError::InstructionDecoderError)?;

    let mut kernel = Kernel::new(program, file.ehdr.e_entry, text_header.sh_addr);
    for _ in 0..MAX_STEPS {
        match kernel.step() {
            Err(e) => return Err(ShellError::KernelError(e)),
            Ok(s) => println!("{s:?}"),
        }
    }

    Ok(())
}
