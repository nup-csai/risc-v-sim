mod kernel;

use clap::Parser;
use elf::endian::AnyEndian;
use elf::ElfBytes;
use kernel::decode_instruction;
use kernel::Processor;
use kernel::{Instruction, InstructionError};
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
enum RunError {
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
    #[error("Instruction number {instruction_n}: {instruction_val:#x} is not a valid instruction")]
    BadInstruction {
        instruction_n: usize,
        instruction_val: u32,
    },
    #[error("Tried to fetch an instruction out of range: {0}")]
    FetchOutOfRange(usize),
    #[error("Failed to execute instruction {instruction_idx}: {instruction_error}")]
    InstructionError {
        instruction_idx: usize,
        instruction_error: InstructionError,
    },
}

fn main() -> Result<(), RunError> {
    let args = Args::parse();
    let path = std::path::PathBuf::from(args.path);
    let file_data = std::fs::read(path).map_err(RunError::Load)?;
    let slice = file_data.as_slice();
    let file = ElfBytes::<AnyEndian>::minimal_parse(slice).map_err(RunError::ElfHead)?;

    if file.ehdr.endianness != AnyEndian::Little {
        return Err(RunError::ElfNotLittleEndian);
    }

    let text_header = file
        .section_header_by_name(".text")
        .map_err(RunError::ElfSection)?
        .ok_or(RunError::NoText)?;
    let (text, compression_header) = file
        .section_data(&text_header)
        .map_err(RunError::TextData)?;
    if compression_header.is_some() {
        return Err(RunError::CompressedText);
    }
    let program = text
        .chunks(4)
        .enumerate()
        .map(parse_text_chunk)
        .collect::<Result<Vec<_>, _>>()?;

    let text_offset = text_header.sh_addr;
    let start = file.ehdr.e_entry;
    let mut processor = Processor::new();

    println!("text_offset={text_offset}, start={start}");

    processor.pc = start;
    for _ in 0..MAX_STEPS {
        let instruction_idx = instruction_idx(processor.pc, text_offset);
        println!(
            "Fetching at {} (instruction {})",
            processor.pc, instruction_idx
        );

        let instr = program
            .get(instruction_idx)
            .ok_or(RunError::FetchOutOfRange(instruction_idx))?;
        println!("Executing: {instr:?}");

        instr
            .execute(&mut processor)
            .map_err(|instruction_error| RunError::InstructionError {
                instruction_idx,
                instruction_error,
            })?;
        processor.pc += 4;

        println!("New state: {processor:?}");
    }

    Ok(())
}

fn parse_text_chunk((instruction_n, chunk): (usize, &[u8])) -> Result<Instruction, RunError> {
    let instruction_bytes: [u8; 4] = chunk.try_into().map_err(|_| RunError::UnalignedText)?;
    let instruction_val = u32::from_le_bytes(instruction_bytes);

    decode_instruction(instruction_val).ok_or(RunError::BadInstruction {
        instruction_n,
        instruction_val,
    })
}

fn instruction_idx(pc: u64, text_offset: u64) -> usize {
    // TODO: handle underflow
    let local_offset = pc - text_offset;
    (local_offset / 4) as usize
}
