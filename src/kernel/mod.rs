pub mod decoder;
pub mod instruction;
pub mod processor;

pub use decoder::*;
pub use instruction::*;
pub use processor::*;
use thiserror::Error;

#[derive(Debug)]
pub struct Kernel {
    program: Program,
    program_offset: u64,
    processor: Processor,
}

impl Kernel {
    pub fn new(program: Program, entry_point: u64, program_offset: u64) -> Self {
        let mut processor = Processor::new();
        processor.pc = entry_point;

        Self {
            program,
            program_offset,
            processor,
        }
    }

    pub fn step(&mut self) -> Result<KernelStep, KernelError> {
        let old_processor = self.processor;
        let instruction = self.fetch_instruction()?;

        instruction
            .execute(&mut self.processor)
            .map_err(|instruction_error| KernelError::InstructionError {
                instruction_address: self.processor.pc,
                instruction_error,
            })?;
        self.processor.pc += 4;

        Ok(KernelStep {
            old_processor,
            instruction,
            new_processor: self.processor,
        })
    }

    fn fetch_instruction(&self) -> Result<Instruction, KernelError> {
        // TODO: handle underflow
        let local_offset = self.processor.pc - self.program_offset;
        let instruction_index = (local_offset / 4) as usize;

        self.program
            .instructions
            .get(instruction_index)
            .map(|x| *x)
            .ok_or(KernelError::FetchOutOfRange(instruction_index))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    instructions: Vec<Instruction>,
}

impl Program {
    pub fn from_instructions(instructions: Vec<Instruction>) -> Self {
        Self { instructions }
    }

    pub fn from_raw_instructions(
        instructions: impl IntoIterator<Item = InstructionVal>,
    ) -> Result<Self, InstructionDecodeError> {
        let instructions = instructions
            .into_iter()
            .enumerate()
            .map(Self::decode_instruction)
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Self::from_instructions(instructions))
    }

    fn decode_instruction(
        (idx, code): (usize, InstructionVal),
    ) -> Result<Instruction, InstructionDecodeError> {
        match decode_instruction(code) {
            Ok(instruction) => Ok(instruction),
            Err(error) => Err(InstructionDecodeError {
                instruction_idx: idx,
                instruction_code: code,
                error,
            }),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Error)]
#[error("Failed to encode instruction {instruction_idx}: {instruction_code:#x} is not a valid instruction")]
pub struct InstructionDecodeError {
    pub instruction_idx: usize,
    pub instruction_code: InstructionVal,
    #[source]
    pub error: DecodeError,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, serde::Serialize)]
pub struct KernelStep {
    pub old_processor: Processor,
    pub new_processor: Processor,
    pub instruction: Instruction,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Error)]
pub enum KernelError {
    #[error("Failed to execute instruction {instruction_address}: {instruction_error}")]
    InstructionError {
        instruction_address: u64,
        instruction_error: InstructionError,
    },
    #[error("Tried to fetch an instruction out of range: {0}")]
    FetchOutOfRange(usize),
}
