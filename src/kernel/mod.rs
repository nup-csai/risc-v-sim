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
    pub const fn new(program: Program, entry_point: u64, program_offset: u64) -> Self {
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
        let old_pc = old_processor.pc;
        let instruction = self.fetch_instruction()?;

        self.processor.pc += 4;
        instruction
            .execute(&mut self.processor, old_pc)
            .map_err(|instruction_error| KernelError::InstructionError {
                instruction_address: self.processor.pc,
                instruction_error,
            })?;

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
    pub const fn from_instructions(instructions: Vec<Instruction>) -> Self {
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

#[cfg(test)]
mod tests {
    use super::{GeneralRegister, Imm, Instruction, InstructionVal, Kernel, Program, RegisterVal};

    #[test]
    fn basic_test() {
        run_test(
            0,
            0,
            vec![
                Instruction::Xor {
                    rd: reg_x(1),
                    rs1: reg_x(2),
                    rs2: reg_x(5),
                },
                Instruction::Add {
                    rd: reg_x(1),
                    rs1: reg_x(2),
                    rs2: reg_x(5),
                },
                Instruction::Sub {
                    rd: reg_x(1),
                    rs1: reg_x(2),
                    rs2: reg_x(5),
                },
                Instruction::Addi {
                    rd: reg_x(1),
                    rs1: reg_x(2),
                    imm: imm(234),
                },
            ],
            vec![0, 1, 2],
        );
    }

    #[test]
    fn basic_offset_test() {
        run_test(
            32,
            32,
            vec![
                Instruction::Xor {
                    rd: reg_x(1),
                    rs1: reg_x(2),
                    rs2: reg_x(5),
                },
                Instruction::Add {
                    rd: reg_x(1),
                    rs1: reg_x(2),
                    rs2: reg_x(5),
                },
                Instruction::Sub {
                    rd: reg_x(1),
                    rs1: reg_x(2),
                    rs2: reg_x(5),
                },
                Instruction::Addi {
                    rd: reg_x(1),
                    rs1: reg_x(2),
                    imm: imm(234),
                },
            ],
            vec![0, 1, 2],
        );
    }

    #[test]
    fn tricky_offset_test() {
        run_test(
            36,
            32,
            vec![
                Instruction::Xor {
                    rd: reg_x(1),
                    rs1: reg_x(2),
                    rs2: reg_x(5),
                },
                Instruction::Add {
                    rd: reg_x(1),
                    rs1: reg_x(2),
                    rs2: reg_x(5),
                },
                Instruction::Sub {
                    rd: reg_x(1),
                    rs1: reg_x(2),
                    rs2: reg_x(5),
                },
                Instruction::Addi {
                    rd: reg_x(1),
                    rs1: reg_x(2),
                    imm: imm(234),
                },
            ],
            vec![1, 2, 3],
        );
    }

    #[test]
    fn basic_loop() {
        #[rustfmt::skip]
        let expected_trace = vec![
            0, 1, 2, 3,
            0, 1, 2, 3,
            0, 1, 2, 3,
        ];
        run_test(
            0,
            0,
            vec![
                Instruction::Xor {
                    rd: reg_x(1),
                    rs1: reg_x(2),
                    rs2: reg_x(5),
                },
                Instruction::Add {
                    rd: reg_x(1),
                    rs1: reg_x(2),
                    rs2: reg_x(5),
                },
                Instruction::Sub {
                    rd: reg_x(1),
                    rs1: reg_x(2),
                    rs2: reg_x(5),
                },
                Instruction::Jal {
                    rd: reg_x(0),
                    offset: imm(0xF_FFFA),
                },
            ],
            expected_trace,
        );
    }

    fn run_test(
        entry_point: u64,
        program_offset: u64,
        program: Vec<Instruction>,
        expected_trace: Vec<usize>,
    ) {
        let program = Program::from_instructions(program);
        let mut kernel = Kernel::new(program, entry_point, program_offset);
        let actual_trace = (0..expected_trace.len())
            .map(|_| kernel.step().unwrap())
            .map(|step| {
                (step.old_processor.pc - program_offset) as usize
                    / std::mem::size_of::<InstructionVal>()
            })
            .collect::<Vec<_>>();

        assert_eq!(expected_trace, actual_trace)
    }

    /// Shortcut function that panics if `v` is not a valid reg index.
    fn reg_x(x: InstructionVal) -> GeneralRegister {
        GeneralRegister::new(x).unwrap()
    }

    /// Shortcut function that panics if `v` is not a valid imm value.
    fn imm<const WIDTH: usize>(v: RegisterVal) -> Imm<{ WIDTH }> {
        Imm::new(v).unwrap()
    }
}
