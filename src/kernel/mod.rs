pub mod decoder;
pub mod instruction;
pub mod memory;
pub mod processor;

pub use decoder::*;
pub use instruction::*;
pub use memory::*;
pub use processor::*;

use thiserror::Error;

#[derive(Debug)]
pub struct Kernel {
    pub processor: Processor,
    pub memory: Memory,
}

impl Kernel {
    pub const fn new(memory: Memory, entry_point: u64) -> Self {
        let mut processor = Processor::new();
        processor.pc = entry_point;

        Kernel { processor, memory }
    }

    pub fn from_program(program: Program, entry_point: u64, program_offset: u64) -> Self {
        let mut memory = Memory::new();
        let program_bytes = program.into_bytes().into_iter().collect();
        memory
            .add_segment(MemorySegment {
                is_read: false,
                is_write: false,
                is_execute: true,
                offset: program_offset,
                mem: program_bytes,
            })
            .unwrap();

        Self::new(memory, entry_point)
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
        let instruction_address = self.processor.pc;
        let instruction_code =
            self.memory
                .fetch_instruction(instruction_address)
                .map_err(|memory_error| KernelError::FetchError {
                    instruction_address,
                    memory_error,
                })?;
        let instruction = decode_instruction(instruction_code).map_err(|decode_error| {
            KernelError::DecodeError {
                instruction_address,
                instruction_code,
                decode_error,
            }
        })?;

        Ok(instruction)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    instructions: Vec<InstructionVal>,
}

impl Program {
    pub fn from_instructions(instructions: Vec<Instruction>) -> Self {
        Self {
            instructions: instructions.into_iter().map(encode_instruction).collect(),
        }
    }

    pub fn from_raw_instructions(
        instructions: impl IntoIterator<Item = InstructionVal>,
    ) -> Result<Self, InstructionDecodeError> {
        let instructions = instructions.into_iter().collect::<Vec<_>>();
        for (idx, instruction_code) in instructions.iter().copied().enumerate() {
            decode_instruction(instruction_code).map_err(|error| InstructionDecodeError {
                instruction_idx: idx,
                instruction_code,
                error,
            })?;
        }

        Ok(Self { instructions })
    }

    pub fn into_bytes(self) -> impl IntoIterator<Item = u8> {
        self.instructions.into_iter().flat_map(u32::to_le_bytes)
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
    #[error("Failed to execute instruction at {instruction_address:#x}: {instruction_error}")]
    InstructionError {
        instruction_address: RegisterVal,
        #[source]
        instruction_error: InstructionError,
    },
    #[error("Failed to fetch instruction at {instruction_address:#x}: {memory_error}")]
    FetchError {
        instruction_address: RegisterVal,
        #[source]
        memory_error: MemoryError,
    },
    #[error("Failed to decode instruction at {instruction_address:#x} with code {instruction_code:#x}: {decode_error}")]
    DecodeError {
        instruction_address: RegisterVal,
        instruction_code: InstructionVal,
        #[source]
        decode_error: DecodeError,
    },
}

#[cfg(test)]
mod tests {
    use super::{Bit, GeneralRegister, Instruction, InstructionVal, Kernel, Program, RegisterVal};

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
                    imm: bit(234),
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
                    imm: bit(234),
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
                    imm: bit(234),
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
                    imm: bit(0xF_FFFA),
                },
            ],
            expected_trace,
        );
    }

    fn run_test(
        entry_point: RegisterVal,
        program_offset: RegisterVal,
        program: Vec<Instruction>,
        expected_trace: Vec<usize>,
    ) {
        let program = Program::from_instructions(program);
        let mut kernel = Kernel::from_program(program, entry_point, program_offset);
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
        GeneralRegister::new(x).expect("Bad register value")
    }

    /// Shortcut function that panics if `v` is not a valid Bit<N> value.
    fn bit<const WIDTH: usize>(v: RegisterVal) -> Bit<{ WIDTH }> {
        Bit::new(v).expect("bad bit value")
    }
}
