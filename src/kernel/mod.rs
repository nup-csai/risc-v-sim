pub mod decoder;
pub mod instruction;
pub mod memory;
pub mod registers;

pub use decoder::*;
pub use instruction::*;
pub use memory::*;
pub use registers::*;

use thiserror::Error;

#[derive(Debug)]
pub struct Kernel {
    pub registers: Registers,
    pub memory: Memory,
}

impl Kernel {
    pub const fn new(memory: Memory, entry_point: RegVal) -> Self {
        let mut registers = Registers::new();
        registers.pc = entry_point;

        Kernel { registers, memory }
    }

    pub fn from_program(
        program: Program,
        entry_point: RegVal,
        program_off: RegVal,
    ) -> Self {
        let mut memory = Memory::new();
        let program_bytes = program.into_bytes().into_iter().collect();
        memory
            .add_segment(MemorySegment {
                is_read: false,
                is_write: false,
                is_execute: true,
                off: program_off,
                mem: program_bytes,
            })
            .unwrap();

        Self::new(memory, entry_point)
    }

    pub fn step(&mut self) -> Result<KernelStep, KernelError> {
        let old_registers = self.registers;
        let old_pc = old_registers.pc;
        let instruction = self.fetch_instruction()?;

        self.registers.pc += 4;
        instruction
            .execute(&mut self.registers, &mut self.memory, old_pc)
            .map_err(|instruction_error| KernelError::InstructionError {
                instruction_address: self.registers.pc,
                instruction_error,
            })?;

        Ok(KernelStep { old_registers, instruction, new_registers: self.registers })
    }

    fn fetch_instruction(&self) -> Result<Instruction, KernelError> {
        let instruction_address = self.registers.pc;
        let instruction_code = self
            .memory
            .fetch_instruction(instruction_address)
            .map_err(|memory_error| KernelError::FetchError {
                instruction_address,
                memory_error,
            })?;

        decode_instruction(instruction_code).map_err(|decode_error| {
            KernelError::DecodeError {
                instruction_address,
                instruction_code,
                decode_error,
            }
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    instructions: Vec<InstrVal>,
}

impl Program {
    pub fn from_instructions(instructions: Vec<Instruction>) -> Self {
        Self { instructions: instructions.into_iter().map(encode_instruction).collect() }
    }

    pub fn from_raw_instructions(
        instructions: impl IntoIterator<Item = InstrVal>,
    ) -> Result<Self, InstructionDecodeError> {
        let instructions = instructions.into_iter().collect::<Vec<_>>();
        for (idx, instruction_code) in instructions.iter().copied().enumerate() {
            decode_instruction(instruction_code).map_err(|error| {
                InstructionDecodeError { instruction_idx: idx, instruction_code, error }
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
    pub instruction_code: InstrVal,
    #[source]
    pub error: DecodeError,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, serde::Serialize)]
pub struct KernelStep {
    pub old_registers: Registers,
    pub new_registers: Registers,
    pub instruction: Instruction,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Error)]
pub enum KernelError {
    #[error(
        "Failed to execute instruction at {instruction_address:#x}: {instruction_error}"
    )]
    InstructionError {
        instruction_address: RegVal,
        #[source]
        instruction_error: InstructionError,
    },
    #[error("Failed to fetch instruction at {instruction_address:#x}: {memory_error}")]
    FetchError {
        instruction_address: RegVal,
        #[source]
        memory_error: MemoryError,
    },
    #[error(
        "Failed to decode instruction at {instruction_address:#x} with code {instruction_code:#x}: {decode_error}"
    )]
    DecodeError {
        instruction_address: RegVal,
        instruction_code: InstrVal,
        #[source]
        decode_error: DecodeError,
    },
}

#[cfg(test)]
mod tests {
    use crate::kernel::MemorySegment;
    use crate::program;
    use crate::util::bit;

    use super::{InstrVal, Instruction, Kernel, Program, RegVal};

    const MEM_OFFSET: RegVal = 0x100;
    const MEM_LEN: RegVal = 0x1000;

    #[test]
    fn basic() {
        let program = program![
            xor RA, SP, T0;
            add RA, SP, T0;
            sub RA, SP, T0;
            addi RA, SP, 234;
        ];
        assert_trace(0, 0, program.into(), vec![0, 1, 2]);
    }

    #[test]
    fn basic_with_offset() {
        let program = program![
            xor RA, SP, T0;
            add RA, SP, T0;
            sub RA, SP, T0;
            addi RA, SP, 234;
        ];
        assert_trace(32, 32, program.into(), vec![0, 1, 2]);
    }

    #[test]
    fn basic_tricky_offset() {
        let program = program![
            xor RA, SP, T0;
            add RA, SP, T0;
            sub RA, SP, T0;
            addi RA, SP, 234;
        ];
        assert_trace(36, 32, program.into(), vec![1, 2, 3]);
    }

    #[test]
    fn basic_loop() {
        let program = program![
            xor RA, SP, T0;
            add RA, SP, T0;
            sub RA, SP, T0;
            jal ZERO, 0xF_FFFA;
        ];
        #[rustfmt::skip]
        let expected_trace = vec![
            0, 1, 2, 3,
            0, 1, 2, 3,
            0, 1, 2, 3,
        ];
        assert_trace(0, 0, program.into(), expected_trace);
    }

    /// Test storing a message byte-by-byte.
    #[test]
    fn byte_storing() {
        let msg = b"hello";
        let program = msg
            .into_iter()
            .enumerate()
            .flat_map(byte_store)
            .collect::<Vec<_>>();
        let step_count = program.len();

        let mut kernel = new_kernel(program, 0, 0);
        kernel.memory.add_segment(new_mem()).unwrap();
        for _ in 0..step_count {
            kernel.step().unwrap();
        }

        let result_segment = kernel.memory.segments()[1].as_bytes();
        assert_eq!(&result_segment[0..msg.len()], msg);
    }

    /// Test storing a message in 4-byte words.
    #[test]
    fn word_storing() {
        let pieces = [b"Hell", b"o, w", b"orld"];
        let msg = b"Hello, world";
        let program = pieces
            .into_iter()
            .enumerate()
            .flat_map(word_store)
            .collect::<Vec<_>>();
        let step_count = program.len();

        let mut kernel = new_kernel(program, 0, 0);
        kernel.memory.add_segment(new_mem()).unwrap();
        for _ in 0..step_count {
            kernel.step().unwrap();
        }

        let result_segment = kernel.memory.segments()[1].as_bytes();
        assert_eq!(&result_segment[0..msg.len()], msg.as_slice());
    }

    fn new_mem() -> MemorySegment {
        MemorySegment::new_zeroed(true, true, true, MEM_OFFSET, MEM_LEN)
    }

    fn byte_store((idx, val): (usize, &u8)) -> impl IntoIterator<Item = Instruction> {
        program![
            add T0, ZERO, ZERO;
            addi T0, ZERO, {bit(*val as RegVal)};
            sb ZERO, T0, {bit(MEM_OFFSET + idx as RegVal)};
        ]
    }

    fn word_store(
        (idx, val): (usize, &[u8; 4]),
    ) -> impl IntoIterator<Item = Instruction> {
        let off = MEM_OFFSET + (4 * idx) as RegVal;
        let val = u32::from_le_bytes(*val);
        let lower_part = (val & 0x0000_0FFF) as RegVal;
        let mut higher_part = ((val & 0xFFFF_F000) >> 12) as RegVal;
        // Because `addi` sign-extends, add a 1 to lui's immediate value
        // to cancel out the unwanted addition.
        if (lower_part & 0x800) == 0x800 {
            higher_part = higher_part.wrapping_add(1);
            higher_part &= 0xF_FFFF;
        }

        program![
            lui T0, {bit(higher_part)};
            addi T0, T0, {bit(lower_part)};
            sw ZERO, T0, {bit(off)};
        ]
    }

    fn assert_trace(
        entry_point: RegVal,
        program_off: RegVal,
        program: Vec<Instruction>,
        expected_trace: Vec<usize>,
    ) {
        let mut kernel = new_kernel(program, entry_point, program_off);
        let mut actual_trace = Vec::new();
        for _ in 0..expected_trace.len() {
            let step = kernel.step().unwrap();
            let local_exec_addr = (step.old_registers.pc - program_off) as usize;
            actual_trace.push(local_exec_addr / std::mem::size_of::<InstrVal>());
        }

        assert_eq!(expected_trace, actual_trace);
    }

    fn new_kernel(
        program: Vec<Instruction>,
        entry_point: RegVal,
        program_off: RegVal,
    ) -> Kernel {
        let program = Program::from_instructions(program);
        Kernel::from_program(program, entry_point, program_off)
    }
}
