//! The kernel is the main logic component of risc-v-sim,
//! that represents a `RiscV` computer.
//!
//! The Kernel consists of two simple parts:
//! 1. registers ([`registers::Registers`])
//! 2. memory ([`memory::Memory`])

pub mod decoder;
pub mod instruction;
pub mod memory;
pub mod registers;

pub use decoder::*;
pub use instruction::*;
use log::debug;
pub use memory::*;
pub use registers::*;

use serde::Serialize;
use thiserror::Error;

#[derive(Debug)]
pub struct Kernel {
    pub registers: Registers,
    pub memory: Memory,
}

impl Kernel {
    #[must_use]
    pub const fn new(memory: Memory, start_pc: RegVal) -> Self {
        let mut registers = Registers::new();
        registers.pc = start_pc;

        Kernel { registers, memory }
    }

    #[must_use]
    pub fn from_program(program: &Program) -> Self {
        let mut memory = Memory::new();
        memory
            .add_segment(MemorySegment {
                is_read: false,
                is_write: false,
                is_execute: true,
                off: program.load_offset,
                mem: program.as_bytes().into(),
            })
            .expect("added a segment to an empty memory");

        Self::new(memory, program.entry_point)
    }

    /// Does a single instruction step simulation.
    ///
    /// # Errors
    ///
    /// An error is returned if:
    /// 1. Trying to fetch instruction bytes at the address stored
    ///    in `pc` leads to a memory error. See [`Memory::fetch_instruction()`]
    ///    for more info.
    /// 2. The fetched instruction bytes do no represent any supported
    ///    instruction.
    /// 3. An error happened during isntruction execution. See [`Instruction::execute()`]
    ///    for more info.
    pub fn step(&mut self) -> Result<KernelStep, KernelError> {
        debug!(target: "rvsim::kernel", "Kernel step start, registers={:x?}", self.registers);

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
        debug!(target: "rvsim::kernel", "Kernel step done, registers={:x?}", self.registers);

        Ok(KernelStep { old_registers, instruction, new_registers: self.registers })
    }

    fn fetch_instruction(&self) -> Result<Instruction, KernelError> {
        let instruction_address = self.registers.pc;
        let instruction_code =
            self.memory
                .fetch_instruction(instruction_address)
                .map_err(|memory_error| KernelError::FetchError {
                    instruction_address,
                    memory_error,
                })?;

        decode_instruction(instruction_code).map_err(|decode_error| KernelError::DecodeError {
            instruction_address,
            instruction_code,
            decode_error,
        })
    }
}

/// Verified collection of instructions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    instructions: Vec<[u8; 4]>,
    pub load_offset: RegVal,
    pub entry_point: RegVal,
}

impl Program {
    /// Construct a [`Program`] from already parsed instructions.
    pub fn from_instructions(
        instructions: impl IntoIterator<Item = Instruction>,
        load_offset: RegVal,
        entry_point: RegVal,
    ) -> Self {
        let instructions = instructions
            .into_iter()
            .map(encode_instruction)
            .map(InstrVal::to_le_bytes)
            .collect();
        Self { instructions, load_offset, entry_point }
    }

    /// Constructs a [`Program`] from a collection of raw instruction
    /// values.
    ///
    /// # Errors
    ///
    /// Returns `Err` if some the collection contains an invalid
    /// instruction code. For more information, see [`decode_instruction()`].
    pub fn from_raw_instructions(
        instructions: impl IntoIterator<Item = InstrVal>,
        load_offset: RegVal,
        entry_point: RegVal,
    ) -> Result<Self, InstructionDecodeError> {
        let instructions = instructions
            .into_iter()
            .map(InstrVal::to_le_bytes)
            .collect::<Vec<_>>();
        for (idx, instruction_bytes) in instructions.iter().copied().enumerate() {
            let instruction_code = InstrVal::from_le_bytes(instruction_bytes);
            decode_instruction(instruction_code).map_err(|error| InstructionDecodeError {
                instruction_idx: idx,
                instruction_code,
                error,
            })?;
        }

        Ok(Self { instructions, load_offset, entry_point })
    }

    /// Returns program bytes as a flat slice.
    pub fn as_bytes(&self) -> &[u8] {
        self.instructions.as_flattened()
    }

    /// Returns program length.
    ///
    /// Note that it is length in **instructions**.
    /// For the byte-length use `program.as_bytes().len()`.
    pub fn len(&self) -> usize {
        self.instructions.len()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Error)]
#[error(
    "Failed to encode instruction {instruction_idx}: {instruction_code:#x} is not a valid instruction"
)]
pub struct InstructionDecodeError {
    pub instruction_idx: usize,
    pub instruction_code: InstrVal,
    #[source]
    pub error: DecodeError,
}

/// Result of a successful [`Kernel`] instruction step.
#[derive(Clone, Copy, PartialEq, Eq, Debug, serde::Serialize)]
pub struct KernelStep {
    /// Registers before the step.
    pub old_registers: Registers,
    /// Registers after the step.
    pub new_registers: Registers,
    /// The instruction that was executed.
    pub instruction: Instruction,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Error, Serialize)]
pub enum KernelError {
    #[error("Failed to execute instruction at {instruction_address:#x}: {instruction_error}")]
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
    use crate::util::bit;

    use super::{InstrVal, Instruction, Kernel, Program, RegId, RegVal};

    const MEM_OFFSET: RegVal = 0x100;
    const MEM_LEN: RegVal = 0x1000;

    const BASIC_INSTRUCTIONS: [Instruction; 4] = [
        Instruction::Xor(RegId::RA, RegId::SP, RegId::T0),
        Instruction::Add(RegId::RA, RegId::SP, RegId::T0),
        Instruction::Sub(RegId::RA, RegId::SP, RegId::T0),
        Instruction::Addi(RegId::RA, RegId::SP, bit(234)),
    ];

    #[test]
    fn basic() {
        assert_trace(&BASIC_INSTRUCTIONS, 0, 0, vec![0, 1, 2]);
    }

    #[test]
    fn basic_with_offset() {
        assert_trace(&BASIC_INSTRUCTIONS, 32, 32, vec![0, 1, 2]);
    }

    #[test]
    fn basic_tricky_offset() {
        assert_trace(&BASIC_INSTRUCTIONS, 32, 36, vec![1, 2, 3]);
    }

    #[test]
    fn basic_loop() {
        use Instruction::*;

        let instructions = [
            Xor(RegId::RA, RegId::SP, RegId::T0),
            Add(RegId::RA, RegId::SP, RegId::T0),
            Sub(RegId::RA, RegId::SP, RegId::T0),
            Jal(RegId::ZERO, bit(0xF_FFFA)),
        ];
        #[rustfmt::skip]
        let expected_trace = vec![
            0, 1, 2, 3,
            0, 1, 2, 3,
            0, 1, 2, 3,
        ];
        assert_trace(&instructions, 0, 0, expected_trace);
    }

    /// Test storing a message byte-by-byte.
    #[test]
    fn byte_storing() {
        let msg = b"hello";
        let instructions = msg.into_iter().enumerate().flat_map(byte_store);
        let program = Program::from_instructions(instructions, 0, 0);
        let mut kernel = Kernel::from_program(&program);
        kernel.memory.add_segment(new_mem()).unwrap();
        for _ in 0..program.len() {
            kernel.step().unwrap();
        }

        let result_segment = kernel.memory.segments()[1].as_bytes();
        assert_eq!(&result_segment[0..msg.len()], msg);
    }

    /// Test storing a message in 4-byte words.
    #[test]
    fn word_storing() {
        let msg = b"Hello, world";
        let (pieces, _) = msg.as_chunks();
        let instructions = pieces.into_iter().enumerate().flat_map(word_store);
        let program = Program::from_instructions(instructions, 0, 0);
        let mut kernel = Kernel::from_program(&program);
        kernel.memory.add_segment(new_mem()).unwrap();
        for _ in 0..program.len() {
            kernel.step().unwrap();
        }

        let result_segment = kernel.memory.segments()[1].as_bytes();
        assert_eq!(&result_segment[0..msg.len()], msg.as_slice());
    }

    fn new_mem() -> MemorySegment {
        MemorySegment::new_zeroed(true, true, true, MEM_OFFSET, MEM_LEN)
    }

    fn byte_store((idx, val): (usize, &u8)) -> impl IntoIterator<Item = Instruction> {
        use Instruction::*;

        [
            Add(RegId::T0, RegId::ZERO, RegId::ZERO),
            Addi(RegId::T0, RegId::ZERO, bit(*val as RegVal)),
            Sb(RegId::ZERO, RegId::T0, bit(MEM_OFFSET + idx as RegVal)),
        ]
    }

    fn word_store((idx, val): (usize, &[u8; 4])) -> impl IntoIterator<Item = Instruction> {
        use Instruction::*;

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

        [
            Lui(RegId::T0, bit(higher_part)),
            Addi(RegId::T0, RegId::T0, bit(lower_part)),
            Sw(RegId::ZERO, RegId::T0, bit(off)),
        ]
    }

    fn assert_trace(
        instructions: &[Instruction],
        load_offset: RegVal,
        entry_point: RegVal,
        expected_trace: Vec<usize>,
    ) {
        let instructions = instructions.iter().copied();
        let program = Program::from_instructions(instructions, load_offset, entry_point);
        let mut kernel = Kernel::from_program(&program);
        let mut actual_trace = Vec::new();
        for _ in 0..expected_trace.len() {
            let step = kernel.step().unwrap();
            let local_exec_addr = (step.old_registers.pc - load_offset) as usize;
            actual_trace.push(local_exec_addr / std::mem::size_of::<InstrVal>());
        }

        assert_eq!(expected_trace, actual_trace);
    }
}
