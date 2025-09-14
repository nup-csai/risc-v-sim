//! This module contains the type-safe internal representation
//! of a RiscV instruction and other related types related to it.

use thiserror::Error;

use super::{Memory, MemoryError, RegId, RegVal, Registers};

/// Error returned by [Instruction::execute].
#[derive(Clone, Copy, PartialEq, Eq, Error, Debug)]
pub enum InstructionError {
    #[error("Failed to execute instruction {instruction:?} at {instruction_address:#x}: {memory_error}")]
    MemoryError {
        instruction_address: RegVal,
        instruction: Instruction,
        #[source]
        memory_error: MemoryError,
    },
}

/// [Instruction] is a type-safe representation of a CPU
/// instruction. That means, all valid values of this type
/// are valid RiscV instructions. Each instruction behavior is documented.
///
/// The pseudo-code slightly differs from the documentation. This
/// is because we assume that the immediate value is always placed
/// in the lowest bits of [RegisterVal]. Because of that, e.g.
/// `lui` is documented to be offsetting `imm` by 12 bits.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
pub enum Instruction {
    /* J-Type instructions */
    /// Jal instruction. Has the following semantics
    /// ```pic
    /// rd = PC + 4 // Overflow
    /// PC += sext(imm << 1) // Overflow
    /// ```
    Jal { rd: RegId, imm: Bit<20> },
    /* R-Type instructions */
    /// Add instruction. Has the following semantics
    /// ```pic
    /// rd = rs1 + rs2 // Overflow
    /// ```
    Add { rd: RegId, rs1: RegId, rs2: RegId },
    /// Sub instruction. Has the following semantics
    /// ```pic
    /// rd = rs1 - rs2 // Overflow
    /// ```
    Sub { rd: RegId, rs1: RegId, rs2: RegId },
    /// Xor instruction. Has the following semantics
    /// ```pic
    /// rd = rs1 ^ rs2
    /// ```
    Xor { rd: RegId, rs1: RegId, rs2: RegId },
    /* U-Type instructions */
    /// Lui instruction. Has the following semantics
    /// ```pic
    /// rd = sext(imm << 12)
    /// ```
    Lui { rd: RegId, imm: Bit<20> },
    /// Auipc instruction. Has the following semantics
    /// ```pic
    /// rd = PC + sext(imm << 12) // Overflow
    /// ```
    Auipc { rd: RegId, imm: Bit<20> },
    /* I-Type instructions */
    /// Addi instruction. Has the following semantics
    /// ```pic
    /// rd = rs1 + sext(imm) // Overflow
    /// ```
    Addi { rd: RegId, rs1: RegId, imm: Bit<12> },
    /// Xori instruction. Has the following semantics
    /// ```pic
    /// rd = rs1 ^ sext(rs2)
    /// ```
    Xori { rd: RegId, rs1: RegId, imm: Bit<12> },
    /// Jalr instruction. Has the following semantics
    /// ```pic
    /// rd = PC + 4 // Overflow
    /// PC = rs1 + sext(imm) // Overflow
    /// ```
    Jalr { rd: RegId, rs1: RegId, imm: Bit<12> },
    /// Lb instruction. Has the following semantics
    /// ```pic
    /// rd = sext(Read(rs1 + sext(imm), 8))
    /// ```
    Lb { rd: RegId, rs1: RegId, imm: Bit<12> },
    /// Lb instruction. Has the following semantics
    /// ```pic
    /// rd = sext(Read(rs1 + sext(imm), 16))
    /// ```
    Lh { rd: RegId, rs1: RegId, imm: Bit<12> },
    /// Lb instruction. Has the following semantics
    /// ```pic
    /// rd = sext(Read(rs1 + sext(imm), 32))
    /// ```
    Lw { rd: RegId, rs1: RegId, imm: Bit<12> },
    /// Lb instruction. Has the following semantics
    /// ```pic
    /// rd = sext(Read(rs1 + sext(imm), 8))
    /// ```
    Lbu { rd: RegId, rs1: RegId, imm: Bit<12> },
    /// Lb instruction. Has the following semantics
    /// ```pic
    /// rd = sext(Read(rs1 + sext(imm), 16))
    /// ```
    Lhu { rd: RegId, rs1: RegId, imm: Bit<12> },
    /* S-Type instructions */
    /// Sw instruction. Has the followng semantics
    /// ```pic
    /// Write(rs1 + sext(imm), rs2[8:0])
    /// ```
    Sb { rs1: RegId, rs2: RegId, imm: Bit<12> },
    /// Sh instruction. Has the followng semantics
    /// ```pic
    /// Write(rs1 + sext(imm)], rs2[16:0])
    /// ```
    Sh { rs1: RegId, rs2: RegId, imm: Bit<12> },
    /// Sw instruction. Has the followng semantics
    /// ```pic
    /// Write(rs1 + sext(imm), rs2[31:0])
    /// ```
    Sw { rs1: RegId, rs2: RegId, imm: Bit<12> },
}

impl Instruction {
    pub fn execute(
        self,
        registers: &mut Registers,
        memory: &mut Memory,
        old_pc: RegVal,
    ) -> Result<(), InstructionError> {
        match self {
            Instruction::Jal { rd, imm } => {
                let new_pc = old_pc.wrapping_add(imm.get_sext() << 1);
                registers.set(rd, old_pc + 4);
                registers.pc = new_pc;
                Ok(())
            }
            Instruction::Add { rd, rs1, rs2 } => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                registers.set(rd, rs1.wrapping_add(rs2));
                Ok(())
            }
            Instruction::Sub { rd, rs1, rs2 } => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                registers.set(rd, rs1.wrapping_sub(rs2));
                Ok(())
            }
            Instruction::Xor { rd, rs1, rs2 } => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                registers.set(rd, rs1 ^ rs2);
                Ok(())
            }
            Instruction::Lui { rd, imm } => {
                registers.set(rd, imm.get_sext() << 12);
                Ok(())
            }
            Instruction::Auipc { rd, imm } => {
                registers.set(rd, old_pc.wrapping_add(imm.get_sext() << 12));
                Ok(())
            }
            Instruction::Addi { rd, rs1, imm } => {
                let rs1 = registers.get(rs1);
                registers.set(rd, rs1.wrapping_add(imm.get_sext()));
                Ok(())
            }
            Instruction::Xori { rd, rs1, imm } => {
                let rs1 = registers.get(rs1);
                registers.set(rd, rs1 ^ imm.get_sext());
                Ok(())
            }
            Instruction::Jalr { rd, rs1, imm } => {
                let rs1 = registers.get(rs1);
                let new_pc = rs1.wrapping_add(imm.get_sext());
                registers.set(rd, old_pc + 4);
                registers.pc = new_pc;
                Ok(())
            }
            Instruction::Lb { rd, rs1, imm } => {
                let rs1 = registers.get(rs1);
                let address = rs1.wrapping_add(imm.get_sext());
                let mut dst = [0u8; std::mem::size_of::<RegVal>()];
                self.mem_read(memory, old_pc, address, &mut dst[0..1])?;
                registers.set(rd, sext_regval::<8>(RegVal::from_le_bytes(dst)));
                Ok(())
            }
            Instruction::Lh { rd, rs1, imm } => {
                let rs1 = registers.get(rs1);
                let address = rs1.wrapping_add(imm.get_sext());
                let mut dst = [0u8; std::mem::size_of::<RegVal>()];
                self.mem_read(memory, old_pc, address, &mut dst[0..2])?;
                registers.set(rd, sext_regval::<16>(RegVal::from_le_bytes(dst)));
                Ok(())
            }
            Instruction::Lw { rd, rs1, imm } => {
                let rs1 = registers.get(rs1);
                let address = rs1.wrapping_add(imm.get_sext());
                let mut dst = [0u8; std::mem::size_of::<RegVal>()];
                self.mem_read(memory, old_pc, address, &mut dst[0..4])?;
                // TODO: remove the sext when we migrate to RV32
                registers.set(rd, sext_regval::<32>(RegVal::from_le_bytes(dst)));
                Ok(())
            }
            Instruction::Lbu { rd, rs1, imm } => {
                let rs1 = registers.get(rs1);
                let address = rs1.wrapping_add(imm.get_sext());
                let mut dst = [0u8; std::mem::size_of::<RegVal>()];
                self.mem_read(memory, old_pc, address, &mut dst[0..1])?;
                registers.set(rd, RegVal::from_le_bytes(dst));
                Ok(())
            }
            Instruction::Lhu { rd, rs1, imm } => {
                let rs1 = registers.get(rs1);
                let address = rs1.wrapping_add(imm.get_sext());
                let mut dst = [0u8; std::mem::size_of::<RegVal>()];
                self.mem_read(memory, old_pc, address, &mut dst[0..2])?;
                registers.set(rd, RegVal::from_le_bytes(dst));
                Ok(())
            }
            Instruction::Sb { rs1, rs2, imm } => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                let address = rs1.wrapping_add(imm.get_sext());
                let src = rs2.to_le_bytes();
                self.mem_write(memory, old_pc, address, &src[0..1])?;
                Ok(())
            }
            Instruction::Sh { rs1, rs2, imm } => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                let address = rs1.wrapping_add(imm.get_sext());
                let src = rs2.to_le_bytes();
                self.mem_write(memory, old_pc, address, &src[0..2])?;
                Ok(())
            }
            Instruction::Sw { rs1, rs2, imm } => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                let address = rs1.wrapping_add(imm.get_sext());
                let src = rs2.to_le_bytes();
                self.mem_write(memory, old_pc, address, &src[0..4])?;
                Ok(())
            }
        }
    }

    fn mem_read(
        self,
        memory: &Memory,
        instruction_address: RegVal,
        address: RegVal,
        dst: &mut [u8],
    ) -> Result<(), InstructionError> {
        memory
            .read(address, dst)
            .map_err(|memory_error| InstructionError::MemoryError {
                instruction: self,
                instruction_address,
                memory_error,
            })
    }

    fn mem_write(
        self,
        memory: &mut Memory,
        instruction_address: RegVal,
        address: RegVal,
        src: &[u8],
    ) -> Result<(), InstructionError> {
        memory
            .write(address, src)
            .map_err(|memory_error| InstructionError::MemoryError {
                instruction: self,
                instruction_address,
                memory_error,
            })
    }
}

fn sext_regval<const N: usize>(x: RegVal) -> RegVal {
    Bit::<N>::new(x).unwrap().get_sext()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
#[repr(transparent)]
/// Contains a N-bit wide immediate value
pub struct Bit<const N: usize>(RegVal);

impl<const N: usize> Bit<N> {
    /// The maximum possible value.
    pub const MAX: RegVal = ((1 as RegVal) << N) - 1;

    const SIGN_BIT: RegVal = (1 as RegVal) << (N - 1);
    const EXTENSION: RegVal = RegVal::MAX ^ Self::MAX;

    pub const fn new(val: RegVal) -> Option<Self> {
        if val <= Self::MAX {
            Some(Self(val))
        } else {
            None
        }
    }

    /// Get the value as [RegisterVal].
    /// The value is zero-extended.
    // NOTE: unused, but may be useful later.
    #[allow(dead_code)]
    pub const fn get_zext(self) -> RegVal {
        self.0
    }

    /// Get the value as [RegisterVal].
    /// The value is sign-extended.
    pub const fn get_sext(self) -> RegVal {
        let mut result = self.0;
        if (result & Self::SIGN_BIT) == Self::SIGN_BIT {
            result |= Self::EXTENSION;
        }
        result
    }
}

/// Useful short-cut functions for constructing instructions.
pub mod shortcodes {
    use super::{Bit, Instruction, RegId};

    pub const fn jal(rd: RegId, imm: Bit<20>) -> Instruction {
        Instruction::Jal { rd, imm }
    }

    pub const fn add(rd: RegId, rs1: RegId, rs2: RegId) -> Instruction {
        Instruction::Add { rd, rs1, rs2 }
    }

    pub const fn sub(rd: RegId, rs1: RegId, rs2: RegId) -> Instruction {
        Instruction::Sub { rd, rs1, rs2 }
    }

    pub const fn xor(rd: RegId, rs1: RegId, rs2: RegId) -> Instruction {
        Instruction::Xor { rd, rs1, rs2 }
    }

    pub const fn lui(rd: RegId, imm: Bit<20>) -> Instruction {
        Instruction::Lui { rd, imm }
    }

    pub const fn auipc(rd: RegId, imm: Bit<20>) -> Instruction {
        Instruction::Auipc { rd, imm }
    }

    pub const fn addi(rd: RegId, rs1: RegId, imm: Bit<12>) -> Instruction {
        Instruction::Addi { rd, rs1, imm }
    }

    pub const fn xori(rd: RegId, rs1: RegId, imm: Bit<12>) -> Instruction {
        Instruction::Xori { rd, rs1, imm }
    }

    pub const fn jalr(rd: RegId, rs1: RegId, imm: Bit<12>) -> Instruction {
        Instruction::Jalr { rd, rs1, imm }
    }

    pub const fn lb(rd: RegId, rs1: RegId, imm: Bit<12>) -> Instruction {
        Instruction::Lb { rd, rs1, imm }
    }

    pub const fn lh(rd: RegId, rs1: RegId, imm: Bit<12>) -> Instruction {
        Instruction::Lh { rd, rs1, imm }
    }

    pub const fn lw(rd: RegId, rs1: RegId, imm: Bit<12>) -> Instruction {
        Instruction::Lw { rd, rs1, imm }
    }

    pub const fn lbu(rd: RegId, rs1: RegId, imm: Bit<12>) -> Instruction {
        Instruction::Lbu { rd, rs1, imm }
    }

    pub const fn lhu(rd: RegId, rs1: RegId, imm: Bit<12>) -> Instruction {
        Instruction::Lhu { rd, rs1, imm }
    }

    pub const fn sb(rs1: RegId, rs2: RegId, imm: Bit<12>) -> Instruction {
        Instruction::Sb { rs1, rs2, imm }
    }

    pub const fn sh(rs1: RegId, rs2: RegId, imm: Bit<12>) -> Instruction {
        Instruction::Sh { rs1, rs2, imm }
    }

    pub const fn sw(rs1: RegId, rs2: RegId, imm: Bit<12>) -> Instruction {
        Instruction::Sw { rs1, rs2, imm }
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::RegVal;

    use super::Bit;

    const SAMPLE_COUNT: usize = 10_000;

    #[test]
    fn test_imm_12_max() {
        for x in 0..=Bit::<12>::MAX {
            Bit::<12>::new(x).expect("Must succeed");
        }
        for _ in 0..SAMPLE_COUNT {
            let x = rand::random_range((Bit::<12>::MAX + 1)..RegVal::MAX);
            assert_eq!(Bit::<12>::new(x), None);
        }
    }

    #[test]
    fn test_sext_positive_12() {
        for x in 0..0x400 {
            let imm = Bit::<12>::new(x).unwrap();
            assert_eq!(x, imm.get_sext());
        }
    }

    #[test]
    fn test_sext_negative_12() {
        for x in 0..0x400 {
            let imm = Bit::<12>::new(x | 0x800).unwrap();
            let target = x | 0xffff_ffff_ffff_f800;
            assert_eq!(target, imm.get_sext(), "Imm value: {}", imm.get_zext());
        }
    }

    #[test]
    fn test_sext_positive_20() {
        for x in 0..0x4_0000 {
            let imm = Bit::<20>::new(x).unwrap();
            assert_eq!(x, imm.get_sext());
        }
    }

    #[test]
    fn test_sext_negative_20() {
        for x in 0..0x4_0000 {
            let imm = Bit::<20>::new(x | 0x8_0000).unwrap();
            let target = x | 0xffff_ffff_fff8_0000;
            assert_eq!(target, imm.get_sext(), "Imm value: {}", imm.get_zext());
        }
    }

    #[test]
    fn test_imm_20_max() {
        for x in 0..=Bit::<20>::MAX {
            Bit::<20>::new(x).expect("Must succeed");
        }
        for _ in 0..SAMPLE_COUNT {
            let x = rand::random_range((Bit::<20>::MAX + 1)..RegVal::MAX);
            assert_eq!(Bit::<20>::new(x), None);
        }
    }
}
