//! This module contains the type-safe internal representation
//! of a RiscV instruction and other related types related to it.

use std::ops::{Shl, Shr};

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
/// are valid RiscV instructions. The order of operands in
/// the instructions is the same as in RiscV assembly.
///
/// For instruction behaviour, please consult the RiscV
/// documentation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
pub enum Instruction {
    /* J-Type instructions */
    Jal(RegId, Bit<20>),
    /* R-Type instructions */
    Add(RegId, RegId, RegId),
    Sub(RegId, RegId, RegId),
    Xor(RegId, RegId, RegId),
    /* U-Type instructions */
    Lui(RegId, Bit<20>),
    Auipc(RegId, Bit<20>),
    /* I-Type instructions */
    Addi(RegId, RegId, Bit<12>),
    Slli(RegId, RegId, Bit<12>),
    Slti(RegId, RegId, Bit<12>),
    Sltiu(RegId, RegId, Bit<12>),
    Xori(RegId, RegId, Bit<12>),
    Srli(RegId, RegId, Bit<5>),
    Srai(RegId, RegId, Bit<5>),
    Ori(RegId, RegId, Bit<12>),
    Andi(RegId, RegId, Bit<12>),
    Jalr(RegId, RegId, Bit<12>),
    Lb(RegId, RegId, Bit<12>),
    Lh(RegId, RegId, Bit<12>),
    Lw(RegId, RegId, Bit<12>),
    Lbu(RegId, RegId, Bit<12>),
    Lhu(RegId, RegId, Bit<12>),
    Sb(RegId, RegId, Bit<12>),
    Sh(RegId, RegId, Bit<12>),
    Sw(RegId, RegId, Bit<12>),
}

impl Instruction {
    pub fn execute(
        self,
        registers: &mut Registers,
        memory: &mut Memory,
        old_pc: RegVal,
    ) -> Result<(), InstructionError> {
        match self {
            Instruction::Jal(rd, imm) => {
                let new_pc = old_pc.wrapping_add(imm.get_sext() << 1);
                registers.set(rd, old_pc + 4);
                registers.pc = new_pc;
                Ok(())
            }
            Instruction::Add(rd, rs1, rs2) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                registers.set(rd, rs1.wrapping_add(rs2));
                Ok(())
            }
            Instruction::Sub(rd, rs1, rs2) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                registers.set(rd, rs1.wrapping_sub(rs2));
                Ok(())
            }
            Instruction::Xor(rd, rs1, rs2) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                registers.set(rd, rs1 ^ rs2);
                Ok(())
            }
            Instruction::Lui(rd, imm) => {
                registers.set(rd, imm.get_sext() << 12);
                Ok(())
            }
            Instruction::Auipc(rd, imm) => {
                registers.set(rd, old_pc.wrapping_add(imm.get_sext() << 12));
                Ok(())
            }
            Instruction::Addi(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                registers.set(rd, rs1.wrapping_add(imm.get_sext()));
                Ok(())
            }
            Instruction::Slli(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                registers.set(rd, rs1.shl(imm.get_zext()));
                Ok(())
            }
            Instruction::Slti(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                let new_rd = if lts_regval(rs1, imm.get_sext()) { 1 } else { 0 };
                registers.set(rd, new_rd);
                Ok(())
            }
            Instruction::Sltiu(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                let new_rd = if rs1 < imm.get_zext() { 1 } else { 0 };
                registers.set(rd, new_rd);
                Ok(())
            }
            Instruction::Xori(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                registers.set(rd, rs1 ^ imm.get_sext());
                Ok(())
            }
            Instruction::Srli(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                registers.set(rd, rs1.shr(imm.get_zext()));
                Ok(())
            }
            Instruction::Srai(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                registers.set(rd, shra_regval(rs1, imm.get_zext()));
                Ok(())
            }
            Instruction::Ori(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                registers.set(rd, rs1 | imm.get_sext());
                Ok(())
            }
            Instruction::Andi(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                registers.set(rd, rs1 & imm.get_sext());
                Ok(())
            }
            Instruction::Jalr(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                let new_pc = rs1.wrapping_add(imm.get_sext());
                registers.set(rd, old_pc + 4);
                registers.pc = new_pc;
                Ok(())
            }
            Instruction::Lb(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                let address = rs1.wrapping_add(imm.get_sext());
                let mut dst = [0u8; std::mem::size_of::<RegVal>()];
                self.mem_read(memory, old_pc, address, &mut dst[0..1])?;
                registers.set(rd, sext_regval::<8>(RegVal::from_le_bytes(dst)));
                Ok(())
            }
            Instruction::Lh(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                let address = rs1.wrapping_add(imm.get_sext());
                let mut dst = [0u8; std::mem::size_of::<RegVal>()];
                self.mem_read(memory, old_pc, address, &mut dst[0..2])?;
                registers.set(rd, sext_regval::<16>(RegVal::from_le_bytes(dst)));
                Ok(())
            }
            Instruction::Lw(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                let address = rs1.wrapping_add(imm.get_sext());
                let mut dst = [0u8; std::mem::size_of::<RegVal>()];
                self.mem_read(memory, old_pc, address, &mut dst[0..4])?;
                // TODO: remove the sext when we migrate to RV32
                registers.set(rd, sext_regval::<32>(RegVal::from_le_bytes(dst)));
                Ok(())
            }
            Instruction::Lbu(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                let address = rs1.wrapping_add(imm.get_sext());
                let mut dst = [0u8; std::mem::size_of::<RegVal>()];
                self.mem_read(memory, old_pc, address, &mut dst[0..1])?;
                registers.set(rd, RegVal::from_le_bytes(dst));
                Ok(())
            }
            Instruction::Lhu(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                let address = rs1.wrapping_add(imm.get_sext());
                let mut dst = [0u8; std::mem::size_of::<RegVal>()];
                self.mem_read(memory, old_pc, address, &mut dst[0..2])?;
                registers.set(rd, RegVal::from_le_bytes(dst));
                Ok(())
            }
            Instruction::Sb(rs1, rs2, imm) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                let address = rs1.wrapping_add(imm.get_sext());
                let src = rs2.to_le_bytes();
                self.mem_write(memory, old_pc, address, &src[0..1])?;
                Ok(())
            }
            Instruction::Sh(rs1, rs2, imm) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                let address = rs1.wrapping_add(imm.get_sext());
                let src = rs2.to_le_bytes();
                self.mem_write(memory, old_pc, address, &src[0..2])?;
                Ok(())
            }
            Instruction::Sw(rs1, rs2, imm) => {
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

/// Does an arithmetic shift on a regval.
fn shra_regval(x: RegVal, amount: RegVal) -> RegVal {
    // Sanity check for making migration seemless.
    // If this is true, it will be NOOP in release.
    assert_eq!(i64::BITS, RegVal::BITS);
    // Converting between i64 and RegVal is just
    // a bit reinterpretation.
    // When doing a sihft to the left on a signed
    // integer, rust does an arithmetic shift.
    ((x as i64) >> amount) as RegVal
}

/// Check if x < y, treating both as signed values.
fn lts_regval(x: RegVal, y: RegVal) -> bool {
    // Sanity check for making migration seemless.
    // If this is true, it will be NOOP in release.
    assert_eq!(i64::BITS, RegVal::BITS);
    (x as i64) < (y as i64)
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
