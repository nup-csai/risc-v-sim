//! This module contains the type-safe internal representation
//! of a RiscV instruction and other related types related to it.

use std::{
    fmt,
    ops::{Shl, Shr},
};

use thiserror::Error;

use crate::kernel::{RegValSigned, REGVAL_SIZE_MASK};

use super::{Memory, MemoryError, RegId, RegVal, Registers};

/// Error returned by [Instruction::execute].
#[derive(Clone, Copy, PartialEq, Eq, Error, Debug)]
pub enum InstructionError {
    #[error("instruction `{instruction}`: {memory_error}")]
    MemoryError {
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
    Or(RegId, RegId, RegId),
    And(RegId, RegId, RegId),
    Sll(RegId, RegId, RegId),
    Srl(RegId, RegId, RegId),
    Sra(RegId, RegId, RegId),
    Slt(RegId, RegId, RegId),
    Sltu(RegId, RegId, RegId),
    /* U-Type instructions */
    Lui(RegId, Bit<20>),
    Auipc(RegId, Bit<20>),
    /* I-Type instructions */
    Addi(RegId, RegId, Bit<12>),
    Xori(RegId, RegId, Bit<12>),
    Ori(RegId, RegId, Bit<12>),
    Andi(RegId, RegId, Bit<12>),
    Slli(RegId, RegId, Bit<12>),
    Srli(RegId, RegId, Bit<5>),
    Srai(RegId, RegId, Bit<5>),
    Slti(RegId, RegId, Bit<12>),
    Sltiu(RegId, RegId, Bit<12>),
    Jalr(RegId, RegId, Bit<12>),
    Lb(RegId, RegId, Bit<12>),
    Lh(RegId, RegId, Bit<12>),
    Lw(RegId, RegId, Bit<12>),
    Lbu(RegId, RegId, Bit<12>),
    Lhu(RegId, RegId, Bit<12>),
    /* S-Type instructions */
    Sb(RegId, RegId, Bit<12>),
    Sh(RegId, RegId, Bit<12>),
    Sw(RegId, RegId, Bit<12>),
    /* B-Type instructions */
    Beq(RegId, RegId, Bit<12>),
    Bne(RegId, RegId, Bit<12>),
    Blt(RegId, RegId, Bit<12>),
    Bge(RegId, RegId, Bit<12>),
    Bltu(RegId, RegId, Bit<12>),
    Bgeu(RegId, RegId, Bit<12>),
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
            Instruction::Or(rd, rs1, rs2) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                registers.set(rd, rs1 | rs2);
                Ok(())
            }
            Instruction::And(rd, rs1, rs2) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                registers.set(rd, rs1 & rs2);
                Ok(())
            }
            Instruction::Sll(rd, rs1, rs2) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2) & REGVAL_SIZE_MASK;
                registers.set(rd, rs1 << rs2);
                Ok(())
            }
            Instruction::Srl(rd, rs1, rs2) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2) & REGVAL_SIZE_MASK;
                registers.set(rd, rs1 >> rs2);
                Ok(())
            }
            Instruction::Sra(rd, rs1, rs2) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2) & REGVAL_SIZE_MASK;
                registers.set(rd, shra_regval(rs1, rs2));
                Ok(())
            }
            Instruction::Slt(rd, rs1, rs2) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                let new_rd = if lts_regval(rs1, rs2) { 1 } else { 0 };
                registers.set(rd, new_rd);
                Ok(())
            }
            Instruction::Sltu(rd, rs1, rs2) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                let new_rd = if rs1 < rs2 { 1 } else { 0 };
                registers.set(rd, new_rd);
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
            Instruction::Xori(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                registers.set(rd, rs1 ^ imm.get_sext());
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
            Instruction::Slli(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                registers.set(rd, rs1.shl(imm.get_zext()));
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
                let val = self.mem_read(memory, address, 1)?;
                registers.set(rd, sext_regval::<8>(val));
                Ok(())
            }
            Instruction::Lh(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                let address = rs1.wrapping_add(imm.get_sext());
                let val = self.mem_read(memory, address, 2)?;
                registers.set(rd, sext_regval::<16>(val));
                Ok(())
            }
            Instruction::Lw(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                let address = rs1.wrapping_add(imm.get_sext());
                let val = self.mem_read(memory, address, 4)?;
                // TODO: remove the sext when we migrate to RV32
                registers.set(rd, sext_regval::<32>(val));
                Ok(())
            }
            Instruction::Lbu(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                let address = rs1.wrapping_add(imm.get_sext());
                let val = self.mem_read(memory, address, 1)?;
                registers.set(rd, val);
                Ok(())
            }
            Instruction::Lhu(rd, rs1, imm) => {
                let rs1 = registers.get(rs1);
                let address = rs1.wrapping_add(imm.get_sext());
                let val = self.mem_read(memory, address, 2)?;
                registers.set(rd, val);
                Ok(())
            }
            Instruction::Sb(rs1, rs2, imm) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                let address = rs1.wrapping_add(imm.get_sext());
                self.mem_write(memory, address, rs2, 1)?;
                Ok(())
            }
            Instruction::Sh(rs1, rs2, imm) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                let address = rs1.wrapping_add(imm.get_sext());
                self.mem_write(memory, address, rs2, 2)?;
                Ok(())
            }
            Instruction::Sw(rs1, rs2, imm) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                let address = rs1.wrapping_add(imm.get_sext());
                self.mem_write(memory, address, rs2, 4)?;
                Ok(())
            }
            Instruction::Beq(rs1, rs2, imm) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                if rs1 == rs2 {
                    registers.pc = old_pc.wrapping_add(imm.get_sext() << 1);
                }
                Ok(())
            }
            Instruction::Bne(rs1, rs2, imm) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                if rs1 != rs2 {
                    registers.pc = old_pc.wrapping_add(imm.get_sext() << 1);
                }
                Ok(())
            }
            Instruction::Blt(rs1, rs2, imm) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                if lts_regval(rs1, rs2) {
                    registers.pc = old_pc.wrapping_add(imm.get_sext() << 1);
                }
                Ok(())
            }
            Instruction::Bge(rs1, rs2, imm) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                if ge_regval(rs1, rs2) {
                    registers.pc = old_pc.wrapping_add(imm.get_sext() << 1);
                }
                Ok(())
            }
            Instruction::Bltu(rs1, rs2, imm) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                if rs1 < rs2 {
                    registers.pc = old_pc.wrapping_add(imm.get_sext() << 1);
                }
                Ok(())
            }
            Instruction::Bgeu(rs1, rs2, imm) => {
                let rs1 = registers.get(rs1);
                let rs2 = registers.get(rs2);
                if rs1 >= rs2 {
                    registers.pc = old_pc.wrapping_add(imm.get_sext() << 1);
                }
                Ok(())
            }
        }
    }

    fn mem_read(
        self,
        memory: &Memory,
        address: RegVal,
        sz: usize,
    ) -> Result<RegVal, InstructionError> {
        let mut dst = [0u8; std::mem::size_of::<RegVal>()];
        memory
            .read(address, &mut dst[0..sz])
            .map_err(|memory_error| InstructionError::MemoryError {
                instruction: self,
                memory_error,
            })?;
        Ok(RegVal::from_le_bytes(dst))
    }

    fn mem_write(
        self,
        memory: &mut Memory,
        address: RegVal,
        val: RegVal,
        sz: usize,
    ) -> Result<(), InstructionError> {
        let src = &val.to_le_bytes()[0..sz];
        memory
            .write(address, src)
            .map_err(|memory_error| InstructionError::MemoryError {
                instruction: self,
                memory_error,
            })
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Instruction::*;

        match *self {
            Jal(rd, imm) => write!(f, "jal {rd} {:#x}", imm.get_zext() << 1),
            Add(rd, rs1, rs2) => write!(f, "add {rd} {rs1} {rs2}"),
            Sub(rd, rs1, rs2) => write!(f, "sub {rd} {rs1} {rs2}"),
            Xor(rd, rs1, rs2) => write!(f, "xor {rd} {rs1} {rs2}"),
            Or(rd, rs1, rs2) => write!(f, "or {rd} {rs1} {rs2}"),
            And(rd, rs1, rs2) => write!(f, "and {rd} {rs1} {rs2}"),
            Sll(rd, rs1, rs2) => write!(f, "sll {rd} {rs1} {rs2}"),
            Srl(rd, rs1, rs2) => write!(f, "srl {rd} {rs1} {rs2}"),
            Sra(rd, rs1, rs2) => write!(f, "sra {rd} {rs1} {rs2}"),
            Slt(rd, rs1, rs2) => write!(f, "slt {rd} {rs1} {rs2}"),
            Sltu(rd, rs1, rs2) => write!(f, "sltu {rd} {rs1} {rs2}"),
            Lui(rd, imm) => write!(f, "lui {rd} {:#x}", imm.get_zext()),
            Auipc(rd, imm) => write!(f, "auipc {rd} {:#x}", imm.get_zext()),
            Addi(rd, rs1, imm) => write!(f, "addi {rd} {rs1} {}", imm.get_signed()),
            Xori(rd, rs1, imm) => write!(f, "xori {rd} {rs1} {}", imm.get_signed()),
            Ori(rd, rs1, imm) => write!(f, "ori {rd} {rs1} {}", imm.get_signed()),
            Andi(rd, rs1, imm) => write!(f, "andi {rd} {rs1} {}", imm.get_signed()),
            Slli(rd, rs1, imm) => write!(f, "slli {rd} {rs1} {}", imm.get_signed()),
            Srli(rd, rs1, imm) => write!(f, "srli {rd} {rs1} {}", imm.get_signed()),
            Srai(rd, rs1, imm) => write!(f, "srai {rd} {rs1} {}", imm.get_signed()),
            Slti(rd, rs1, imm) => write!(f, "slti {rd} {rs1} {}", imm.get_signed()),
            Sltiu(rd, rs1, imm) => write!(f, "sltiu {rd} {rs1} {}", imm.get_signed()),
            Jalr(rd, rs1, imm) => write!(f, "jalr {rd} {rs1} {}", imm.get_signed()),
            Lb(rd, rs1, imm) => write!(f, "lb {rd} {rs1} {}", imm.get_signed()),
            Lh(rd, rs1, imm) => write!(f, "lh {rd} {rs1} {}", imm.get_signed()),
            Lw(rd, rs1, imm) => write!(f, "lw {rd} {rs1} {}", imm.get_signed()),
            Lbu(rd, rs1, imm) => write!(f, "lbu {rd} {rs1} {}", imm.get_signed()),
            Lhu(rd, rs1, imm) => write!(f, "lhu {rd} {rs1} {}", imm.get_signed()),
            Sb(rs1, rs2, imm) => write!(f, "sb {rs2} {}({rs1})", imm.get_signed()),
            Sh(rs1, rs2, imm) => write!(f, "sh {rs2} {}({rs1})", imm.get_signed()),
            Sw(rs1, rs2, imm) => write!(f, "sw {rs2} {}({rs1})", imm.get_signed()),
            Beq(rs1, rs2, imm) => write!(f, "beq {rs1} {rs2} {}", imm.get_sext() << 1),
            Bne(rs1, rs2, imm) => write!(f, "bne {rs1} {rs2} {}", imm.get_sext() << 1),
            Blt(rs1, rs2, imm) => write!(f, "blt {rs1} {rs2} {}", imm.get_sext() << 1),
            Bge(rs1, rs2, imm) => write!(f, "bge {rs1} {rs2} {}", imm.get_sext() << 1),
            Bltu(rs1, rs2, imm) => write!(f, "bltu {rs1} {rs2} {}", imm.get_sext() << 1),
            Bgeu(rs1, rs2, imm) => write!(f, "bgeu {rs1} {rs2} {}", imm.get_sext() << 1),
        }
    }
}

fn sext_regval<const N: usize>(x: RegVal) -> RegVal {
    Bit::<N>::new(x).unwrap().get_sext()
}

/// Does an arithmetic shift on a regval.
fn shra_regval(x: RegVal, amount: RegVal) -> RegVal {
    // Converting between RegValSigned and RegVal is just
    // a bit reinterpretation.
    // When doing a sihft to the left on a signed
    // integer, rust does an arithmetic shift.
    ((x as RegValSigned) >> amount) as RegVal
}

/// Check if x < y, treating both as signed values.
fn lts_regval(x: RegVal, y: RegVal) -> bool {
    (x as RegValSigned) < (y as RegValSigned)
}

/// Check if x >= y, treating both as signed values.
fn ge_regval(x: RegVal, y: RegVal) -> bool {
    (x as RegValSigned) >= (y as RegValSigned)
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

    pub const fn get_signed(self) -> RegValSigned {
        self.get_sext() as RegValSigned
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
