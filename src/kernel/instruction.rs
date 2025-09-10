//! This module contains the type-safe internal representation
//! of a RiscV instruction and other related types related to it.

use thiserror::Error;

use super::{GeneralRegister, Processor, RegisterVal};

/// Error returned by [Instruction::execute].
#[derive(Clone, Copy, PartialEq, Eq, Error, Debug)]
pub enum InstructionError {}

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
    Jal { rd: GeneralRegister, imm: Bit<20> },
    /* R-Type instructions */
    /// Add instruction. Has the following semantics
    /// ```pic
    /// rd = rs1 + rs2 // Overflow
    /// ```
    Add {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        rs2: GeneralRegister,
    },
    /// Sub instruction. Has the following semantics
    /// ```pic
    /// rd = rs1 - rs2 // Overflow
    /// ```
    Sub {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        rs2: GeneralRegister,
    },
    /// Xor instruction. Has the following semantics
    /// ```pic
    /// rd = rs1 ^ rs2
    /// ```
    Xor {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        rs2: GeneralRegister,
    },
    /* U-Type instructions */
    /// Lui instruction. Has the following semantics
    /// ```pic
    /// rd = sext(imm << 12)
    /// ```
    Lui { rd: GeneralRegister, imm: Bit<20> },
    /// Auipc instruction. Has the following semantics
    /// ```pic
    /// rd = PC + sext(imm << 12) // Overflow
    /// ```
    Auipc { rd: GeneralRegister, imm: Bit<20> },
    /* I-Type instructions */
    /// Addi instruction. Has the following semantics
    /// ```pic
    /// rd = rs1 + sext(imm) // Overflow
    /// ```
    Addi {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        imm: Bit<12>,
    },
    /// Xori instruction. Has the following semantics
    /// ```pic
    /// rd = rs1 ^ sext(rs2)
    /// ```
    Xori {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        imm: Bit<12>,
    },
    /// Jalr instruction. Has the following semantics
    /// ```pic
    /// rd = PC + 4 // Overflow
    /// PC = rs1 + sext(imm) // Overflow
    /// ```
    Jalr {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        imm: Bit<12>,
    },
}

impl Instruction {
    /// Executes the instruction on a processor. The processor is
    /// modified in-place. In case of an error, an error is returned.
    /// The processor state will not be reliable if `execute` fails.
    pub fn execute(
        self,
        processor: &mut Processor,
        old_pc: RegisterVal,
    ) -> Result<(), InstructionError> {
        match self {
            Instruction::Jal { rd, imm } => {
                let new_pc = old_pc.wrapping_add(imm.get_sext() << 1);
                processor.set_register(rd, old_pc + 4);
                processor.pc = new_pc;
                Ok(())
            }
            Instruction::Add { rd, rs1, rs2 } => {
                let rs1 = processor.get_register(rs1);
                let rs2 = processor.get_register(rs2);
                processor.set_register(rd, rs1.wrapping_add(rs2));
                Ok(())
            }
            Instruction::Sub { rd, rs1, rs2 } => {
                let rs1 = processor.get_register(rs1);
                let rs2 = processor.get_register(rs2);
                processor.set_register(rd, rs1.wrapping_sub(rs2));
                Ok(())
            }
            Instruction::Xor { rd, rs1, rs2 } => {
                let rs1 = processor.get_register(rs1);
                let rs2 = processor.get_register(rs2);
                processor.set_register(rd, rs1 ^ rs2);
                Ok(())
            }
            Instruction::Lui { rd, imm } => {
                processor.set_register(rd, imm.get_sext() << 12);
                Ok(())
            }
            Instruction::Auipc { rd, imm } => {
                processor.set_register(rd, old_pc.wrapping_add(imm.get_sext() << 12));
                Ok(())
            }
            Instruction::Addi { rd, rs1, imm } => {
                let rs1 = processor.get_register(rs1);
                processor.set_register(rd, rs1.wrapping_add(imm.get_sext()));
                Ok(())
            }
            Instruction::Xori { rd, rs1, imm } => {
                let rs1 = processor.get_register(rs1);
                processor.set_register(rd, rs1 ^ imm.get_sext());
                Ok(())
            }
            Instruction::Jalr { rd, rs1, imm } => {
                let rs1 = processor.get_register(rs1);
                let new_pc = rs1.wrapping_add(imm.get_sext());
                processor.set_register(rd, old_pc + 4);
                processor.pc = new_pc;
                Ok(())
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
#[repr(transparent)]
/// Contains a N-bit wide immediate value
pub struct Bit<const WIDTH: usize>(RegisterVal);

impl<const WIDTH: usize> Bit<WIDTH> {
    /// The maximum possible value.
    pub const MAX: RegisterVal = ((1 as RegisterVal) << WIDTH) - 1;

    const SIGN_BIT: RegisterVal = (1 as RegisterVal) << WIDTH - 1;
    const EXTENSION: RegisterVal = RegisterVal::MAX ^ Self::MAX;

    pub const fn new(val: RegisterVal) -> Option<Self> {
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
    pub const fn get_zext(self) -> RegisterVal {
        self.0
    }

    /// Get the value as [RegisterVal].
    /// The value is sign-extended.
    pub const fn get_sext(self) -> RegisterVal {
        let mut result = self.0;
        if (result & Self::SIGN_BIT) == Self::SIGN_BIT {
            result |= Self::EXTENSION;
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::RegisterVal;

    use super::Bit;

    const SAMPLE_COUNT: usize = 10_000;

    #[test]
    fn test_imm_12_max() {
        for x in 0..=Bit::<12>::MAX {
            Bit::<12>::new(x).expect("Must succeed");
        }
        for _ in 0..SAMPLE_COUNT {
            let x = rand::random_range((Bit::<12>::MAX + 1)..RegisterVal::MAX);
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
            let x = rand::random_range((Bit::<20>::MAX + 1)..RegisterVal::MAX);
            assert_eq!(Bit::<20>::new(x), None);
        }
    }
}
