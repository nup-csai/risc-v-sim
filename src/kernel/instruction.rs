use thiserror::Error;

use super::{GeneralRegister, Processor, RegisterVal};

#[derive(Clone, Copy, PartialEq, Eq, Error, Debug)]
pub enum InstructionError {}

/// [Instruction] is a type-safe representation of a CPU
/// instruction. That means, all valid values of this type
/// are valid RiscV instructions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
pub enum Instruction {
    /* J-Type instructions */
    Jal {
        rd: GeneralRegister,
        offset: Imm<20>,
    },
    /* R-Type instructions */
    Add {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        rs2: GeneralRegister,
    },
    Sub {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        rs2: GeneralRegister,
    },
    Xor {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        rs2: GeneralRegister,
    },
    /* U-Type instructions */
    Lui {
        rd: GeneralRegister,
        imm: Imm<20>,
    },
    Auipc {
        rd: GeneralRegister,
        imm: Imm<20>,
    },
    /* I-Type instructions */
    Addi {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        imm: Imm<12>,
    },
    Xori {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        imm: Imm<12>,
    },
    Jalr {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        offset: Imm<12>,
    },
}

impl Instruction {
    pub fn execute(self, state: &mut Processor) -> Result<(), InstructionError> {
        match self {
            Instruction::Jal { rd, offset } => {
                let old_pc = state.pc;
                let new_pc = state.pc.wrapping_add(offset.get_sext());
                state.set_register(rd, old_pc + 4);
                state.pc = new_pc;
                Ok(())
            }
            Instruction::Add { rd, rs1, rs2 } => {
                let rs1 = state.get_register(rs1);
                let rs2 = state.get_register(rs2);
                state.set_register(rd, rs1.wrapping_add(rs2));
                Ok(())
            }
            Instruction::Sub { rd, rs1, rs2 } => {
                let rs1 = state.get_register(rs1);
                let rs2 = state.get_register(rs2);
                state.set_register(rd, rs1.wrapping_sub(rs2));
                Ok(())
            }
            Instruction::Xor { rd, rs1, rs2 } => {
                let rs1 = state.get_register(rs1);
                let rs2 = state.get_register(rs2);
                state.set_register(rd, rs1 ^ rs2);
                Ok(())
            }
            Instruction::Lui { rd, imm } => {
                state.set_register(rd, imm.get_sext());
                Ok(())
            }
            Instruction::Auipc { rd, imm } => {
                state.set_register(rd, state.pc + imm.get_sext() << 12);
                Ok(())
            }
            Instruction::Addi { rd, rs1, imm } => {
                let rs1 = state.get_register(rs1);
                state.set_register(rd, rs1.wrapping_add(imm.get_sext()));
                Ok(())
            }
            Instruction::Xori { rd, rs1, imm } => {
                let rs1 = state.get_register(rs1);
                state.set_register(rd, rs1 ^ imm.get_sext());
                Ok(())
            }
            Instruction::Jalr { rd, rs1, offset } => {
                let old_pc = state.pc;
                let rs1 = state.get_register(rs1);
                let new_pc = rs1.wrapping_add(offset.get_sext());
                state.set_register(rd, old_pc + 4);
                state.pc = new_pc;
                Ok(())
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
#[repr(transparent)]
/// Contains a N-bit wide immediate value
pub struct Imm<const WIDTH: usize>(RegisterVal);

impl<const WIDTH: usize> Imm<WIDTH> {
    /// The maximum possible value.
    pub const MAX: RegisterVal = ((1 as RegisterVal) << WIDTH) - 1;

    const SIGN_BIT: RegisterVal = (1 as RegisterVal) << WIDTH - 1;
    const EXTENSION: RegisterVal = RegisterVal::MAX ^ Self::MAX;

    pub fn new(val: RegisterVal) -> Option<Self> {
        (val <= Self::MAX).then_some(Self(val))
    }

    /// Get the value as [RegisterVal].
    /// The value is zero-extended.
    // NOTE: unused, but may be useful later.
    #[allow(dead_code)]
    pub fn get_zext(self) -> RegisterVal {
        self.0
    }

    /// Get the value as [RegisterVal].
    /// The value is sign-extended.
    pub fn get_sext(self) -> RegisterVal {
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

    use super::Imm;

    const SAMPLE_COUNT: usize = 10_000;

    #[test]
    fn test_imm_12_max() {
        for x in 0..=Imm::<12>::MAX {
            Imm::<12>::new(x).expect("Must succeed");
        }
        for _ in 0..SAMPLE_COUNT {
            let x = rand::random_range((Imm::<12>::MAX + 1)..RegisterVal::MAX);
            assert_eq!(Imm::<12>::new(x), None);
        }
    }

    #[test]
    fn test_sext_positive_12() {
        for x in 0..0x400 {
            let imm = Imm::<12>::new(x).unwrap();
            assert_eq!(x, imm.get_sext());
        }
    }

    #[test]
    fn test_sext_negative_12() {
        for x in 0..0x400 {
            let imm = Imm::<12>::new(x | 0x800).unwrap();
            let target = x | 0xffff_ffff_ffff_f800;
            assert_eq!(target, imm.get_sext(), "Imm value: {}", imm.get_zext());
        }
    }

    #[test]
    fn test_sext_positive_20() {
        for x in 0..0x4_0000 {
            let imm = Imm::<20>::new(x).unwrap();
            assert_eq!(x, imm.get_sext());
        }
    }

    #[test]
    fn test_sext_negative_20() {
        for x in 0..0x4_0000 {
            let imm = Imm::<20>::new(x | 0x8_0000).unwrap();
            let target = x | 0xffff_ffff_fff8_0000;
            assert_eq!(target, imm.get_sext(), "Imm value: {}", imm.get_zext());
        }
    }

    #[test]
    fn test_imm_20_max() {
        for x in 0..=Imm::<20>::MAX {
            Imm::<20>::new(x).expect("Must succeed");
        }
        for _ in 0..SAMPLE_COUNT {
            let x = rand::random_range((Imm::<20>::MAX + 1)..RegisterVal::MAX);
            assert_eq!(Imm::<20>::new(x), None);
        }
    }
}
