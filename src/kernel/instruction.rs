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
        offset: RegisterVal,
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
        imm: RegisterVal,
    },
    Auipc {
        rd: GeneralRegister,
        imm: RegisterVal,
    },
    /* I-Type instructions */
    Addi {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        imm: RegisterVal,
    },
    Xori {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        imm: RegisterVal,
    },
    Jalr {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        offset: RegisterVal,
    },
}

fn sext(imm: RegisterVal) -> RegisterVal {
    let sign_bit = 1 << 11;
    let mask = !0 << 12;
    if imm & sign_bit != 0 {
        imm | mask
    } else {
        imm
    }
}

impl Instruction {
    pub fn execute(self, state: &mut Processor) -> Result<(), InstructionError> {
        match self {
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
            Instruction::Addi { rd, rs1, imm } => {
                let rs1 = state.get_register(rs1);
                state.set_register(rd, rs1.wrapping_add(sext(imm)));
                Ok(())
            }
            Instruction::Lui { rd, imm } => {
                state.set_register(rd, sext(imm));
                Ok(())
            }
            Instruction::Xor { rd, rs1, rs2 } => {
                let rs1 = state.get_register(rs1);
                let rs2 = state.get_register(rs2);
                state.set_register(rd, rs1 ^ rs2);
                Ok(())
            }
            Instruction::Xori { rd, rs1, imm } => {
                let rs1 = state.get_register(rs1);
                state.set_register(rd, rs1 ^ sext(imm));
                Ok(())
            }
            Instruction::Jal { rd, offset } => {
                let old_pc = state.pc;
                let new_pc = state.pc.wrapping_add(sext(offset));
                state.set_register(rd, old_pc + 4);
                state.pc = new_pc;
                Ok(())
            }
            Instruction::Jalr { rd, rs1, offset } => {
                let old_pc = state.pc;
                let rs1 = state.get_register(rs1);
                let new_pc = rs1.wrapping_add(offset);
                state.set_register(rd, old_pc + 4);
                state.pc = new_pc;
                Ok(())
            }
            Instruction::Auipc { rd, imm } => {
                state.set_register(rd, state.pc + sext(imm) << 12);
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod tsets {
    use super::sext;

    #[test]
    fn test_sext_positive() {
        for x in 0..0x400 {
            assert_eq!(x, sext(x));
        }
    }

    #[test]
    fn test_sext_negative() {
        for x in 0..0x400 {
            let imm = x | 0x800;
            let target = x | 0xffff_ffff_ffff_f800;
            assert_eq!(target, sext(imm), "Imm value: {imm}");
        }
    }
}
