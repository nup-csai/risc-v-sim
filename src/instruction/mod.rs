use thiserror::Error;

use crate::processor::{Processor, ProcessorError};

#[derive(Error, Debug)]
pub enum InstructionError {
    #[error("Attempted to overflow program counter")]
    OverflowPC,

    #[error("Processor error: {0}")]
    ProcessorError(ProcessorError),
}

#[derive(Clone, Copy, Debug)]
pub enum Instruction {
    Add { rd: u64, rs1: u64, rs2: u64 },
    Sub { rd: u64, rs1: u64, rs2: u64 },
    Addi { rd: u64, rs1: u64, imm: u64 },
    Subi { rd: u64, rs1: u64, imm: u64 },
    Lui { rd: u64, imm: u64 },
    Xor { rd: u64, rs1: u64, rs2: u64 },
    Xori { rd: u64, rs1: u64, imm: u64 },
    Jal { rd: u64, offset: u64 },
    Jalr { rd: u64, rs1: u64, offset: u64 },
    Auipc { rd: u64, imm: u64 },
}

fn sext(imm: u64) -> u64 {
    let sign_bit = 1 << 11;
    let mask = !0 << 12;
    if imm & sign_bit != 0 {
        imm | mask
    } else {
        imm
    }
}

impl From<ProcessorError> for InstructionError {
    fn from(error: ProcessorError) -> Self {
        InstructionError::ProcessorError(error)
    }
}

impl Instruction {
    pub fn execute(self, state: &mut Processor) -> Result<(), InstructionError> {
        match self {
            Instruction::Add { rd, rs1, rs2 } => {
                let rs1 = state.get_register(rs1)?;
                let rs2 = state.get_register(rs2)?;
                state.set_register(rd, rs1.wrapping_add(rs2))?;
                Ok(())
            }
            Instruction::Sub { rd, rs1, rs2 } => {
                let rs1 = state.get_register(rs1)?;
                let rs2 = state.get_register(rs2)?;
                state.set_register(rd, rs1.wrapping_sub(rs2))?;
                Ok(())
            }
            Instruction::Addi { rd, rs1, imm } => {
                let rs1 = state.get_register(rs1)?;
                state.set_register(rd, rs1.wrapping_add(sext(imm)))?;
                Ok(())
            }
            Instruction::Subi { rd, rs1, imm } => {
                let rs1 = state.get_register(rs1)?;
                state.set_register(rd, rs1.wrapping_sub(sext(imm)))?;
                Ok(())
            }
            Instruction::Lui { rd, imm } => {
                state.set_register(rd, sext(imm))?;
                Ok(())
            }
            Instruction::Xor { rd, rs1, rs2 } => {
                let rs1 = state.get_register(rs1)?;
                let rs2 = state.get_register(rs2)?;
                state.set_register(rd, rs1 ^ rs2)?;
                Ok(())
            }
            Instruction::Xori { rd, rs1, imm } => {
                let rs1 = state.get_register(rs1)?;
                state.set_register(rd, rs1 ^ sext(imm))?;
                Ok(())
            }
            Instruction::Jal { rd, offset } => {
                let old_pc = state.get_pc() + 4;
                let (new_pc, overflow) = rd.overflowing_add(offset);
                if overflow {
                    // does nothing yet, will have some functional to handle this later
                }
                state.set_register(rd, old_pc + 4)?;
                state.set_pc(new_pc);
                Ok(())
            }
            Instruction::Jalr { rd, rs1, offset } => {
                let old_pc = state.get_pc() + 4;
                let rs1 = state.get_register(rs1)?;
                let (new_pc, overflow) = rs1.overflowing_add(offset);
                if overflow {
                    // does nothing yet, will have some functional to handle this later
                }
                state.set_register(rd, old_pc + 4)?;
                state.set_pc(new_pc);
                Ok(())
            }
            Instruction::Auipc { rd, imm } => {
                let cur_pc = state.get_pc();
                state.set_register(rd, cur_pc + sext(imm) << 12)?;
                Ok(())
            }
        }
    }
}
