use crate::instruction::Instruction;
use crate::processor::Register;

pub fn decoder(instruction: u32) -> Option<Instruction> {
    let opcode = instruction & 0b1111111;
    match opcode {
        // 0b0110111 is LUI
        0b0110111 => {
            Some(
                Instruction::Lui {
                    rd: Register::from(((instruction << 7) & 0b11111) as u64),
                    imm: (instruction >> 12) as u64
                }
            )
        },
        // 0b1101111 is JAL
        0b1101111 => {
            let mut imm = 0;
            imm |= (instruction >> 31) << 20;
            imm |= (instruction << 12) & 0b11111111110000000000;
            imm |= (instruction << 21) & 0b100000000000;
            imm |= (instruction << 1) & 0b11111111110;
            Some(
                Instruction::Jal {
                    rd: Register::from(((instruction << 7) & 0b11111) as u64),
                    offset: imm as u64
                }
            )
        },
        // 0b1100111 is JALR
        0b1100111 => {
            Some(
                Instruction::Jalr {
                    rd: Register::from(((instruction << 7) & 0b11111) as u64),
                    rs1: Register::from(((instruction << 15) & 0b11111) as u64),
                    offset: (instruction >> 12) as u64
                }
            )
        },
        // 0b0010111 is AUIPC
        0b0010111 => {
            Some(
                Instruction::Auipc {
                    rd: Register::from(((instruction << 7) & 0b11111) as u64),
                    imm: (instruction >> 12) as u64
                }
            )
        },
        // 0b1100011 is imm r32i operations
        0b0010011 => {
            let additional_opcode = (instruction << 13) & 0b111;
            match additional_opcode {
                0b000 => {
                    Some(
                        Instruction::Addi {
                            rd: Register::from(((instruction << 7) & 0b11111) as u64),
                            rs1: Register::from(((instruction << 15) & 0b11111) as u64),
                            imm: (instruction >> 20) as u64
                        }
                    )
                },
                0b100 => {
                    Some(
                        Instruction::Xori {
                            rd: Register::from(((instruction << 7) & 0b11111) as u64),
                            rs1: Register::from(((instruction << 15) & 0b11111) as u64),
                            imm: (instruction >> 20) as u64
                        }
                    )
                },
                _ => None
            }
        },
        // 0b0110011 is non-imm r32i operations
        0b0110011 => {
            let additional_opcode = (instruction << 13) & 0b111;
            let additional_opcode2 = (instruction << 30) & 0b1;
            match additional_opcode {
                0b000 => {
                    match additional_opcode2 {
                        0b0 => Some(
                            Instruction::Add {
                                rd: Register::from(((instruction << 7) & 0b11111) as u64),
                                rs1: Register::from(((instruction << 15) & 0b11111) as u64),
                                rs2: Register::from(((instruction << 20) & 0b11111) as u64)
                            }
                        ),
                        0b1 => Some(
                            Instruction::Sub {
                                rd: Register::from(((instruction << 7) & 0b11111) as u64),
                                rs1: Register::from(((instruction << 15) & 0b11111) as u64),
                                rs2: Register::from(((instruction << 20) & 0b11111) as u64)
                            }
                        ),
                        _ => None
                    }
                },
                0b100 => {
                    Some(
                        Instruction::Xor {
                            rd: Register::from(((instruction << 7) & 0b11111) as u64),
                            rs1: Register::from(((instruction << 15) & 0b11111) as u64),
                            rs2: Register::from(((instruction << 20) & 0b11111) as u64)
                        }
                    )
                },
                _ => None
            }
        },
        _ => None
    }
}