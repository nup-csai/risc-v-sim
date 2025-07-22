use crate::instruction::Instruction;
use crate::processor::GeneralRegister;

pub mod opcodes {
    /* J-type instructions */
    pub const JAL: u32 = 0b1101111;

    /* R-type instructions */
    pub const R_ALU_OP: u32 = 0b0110011;

    /* U-type instructions */
    pub const LUI: u32 = 0b0110111;
    pub const AUIPC: u32 = 0b0010111;

    /* I-type instructions */
    pub const I_ALU_OP: u32 = 0b0010011;
    pub const JALR: u32 = 0b1100111;
}

pub mod r_alu_op {
    /* Codes for ADD */
    pub const FUNCT3_ADD: u32 = 0b000;
    pub const FUNCT7_ADD: u32 = 0b0000000;

    /* Codes for SUB */
    pub const FUNCT3_SUB: u32 = 0b000;
    pub const FUNCT7_SUB: u32 = 0b0100000;

    /* Codes for XOR */
    pub const FUNCT3_XOR: u32 = 0b100;
    pub const FUNCT7_XOR: u32 = 0b0000000;
}

pub mod i_alu_op {
    pub const FUNCT3_ADDI: u32 = 0b000;
    pub const FUNCT3_XORI: u32 = 0b100;
}

const REGISTER_MASK: u32 = 0b11111;

pub fn decode_instruction(instruction: u32) -> Option<Instruction> {
    let instruction = match get_opcode(instruction) {
        /* J-type instructions */
        opcodes::JAL => Instruction::Jal {
            rd: GeneralRegister::new(get_rd(instruction))?,
            offset: get_j_type_imm(instruction) as u64,
        },
        /* R-type instructions */
        opcodes::R_ALU_OP => decode_r_alu_op(instruction)?,
        /* U-type instructions */
        opcodes::LUI => Instruction::Lui {
            rd: GeneralRegister::new(get_rd(instruction))?,
            imm: get_u_type_imm(instruction) as u64,
        },
        opcodes::AUIPC => Instruction::Auipc {
            rd: GeneralRegister::new(get_rd(instruction))?,
            imm: get_u_type_imm(instruction) as u64,
        },
        /* I-type instructions */
        opcodes::I_ALU_OP => decode_i_alu_op(instruction)?,
        opcodes::JALR => Instruction::Jalr {
            rd: GeneralRegister::new(get_rd(instruction))?,
            rs1: GeneralRegister::new(get_rs1(instruction))?,
            offset: get_i_type_imm(instruction) as u64,
        },
        _ => return None,
    };

    Some(instruction)
}

fn decode_i_alu_op(instruction: u32) -> Option<Instruction> {
    let funct3 = get_funct3(instruction);
    let rd = GeneralRegister::new(get_rd(instruction))?;
    let rs1 = GeneralRegister::new(get_rs1(instruction))?;
    let imm = get_i_type_imm(instruction) as u64;

    let instruction = match funct3 {
        i_alu_op::FUNCT3_ADDI => Instruction::Addi { rd, rs1, imm },
        i_alu_op::FUNCT3_XORI => Instruction::Xori { rd, rs1, imm },
        _ => return None,
    };

    Some(instruction)
}

fn decode_r_alu_op(instruction: u32) -> Option<Instruction> {
    let funct3_7 = (get_funct3(instruction), get_funct7(instruction));
    let rd = GeneralRegister::new(get_rd(instruction))?;
    let rs1 = GeneralRegister::new(get_rs1(instruction))?;
    let rs2 = GeneralRegister::new(get_rs2(instruction))?;

    let instruction = match funct3_7 {
        (r_alu_op::FUNCT3_ADD, r_alu_op::FUNCT7_ADD) => Instruction::Add { rd, rs1, rs2 },
        (r_alu_op::FUNCT3_SUB, r_alu_op::FUNCT7_SUB) => Instruction::Sub { rd, rs1, rs2 },
        (r_alu_op::FUNCT3_XOR, r_alu_op::FUNCT7_XOR) => Instruction::Xor { rd, rs1, rs2 },
        _ => return None,
    };

    Some(instruction)
}

fn get_opcode(instruction: u32) -> u32 {
    instruction & 0b1111111
}

/// Get the func3 field. Applicable to R, I, S, B instructions.
/// The value is placed into the lowest bits of u32.
fn get_funct3(instruction: u32) -> u32 {
    (instruction >> 12) & 0b111
}

/// Get the func7 field. Applicable to R instructions.
/// The value is placed into the lowest bits of u32.
fn get_funct7(instruction: u32) -> u32 {
    (instruction >> 25) & 0b1111111
}

/// Get the rd field. Applicable to R, I, U, J instructions.
/// The value is placed into the lowest bits of u32.
fn get_rd(instruction: u32) -> u32 {
    (instruction >> 7) & REGISTER_MASK
}

/// Get the rs1 field. Applicable to R, I, S, B instructions.
/// The value is placed into the lowest bits of u32.
fn get_rs1(instruction: u32) -> u32 {
    (instruction >> 15) & REGISTER_MASK
}

/// Get the rs2 field. Applicable to R, S, B instructions.
/// The value is placed into the lowest bits of u32.
fn get_rs2(instruction: u32) -> u32 {
    (instruction >> 20) & REGISTER_MASK
}

/// Get the immediate value. Applicable to I instructions ONLY.
/// The value is placed into the lowest bits of u32.
/// The value is not sign-extended.
fn get_i_type_imm(instruction: u32) -> u32 {
    (instruction >> 20) as u32
}

/// Get the immediate value. Applicable to U instructions ONLY.
/// The value is placed into the lowest bits of u32.
/// The value is not sign-extended.
fn get_u_type_imm(instruction: u32) -> u32 {
    (instruction >> 12) as u32
}

/// Get the immediate value. Applicable to J instructions ONLY.
/// The value is placed into the lowest bits of u32.
/// The value is not sign-extended.
fn get_j_type_imm(instruction: u32) -> u32 {
    let imm_1_10 = (instruction & 0x7FC0_0000) >> 21;
    let imm_11 = (instruction & 0x0010_0000) >> 20;
    let imm_12_19 = (instruction & 0x000F_F000) >> 12;
    let imm_20 = (instruction & 0x8000_0000) >> 30;

    (imm_1_10 << 1) | (imm_11 << 11) | (imm_12_19 << 12) | (imm_20 << 20)
}

#[cfg(test)]
mod tests {
    use super::{i_alu_op, opcodes, r_alu_op};
    use crate::{instruction::Instruction, processor::GeneralRegister};

    const SAMPLE_COUNT: usize = 1000;

    #[derive(Debug, Clone, Copy)]
    struct ParseTest {
        input: u32,
        expected: Option<Instruction>,
    }

    #[test]
    fn test_simple_positive_parse() {
        for t in test_data_good() {
            assert_eq!(super::decode_instruction(t.input), t.expected);
        }
    }

    #[test]
    fn test_simple_negative_parse_i_op() {
        for t in test_data_bad_i_alu_instr() {
            assert_eq!(
                super::decode_instruction(t.input),
                t.expected,
                "Input {:#x}",
                t.input
            );
        }
    }

    #[test]
    fn test_simple_negative_parse_r_op() {
        for t in test_data_bad_r_alu_instr() {
            assert_eq!(
                super::decode_instruction(t.input),
                t.expected,
                "Input {:#x}",
                t.input
            );
        }
    }

    #[test]
    fn test_simple_negative_parse_opcode() {
        for t in test_data_bad_opcode() {
            assert_eq!(
                super::decode_instruction(t.input),
                t.expected,
                "Input {:#x}",
                t.input
            );
        }
    }

    /// This testdata is a bunch of positive cases where the decoder should return a
    /// successful result.
    /// This test data should include samples of all instructions supported by the simulator.
    /// Use this tool to debug failing tests: https://luplab.gitlab.io/rvcodecjs.
    fn test_data_good() -> impl IntoIterator<Item = ParseTest> {
        // NOTE: please keep the type ordering the same as in
        // the parser implementation.
        vec![
            /* J-Type instructions */
            ParseTest {
                input: 0x1440_006f,
                expected: Some(Instruction::Jal {
                    rd: reg_x(0),
                    offset: 324,
                }),
            },
            ParseTest {
                input: 0x144_002ef,
                expected: Some(Instruction::Jal {
                    rd: reg_x(5),
                    offset: 324,
                }),
            },
            /* R-Type instructions */
            ParseTest {
                input: 0x0013_0233,
                expected: Some(Instruction::Add {
                    rd: reg_x(4),
                    rs1: reg_x(6),
                    rs2: reg_x(1),
                }),
            },
            ParseTest {
                input: 0x41c0_02b3,
                expected: Some(Instruction::Sub {
                    rd: reg_x(5),
                    rs1: reg_x(0),
                    rs2: reg_x(28),
                }),
            },
            ParseTest {
                input: 0x0094_41b3,
                expected: Some(Instruction::Xor {
                    rd: reg_x(3),
                    rs1: reg_x(8),
                    rs2: reg_x(9),
                }),
            },
            /* U-Type instructions */
            ParseTest {
                input: 0x011e_b337,
                expected: Some(Instruction::Lui {
                    rd: reg_x(6),
                    imm: 4587,
                }),
            },
            ParseTest {
                input: 0x0131_7617,
                expected: Some(Instruction::Auipc {
                    rd: reg_x(12),
                    imm: 4887,
                }),
            },
            /* I-Type instructions */
            ParseTest {
                input: 0x0146_0593,
                expected: Some(Instruction::Addi {
                    rd: reg_x(11),
                    rs1: reg_x(12),
                    imm: 20,
                }),
            },
            ParseTest {
                input: 0x0d80_ec293,
                expected: Some(Instruction::Xori {
                    rd: reg_x(5),
                    rs1: reg_x(29),
                    imm: 3456,
                }),
            },
            ParseTest {
                input: 0x0ff2_8567,
                expected: Some(Instruction::Jalr {
                    rd: reg_x(10),
                    rs1: reg_x(5),
                    offset: 255,
                }),
            },
        ]
    }

    /// Shortcut function that panics if `v` is not a valid reg index.
    fn reg_x(v: u32) -> GeneralRegister {
        GeneralRegister::new(v).unwrap()
    }

    /// This testdata is a bunch of negative test cases, where the decoder
    /// should fail.
    fn test_data_bad_i_alu_instr() -> impl IntoIterator<Item = ParseTest> {
        // TODO: seed the RNG
        (0..SAMPLE_COUNT)
            .map(|_| get_bad_i_alu_instr())
            .map(|bad_instr| ParseTest {
                input: bad_instr,
                expected: None,
            })
    }

    fn get_bad_i_alu_instr() -> u32 {
        let funct3 = get_bad_funct3();
        let rest = rand::random::<u32>() & 0xffff_8f80;

        opcodes::I_ALU_OP | rest | funct3
    }

    fn get_bad_funct3() -> u32 {
        let good_functs = [i_alu_op::FUNCT3_ADDI, i_alu_op::FUNCT3_XORI];

        // FIXME: this sampling might be suboptimal, because
        // we are actually trying to randomize only the funct3 bits
        loop {
            let funct3 = rand::random::<u32>();
            if !good_functs.contains(&super::get_funct3(funct3)) {
                return funct3 & 0x0000_7000;
            }
        }
    }

    /// This testdata is a bunch of negative test cases, where the decoder
    /// should fail.
    fn test_data_bad_r_alu_instr() -> impl IntoIterator<Item = ParseTest> {
        // TODO: seed the RNG
        (0..SAMPLE_COUNT)
            .map(|_| get_bad_r_alu_instr())
            .map(|bad_instr| ParseTest {
                input: bad_instr,
                expected: None,
            })
    }

    fn get_bad_r_alu_instr() -> u32 {
        let funct37 = get_bad_funct37();
        let rest = rand::random::<u32>() & 0x01ff_8f80;

        opcodes::R_ALU_OP | rest | funct37
    }

    fn get_bad_funct37() -> u32 {
        let good_functs = [
            (r_alu_op::FUNCT3_ADD, r_alu_op::FUNCT7_ADD),
            (r_alu_op::FUNCT3_SUB, r_alu_op::FUNCT7_SUB),
            (r_alu_op::FUNCT3_XOR, r_alu_op::FUNCT7_XOR),
        ];

        // FIXME: this sampling might be suboptimal, because
        // we are actually trying to randomize only the funct37 bits
        loop {
            let funct37 = rand::random::<u32>();
            let funct3 = super::get_funct3(funct37);
            let funct7 = super::get_funct7(funct37);
            if !good_functs.contains(&(funct3, funct7)) {
                return funct37 & 0xfe00_7000;
            }
        }
    }

    /// This testdata is a bunch of negative test cases, where the decoder
    /// should fail.
    fn test_data_bad_opcode() -> impl IntoIterator<Item = ParseTest> {
        // TODO: seed the RNG
        (0..SAMPLE_COUNT)
            .map(|_| get_bad_opcode_instr())
            .map(|bad_instr| ParseTest {
                input: bad_instr,
                expected: None,
            })
    }

    fn get_bad_opcode_instr() -> u32 {
        let opcode = get_bad_opcode();
        let other = rand::random::<u32>() & !0b1111111;

        opcode | other
    }

    fn get_bad_opcode() -> u32 {
        let good_opcodes = [
            opcodes::JAL,
            opcodes::R_ALU_OP,
            opcodes::LUI,
            opcodes::AUIPC,
            opcodes::I_ALU_OP,
            opcodes::JALR,
        ];

        // FIXME: this sampling might be suboptimal, because
        // we are actually trying to randomize only the lower 7 bits
        loop {
            let opcode = super::get_opcode(rand::random::<u32>());
            if !good_opcodes.contains(&opcode) {
                return opcode;
            }
        }
    }
}
