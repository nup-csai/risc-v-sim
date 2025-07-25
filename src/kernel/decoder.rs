//! This module contains the decoder of the RiscV instructions.
//! It does not support the compressed instructions. For a list
//! of the supported instructions, please consult the [Instruction]
//! type.
//!
//! # RiscV instructions
//!
//! This section lists instruction types and their bit representation.
//! This bits are going from highest to lowest from left to right.
//!
//! ## J-Type
//!
//! J-Type instructions have the following bit represenation
//!
//! ```
//! 00010100010000000000 00000 1101111
//! |                    |     | opcode
//! |                    | source register
//! | immediate value
//! ```
//!
//! ## R-Type
//!
//! R-Type instructions have the following bit representation
//!
//! ```
//! 0000000 00001 00110 000 00100 0110011
//! |       |     |     |   |     | opcode
//! |       |     |     |   | destination register
//! |       |     |     | funct 3
//! |       |     | source register 1
//! |       | source register 2
//! | funct 7
//! ```
//!
//! ## U-Type
//!
//! U-Type instructions have the following bit representation
//!
//! ```
//! 00000001000111101011 00110 0110111
//! |                    |     | opcode
//! |                    | destination register
//! | immediate value
//! ```
//!
//! ## I-Type
//!
//! I-Type instructions have the following bit representation
//!
//! ```
//! 000000010100 01100 000 01011 0010011
//! |            |     |   |     | opcode
//! |            |     |   | destination register
//! |            |     | funct 3
//! |            | source register
//! | immediate value
//! ```

use thiserror::Error;

use super::GeneralRegister;
use super::Imm;
use super::Instruction;
use super::InstructionVal;
use super::RegisterVal;

/// [opcodes] module contains constants of opcodes for [Instruction].
pub mod opcodes {
    #[allow(unused_imports)]
    use super::Instruction;
    use super::InstructionVal;

    /* J-type instructions */
    /// Opcode of [Instruction::Jal]
    pub const JAL: InstructionVal = 0b1101111;

    /* R-type instructions */
    /// Opcode of the following instructions:
    /// * [Instruction::Add]
    /// * [Instruction::Sub]
    /// * [Instruction::Xor]
    ///
    /// To figure our what instruction it is,
    /// you need to look at funct3 and funct7.
    pub const R_ALU_OP: InstructionVal = 0b0110011;

    /* U-type instructions */
    /// Opcode of [Instruction::Lui]
    pub const LUI: InstructionVal = 0b0110111;
    /// Opcode of [Instruction::Auipc]
    pub const AUIPC: InstructionVal = 0b0010111;

    /* I-type instructions */
    /// Opcode of the following instructions:
    /// * [Instruction::Addi]
    /// * [Instruction::Xori]
    ///
    /// To figure our what instruction it is,
    /// you need to look at funct3.
    pub const I_ALU_OP: InstructionVal = 0b0010011;
    /// Opcode of [Instruction::Jalr]
    pub const JALR: InstructionVal = 0b1100111;
}

/// [r_alu_op] contains `funct3` and `funct7` values
/// for instructions with opcode [opcodes::R_ALU_OP].
/// For more information, see the comment above that constant.
pub mod r_alu_op {
    use super::InstructionVal;

    /* Codes for ADD */
    pub const FUNCT3_ADD: InstructionVal = 0b000;
    pub const FUNCT7_ADD: InstructionVal = 0b0000000;

    /* Codes for SUB */
    pub const FUNCT3_SUB: InstructionVal = 0b000;
    pub const FUNCT7_SUB: InstructionVal = 0b0100000;

    /* Codes for XOR */
    pub const FUNCT3_XOR: InstructionVal = 0b100;
    pub const FUNCT7_XOR: InstructionVal = 0b0000000;
}

/// [i_alu_op] contains `funct3` values
/// for instructions with opcode [opcodes::I_ALU_OP].
/// For more information, see the comment above that constant.
pub mod i_alu_op {
    use super::InstructionVal;

    pub const FUNCT3_ADDI: InstructionVal = 0b000;
    pub const FUNCT3_XORI: InstructionVal = 0b100;
}

const REGISTER_MASK: InstructionVal = 0b11111;

/// Decode a RiscV instruction.
pub fn decode_instruction(instruction: InstructionVal) -> Result<Instruction, DecodeError> {
    let instruction = match get_opcode(instruction) {
        /* J-type instructions */
        opcodes::JAL => Instruction::Jal {
            rd: get_rd(instruction),
            offset: get_j_type_imm(instruction),
        },
        /* R-type instructions */
        opcodes::R_ALU_OP => decode_r_alu_op(instruction)?,
        /* U-type instructions */
        opcodes::LUI => Instruction::Lui {
            rd: get_rd(instruction),
            imm: get_u_type_imm(instruction),
        },
        opcodes::AUIPC => Instruction::Auipc {
            rd: get_rd(instruction),
            imm: get_u_type_imm(instruction),
        },
        /* I-type instructions */
        opcodes::I_ALU_OP => decode_i_alu_op(instruction)?,
        opcodes::JALR => Instruction::Jalr {
            rd: get_rd(instruction),
            rs1: get_rs1(instruction),
            offset: get_i_type_imm(instruction),
        },
        opcode => return Err(DecodeError::UnknownOpcode(opcode)),
    };

    Ok(instruction)
}

/// Decode an instruction with opcode [opcodes::I_ALU_OP].
fn decode_i_alu_op(instruction: InstructionVal) -> Result<Instruction, DecodeError> {
    let funct3 = get_funct3(instruction);
    let rd = get_rd(instruction);
    let rs1 = get_rs1(instruction);
    let imm = get_i_type_imm(instruction);

    let instruction = match funct3 {
        i_alu_op::FUNCT3_ADDI => Instruction::Addi { rd, rs1, imm },
        i_alu_op::FUNCT3_XORI => Instruction::Xori { rd, rs1, imm },
        funct3 => return Err(DecodeError::UnknownIAluOp { funct3 }),
    };

    Ok(instruction)
}

/// Decode an instruction with opcode [opcodes::R_ALU_OP].
fn decode_r_alu_op(instruction: InstructionVal) -> Result<Instruction, DecodeError> {
    let funct3_7 = (get_funct3(instruction), get_funct7(instruction));
    let rd = get_rd(instruction);
    let rs1 = get_rs1(instruction);
    let rs2 = get_rs2(instruction);

    let instruction = match funct3_7 {
        (r_alu_op::FUNCT3_ADD, r_alu_op::FUNCT7_ADD) => Instruction::Add { rd, rs1, rs2 },
        (r_alu_op::FUNCT3_SUB, r_alu_op::FUNCT7_SUB) => Instruction::Sub { rd, rs1, rs2 },
        (r_alu_op::FUNCT3_XOR, r_alu_op::FUNCT7_XOR) => Instruction::Xor { rd, rs1, rs2 },
        (funct3, funct7) => return Err(DecodeError::UnknownRAluOp { funct3, funct7 }),
    };

    Ok(instruction)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Error)]
pub enum DecodeError {
    #[error("Unkown instruction opcode: {0:#x}")]
    UnknownOpcode(u32),
    #[error("Unkown r ALU op funct values: {funct3:#x} and {funct7:#x}")]
    UnknownRAluOp { funct3: u32, funct7: u32 },
    #[error("Unkown i ALU op funct3 value: {funct3:#x}")]
    UnknownIAluOp { funct3: u32 },
}

/// Get the opcode field.
/// This field is present in all instruction types.
fn get_opcode(instruction: InstructionVal) -> InstructionVal {
    instruction & 0b1111111
}

/// Get the func3 field. Applicable to R, I, S, B instructions.
/// The value is placed into the lowest bits of [InstructionVal].
fn get_funct3(instruction: InstructionVal) -> InstructionVal {
    (instruction >> 12) & 0b111
}

/// Get the func7 field. Applicable to R instructions.
/// The value is placed into the lowest bits of [InstructionVal].
fn get_funct7(instruction: InstructionVal) -> InstructionVal {
    (instruction >> 25) & 0b1111111
}

/// Get the rd field. Applicable to R, I, U, J instructions.
/// The value is placed into the lowest bits of [InstructionVal].
/// The result is immediately wrapped with [GeneralRegister] for
/// convenience.
fn get_rd(instruction: InstructionVal) -> GeneralRegister {
    let raw = (instruction >> 7) & REGISTER_MASK;
    GeneralRegister::new(raw).unwrap()
}

/// Get the rs1 field. Applicable to R, I, S, B instructions.
/// The value is placed into the lowest bits of [InstructionVal].
/// The result is immediately wrapped with [GeneralRegister] for
/// convenience.
fn get_rs1(instruction: InstructionVal) -> GeneralRegister {
    let raw = (instruction >> 15) & REGISTER_MASK;
    GeneralRegister::new(raw).unwrap()
}

/// Get the rs2 field. Applicable to R, S, B instructions.
/// The value is placed into the lowest bits of [InstructionVal].
/// The result is immediately wrapped with [GeneralRegister] for
/// convenience.
fn get_rs2(instruction: InstructionVal) -> GeneralRegister {
    let raw = (instruction >> 20) & REGISTER_MASK;
    GeneralRegister::new(raw).unwrap()
}

/// Get the immediate value. Applicable to I instructions ONLY.
/// The value is placed into the lowest bits of [InstructionVal].
/// The value is not sign-extended.
/// The result is immediately wrapped with [Imm] for convenience.
fn get_i_type_imm(instruction: InstructionVal) -> Imm<12> {
    Imm::new((instruction >> 20) as RegisterVal).unwrap()
}

/// Get the immediate value. Applicable to U instructions ONLY.
/// The value is placed into the lowest bits of [InstructionVal].
/// The value is not sign-extended.
/// The result is immediately wrapped with [Imm] for convenience.
fn get_u_type_imm(instruction: InstructionVal) -> Imm<20> {
    Imm::new((instruction >> 12) as RegisterVal).unwrap()
}

/// Get the immediate value. Applicable to J instructions ONLY.
/// The value is placed into the lowest bits of [InstructionVal].
/// The value is not sign-extended.
/// The result is immediately wrapped with [Imm] for convenience.
fn get_j_type_imm(instruction: InstructionVal) -> Imm<20> {
    let imm_1_10 = (instruction & 0x7FC0_0000) >> 21;
    let imm_11 = (instruction & 0x0010_0000) >> 20;
    let imm_12_19 = (instruction & 0x000F_F000) >> 12;
    let imm_20 = (instruction & 0x8000_0000) >> 30;
    let raw = (imm_1_10 << 1) | (imm_11 << 11) | (imm_12_19 << 12) | (imm_20 << 20);
    Imm::new(raw as RegisterVal).unwrap()
}

#[cfg(test)]
mod tests {
    use crate::kernel::{Imm, InstructionVal, RegisterVal};

    use super::{get_funct3, get_funct7, get_opcode, i_alu_op, opcodes, r_alu_op, DecodeError};
    use super::{GeneralRegister, Instruction};

    const SAMPLE_COUNT: usize = 1000;

    #[derive(Debug, Clone, Copy)]
    struct ParseTest {
        input: InstructionVal,
        expected: Result<Instruction, DecodeError>,
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
                input: 0b00010100010000000000_00000_1101111,
                expected: Ok(Instruction::Jal {
                    rd: reg_x(0),
                    offset: imm(324),
                }),
            },
            ParseTest {
                input: 0b00010100010000000000_001011_101111,
                expected: Ok(Instruction::Jal {
                    rd: reg_x(5),
                    offset: imm(324),
                }),
            },
            /* R-Type instructions */
            ParseTest {
                input: 0b0000000_00001_00110_000_00100_0110011,
                expected: Ok(Instruction::Add {
                    rd: reg_x(4),
                    rs1: reg_x(6),
                    rs2: reg_x(1),
                }),
            },
            ParseTest {
                input: 0b0100000_11100_00000_000_00101_0110011,
                expected: Ok(Instruction::Sub {
                    rd: reg_x(5),
                    rs1: reg_x(0),
                    rs2: reg_x(28),
                }),
            },
            ParseTest {
                input: 0b0000000_01001_01000_100_00011_0110011,
                expected: Ok(Instruction::Xor {
                    rd: reg_x(3),
                    rs1: reg_x(8),
                    rs2: reg_x(9),
                }),
            },
            /* U-Type instructions */
            ParseTest {
                input: 0b00000001000111101011_00110_0110111,
                expected: Ok(Instruction::Lui {
                    rd: reg_x(6),
                    imm: imm(4587),
                }),
            },
            ParseTest {
                input: 0b00000001001100010111_01100_0010111,
                expected: Ok(Instruction::Auipc {
                    rd: reg_x(12),
                    imm: imm(4887),
                }),
            },
            /* I-Type instructions */
            ParseTest {
                input: 0b000000010100_01100_000_01011_0010011,
                expected: Ok(Instruction::Addi {
                    rd: reg_x(11),
                    rs1: reg_x(12),
                    imm: imm(20),
                }),
            },
            ParseTest {
                input: 0b110110000000_11101_100_00101_0010011,
                expected: Ok(Instruction::Xori {
                    rd: reg_x(5),
                    rs1: reg_x(29),
                    imm: imm(3456),
                }),
            },
            ParseTest {
                input: 0b000011111111_00101_000_01010_1100111,
                expected: Ok(Instruction::Jalr {
                    rd: reg_x(10),
                    rs1: reg_x(5),
                    offset: imm(255),
                }),
            },
        ]
    }

    /// Shortcut function that panics if `v` is not a valid imm value.
    fn imm<const WIDTH: usize>(v: RegisterVal) -> Imm<{ WIDTH }> {
        Imm::new(v).unwrap()
    }

    /// Shortcut function that panics if `v` is not a valid reg index.
    fn reg_x(v: InstructionVal) -> GeneralRegister {
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
                expected: Err(DecodeError::UnknownIAluOp {
                    funct3: get_funct3(bad_instr),
                }),
            })
    }

    fn get_bad_i_alu_instr() -> InstructionVal {
        let funct3 = get_bad_funct3();
        let rest = rand::random::<InstructionVal>() & 0xffff_8f80;

        opcodes::I_ALU_OP | rest | funct3
    }

    fn get_bad_funct3() -> InstructionVal {
        let good_functs = [i_alu_op::FUNCT3_ADDI, i_alu_op::FUNCT3_XORI];

        // FIXME: this sampling might be suboptimal, because
        // we are actually trying to randomize only the funct3 bits
        loop {
            let funct3 = rand::random::<InstructionVal>();
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
                expected: Err(DecodeError::UnknownRAluOp {
                    funct3: get_funct3(bad_instr),
                    funct7: get_funct7(bad_instr),
                }),
            })
    }

    fn get_bad_r_alu_instr() -> InstructionVal {
        let funct37 = get_bad_funct37();
        let rest = rand::random::<InstructionVal>() & 0x01ff_8f80;

        opcodes::R_ALU_OP | rest | funct37
    }

    fn get_bad_funct37() -> InstructionVal {
        let good_functs = [
            (r_alu_op::FUNCT3_ADD, r_alu_op::FUNCT7_ADD),
            (r_alu_op::FUNCT3_SUB, r_alu_op::FUNCT7_SUB),
            (r_alu_op::FUNCT3_XOR, r_alu_op::FUNCT7_XOR),
        ];

        // FIXME: this sampling might be suboptimal, because
        // we are actually trying to randomize only the funct37 bits
        loop {
            let funct37 = rand::random::<InstructionVal>();
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
                expected: Err(DecodeError::UnknownOpcode(get_opcode(bad_instr))),
            })
    }

    fn get_bad_opcode_instr() -> InstructionVal {
        let opcode = get_bad_opcode();
        let other = rand::random::<InstructionVal>() & !0b1111111;

        opcode | other
    }

    fn get_bad_opcode() -> InstructionVal {
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
            let opcode = super::get_opcode(rand::random::<InstructionVal>());
            if !good_opcodes.contains(&opcode) {
                return opcode;
            }
        }
    }
}
