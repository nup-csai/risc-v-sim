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
//! J-Type instructions have the following bit represenation.
//! The values in square brackets indicate what bits of the immediate
//! value are stored and in which order as such instructions do not
//! store them consecutively.
//!
//! ```pic
//! jal zero, 324
//! 00010100010000000000 00000 1101111
//! |                    |     | opcode
//! |                    | destination register
//! | immediate value [20 | 10:1 | 11 | 19:12]
//! ```
//!
//! Here is an example of the decoder decoding this instruction
//!
//! ```
//! # use risc_v_sim::kernel::{decode_instruction,Bit,GeneralRegister,Instruction};
//! let decoded = decode_instruction(0b00010100010000000000_00000_1101111).unwrap();
//! assert_eq!(decoded, Instruction::Jal {
//!     rd: GeneralRegister::ZERO,
//!     /// We extract the immediate value as-is, instead of getting it with 1-bit offset
//!     imm: Bit::new(324 >> 1).unwrap(),
//! });
//! ```
//!
//! ## R-Type
//!
//! R-Type instructions have the following bit representation
//!
//! ```pic
//! add tp, t1, ra
//! 0000000 00001 00110 000 00100 0110011
//! |       |     |     |   |     | opcode
//! |       |     |     |   | destination register
//! |       |     |     | funct 3
//! |       |     | source register 1
//! |       | source register 2
//! | funct 7
//! ```
//!
//! Here is an example of the decoder decoding this instruction
//!
//! ```
//! # use risc_v_sim::kernel::{decode_instruction,Bit,GeneralRegister,Instruction};
//! let decoded = decode_instruction(0b0000000_00001_00110_000_00100_0110011).unwrap();
//! assert_eq!(decoded, Instruction::Add {
//!     rd: GeneralRegister::TP,
//!     rs1: GeneralRegister::T1,
//!     rs2: GeneralRegister::RA,
//! });
//! ```
//!
//! ## U-Type
//!
//! U-Type instructions have the following bit representation
//!
//! ```pic
//! lui t1, 4587
//! 00000001000111101011 00110 0110111
//! |                    |     | opcode
//! |                    | destination register
//! | immediate value [31:12]
//! ```
//!
//! Here is an example of the decoder decoding this instruction
//!
//! ```
//! # use risc_v_sim::kernel::{decode_instruction,Bit,GeneralRegister,Instruction};
//! let decoded = decode_instruction(0b00000001000111101011_00110_0110111).unwrap();
//! assert_eq!(decoded, Instruction::Lui {
//!     rd: GeneralRegister::T1,
//!     /// RiscV documentation specified that this immediate value represents bits from 12 to 31.
//!     /// However, when using assembly, you specify this value as if the 12-bit offset does
//!     /// not exist. This why this value is the same as in the asm instruction above.
//!     imm: Bit::new(4587).unwrap(),
//! });
//! ```
//!
//! ## I-Type
//!
//! I-Type instructions have the following bit representation
//!
//! ```pic
//! addi a1, a2, 20
//! 000000010100 01100 000 01011 0010011
//! |            |     |   |     | opcode
//! |            |     |   | destination register
//! |            |     | funct 3
//! |            | source register
//! | immediate value [11:0]
//! ```
//!
//! Here is an example of the decoder decoding this instruction
//!
//! ```
//! # use risc_v_sim::kernel::{decode_instruction,Bit,GeneralRegister,Instruction};
//! let decoded = decode_instruction(0b000000010100_01100_000_01011_0010011).unwrap();
//! assert_eq!(decoded, Instruction::Addi {
//!     rd: GeneralRegister::A1,
//!     rs1: GeneralRegister::A2,
//!     imm: Bit::new(20).unwrap(),
//! });
//! ```
//!
//! ## S-Type
//!
//! S-Type instructions have the following bit representation
//!
//! ```pic
//! sw t2, 123(t0)
//! 0000011 00111 00101 010 11011 0100011
//! |       |     |     |   |     | opcode
//! |       |     |     |   | imm [0:4]
//! |       |     |     | funct 3
//! |       |     | rs1
//! |       | rs2
//! | imm [5:11]
//! ```
//!
//! Here is an example of the decoder decoding this instruction
//!
//! ```
//! # use risc_v_sim::kernel::{decode_instruction,Bit,GeneralRegister,Instruction};
//! let decoded = decode_instruction(0b0000011_00111_00101_010_11011_0100011).unwrap();
//! assert_eq!(decoded, Instruction::Sw {
//!     rs1: GeneralRegister::T0,
//!     rs2: GeneralRegister::T2,
//!     imm: Bit::new(123).unwrap(),
//! });
//! ```

use thiserror::Error;

use super::Bit;
use super::GeneralRegister;
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
    /// To figure out what instruction it is,
    /// you need to look at funct3.
    pub const I_ALU_OP: InstructionVal = 0b0010011;
    /// Opcode of [Instruction::Jalr]
    pub const JALR: InstructionVal = 0b1100111;
    /// Opcode of the following instructions
    /// * [Instruction::Lb]
    /// * [Instruction::Lh]
    /// * [Instruction::Lw]
    /// * [Instruction::Lbu]
    /// * [Instruction::Lhu]
    ///
    /// To figure out what instruction it is,
    /// you need to look at funct3.
    pub const LOAD_OP: InstructionVal = 0b0000011;

    /* S-type instructions */
    /// Opcode of the following instructions
    /// * [Instruction::Sb]
    /// * [Instruction::Sh]
    /// * [Instruction::Sw]
    ///
    /// To figure out what instruction it is,
    /// you need to look at funct3.
    pub const STORE_OP: InstructionVal = 0b0100011;

    pub const ALL_OPCODES: [InstructionVal; 8] =
        [JAL, R_ALU_OP, LUI, AUIPC, I_ALU_OP, JALR, LOAD_OP, STORE_OP];
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

    pub const ALL_FUNCT37: [(InstructionVal, InstructionVal); 3] = [
        (FUNCT3_ADD, FUNCT7_ADD),
        (FUNCT3_SUB, FUNCT7_SUB),
        (FUNCT3_XOR, FUNCT7_XOR),
    ];
}

/// [i_alu_op] contains `funct3` values
/// for instructions with opcode [opcodes::I_ALU_OP].
/// For more information, see the comment above that constant.
pub mod i_alu_op {
    use super::InstructionVal;

    pub const FUNCT3_ADDI: InstructionVal = 0b000;
    pub const FUNCT3_XORI: InstructionVal = 0b100;

    pub const ALL_FUNCT3: [InstructionVal; 2] = [FUNCT3_ADDI, FUNCT3_XORI];
}

/// [load_op] contains `funct3` values
/// for instructions with opcode [opcodes::LOAD_OP].
/// For more information, see the comment above that constant.
pub mod load_op {
    use super::InstructionVal;

    pub const FUNCT3_LB: InstructionVal = 0b000;
    pub const FUNCT3_LH: InstructionVal = 0b001;
    pub const FUNCT3_LW: InstructionVal = 0b010;
    pub const FUNCT3_LBU: InstructionVal = 0b100;
    pub const FUNCT3_LHU: InstructionVal = 0b101;

    pub const ALL_FUNCT3: [InstructionVal; 5] =
        [FUNCT3_LB, FUNCT3_LH, FUNCT3_LW, FUNCT3_LBU, FUNCT3_LHU];
}

/// [store_op] contains `funct3` values
/// for instructions with opcode [opcodes::STORE_OP].
/// For more information, see the comment above that constant.
pub mod store_op {
    use super::InstructionVal;

    pub const FUNCT3_SB: InstructionVal = 0b000;
    pub const FUNCT3_SH: InstructionVal = 0b001;
    pub const FUNCT3_SW: InstructionVal = 0b010;

    pub const ALL_FUNCT3: [InstructionVal; 3] = [FUNCT3_SB, FUNCT3_SH, FUNCT3_SW];
}

const REGISTER_MASK: InstructionVal = 0b11111;

/// [offsets] contains all the bit offsets for parts of an
/// instruction.
pub mod offsets {
    use super::InstructionVal;

    pub const OPCODE: InstructionVal = 0;
    pub const FUNCT3: InstructionVal = 12;
    pub const FUNCT7: InstructionVal = 25;
    pub const RD: InstructionVal = 7;
    pub const RS1: InstructionVal = 15;
    pub const RS2: InstructionVal = 20;
    pub const I_TYPE_IMM: InstructionVal = 20;
    pub const U_TYPE_IMM: InstructionVal = 12;
    pub const J_TYPE_IMM_0_9: InstructionVal = 21;
    pub const J_TYPE_IMM_10: InstructionVal = 20;
    pub const J_TYPE_IMM_11_18: InstructionVal = 12;
    pub const J_TYPE_IMM_19: InstructionVal = 31;
    pub const S_TYPE_IMM_0_4: InstructionVal = 7;
    pub const S_TYPE_IMM_5_11: InstructionVal = 25;
}

/// Decode a RiscV instruction.
pub const fn decode_instruction(instruction: InstructionVal) -> Result<Instruction, DecodeError> {
    let instruction = match get_opcode(instruction) {
        /* J-type instructions */
        opcodes::JAL => Instruction::Jal {
            rd: get_rd(instruction),
            imm: get_j_type_imm(instruction),
        },
        /* R-type instructions */
        opcodes::R_ALU_OP => match decode_r_alu_op(instruction) {
            Ok(x) => x,
            Err(e) => return Err(e),
        },
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
        opcodes::I_ALU_OP => match decode_i_alu_op(instruction) {
            Ok(x) => x,
            Err(e) => return Err(e),
        },
        opcodes::JALR => Instruction::Jalr {
            rd: get_rd(instruction),
            rs1: get_rs1(instruction),
            imm: get_i_type_imm(instruction),
        },
        opcodes::LOAD_OP => match decode_load_op(instruction) {
            Ok(x) => x,
            Err(e) => return Err(e),
        },
        /* S-type instructions */
        opcodes::STORE_OP => match decode_store_op(instruction) {
            Ok(x) => x,
            Err(e) => return Err(e),
        },
        opcode => return Err(DecodeError::UnknownOpcode(opcode)),
    };

    Ok(instruction)
}

/// Decode an instruction with opcode [opcodes::I_ALU_OP].
const fn decode_i_alu_op(instruction: InstructionVal) -> Result<Instruction, DecodeError> {
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
const fn decode_r_alu_op(instruction: InstructionVal) -> Result<Instruction, DecodeError> {
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

/// Decode an instruction with opcode [opcodes::LOAD_OP].
const fn decode_load_op(instruction: InstructionVal) -> Result<Instruction, DecodeError> {
    let funct3 = get_funct3(instruction);
    let rd = get_rd(instruction);
    let rs1 = get_rs1(instruction);
    let imm = get_i_type_imm(instruction);

    let instruction = match funct3 {
        load_op::FUNCT3_LB => Instruction::Lb { rd, rs1, imm },
        load_op::FUNCT3_LH => Instruction::Lh { rd, rs1, imm },
        load_op::FUNCT3_LW => Instruction::Lw { rd, rs1, imm },
        load_op::FUNCT3_LBU => Instruction::Lbu { rd, rs1, imm },
        load_op::FUNCT3_LHU => Instruction::Lhu { rd, rs1, imm },
        funct3 => return Err(DecodeError::UnknownLoadOp { funct3 }),
    };

    Ok(instruction)
}

/// Decode an instruction with opcode [opcodes::STORE_OP].
const fn decode_store_op(instruction: InstructionVal) -> Result<Instruction, DecodeError> {
    let funct3 = get_funct3(instruction);
    let rs1 = get_rs1(instruction);
    let rs2 = get_rs2(instruction);
    let imm = get_s_type_imm(instruction);

    let instruction = match funct3 {
        store_op::FUNCT3_SB => Instruction::Sb { rs1, rs2, imm },
        store_op::FUNCT3_SH => Instruction::Sh { rs1, rs2, imm },
        store_op::FUNCT3_SW => Instruction::Sw { rs1, rs2, imm },
        funct3 => return Err(DecodeError::UnknownStoreOp { funct3 }),
    };

    Ok(instruction)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Error)]
pub enum DecodeError {
    #[error("Unkown instruction opcode: {0:#x}")]
    UnknownOpcode(InstructionVal),
    #[error("Unkown r ALU op funct values: {funct3:#x} and {funct7:#x}")]
    UnknownRAluOp {
        funct3: InstructionVal,
        funct7: InstructionVal,
    },
    #[error("Unkown i ALU op funct3 value: {funct3:#x}")]
    UnknownIAluOp { funct3: InstructionVal },
    #[error("Unkown load op funct3 value: {funct3:#x}")]
    UnknownLoadOp { funct3: InstructionVal },
    #[error("Unkown store op funct3 value: {funct3:#x}")]
    UnknownStoreOp { funct3: InstructionVal },
}

/// Get the opcode field.
/// This field is present in all instruction types.
const fn get_opcode(instruction: InstructionVal) -> InstructionVal {
    (instruction >> offsets::OPCODE) & 0b1111111
}

/// Get the func3 field. Applicable to R, I, S, B instructions.
/// The value is placed into the lowest bits of [InstructionVal].
const fn get_funct3(instruction: InstructionVal) -> InstructionVal {
    (instruction >> offsets::FUNCT3) & 0b111
}

/// Get the func7 field. Applicable to R instructions.
/// The value is placed into the lowest bits of [InstructionVal].
const fn get_funct7(instruction: InstructionVal) -> InstructionVal {
    (instruction >> offsets::FUNCT7) & 0b1111111
}

/// Get the rd field. Applicable to R, I, U, J instructions.
/// The value is placed into the lowest bits of [InstructionVal].
/// The result is immediately wrapped with [GeneralRegister] for
/// convenience.
const fn get_rd(instruction: InstructionVal) -> GeneralRegister {
    let raw = (instruction >> offsets::RD) & REGISTER_MASK;
    GeneralRegister::new(raw).unwrap()
}

/// Get the rs1 field. Applicable to R, I, S, B instructions.
/// The value is placed into the lowest bits of [InstructionVal].
/// The result is immediately wrapped with [GeneralRegister] for
/// convenience.
const fn get_rs1(instruction: InstructionVal) -> GeneralRegister {
    let raw = (instruction >> offsets::RS1) & REGISTER_MASK;
    GeneralRegister::new(raw).unwrap()
}

/// Get the rs2 field. Applicable to R, S, B instructions.
/// The value is placed into the lowest bits of [InstructionVal].
/// The result is immediately wrapped with [GeneralRegister] for
/// convenience.
const fn get_rs2(instruction: InstructionVal) -> GeneralRegister {
    let raw = (instruction >> offsets::RS2) & REGISTER_MASK;
    GeneralRegister::new(raw).unwrap()
}

/// Get the immediate value. Applicable to I instructions ONLY.
/// The value is placed into the lowest bits of [InstructionVal].
/// The value is not sign-extended.
/// The result is immediately wrapped with [Bit] for convenience.
const fn get_i_type_imm(instruction: InstructionVal) -> Bit<12> {
    Bit::new((instruction >> offsets::I_TYPE_IMM) as RegisterVal).unwrap()
}

/// Get the immediate value. Applicable to U instructions ONLY.
/// The value is placed into the lowest bits of [InstructionVal].
/// The value is not sign-extended.
/// The result is immediately wrapped with [Bit] for convenience.
const fn get_u_type_imm(instruction: InstructionVal) -> Bit<20> {
    Bit::new((instruction >> offsets::U_TYPE_IMM) as RegisterVal).unwrap()
}

/// Get the immediate value. Applicable to J instructions ONLY.
/// The value is placed into the lowest bits of [InstructionVal].
/// The value is not sign-extended.
/// The result is immediately wrapped with [Bit] for convenience.
const fn get_j_type_imm(instruction: InstructionVal) -> Bit<20> {
    let imm_0_9 = (instruction & 0x7FE0_0000) >> offsets::J_TYPE_IMM_0_9;
    let imm_10 = (instruction & 0x0010_0000) >> offsets::J_TYPE_IMM_10;
    let imm_11_18 = (instruction & 0x000F_F000) >> offsets::J_TYPE_IMM_11_18;
    let imm_19 = (instruction & 0x8000_0000) >> offsets::J_TYPE_IMM_19;
    let raw = (imm_0_9 << 0) | (imm_10 << 10) | (imm_11_18 << 11) | (imm_19 << 19);
    Bit::new(raw as RegisterVal).unwrap()
}

/// Get the immediate value. Applicable to S instructions ONLY.
/// The value is placed into the lowest bits of [InstructionVal].
/// The value is not sign-extended.
/// The result is immediately wrapped with [Imm] for convenience.
const fn get_s_type_imm(instruction: InstructionVal) -> Bit<12> {
    let imm_0_4 = (instruction & 0x0000_0F80) >> offsets::S_TYPE_IMM_0_4;
    let imm_5_11 = (instruction & 0xFE00_0000) >> offsets::S_TYPE_IMM_5_11;
    let raw = (imm_0_4 << 0) | (imm_5_11 << 5);
    Bit::new(raw as RegisterVal).unwrap()
}

/// Encode an instruction back into its [InstructionVal] representation.
/// The returned value is guaranteed to be parseable back into [Instruction]
/// and is also a valid RiscV instruction.
pub const fn encode_instruction(instruction: Instruction) -> InstructionVal {
    match instruction {
        /* J-type instructions */
        Instruction::Jal { rd, imm } => {
            let imm = imm.get_zext() as InstructionVal;
            let imm_0_9 = (imm & 0x0000_03FF) >> 0;
            let imm_10 = (imm & 0x0000_0400) >> 10;
            let imm_11_18 = (imm & 0x0007_F800) >> 11;
            let imm_19 = (imm & 0x0008_0000) >> 19;

            let mut out = 0;
            out |= opcodes::JAL;
            out |= rd.get() << offsets::RD;
            out |= imm_11_18 << offsets::J_TYPE_IMM_11_18;
            out |= imm_10 << offsets::J_TYPE_IMM_10;
            out |= imm_0_9 << offsets::J_TYPE_IMM_0_9;
            out |= imm_19 << offsets::J_TYPE_IMM_19;
            out
        }
        /* R-type instructions */
        Instruction::Add { rd, rs1, rs2 } => {
            encode_r_alu_op(rd, r_alu_op::FUNCT3_ADD, rs1, rs2, r_alu_op::FUNCT7_ADD)
        }
        Instruction::Sub { rd, rs1, rs2 } => {
            encode_r_alu_op(rd, r_alu_op::FUNCT3_SUB, rs1, rs2, r_alu_op::FUNCT7_SUB)
        }
        Instruction::Xor { rd, rs1, rs2 } => {
            encode_r_alu_op(rd, r_alu_op::FUNCT3_XOR, rs1, rs2, r_alu_op::FUNCT7_XOR)
        }
        /* U-type instructions */
        Instruction::Lui { rd, imm } => encode_u_instr(opcodes::LUI, rd, imm),
        Instruction::Auipc { rd, imm } => encode_u_instr(opcodes::AUIPC, rd, imm),
        /* I-type instructions */
        Instruction::Addi { rd, rs1, imm } => encode_i_alu_op(rd, i_alu_op::FUNCT3_ADDI, rs1, imm),
        Instruction::Xori { rd, rs1, imm } => encode_i_alu_op(rd, i_alu_op::FUNCT3_XORI, rs1, imm),
        Instruction::Jalr { rd, rs1, imm } => {
            let mut out = 0;
            out |= opcodes::JALR << offsets::OPCODE;
            out |= rd.get() << offsets::RD;
            out |= rs1.get() << offsets::RS1;
            out |= (imm.get_zext() as InstructionVal) << offsets::I_TYPE_IMM;
            out
        }
        Instruction::Lb { rd, rs1, imm } => encode_load_op(rd, load_op::FUNCT3_LB, rs1, imm),
        Instruction::Lh { rd, rs1, imm } => encode_load_op(rd, load_op::FUNCT3_LH, rs1, imm),
        Instruction::Lw { rd, rs1, imm } => encode_load_op(rd, load_op::FUNCT3_LW, rs1, imm),
        Instruction::Lbu { rd, rs1, imm } => encode_load_op(rd, load_op::FUNCT3_LBU, rs1, imm),
        Instruction::Lhu { rd, rs1, imm } => encode_load_op(rd, load_op::FUNCT3_LHU, rs1, imm),
        /* S-type instructions */
        Instruction::Sb { rs1, rs2, imm } => encode_store_op(store_op::FUNCT3_SB, rs1, rs2, imm),
        Instruction::Sh { rs1, rs2, imm } => encode_store_op(store_op::FUNCT3_SH, rs1, rs2, imm),
        Instruction::Sw { rs1, rs2, imm } => encode_store_op(store_op::FUNCT3_SW, rs1, rs2, imm),
    }
}

const fn encode_r_alu_op(
    rd: GeneralRegister,
    funct3: InstructionVal,
    rs1: GeneralRegister,
    rs2: GeneralRegister,
    funct7: InstructionVal,
) -> InstructionVal {
    let mut out = 0;
    out |= opcodes::R_ALU_OP << offsets::OPCODE;
    out |= rd.get() << offsets::RD;
    out |= funct3 << offsets::FUNCT3;
    out |= rs1.get() << offsets::RS1;
    out |= rs2.get() << offsets::RS2;
    out |= funct7 << offsets::FUNCT7;
    out
}

const fn encode_u_instr(
    opcode: InstructionVal,
    rd: GeneralRegister,
    imm: Bit<20>,
) -> InstructionVal {
    let mut out = 0;
    out |= opcode << offsets::OPCODE;
    out |= rd.get() << offsets::RD;
    out |= (imm.get_zext() as InstructionVal) << offsets::U_TYPE_IMM;
    out
}

const fn encode_i_alu_op(
    rd: GeneralRegister,
    funct3: InstructionVal,
    rs1: GeneralRegister,
    imm: Bit<12>,
) -> InstructionVal {
    let mut out = 0;
    out |= opcodes::I_ALU_OP << offsets::OPCODE;
    out |= rd.get() << offsets::RD;
    out |= funct3 << offsets::FUNCT3;
    out |= rs1.get() << offsets::RS1;
    out |= (imm.get_zext() as InstructionVal) << offsets::I_TYPE_IMM;
    out
}

const fn encode_load_op(
    rd: GeneralRegister,
    funct3: InstructionVal,
    rs1: GeneralRegister,
    imm: Bit<12>,
) -> InstructionVal {
    let mut out = 0;
    out |= opcodes::LOAD_OP << offsets::OPCODE;
    out |= rd.get() << offsets::RD;
    out |= funct3 << offsets::FUNCT3;
    out |= rs1.get() << offsets::RS1;
    out |= (imm.get_zext() as InstructionVal) << offsets::I_TYPE_IMM;
    out
}

const fn encode_store_op(
    funct3: InstructionVal,
    rs1: GeneralRegister,
    rs2: GeneralRegister,
    imm: Bit<12>,
) -> InstructionVal {
    let imm = imm.get_zext() as InstructionVal;
    let imm_0_4 = (imm & 0x0000_001F) >> 0;
    let imm_5_11 = (imm & 0x0000_0FE0) >> 5;

    let mut out = 0;
    out |= opcodes::STORE_OP << offsets::OPCODE;
    out |= imm_0_4 << offsets::S_TYPE_IMM_0_4;
    out |= funct3 << offsets::FUNCT3;
    out |= rs1.get() << offsets::RS1;
    out |= rs2.get() << offsets::RS2;
    out |= imm_5_11 << offsets::S_TYPE_IMM_5_11;
    out
}

#[cfg(test)]
mod tests {
    use crate::kernel::{encode_instruction, load_op, Bit, InstructionVal, RegisterVal};

    use super::{
        get_funct3, get_funct7, get_opcode, i_alu_op, opcodes, r_alu_op, store_op, DecodeError,
    };
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
            let decoded = super::decode_instruction(t.input);
            assert_eq!(decoded, t.expected);
            assert_eq!(
                encode_instruction(decoded.unwrap()),
                t.input,
                "failed to decode-encode instruction: {:#b}",
                t.input
            );
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
    fn test_simple_negative_parse_store_op() {
        for t in test_data_bad_store_op_instr() {
            assert_eq!(
                super::decode_instruction(t.input),
                t.expected,
                "Input {:#x}",
                t.input
            );
        }
    }

    #[test]
    fn test_simple_negative_parse_load_op() {
        for t in test_data_bad_load_op_instr() {
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
                    imm: bit(162),
                }),
            },
            ParseTest {
                input: 0b00010100010000000000_00101_1101111,
                expected: Ok(Instruction::Jal {
                    rd: reg_x(5),
                    imm: bit(162),
                }),
            },
            ParseTest {
                input: 0b11111111000111111111_00000_1101111,
                expected: Ok(Instruction::Jal {
                    rd: reg_x(0),
                    imm: bit(0xf_fff8),
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
                    imm: bit(4587),
                }),
            },
            ParseTest {
                input: 0b00000001001100010111_01100_0010111,
                expected: Ok(Instruction::Auipc {
                    rd: reg_x(12),
                    imm: bit(4887),
                }),
            },
            /* I-Type instructions */
            ParseTest {
                input: 0b000000010100_01100_000_01011_0010011,
                expected: Ok(Instruction::Addi {
                    rd: reg_x(11),
                    rs1: reg_x(12),
                    imm: bit(20),
                }),
            },
            ParseTest {
                input: 0b110110000000_11101_100_00101_0010011,
                expected: Ok(Instruction::Xori {
                    rd: reg_x(5),
                    rs1: reg_x(29),
                    imm: bit(3456),
                }),
            },
            ParseTest {
                input: 0b000011111111_00101_000_01010_1100111,
                expected: Ok(Instruction::Jalr {
                    rd: reg_x(10),
                    rs1: reg_x(5),
                    imm: bit(255),
                }),
            },
            ParseTest {
                input: 0b000010000100_00110_000_00101_0000011,
                expected: Ok(Instruction::Lb {
                    rd: reg_x(5),
                    rs1: reg_x(6),
                    imm: bit(132),
                }),
            },
            ParseTest {
                input: 0b111111111111_11111_001_11100_0000011,
                expected: Ok(Instruction::Lh {
                    rd: reg_x(28),
                    rs1: reg_x(31),
                    imm: bit(0xFFF),
                }),
            },
            ParseTest {
                input: 0b000000000010_01011_010_01110_0000011,
                expected: Ok(Instruction::Lw {
                    rd: reg_x(14),
                    rs1: reg_x(11),
                    imm: bit(2),
                }),
            },
            ParseTest {
                input: 0b000000000001_01110_100_01111_0000011,
                expected: Ok(Instruction::Lbu {
                    rd: reg_x(15),
                    rs1: reg_x(14),
                    imm: bit(1),
                }),
            },
            ParseTest {
                input: 0b000000000100_01111_101_01111_0000011,
                expected: Ok(Instruction::Lhu {
                    rd: reg_x(15),
                    rs1: reg_x(15),
                    imm: bit(4),
                }),
            },
            /* S-Type instructions */
            ParseTest {
                input: 0b000001100101_00111_000_11011_0100011,
                expected: Ok(Instruction::Sb {
                    rs1: reg_x(7),
                    rs2: reg_x(5),
                    imm: bit(123),
                }),
            },
            ParseTest {
                input: 0b111111111111_00000_001_11111_0100011,
                expected: Ok(Instruction::Sh {
                    rs1: reg_x(0),
                    rs2: reg_x(31),
                    imm: bit(4095),
                }),
            },
            ParseTest {
                input: 0b111111111111_00000_010_11111_0100011,
                expected: Ok(Instruction::Sw {
                    rs1: reg_x(0),
                    rs2: reg_x(31),
                    imm: bit(4095),
                }),
            },
        ]
    }

    /// Shortcut function that panics if `v` is not a valid Bit<N> value.
    fn bit<const WIDTH: usize>(v: RegisterVal) -> Bit<{ WIDTH }> {
        Bit::new(v).expect("bad bit value")
    }

    /// Shortcut function that panics if `v` is not a valid reg index.
    fn reg_x(v: InstructionVal) -> GeneralRegister {
        GeneralRegister::new(v).expect("Bad register value")
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
        let funct3 = get_bad_i_alu_op_funct3();
        let rest = rand::random::<InstructionVal>() & 0xffff_8f80;

        opcodes::I_ALU_OP | rest | funct3
    }

    fn get_bad_i_alu_op_funct3() -> InstructionVal {
        // FIXME: this sampling might be suboptimal, because
        // we are actually trying to randomize only the funct3 bits
        loop {
            let funct3 = rand::random::<InstructionVal>();
            if !i_alu_op::ALL_FUNCT3.contains(&super::get_funct3(funct3)) {
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
        let funct37 = get_bad_r_alu_op_funct37();
        let rest = rand::random::<InstructionVal>() & 0x01ff_8f80;

        opcodes::R_ALU_OP | rest | funct37
    }

    fn get_bad_r_alu_op_funct37() -> InstructionVal {
        // FIXME: this sampling might be suboptimal, because
        // we are actually trying to randomize only the funct37 bits
        loop {
            let funct37 = rand::random::<InstructionVal>();
            let funct3 = super::get_funct3(funct37);
            let funct7 = super::get_funct7(funct37);
            if !r_alu_op::ALL_FUNCT37.contains(&(funct3, funct7)) {
                return funct37 & 0xfe00_7000;
            }
        }
    }

    /// This testdata is a bunch of negative test cases, where the decoder
    /// should fail.
    fn test_data_bad_store_op_instr() -> impl IntoIterator<Item = ParseTest> {
        // TODO: seed the RNG
        (0..SAMPLE_COUNT)
            .map(|_| get_bad_store_op_instr())
            .map(|bad_instr| ParseTest {
                input: bad_instr,
                expected: Err(DecodeError::UnknownStoreOp {
                    funct3: get_funct3(bad_instr),
                }),
            })
    }

    fn get_bad_store_op_instr() -> InstructionVal {
        let funct3 = get_bad_store_op_funct3();
        let rest = rand::random::<InstructionVal>() & 0xffff_8f80;

        opcodes::STORE_OP | rest | funct3
    }

    fn get_bad_store_op_funct3() -> InstructionVal {
        // FIXME: this sampling might be suboptimal, because
        // we are actually trying to randomize only the funct3 bits
        loop {
            let funct3 = rand::random::<InstructionVal>();
            if !store_op::ALL_FUNCT3.contains(&super::get_funct3(funct3)) {
                return funct3 & 0x0000_7000;
            }
        }
    }
    /// This testdata is a bunch of negative test cases, where the decoder
    /// should fail.
    fn test_data_bad_load_op_instr() -> impl IntoIterator<Item = ParseTest> {
        // TODO: seed the RNG
        (0..SAMPLE_COUNT)
            .map(|_| get_bad_load_op_instr())
            .map(|bad_instr| ParseTest {
                input: bad_instr,
                expected: Err(DecodeError::UnknownLoadOp {
                    funct3: get_funct3(bad_instr),
                }),
            })
    }

    fn get_bad_load_op_instr() -> InstructionVal {
        let funct3 = get_bad_load_op_funct3();
        let rest = rand::random::<InstructionVal>() & 0xffff_8f80;

        opcodes::LOAD_OP | rest | funct3
    }

    fn get_bad_load_op_funct3() -> InstructionVal {
        // FIXME: this sampling might be suboptimal, because
        // we are actually trying to randomize only the funct3 bits
        loop {
            let funct3 = rand::random::<InstructionVal>();
            if !load_op::ALL_FUNCT3.contains(&super::get_funct3(funct3)) {
                return funct3 & 0x0000_7000;
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
        // FIXME: this sampling might be suboptimal, because
        // we are actually trying to randomize only the lower 7 bits
        loop {
            let opcode = super::get_opcode(rand::random::<InstructionVal>());
            if !opcodes::ALL_OPCODES.contains(&opcode) {
                return opcode;
            }
        }
    }
}
