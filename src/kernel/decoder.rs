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
//! # use risc_v_sim::kernel::{decode_instruction,Bit,RegId,Instruction};
//! let decoded = decode_instruction(0b00010100010000000000_00000_1101111).unwrap();
//! assert_eq!(decoded, Instruction::Jal(
//!     RegId::ZERO,
//!     /// We extract the immediate value as-is, instead of getting it with 1-bit offset
//!     Bit::new(324 >> 1).unwrap(),
//! ));
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
//! # use risc_v_sim::kernel::{decode_instruction,Bit,RegId,Instruction};
//! let decoded = decode_instruction(0b0000000_00001_00110_000_00100_0110011).unwrap();
//! assert_eq!(decoded, Instruction::Add(RegId::TP, RegId::T1, RegId::RA));
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
//! # use risc_v_sim::kernel::{decode_instruction,Bit,RegId,Instruction};
//! let decoded = decode_instruction(0b00000001000111101011_00110_0110111).unwrap();
//! assert_eq!(decoded, Instruction::Lui(
//!     RegId::T1,
//!     /// RiscV documentation specified that this immediate value represents bits from 12 to 31.
//!     /// However, when using assembly, you specify this value as if the 12-bit offset does
//!     /// not exist. This why this value is the same as in the asm instruction above.
//!     Bit::new(4587).unwrap(),
//! ));
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
//! # use risc_v_sim::kernel::{decode_instruction,Bit,RegId,Instruction};
//! let decoded = decode_instruction(0b000000010100_01100_000_01011_0010011).unwrap();
//! assert_eq!(decoded, Instruction::Addi(
//!     RegId::A1,
//!     RegId::A2,
//!     Bit::new(20).unwrap(),
//! ));
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
//! # use risc_v_sim::kernel::{decode_instruction,Bit,RegId,Instruction};
//! let decoded = decode_instruction(0b0000011_00111_00101_010_11011_0100011).unwrap();
//! assert_eq!(decoded, Instruction::Sw(
//!     RegId::T0,
//!     RegId::T2,
//!     Bit::new(123).unwrap(),
//! ));
//! ```

use thiserror::Error;

use crate::c_try;

use super::{Bit, InstrVal, Instruction, RegId, RegVal};

#[derive(Clone, Copy, PartialEq, Eq, Debug, Error)]
pub enum DecodeError {
    #[error("Unkown instruction opcode: {0:#x}")]
    UnknownOpcode(InstrVal),
    #[error("Unkown r ALU op funct values: {funct3:#x} and {funct7:#x}")]
    UnknownRAluOp { funct3: InstrVal, funct7: InstrVal },
    #[error("Unkown i ALU op funct3 value: {funct3:#x}")]
    UnknownIAluOp { funct3: InstrVal },
    #[error("Unkown load op funct3 value: {funct3:#x}")]
    UnknownLoadOp { funct3: InstrVal },
    #[error("Unkown store op funct3 value: {funct3:#x}")]
    UnknownStoreOp { funct3: InstrVal },
    #[error("Unknown bitwise shift type: {shtyp:#x}")]
    UnknownShtyp { shtyp: InstrVal },
}

type Result<T> = std::result::Result<T, DecodeError>;

/// [opcodes] module contains constants of opcodes for [Instruction].
pub mod opcodes {
    use super::InstrVal;
    #[allow(unused_imports)]
    use super::Instruction;

    /* J-type instructions */
    /// Opcode of [Instruction::Jal]
    pub const JAL: InstrVal = 0b1101111;

    /* R-type instructions */
    /// Opcode for register-register integer operations:
    /// * [Instruction::Add]
    /// * [Instruction::Sub]
    /// * [Instruction::Xor]
    ///
    /// To figure our what instruction it is,
    /// you need to look at funct3 and funct7.
    /// The name has been taken from RiscV book.
    pub const OP: InstrVal = 0b0110011;

    /* U-type instructions */
    /// Opcode of [Instruction::Lui]
    pub const LUI: InstrVal = 0b0110111;
    /// Opcode of [Instruction::Auipc]
    pub const AUIPC: InstrVal = 0b0010111;

    /* I-type instructions */
    /// Opcode of the following instructions:
    /// * [Instruction::Addi]
    /// * [Instruction::Xori]
    /// * [Instruction::Ori]
    /// * [Instruction::Andi]
    /// * [Instruction::Slli]
    /// * [Instruction::Srli]
    /// * [Instruction::Srai]
    /// * [Instruction::Slti]
    /// * [Instruction::Sltiu]
    ///
    /// To figure out what instruction it is,
    /// you need to look at funct3.
    /// The name has been taken from RiscV book.
    pub const OP_IMM: InstrVal = 0b0010011;
    /// Opcode of [Instruction::Jalr]
    pub const JALR: InstrVal = 0b1100111;
    /// Opcode of the following instructions
    /// * [Instruction::Lb]
    /// * [Instruction::Lh]
    /// * [Instruction::Lw]
    /// * [Instruction::Lbu]
    /// * [Instruction::Lhu]
    ///
    /// To figure out what instruction it is,
    /// you need to look at funct3.
    pub const LOAD: InstrVal = 0b0000011;

    /* S-type instructions */
    /// Opcode of the following instructions
    /// * [Instruction::Sb]
    /// * [Instruction::Sh]
    /// * [Instruction::Sw]
    ///
    /// To figure out what instruction it is,
    /// you need to look at funct3.
    pub const STORE: InstrVal = 0b0100011;

    pub const ALL_OPCODES: [InstrVal; 8] =
        [JAL, OP, LUI, AUIPC, OP_IMM, JALR, LOAD, STORE];
}

/// [op] contains `funct3` and `funct7` values
/// for instructions with opcode [opcodes::OP].
/// For more information, see the comment above that constant.
pub mod op {
    use super::InstrVal;

    /* Codes for ADD */
    pub const FUNCT3_ADD: InstrVal = 0b000;
    pub const FUNCT7_ADD: InstrVal = 0b0000000;

    /* Codes for SUB */
    pub const FUNCT3_SUB: InstrVal = 0b000;
    pub const FUNCT7_SUB: InstrVal = 0b0100000;

    /* Codes for XOR */
    pub const FUNCT3_XOR: InstrVal = 0b100;
    pub const FUNCT7_XOR: InstrVal = 0b0000000;

    pub const ALL_FUNCT37: [(InstrVal, InstrVal); 3] =
        [(FUNCT3_ADD, FUNCT7_ADD), (FUNCT3_SUB, FUNCT7_SUB), (FUNCT3_XOR, FUNCT7_XOR)];
}

/// [op_imm] contains `funct3` values
/// for instructions with opcode [opcodes::OP_IMM].
/// For more information, see the comment above that constant.
pub mod op_imm {
    #[allow(unused_imports)]
    use super::srli_srai_shtyp;
    use super::InstrVal;

    pub const FUNCT3_ADDI: InstrVal = 0b000;
    pub const FUNCT3_XORI: InstrVal = 0b100;
    pub const FUNCT3_ORI: InstrVal = 0b110;
    pub const FUNCT3_ANDI: InstrVal = 0b111;
    pub const FUNCT3_SLLI: InstrVal = 0b001;
    /// This funct3 represents two operations. SRLI and SRAI
    /// are special as their immediate value is actualy split
    /// into two values known as "shtyp" and "shamt".
    ///
    /// To figure out which one is it, consult values in
    /// [srli_srai_shtyp].
    pub const FUNCT3_SRLI_SRAI: InstrVal = 0b101;
    pub const FUNCT3_SLTI: InstrVal = 0b010;
    pub const FUNCT3_SLTIU: InstrVal = 0b011;

    pub const ALL_FUNCT3: [InstrVal; 8] = [
        FUNCT3_ADDI,
        FUNCT3_XORI,
        FUNCT3_ANDI,
        FUNCT3_ORI,
        FUNCT3_SLLI,
        FUNCT3_SRLI_SRAI,
        FUNCT3_SLTI,
        FUNCT3_SLTIU,
    ];
}

/// The shtyp values for deciding if an instruction is
/// a SRLI or SRAI.
pub mod srli_srai_shtyp {
    use crate::kernel::InstrVal;

    pub const SHTYP_SRLI: InstrVal = 0b0000000;
    pub const SHTYP_SRAI: InstrVal = 0b0100000;

    pub const ALL_SHTYP: [InstrVal; 2] = [SHTYP_SRLI, SHTYP_SRAI];
}

/// [load] contains `funct3` values
/// for instructions with opcode [opcodes::LOAD].
/// For more information, see the comment above that constant.
pub mod load {
    use super::InstrVal;

    pub const FUNCT3_LB: InstrVal = 0b000;
    pub const FUNCT3_LH: InstrVal = 0b001;
    pub const FUNCT3_LW: InstrVal = 0b010;
    pub const FUNCT3_LBU: InstrVal = 0b100;
    pub const FUNCT3_LHU: InstrVal = 0b101;

    pub const ALL_FUNCT3: [InstrVal; 5] =
        [FUNCT3_LB, FUNCT3_LH, FUNCT3_LW, FUNCT3_LBU, FUNCT3_LHU];
}

/// [store] contains `funct3` values
/// for instructions with opcode [opcodes::STORE].
/// For more information, see the comment above that constant.
pub mod store {
    use super::InstrVal;

    pub const FUNCT3_SB: InstrVal = 0b000;
    pub const FUNCT3_SH: InstrVal = 0b001;
    pub const FUNCT3_SW: InstrVal = 0b010;

    pub const ALL_FUNCT3: [InstrVal; 3] = [FUNCT3_SB, FUNCT3_SH, FUNCT3_SW];
}

const REGISTER_MASK: InstrVal = 0b11111;

/// [offsets] contains all the bit offsets for parts of an
/// instruction.
pub mod offsets {
    use super::InstrVal;

    pub const FUNCT3: InstrVal = 12;
    pub const FUNCT7: InstrVal = 25;
    pub const RD: InstrVal = 7;
    pub const RS1: InstrVal = 15;
    pub const RS2: InstrVal = 20;
    pub const I_TYPE_IMM: InstrVal = 20;
    pub const I_TYPE_SHIFT_AMOUNT: InstrVal = 20;
    pub const I_TYPE_SHIFT_TYPE: InstrVal = 25;
    pub const U_TYPE_IMM: InstrVal = 12;
    pub const J_TYPE_IMM_0_9: InstrVal = 21;
    pub const J_TYPE_IMM_10: InstrVal = 20;
    pub const J_TYPE_IMM_11_18: InstrVal = 12;
    pub const J_TYPE_IMM_19: InstrVal = 31;
    pub const S_TYPE_IMM_0_4: InstrVal = 7;
    pub const S_TYPE_IMM_5_11: InstrVal = 25;
}

/// Decode a RiscV instruction.
pub const fn decode_instruction(code: InstrVal) -> Result<Instruction> {
    use Instruction::*;

    let instruction = match get_opcode(code) {
        opcodes::JAL => Jal(get_rd(code), get_j_imm(code)),
        opcodes::OP => c_try!(decode_op(code)),
        opcodes::LUI => Lui(get_rd(code), get_u_imm(code)),
        opcodes::AUIPC => Auipc(get_rd(code), get_u_imm(code)),
        opcodes::OP_IMM => c_try!(decode_op_imm(code)),
        opcodes::JALR => Jalr(get_rd(code), get_rs1(code), get_i_imm(code)),
        opcodes::LOAD => c_try!(decode_load(code)),
        opcodes::STORE => c_try!(decode_store(code)),
        opcode => return Err(DecodeError::UnknownOpcode(opcode)),
    };

    Ok(instruction)
}

/// Decode an instruction with opcode [opcodes::OP_IMM].
const fn decode_op_imm(instruction: InstrVal) -> Result<Instruction> {
    use Instruction::*;

    let funct3 = get_funct3(instruction);
    let rd = get_rd(instruction);
    let rs1 = get_rs1(instruction);
    let imm = get_i_imm(instruction);

    let instruction = match funct3 {
        op_imm::FUNCT3_ADDI => Addi(rd, rs1, imm),
        op_imm::FUNCT3_XORI => Xori(rd, rs1, imm),
        op_imm::FUNCT3_ANDI => Andi(rd, rs1, imm),
        op_imm::FUNCT3_ORI => Ori(rd, rs1, imm),
        op_imm::FUNCT3_SLLI => Slli(rd, rs1, imm),
        op_imm::FUNCT3_SRLI_SRAI => c_try!(decode_srli_srai(instruction)),
        op_imm::FUNCT3_SLTI => Slti(rd, rs1, imm),
        op_imm::FUNCT3_SLTIU => Sltiu(rd, rs1, imm),
        funct3 => return Err(DecodeError::UnknownIAluOp { funct3 }),
    };

    Ok(instruction)
}

/// Decode an op_imm with funct3 [op_imm::FUNCT3_SRLI_SRAI]
const fn decode_srli_srai(instruction: InstrVal) -> Result<Instruction> {
    use Instruction::*;

    let rd = get_rd(instruction);
    let rs1 = get_rs1(instruction);
    let (amount, shtyp) = get_shift_imms(instruction);

    let instruction = match shtyp.get_zext() as InstrVal {
        srli_srai_shtyp::SHTYP_SRLI => Srli(rd, rs1, amount),
        srli_srai_shtyp::SHTYP_SRAI => Srai(rd, rs1, amount),
        shtyp => return Err(DecodeError::UnknownShtyp { shtyp }),
    };

    Ok(instruction)
}

/// Decode an instruction with opcode [opcodes::OP].
const fn decode_op(instruction: InstrVal) -> Result<Instruction> {
    use Instruction::*;

    let funct3_7 = (get_funct3(instruction), get_funct7(instruction));
    let rd = get_rd(instruction);
    let rs1 = get_rs1(instruction);
    let rs2 = get_rs2(instruction);

    let instruction = match funct3_7 {
        (op::FUNCT3_ADD, op::FUNCT7_ADD) => Add(rd, rs1, rs2),
        (op::FUNCT3_SUB, op::FUNCT7_SUB) => Sub(rd, rs1, rs2),
        (op::FUNCT3_XOR, op::FUNCT7_XOR) => Xor(rd, rs1, rs2),
        (funct3, funct7) => return Err(DecodeError::UnknownRAluOp { funct3, funct7 }),
    };

    Ok(instruction)
}

/// Decode an instruction with opcode [opcodes::LOAD].
const fn decode_load(instruction: InstrVal) -> Result<Instruction> {
    use Instruction::*;

    let funct3 = get_funct3(instruction);
    let rd = get_rd(instruction);
    let rs1 = get_rs1(instruction);
    let imm = get_i_imm(instruction);

    let instruction = match funct3 {
        load::FUNCT3_LB => Lb(rd, rs1, imm),
        load::FUNCT3_LH => Lh(rd, rs1, imm),
        load::FUNCT3_LW => Lw(rd, rs1, imm),
        load::FUNCT3_LBU => Lbu(rd, rs1, imm),
        load::FUNCT3_LHU => Lhu(rd, rs1, imm),
        funct3 => return Err(DecodeError::UnknownLoadOp { funct3 }),
    };

    Ok(instruction)
}

/// Decode an instruction with opcode [opcodes::STORE].
const fn decode_store(code: InstrVal) -> Result<Instruction> {
    use Instruction::*;

    let funct3 = get_funct3(code);
    let rs1 = get_rs1(code);
    let rs2 = get_rs2(code);
    let imm = get_s_imm(code);

    let instruction = match funct3 {
        store::FUNCT3_SB => Sb(rs1, rs2, imm),
        store::FUNCT3_SH => Sh(rs1, rs2, imm),
        store::FUNCT3_SW => Sw(rs1, rs2, imm),
        funct3 => return Err(DecodeError::UnknownStoreOp { funct3 }),
    };

    Ok(instruction)
}

/// Get the opcode field.
/// This field is present in all instruction types.
const fn get_opcode(code: InstrVal) -> InstrVal {
    code & 0b1111111
}

/// Get the func3 field. Applicable to R, I, S, B instructions.
/// The value is placed into the lowest bits of [InstrVal].
const fn get_funct3(code: InstrVal) -> InstrVal {
    (code >> offsets::FUNCT3) & 0b111
}

/// Get the func7 field. Applicable to R instructions.
/// The value is placed into the lowest bits of [InstrVal].
const fn get_funct7(code: InstrVal) -> InstrVal {
    (code >> offsets::FUNCT7) & 0b1111111
}

/// Get the rd field. Applicable to R, I, U, J instructions.
/// The value is placed into the lowest bits of [InstrVal].
/// The result is immediately wrapped with [RegId] for
/// convenience.
const fn get_rd(code: InstrVal) -> RegId {
    let raw = (code >> offsets::RD) & REGISTER_MASK;
    RegId::new(raw).unwrap()
}

/// Get the rs1 field. Applicable to R, I, S, B instructions.
/// The value is placed into the lowest bits of [InstrVal].
/// The result is immediately wrapped with [RegId] for
/// convenience.
const fn get_rs1(code: InstrVal) -> RegId {
    let raw = (code >> offsets::RS1) & REGISTER_MASK;
    RegId::new(raw).unwrap()
}

/// Get the rs2 field. Applicable to R, S, B instructions.
/// The value is placed into the lowest bits of [InstrVal].
/// The result is immediately wrapped with [RegId] for
/// convenience.
const fn get_rs2(code: InstrVal) -> RegId {
    let raw = (code >> offsets::RS2) & REGISTER_MASK;
    RegId::new(raw).unwrap()
}

/// Get the immediate value. Applicable to I instructions ONLY.
/// The value is placed into the lowest bits of [InstrVal].
/// The value is not sign-extended.
/// The result is immediately wrapped with [Bit] for convenience.
const fn get_i_imm(code: InstrVal) -> Bit<12> {
    Bit::new((code >> offsets::I_TYPE_IMM) as RegVal).unwrap()
}

/// Get the immediate value split into shift amount and shtyp.
/// Applicable to shif imm-op only.
/// The value is placed into the lowest bits of [InstrVal].
/// The value is not sign-extended.
/// The result is immediately wrapped with [Bit] for convenience.
const fn get_shift_imms(code: InstrVal) -> (Bit<5>, Bit<7>) {
    let amount = (code >> offsets::I_TYPE_SHIFT_AMOUNT) & 0x1F;
    let shtyp = (code >> offsets::I_TYPE_SHIFT_TYPE) & 0x7F;
    let amount = Bit::new(amount as RegVal).unwrap();
    let shtyp = Bit::new(shtyp as RegVal).unwrap();
    (amount, shtyp)
}

/// Get the immediate value. Applicable to U instructions ONLY.
/// The value is placed into the lowest bits of [InstrVal].
/// The value is not sign-extended.
/// The result is immediately wrapped with [Bit] for convenience.
const fn get_u_imm(code: InstrVal) -> Bit<20> {
    Bit::new((code >> offsets::U_TYPE_IMM) as RegVal).unwrap()
}

/// Get the immediate value. Applicable to J instructions ONLY.
/// The value is placed into the lowest bits of [InstrVal].
/// The value is not sign-extended.
/// The result is immediately wrapped with [Bit] for convenience.
const fn get_j_imm(code: InstrVal) -> Bit<20> {
    let imm_0_9 = (code & 0x7FE0_0000) >> offsets::J_TYPE_IMM_0_9;
    let imm_10 = (code & 0x0010_0000) >> offsets::J_TYPE_IMM_10;
    let imm_11_18 = (code & 0x000F_F000) >> offsets::J_TYPE_IMM_11_18;
    let imm_19 = (code & 0x8000_0000) >> offsets::J_TYPE_IMM_19;
    let raw = imm_0_9 | (imm_10 << 10) | (imm_11_18 << 11) | (imm_19 << 19);
    Bit::new(raw as RegVal).unwrap()
}

/// Get the immediate value. Applicable to S instructions ONLY.
/// The value is placed into the lowest bits of [InstrVal].
/// The value is not sign-extended.
/// The result is immediately wrapped with [Bit] for convenience.
const fn get_s_imm(code: InstrVal) -> Bit<12> {
    let imm_0_4 = (code & 0x0000_0F80) >> offsets::S_TYPE_IMM_0_4;
    let imm_5_11 = (code & 0xFE00_0000) >> offsets::S_TYPE_IMM_5_11;
    let raw = imm_0_4 | (imm_5_11 << 5);
    Bit::new(raw as RegVal).unwrap()
}

/// Encode an instruction back into its [InstrVal] representation.
/// The returned value is guaranteed to be parseable back into [Instruction]
/// and is also a valid RiscV instruction.
pub const fn encode_instruction(instruction: Instruction) -> InstrVal {
    use crate::util::bit;
    use Instruction::*;

    match instruction {
        Jal(rd, imm) => encode_jal(rd, imm),
        Add(rd, rs1, rs2) => encode_op(rd, op::FUNCT3_ADD, rs1, rs2, op::FUNCT7_ADD),
        Sub(rd, rs1, rs2) => encode_op(rd, op::FUNCT3_SUB, rs1, rs2, op::FUNCT7_SUB),
        Xor(rd, rs1, rs2) => encode_op(rd, op::FUNCT3_XOR, rs1, rs2, op::FUNCT7_XOR),
        Lui(rd, imm) => encode_u_instr(opcodes::LUI, rd, imm),
        Auipc(rd, imm) => encode_u_instr(opcodes::AUIPC, rd, imm),
        Addi(rd, rs1, imm) => encode_op_imm(rd, op_imm::FUNCT3_ADDI, rs1, imm),
        Xori(rd, rs1, imm) => encode_op_imm(rd, op_imm::FUNCT3_XORI, rs1, imm),
        Ori(rd, rs1, imm) => encode_op_imm(rd, op_imm::FUNCT3_ORI, rs1, imm),
        Andi(rd, rs1, imm) => encode_op_imm(rd, op_imm::FUNCT3_ANDI, rs1, imm),
        Slli(rd, rs1, imm) => {
            encode_op_imm(rd, op_imm::FUNCT3_SLLI, rs1, bit(imm.get_zext()))
        }
        Srli(rd, rs1, imm) => encode_shift(rd, rs1, imm, srli_srai_shtyp::SHTYP_SRLI),
        Srai(rd, rs1, imm) => encode_shift(rd, rs1, imm, srli_srai_shtyp::SHTYP_SRAI),
        Slti(rd, rs1, imm) => encode_op_imm(rd, op_imm::FUNCT3_SLTI, rs1, imm),
        Sltiu(rd, rs1, imm) => encode_op_imm(rd, op_imm::FUNCT3_SLTIU, rs1, imm),
        Jalr(rd, rs1, imm) => encode_jalr(rd, rs1, imm),
        Lb(rd, rs1, imm) => encode_load(rd, load::FUNCT3_LB, rs1, imm),
        Lh(rd, rs1, imm) => encode_load(rd, load::FUNCT3_LH, rs1, imm),
        Lw(rd, rs1, imm) => encode_load(rd, load::FUNCT3_LW, rs1, imm),
        Lbu(rd, rs1, imm) => encode_load(rd, load::FUNCT3_LBU, rs1, imm),
        Lhu(rd, rs1, imm) => encode_load(rd, load::FUNCT3_LHU, rs1, imm),
        Sb(rs1, rs2, imm) => encode_store(store::FUNCT3_SB, rs1, rs2, imm),
        Sh(rs1, rs2, imm) => encode_store(store::FUNCT3_SH, rs1, rs2, imm),
        Sw(rs1, rs2, imm) => encode_store(store::FUNCT3_SW, rs1, rs2, imm),
    }
}

const fn encode_jal(rd: RegId, imm: Bit<20>) -> InstrVal {
    let imm = imm.get_zext() as InstrVal;
    let imm_0_9 = imm & 0x0000_03FF;
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

const fn encode_op(
    rd: RegId,
    funct3: InstrVal,
    rs1: RegId,
    rs2: RegId,
    funct7: InstrVal,
) -> InstrVal {
    let mut out = 0;
    out |= opcodes::OP;
    out |= rd.get() << offsets::RD;
    out |= funct3 << offsets::FUNCT3;
    out |= rs1.get() << offsets::RS1;
    out |= rs2.get() << offsets::RS2;
    out |= funct7 << offsets::FUNCT7;
    out
}

const fn encode_u_instr(opcode: InstrVal, rd: RegId, imm: Bit<20>) -> InstrVal {
    let mut out = 0;
    out |= opcode;
    out |= rd.get() << offsets::RD;
    out |= (imm.get_zext() as InstrVal) << offsets::U_TYPE_IMM;
    out
}

const fn encode_shift(
    rd: RegId,
    rs1: RegId,
    amount: Bit<5>,
    shtyp: InstrVal,
) -> InstrVal {
    let amount_local_off = offsets::I_TYPE_SHIFT_TYPE - offsets::I_TYPE_SHIFT_AMOUNT;
    let mut imm = 0;
    imm |= amount.get_zext();
    imm |= (shtyp << amount_local_off) as RegVal;
    encode_op_imm(rd, op_imm::FUNCT3_SRLI_SRAI, rs1, Bit::new(imm).unwrap())
}

const fn encode_op_imm(
    rd: RegId,
    funct3: InstrVal,
    rs1: RegId,
    imm: Bit<12>,
) -> InstrVal {
    let mut out = 0;
    out |= opcodes::OP_IMM;
    out |= rd.get() << offsets::RD;
    out |= funct3 << offsets::FUNCT3;
    out |= rs1.get() << offsets::RS1;
    out |= (imm.get_zext() as InstrVal) << offsets::I_TYPE_IMM;
    out
}

const fn encode_jalr(rd: RegId, rs1: RegId, imm: Bit<12>) -> InstrVal {
    let mut out = 0;
    out |= opcodes::JALR;
    out |= rd.get() << offsets::RD;
    out |= rs1.get() << offsets::RS1;
    out |= (imm.get_zext() as InstrVal) << offsets::I_TYPE_IMM;
    out
}

const fn encode_load(rd: RegId, funct3: InstrVal, rs1: RegId, imm: Bit<12>) -> InstrVal {
    let mut out = 0;
    out |= opcodes::LOAD;
    out |= rd.get() << offsets::RD;
    out |= funct3 << offsets::FUNCT3;
    out |= rs1.get() << offsets::RS1;
    out |= (imm.get_zext() as InstrVal) << offsets::I_TYPE_IMM;
    out
}

const fn encode_store(
    funct3: InstrVal,
    rs1: RegId,
    rs2: RegId,
    imm: Bit<12>,
) -> InstrVal {
    let imm = imm.get_zext() as InstrVal;
    let imm_0_4 = imm & 0x0000_001F;
    let imm_5_11 = (imm & 0x0000_0FE0) >> 5;

    let mut out = 0;
    out |= opcodes::STORE;
    out |= imm_0_4 << offsets::S_TYPE_IMM_0_4;
    out |= funct3 << offsets::FUNCT3;
    out |= rs1.get() << offsets::RS1;
    out |= rs2.get() << offsets::RS2;
    out |= imm_5_11 << offsets::S_TYPE_IMM_5_11;
    out
}

#[cfg(test)]
mod tests {
    use crate::kernel::{decode_instruction, encode_instruction, InstrVal};
    use crate::util::{bit, reg_x};

    use super::DecodeError;
    use super::Instruction;

    #[derive(Debug, Clone, Copy)]
    struct ParseTest {
        input: InstrVal,
        expected: Result<Instruction, DecodeError>,
    }

    #[test]
    fn test_simple_positive_parse() {
        for t in test_data_good() {
            let decoded = decode_instruction(t.input);
            assert_eq!(decoded, t.expected);
            assert_eq!(
                encode_instruction(decoded.unwrap()),
                t.input,
                "failed to decode-encode instruction: {:#b}",
                t.input
            );
        }
    }

    /// This testdata is a bunch of positive cases where the decoder should return a
    /// successful result.
    /// This test data should include samples of all instructions supported by the simulator.
    /// Use this tool to debug failing tests: https://luplab.gitlab.io/rvcodecjs.
    fn test_data_good() -> impl IntoIterator<Item = ParseTest> {
        use Instruction::*;

        // NOTE: please keep the type ordering the same as in
        // the parser implementation.
        vec![
            /* J-Type instructions */
            ParseTest {
                input: 0b00010100010000000000_00000_1101111,
                expected: Ok(Jal(reg_x(0), bit(162))),
            },
            ParseTest {
                input: 0b00010100010000000000_00101_1101111,
                expected: Ok(Jal(reg_x(5), bit(162))),
            },
            ParseTest {
                input: 0b11111111000111111111_00000_1101111,
                expected: Ok(Jal(reg_x(0), bit(0xf_fff8))),
            },
            /* R-Type instructions */
            ParseTest {
                input: 0b0000000_00001_00110_000_00100_0110011,
                expected: Ok(Add(reg_x(4), reg_x(6), reg_x(1))),
            },
            ParseTest {
                input: 0b0100000_11100_00000_000_00101_0110011,
                expected: Ok(Sub(reg_x(5), reg_x(0), reg_x(28))),
            },
            ParseTest {
                input: 0b0000000_01001_01000_100_00011_0110011,
                expected: Ok(Xor(reg_x(3), reg_x(8), reg_x(9))),
            },
            /* U-Type instructions */
            ParseTest {
                input: 0b00000001000111101011_00110_0110111,
                expected: Ok(Lui(reg_x(6), bit(4587))),
            },
            ParseTest {
                input: 0b00000001001100010111_01100_0010111,
                expected: Ok(Auipc(reg_x(12), bit(4887))),
            },
            /* I-Type instructions */
            ParseTest {
                input: 0b000000010100_01100_000_01011_0010011,
                expected: Ok(Addi(reg_x(11), reg_x(12), bit(20))),
            },
            ParseTest {
                input: 0b110110000000_11101_100_00101_0010011,
                expected: Ok(Xori(reg_x(5), reg_x(29), bit(3456))),
            },
            ParseTest {
                input: 0b000011111111_00101_000_01010_1100111,
                expected: Ok(Jalr(reg_x(10), reg_x(5), bit(255))),
            },
            ParseTest {
                input: 0b000010000100_00110_000_00101_0000011,
                expected: Ok(Lb(reg_x(5), reg_x(6), bit(132))),
            },
            ParseTest {
                input: 0b111111111111_11111_001_11100_0000011,
                expected: Ok(Lh(reg_x(28), reg_x(31), bit(0xFFF))),
            },
            ParseTest {
                input: 0b000000000010_01011_010_01110_0000011,
                expected: Ok(Lw(reg_x(14), reg_x(11), bit(2))),
            },
            ParseTest {
                input: 0b000000000001_01110_100_01111_0000011,
                expected: Ok(Lbu(reg_x(15), reg_x(14), bit(1))),
            },
            ParseTest {
                input: 0b000000000100_01111_101_01111_0000011,
                expected: Ok(Lhu(reg_x(15), reg_x(15), bit(4))),
            },
            /* S-Type instructions */
            ParseTest {
                input: 0b000001100101_00111_000_11011_0100011,
                expected: Ok(Sb(reg_x(7), reg_x(5), bit(123))),
            },
            ParseTest {
                input: 0b111111111111_00000_001_11111_0100011,
                expected: Ok(Sh(reg_x(0), reg_x(31), bit(4095))),
            },
            ParseTest {
                input: 0b111111111111_00000_010_11111_0100011,
                expected: Ok(Sw(reg_x(0), reg_x(31), bit(4095))),
            },
        ]
    }
}
