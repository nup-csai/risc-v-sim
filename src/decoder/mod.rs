use crate::instruction::Instruction;
use crate::processor::Register;

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
    pub const FUNCT7_SUB: u32 = 0b0000010;

    /* Codes for XOR */
    pub const FUNCT3_XOR: u32 = 0b001;
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
            rd: Register::from(get_rd(instruction) as u64),
            offset: get_j_type_imm(instruction) as u64,
        },
        /* R-type instructions */
        opcodes::R_ALU_OP => decode_r_alu_op(instruction)?,
        /* U-type instructions */
        opcodes::LUI => Instruction::Lui {
            rd: Register::from(get_rd(instruction) as u64),
            imm: get_u_type_imm(instruction) as u64, 
        },
        opcodes::AUIPC => Instruction::Auipc {
            rd: Register::from(get_rd(instruction) as u64),
            imm: get_u_type_imm(instruction) as u64,
        },
        /* I-type instructions */
        opcodes::I_ALU_OP => decode_i_alu_op(instruction)?,
        opcodes::JALR => Instruction::Jalr {
            rd: Register::from(get_rd(instruction) as u64),
            rs1: Register::from(get_rs1(instruction) as u64),
            offset: get_i_type_imm(instruction) as u64
        },
        _ => return None,
    };

    Some(instruction)
}

fn decode_i_alu_op(instruction: u32) -> Option<Instruction> {
    let funct3 = get_funct3(instruction);
    let rd = Register::from(get_rd(instruction) as u64);
    let rs1 = Register::from(get_rs1(instruction) as u64);
    let imm = get_i_type_imm(instruction) as u64;

    let instruction = match funct3 {
        i_alu_op::FUNCT3_ADDI => Instruction::Addi {
            rd,
            rs1,
            imm,
        },
        i_alu_op::FUNCT3_XORI => Instruction::Xori {
            rd,
            rs1,
            imm,
        },
        _ => return None
    };

    Some(instruction)
}

fn decode_r_alu_op(instruction: u32) -> Option<Instruction> {
    let funct3_7 = (get_funct3(instruction), get_funct7(instruction));
    let rd = Register::from(get_rd(instruction) as u64);
    let rs1 = Register::from(get_rs1(instruction) as u64);
    let rs2 = Register::from(get_rs2(instruction) as u64);

    let instruction = match funct3_7 {
        (r_alu_op::FUNCT3_ADD, r_alu_op::FUNCT7_ADD) => Instruction::Add { 
            rd, 
            rs1, 
            rs2, 
        },
        (r_alu_op::FUNCT3_SUB, r_alu_op::FUNCT7_SUB) => Instruction::Sub { 
            rd, 
            rs1, 
            rs2, 
        },
        (r_alu_op::FUNCT3_XOR, r_alu_op::FUNCT7_XOR) => Instruction::Xor { 
            rd, 
            rs1, 
            rs2, 
        },
        _ => return None
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