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
