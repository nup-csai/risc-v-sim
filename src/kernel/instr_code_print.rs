//! Methods for pretty-printing instruction codes.

use std::fmt;
use std::io::{Cursor, Write};

use crate::kernel::{INSTRVAL_BITS, Instruction, encode_instruction};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct PrettyBincode(pub Instruction);

impl fmt::Display for PrettyBincode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let val = encode_instruction(self.0);
        let mut bits = [0u8; INSTRVAL_BITS];
        write!(Cursor::new(bits.as_mut_slice()), "{val:032b}").unwrap();
        match self.0 {
            Instruction::Jal(..) => write_j_type(&bits, f),
            Instruction::Add(..)
            | Instruction::Sub(..)
            | Instruction::Xor(..)
            | Instruction::Or(..)
            | Instruction::And(..)
            | Instruction::Sll(..)
            | Instruction::Srl(..)
            | Instruction::Sra(..)
            | Instruction::Slt(..)
            | Instruction::Sltu(..) => write_r_type(&bits, f),
            Instruction::Lui(..) | Instruction::Auipc(..) => write_u_type(&bits, f),
            Instruction::Addi(..)
            | Instruction::Xori(..)
            | Instruction::Ori(..)
            | Instruction::Andi(..)
            | Instruction::Slli(..)
            | Instruction::Srli(..)
            | Instruction::Srai(..)
            | Instruction::Slti(..)
            | Instruction::Sltiu(..)
            | Instruction::Jalr(..)
            | Instruction::Lb(..)
            | Instruction::Lh(..)
            | Instruction::Lw(..)
            | Instruction::Lbu(..)
            | Instruction::Lhu(..)
            | Instruction::Ebreak => write_i_type(&bits, f),
            Instruction::Sb(..) | Instruction::Sh(..) | Instruction::Sw(..) => {
                write_s_type(&bits, f)
            }
            Instruction::Beq(..)
            | Instruction::Bne(..)
            | Instruction::Blt(..)
            | Instruction::Bge(..)
            | Instruction::Bltu(..)
            | Instruction::Bgeu(..) => write_b_type(&bits, f),
        }
    }
}

/// Writes the bits with a layout like that of a J-type instruction
pub fn write_j_type(bits: &[u8; INSTRVAL_BITS], f: &mut fmt::Formatter) -> fmt::Result {
    write!(
        f,
        "{} {} {}",
        sub_slice(bits, 12, 32),
        sub_slice(bits, 7, 12),
        sub_slice(bits, 0, 7),
    )
}

/// Writes the bits with a layout like that of a R-type instruction
pub fn write_r_type(bits: &[u8; INSTRVAL_BITS], f: &mut fmt::Formatter) -> fmt::Result {
    write!(
        f,
        "{} {} {} {} {} {}",
        sub_slice(bits, 25, 32),
        sub_slice(bits, 20, 25),
        sub_slice(bits, 15, 20),
        sub_slice(bits, 12, 15),
        sub_slice(bits, 7, 12),
        sub_slice(bits, 0, 7),
    )
}

/// Writes the bits with a layout like that of a U-type instruction
pub fn write_u_type(bits: &[u8; INSTRVAL_BITS], f: &mut fmt::Formatter) -> fmt::Result {
    write_j_type(bits, f)
}

/// Writes the bits with a layout like that of a I-type instruction
pub fn write_i_type(bits: &[u8; INSTRVAL_BITS], f: &mut fmt::Formatter) -> fmt::Result {
    write!(
        f,
        "{} {} {} {} {}",
        sub_slice(bits, 20, 32),
        sub_slice(bits, 15, 20),
        sub_slice(bits, 12, 15),
        sub_slice(bits, 7, 12),
        sub_slice(bits, 0, 7),
    )
}

/// Writes the bits with a layout like that of a S-type instruction
pub fn write_s_type(bits: &[u8; INSTRVAL_BITS], f: &mut fmt::Formatter) -> fmt::Result {
    write_r_type(bits, f)
}

/// Writes the bits with a layout like that of a B-type instruction
pub fn write_b_type(bits: &[u8; INSTRVAL_BITS], f: &mut fmt::Formatter) -> fmt::Result {
    write_r_type(bits, f)
}

/// Helper for indexing bit digits, because they are backwards
/// in printed notation.
fn sub_slice(bits: &[u8; INSTRVAL_BITS], from: usize, to: usize) -> &str {
    str::from_utf8(&bits[(INSTRVAL_BITS - to)..(INSTRVAL_BITS - from)]).unwrap()
}

#[cfg(test)]
mod tests {
    use crate::kernel::instr_code_print::PrettyBincode;
    use crate::kernel::{Bit, Instruction, RegId};

    #[test]
    fn basic_formats() {
        assert_eq!(
            PrettyBincode(Instruction::Jal(RegId::ZERO, Bit::new(324 >> 1).unwrap(),)).to_string(),
            "00010100010000000000 00000 1101111",
        );

        assert_eq!(
            PrettyBincode(Instruction::Add(RegId::TP, RegId::T1, RegId::RA)).to_string(),
            "0000000 00001 00110 000 00100 0110011",
        );

        assert_eq!(
            PrettyBincode(Instruction::Lui(RegId::T1, Bit::new(4587).unwrap(),)).to_string(),
            "00000001000111101011 00110 0110111",
        );

        assert_eq!(
            PrettyBincode(Instruction::Addi(
                RegId::A1,
                RegId::A2,
                Bit::new(20).unwrap(),
            ))
            .to_string(),
            "000000010100 01100 000 01011 0010011",
        );

        assert_eq!(
            PrettyBincode(Instruction::Sw(
                RegId::T0,
                RegId::T2,
                Bit::new(123).unwrap(),
            ))
            .to_string(),
            "0000011 00111 00101 010 11011 0100011",
        );

        assert_eq!(
            PrettyBincode(Instruction::Beq(
                RegId::T0,
                RegId::T1,
                Bit::new(0xC00).unwrap(),
            ))
            .to_string(),
            "1000000 00110 00101 000 00001 1100011",
        );
    }
}
