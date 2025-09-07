//! This module contains the type-safe internal representation
//! of a RiscV instruction and other related types related to it.

use thiserror::Error;

use super::{GeneralRegister, Memory, MemoryError, Processor, RegisterVal};

/// Error returned by [Instruction::execute].
#[derive(Clone, Copy, PartialEq, Eq, Error, Debug)]
pub enum InstructionError {
    #[error(
        "Failed to execute instruction {instruction:?} at {instruction_address:#x}: {memory_error}"
    )]
    MemoryError {
        instruction_address: RegisterVal,
        instruction: Instruction,
        #[source]
        memory_error: MemoryError,
    },
}

/// [Instruction] is a type-safe representation of a CPU
/// instruction. That means, all valid values of this type
/// are valid RiscV instructions. Each instruction behavior is documented.
///
/// The pseudo-code slightly differs from the documentation. This
/// is because we assume that the immediate value is always placed
/// in the lowest bits of [RegisterVal]. Because of that, e.g.
/// `lui` is documented to be offsetting `imm` by 12 bits.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
pub enum Instruction {
    /* J-Type instructions */
    /// Jal instruction. Has the following semantics
    /// ```pic
    /// rd = PC + 4 // Overflow
    /// PC += sext(imm << 1) // Overflow
    /// ```
    Jal { rd: GeneralRegister, imm: Bit<20> },
    /* R-Type instructions */
    /// Add instruction. Has the following semantics
    /// ```pic
    /// rd = rs1 + rs2 // Overflow
    /// ```
    Add {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        rs2: GeneralRegister,
    },
    /// Sub instruction. Has the following semantics
    /// ```pic
    /// rd = rs1 - rs2 // Overflow
    /// ```
    Sub {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        rs2: GeneralRegister,
    },
    /// Xor instruction. Has the following semantics
    /// ```pic
    /// rd = rs1 ^ rs2
    /// ```
    Xor {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        rs2: GeneralRegister,
    },
    /* U-Type instructions */
    /// Lui instruction. Has the following semantics
    /// ```pic
    /// rd = sext(imm << 12)
    /// ```
    Lui { rd: GeneralRegister, imm: Bit<20> },
    /// Auipc instruction. Has the following semantics
    /// ```pic
    /// rd = PC + sext(imm << 12) // Overflow
    /// ```
    Auipc { rd: GeneralRegister, imm: Bit<20> },
    /* I-Type instructions */
    /// Addi instruction. Has the following semantics
    /// ```pic
    /// rd = rs1 + sext(imm) // Overflow
    /// ```
    Addi {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        imm: Bit<12>,
    },
    /// Xori instruction. Has the following semantics
    /// ```pic
    /// rd = rs1 ^ sext(rs2)
    /// ```
    Xori {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        imm: Bit<12>,
    },
    /// Jalr instruction. Has the following semantics
    /// ```pic
    /// rd = PC + 4 // Overflow
    /// PC = rs1 + sext(imm) // Overflow
    /// ```
    Jalr {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        imm: Bit<12>,
    },
    /// Lb instruction. Has the following semantics
    /// ```pic
    /// rd = sext(Read(rs1 + sext(imm), 8))
    /// ```
    Lb {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        imm: Bit<12>,
    },
    /// Lb instruction. Has the following semantics
    /// ```pic
    /// rd = sext(Read(rs1 + sext(imm), 16))
    /// ```
    Lh {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        imm: Bit<12>,
    },
    /// Lb instruction. Has the following semantics
    /// ```pic
    /// rd = sext(Read(rs1 + sext(imm), 32))
    /// ```
    Lw {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        imm: Bit<12>,
    },
    /// Lb instruction. Has the following semantics
    /// ```pic
    /// rd = sext(Read(rs1 + sext(imm), 8))
    /// ```
    Lbu {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        imm: Bit<12>,
    },
    /// Lb instruction. Has the following semantics
    /// ```pic
    /// rd = sext(Read(rs1 + sext(imm), 16))
    /// ```
    Lhu {
        rd: GeneralRegister,
        rs1: GeneralRegister,
        imm: Bit<12>,
    },
    /* S-Type instructions */
    /// Sw instruction. Has the followng semantics
    /// ```pic
    /// Write(rs1 + sext(imm), rs2[8:0])
    /// ```
    Sb {
        rs1: GeneralRegister,
        rs2: GeneralRegister,
        imm: Bit<12>,
    },
    /// Sh instruction. Has the followng semantics
    /// ```pic
    /// Write(rs1 + sext(imm)], rs2[16:0])
    /// ```
    Sh {
        rs1: GeneralRegister,
        rs2: GeneralRegister,
        imm: Bit<12>,
    },
    /// Sw instruction. Has the followng semantics
    /// ```pic
    /// Write(rs1 + sext(imm), rs2[31:0])
    /// ```
    Sw {
        rs1: GeneralRegister,
        rs2: GeneralRegister,
        imm: Bit<12>,
    },
}

impl Instruction {
    /// Executes the instruction on a processor. The processor is
    /// modified in-place. In case of an error, an error is returned.
    /// The processor state will not be reliable if `execute` fails.
    pub fn execute(
        self,
        processor: &mut Processor,
        memory: &mut Memory,
        old_pc: RegisterVal,
    ) -> Result<(), InstructionError> {
        match self {
            Instruction::Jal { rd, imm } => {
                let new_pc = old_pc.wrapping_add(imm.get_sext() << 1);
                processor.set_register(rd, old_pc + 4);
                processor.pc = new_pc;
                Ok(())
            }
            Instruction::Add { rd, rs1, rs2 } => {
                let rs1 = processor.get_register(rs1);
                let rs2 = processor.get_register(rs2);
                processor.set_register(rd, rs1.wrapping_add(rs2));
                Ok(())
            }
            Instruction::Sub { rd, rs1, rs2 } => {
                let rs1 = processor.get_register(rs1);
                let rs2 = processor.get_register(rs2);
                processor.set_register(rd, rs1.wrapping_sub(rs2));
                Ok(())
            }
            Instruction::Xor { rd, rs1, rs2 } => {
                let rs1 = processor.get_register(rs1);
                let rs2 = processor.get_register(rs2);
                processor.set_register(rd, rs1 ^ rs2);
                Ok(())
            }
            Instruction::Lui { rd, imm } => {
                processor.set_register(rd, imm.get_sext() << 12);
                Ok(())
            }
            Instruction::Auipc { rd, imm } => {
                processor.set_register(rd, old_pc.wrapping_add(imm.get_sext() << 12));
                Ok(())
            }
            Instruction::Addi { rd, rs1, imm } => {
                let rs1 = processor.get_register(rs1);
                processor.set_register(rd, rs1.wrapping_add(imm.get_sext()));
                Ok(())
            }
            Instruction::Xori { rd, rs1, imm } => {
                let rs1 = processor.get_register(rs1);
                processor.set_register(rd, rs1 ^ imm.get_sext());
                Ok(())
            }
            Instruction::Jalr { rd, rs1, imm } => {
                let rs1 = processor.get_register(rs1);
                let new_pc = rs1.wrapping_add(imm.get_sext());
                processor.set_register(rd, old_pc + 4);
                processor.pc = new_pc;
                Ok(())
            }
            Instruction::Lb { rd, rs1, imm } => {
                load_op_impl::<8>(processor, memory, rs1, rd, imm, old_pc, self)
            }
            Instruction::Lh { rd, rs1, imm } => {
                load_op_impl::<16>(processor, memory, rs1, rd, imm, old_pc, self)
            }
            Instruction::Lw { rd, rs1, imm } => {
                load_op_impl::<32>(processor, memory, rs1, rd, imm, old_pc, self)
            }
            Instruction::Lbu { rd, rs1, imm } => {
                uload_op_impl::<1>(processor, memory, rs1, rd, imm, old_pc, self)
            }
            Instruction::Lhu { rd, rs1, imm } => {
                uload_op_impl::<2>(processor, memory, rs1, rd, imm, old_pc, self)
            }
            Instruction::Sb { rs1, rs2, imm } => {
                store_op_impl::<8>(processor, memory, rs1, rs2, imm, old_pc, self)
            }
            Instruction::Sh { rs1, rs2, imm } => {
                store_op_impl::<16>(processor, memory, rs1, rs2, imm, old_pc, self)
            }
            Instruction::Sw { rs1, rs2, imm } => {
                store_op_impl::<32>(processor, memory, rs1, rs2, imm, old_pc, self)
            }
        }
    }
}

fn load_op_impl<const WIDTH: usize>(
    processor: &mut Processor,
    memory: &Memory,
    rs1: GeneralRegister,
    rd: GeneralRegister,
    imm: Bit<12>,
    old_pc: RegisterVal,
    instruction: Instruction,
) -> Result<(), InstructionError> {
    let rs1 = processor.get_register(rs1);
    let address = rs1.wrapping_add(imm.get_sext());
    let mut dst = [0u8; std::mem::size_of::<RegisterVal>()];
    memory
        .read(address, &mut dst[0..WIDTH / 8])
        .map_err(|memory_error| InstructionError::MemoryError {
            instruction_address: old_pc,
            instruction,
            memory_error,
        })?;
    let new_rd = Bit::<WIDTH>::new(RegisterVal::from_le_bytes(dst))
        .expect("unexpected load overflow")
        .get_sext();
    processor.set_register(rd, new_rd);
    Ok(())
}

fn uload_op_impl<const WIDTH: usize>(
    processor: &mut Processor,
    memory: &Memory,
    rs1: GeneralRegister,
    rd: GeneralRegister,
    imm: Bit<12>,
    old_pc: RegisterVal,
    instruction: Instruction,
) -> Result<(), InstructionError> {
    let rs1 = processor.get_register(rs1);
    let address = rs1.wrapping_add(imm.get_sext());
    let mut dst = [0u8; std::mem::size_of::<RegisterVal>()];
    memory
        .read(address, &mut dst[0..WIDTH])
        .map_err(|memory_error| InstructionError::MemoryError {
            instruction_address: old_pc,
            instruction,
            memory_error,
        })?;
    let new_rd = RegisterVal::from_le_bytes(dst);
    processor.set_register(rd, new_rd);
    Ok(())
}

fn store_op_impl<const WIDTH: usize>(
    processor: &Processor,
    memory: &mut Memory,
    rs1: GeneralRegister,
    rs2: GeneralRegister,
    imm: Bit<12>,
    old_pc: RegisterVal,
    instruction: Instruction,
) -> Result<(), InstructionError> {
    let rs1 = processor.get_register(rs1);
    let rs2 = processor.get_register(rs2);
    let address = rs1.wrapping_add(imm.get_sext());
    memory
        .write(address, &rs2.to_le_bytes()[0..WIDTH / 8])
        .map_err(|memory_error| InstructionError::MemoryError {
            instruction_address: old_pc,
            instruction,
            memory_error,
        })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
#[repr(transparent)]
/// Contains a N-bit wide immediate value
pub struct Bit<const WIDTH: usize>(RegisterVal);

impl<const WIDTH: usize> Bit<WIDTH> {
    /// The maximum possible value.
    pub const MAX: RegisterVal = ((1 as RegisterVal) << WIDTH) - 1;

    const SIGN_BIT: RegisterVal = (1 as RegisterVal) << WIDTH - 1;
    const EXTENSION: RegisterVal = RegisterVal::MAX ^ Self::MAX;

    pub const fn new(val: RegisterVal) -> Option<Self> {
        if val <= Self::MAX {
            Some(Self(val))
        } else {
            None
        }
    }

    /// Get the value as [RegisterVal].
    /// The value is zero-extended.
    // NOTE: unused, but may be useful later.
    #[allow(dead_code)]
    pub const fn get_zext(self) -> RegisterVal {
        self.0
    }

    /// Get the value as [RegisterVal].
    /// The value is sign-extended.
    pub const fn get_sext(self) -> RegisterVal {
        let mut result = self.0;
        if (result & Self::SIGN_BIT) == Self::SIGN_BIT {
            result |= Self::EXTENSION;
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::RegisterVal;

    use super::Bit;

    const SAMPLE_COUNT: usize = 10_000;

    #[test]
    fn test_imm_12_max() {
        for x in 0..=Bit::<12>::MAX {
            Bit::<12>::new(x).expect("Must succeed");
        }
        for _ in 0..SAMPLE_COUNT {
            let x = rand::random_range((Bit::<12>::MAX + 1)..RegisterVal::MAX);
            assert_eq!(Bit::<12>::new(x), None);
        }
    }

    #[test]
    fn test_sext_positive_12() {
        for x in 0..0x400 {
            let imm = Bit::<12>::new(x).unwrap();
            assert_eq!(x, imm.get_sext());
        }
    }

    #[test]
    fn test_sext_negative_12() {
        for x in 0..0x400 {
            let imm = Bit::<12>::new(x | 0x800).unwrap();
            let target = x | 0xffff_ffff_ffff_f800;
            assert_eq!(target, imm.get_sext(), "Imm value: {}", imm.get_zext());
        }
    }

    #[test]
    fn test_sext_positive_20() {
        for x in 0..0x4_0000 {
            let imm = Bit::<20>::new(x).unwrap();
            assert_eq!(x, imm.get_sext());
        }
    }

    #[test]
    fn test_sext_negative_20() {
        for x in 0..0x4_0000 {
            let imm = Bit::<20>::new(x | 0x8_0000).unwrap();
            let target = x | 0xffff_ffff_fff8_0000;
            assert_eq!(target, imm.get_sext(), "Imm value: {}", imm.get_zext());
        }
    }

    #[test]
    fn test_imm_20_max() {
        for x in 0..=Bit::<20>::MAX {
            Bit::<20>::new(x).expect("Must succeed");
        }
        for _ in 0..SAMPLE_COUNT {
            let x = rand::random_range((Bit::<20>::MAX + 1)..RegisterVal::MAX);
            assert_eq!(Bit::<20>::new(x), None);
        }
    }
}
