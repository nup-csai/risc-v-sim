use std::fmt;

/// The type of the values the CPU works with.
pub type RegVal = u64;
pub type RegValSigned = i64;
/// The type used to store CPU instructions.
pub type InstrVal = u32;

/// Masks the bits required to index bits of [RegVal].
pub const REGVAL_SIZE_MASK: RegVal = 0b111111;
pub const GENERAL_REGISTER_COUNT: usize = 32;

/// The [Registers] struct contains all Rv64i registers.
/// You can manipulate them with [Registers::get] and
/// [Registers::set]. The [RegId::ZERO] registers is guaranteed
/// to always return `0` wil be unaffected by sets.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
pub struct Registers {
    storage: [RegVal; GENERAL_REGISTER_COUNT - 1],
    pub pc: RegVal,
}

/// [RegId] represents a validated general purpose register index.
/// In baseline Rv64i there are 32 general purpose registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
#[repr(transparent)]
pub struct RegId(InstrVal);

impl RegId {
    pub const fn new(value: InstrVal) -> Option<Self> {
        if value < GENERAL_REGISTER_COUNT as InstrVal {
            Some(Self(value))
        } else {
            None
        }
    }

    pub const fn get(&self) -> InstrVal {
        self.0
    }

    /// Hardwired zero. Always zero on the processor.
    pub const ZERO: RegId = Self(0);
    /// Return address.
    /// Saved by caller.
    pub const RA: RegId = Self(1);
    /// Stack pointer.
    /// Saved by callee.
    pub const SP: RegId = Self(2);
    /// Global pointer
    pub const GP: RegId = Self(3);
    /// Thread pointer
    pub const TP: RegId = Self(4);
    /// Temporary / alternate return address.
    /// Saved by caller.
    pub const T0: RegId = Self(5);
    /// Temporary.
    /// Saved by caller.
    pub const T1: RegId = Self(6);
    /// Temporary.
    /// Saved by caller.
    pub const T2: RegId = Self(7);
    /// Saved register / frame pointer.
    /// Sometimes called S0.
    /// Saved by callee.
    pub const FP: RegId = Self(8);
    /// Saved register.
    /// Saved by callee.
    pub const S1: RegId = Self(9);
    /// Function argument / return value.
    pub const A0: RegId = Self(10);
    /// Function argument / return value.
    pub const A1: RegId = Self(11);
    /// Function argument.
    pub const A2: RegId = Self(12);
    /// Function argument.
    /// Saved by caller.
    pub const A3: RegId = Self(13);
    /// Function argument.
    /// Saved by caller.
    pub const A4: RegId = Self(14);
    /// Function argument.
    /// Saved by caller.
    pub const A5: RegId = Self(15);
    /// Function argument.
    /// Saved by caller.
    pub const A6: RegId = Self(16);
    /// Function argument.
    /// Saved by caller.
    pub const A7: RegId = Self(17);
    /// Saved register.
    /// Saved by callee.
    pub const S2: RegId = Self(18);
    /// Saved register.
    /// Saved by callee.
    pub const S3: RegId = Self(19);
    /// Saved register.
    /// Saved by callee.
    pub const S4: RegId = Self(20);
    /// Saved register.
    /// Saved by callee.
    pub const S5: RegId = Self(21);
    /// Saved register.
    /// Saved by callee.
    pub const S6: RegId = Self(22);
    /// Saved register.
    /// Saved by callee.
    pub const S7: RegId = Self(23);
    /// Saved register.
    /// Saved by callee.
    pub const S8: RegId = Self(24);
    /// Saved register.
    /// Saved by callee.
    pub const S9: RegId = Self(25);
    /// Saved register.
    /// Saved by callee.
    pub const S10: RegId = Self(26);
    /// Saved register.
    /// Saved by callee.
    pub const S11: RegId = Self(27);
    /// Temporary.
    /// Saved by caller.
    pub const T3: RegId = Self(28);
    /// Temporary.
    /// Saved by caller.
    pub const T4: RegId = Self(29);
    /// Temporary.
    /// Saved by caller.
    pub const T5: RegId = Self(30);
    /// Temporary.
    /// Saved by caller.
    pub const T6: RegId = Self(31);
}

impl fmt::Display for RegId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::ZERO => write!(f, "zero"),
            Self::RA => write!(f, "ra"),
            Self::SP => write!(f, "sp"),
            Self::GP => write!(f, "gp"),
            Self::TP => write!(f, "tp"),
            Self::T0 => write!(f, "t0"),
            Self::T1 => write!(f, "t1"),
            Self::T2 => write!(f, "t2"),
            Self::FP => write!(f, "fp"),
            Self::A0 => write!(f, "a0"),
            Self::A1 => write!(f, "a1"),
            Self::A2 => write!(f, "a2"),
            Self::A3 => write!(f, "a3"),
            Self::A4 => write!(f, "a4"),
            Self::A5 => write!(f, "a5"),
            Self::A6 => write!(f, "a6"),
            Self::A7 => write!(f, "a7"),
            Self::S2 => write!(f, "s2"),
            Self::S3 => write!(f, "s3"),
            Self::S4 => write!(f, "s4"),
            Self::S5 => write!(f, "s5"),
            Self::S6 => write!(f, "s6"),
            Self::S7 => write!(f, "s7"),
            Self::S8 => write!(f, "s8"),
            Self::S9 => write!(f, "s9"),
            Self::S10 => write!(f, "s10"),
            Self::S11 => write!(f, "s11"),
            Self::T3 => write!(f, "t3"),
            Self::T4 => write!(f, "t4"),
            Self::T5 => write!(f, "t5"),
            Self::T6 => write!(f, "t6"),
            _ => write!(f, "N/A"),
        }
    }
}

impl Registers {
    /// Create a new `Processor` instance
    pub const fn new() -> Registers {
        Registers { storage: [0; GENERAL_REGISTER_COUNT - 1], pc: 0 }
    }

    /// Get the value of a register.
    pub const fn get(&self, reg: RegId) -> RegVal {
        let reg = reg.get() as usize;
        if reg == 0 {
            return 0;
        }

        // GeneralRegister can't represent out of range indicies.
        // If it manages to do that -- that's a bug
        self.storage[reg - 1]
    }

    pub const fn set(&mut self, reg: RegId, value: RegVal) {
        let reg = reg.get() as usize;
        if reg == 0 {
            return;
        }

        // GeneralRegister can't represent out of range indicies.
        // If it manages to do that -- that's a bug
        self.storage[reg - 1] = value;
    }
}

impl Default for Registers {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::{RegVal, RegValSigned, REGVAL_SIZE_MASK};

    #[test]
    fn signed_unsigned_regval_same_size() {
        assert_eq!(RegVal::BITS, RegValSigned::BITS);
    }

    #[test]
    fn size_mask_correct() {
        let regval_bits_log2 = REGVAL_SIZE_MASK.count_ones();
        assert_eq!((2 as RegVal).pow(regval_bits_log2), RegVal::BITS as RegVal);
    }
}
