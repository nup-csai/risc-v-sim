/// The type of the values the CPU works with.
pub type RegVal = u64;
/// The type used to store CPU instructions.
pub type InstrVal = u32;

pub const GENERAL_REGISTER_COUNT: usize = 32;

/// The `Processor` struct represents a simple risc-v 64i CPU
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
pub struct Processor {
    storage: [RegVal; 31],
    pub pc: RegVal,
}

/// [GeneralRegister] represents a validated general purpose register index.
/// In baseline RiscV (rv64i), there are 32 general purpose registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
#[repr(transparent)]
pub struct GeneralRegister(InstrVal);

impl GeneralRegister {
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
    pub const ZERO: GeneralRegister = Self::new(0).unwrap();
    /// Return address.
    /// Saved by caller.
    pub const RA: GeneralRegister = Self::new(1).unwrap();
    /// Stack pointer.
    /// Saved by callee.
    pub const SP: GeneralRegister = Self::new(2).unwrap();
    /// Global pointer
    pub const GP: GeneralRegister = Self::new(3).unwrap();
    /// Thread pointer
    pub const TP: GeneralRegister = Self::new(4).unwrap();
    /// Temporary / alternate return address.
    /// Saved by caller.
    pub const T0: GeneralRegister = Self::new(5).unwrap();
    /// Temporary.
    /// Saved by caller.
    pub const T1: GeneralRegister = Self::new(6).unwrap();
    /// Temporary.
    /// Saved by caller.
    pub const T2: GeneralRegister = Self::new(7).unwrap();
    /// Saved register / frame pointer.
    /// Sometimes called S0.
    /// Saved by callee.
    pub const FP: GeneralRegister = Self::new(8).unwrap();
    /// Saved register.
    /// Saved by callee.
    pub const S1: GeneralRegister = Self::new(9).unwrap();
    /// Function argument / return value.
    pub const A0: GeneralRegister = Self::new(10).unwrap();
    /// Function argument / return value.
    pub const A1: GeneralRegister = Self::new(11).unwrap();
    /// Function argument.
    pub const A2: GeneralRegister = Self::new(12).unwrap();
    /// Function argument.
    /// Saved by caller.
    pub const A3: GeneralRegister = Self::new(13).unwrap();
    /// Function argument.
    /// Saved by caller.
    pub const A4: GeneralRegister = Self::new(14).unwrap();
    /// Function argument.
    /// Saved by caller.
    pub const A5: GeneralRegister = Self::new(15).unwrap();
    /// Function argument.
    /// Saved by caller.
    pub const A6: GeneralRegister = Self::new(16).unwrap();
    /// Function argument.
    /// Saved by caller.
    pub const A7: GeneralRegister = Self::new(17).unwrap();
    /// Saved register.
    /// Saved by callee.
    pub const S2: GeneralRegister = Self::new(18).unwrap();
    /// Saved register.
    /// Saved by callee.
    pub const S3: GeneralRegister = Self::new(19).unwrap();
    /// Saved register.
    /// Saved by callee.
    pub const S4: GeneralRegister = Self::new(20).unwrap();
    /// Saved register.
    /// Saved by callee.
    pub const S5: GeneralRegister = Self::new(21).unwrap();
    /// Saved register.
    /// Saved by callee.
    pub const S6: GeneralRegister = Self::new(22).unwrap();
    /// Saved register.
    /// Saved by callee.
    pub const S7: GeneralRegister = Self::new(23).unwrap();
    /// Saved register.
    /// Saved by callee.
    pub const S8: GeneralRegister = Self::new(24).unwrap();
    /// Saved register.
    /// Saved by callee.
    pub const S9: GeneralRegister = Self::new(25).unwrap();
    /// Saved register.
    /// Saved by callee.
    pub const S10: GeneralRegister = Self::new(26).unwrap();
    /// Saved register.
    /// Saved by callee.
    pub const S11: GeneralRegister = Self::new(27).unwrap();
    /// Temporary.
    /// Saved by caller.
    pub const T3: GeneralRegister = Self::new(28).unwrap();
    /// Temporary.
    /// Saved by caller.
    pub const T4: GeneralRegister = Self::new(29).unwrap();
    /// Temporary.
    /// Saved by caller.
    pub const T5: GeneralRegister = Self::new(30).unwrap();
    /// Temporary.
    /// Saved by caller.
    pub const T6: GeneralRegister = Self::new(31).unwrap();
}

impl Processor {
    /// Create a new `Processor` instance
    pub const fn new() -> Processor {
        Processor { storage: [0; GENERAL_REGISTER_COUNT - 1], pc: 0 }
    }

    /// Get the value of a register.
    pub const fn get_register(&self, reg: GeneralRegister) -> RegVal {
        let reg = reg.get() as usize;
        if reg == 0 {
            return 0;
        }

        // GeneralRegister can't represent out of range indicies.
        // If it manages to do that -- that's a bug
        self.storage[reg - 1]
    }

    pub const fn set_register(&mut self, reg: GeneralRegister, value: RegVal) {
        let reg = reg.get() as usize;
        if reg == 0 {
            return;
        }

        // GeneralRegister can't represent out of range indicies.
        // If it manages to do that -- that's a bug
        self.storage[reg - 1] = value;
    }
}
