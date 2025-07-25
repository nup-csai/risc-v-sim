/// The type of the values the CPU works with.
pub type RegisterVal = u64;
/// The type used to store CPU instructions.
pub type InstructionVal = u32;

pub const GENERAL_REGISTER_COUNT: usize = 32;

/// The `Processor` struct represents a simple risc-v 64i CPU
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
pub struct Processor {
    registers: [RegisterVal; 31],
    pub pc: RegisterVal,
}

/// [GeneralRegister] represents a validated general purpose register index.
/// In baseline RiscV (rv64i), there are 32 general purpose registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
#[repr(transparent)]
pub struct GeneralRegister(InstructionVal);

impl GeneralRegister {
    pub fn new(value: InstructionVal) -> Option<Self> {
        (value < GENERAL_REGISTER_COUNT as InstructionVal).then_some(Self(value))
    }

    pub fn get(&self) -> InstructionVal {
        self.0
    }
}

impl Processor {
    /// Create a new `Processor` instance
    pub fn new() -> Processor {
        Processor {
            registers: [0; GENERAL_REGISTER_COUNT - 1],
            pc: 0,
        }
    }

    /// Get the value of a register.
    pub fn get_register(&self, reg: GeneralRegister) -> RegisterVal {
        let reg = reg.get() as usize;
        if reg == 0 {
            return 0;
        }

        // GeneralRegister can't represent out of range indicies.
        // If it manages to do that -- that's a bug
        self.registers[reg - 1]
    }

    pub fn set_register(&mut self, reg: GeneralRegister, value: RegisterVal) {
        let reg = reg.get() as usize;
        if reg == 0 {
            return;
        }

        // GeneralRegister can't represent out of range indicies.
        // If it manages to do that -- that's a bug
        self.registers[reg - 1] = value;
    }
}
