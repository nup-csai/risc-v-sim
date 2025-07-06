use thiserror::Error;

#[derive(Error, Debug)]
pub enum ProcessorError {
    #[error("Invalid register number {0}, expected a number between 0 and 31")]
    InvalidRegister(u64),
}

/// The `Processor` struct represents a simple risc-v 64i CPU
#[derive(Debug, Clone, Copy)]
pub struct Processor {
    registers: [u64; 31],
    pub pc: u64,
}

#[derive(Debug, Clone, Copy)]
pub struct Register {
    value: u64,
}

impl Register {
    pub fn get(&self) -> u64 {
        self.value
    }

    pub fn set(&mut self, value: u64) {
        if value > 31 {
            panic!("Invalid register number {}", value);
        }
        self.value = value;
    }

    pub fn from(value: u64) -> Register {
        if value > 31 {
            panic!("Invalid register number {}", value);
        }
        Register { value }
    }
}

impl Processor {
    /// Create a new `Processor` instance
    pub fn new() -> Processor {
        Processor {
            registers: [0; 31],
            pc: 0,
        }
    }

    /// Get the value of a register, private function because is to be used only in the module
    pub fn get_register(&self, reg: Register) -> Result<u64, ProcessorError> {
        let reg_num = reg.get();
        if reg_num == 0 {
            return Ok(0);
        }
        if reg_num > 31 {
            return Err(ProcessorError::InvalidRegister(reg_num));
        }
        Ok(self.registers[(reg_num - 1) as usize])
    }

    /// Set the value of a register, private function because is to be used only in the module
    pub fn set_register(&mut self, reg: Register, value: u64) -> Result<(), ProcessorError> {
        let reg_num = reg.get();
        if reg_num == 0 {
            return Ok(());
        }
        if reg_num > 31 {
            return Err(ProcessorError::InvalidRegister(reg_num));
        }
        self.registers[(reg_num - 1) as usize] = value;
        Ok(())
    }
}
