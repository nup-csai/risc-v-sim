use thiserror::Error;

#[derive(Error, Debug)]
pub enum ProcessorError {
    #[error("Invalid register number {0}, expected a number between 0 and 31")]
    InvalidRegister(u64),

    #[error("Cannot set register 0")]
    CannotSetRegisterZero,
}

/// The `Processor` struct represents a simple risc-v 64i CPU
#[derive(Debug, Clone, Copy)]
pub struct Processor {
    registers: [u64; 31],
    pc: u64,
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
    pub fn get_register(&self, reg: u64) -> Result<u64, ProcessorError> {
        if reg == 0 {
            return Ok(0);
        }
        if reg > 31 {
            return Err(ProcessorError::InvalidRegister(reg));
        }
        Ok(self.registers[(reg - 1) as usize])
    }

    /// Set the value of a register, private function because is to be used only in the module
    pub fn set_register(&mut self, reg: u64, value: u64) -> Result<(), ProcessorError> {
        if reg == 0 {
            return Err(ProcessorError::CannotSetRegisterZero);
        }
        if reg > 31 {
            return Err(ProcessorError::InvalidRegister(reg));
        }
        self.registers[(reg - 1) as usize] = value;
        Ok(())
    }
}
