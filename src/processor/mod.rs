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
    fn get_register(&self, reg: u64) -> Result<u64, &str> {
        if reg == 0 {
            return Ok(0);
        }
        if reg > 31 {
            return Err("Invalid register number");
        }
        Ok(self.registers[(reg - 1) as usize])
    }

    /// Set the value of a register, private function because is to be used only in the module
    fn set_register(&mut self, reg: u64, value: u64) -> Result<(), &str> {
        if reg == 0 {
            return Err("Cannot set register 0");
        }
        if reg > 31 {
            return Err("Invalid register number");
        }
        self.registers[(reg - 1) as usize] = value;
        Ok(())
    }
}
