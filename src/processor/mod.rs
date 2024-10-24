/// The `Processor` struct represents a simple risc-v 64i CPU
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_set_get_register() {
        let mut processor = Processor::new();

        assert_eq!(processor.set_register(1, 15), Ok(()));
        let value = processor.get_register(1).unwrap();
        assert_eq!(value, 15);
    }

    #[test]
    fn test_register0() {
        let mut processor = Processor::new();

        assert_eq!(
            processor.set_register(0, 34543),
            Err("Cannot set register 0")
        );
        assert!(processor.get_register(0).is_ok());
        assert_eq!(processor.get_register(0), Ok(0));
    }

    #[test]
    fn test_register() {
        let mut processor = Processor::new();

        assert_eq!(
            processor.set_register(32, 34543),
            Err("Invalid register number")
        );
        assert_eq!(processor.get_register(320), Err("Invalid register number"));
    }
}
