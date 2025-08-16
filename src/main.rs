use std::io::Write;

use clap::Parser;
use risc_v_sim::kernel::Kernel;
use risc_v_sim::shell::{load_program_from_file, ShellError};

/// MVP of RVsim!
#[derive(Parser, Debug)]
struct Args {
    /// Path to the .elf file
    #[arg(short, long)]
    path: String,
}

const MAX_STEPS: usize = 10;

fn main() -> Result<(), ShellError> {
    let args = Args::parse();
    let info = load_program_from_file(&args.path)?;

    let mut kernel = Kernel::new(info.program, info.entry, info.load_address);
    for _ in 0..MAX_STEPS {
        match kernel.step() {
            Err(e) => return Err(ShellError::KernelError(e)),
            Ok(s) => {
                let mut stdout = std::io::stdout().lock();
                serde_json::ser::to_writer(&mut stdout, &s).unwrap();
                stdout.write(std::slice::from_ref(&b'\n')).unwrap();
            }
        }
    }

    Ok(())
}
