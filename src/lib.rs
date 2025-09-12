pub mod kernel;
pub mod shell;

use std::io::Write;
use std::path::PathBuf;

use clap::Parser;
use kernel::Kernel;
use shell::{load_program_from_file, ShellError};

use crate::kernel::Memory;

/// Emulates RiscV programs. After each step, the program
/// prints a trace step into standard output. Each trace step
/// is a JSON message located on a single line. A line break
/// means the end of a trace step.
///
/// It is guaranteed that the program will not print anything
/// else to the standard output, so the user may freely pipe
/// the output into a JSON-parsing program.
///
/// All errors will be reported into standard error.
#[derive(Parser, Debug)]
pub struct Args {
    /// Path to the .elf file
    #[arg(short, long)]
    path: PathBuf,
    /// Amount of ticks to do
    #[arg(short, long)]
    ticks: usize,
}

pub fn run(args: Args) -> Result<(), ShellError> {
    let info = load_program_from_file(&args.path)?;
    let entry_point = info.entry;
    let mut memory = Memory::new();

    info.load_into_memory(&mut memory, false, false)
        .map_err(ShellError::LoadingProramIntoMemory)?;

    let mut kernel = Kernel::new(memory, entry_point);
    for _ in 0..args.ticks {
        let step = kernel.step().map_err(ShellError::KernelError)?;
        let mut stdout = std::io::stdout().lock();
        serde_json::ser::to_writer(&mut stdout, &step).unwrap();
        stdout.write(std::slice::from_ref(&b'\n')).unwrap();
    }

    Ok(())
}
