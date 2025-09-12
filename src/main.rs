use clap::Parser;
use risc_v_sim::{run, Args};
use std::process::ExitCode;

fn main() -> ExitCode {
    let args = Args::parse();
    if let Err(e) = run(args) {
        eprintln!("{e}");
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}
