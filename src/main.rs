use clap::Parser;
use risc_v_sim::{run_cli, Args};
use std::process::ExitCode;

fn main() -> ExitCode {
    let args = Args::parse();
    if let Err(e) = run_cli(args) {
        eprintln!("{e}");
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}
