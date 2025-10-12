use clap::Parser;
use log::error;
use risc_v_sim::{Args, run_cli};
use std::process::ExitCode;

fn main() -> ExitCode {
    env_logger::builder().parse_default_env().init();

    let args = Args::parse();
    if let Err(e) = run_cli(args) {
        error!("{e}");
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}
