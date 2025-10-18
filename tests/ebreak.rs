//! The integration test for the ebreak instruction.
//! Uses the ebreak.elf artifact from QEMU trace capturer.
//! Please make sure you have captured the QEMU traces first.
//! For more information, see the README in `riscv-samples`.

mod common;
use common::*;

use std::path::PathBuf;

use log::info;
use risc_v_sim::kernel::{InstrVal, RegVal, Registers};

/// Ebreak test makes sure the shell terminates after it
/// incounters the ebreak instruction.
#[test]
fn ebreak() {
    init_test();

    let elf_path = PathBuf::from_iter(["riscv-samples", "bin", "ebreak.elf"]);
    let mut ebreak_trace = [Registers::new(); 3];
    for (idx, entry) in ebreak_trace.iter_mut().enumerate() {
        let off = ((idx + 1) * std::mem::size_of::<InstrVal>()) as RegVal;
        entry.pc = SIMULATION_PROGRAM_OFFSET + off;
    }

    KernelRunner::new_with_trace(elf_path, &ebreak_trace).run();
    info!("Pass");
}
