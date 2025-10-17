//! The integration test for the ebreak instruction.
//! Uses the ebreak.elf artifact from QEMU trace capturer.
//! Please make sure you have captured the QEMU traces first.
//! For more information, see the README in `riscv-samples`.

use std::path::PathBuf;

use env_logger::Builder;
use log::info;
use risc_v_sim::{
    kernel::{
        GENERAL_REGISTER_COUNT, InstrVal, Kernel, KernelStep, MemorySegment, RegId, RegVal,
        Registers,
    },
    shell::{load_program_from_file, run_kernel},
};

const SIMULATION_PROGRAM_OFFSET: RegVal = 0x80000000;
const SIMULATION_RW_MEM_OFFSET: RegVal = 0x1000;
const SIUMLATION_RW_MEM_SIZE: RegVal = 0x8000;

/// Ebreak test makes sure the shell terminates after it
/// incounters the ebreak instruction.
#[test]
fn ebreak() {
    Builder::new()
        .is_test(true)
        .filter_level(log::LevelFilter::Debug)
        .init();

    let elf_path = PathBuf::from_iter(["riscv-samples", "bin", "ebreak.elf"]);
    let mut ebreak_trace = [Registers::new(); 3];
    ebreak_trace[0].pc = 0x80000004;
    ebreak_trace[1].pc = 0x80000008;
    ebreak_trace[2].pc = 0x8000000C;
    assert_elf_trace(elf_path, &ebreak_trace);

    info!("Pass");
}

fn assert_elf_trace(elf_path: PathBuf, qemu_trace: &[Registers]) {
    let mut kernel = Kernel::from_program(&load_program_from_file(&elf_path).unwrap());
    kernel
        .memory
        .add_segment(MemorySegment::new_zeroed(
            true,
            true,
            false,
            SIMULATION_PROGRAM_OFFSET + SIMULATION_RW_MEM_OFFSET,
            SIUMLATION_RW_MEM_SIZE,
        ))
        .unwrap();
    let run_res = run_kernel(&mut kernel, 5);
    assert!(run_res.err.is_none());

    for (idx, (qemu_step, step)) in qemu_trace.iter().zip(&run_res.steps).enumerate() {
        let trace_entry = step.new_registers;
        if trace_entry != *qemu_step {
            dump_trace(&run_res.steps);
            find_mismatches_in_regs(&trace_entry, qemu_step);
            panic!("simulation mismatched qemu on step {idx}");
        }
    }
}

fn dump_trace(kernel_trace: &[KernelStep]) {
    for step in kernel_trace {
        info!("{step:x?}");
    }
}

static REGID_TO_NAME: [&str; GENERAL_REGISTER_COUNT] = [
    "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "fp", "s1", "a0", "a1", "a2", "a3", "a4",
    "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4",
    "t5", "t6",
];

fn find_mismatches_in_regs(found: &Registers, expected: &Registers) {
    if found.pc != expected.pc {
        info!(
            "mismatch: pc. Expected {:#x}, found {:#x}",
            expected.pc, found.pc
        );
    }
    for idx in 0..GENERAL_REGISTER_COUNT {
        let name = REGID_TO_NAME[idx];
        let idx = RegId::new(idx as InstrVal).unwrap();
        let (found_reg, expected_reg) = (found.get(idx), expected.get(idx));
        if found_reg != expected_reg {
            info!("mismatch: {name}. Expected {expected_reg:#x}, found {found_reg:#x}");
        }
    }
}
