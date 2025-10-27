//! The integration tests for checking risc-v-sim against QEMU.
//! Please make sure you have captured the QEMU traces first.
//! For more information, see the README in `riscv-samples`.

mod common;
use common::*;

use std::fs::{self};
use std::io::{BufRead, BufReader};
use std::path::PathBuf;

use log::info;
use risc_v_sim::kernel::{InstrVal, RegId, RegVal, Registers};
use risc_v_sim::shell::MemorySegmentDef;

const SIMULATION_RW_MEM_OFFSET: RegVal = 0x1000;
const SIUMLATION_RW_MEM_SIZE: RegVal = 0x1000;

#[test]
fn vs_qemu_traces() {
    init_test();

    let traces_dir = PathBuf::from_iter(["riscv-samples", "traces"])
        .canonicalize()
        .unwrap();
    info!("checking trace dir: {traces_dir:?}");

    let traces_exist = fs::exists(&traces_dir).unwrap();
    assert!(
        traces_exist,
        "trace directory not found. Make sure you build and capture the samples"
    );

    for entry in std::fs::read_dir(traces_dir).unwrap() {
        let entry = entry.unwrap().path().canonicalize().unwrap();
        let Some(extension) = entry.extension() else {
            info!("Skipping {entry:?} (not a file with extension)");
            continue;
        };
        if extension != "trace" {
            info!("Skipping {entry:?} (file doesn't have a .trace extension)");
            continue;
        }

        let filename = entry
            .file_name()
            .expect("File has extension but now filename");
        let mut elf_path = PathBuf::from_iter(["riscv-samples", "bin"]);
        elf_path.push(filename);
        elf_path.set_extension("elf");

        let mem_path = make_test_mem_path("vsqemu-".to_string() + filename.to_str().unwrap());

        info!("Reading trace from {entry:?}");
        let qemu_trace = read_qemu_trace(entry);

        info!("Simulating {elf_path:?}");
        // QEMU lets you use the whole 0x80000000:0x8000000 segment as RAM.
        // Let's assume the program will always fit into first 4Kb, so the next
        // 4Kb will be reserved by the memory for program to write to.
        KernelRunner::new_with_trace(elf_path, &qemu_trace)
            .with_output(MemorySegmentDef {
                off: SIMULATION_PROGRAM_OFFSET + SIMULATION_RW_MEM_OFFSET,
                len: SIUMLATION_RW_MEM_SIZE,
                is_read: true,
                is_write: true,
                is_execute: false,
                path: mem_path,
            })
            .run();

        info!("Pass");
    }
}

fn read_qemu_trace(path: PathBuf) -> Vec<Registers> {
    let mut regs = Registers::new();
    let mut result = Vec::new();
    let file = BufReader::new(fs::File::open(path).unwrap());
    for line in file.lines() {
        let line = line.unwrap();
        if line == "===NEXT" {
            result.push(regs);
        }
        parse_reg_from_line(&mut regs, &line);
    }

    result
}

fn parse_reg_from_line(regs: &mut Registers, line: &str) {
    let mut it = line.split_ascii_whitespace();
    let Some(name) = it.next() else {
        return;
    };
    let Some(val) = it.next() else {
        return;
    };
    // Cut off the 0x part. Rust's number parser doesn't like it.
    let Some(val) = val.get(2..) else {
        return;
    };
    let Ok(val) = RegVal::from_str_radix(val, 16) else {
        return;
    };

    if name == "pc" {
        regs.pc = val;
        return;
    }
    match REGID_TO_NAME.iter().position(|x| *x == name) {
        Some(idx) => regs.set(RegId::new(idx as InstrVal).unwrap(), val),
        None => panic!("unknown reg {name:?}"),
    }
}
