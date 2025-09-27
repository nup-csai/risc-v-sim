use std::{
    fs::{self},
    io::{BufRead, BufReader},
    path::PathBuf,
};

use risc_v_sim::kernel::{
    InstrVal, KernelStep, Memory, MemorySegment, RegId, RegVal, Registers, GENERAL_REGISTER_COUNT,
};

const SIMULATION_PROGRAM_OFFSET: RegVal = 0x80000000;
const SIMULATION_RW_MEM_OFFSET: RegVal = 0x1000;
const SIUMLATION_RW_MEM_SIZE: RegVal = 0x8000;

#[test]
fn vs_qemu_traces() {
    let traces_dir = PathBuf::from_iter(["riscv-samples", "traces"])
        .canonicalize()
        .unwrap();
    println!("checking trace dir: {traces_dir:?}");

    let traces_exist = fs::exists(&traces_dir).unwrap();
    assert!(
        traces_exist,
        "trace directory not found. Make sure you build and capture the samples"
    );

    let mut ran_tests = false;
    for entry in std::fs::read_dir(traces_dir).unwrap() {
        ran_tests = true;

        let entry = entry.unwrap().path().canonicalize().unwrap();
        let Some(extension) = entry.extension() else {
            println!("Skipping {entry:?} (not a file with extension)");
            continue;
        };
        if extension != "trace" {
            println!("Skipping {entry:?} (file doesn't have a .trace extension)");
            continue;
        }

        let filename = entry
            .file_name()
            .expect("File has extension but now filename");
        let mut elf_path = PathBuf::from_iter(["riscv-samples", "bin"]);
        elf_path.push(filename);
        elf_path.set_extension("elf");

        println!("Reading trace from {entry:?}");
        let qemu_trace = read_qemu_trace(entry);

        println!("Simulating {elf_path:?}");
        assert_elf_trace(elf_path, &qemu_trace);

        println!("Pass");
    }

    assert!(ran_tests, "no tests were run");
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

fn assert_elf_trace(elf_path: PathBuf, qemu_trace: &[Registers]) {
    let info = risc_v_sim::shell::load_program_from_file(&elf_path).unwrap();
    let entry_point = info.entry;
    assert_eq!(info.load_address, SIMULATION_PROGRAM_OFFSET);

    let mut mem = Memory::new();
    // QEMU lets you use the whole 0x80000000:0x8000000 segment as RAM.
    // Let's assume the program will always fit into first 4Kb, so the next
    // 4Kb will be reserved by the memory for program to write to.
    info.load_into_memory(&mut mem, true, false).unwrap();
    mem.add_segment(MemorySegment::new_zeroed(
        true,
        true,
        false,
        SIMULATION_PROGRAM_OFFSET + SIMULATION_RW_MEM_OFFSET,
        SIUMLATION_RW_MEM_SIZE,
    ))
    .unwrap();

    let mut kernel_trace = Vec::new();
    let mut kernel = risc_v_sim::kernel::Kernel::new(mem, entry_point);
    for (idx, qemu_step) in qemu_trace.iter().enumerate() {
        let step = match kernel.step() {
            Ok(x) => x,
            Err(e) => {
                dump_trace(&kernel_trace);
                panic!("Simulation fail: {e}");
            }
        };
        kernel_trace.push(step);

        let trace_entry = step.new_registers;
        if trace_entry != *qemu_step {
            dump_trace(&kernel_trace);
            find_mismatches_in_regs(&trace_entry, qemu_step);
            panic!("simulation mismatched qemu on step {idx}");
        }
    }
}

fn dump_trace(kernel_trace: &[KernelStep]) {
    for step in kernel_trace {
        println!("{step:?}");
    }
}

static REGID_TO_NAME: [&str; GENERAL_REGISTER_COUNT] = [
    "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "fp", "s1", "a0", "a1", "a2", "a3", "a4",
    "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4",
    "t5", "t6",
];

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

fn find_mismatches_in_regs(found: &Registers, expected: &Registers) {
    if found.pc != expected.pc {
        println!(
            "mismatch: pc. Expected {:#x}, found {:#}",
            expected.pc, found.pc
        );
    }
    for idx in 0..GENERAL_REGISTER_COUNT {
        let name = REGID_TO_NAME[idx];
        let idx = RegId::new(idx as InstrVal).unwrap();
        let (found_reg, expected_reg) = (found.get(idx), expected.get(idx));
        if found_reg != expected_reg {
            println!("mismatch: {name}. Expected {expected_reg:#x}, found {found_reg:#x}");
        }
    }
}
