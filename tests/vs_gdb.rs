//! Tests that compare rvsim to qemu. We do that by capturing a small
//! trace of what qemu does with GDB. The way we do it can be seen in
//! the ./samples directory. You can run the trace capture part yourself
//! locally if you have docker installed:
//! docker run
//!  --rm
//!  -a STDOUT
//!  --name trace_capture
//!  --tmpfs /tmp
//!  --mount type=bind,src=./tests/samples/,dst=/ws,ro
//!  --mount type=bind,src=./tests/elfs/,dst=/elfs
//!  krinkin/rv64-toolchain
//!  /usr/bin/bash
//!   /ws/capture_trace.sh /ws/ASM.s TICKCOUNT

use std::{fs, io, path::PathBuf, process};

use risc_v_sim::kernel::{GeneralRegister, Memory, MemorySegment, RegisterVal};

#[test]
fn test_vs_gdb() {
    let files_with_tick_count = [
        ("basic.s", 4),
        ("basic2.s", 6),
        ("xoriadd.s", 7),
        ("auipc.s", 5),
        ("load_constant.s", 2),
        ("loop.s", 8),
        ("jumps.s", 10),
        ("calls.s", 10),
        ("basic_mem.s", 7),
    ];

    // Create a dir for placing the built elfs
    let elfs_dir = PathBuf::from_iter(["tests", "elfs"]);
    if !fs::exists(&elfs_dir).unwrap() {
        fs::create_dir(&elfs_dir).unwrap();
    }

    for (filename, tick_count) in files_with_tick_count {
        println!("Capturing: {filename:?}");
        let docker_out = run_qemu_command(filename, tick_count);
        let qemu_trace = parse_trace(docker_out);
        assert_eq!(qemu_trace.len(), tick_count);

        println!("Simulating the elf");
        let simulated_trace = simulate_elf(filename, tick_count);
        assert_eq!(simulated_trace.len(), tick_count);

        assert_eq!(qemu_trace, simulated_trace);
        println!("Pass: {filename:?}");
    }
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
struct TraceEntry {
    ra: RegisterVal,
    sp: RegisterVal,
    gp: RegisterVal,
    tp: RegisterVal,
    t0: RegisterVal,
    t1: RegisterVal,
    t2: RegisterVal,
    fp: RegisterVal,
    s1: RegisterVal,
    a0: RegisterVal,
    a1: RegisterVal,
    a2: RegisterVal,
    a3: RegisterVal,
    a4: RegisterVal,
    a5: RegisterVal,
    a6: RegisterVal,
    a7: RegisterVal,
    s2: RegisterVal,
    s3: RegisterVal,
    s4: RegisterVal,
    s5: RegisterVal,
    s6: RegisterVal,
    s7: RegisterVal,
    s8: RegisterVal,
    s9: RegisterVal,
    s10: RegisterVal,
    s11: RegisterVal,
    t3: RegisterVal,
    t4: RegisterVal,
    t5: RegisterVal,
    t6: RegisterVal,
    pc: RegisterVal,
}

static TRACER_NAME: &str = "trace_capture";

fn run_qemu_command(filename: &str, tick_count: usize) -> process::Output {
    let tick_count = tick_count.to_string();
    let mut cmd = process::Command::new("docker");
    let out = cmd
        .arg("run")
        .args(["-a", "STDOUT"])
        .args(["-a", "STDERR"])
        .args(["--name", TRACER_NAME])
        .args(["--tmpfs", "/tmp"])
        .args(["--mount", "type=bind,src=./tests/samples/,dst=/ws,ro"])
        .args(["--mount", "type=bind,src=./tests/elfs/,dst=/elfs"])
        .arg("krinkin/rv64-toolchain")
        .args([
            "/usr/bin/bash",
            "/ws/capture_trace.sh",
            &filename,
            &tick_count,
        ])
        .output()
        .unwrap();

    let result = process::Command::new("docker")
        .args(["rm", TRACER_NAME])
        .output();
    if let Err(e) = result {
        println!("Cleanup failed: {e}");
    }

    if !out.status.success() {
        let stderr = String::from_utf8_lossy(&out.stderr);
        panic!("docker failed: {stderr}");
    }
    out
}

fn parse_trace(docker_out: process::Output) -> Vec<TraceEntry> {
    let mut io = io::Cursor::new(docker_out.stdout);
    std::iter::from_fn(move || parse_trace_step(&mut io).unwrap())
        .skip(1)
        .collect::<Vec<_>>()
}

fn parse_trace_step(io: impl io::BufRead) -> io::Result<Option<TraceEntry>> {
    let mut entry = TraceEntry::default();

    for line in io.lines() {
        let line = line.unwrap();
        if line == "===NEXT" || line == "===END" {
            println!("{entry:?}");
            return Ok(Some(entry));
        }
        parse_register_entry(&line, &mut entry);
    }

    Ok(None)
}

fn parse_register_entry(line: &str, entry: &mut TraceEntry) {
    let mut it = line.split_ascii_whitespace();
    let Some(name) = it.next() else {
        return;
    };
    let Some(val) = it.next() else { return };
    // Cut off the 0x part. Rust's number parser doesn't like it.
    let Some(val) = val.get(2..) else {
        return;
    };
    let Ok(val) = RegisterVal::from_str_radix(val, 16) else {
        return;
    };

    match name {
        "ra" => entry.ra = val,
        "sp" => entry.sp = val,
        "gp" => entry.gp = val,
        "tp" => entry.tp = val,
        "t0" => entry.t0 = val,
        "t1" => entry.t1 = val,
        "t2" => entry.t2 = val,
        "fp" => entry.fp = val,
        "s1" => entry.s1 = val,
        "a0" => entry.a0 = val,
        "a1" => entry.a1 = val,
        "a2" => entry.a2 = val,
        "a3" => entry.a3 = val,
        "a4" => entry.a4 = val,
        "a5" => entry.a5 = val,
        "a6" => entry.a6 = val,
        "a7" => entry.a7 = val,
        "s2" => entry.s2 = val,
        "s3" => entry.s3 = val,
        "s4" => entry.s4 = val,
        "s5" => entry.s5 = val,
        "s6" => entry.s6 = val,
        "s7" => entry.s7 = val,
        "s8" => entry.s8 = val,
        "s9" => entry.s9 = val,
        "s10" => entry.s10 = val,
        "s11" => entry.s11 = val,
        "t3" => entry.t3 = val,
        "t4" => entry.t4 = val,
        "t5" => entry.t5 = val,
        "t6" => entry.t6 = val,
        "pc" => entry.pc = val,
        _ => (),
    }
}

const SIMULATION_PROGRAM_OFFSET: RegisterVal = 0x80000000;
const SIMULATION_RW_MEM_OFFSET: RegisterVal = 0x1000;
const SIUMLATION_RW_MEM_SIZE: RegisterVal = 0x8000;

fn simulate_elf(filename: &str, tick_count: usize) -> Vec<TraceEntry> {
    let mut elf_path = PathBuf::from_iter(["tests", "elfs", filename]);
    elf_path.set_extension("s.elf");

    let mut result = Vec::new();
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

    let mut kernel = risc_v_sim::kernel::Kernel::new(mem, entry_point);

    for _ in 0..tick_count {
        let kernel_step = kernel.step().unwrap();
        println!("{kernel_step:?}");
        result.push(kernel_step_to_trace_entry(kernel_step));
    }

    result
}

fn kernel_step_to_trace_entry(kernel_step: risc_v_sim::kernel::KernelStep) -> TraceEntry {
    TraceEntry {
        ra: kernel_step.new_processor.get_register(GeneralRegister::RA),
        sp: kernel_step.new_processor.get_register(GeneralRegister::SP),
        gp: kernel_step.new_processor.get_register(GeneralRegister::GP),
        tp: kernel_step.new_processor.get_register(GeneralRegister::TP),
        t0: kernel_step.new_processor.get_register(GeneralRegister::T0),
        t1: kernel_step.new_processor.get_register(GeneralRegister::T1),
        t2: kernel_step.new_processor.get_register(GeneralRegister::T2),
        fp: kernel_step.new_processor.get_register(GeneralRegister::FP),
        s1: kernel_step.new_processor.get_register(GeneralRegister::S1),
        a0: kernel_step.new_processor.get_register(GeneralRegister::A0),
        a1: kernel_step.new_processor.get_register(GeneralRegister::A1),
        a2: kernel_step.new_processor.get_register(GeneralRegister::A2),
        a3: kernel_step.new_processor.get_register(GeneralRegister::A3),
        a4: kernel_step.new_processor.get_register(GeneralRegister::A4),
        a5: kernel_step.new_processor.get_register(GeneralRegister::A5),
        a6: kernel_step.new_processor.get_register(GeneralRegister::A6),
        a7: kernel_step.new_processor.get_register(GeneralRegister::A7),
        s2: kernel_step.new_processor.get_register(GeneralRegister::S2),
        s3: kernel_step.new_processor.get_register(GeneralRegister::S3),
        s4: kernel_step.new_processor.get_register(GeneralRegister::S4),
        s5: kernel_step.new_processor.get_register(GeneralRegister::S5),
        s6: kernel_step.new_processor.get_register(GeneralRegister::S6),
        s7: kernel_step.new_processor.get_register(GeneralRegister::S7),
        s8: kernel_step.new_processor.get_register(GeneralRegister::S8),
        s9: kernel_step.new_processor.get_register(GeneralRegister::S9),
        s10: kernel_step.new_processor.get_register(GeneralRegister::S10),
        s11: kernel_step.new_processor.get_register(GeneralRegister::S11),
        t3: kernel_step.new_processor.get_register(GeneralRegister::T3),
        t4: kernel_step.new_processor.get_register(GeneralRegister::T4),
        t5: kernel_step.new_processor.get_register(GeneralRegister::T5),
        t6: kernel_step.new_processor.get_register(GeneralRegister::T6),
        pc: kernel_step.new_processor.pc,
    }
}
