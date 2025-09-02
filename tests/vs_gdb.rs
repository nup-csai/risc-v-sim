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

use risc_v_sim::kernel::GeneralRegister;

static TRACER_NAME: &str = "trace_capture";

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
struct TraceEntry {
    ra: u64,
    sp: u64,
    gp: u64,
    tp: u64,
    t0: u64,
    t1: u64,
    t2: u64,
    fp: u64,
    s1: u64,
    a0: u64,
    a1: u64,
    a2: u64,
    a3: u64,
    a4: u64,
    a5: u64,
    a6: u64,
    a7: u64,
    s2: u64,
    s3: u64,
    s4: u64,
    s5: u64,
    s6: u64,
    s7: u64,
    s8: u64,
    s9: u64,
    s10: u64,
    s11: u64,
    t3: u64,
    t4: u64,
    t5: u64,
    t6: u64,
    pc: u64,
}

#[test]
fn test_vs_gdb() {
    let files_with_tick_count = [
        ("basic.s", 4),
        ("basic2.s", 6),
        ("auipc.s", 5),
        ("load_constant.s", 2),
        ("loop.s", 8),
        ("jumps.s", 10),
        ("calls.s", 10),
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
    let Ok(val) = u64::from_str_radix(val, 16) else {
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

fn simulate_elf(filename: &str, tick_count: usize) -> Vec<TraceEntry> {
    let mut elf_path = PathBuf::from_iter(["tests", "elfs", filename]);
    elf_path.set_extension("s.elf");

    let mut result = Vec::new();
    let info = risc_v_sim::shell::load_program_from_file(&elf_path).unwrap();
    let mut kernel =
        risc_v_sim::kernel::Kernel::from_program(info.program, info.entry, info.load_address);

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
