#![allow(dead_code)]

use std::path::PathBuf;

use env_logger::Builder;
use log::info;
use risc_v_sim::kernel::{GENERAL_REGISTER_COUNT, InstrVal, Kernel, RegId, RegVal, Registers};
use risc_v_sim::shell::{KernelDef, MemorySegmentDef, RunResult, run_from_spec};

pub const SIMULATION_PROGRAM_OFFSET: RegVal = 0x80000000;
pub static TEST_MEM_DIR: &str = "test-mems";

pub fn make_test_mem_path(filename: impl AsRef<str>) -> PathBuf {
    let mut mem_path = PathBuf::from(TEST_MEM_DIR);
    mem_path.push(filename.as_ref());
    mem_path.set_extension("bin");

    mem_path
}

pub fn init_test() {
    Builder::new()
        .is_test(true)
        .filter_level(log::LevelFilter::Debug)
        .init();
    let _ = std::fs::create_dir(TEST_MEM_DIR);
}

struct ExpectedMem {
    off: RegVal,
    data: Box<[u8]>,
}

#[derive(Default)]
pub struct KernelRunner<'a> {
    elf_path: PathBuf,
    step_count: Option<usize>,
    expected_trace: Option<&'a [Registers]>,
    inputs: Vec<MemorySegmentDef>,
    outputs: Vec<MemorySegmentDef>,
    expected_mems: Vec<ExpectedMem>,
}

impl<'a> KernelRunner<'a> {
    pub fn new_with_steps(elf_path: PathBuf, step_count: usize) -> Self {
        KernelRunner { elf_path, step_count: Some(step_count), ..Default::default() }
    }

    pub fn new_with_trace(elf_path: PathBuf, expected_trace: &'a [Registers]) -> Self {
        KernelRunner { elf_path, expected_trace: Some(expected_trace), ..Default::default() }
    }

    pub fn with_input(&mut self, input: MemorySegmentDef) -> &mut Self {
        self.inputs.push(input);
        self
    }

    pub fn with_output(&mut self, output: MemorySegmentDef) -> &mut Self {
        self.outputs.push(output);
        self
    }

    pub fn with_expected_mem(&mut self, off: RegVal, data: &[u8]) -> &mut Self {
        self.expected_mems
            .push(ExpectedMem { off, data: data.into() });
        self
    }

    pub fn run(&self) {
        let step_count = match (self.expected_trace, self.step_count) {
            (None, None) => {
                panic!("At least one of expected trace or step count must be specified")
            }
            (Some(_), Some(_)) => panic!("Do not specify both trace and step count"),
            (Some(tr), None) => tr.len(),
            (None, Some(c)) => c,
        };
        let kern_def = KernelDef {
            elfpath: self.elf_path.clone(),
            inputs: self.inputs.clone(),
            outputs: self.outputs.clone(),
        };
        let (kernel, run_res) = run_from_spec(kern_def, step_count).unwrap();
        info!("Kernel has been run");
        if let Some(err) = &run_res.err {
            panic!("Kernel error during execution: {}", err.msg);
        }

        self.check_trace(&run_res);
        self.check_mem(&kernel);
    }

    fn check_trace(&self, run_res: &RunResult) {
        let Some(trace) = self.expected_trace else {
            info!("Skipping trace check: no expected trace specified");
            return;
        };

        info!("Comparing traces");
        assert_eq!(
            run_res.steps.len(),
            trace.len(),
            "Traces have different lengths"
        );
        let iter = run_res.steps.iter().zip(trace).enumerate();
        for (idx, (kern_step, expected_step)) in iter {
            let found_step = kern_step.new_registers;
            if found_step != *expected_step {
                find_mismatches_in_regs(&found_step, expected_step);
                panic!("simulation mismatched qemu on step {idx}");
            }
        }
    }

    fn check_mem(&self, kernel: &Kernel) {
        info!("Checking memory");
        // NOTE: this works only when the user provides
        //       memory expectations, that do not cross segment boundaries
        for mem in self.expected_mems.iter() {
            info!("Checking {:#x}:{:#x}", mem.off, mem.data.len());

            let segment = kernel.memory.find_segment(mem.off).unwrap();
            let local_start = (mem.off - segment.off) as usize;
            let local_end = local_start + mem.data.len();
            let found_mem = &segment.as_bytes()[local_start..local_end];

            assert_eq!(&*mem.data, found_mem);
            info!("Checking {:#x}:{:#x}: pass", mem.off, mem.data.len());
        }
    }
}

pub static REGID_TO_NAME: [&str; GENERAL_REGISTER_COUNT] = [
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
