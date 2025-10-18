//! The integration test for the ebreak instruction.
//! Uses the cpy_arbitrary.elf artifact from QEMU trace capturer.
//! Please make sure you have captured the QEMU traces first.
//! For more information, see the README in `riscv-samples`.

mod common;
use common::*;

use std::fs::File;
use std::io::Write;
use std::path::PathBuf;

use log::info;
use risc_v_sim::kernel::RegVal;
use risc_v_sim::shell::MemorySegmentDef;

static MSG: &[u8] = b"Hello, world";
const OUTPUT_OFFSET: RegVal = 0x400;

/// basic_mount test check risc-v-sim's segment mounting functionality.
/// It does so by running a simplistic memcpy, where
/// * source is an input segment (file basic_mount-input.bin)
/// * destination is an output segment (file basic_mount-output.bin)
#[test]
fn basic_mount() {
    init_test();

    let elf_path = PathBuf::from_iter(["riscv-samples", "bin", "cpy_arbitrary.elf"]);
    let input_path = create_input_segment_file();
    // The program has a ebreak instruction.
    // We can run it for a long enough time instead of the perfect amount.
    KernelRunner::new_with_steps(elf_path, 300)
        .with_input(MemorySegmentDef {
            off: 0x0,
            len: MSG.len() as RegVal,
            is_read: true,
            is_write: false,
            is_execute: false,
            path: input_path,
        })
        .with_output(MemorySegmentDef {
            off: OUTPUT_OFFSET,
            len: MSG.len() as RegVal,
            is_read: false,
            is_write: true,
            is_execute: false,
            path: make_test_mem_path("basic_mount-output"),
        })
        .with_expected_mem(OUTPUT_OFFSET, MSG)
        .run();

    info!("Pass");
}

fn create_input_segment_file() -> PathBuf {
    let out_path = make_test_mem_path("basic_mount-input");
    let mut file = File::create(&out_path).unwrap();
    file.write_all(MSG).unwrap();
    out_path
}
