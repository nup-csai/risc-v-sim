//! Uses the write_and_fail.elf artifact from QEMU trace capturer.
//! Please make sure you have captured the QEMU traces first.
//! For more information, see the README in `riscv-samples`.

mod common;
use common::*;

use std::path::{Path, PathBuf};

use log::info;
use risc_v_sim::kernel::{KernelError, MemoryError, RegVal};
use risc_v_sim::shell::MemorySegmentDef;

static MSG: &[u8] = b"HI";

/// write_segments_on_err test check that risc-v-sim writes to output
/// segments even if an error happens. This is important for debugging.
#[test]
fn write_segments_on_err() {
    init_test();

    let elf_path = PathBuf::from_iter(["riscv-samples", "bin", "write_and_fail.elf"]);
    let output_path = make_test_mem_path("write_segments_on_err-output");
    let err = KernelRunner::new_with_steps(elf_path, 300)
        .with_output(MemorySegmentDef {
            off: 0,
            len: MSG.len() as RegVal,
            is_read: false,
            is_write: true,
            is_execute: false,
            path: output_path.clone(),
        })
        .with_expected_mem(0, MSG)
        .run_failing();
    let expected_error = KernelError::FetchError {
        instruction_address: 0xAD,
        memory_error: MemoryError::AddressOutOfRange { address: 0xAD },
    };
    assert_eq!(err, expected_error, "Kernel failed with unexpected error");
    check_output_segment_file(&output_path);

    info!("Pass");
}

fn check_output_segment_file(path: &Path) {
    info!("Checking that the memory still has been dumped to {path:?}");
    let data = std::fs::read(path).expect("Output segment file must exist and be openeable");
    assert_eq!(data, MSG);
}
