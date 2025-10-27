//! The shell is a collection of wrapper code on top of
//! the kernel to provide risc-v-sim's interface.

mod kernel_def;

use std::path::PathBuf;

use log::{debug, trace};
use serde::Serialize;
use thiserror::Error;

use crate::kernel::{
    Instruction, InstructionDecodeError, Kernel, KernelError, KernelStep, Memory, MemoryError,
    MemorySegment,
};

pub use kernel_def::*;

#[derive(Debug, Error)]
pub enum ShellError {
    #[error("Failed to load the .elf file: {0}")]
    Load(#[source] std::io::Error),
    #[error("Failed to parse the .elf file: {0}")]
    ElfHead(#[source] elf::ParseError),
    #[error("The .elf file is not little-endian")]
    ElfNotLittleEndian,
    #[error("Failed to parse a section from the .elf file: {0}")]
    ElfSection(#[source] elf::ParseError),
    #[error(".elf file has no sections")]
    NoSections,
    #[error(".elf file has no string table")]
    NoStrtable,
    #[error("The .elf file does not have a .text section")]
    NoText,
    /// This error may happen if the .text section is compressed
    /// and the compression header is malformed.
    #[error("Failed to read section {0:?} data")]
    SectionData(&'static str, #[source] elf::ParseError),
    #[error("Compressed sections is not supported. Section {0:?} is compressed")]
    CompressedSection(&'static str),
    #[error("The .text section is not a multiple of 4")]
    UnalignedText,
    #[error("Failed to decode the .text section: {0}")]
    InstructionDecoderError(#[source] InstructionDecodeError),
    #[error("Failed to load the program into memory: {0}")]
    LoadingProramIntoMemory(#[source] MemoryError),
    #[error("Failed to load segment bytes from {path:?}: {error}")]
    LoadingInputSegment {
        path: PathBuf,
        #[source]
        error: std::io::Error,
    },
    #[error("Failed to add a segment to memory: {0}")]
    AddingSegmentToMemory(#[source] MemoryError),
    #[error("Failed to write segment bytes to {path:?}: {error}")]
    WritingOutputSegment {
        path: PathBuf,
        #[source]
        error: std::io::Error,
    },
    #[error("Kernel error: {0}")]
    KernelError(#[source] KernelError),
}

type Result<T> = std::result::Result<T, ShellError>;

/// Status of a kernel run. Contains a trace with an error
/// if one happened during execution.
#[derive(Debug, Serialize)]
pub struct RunResult {
    pub steps: Vec<KernelStep>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub err: Option<RunError>,
}

#[derive(Debug, Serialize)]
pub struct RunError {
    pub msg: String,
    pub detail: KernelError,
}

/// Runs a kernel for `step_count` steps, returning the result.
///
/// The kernel is constructed from [`KernelDef`]. The kernel
/// is run with [`run_kernel()`]. See that function for more information.
///
/// Segments specified in spec's `outputs` field, wil have their bytes
/// written to files specified by their paths.
pub fn run_from_spec(spec: KernelDef, step_count: usize) -> Result<(Kernel, RunResult)> {
    debug!(target: "rvsim::shell", "Run kernel from spec {spec:?}");

    let mut kernel = spec.build_kernel()?;
    let run_result = run_kernel(&mut kernel, step_count);

    for def in &spec.outputs {
        debug!(target: "rvsim::shell", "writing back output segment for file {:?}", def.path);

        let path = def.path.clone();
        let segment = find_segment_for_def(&kernel.memory, def);
        std::fs::write(&path, segment.as_bytes())
            .map_err(|error| ShellError::WritingOutputSegment { path, error })?;
    }

    Ok((kernel, run_result))
}

fn find_segment_for_def<'a>(memory: &'a Memory, def: &MemorySegmentDef) -> &'a MemorySegment {
    memory
        .segments()
        .iter()
        .find(|s| s.contains_address(def.off))
        .expect("memory segment disappeared")
}

/// Runs the kernel for `step_count` steps, returning the result.
///
/// The execution will terminate early if the kernel executes
/// [`Instruction::Ebreak`].
///
/// The result is a special struct, which serializes into a machine-friendly
/// shaped JSON.
pub fn run_kernel(kernel: &mut Kernel, step_count: usize) -> RunResult {
    debug!(target: "rvsim::shell", "Run kernel for {step_count} steps");

    let mut kern_err = None;
    let mut steps = Vec::new();
    for _ in 0..step_count {
        let step = match kernel.step() {
            Ok(x) => x,
            Err(e) => {
                kern_err = Some(e);
                break;
            }
        };

        steps.push(step);
        if matches!(step.instruction.obj, Instruction::Ebreak) {
            break;
        }
    }
    let err = kern_err.map(kernel_error_to_run_error);

    let res = RunResult { steps, err };
    trace!(target: "rvsim::shell", "result: {res:?}");
    res
}

fn kernel_error_to_run_error(kern_err: KernelError) -> RunError {
    RunError { msg: kern_err.to_string(), detail: kern_err }
}
