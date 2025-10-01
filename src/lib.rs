//! risc-v-sim is a `RiscV` emulator aimed to be used for
//! educational purposes. It provides a RV64i compatible
//! single core `RiscV` processor with a flexible address
//! space. Once risc-v-sim terminates, it outputs the
//! program trace, formatted as a JSON object. The trace
//! also contains an error message, describing what went
//! wrong during the exeuction.
//!
//! risc-v-sim is not intended to be used as a
//! general-purpose `RiscV` emulator. It does not support
//! traps for handling incorrect memory accesses. Incorrect
//! memory accesses cause the execution to halt, giving the
//! user a clear message of what went wrong.
//!
//! Risc-v-sim is capable of reading and running `RiscV`
//! little-endian `.elf` files, which makes it possible
//! to use it with a real compiler targetting `RiscV` in
//! a teaching course.
//!  
//! ## The Address Space
//! risc-v-sim's address is not mapped to anything by default.
//! The user can map address ranges to various **files**.
//!
//! There are two types of segments in RiscV:
//! 1. Input segments -- a file is loaded into memory and placed
//! into the specified address range
//! 2. Output segments -- all data a program writes is written to
//! a specified file once risc-v-sim terminates
//!
//! ## Overview
//! risc-v-sim consists of two main parts:
//! 1. [`kernel`] - main runtime
//! 2. [`shell`] - utility on top of the kernel to load elfs
//!    and configure the input/output segments
//!
//! The kernel itself is a simple implementation of a CPU exeuction
//! step ([`Kernel::step()`]):
//! 1. Fetch ([`kernel::memory`])
//! 2. Decode ([`kernel::decoder`])
//! 3. Execute ([`kernel::instruction`])
//!
//! The shell then drives the kernel by caling the step function.
//!
//! ## Testing
//! Risc-v-sim is tested against QEMU to make sure the behaviour
//! is compatible with a more recognized implementation. For more
//! information, see the `riscv-samples` directory in the repository
//! root.
//!
//! ## Further Reading
//! For a brief reference of the Rv64i architecture, it is recommended
//! consult the RiscV reference card by Berkley: <https://github.com/jameslzhu/riscv-card/releases/download/latest/riscv-card.pdf>.
//!
//! Alternatively, it is recommended to consult with the RiscV manual
//! volume I (Unpriveleged Architecture): <https://riscv.github.io/riscv-isa-manual/snapshot/unprivileged/>.

pub mod kernel;
pub mod shell;
mod util;

use std::error::Error;
use std::io::{Read, stdout};
use std::path::PathBuf;
use std::str::FromStr;

use clap::Parser;
use kernel::Kernel;
use shell::{ShellError, load_program_from_file};

use crate::kernel::{Memory, MemorySegment, RegVal};
use crate::shell::run_kernel;

pub type ErrBox = Box<dyn Error + Send + Sync>;

/// Emulates `RiscV` programs. The result is a JSON object printed
/// into stdout. The JSON object is guaranteed to always be printed
/// to stdout and will have the same shape. The user may freely pipe
/// the output into a JSON-parsing program.
///
/// All errors and logs will also be reported into standard error
/// for debugging purposes.
#[derive(Parser, Debug)]
#[doc(hidden)]
pub struct Args {
    /// Path to the .elf file
    #[arg(short, long)]
    path: PathBuf,
    /// Amount of ticks to do
    #[arg(short, long)]
    ticks: usize,
    /// Mounts `FILE` into program's memory as input. The given file bytes will
    /// be copied into memory and will be available for the program to interact with.
    /// The location of the bytes is specified with `OFFSET` and `LENGTH`.
    ///
    /// If `LENGTH` is larger than FILE's length - the excess is padded with zeroes.
    /// If `LENGTH` is smaller than FILE's length - the bytes will be truncated.
    ///
    /// `FLAGS` is an optional argument that controls the permissions for the
    /// region the file is mounted into:
    /// `r` - allow reads,
    /// `w` - allow writes,
    /// `x` - allow execution.
    ///
    /// The default permissions for inputs is just `r`.
    ///
    /// Even if the input is mounted with write permissions, the changes WILL NOT
    /// be reflected in the source file. You can use this option to give the
    /// program temporary working memory by mounting `/dev/null`.
    #[arg(short, long, value_name = "OFFSET:LENGTH[:FLAGS]=FILE", value_parser=parse_input_memory_segment)]
    input: Vec<(MemorySegmentDef, PathBuf)>,
    /// Mounts `FILE` into program's memory as output. The program will get a
    /// specified segment filled with zeros. At the end of program execution
    /// the contents of the segment will be written into `FILE`.
    ///
    /// `FLAGS` is an optional argument that controls the permissions for the
    /// region the file is mounted into:
    /// `r` - allow reads,
    /// `w` - allow writes,
    /// `x` - allow execution.
    ///
    /// The default permissions for inputs is just `w`.
    #[arg(short, long, value_name = "OFFSET:LENGTH[:FLAGS]=FILE", value_parser=parse_output_memory_segment)]
    output: Vec<(MemorySegmentDef, PathBuf)>,
}

/// Run the CLI according to specified `args`.
///
/// # Errors
///
/// If something goes wrong, [`ShellError`] is returned.
pub fn run_cli(args: &Args) -> Result<(), ShellError> {
    let mut memory = Memory::new();
    let entry_point = load_program_into_memory(&mut memory, &args.path)?;
    load_segments_into_memory(&mut memory, &args.input, &args.output)?;

    let mut kernel = Kernel::new(memory, entry_point);
    run_kernel(&mut kernel, args.ticks, &mut stdout().lock())?;

    for (def, file) in &args.output {
        let segment = find_segment_for_def(&kernel.memory, def);
        std::fs::write(file.clone(), segment.as_bytes())
            .map_err(|error| ShellError::WritingOutputSegment { file: file.clone(), error })?;
    }

    Ok(())
}

#[derive(Debug, Clone, Copy)]
pub struct MemorySegmentDef {
    pub off: RegVal,
    pub len: RegVal,
    pub is_read: bool,
    pub is_write: bool,
    pub is_execute: bool,
}

impl MemorySegmentDef {
    fn to_segment(self, mem: impl Into<Box<[u8]>>) -> MemorySegment {
        let mem = mem.into();
        assert_eq!(mem.len(), self.len as usize);

        MemorySegment {
            is_read: self.is_read,
            is_write: self.is_write,
            is_execute: self.is_execute,
            off: self.off,
            mem,
        }
    }
}

fn load_program_into_memory(memory: &mut Memory, path: &PathBuf) -> Result<RegVal, ShellError> {
    let info = load_program_from_file(path)?;
    info.load_into_memory(memory, false, false)
        .map_err(ShellError::LoadingProramIntoMemory)?;
    Ok(info.entry)
}

fn load_segments_into_memory(
    memory: &mut Memory,
    inputs: &[(MemorySegmentDef, PathBuf)],
    outputs: &[(MemorySegmentDef, PathBuf)],
) -> Result<(), ShellError> {
    for (def, path) in inputs {
        let bytes = read_file(path, def.len)?;
        memory
            .add_segment(def.to_segment(bytes))
            .map_err(ShellError::AddingSegmentToMemory)?;
    }

    for (def, _) in outputs {
        let bytes = vec![0u8; def.len as usize].into_boxed_slice();
        memory
            .add_segment(def.to_segment(bytes))
            .map_err(ShellError::AddingSegmentToMemory)?;
    }

    Ok(())
}

fn read_file(path: &PathBuf, amount: u64) -> Result<Vec<u8>, ShellError> {
    let make_err =
        |error: std::io::Error| ShellError::LoadingInputSegment { path: path.clone(), error };

    let mut bytes = Vec::with_capacity(amount as usize);
    let file = std::fs::File::open(path).map_err(make_err)?;
    file.take(amount)
        .read_to_end(&mut bytes)
        .map_err(make_err)?;
    Ok(bytes)
}

fn find_segment_for_def<'a>(memory: &'a Memory, def: &MemorySegmentDef) -> &'a MemorySegment {
    memory
        .segments()
        .iter()
        .find(|s| s.contains_address(def.off))
        .expect("memory segment disappeared")
}

fn parse_input_memory_segment(s: &str) -> Result<(MemorySegmentDef, PathBuf), ErrBox> {
    parse_memory_segment(s, true)
}

fn parse_output_memory_segment(s: &str) -> Result<(MemorySegmentDef, PathBuf), ErrBox> {
    parse_memory_segment(s, false)
}

fn parse_memory_segment(s: &str, is_input: bool) -> Result<(MemorySegmentDef, PathBuf), ErrBox> {
    use clap::{Error, error::*};

    let eq_pos = s.find('=').ok_or_else(|| Error::new(ErrorKind::NoEquals))?;
    let segment_def_string = &s[..eq_pos];
    let file_path_str = &s[eq_pos + 1..];

    let segment_def = parse_segment_def(segment_def_string, is_input)?;
    Ok((segment_def, PathBuf::from_str(file_path_str).unwrap()))
}

fn parse_segment_def(s: &str, is_input: bool) -> Result<MemorySegmentDef, ErrBox> {
    let pieces = s.split(':').collect::<Vec<&str>>();
    if pieces.len() < 2 {
        return Err(format!("not enough `:` in `{s}`").into());
    }
    if pieces.len() > 3 {
        return Err(format!("too many `:` in `{s}`").into());
    }

    let (is_read, is_write, is_execute) = match pieces.get(2) {
        Some(s) => parse_segment_flags(s)?,
        None if is_input => (true, false, false),
        None => (false, true, false),
    };

    Ok(MemorySegmentDef {
        off: parse_int_hex_or_dec(pieces[0])?,
        len: parse_int_hex_or_dec(pieces[1])?,
        is_read,
        is_write,
        is_execute,
    })
}

fn parse_segment_flags(s: &str) -> Result<(bool, bool, bool), ErrBox> {
    let mut is_read = false;
    let mut is_write = false;
    let mut is_execute = false;

    for ch in s.chars() {
        match ch {
            'r' => is_read = true,
            'w' => is_write = true,
            'x' => is_execute = true,
            _ => {
                return Err(format!(
                    "`{ch}` is not a valid permission flag. Available flags are: r, w and x"
                )
                .into());
            }
        }
    }

    Ok((is_read, is_write, is_execute))
}

fn parse_int_hex_or_dec(s: &str) -> Result<RegVal, ErrBox> {
    let mut radix = 10;
    let mut to_parse = s;
    // Trim off `0x`. Rust number parser doesn't like it.
    if s.starts_with("0x") {
        radix = 16;
        to_parse = &to_parse[2..];
    }

    let res = RegVal::from_str_radix(to_parse, radix).map_err(|_| {
        format!("`{s}` must be a valid decimal number or a hexadecimal nummber prefixed with `0x`")
    })?;
    Ok(res)
}
