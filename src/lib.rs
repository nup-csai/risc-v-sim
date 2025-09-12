pub mod kernel;
pub mod shell;

use std::error::Error;
use std::path::PathBuf;
use std::{io::Write, str::FromStr};

use clap::Parser;
use kernel::Kernel;
use shell::{load_program_from_file, ShellError};

use crate::kernel::{Memory, MemorySegment, RegisterVal};

/// Emulates RiscV programs. After each step, the program
/// prints a trace step into standard output. Each trace step
/// is a JSON message located on a single line. A line break
/// means the end of a trace step.
///
/// It is guaranteed that the program will not print anything
/// else to the standard output, so the user may freely pipe
/// the output into a JSON-parsing program.
///
/// All errors will be reported into standard error.
#[derive(Parser, Debug)]
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
    /// the contents of the segment will be written into `FILE``.
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

#[derive(Debug, Clone, Copy)]
pub struct MemorySegmentDef {
    pub offset: RegisterVal,
    pub length: RegisterVal,
    pub is_read: bool,
    pub is_write: bool,
    pub is_execute: bool,
}

fn parse_input_memory_segment(
    s: &str,
) -> Result<(MemorySegmentDef, PathBuf), Box<dyn Error + Send + Sync>> {
    parse_memory_segment(s, true, false, false)
}

fn parse_output_memory_segment(
    s: &str,
) -> Result<(MemorySegmentDef, PathBuf), Box<dyn Error + Send + Sync>> {
    parse_memory_segment(s, false, true, false)
}

fn parse_memory_segment(
    s: &str,
    mut is_read: bool,
    mut is_write: bool,
    mut is_execute: bool,
) -> Result<(MemorySegmentDef, PathBuf), Box<dyn Error + Send + Sync>> {
    use clap::{error::*, Error};

    let eq_pos = s.find('=').ok_or_else(|| Error::new(ErrorKind::NoEquals))?;
    let segment_def_string = &s[..eq_pos];
    let file_path_str = &s[eq_pos + 1..];

    let mut segment_def_pieces = segment_def_string.split(':');
    let segment_offset_string = segment_def_pieces
        .next()
        .ok_or_else(|| format!("not enough `:` in `{segment_def_string}`"))?;
    let segment_length_string = segment_def_pieces
        .next()
        .ok_or_else(|| format!("not enough `:` in `{segment_def_string}`"))?;
    let segment_flags_string = segment_def_pieces.next();
    if segment_def_pieces.next().is_some() {
        return Err(format!("too many `:` in `{segment_def_string}`").into());
    }
    if let Some(segment_flags_string) = segment_flags_string {
        (is_read, is_write, is_execute) = parse_segment_flags(segment_flags_string)?;
    }

    let segment_def = MemorySegmentDef {
        offset: parse_segment_number(segment_offset_string)?,
        length: parse_segment_number(segment_length_string)?,
        is_read,
        is_write,
        is_execute,
    };
    let path = PathBuf::from_str(file_path_str).unwrap();

    Ok((segment_def, path))
}

fn parse_segment_number(s: &str) -> Result<RegisterVal, Box<dyn Error + Send + Sync>> {
    let mut radix = 10;
    let mut to_parse = s;
    if s.starts_with("0x") {
        radix = 16;
        to_parse = &to_parse[2..];
    }

    let res = RegisterVal::from_str_radix(to_parse, radix).map_err(|_| {
        format!("`{s}` must be a valid decimal number or a hexadecimal nummber prefixed with `0x`")
    })?;
    Ok(res)
}

fn parse_segment_flags(s: &str) -> Result<(bool, bool, bool), Box<dyn Error + Send + Sync>> {
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
                .into())
            }
        }
    }

    Ok((is_read, is_write, is_execute))
}

pub fn run(args: Args) -> Result<(), ShellError> {
    let info = load_program_from_file(&args.path)?;
    let entry_point = info.entry;
    let mut memory = Memory::new();

    info.load_into_memory(&mut memory, false, false)
        .map_err(ShellError::LoadingProramIntoMemory)?;

    for (def, file) in &args.input {
        let bytes = std::fs::read(file).map_err(|error| ShellError::LoadingInputSegment {
            file: file.clone(),
            error,
        })?;

        memory
            .add_segment(MemorySegment {
                is_read: def.is_read,
                is_write: def.is_write,
                is_execute: def.is_execute,
                offset: def.offset,
                mem: bytes[0..std::cmp::min(bytes.len(), def.length as usize)].into(),
            })
            .map_err(ShellError::AddingSegmentToMemory)?;
    }

    for (def, _) in &args.output {
        let bytes = vec![0u8; def.length as usize].into_boxed_slice();
        memory
            .add_segment(MemorySegment {
                is_read: def.is_read,
                is_write: def.is_write,
                is_execute: def.is_execute,
                offset: def.offset,
                mem: bytes,
            })
            .map_err(ShellError::AddingSegmentToMemory)?;
    }

    let mut kernel = Kernel::new(memory, entry_point);
    for _ in 0..args.ticks {
        let step = kernel.step().map_err(ShellError::KernelError)?;
        let mut stdout = std::io::stdout().lock();
        serde_json::ser::to_writer(&mut stdout, &step).unwrap();
        stdout.write(std::slice::from_ref(&b'\n')).unwrap();
    }

    for (def, file) in &args.output {
        let segment = kernel
            .memory
            .segments()
            .iter()
            .find(|s| s.contains_address(def.offset))
            .unwrap();
        std::fs::write(file.clone(), segment.as_bytes()).map_err(|error| {
            ShellError::WritingOutputSegment {
                file: file.clone(),
                error,
            }
        })?;
    }

    Ok(())
}
