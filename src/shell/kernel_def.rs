use super::{Result, ShellError};
use crate::kernel::{InstrVal, Kernel, MemorySegment, Program, RegVal};

use elf::ElfBytes;
use elf::endian::AnyEndian;
use log::{debug, info, trace};

use std::{
    io::Read,
    path::{Path, PathBuf},
};

static SECTION_TEXT: &str = ".text";

/// Specification for constructing and running a kernel.
///
/// The specification should be passed to [`crate::shell::run_from_spec()`],
/// however you may also use it to build a kernel.
#[derive(Debug)]
pub struct KernelDef {
    /// The .elf file path to use
    pub elfpath: PathBuf,
    /// The input segments.
    pub inputs: Vec<MemorySegmentDef>,
    /// The output segments.
    pub outputs: Vec<MemorySegmentDef>,
}

impl KernelDef {
    /// Construct a kernel according to the def.
    ///
    /// * Segments declared in `inputs` will be construced from bytes
    ///   specified stored files specified by their `path` field. Extra
    ///   space will be zero-padded.
    /// * Segments declared in `outputs` will be constructed from zeroes
    pub fn build_kernel(&self) -> Result<Kernel> {
        let program = load_program_from_file(&self.elfpath)?;
        let mut kernel = Kernel::from_program(&program);

        for def in &self.inputs {
            debug!(target: "rvsim::shell", "Input segment from {:?}", def.path);
            let bytes = Self::read_file(&def.path, def.len)?;
            kernel
                .memory
                .add_segment(def.to_segment(bytes))
                .map_err(ShellError::AddingSegmentToMemory)?;
        }

        for def in &self.outputs {
            debug!(target: "rvsim::shell", "Output segment from {:?}", def.path);
            let bytes = vec![0u8; def.len as usize].into_boxed_slice();
            kernel
                .memory
                .add_segment(def.to_segment(bytes))
                .map_err(ShellError::AddingSegmentToMemory)?;
        }

        Ok(kernel)
    }

    fn read_file(path: &PathBuf, amount: u64) -> Result<Vec<u8>> {
        trace!(target: "rvsim::shell", "Reading at most {amount:#x} bytes from {path:?}");

        let make_err =
            |error: std::io::Error| ShellError::LoadingInputSegment { path: path.clone(), error };

        let mut bytes = Vec::with_capacity(amount as usize);
        let file = std::fs::File::open(path).map_err(make_err)?;
        file.take(amount)
            .read_to_end(&mut bytes)
            .map_err(make_err)?;
        Ok(bytes)
    }
}

/// Specification for constructing a memory segment.
#[derive(Debug, Clone)]
pub struct MemorySegmentDef {
    pub off: RegVal,
    pub len: RegVal,
    pub is_read: bool,
    pub is_write: bool,
    pub is_execute: bool,
    pub path: PathBuf,
}

impl MemorySegmentDef {
    /// Construct a segment according to def.
    pub fn to_segment(&self, mem: impl Into<Box<[u8]>>) -> MemorySegment {
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

/// Reads a program from an `.elf` file.
///
/// The elf file must satisfy the following constraints:
/// * The elf file must be for a little-endian architecture
/// * The elf file must have .text section
/// * The .text section offset must be aligned to 4 bytes
/// * The .text section is not compressed
/// * The .text section must contain supported `RiscV` instructions
///
/// # Errors
///
/// 1. Returns [`ShellError::Load`] if an IO error happens during program load.
/// 2. Returns an error if `data` doesn't contain valid elf file bytes
///    or the elf file doesn't satisfy the constraints
pub fn load_program_from_file(path: impl AsRef<Path>) -> Result<Program> {
    debug!(target: "rvsim::shell", "Loading a program from {:?}", path.as_ref());

    let elf_bytes = std::fs::read(path).map_err(ShellError::Load)?;
    let file = ElfBytes::<AnyEndian>::minimal_parse(&elf_bytes).map_err(ShellError::ElfHead)?;

    if file.ehdr.endianness != AnyEndian::Little {
        return Err(ShellError::ElfNotLittleEndian);
    }

    let (raw_stream, load_offset, entry_point) = read_program_text(&file)?;
    info!(target: "rvsim::shell", "load_offset={load_offset:#x}, entry_point={entry_point:#x}", );
    Program::from_raw_instructions(raw_stream, load_offset, entry_point)
        .map_err(ShellError::InstructionDecoderError)
}

fn read_program_text(
    file: &ElfBytes<AnyEndian>,
) -> Result<(impl Iterator<Item = InstrVal>, RegVal, RegVal)> {
    let text_header = file
        .section_header_by_name(SECTION_TEXT)
        .map_err(ShellError::ElfSection)?
        .ok_or(ShellError::NoText)?;
    let (text, compression_header) = file
        .section_data(&text_header)
        .map_err(ShellError::TextData)?;
    if compression_header.is_some() {
        return Err(ShellError::CompressedText);
    }

    let (chunks, tail) = text.as_chunks::<4>();
    if !tail.is_empty() {
        return Err(ShellError::UnalignedText);
    }

    let raw_stream = chunks.iter().copied().map(InstrVal::from_le_bytes);
    Ok((raw_stream, text_header.sh_addr, file.ehdr.e_entry))
}
