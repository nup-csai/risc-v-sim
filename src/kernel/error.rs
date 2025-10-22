//! Errors returned by the kernel.

use serde::Serialize;
use thiserror::Error;

use crate::kernel::{InstrVal, InstructionInfo, RegVal};

#[derive(Clone, Copy, PartialEq, Eq, Debug, Error)]
#[error(
    "Failed to encode instruction {instruction_idx}: {instruction_code:#x} is not a valid instruction"
)]
pub struct InstructionDecodeError {
    pub instruction_idx: usize,
    pub instruction_code: InstrVal,
    #[source]
    pub error: DecodeError,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Error, Serialize)]
pub enum KernelError {
    #[error(
        "Failed to execute instruction at {instruction_address:#x}: instruction: {instruction}: {instruction_error}"
    )]
    InstructionError {
        instruction_address: RegVal,
        instruction: InstructionInfo,
        #[source]
        instruction_error: InstructionError,
    },
    #[error("Failed to fetch instruction at {instruction_address:#x}: {memory_error}")]
    FetchError {
        instruction_address: RegVal,
        #[source]
        memory_error: MemoryError,
    },
    #[error(
        "Failed to decode instruction at {instruction_address:#x} with code {instruction_code:#x}: {decode_error}"
    )]
    DecodeError {
        instruction_address: RegVal,
        instruction_code: InstrVal,
        #[source]
        decode_error: DecodeError,
    },
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Error, Serialize)]
pub enum DecodeError {
    #[error("Unknown instruction opcode: {0:#x}")]
    UnknownOpcode(InstrVal),
    #[error("Unknown op funct3 and funct7 values: {funct3:#x} and {funct7:#x}")]
    UnknownOp { funct3: InstrVal, funct7: InstrVal },
    #[error("Unknown imm-op funct3 value: {funct3:#x}")]
    UnknownImmOp { funct3: InstrVal },
    #[error("Unknown load op funct3 value: {funct3:#x}")]
    UnknownLoadOp { funct3: InstrVal },
    #[error("Unknown env-op funct3 and imm values: {funct3:#x} and {imm:#x}")]
    UnknownEnvOp { funct3: InstrVal, imm: InstrVal },
    #[error("Unknown store op funct3 value: {funct3:#x}")]
    UnknownStoreOp { funct3: InstrVal },
    #[error("Unknown bitwise shift type: {shtyp:#x}")]
    UnknownImmOpShtyp { shtyp: InstrVal },
    #[error("Unknown branch funct3 value: {funct3:#x}")]
    UnknownBranch { funct3: InstrVal },
}

#[derive(Clone, Copy, PartialEq, Eq, Error, Debug, Serialize)]
pub enum InstructionError {
    #[error("memory error: {0}")]
    MemoryError(#[source] MemoryError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error, Serialize)]
pub enum MemoryError {
    #[error("Address {address:#x} is not mapped")]
    AddressOutOfRange { address: RegVal },
    #[error("Address {address:#x}: segment doesn't allow reads")]
    AddressNotReadable { address: RegVal },
    #[error("Address {address:#x}: segment doesn't allow writes")]
    AddressNotWritable { address: RegVal },
    #[error("Address {address:#x}: segment doesn't allow execution")]
    AddressNotExecutable { address: RegVal },
    #[error("Address {address:#x} is not {expected_alignment}-aligned")]
    MisalignedAccess { address: RegVal, expected_alignment: usize },
    #[error("Segment {off:#x}:{len:#x} overlaps existing: {found_off:#x}:{found_len:#x}")]
    SegmentOverlap { found_off: RegVal, found_len: RegVal, off: RegVal, len: RegVal },
}
