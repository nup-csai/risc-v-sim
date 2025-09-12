use thiserror::Error;

use crate::kernel::{InstructionVal, RegisterVal};

/// The heart of the memory system. All memory requests
/// should be done through it. A memory system consists of
/// N **noverlapping** segments. The no-overlap part is important
/// as it allows an unambigious mapping of addresses to segments.
/// Segments are just chunks of plain bytes with permission control.
/// For more information, see [MemorySegment].
#[derive(Debug)]
pub struct Memory {
    segments: Vec<MemorySegment>,
}

impl Memory {
    pub fn new() -> Self {
        Self {
            segments: Vec::new(),
        }
    }

    /// Adds a segment ot the memory. If the segment turns out to be overlapping,
    /// [MemoryError::AddingOverlappingSegment] is returned.
    pub fn add_segment(&mut self, added_segment: MemorySegment) -> Result<(), MemoryError> {
        let conflicting_segment = self
            .segments
            .iter()
            .find(|x| x.overlaps_segment(added_segment.offset, added_segment.len()));
        if let Some(conflicting_segment) = conflicting_segment {
            return Err(MemoryError::AddingOverlappingSegment {
                existing_segment_offset: conflicting_segment.offset,
                existing_segment_len: conflicting_segment.len(),
                added_segment_offset: added_segment.offset,
                added_segment_len: added_segment.len(),
            });
        }

        self.segments.push(added_segment);
        Ok(())
    }

    /// Issue a read request to the memory. The result of the read is written into `dst`.
    /// The alignment of that operation is equal to `dst` length.
    ///
    /// # Errors
    ///
    /// The following scenarios will read to memory errors:
    /// * `address` not belonging to any segment
    /// * the segment responsible for `address` does not allow reads
    /// * alignment enforcement is enabled and `address` is not properly aligned
    pub fn read(&self, address: RegisterVal, dst: &mut [u8]) -> Result<(), MemoryError> {
        let Some(matching_segment) = self.segments.iter().find(|x| x.contains_address(address))
        else {
            return Err(MemoryError::AddressOutOfRange { address });
        };

        if !matching_segment.is_read {
            return Err(MemoryError::AddressNotReadable { address });
        }

        if address as usize % dst.len() != 0 {
            return Err(MemoryError::MisalignedAccess {
                address,
                expected_alignment: dst.len(),
            });
        }

        let (local_start, local_end) =
            Self::translate_address(address, dst.len(), matching_segment);
        let src = &matching_segment.as_bytes()[local_start..local_end];
        dst.copy_from_slice(src);

        Ok(())
    }

    /// Issue a wirtte request to the memory. The contents of `src` will be
    /// written to the appropriate memory segment.
    ///
    /// # Errors
    ///
    /// The following scenarios will read to memory errors:
    /// * `address` not belonging to any segment
    /// * the segment responsible for `address` does not allow writes
    /// * alignment enforcement is enabled and `address` is not properly aligned
    pub fn write(&mut self, address: RegisterVal, src: &[u8]) -> Result<(), MemoryError> {
        let Some(matching_segment) = self
            .segments
            .iter_mut()
            .find(|x| x.contains_address(address))
        else {
            return Err(MemoryError::AddressOutOfRange { address });
        };

        if !matching_segment.is_write {
            return Err(MemoryError::AddressNotWritable { address });
        }

        if address as usize % src.len() != 0 {
            return Err(MemoryError::MisalignedAccess {
                address,
                expected_alignment: src.len(),
            });
        }

        let (local_start, local_end) =
            Self::translate_address(address, src.len(), matching_segment);
        let dst = &mut matching_segment.as_mut_bytes()[local_start..local_end];
        dst.copy_from_slice(src);

        Ok(())
    }

    /// Issue an instruction fetch request to the memory. The result of the fetch is returned.
    /// The alignment of that operation is equal 4.
    ///
    /// # Errors
    ///
    /// The following scenarios will read to memory errors:
    /// * `address` not belonging to any segment
    /// * the segment responsible for `address` does not allow execution
    /// * alignment enforcement is enabled and `address` is not properly aligned
    pub fn fetch_instruction(&self, address: RegisterVal) -> Result<InstructionVal, MemoryError> {
        let Some(matching_segment) = self.segments.iter().find(|x| x.contains_address(address))
        else {
            return Err(MemoryError::AddressOutOfRange { address });
        };

        if !matching_segment.is_execute {
            return Err(MemoryError::AddressNotExecutable { address });
        }

        if address % 4 != 0 {
            return Err(MemoryError::MisalignedAccess {
                address,
                expected_alignment: 4,
            });
        }

        let mut dst = [0u8; 4];
        let (local_start, local_end) =
            Self::translate_address(address, dst.len(), matching_segment);
        let src = &matching_segment.as_bytes()[local_start..local_end];
        dst.copy_from_slice(src);

        Ok(InstructionVal::from_le_bytes(dst))
    }

    fn translate_address(
        address: RegisterVal,
        len: usize,
        matching_segment: &MemorySegment,
    ) -> (usize, usize) {
        let local_start = (address - matching_segment.offset) as usize;
        let local_end = local_start + len;

        (local_start, local_end)
    }

    /// Get all memory segments. You can't get a mutable access
    /// to the segments as that would violate the structure's gurantees.
    /// If you need modify segment's data or permissions, please see the
    /// following methods:
    /// * [Memory::segment_data_mut]
    /// * [Memory::set_segment_read]
    /// * [Memory::set_segment_write]
    /// * [Memory::set_segment_execute]
    pub fn segments(&self) -> &[MemorySegment] {
        &self.segments
    }

    /// Get a mutable reference to segment's data, specified by `idx`.
    pub fn segment_data_mut(&mut self, idx: usize) -> &mut [u8] {
        self.segments[idx].as_mut_bytes()
    }

    /// Set `is_read` flag for segment specified by `idx`.
    pub fn set_segment_read(&mut self, idx: usize, is_read: bool) {
        self.segments[idx].is_read = is_read
    }

    /// Set `is_write` flag for segment specified by `idx`.
    pub fn set_segment_write(&mut self, idx: usize, is_write: bool) {
        self.segments[idx].is_write = is_write
    }

    /// Set `is_execute` flag for segment specified by `idx`.
    pub fn set_segment_execute(&mut self, idx: usize, is_execute: bool) {
        self.segments[idx].is_execute = is_execute
    }
}

/// The memory segment structure. A memory segment consists of:
/// * global offset in the memory
/// * constant-size data buffer
/// * permission flags
///
/// The permission flags act similarly to RiscV's permission flags from
/// PMP (Physical Memory Protection). Do note however that this is not
/// an implementation of PMP as they can only be set by the kernel.
#[derive(Debug, Clone)]
pub struct MemorySegment {
    /// Flag for allowing read operations from the segment.
    pub is_read: bool,
    /// Flag for allowing write operations to the segment.
    pub is_write: bool,
    /// Flag for allowing instruction fetches from the segment.
    /// Note, that like in RiscV's PMP, you do not need read access
    /// to execute instructions from the segment.
    pub is_execute: bool,
    /// Segment's global offset within the memory.
    pub offset: RegisterVal,
    /// Segment's buffer.
    pub mem: Box<[u8]>,
}

impl MemorySegment {
    /// Create a segment with specified offset, size and permissions
    /// with all of its bytes zeroed.
    pub fn new_zeroed(
        is_read: bool,
        is_write: bool,
        is_execute: bool,
        offset: RegisterVal,
        len: RegisterVal,
    ) -> Self {
        Self {
            is_read,
            is_write,
            is_execute,
            offset,
            mem: vec![0; len as usize].into_boxed_slice(),
        }
    }

    pub fn len(&self) -> RegisterVal {
        self.as_bytes().len() as RegisterVal
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.mem
    }

    pub fn as_mut_bytes(&mut self) -> &mut [u8] {
        &mut self.mem
    }

    /// Checks if the segment contains `address`.
    pub fn contains_address(&self, address: RegisterVal) -> bool {
        match address.checked_sub(self.offset) {
            Some(local_offset) => local_offset < self.mem.len() as RegisterVal,
            None => false,
        }
    }

    /// Checks if the segment overlaps an other segment specified by its offset
    /// and length.
    pub fn overlaps_segment(&self, other_offset: RegisterVal, other_len: RegisterVal) -> bool {
        if other_offset < self.offset {
            other_offset + other_len > self.offset
        } else {
            self.offset + self.len() > other_offset
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum MemoryError {
    #[error("Address {address:#x} is not mapped")]
    AddressOutOfRange { address: RegisterVal },
    #[error("Address {address:#x} does not have read permissions")]
    AddressNotReadable { address: RegisterVal },
    #[error("Address {address:#x} does not have write permissions")]
    AddressNotWritable { address: RegisterVal },
    #[error("Address {address:#x} does not have execute permissions")]
    AddressNotExecutable { address: RegisterVal },
    #[error("Expected {address:#x} to {expected_alignment}-aligned")]
    MisalignedAccess {
        address: RegisterVal,
        expected_alignment: usize,
    },
    #[error("Added segment {added_segment_offset:#x}:{added_segment_len:#x}) already overlaps with previously added one {existing_segment_offset:#x}:{existing_segment_len:#x}")]
    AddingOverlappingSegment {
        existing_segment_offset: RegisterVal,
        existing_segment_len: RegisterVal,
        added_segment_offset: RegisterVal,
        added_segment_len: RegisterVal,
    },
}

#[cfg(test)]
mod tests {
    use rand::{random, random_range};

    use crate::kernel::{
        memory::{Memory, MemorySegment},
        RegisterVal,
    };

    const SEGMENT_SAMPLING_COUNT: usize = 1_000;
    const ADDRESS_SAMPLING_COUNT: usize = 100;

    #[test]
    fn test_empty_segment_contains() {
        for _ in 0..SEGMENT_SAMPLING_COUNT {
            let segment = MemorySegment::new_zeroed(true, true, true, random(), 0);

            for _ in 0..ADDRESS_SAMPLING_COUNT {
                let address = random();
                assert!(
                    !segment.contains_address(address),
                    "Empty segment at {} shouldn't contain {address}",
                    segment.offset
                );
            }
        }
    }

    #[test]
    fn test_segment_contains() {
        for _ in 0..SEGMENT_SAMPLING_COUNT {
            let offset = random_range(0..0x0800_0000);
            let len = random_range(1..0x0800_0000);

            let segment = MemorySegment::new_zeroed(true, true, true, offset, len);

            assert!(
                segment.contains_address(offset),
                "segment {offset}:{len} must contain {offset}"
            );
            assert!(
                segment.contains_address(offset + len - 1),
                "segment {offset}:{len} must contain {}",
                offset + len - 1
            );

            for _ in 0..ADDRESS_SAMPLING_COUNT {
                let address = random_range(offset..offset + len);
                assert!(
                    segment.contains_address(address),
                    "segment {offset}:{len} must contain {address}"
                );
            }

            for _ in 0..ADDRESS_SAMPLING_COUNT {
                let address = random_range(0..offset);
                assert!(
                    !segment.contains_address(address),
                    "segment {offset}:{len} must not contain {address}"
                );
            }

            for _ in 0..ADDRESS_SAMPLING_COUNT {
                let address = random_range(offset + len..=RegisterVal::MAX);
                assert!(
                    !segment.contains_address(address),
                    "segment {offset}:{len} must not contain {address}"
                );
            }
        }
    }

    #[test]
    fn test_segment_overlaps_positive() {
        for _ in 0..SEGMENT_SAMPLING_COUNT {
            for _ in 0..ADDRESS_SAMPLING_COUNT {
                let offset1 = random_range(0..0x0800_0000);
                let len1 = random_range(1..0x0800_0000);
                let segment1 = MemorySegment::new_zeroed(false, false, false, offset1, len1);

                let offset2 = offset1 + random_range(0..len1 - 1);
                let len2 = random_range(1..0x0800_0000);

                assert!(
                    segment1.overlaps_segment(offset2, len2),
                    "segment {offset1}:{len1} must overlap {offset2}:{len2}"
                )
            }

            for _ in 0..ADDRESS_SAMPLING_COUNT {
                let offset1 = random_range(0..0x0800_0000);
                let len1 = random_range(1..0x0800_0000);
                let segment1 = MemorySegment::new_zeroed(false, false, false, offset1, len1);

                let end2 = offset1 + random_range(1..len1 - 1);
                let offset2 = random_range(0..end2);
                let len2 = end2 - offset2;

                assert!(
                    segment1.overlaps_segment(offset2, len2),
                    "segment {offset1}:{len1} must overlap {offset2}:{len2}"
                )
            }
        }
    }

    #[test]
    fn test_segment_overlaps_negative() {
        for _ in 0..SEGMENT_SAMPLING_COUNT {
            for _ in 0..ADDRESS_SAMPLING_COUNT {
                let offset1 = random_range(0..0x0800_0000);
                let len1 = random_range(1..0x0800_0000);
                let segment1 = MemorySegment::new_zeroed(false, false, false, offset1, len1);

                let offset2 = offset1 + len1 + random_range(0..0x0800_0000);
                let len2 = random_range(1..0x0800_0000);

                assert!(
                    !segment1.overlaps_segment(offset2, len2),
                    "segment {offset1}:{len1} must not overlap {offset2}:{len2}"
                )
            }

            for _ in 0..ADDRESS_SAMPLING_COUNT {
                let offset1 = random_range(0..0x0800_0000);
                let len1 = random_range(1..0x0800_0000);
                let segment1 = MemorySegment::new_zeroed(false, false, false, offset1, len1);

                let end2 = random_range(0..offset1);
                let offset2 = random_range(0..end2);
                let len2 = end2 - offset2;

                assert!(
                    !segment1.overlaps_segment(offset2, len2),
                    "segment {offset1}:{len1} must not overlap {offset2}:{len2}"
                )
            }
        }
    }

    #[test]
    fn test_executable_segment() {
        let sample_instructions = [
            // jal x0, 324
            0b00010100010000000000_00000_1101111,
            // add x4, x6, x1
            0b0000000_00001_00110_000_00100_0110011,
            //auipc x12, 4887
            0b00000001001100010111_01100_0010111,
        ];
        let segment_mem = sample_instructions
            .into_iter()
            .flat_map(u32::to_le_bytes)
            .collect();
        let mut mem = Memory::new();
        mem.add_segment(MemorySegment {
            is_read: false,
            is_write: false,
            is_execute: true,
            offset: 0,
            mem: segment_mem,
        })
        .unwrap();

        for (idx, target) in sample_instructions.into_iter().enumerate() {
            let address = idx as RegisterVal * 4;
            let instr = mem.fetch_instruction(address).unwrap();

            assert_eq!(target, instr);
        }
    }
}
