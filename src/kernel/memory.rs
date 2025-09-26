use thiserror::Error;

use crate::kernel::{InstrVal, RegVal};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum MemoryError {
    #[error("Address {address:#x} is not mapped")]
    AddressOutOfRange { address: RegVal },
    #[error("Address {address:#x} does not have read permissions")]
    AddressNotReadable { address: RegVal },
    #[error("Address {address:#x} does not have write permissions")]
    AddressNotWritable { address: RegVal },
    #[error("Address {address:#x} does not have execute permissions")]
    AddressNotExecutable { address: RegVal },
    #[error("Expected {address:#x} to {expected_alignment}-aligned")]
    MisalignedAccess { address: RegVal, expected_alignment: usize },
    #[error("Segment {off:#x}:{len:#x}) overlaps existing: {found_off:#x}:{found_len:#x}")]
    SegmentOverlap { found_off: RegVal, found_len: RegVal, off: RegVal, len: RegVal },
}

type Result<T> = std::result::Result<T, MemoryError>;

/// The heart of the memory system. All memory requests
/// should be done through it. A memory system consists of
/// N **noverlapping** segments. The no-overlap part is important
/// as it allows an unambigious mapping of addresses to segments.
/// Segments are just chunks of plain bytes with permission control.
/// For more information, see [`MemorySegment`].
#[derive(Debug)]
pub struct Memory {
    segments: Vec<MemorySegment>,
}

impl Memory {
    #[must_use]
    pub fn new() -> Self {
        Self { segments: Vec::new() }
    }

    /// Adds a segment ot the memory.
    ///
    /// # Errors
    ///
    /// If the segment turns out to be overlapping,
    /// [`MemoryError::SegmentOverlap`] is returned.
    pub fn add_segment(&mut self, added_segment: MemorySegment) -> Result<()> {
        let conflicting_segment = self
            .segments
            .iter()
            .find(|x| x.overlaps_segment(added_segment.off, added_segment.len()));
        if let Some(conflicting_segment) = conflicting_segment {
            return Err(MemoryError::SegmentOverlap {
                found_off: conflicting_segment.off,
                found_len: conflicting_segment.len(),
                off: added_segment.off,
                len: added_segment.len(),
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
    pub fn load(&self, address: RegVal, dst: &mut [u8]) -> Result<()> {
        let segment = self.find_segment(address)?;
        if !segment.is_read {
            return Err(MemoryError::AddressNotReadable { address });
        }
        Self::alignment_check(address, dst.len())?;

        let (seg_start, seg_end) = to_segment_offs(address, dst.len(), segment);
        let src = &segment.as_bytes()[seg_start..seg_end];
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
    pub fn fetch_instruction(&self, address: RegVal) -> Result<InstrVal> {
        let segment = self.find_segment(address)?;
        if !segment.is_execute {
            return Err(MemoryError::AddressNotExecutable { address });
        }
        Self::alignment_check(address, 4)?;

        let mut dst = [0u8; 4];
        let (seg_start, seg_end) = to_segment_offs(address, dst.len(), segment);
        let src = &segment.as_bytes()[seg_start..seg_end];
        dst.copy_from_slice(src);

        Ok(InstrVal::from_le_bytes(dst))
    }

    /// Finds a segment that contains `address`.
    ///
    /// # Errors
    ///
    /// Returns [`MemoryError::AddressOutOfRange`] if there is no segment
    /// containing `adress`.
    pub fn find_segment(&self, address: RegVal) -> Result<&MemorySegment> {
        self.segments
            .iter()
            .find(|x| x.contains_address(address))
            .ok_or(MemoryError::AddressOutOfRange { address })
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
    pub fn store(&mut self, address: RegVal, src: &[u8]) -> Result<()> {
        let segment = self.find_segment_mut(address)?;
        if !segment.is_write {
            return Err(MemoryError::AddressNotWritable { address });
        }
        Self::alignment_check(address, src.len())?;

        let (seg_start, seg_end) = to_segment_offs(address, src.len(), segment);
        let dst = &mut segment.as_mut_bytes()[seg_start..seg_end];
        dst.copy_from_slice(src);

        Ok(())
    }

    fn find_segment_mut(&mut self, address: RegVal) -> Result<&mut MemorySegment> {
        self.segments
            .iter_mut()
            .find(|x| x.contains_address(address))
            .ok_or(MemoryError::AddressOutOfRange { address })
    }

    /// Get all memory segments. You can't get a mutable access
    /// to the segments as that would violate the structure's gurantees.
    /// If you need modify segment's data or permissions, please see the
    /// following methods:
    /// * [`Memory::segment_data_mut`]
    /// * [`Memory::set_segment_read`]
    /// * [`Memory::set_segment_write`]
    /// * [`Memory::set_segment_execute`]
    pub fn segments(&self) -> &[MemorySegment] {
        &self.segments
    }

    /// Get a mutable reference to segment's data, specified by `idx`.
    pub fn segment_data_mut(&mut self, idx: usize) -> &mut [u8] {
        self.segments[idx].as_mut_bytes()
    }

    /// Set `is_read` flag for segment specified by `idx`.
    pub fn set_segment_read(&mut self, idx: usize, is_read: bool) {
        self.segments[idx].is_read = is_read;
    }

    /// Set `is_write` flag for segment specified by `idx`.
    pub fn set_segment_write(&mut self, idx: usize, is_write: bool) {
        self.segments[idx].is_write = is_write;
    }

    /// Set `is_execute` flag for segment specified by `idx`.
    pub fn set_segment_execute(&mut self, idx: usize, is_execute: bool) {
        self.segments[idx].is_execute = is_execute;
    }

    fn alignment_check(address: RegVal, expected_alignment: usize) -> Result<()> {
        if address as usize % expected_alignment == 0 {
            return Ok(());
        }
        Err(MemoryError::MisalignedAccess { address, expected_alignment })
    }
}

impl Default for Memory {
    fn default() -> Self {
        Self::new()
    }
}

/// Convert a pair of offsets desribing a byte range into
/// offsets local to a segment. The function does not do
/// any validation, so you will have to make sure that
/// the global offsets properly fit into the segment.
fn to_segment_offs(address: RegVal, len: usize, segment: &MemorySegment) -> (usize, usize) {
    let local_start = (address - segment.off) as usize;
    let local_end = local_start + len;

    (local_start, local_end)
}

/// The memory segment structure. A memory segment consists of:
/// * global offset in the memory
/// * constant-size data buffer
/// * permission flags
///
/// The permission flags act similarly to `RiscV`'s permission flags from
/// PMP (Physical Memory Protection). Do note however that this is not
/// an implementation of PMP as they can only be set by the kernel.
#[derive(Debug, Clone)]
pub struct MemorySegment {
    /// Flag for allowing read operations from the segment.
    pub is_read: bool,
    /// Flag for allowing write operations to the segment.
    pub is_write: bool,
    /// Flag for allowing instruction fetches from the segment.
    /// Note, that like in `RiscV`'s PMP, you do not need read access
    /// to execute instructions from the segment.
    pub is_execute: bool,
    /// Segment's global offset within the memory.
    pub off: RegVal,
    /// Segment's buffer.
    pub mem: Box<[u8]>,
}

impl MemorySegment {
    /// Create a segment with specified offset, size and permissions
    /// with all of its bytes zeroed.
    #[must_use]
    pub fn new_zeroed(
        is_read: bool,
        is_write: bool,
        is_execute: bool,
        off: RegVal,
        len: RegVal,
    ) -> Self {
        let mem = vec![0; len as usize].into_boxed_slice();
        Self { is_read, is_write, is_execute, off, mem }
    }

    // MemorySegment is not a container it is okay to not
    // have an `is_empty`.
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> RegVal {
        self.as_bytes().len() as RegVal
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.mem
    }

    pub fn as_mut_bytes(&mut self) -> &mut [u8] {
        &mut self.mem
    }

    /// Checks if the segment contains `address`.
    pub fn contains_address(&self, address: RegVal) -> bool {
        match address.checked_sub(self.off) {
            Some(local_off) => local_off < self.mem.len() as RegVal,
            None => false,
        }
    }

    /// Checks if the segment overlaps an other segment specified by its offset
    /// and length.
    pub fn overlaps_segment(&self, other_off: RegVal, other_len: RegVal) -> bool {
        if other_off < self.off {
            other_off + other_len > self.off
        } else {
            self.off + self.len() > other_off
        }
    }
}

#[cfg(test)]
mod tests {
    use rand::{random, random_range};

    use crate::kernel::{
        memory::{Memory, MemorySegment},
        RegVal,
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
                    segment.off
                );
            }
        }
    }

    #[test]
    fn test_segment_contains() {
        for _ in 0..SEGMENT_SAMPLING_COUNT {
            let off = random_range(0..0x0800_0000);
            let len = random_range(1..0x0800_0000);

            let segment = MemorySegment::new_zeroed(true, true, true, off, len);

            assert!(
                segment.contains_address(off),
                "segment {off}:{len} must contain {off}"
            );
            assert!(
                segment.contains_address(off + len - 1),
                "segment {off}:{len} must contain {}",
                off + len - 1
            );

            for _ in 0..ADDRESS_SAMPLING_COUNT {
                let address = random_range(off..off + len);
                assert!(
                    segment.contains_address(address),
                    "segment {off}:{len} must contain {address}"
                );
            }

            for _ in 0..ADDRESS_SAMPLING_COUNT {
                let address = random_range(0..off);
                assert!(
                    !segment.contains_address(address),
                    "segment {off}:{len} must not contain {address}"
                );
            }

            for _ in 0..ADDRESS_SAMPLING_COUNT {
                let address = random_range(off + len..=RegVal::MAX);
                assert!(
                    !segment.contains_address(address),
                    "segment {off}:{len} must not contain {address}"
                );
            }
        }
    }

    #[test]
    fn test_segment_overlaps_positive() {
        for _ in 0..SEGMENT_SAMPLING_COUNT {
            for _ in 0..ADDRESS_SAMPLING_COUNT {
                let off1 = random_range(0..0x0800_0000);
                let len1 = random_range(1..0x0800_0000);
                let segment1 = MemorySegment::new_zeroed(false, false, false, off1, len1);

                let off2 = off1 + random_range(0..len1 - 1);
                let len2 = random_range(1..0x0800_0000);

                assert!(
                    segment1.overlaps_segment(off2, len2),
                    "segment {off1}:{len1} must overlap {off2}:{len2}"
                );
            }

            for _ in 0..ADDRESS_SAMPLING_COUNT {
                let off1 = random_range(0..0x0800_0000);
                let len1 = random_range(1..0x0800_0000);
                let segment1 = MemorySegment::new_zeroed(false, false, false, off1, len1);

                let end2 = off1 + random_range(1..len1 - 1);
                let off2 = random_range(0..end2);
                let len2 = end2 - off2;

                assert!(
                    segment1.overlaps_segment(off2, len2),
                    "segment {off1}:{len1} must overlap {off2}:{len2}"
                );
            }
        }
    }

    #[test]
    fn test_segment_overlaps_negative() {
        for _ in 0..SEGMENT_SAMPLING_COUNT {
            for _ in 0..ADDRESS_SAMPLING_COUNT {
                let off1 = random_range(0..0x0800_0000);
                let len1 = random_range(1..0x0800_0000);
                let segment1 = MemorySegment::new_zeroed(false, false, false, off1, len1);

                let off2 = off1 + len1 + random_range(0..0x0800_0000);
                let len2 = random_range(1..0x0800_0000);

                assert!(
                    !segment1.overlaps_segment(off2, len2),
                    "segment {off1}:{len1} must not overlap {off2}:{len2}"
                );
            }

            for _ in 0..ADDRESS_SAMPLING_COUNT {
                let off1 = random_range(0..0x0800_0000);
                let len1 = random_range(1..0x0800_0000);
                let segment1 = MemorySegment::new_zeroed(false, false, false, off1, len1);

                let end2 = random_range(0..off1);
                let off2 = random_range(0..=end2);
                let len2 = end2 - off2;

                assert!(
                    !segment1.overlaps_segment(off2, len2),
                    "segment {off1}:{len1} must not overlap {off2}:{len2}"
                );
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
            off: 0,
            mem: segment_mem,
        })
        .unwrap();

        for (idx, target) in sample_instructions.into_iter().enumerate() {
            let address = idx as RegVal * 4;
            let instr = mem.fetch_instruction(address).unwrap();

            assert_eq!(target, instr);
        }
    }
}
