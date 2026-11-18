//! **The card: one context owning its stream and buffers, and its census** (the hardware law; #15).
//!
//! [definition] **Common context ownership (#15).** A [`Card`] owns one driver context and, inside
//! it, one ordered stream. Every buffer is a [`CardBuffer`] that borrows
//! its card, so it cannot outlive the context that allocated it, and every launch and transfer
//! refuses a buffer of another card ([`CardError::ForeignBuffer`]): a cross-context use is
//! unrepresentable past the card's life and refused within it. The card makes its context current
//! before each driver call and before its buffers are released, so an owner on another
//! context in the same thread never receives this card's work.
//!
//! [definition] **The census** ([`DeviceCensus`]): the device's capacity read through the driver
//! (multiprocessors, warp, threads and blocks per block and per multiprocessor, the grid, shared
//! memory and registers per block and per multiprocessor, memory). **No bound is authored:** what a
//! launch takes of the device (its multiprocessors, its memory) it reads here.

use crate::cuda::{
    self, Context, CudaError, Device, DeviceAttribute, DeviceBuffer, DeviceZeroable, Dim3,
    MemoryInfo, Stream,
};
use crate::ffi::CUdeviceptr;

/// [definition; November 14, C3 of #603] **The card's refusals**: the driver's, the census, a foreign buffer and a
/// shape. They were cases of the October `DeviceError` (retired with its crate, C8 of #603); the card and the field's
/// realization return only these.
#[derive(Debug, thiserror::Error)]
pub enum CardError {
    #[error("the CUDA driver refused: {0}")]
    Driver(Box<CudaError>),
    #[error("the driver reported {what} = {value}; a census extent is positive")]
    Census { what: &'static str, value: i32 },
    #[error("a buffer of another card was offered; a card's launches read only its own buffers")]
    ForeignBuffer,
    #[error("{what}: expected {expected}, found {found}")]
    Shape {
        what: &'static str,
        expected: usize,
        found: usize,
    },
}

// -------------------------------------------------------------------------------------------
// the census

/// [definition] **The device's capacity**, read through the driver at the card's open.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceCensus {
    pub name: String,
    pub compute_capability: (u32, u32),
    pub multiprocessors: u32,
    /// The driver admits cooperative grids whose blocks are simultaneously resident.
    pub cooperative_launch: bool,
    pub warp: u32,
    pub max_threads_per_block: u32,
    pub max_threads_per_multiprocessor: u32,
    pub max_blocks_per_multiprocessor: u32,
    pub max_grid: Dim3,
    /// Shared octets a block may declare without opting in.
    pub shared_per_block: u32,
    pub shared_per_block_optin: u32,
    pub shared_per_multiprocessor: u32,
    pub registers_per_block: u32,
    pub registers_per_multiprocessor: u32,
    /// [measurement; theory, November 13, P56 item 5] The L2 cache's octets.
    pub l2_octets: u32,
    /// Free and total device memory at the open.
    pub memory: MemoryInfo,
}

impl DeviceCensus {
    /// Read the census off a device, in a context current on this thread.
    pub fn read(device: &Device, memory: MemoryInfo) -> Result<Self, CardError> {
        let read = |attribute: DeviceAttribute, what: &'static str| -> Result<u32, CardError> {
            let value = device.attribute(attribute)?;
            u32::try_from(value)
                .ok()
                .filter(|value| *value > 0)
                .ok_or(CardError::Census { what, value })
        };
        let census = device.launch_census()?;
        let minor = device.attribute(DeviceAttribute::COMPUTE_CAPABILITY_MINOR)?;
        let cooperative = device.attribute(DeviceAttribute::COOPERATIVE_LAUNCH)?;
        let cooperative_launch = match cooperative {
            0 => false,
            1 => true,
            value => {
                return Err(CardError::Census {
                    what: "cooperative launch boolean",
                    value,
                });
            }
        };
        Ok(Self {
            name: device.name.clone(),
            compute_capability: (
                read(DeviceAttribute::COMPUTE_CAPABILITY_MAJOR, "compute major")?,
                u32::try_from(minor).map_err(|_| CardError::Census {
                    what: "compute minor",
                    value: minor,
                })?,
            ),
            multiprocessors: census.multiprocessor_count,
            cooperative_launch,
            warp: read(DeviceAttribute::WARP_SIZE, "warp")?,
            max_threads_per_block: census.max_threads_per_block,
            max_threads_per_multiprocessor: read(
                DeviceAttribute::MAX_THREADS_PER_MULTIPROCESSOR,
                "threads per multiprocessor",
            )?,
            max_blocks_per_multiprocessor: read(
                DeviceAttribute::MAX_BLOCKS_PER_MULTIPROCESSOR,
                "blocks per multiprocessor",
            )?,
            max_grid: census.max_grid,
            shared_per_block: read(
                DeviceAttribute::MAX_SHARED_MEMORY_PER_BLOCK,
                "shared octets per block",
            )?,
            shared_per_block_optin: read(
                DeviceAttribute::MAX_SHARED_MEMORY_PER_BLOCK_OPTIN,
                "opt-in shared octets per block",
            )?,
            shared_per_multiprocessor: read(
                DeviceAttribute::MAX_SHARED_MEMORY_PER_MULTIPROCESSOR,
                "shared octets per multiprocessor",
            )?,
            registers_per_block: read(
                DeviceAttribute::MAX_REGISTERS_PER_BLOCK,
                "registers per block",
            )?,
            registers_per_multiprocessor: read(
                DeviceAttribute::MAX_REGISTERS_PER_MULTIPROCESSOR,
                "registers per multiprocessor",
            )?,
            l2_octets: read(DeviceAttribute::from_raw(38), "L2 cache octets")?,
            memory,
        })
    }
}

// -------------------------------------------------------------------------------------------
// the card

/// [definition] **The card**: one context, one ordered stream in it and its census. See the module
/// header.
///
/// [realization; November 14, C3 of #603] A card opens with no image ([`Card::open`]): an owner that
/// launches from its own image loads it (the field's, `Resident::open`).
pub struct Card {
    // Fields drop in declaration order: the stream before the context.
    stream: Stream,
    census: DeviceCensus,
    context: Context,
}

impl Drop for Card {
    fn drop(&mut self) {
        // The stream is released in this card's context.
        let _ = self.context.make_current();
    }
}

impl Card {
    /// **Open the card at a device ordinal**: a context, the census and a stream, with no image.
    pub fn open(ordinal: i32) -> Result<Self, CardError> {
        Self::opened(ordinal)
    }

    fn opened(ordinal: i32) -> Result<Self, CardError> {
        cuda::init()?;
        let device = Device::get(ordinal)?;
        let context = Context::create(&device)?;
        context.make_current()?;
        let census = DeviceCensus::read(&device, context.memory_info()?)?;
        let stream = Stream::create()?;
        Ok(Self {
            stream,
            census,
            context,
        })
    }

    pub fn census(&self) -> &DeviceCensus {
        &self.census
    }

    pub fn current(&self) -> Result<(), CardError> {
        Ok(self.context.make_current()?)
    }

    /// The card's ordered stream, for an owner that launches its own image's entries in the
    /// card's order (so [`Card::write`] and [`Card::fetch`] wait for them).
    pub fn stream(&self) -> &Stream {
        &self.stream
    }

    /// Refuse a buffer of another card.
    pub fn owns<T>(&self, buffer: &CardBuffer<'_, T>) -> Result<(), CardError> {
        if core::ptr::eq(buffer.card, self) {
            Ok(())
        } else {
            Err(CardError::ForeignBuffer)
        }
    }

    /// An uninitialized buffer of `len` elements (one element is reserved for an empty one).
    pub fn alloc<T: Copy>(&self, len: usize) -> Result<CardBuffer<'_, T>, CardError> {
        self.current()?;
        Ok(CardBuffer {
            card: self,
            buffer: DeviceBuffer::alloc(len.max(1))?,
            len,
        })
    }

    /// A buffer of `len` zeros, zeroed on the card's stream.
    pub fn zeroed<T: DeviceZeroable>(&self, len: usize) -> Result<CardBuffer<'_, T>, CardError> {
        let buffer = self.alloc::<T>(len)?;
        self.stream.memset_u32_async(
            buffer.device_ptr(),
            0,
            cuda::device_dword_count::<T>(len.max(1)),
        )?;
        Ok(buffer)
    }

    /// A buffer holding `values` (a synchronous transfer: complete when this returns).
    pub fn upload<T: Copy>(&self, values: &[T]) -> Result<CardBuffer<'_, T>, CardError> {
        let buffer = self.alloc::<T>(values.len())?;
        self.write(&buffer, 0, values)?;
        Ok(buffer)
    }

    /// Overwrite `values.len()` elements of a buffer from `offset`, after the card's stream has
    /// reached this point (a synchronous transfer).
    pub fn write<T: Copy>(
        &self,
        buffer: &CardBuffer<'_, T>,
        offset: usize,
        values: &[T],
    ) -> Result<(), CardError> {
        self.owns(buffer)?;
        if offset + values.len() > buffer.len {
            return Err(CardError::Shape {
                what: "a write within its buffer",
                expected: buffer.len,
                found: offset + values.len(),
            });
        }
        if values.is_empty() {
            return Ok(());
        }
        self.stream.synchronize()?;
        self.current()?;
        Ok(buffer.buffer.copy_range_from_slice(offset, values)?)
    }

    /// Zero `octets` octets of a buffer from the octet `offset`, ordered on the card's stream (no
    /// transfer); both are multiples of four, the memset's word.
    pub fn zero_octets<T: Copy>(
        &self,
        buffer: &CardBuffer<'_, T>,
        offset: usize,
        octets: usize,
    ) -> Result<(), CardError> {
        self.owns(buffer)?;
        let extent = buffer.len * core::mem::size_of::<T>();
        if !offset.is_multiple_of(4) || !octets.is_multiple_of(4) || offset + octets > extent {
            return Err(CardError::Shape {
                what: "a zeroed range of whole 4-octet words within its buffer",
                expected: extent,
                found: offset + octets,
            });
        }
        if octets == 0 {
            return Ok(());
        }
        self.current()?;
        Ok(self.stream.memset_u32_async(
            buffer.device_ptr() + offset as CUdeviceptr,
            0,
            octets / 4,
        )?)
    }

    /// **Read a buffer back** after every launch ordered before it (a transfer across the bus).
    pub fn fetch<T: Copy + Default>(
        &self,
        buffer: &CardBuffer<'_, T>,
    ) -> Result<Vec<T>, CardError> {
        self.fetch_range(buffer, 0, buffer.len)
    }

    /// Read `len` elements from `offset` back after every launch ordered before it.
    pub fn fetch_range<T: Copy + Default>(
        &self,
        buffer: &CardBuffer<'_, T>,
        offset: usize,
        len: usize,
    ) -> Result<Vec<T>, CardError> {
        self.owns(buffer)?;
        if offset + len > buffer.len {
            return Err(CardError::Shape {
                what: "a fetch within its buffer",
                expected: buffer.len,
                found: offset + len,
            });
        }
        let mut values = vec![T::default(); len];
        if len == 0 {
            return Ok(values);
        }
        self.stream.synchronize()?;
        self.current()?;
        buffer.buffer.copy_range_to_slice(offset, &mut values)?;
        Ok(values)
    }

    /// Wait until every launch on the card's stream has completed.
    pub fn synchronize(&self) -> Result<(), CardError> {
        Ok(self.stream.synchronize()?)
    }
}

/// [definition] **A buffer of one card** (#15): it borrows its card, so it cannot outlive the
/// context that allocated it, and the card refuses it anywhere else. Released in its card's
/// context, after every launch ordered on the card's stream has completed, so no launch in flight
/// reads a released buffer.
pub struct CardBuffer<'c, T> {
    card: &'c Card,
    buffer: DeviceBuffer<T>,
    len: usize,
}

impl<T> Drop for CardBuffer<'_, T> {
    fn drop(&mut self) {
        let _ = self.card.context.make_current();
        let _ = self.card.stream.synchronize();
    }
}

impl<'c, T: Copy> CardBuffer<'c, T> {
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn device_ptr(&self) -> CUdeviceptr {
        self.buffer.device_ptr()
    }
}

impl From<CudaError> for CardError {
    fn from(error: CudaError) -> Self {
        CardError::Driver(Box::new(error))
    }
}
