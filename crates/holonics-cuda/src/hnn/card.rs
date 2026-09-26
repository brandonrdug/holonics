//! **The card: one context owning its module, stream and buffers, its census, and the launches
//! derived from it** (the hardware law; #15).
//!
//! [definition] **Common context ownership (#15).** A [`Card`] owns one driver context and, inside
//! it, the HNN's loaded image and one ordered stream. Every buffer is a [`CardBuffer`] that borrows
//! its card, so it cannot outlive the context that allocated it, and every launch and transfer
//! refuses a buffer of another card ([`DeviceError::ForeignBuffer`]): a cross-context use is
//! unrepresentable past the card's life and refused within it. The card makes its context current
//! before each driver call and before its buffers and module are released, so an owner on another
//! context in the same thread never receives this card's work.
//!
//! [definition] **The census** ([`DeviceCensus`], [`EntryCensus`]): the device's capacity read
//! through the driver (multiprocessors, warp, threads and blocks per block and per multiprocessor,
//! the grid, shared memory and registers per block and per multiprocessor, memory), and each
//! entry's lowered limits (its thread ceiling, registers, static shared and local octets). **No
//! bound is authored:** every layout below is derived from these readings and the shape it
//! covers, and a shape the census cannot carry is refused ([`DeviceError::Launch`]).
//!
//! [definition] **The partition is certified before the launch** (CLAUDE.md, hardware law):
//! co-present blocks and threads commute when their reads and writes do.
//! - The lattice read ([`read_layout`]): every block reads the shared immutable locus and operand
//!   and writes only its own output entry and status; within a block, the threads' partial sums are
//!   joined by the ring's addition and the certificate's saturated addition, both associative and
//!   commutative, so the tree's order changes no value and no refusal.
//! - The moment ingest ([`ingest_layout`]): one block, so no two blocks share the moment; within
//!   it, the counts are atomic integer additions (commutative), and each tile's scans are ordered
//!   by barriers.
//! - The word's tick and adjoint tick ([`read_layout`] over the flattened rows): every block reads
//!   the immutable charts and the state it is handed and writes only its own entry of the other
//!   state buffer, its status and its own remainder; the two state buffers alternate, so no block
//!   reads what another writes in the same launch.
//! - The inverse residual and refinement ([`read_layout`] over rows × columns): every block reads
//!   the immutable operator, chart and residual and writes only its own entry (the refinement into
//!   the other chart buffer). The certificate ([`certificate_layout`]): one block per chart, whose
//!   row sums are joined by a tree of maxima (associative and commutative).
//!
//! Each [`Layout`] carries its [`Realization`], the report the hardware law asks for.

use core::ffi::c_void;
use core::marker::PhantomData;

use crate::cuda::{
    self, Context, CudaError, Device, DeviceAttribute, DeviceBuffer, DeviceZeroable, Dim3,
    GraphCensus, GraphExec, MemoryInfo, Module, PinnedHost, Stream,
};
use crate::ffi::CUdeviceptr;
use crate::hnn::DeviceError;

/// The PTX image of `kernels/hnn.cu`, compiled by `build.rs`; empty when no `nvcc` answered.
const IMAGE: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/hnn.ptx"));

/// The architecture the image was built for, or the reason it is absent (`build.rs`).
pub const KERNELS: &str = env!("HOLONICS_CUDA_KERNELS");

// -------------------------------------------------------------------------------------------
// the census

/// [definition] **The device's capacity**, read through the driver at the card's open.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeviceCensus {
    pub name: String,
    pub compute_capability: (u32, u32),
    pub multiprocessors: u32,
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
    /// Free and total device memory at the open.
    pub memory: MemoryInfo,
}

impl DeviceCensus {
    /// Read the census off a device, in a context current on this thread.
    pub fn read(device: &Device, memory: MemoryInfo) -> Result<Self, DeviceError> {
        let read = |attribute: DeviceAttribute, what: &'static str| -> Result<u32, DeviceError> {
            let value = device.attribute(attribute)?;
            u32::try_from(value)
                .ok()
                .filter(|value| *value > 0)
                .ok_or(DeviceError::Census { what, value })
        };
        let census = device.launch_census()?;
        let minor = device.attribute(DeviceAttribute::COMPUTE_CAPABILITY_MINOR)?;
        Ok(Self {
            name: device.name.clone(),
            compute_capability: (
                read(DeviceAttribute::COMPUTE_CAPABILITY_MAJOR, "compute major")?,
                u32::try_from(minor).map_err(|_| DeviceError::Census {
                    what: "compute minor",
                    value: minor,
                })?,
            ),
            multiprocessors: census.multiprocessor_count,
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
            memory,
        })
    }
}

/// [definition] **One entry's lowered limits**, read after the driver lowered the PTX for this
/// card.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EntryCensus {
    pub name: &'static str,
    pub max_threads_per_block: u32,
    pub registers: u32,
    pub static_shared: u32,
    pub local_octets: usize,
}

// -------------------------------------------------------------------------------------------
// layouts

/// [definition] **The realization a launch enacts** (the hardware law's report: which index is a
/// block, which a thread, and what a thread loops over).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Realization {
    /// Each block is one output entry `(row, vector)` of a read; its `threads` divide the row's
    /// columns, each looping over at most `per_thread` of them (`j ≡ t mod threads`), and the
    /// block reduces their ring words and certificates by a shared-memory tree. `entries` blocks;
    /// no thread loops over rows.
    EntryPerBlock {
        entries: u64,
        threads: u32,
        per_thread: u32,
    },
    /// One block carries the whole cell sequence: each thread is one cell of a tile of `threads`
    /// cells, and the block loops over at most `tiles` tiles in order, carrying the rings' phases
    /// between them; within a tile each ring's advances are one block scan, in carry order.
    OneBlockScan { threads: u32, tiles: u64 },
    /// Each block is one chart of `charts`: its `threads` divide the chart's rows (`i ≡ t mod
    /// threads`), each thread looping over at most `rows_per_thread` rows and, within each, over
    /// the row's columns; the block keeps the largest row sum by a shared-memory tree of maxima.
    ChartPerBlock {
        charts: u64,
        threads: u32,
        rows_per_thread: u32,
    },
}

/// [definition] **A launch derived from the census**: its grid, block, dynamic shared octets and
/// realization.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Layout {
    pub grid: Dim3,
    pub block: Dim3,
    pub shared: u32,
    pub realization: Realization,
}

/// The greatest power of two at most `value` (`value ≥ 1`).
fn floor_power_of_two(value: u32) -> u32 {
    1 << value.ilog2()
}

/// The threads a block may carry for an entry: the entry's and the device's ceilings.
fn thread_ceiling(census: &DeviceCensus, entry: &EntryCensus) -> u32 {
    entry
        .max_threads_per_block
        .min(census.max_threads_per_block)
}

/// The dynamic shared octets a block may declare beside the entry's static shared.
fn shared_ceiling(census: &DeviceCensus, entry: &EntryCensus) -> u32 {
    census.shared_per_block.saturating_sub(entry.static_shared)
}

/// The shared octets per thread of the lattice read: its ring word and its certificate.
pub const READ_SHARED_PER_THREAD: u32 = 2 * core::mem::size_of::<i128>() as u32;

/// [definition] **The lattice read's layout** for `vectors` operands of a `rows × columns` locus:
/// one block per output entry; the block's width is the least power of two covering the row (at
/// least one warp), bounded by the entry's and the device's thread ceilings and by the shared
/// octets two 16-octet words per thread need; a row wider than the block is split over its
/// threads, each looping over `⌈columns/threads⌉` of its entries. The grid is `(rows, vectors)`,
/// refused past the device's grid.
pub fn read_layout(
    census: &DeviceCensus,
    entry: &EntryCensus,
    rows: usize,
    columns: usize,
    vectors: usize,
) -> Result<Layout, DeviceError> {
    if rows == 0 || columns == 0 || vectors == 0 {
        return Err(DeviceError::Launch {
            entry: entry.name,
            clause: "a read covers at least one row, column and vector",
        });
    }
    let (Ok(rows), Ok(columns), Ok(vectors)) = (
        u32::try_from(rows),
        u32::try_from(columns),
        u32::try_from(vectors),
    ) else {
        return Err(DeviceError::Launch {
            entry: entry.name,
            clause: "a read's extents fit the kernel's 32-bit wire",
        });
    };
    if rows > census.max_grid.x || vectors > census.max_grid.y {
        return Err(DeviceError::Launch {
            entry: entry.name,
            clause: "the rows fit the grid's X extent and the vectors its Y extent",
        });
    }
    let shared_threads = shared_ceiling(census, entry) / READ_SHARED_PER_THREAD;
    let ceiling = thread_ceiling(census, entry).min(shared_threads);
    if ceiling == 0 {
        return Err(DeviceError::Launch {
            entry: entry.name,
            clause: "the block carries at least one thread and its shared words",
        });
    }
    // Both are powers of two, so the least is one.
    let cover = columns
        .max(census.warp)
        .checked_next_power_of_two()
        .unwrap_or(u32::MAX);
    let threads = floor_power_of_two(ceiling).min(cover);
    Ok(Layout {
        grid: Dim3 {
            x: rows,
            y: vectors,
            z: 1,
        },
        block: Dim3::x(threads),
        shared: threads * READ_SHARED_PER_THREAD,
        realization: Realization::EntryPerBlock {
            entries: u64::from(rows) * u64::from(vectors),
            threads,
            per_thread: columns.div_ceil(threads),
        },
    })
}

/// The shared octets per thread of the inverse certificate: its largest row sum.
pub const CERTIFICATE_SHARED_PER_THREAD: u32 = core::mem::size_of::<u128>() as u32;

/// [definition] **The inverse certificate's layout** for `charts` charts of at most `width` rows:
/// one block per chart, as wide as the least power of two covering the widest chart's rows (at
/// least one warp), bounded by the entry's and the device's thread ceilings and by the shared
/// octets of one 16-octet word per thread; a chart with more rows than threads is split over them,
/// each looping over `⌈width/threads⌉` rows. The grid is `charts` blocks, refused past the
/// device's grid.
pub fn certificate_layout(
    census: &DeviceCensus,
    entry: &EntryCensus,
    charts: usize,
    width: usize,
) -> Result<Layout, DeviceError> {
    if charts == 0 || width == 0 {
        return Err(DeviceError::Launch {
            entry: entry.name,
            clause: "a certificate covers at least one chart of at least one row",
        });
    }
    let (Ok(charts), Ok(width)) = (u32::try_from(charts), u32::try_from(width)) else {
        return Err(DeviceError::Launch {
            entry: entry.name,
            clause: "the charts and their rows fit the kernel's 32-bit wire",
        });
    };
    if charts > census.max_grid.x {
        return Err(DeviceError::Launch {
            entry: entry.name,
            clause: "the charts fit the grid's X extent",
        });
    }
    let shared_threads = shared_ceiling(census, entry) / CERTIFICATE_SHARED_PER_THREAD;
    let ceiling = thread_ceiling(census, entry).min(shared_threads);
    if ceiling == 0 {
        return Err(DeviceError::Launch {
            entry: entry.name,
            clause: "the block carries at least one thread and its shared word",
        });
    }
    let cover = width
        .max(census.warp)
        .checked_next_power_of_two()
        .unwrap_or(u32::MAX);
    let threads = floor_power_of_two(ceiling).min(cover);
    Ok(Layout {
        grid: Dim3::x(charts),
        block: Dim3::x(threads),
        shared: threads * CERTIFICATE_SHARED_PER_THREAD,
        realization: Realization::ChartPerBlock {
            charts: u64::from(charts),
            threads,
            rows_per_thread: width.div_ceil(threads),
        },
    })
}

/// The ingest's shared octets: `rings` 8-octet advance totals and 4-octet phases, and one 4-octet
/// scan word per ring and thread.
pub fn ingest_shared(rings: u32, threads: u32) -> Option<u32> {
    rings
        .checked_mul(12)?
        .checked_add(rings.checked_mul(threads)?.checked_mul(4)?)
}

/// [definition] **The moment ingest's layout** for `rings` rings and `cells` cells: one block, as
/// wide as the greatest power of two the entry's and the device's thread ceilings and the shared
/// octets of its `rings` scans admit; `lanes`, when given, narrows the block further (a
/// realization choice, which changes no value: the parity test crosses tiles with it).
pub fn ingest_layout(
    census: &DeviceCensus,
    entry: &EntryCensus,
    rings: usize,
    cells: usize,
    lanes: Option<u32>,
) -> Result<Layout, DeviceError> {
    let Ok(rings) = u32::try_from(rings) else {
        return Err(DeviceError::Launch {
            entry: entry.name,
            clause: "the rings fit the kernel's 32-bit wire",
        });
    };
    if rings == 0 {
        return Err(DeviceError::Launch {
            entry: entry.name,
            clause: "an ingest steps at least one ring",
        });
    }
    let available = shared_ceiling(census, entry);
    let fixed = rings * 12;
    let shared_threads = available.saturating_sub(fixed) / (4 * rings);
    let mut ceiling = thread_ceiling(census, entry).min(shared_threads);
    if let Some(lanes) = lanes {
        ceiling = ceiling.min(lanes);
    }
    if ceiling == 0 {
        return Err(DeviceError::Launch {
            entry: entry.name,
            clause: "the block carries at least one cell and its rings' scans",
        });
    }
    let threads = floor_power_of_two(ceiling);
    let shared = ingest_shared(rings, threads).ok_or(DeviceError::Launch {
        entry: entry.name,
        clause: "the ingest's shared octets fit a 32-bit extent",
    })?;
    Ok(Layout {
        grid: Dim3::x(1),
        block: Dim3::x(threads),
        shared,
        realization: Realization::OneBlockScan {
            threads,
            tiles: (cells as u64).div_ceil(u64::from(threads)),
        },
    })
}

// -------------------------------------------------------------------------------------------
// the card

/// [definition] **The card**: one context, the HNN's loaded image and one ordered stream in it,
/// and its census. See the module header.
pub struct Card {
    // Fields drop in declaration order: the image and the stream before the context.
    module: Module,
    stream: Stream,
    census: DeviceCensus,
    context: Context,
}

impl Drop for Card {
    fn drop(&mut self) {
        // The image and the stream are released in this card's context.
        let _ = self.context.make_current();
    }
}

impl Card {
    /// **Open the card at a device ordinal**: a context, the census, the image and a stream.
    /// Refused with [`DeviceError::NoKernels`] when the build had no `nvcc`.
    pub fn open(ordinal: i32) -> Result<Self, DeviceError> {
        if IMAGE.is_empty() {
            return Err(DeviceError::NoKernels { reason: KERNELS });
        }
        cuda::init()?;
        let device = Device::get(ordinal)?;
        let context = Context::create(&device)?;
        context.make_current()?;
        let census = DeviceCensus::read(&device, context.memory_info()?)?;
        let module = Module::load_ptx(IMAGE)?;
        let stream = Stream::create()?;
        Ok(Self {
            module,
            stream,
            census,
            context,
        })
    }

    pub fn census(&self) -> &DeviceCensus {
        &self.census
    }

    pub(crate) fn current(&self) -> Result<(), DeviceError> {
        Ok(self.context.make_current()?)
    }

    /// An entry's lowered limits.
    pub fn entry(&self, name: &'static str) -> Result<EntryCensus, DeviceError> {
        self.current()?;
        let function = self.module.function(name)?;
        Ok(EntryCensus {
            name,
            max_threads_per_block: function.max_threads_per_block()?,
            registers: function.num_regs()?,
            static_shared: function.static_shared_bytes()?,
            local_octets: function.local_size_bytes()?,
        })
    }

    /// Refuse a buffer of another card.
    pub(crate) fn owns<T>(&self, buffer: &CardBuffer<'_, T>) -> Result<(), DeviceError> {
        if core::ptr::eq(buffer.card, self) {
            Ok(())
        } else {
            Err(DeviceError::ForeignBuffer)
        }
    }

    /// An uninitialized buffer of `len` elements (one element is reserved for an empty one).
    pub fn alloc<T: Copy>(&self, len: usize) -> Result<CardBuffer<'_, T>, DeviceError> {
        self.current()?;
        Ok(CardBuffer {
            card: self,
            buffer: DeviceBuffer::alloc(len.max(1))?,
            len,
        })
    }

    /// A buffer of `len` zeros, zeroed on the card's stream.
    pub fn zeroed<T: DeviceZeroable>(&self, len: usize) -> Result<CardBuffer<'_, T>, DeviceError> {
        let buffer = self.alloc::<T>(len)?;
        self.stream.memset_u32_async(
            buffer.device_ptr(),
            0,
            cuda::device_dword_count::<T>(len.max(1)),
        )?;
        Ok(buffer)
    }

    /// A buffer holding `values` (a synchronous transfer: complete when this returns).
    pub fn upload<T: Copy>(&self, values: &[T]) -> Result<CardBuffer<'_, T>, DeviceError> {
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
    ) -> Result<(), DeviceError> {
        self.owns(buffer)?;
        if offset + values.len() > buffer.len {
            return Err(DeviceError::Shape {
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

    /// Page-locked host staging of `octets` octets, allocated in the card's context.
    pub(crate) fn pinned(&self, octets: usize) -> Result<PinnedHost, DeviceError> {
        self.current()?;
        Ok(PinnedHost::alloc(octets)?)
    }

    fn staged_range<T: Copy>(
        buffer: &CardBuffer<'_, T>,
        offset: usize,
        staging: &PinnedHost,
        at: usize,
        octets: usize,
    ) -> Result<(), DeviceError> {
        let extent = buffer.len * core::mem::size_of::<T>();
        if offset + octets > extent || at + octets > staging.octets() {
            return Err(DeviceError::Shape {
                what: "a staged copy within its buffer and its staging",
                expected: extent.min(staging.octets()),
                found: (offset + octets).max(at + octets),
            });
        }
        Ok(())
    }

    /// **Copy `octets` octets of page-locked staging, from `at`, into a buffer at the octet
    /// `offset`**, ordered on the card's stream: no host synchronization.
    ///
    /// # Safety
    /// The staged octets stay unwritten until the card's stream has passed the copy.
    pub(crate) unsafe fn stage_in<T: Copy>(
        &self,
        buffer: &CardBuffer<'_, T>,
        offset: usize,
        staging: &PinnedHost,
        at: usize,
        octets: usize,
    ) -> Result<(), DeviceError> {
        self.owns(buffer)?;
        Self::staged_range(buffer, offset, staging, at, octets)?;
        self.current()?;
        unsafe {
            self.stream.copy_host_to_device_async(
                buffer.device_ptr() + offset as CUdeviceptr,
                staging.as_ptr().cast::<u8>().add(at).cast(),
                octets,
            )?;
        }
        Ok(())
    }

    /// **Copy `octets` octets of a buffer, from the octet `offset`, into page-locked staging at
    /// `at`**, ordered on the card's stream: the octets are there once the stream is synchronized.
    ///
    /// # Safety
    /// The staging octets are neither read nor written until the card's stream has passed the copy.
    pub(crate) unsafe fn stage_out<T: Copy>(
        &self,
        buffer: &CardBuffer<'_, T>,
        offset: usize,
        staging: &mut PinnedHost,
        at: usize,
        octets: usize,
    ) -> Result<(), DeviceError> {
        self.owns(buffer)?;
        Self::staged_range(buffer, offset, staging, at, octets)?;
        self.current()?;
        unsafe {
            self.stream.copy_device_to_host_async(
                staging.as_mut_octets().as_mut_ptr().add(at).cast(),
                buffer.device_ptr() + offset as CUdeviceptr,
                octets,
            )?;
        }
        Ok(())
    }

    /// Zero `octets` octets of a buffer from the octet `offset`, ordered on the card's stream (no
    /// transfer); both are multiples of four, the memset's word.
    pub(crate) fn zero_octets<T: Copy>(
        &self,
        buffer: &CardBuffer<'_, T>,
        offset: usize,
        octets: usize,
    ) -> Result<(), DeviceError> {
        self.owns(buffer)?;
        let extent = buffer.len * core::mem::size_of::<T>();
        if !offset.is_multiple_of(4) || !octets.is_multiple_of(4) || offset + octets > extent {
            return Err(DeviceError::Shape {
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
    ) -> Result<Vec<T>, DeviceError> {
        self.fetch_range(buffer, 0, buffer.len)
    }

    /// Read `len` elements from `offset` back after every launch ordered before it.
    pub fn fetch_range<T: Copy + Default>(
        &self,
        buffer: &CardBuffer<'_, T>,
        offset: usize,
        len: usize,
    ) -> Result<Vec<T>, DeviceError> {
        self.owns(buffer)?;
        if offset + len > buffer.len {
            return Err(DeviceError::Shape {
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

    /// Launch an entry on the card's stream at a derived layout. `params` point at each argument
    /// in declared order; the caller has checked every buffer with [`Card::owns`].
    pub(crate) fn launch(
        &self,
        entry: &'static str,
        layout: &Layout,
        params: &mut [*mut c_void],
    ) -> Result<(), DeviceError> {
        self.current()?;
        let function = self.module.function(entry)?;
        function.launch_on_shared(
            &self.stream,
            layout.grid,
            layout.block,
            layout.shared,
            params,
        )?;
        Ok(())
    }

    /// Wait until every launch on the card's stream has completed.
    pub fn synchronize(&self) -> Result<(), DeviceError> {
        Ok(self.stream.synchronize()?)
    }

    /// Begin recording the card's stream as one graph: launches issued until
    /// [`Card::end_capture`] are bound, not executed. No allocation or synchronous transfer may be
    /// issued in between (the driver refuses it).
    pub(crate) fn begin_capture(&self) -> Result<(), DeviceError> {
        self.current()?;
        Ok(self.stream.begin_capture()?)
    }

    /// Close the capture and instantiate the bound graph.
    pub(crate) fn end_capture(&self) -> Result<(GraphExec, GraphCensus), DeviceError> {
        self.current()?;
        let graph = self.stream.end_capture()?;
        let census = graph.census()?;
        Ok((graph.instantiate()?, census))
    }

    /// Launch an instantiated graph on the card's stream.
    pub(crate) fn launch_graph(&self, graph: &GraphExec) -> Result<(), DeviceError> {
        self.current()?;
        Ok(graph.launch(&self.stream)?)
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

    /// The card that owns it.
    pub(crate) fn card(&self) -> &'c Card {
        self.card
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub(crate) fn device_ptr(&self) -> CUdeviceptr {
        self.buffer.device_ptr()
    }
}

/// [definition] **A borrowed view of a resident operand**: `vectors` rows of `width` signed 64-bit
/// words at the lattice exponent `exponent` (a vector's value is its words times `2^(−exponent)`),
/// in a buffer of one card. It borrows the buffer, so the operand outlives every read of it.
#[derive(Clone, Copy)]
pub struct Operand<'a> {
    pub(crate) card: &'a Card,
    pub(crate) pointer: CUdeviceptr,
    pub(crate) vectors: usize,
    pub(crate) width: usize,
    pub(crate) exponent: u32,
    pub(crate) _borrow: PhantomData<&'a ()>,
}

impl Operand<'_> {
    pub fn vectors(&self) -> usize {
        self.vectors
    }

    pub fn width(&self) -> usize {
        self.width
    }

    pub fn exponent(&self) -> u32 {
        self.exponent
    }
}

impl From<CudaError> for DeviceError {
    fn from(error: CudaError) -> Self {
        DeviceError::Driver(Box::new(error))
    }
}
