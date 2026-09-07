use super::*;

impl<'chart> ResidentSurface<'chart> {
    /// Completed Metal command-buffer times, observed without reading native state or waiting.
    #[cfg(target_os = "macos")]
    pub fn metal_execution_timing(&self) -> mount::cuda::MetalExecutionTiming {
        self.context.execution_timing()
    }
    /// **Mount the apparatus occurrence** on the readout's context. Refuses when no device answers,
    /// when the census names a device the readout did not mount, or when a kernel symbol is
    /// missing from the module.
    #[cfg(target_os = "linux")]
    pub fn on(readout: &'chart ResidentReadout) -> Result<Self, ResidentRefusal> {
        mount::cuda::init()?;
        if Device::count()? == 0 {
            return Err(ResidentRefusal::NoResidentChart);
        }
        let device = Device::get(0)?;
        if device.name != readout.device_name() {
            return Err(ResidentRefusal::DeviceDisagrees {
                readout: readout.device_name().to_owned(),
                mounted: device.name.clone(),
            });
        }
        let context = BorrowedContext::adopt(readout.raw_context())?;
        context.make_current()?;
        let module = Module::load_ptx(PTX)?;
        let attribute = |selector: i32| -> Result<u32, ResidentRefusal> {
            let value = device.attribute(DeviceAttribute::from_raw(selector))?;
            Ok(u32::try_from(value).unwrap_or(0))
        };
        let declaration = DeviceDeclaration {
            ordinal: 0,
            name: device.name.clone(),
            capability_major: attribute(ATTRIBUTE_COMPUTE_CAPABILITY_MAJOR)?,
            capability_minor: attribute(ATTRIBUTE_COMPUTE_CAPABILITY_MINOR)?,
            multiprocessors: attribute(ATTRIBUTE_MULTIPROCESSOR_COUNT)?,
            warp_size: attribute(ATTRIBUTE_WARP_SIZE)?,
            max_threads_per_block: attribute(ATTRIBUTE_MAX_THREADS_PER_BLOCK)?,
            max_threads_per_multiprocessor: attribute(ATTRIBUTE_MAX_THREADS_PER_MULTIPROCESSOR)?,
            max_grid_x: attribute(ATTRIBUTE_MAX_GRID_DIM_X)?,
            max_sectiond_bytes: attribute(ATTRIBUTE_MAX_SHARED_MEMORY_PER_BLOCK)?,
            async_engines: attribute(ATTRIBUTE_ASYNC_ENGINE_COUNT)?,
            concurrent_kernels: attribute(ATTRIBUTE_CONCURRENT_KERNELS)? != 0,
            unified_addressing: attribute(ATTRIBUTE_UNIFIED_ADDRESSING)? != 0,
        };
        let mut kernel_block = declaration.max_threads_per_block.max(1);
        for symbol in KERNELS {
            let function = module.function(symbol)?;
            kernel_block = kernel_block.min(function.max_threads_per_block()?);
        }
        let launch = DerivedLaunch::from_admissions(
            declaration.max_threads_per_block.max(1),
            kernel_block,
            declaration.max_grid_x.max(1),
            declaration.warp_size.max(1),
        );
        let reduction_block = {
            let admitted = launch.block_x.max(1);
            let mut block = 1u32;
            while block * 2 <= admitted {
                block *= 2;
            }
            block.max(launch.warp.max(1))
        };
        let cover = HardwareCover::over(Some(declaration.clone()));
        let sm_limits = MultiprocessorLimits {
            max_blocks: attribute(ATTRIBUTE_MAX_BLOCKS_PER_MULTIPROCESSOR)?,
            max_threads: declaration.max_threads_per_multiprocessor,
            max_registers: attribute(ATTRIBUTE_MAX_REGISTERS_PER_MULTIPROCESSOR)?,
            max_shared_octets: attribute(ATTRIBUTE_MAX_SHARED_MEMORY_PER_MULTIPROCESSOR)?,
            warp: declaration.warp_size.max(1),
            multiprocessors: declaration.multiprocessors.max(1),
            register_grain: REGISTER_GRAIN_PER_WARP,
        };
        let allocation_grain = context.allocation_grain_bytes()? as u64;
        let memory_at_mount = context.memory_info()?;
        let ptx_sha256 = Sha256::digest(PTX)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
        Ok(Self {
            readout,
            context,
            device,
            module,
            ptx_sha256,
            max_shared_octets: declaration.max_sectiond_bytes,
            declaration,
            cover,
            launch,
            reduction_block,
            memory_at_mount,
            allocation_grain,
            sm_limits,
            partials: RefCell::new(Vec::new()),
            census: RefCell::new(TransferCensus::default()),
        })
    }

    #[cfg(target_os = "macos")]
    pub fn on(readout: &'chart ResidentReadout) -> Result<Self, ResidentRefusal> {
        let device = Device::get(0)?;
        if device.name != readout.device_name() {
            return Err(ResidentRefusal::DeviceDisagrees {
                readout: readout.device_name().into(),
                mounted: device.name,
            });
        }
        let context = BorrowedContext::adopt(readout.raw_context())?;
        context.make_current()?;
        let module = Module::load_metal(METAL_SOURCE)?;
        let function = module.function("section_constitutive_circulation")?;
        let warp = function.execution_width();
        let block = function.max_threads_per_block()?.min(device.max_threads());
        let declaration = DeviceDeclaration {
            ordinal: 0,
            name: device.name.clone(),
            capability_major: 0,
            capability_minor: 0,
            // Metal does not publish CUDA SM/engine counts. Zero records unavailable testimony;
            // the ordered native implementation does not use those fields for placement.
            multiprocessors: 0,
            max_threads_per_multiprocessor: 0,
            async_engines: 0,
            warp_size: warp,
            max_threads_per_block: block,
            max_grid_x: u32::MAX,
            max_sectiond_bytes: device.max_shared_bytes(),
            concurrent_kernels: false,
            unified_addressing: device.unified_memory(),
        };
        // This dependent implementation intentionally uses one thread, within the queried
        // pipeline admission. The hardware SIMD width remains device testimony.
        let launch = DerivedLaunch {
            block_x: 1,
            max_grid_x: u32::MAX,
            warp,
        };
        let cover = HardwareCover::over(Some(declaration.clone()));
        let allocation_grain = context.allocation_grain_bytes()? as u64;
        let memory_at_mount = context.memory_info()?;
        let ptx_sha256 = Sha256::digest(METAL_SOURCE.as_bytes())
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        drop(function);
        Ok(Self {
            readout,
            context,
            device,
            module,
            ptx_sha256,
            max_shared_octets: declaration.max_sectiond_bytes,
            declaration,
            cover,
            launch,
            reduction_block: 1,
            memory_at_mount,
            allocation_grain,
            sm_limits: MultiprocessorLimits::default(),
            partials: RefCell::new(Vec::new()),
            census: RefCell::new(TransferCensus::default()),
        })
    }

    pub fn device_name(&self) -> &str {
        &self.device.name
    }
    pub fn readout(&self) -> &'chart ResidentReadout {
        self.readout
    }
    /// The device's own declaration, as the surface read it. A reading; the cover is built from it.
    pub fn declaration(&self) -> &DeviceDeclaration {
        &self.declaration
    }
    /// **The cover this surface stands under.** Built from the mounted device's own attributes;
    /// a passage reads it here and cannot be handed another.
    pub fn cover(&self) -> &HardwareCover {
        &self.cover
    }
    /// Kernel source/artifact content digest (PTX on CUDA, MSL source on Metal).
    /// The legacy method name is retained for source compatibility; this is artifact lineage.
    pub fn ptx_sha256(&self) -> &str {
        &self.ptx_sha256
    }
    /// The mode this surface stands in: source law, boundary, kernel name and content, device,
    /// arithmetic tier and apparatus chart. Two surfaces with one kernel name and different PTX
    /// are two modes.
    pub fn mode(&self) -> ModeIdentity {
        ModeIdentity::of(
            &self.cover,
            "holonic_engine::resident_section",
            "exact-integer-interval-v2",
            "exact_resident_section",
        )
        .with_kernel_content(self.ptx_sha256.clone())
    }
    /// CUDA free/total device memory, or Metal recommended working-set budget and
    /// remaining allocation budget. The latter is not physical free VRAM.
    pub fn memory_at_mount(&self) -> MemoryInfo {
        self.memory_at_mount
    }
    pub fn memory(&self) -> Result<MemoryInfo, ResidentRefusal> {
        Ok(self.context.memory_info()?)
    }
    /// The measured allocation grain, in octets. A deed's apparatus prediction rounds every
    /// allocation up to it; changing the grain changes the requirement lawfully and visibly.
    pub fn allocation_grain(&self) -> u64 {
        self.allocation_grain
    }
    /// The census so far. A reading, never a governor.
    pub fn census(&self) -> TransferCensus {
        self.census.borrow().clone()
    }
    /// The exact carrier's octave aperture: what an accumulation may occupy before the hand.
    pub const fn carrier_octaves() -> u32 {
        WIDE_OCTAVES - 1
    }
    /// The launch geometry derived from the device and the kernels: the block, the grid ceiling,
    /// the warp. Read by the passage to place cells on the cover's device chart.
    pub fn derived_launch(&self) -> (u32, u32, u32) {
        (
            self.launch.block_x,
            self.launch.max_grid_x,
            self.launch.warp,
        )
    }

    // -----------------------------------------------------------------------------------------
    // allocation, staging, mounting — the material's arrival, counted
    // -----------------------------------------------------------------------------------------

    pub(super) fn alloc<T: Copy>(&self, count: usize) -> Result<DeviceBuffer<T>, ResidentRefusal> {
        self.context.make_current()?;
        let buffer = DeviceBuffer::<T>::alloc(count.max(1))?;
        let mut census = self.census.borrow_mut();
        census.allocations += 1;
        census.resident_grew((count.max(1) * std::mem::size_of::<T>()) as u64);
        Ok(buffer)
    }

    /// **One counted pooled allocation of raw octets**, for a caller that reuses one standing
    /// across many deeds instead of allocating one per deed. The surface counts it exactly as it
    /// counts a section, so a pooled realization's allocation census is comparable with a
    /// per-deed one rather than invisible beside it.
    pub fn alloc_octets(&self, octets: usize) -> Result<DeviceBuffer<u8>, ResidentRefusal> {
        self.alloc::<u8>(octets)
    }

    /// Copy one exact octet subspan into a caller-owned resident pool and count the crossing.
    /// The pool remains opaque outside this crate; this is the bounded intake used when one
    /// coefficient atlas is too large to stage as a single serial allocation.
    pub(crate) fn copy_octets(
        &self,
        destination: &DeviceBuffer<u8>,
        offset: usize,
        octets: &[u8],
    ) -> Result<(), ResidentRefusal> {
        self.context.make_current()?;
        destination.copy_range_from_slice(offset, octets)?;
        self.census.borrow_mut().ingress_octets += octets.len() as u64;
        Ok(())
    }

    /// Copy one exact octet subspan between caller-owned resident pools and count the internal
    /// transport.  No octet crosses to the serial chart.
    pub(crate) fn copy_resident_octets(
        &self,
        destination: &DeviceBuffer<u8>,
        destination_offset: usize,
        source: &DeviceBuffer<u8>,
        source_offset: usize,
        octets: usize,
    ) -> Result<(), ResidentRefusal> {
        self.context.make_current()?;
        destination.copy_range_from_buffer(destination_offset, source, source_offset, octets)?;
        self.census.borrow_mut().device_to_device_octets += octets as u64;
        Ok(())
    }

    /// Release a pooled allocation's octets from the resident census. The buffer's own `Drop`
    /// frees the card; this is the census half, which a `DeviceBuffer` cannot do for itself
    /// because it does not know the surface.
    pub fn released_octets(&self, octets: u64) {
        self.census.borrow_mut().resident_shrank(octets);
    }

    /// **Synchronize a caller's stream and count it.** The terminal synchronization of a deed
    /// that launched its graphs onto a stream of its own rather than onto a passage's origin.
    pub fn synchronize_counted(&self, stream: &Stream) -> Result<(), ResidentRefusal> {
        self.context.make_current()?;
        stream.synchronize()?;
        self.census.borrow_mut().synchronizations += 1;
        Ok(())
    }

    /// A fresh section, allocated and unwritten. Allocation is counted; nothing launches.
    pub fn fresh_section(
        &'chart self,
        rows: usize,
        width: usize,
        grain: ResidentGrain,
    ) -> Result<ResidentSection<'chart>, ResidentRefusal> {
        let count = rows * width;
        let lo = self.alloc::<i64>(count)?;
        let hi = self.alloc::<i64>(count)?;
        Ok(ResidentSection {
            surface: self,
            lo,
            hi,
            rows,
            width,
            grain,
            octets: 2 * (count.max(1) * 8) as u64,
        })
    }

    /// Remount one exact detached section. Both endpoint populations cross once; no law is
    /// replayed and no midpoint is reconstructed from an exterior approximation.
    pub fn mount_section_rest(
        &'chart self,
        rest: &ResidentSectionRest,
    ) -> Result<ResidentSection<'chart>, ResidentRefusal> {
        rest.validate()
            .map_err(|what| ResidentRefusal::Declaration {
                operation: "mount-section-rest",
                what,
            })?;
        let section = self.fresh_section(rest.rows, rest.width, rest.grain)?;
        let mut lower = Vec::with_capacity(rest.intervals.len());
        let mut upper = Vec::with_capacity(rest.intervals.len());
        for (lo, hi) in &rest.intervals {
            lower.push(*lo);
            upper.push(*hi);
        }
        self.context.make_current()?;
        section.lo.copy_from_slice(&lower)?;
        section.hi.copy_from_slice(&upper)?;
        self.census.borrow_mut().ingress_octets += (rest.intervals.len() * 16) as u64;
        Ok(section)
    }

    /// Mount one already-sealed endpoint from an exterior rest without allocating a redundant
    /// upper endpoint. This is persistence of an existing point carrier, not interval projection.
    pub(crate) fn mount_endpoint_rest(
        &'chart self,
        rows: usize,
        width: usize,
        words: &[i64],
    ) -> Result<ResidentEndpoint<'chart>, ResidentRefusal> {
        if rows == 0 || width == 0 || rows.checked_mul(width) != Some(words.len()) {
            return Err(ResidentRefusal::Declaration {
                operation: "mount-endpoint-rest",
                what: "endpoint shape does not match its complete word population".into(),
            });
        }
        let endpoint = ResidentEndpoint {
            surface: self,
            words: self.alloc::<i64>(words.len())?,
            rows,
            width,
        };
        self.context.make_current()?;
        endpoint.words.copy_from_slice(words)?;
        self.census.borrow_mut().ingress_octets += (words.len() * 8) as u64;
        Ok(endpoint)
    }

    /// Explicit checkpoint egress of an existing sealed endpoint. No arithmetic is replayed.
    pub(crate) fn detach_endpoint(
        &self,
        endpoint: &ResidentEndpoint<'chart>,
    ) -> Result<Vec<i64>, ResidentRefusal> {
        let mut words = Vec::new();
        words
            .try_reserve_exact(endpoint.words.len())
            .map_err(|error| ResidentRefusal::Declaration {
                operation: "detach-endpoint",
                what: error.to_string(),
            })?;
        words.resize(endpoint.words.len(), 0);
        self.context.make_current()?;
        endpoint.words.copy_to_slice(&mut words)?;
        let mut census = self.census.borrow_mut();
        census.egress_section_octets += (words.len() * 8) as u64;
        census.section_read_outs += 1;
        Ok(words)
    }

    /// Detach one exact resident section after its passage has returned. This is one explicit
    /// apparatus egress and is counted by [`read_out`].
    pub fn detach_section(
        &self,
        section: &ResidentSection<'chart>,
        bound_octaves: u32,
    ) -> Result<ResidentSectionRest, ResidentRefusal> {
        let intervals = self.read_out(section)?;
        ResidentSectionRest::found(
            section.rows(),
            section.width(),
            section.grain(),
            bound_octaves,
            intervals,
        )
        .map_err(|what| ResidentRefusal::Declaration {
            operation: "detach-section-rest",
            what,
        })
    }

    /// Stage entering codewords: allocate once and upload (ingress). Refillable.
    pub fn stage_words(
        &'chart self,
        words: &[u16],
        rows: usize,
        width: usize,
    ) -> Result<StagedWords<'chart>, ResidentRefusal> {
        if words.len() != rows * width {
            return Err(ResidentRefusal::Ragged {
                operation: "stage",
                words: words.len(),
                rows,
                width,
            });
        }
        let buffer = self.alloc::<u16>(words.len())?;
        let staged = StagedWords {
            surface: self,
            buffer,
            rows,
            width,
            octets: (words.len().max(1) * 2) as u64,
        };
        self.refill(&staged, words)?;
        Ok(staged)
    }

    /// Upload new entering codewords into a staged buffer of the same extent — a later deed's
    /// material crossing once.
    pub fn refill(
        &self,
        staged: &StagedWords<'chart>,
        words: &[u16],
    ) -> Result<(), ResidentRefusal> {
        if words.len() != staged.rows * staged.width {
            return Err(ResidentRefusal::Ragged {
                operation: "refill",
                words: words.len(),
                rows: staged.rows,
                width: staged.width,
            });
        }
        self.context.make_current()?;
        staged.buffer.copy_from_slice(words)?;
        self.census.borrow_mut().ingress_octets += (words.len() * 2) as u64;
        Ok(())
    }

    /// Lay the site's band group elements down once. `elements[b] = ((cos_lo, cos_hi), (sin_lo,
    /// sin_hi))` at `2^-grain`, founded on the serial chart from the exact algebraic angle.
    pub fn mount_bands(
        &'chart self,
        elements: &[((i64, i64), (i64, i64))],
        grain: u32,
    ) -> Result<BandElements<'chart>, ResidentRefusal> {
        let n = elements.len();
        let cos_lo = self.alloc::<i64>(n)?;
        let cos_hi = self.alloc::<i64>(n)?;
        let sin_lo = self.alloc::<i64>(n)?;
        let sin_hi = self.alloc::<i64>(n)?;
        let mut words = vec![0i64; n];
        for (buffer, pick) in [(&cos_lo, 0usize), (&cos_hi, 1), (&sin_lo, 2), (&sin_hi, 3)] {
            for (slot, ((cl, ch), (sl, sh))) in words.iter_mut().zip(elements) {
                *slot = [*cl, *ch, *sl, *sh][pick];
            }
            buffer.copy_from_slice(&words)?;
        }
        self.census.borrow_mut().ingress_octets += (4 * n * 8) as u64;
        Ok(BandElements {
            surface: self,
            cos_lo,
            cos_hi,
            sin_lo,
            sin_hi,
            bands: n,
            grain,
            octets: (4 * n.max(1) * 8) as u64,
        })
    }

    /// The integer positions of a section's rows, laid down once.
    pub fn mount_positions(
        &'chart self,
        positions: &[u32],
    ) -> Result<Positions<'chart>, ResidentRefusal> {
        let buffer = self.alloc::<u32>(positions.len())?;
        buffer.copy_from_slice(positions)?;
        self.census.borrow_mut().ingress_octets += (positions.len() * 4) as u64;
        Ok(Positions {
            surface: self,
            buffer,
            rows: positions.len(),
            octets: (positions.len().max(1) * 4) as u64,
        })
    }

    /// **The terminal receiver's copy.** The one place a section crosses to the serial chart, and it
    /// is counted as such. Returns `(lo, hi)` per coordinate at the section's grain, row-major.
    pub fn read_out(
        &self,
        section: &ResidentSection<'chart>,
    ) -> Result<Vec<(i64, i64)>, ResidentRefusal> {
        self.context.make_current()?;
        let count = section.count();
        let mut lo = vec![0i64; count];
        let mut hi = vec![0i64; count];
        section.lo.copy_to_slice(&mut lo)?;
        section.hi.copy_to_slice(&mut hi)?;
        {
            let mut census = self.census.borrow_mut();
            census.egress_section_octets += (2 * count * 8) as u64;
            census.section_read_outs += 1;
        }
        Ok(lo.into_iter().zip(hi).collect())
    }

    /// Exact terminal-row receiver. The earlier rows stay resident as reconstruction fibre;
    /// no projection buffer or native mutation is needed to read this contiguous interval span.
    pub fn read_out_terminal_row(
        &self,
        section: &ResidentSection<'chart>,
    ) -> Result<Vec<(i64, i64)>, ResidentRefusal> {
        if section.rows == 0 || section.width == 0 {
            return Err(ResidentRefusal::Declaration {
                operation: "read-terminal-row",
                what: "empty source section".into(),
            });
        }
        let offset = (section.rows - 1)
            .checked_mul(section.width)
            .ok_or_else(|| ResidentRefusal::Declaration {
                operation: "read-terminal-row",
                what: "source row extent overflow".into(),
            })?;
        self.context.make_current()?;
        let mut lower = vec![0i64; section.width];
        let mut upper = vec![0i64; section.width];
        section.lo.copy_range_to_slice(offset, &mut lower)?;
        section.hi.copy_range_to_slice(offset, &mut upper)?;
        let mut census = self.census.borrow_mut();
        census.egress_section_octets += (section.width * 16) as u64;
        census.section_read_outs += 1;
        Ok(lower.into_iter().zip(upper).collect())
    }

    /// The octaves the entering words occupy after the exact dyadic scale and the placement at the
    /// grain — the mouth's a-priori bound, read from the material. Public so a caller can take the
    /// same reading the law takes.
    pub fn entering_octaves(words: &[u16], scale: Dyadic, grain: ResidentGrain) -> u32 {
        entering_octaves(words, scale, grain)
    }

    pub(super) fn admit_octaves(
        operation: &'static str,
        needed: u32,
    ) -> Result<(), ResidentRefusal> {
        let admitted = Self::carrier_octaves();
        if needed > admitted {
            return Err(ResidentRefusal::CarrierRange {
                operation,
                needed,
                admitted,
            });
        }
        Ok(())
    }
}
