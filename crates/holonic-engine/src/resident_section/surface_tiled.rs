use super::*;

impl<'chart> ResidentSurface<'chart> {
    // -----------------------------------------------------------------------------------------
    // the arithmetic control — a serial-chart reference can refute the helpers
    // -----------------------------------------------------------------------------------------

    /// Run the kernel's exact helpers on declared operands and return the wide results and the
    /// per-operand refusal words. A control, outside any passage; launched directly and
    /// synchronized, and counted as such.
    #[allow(clippy::type_complexity)]
    pub fn arithmetic_control(
        &self,
        a: &[i64],
        b: &[i64],
        s: &[i32],
        span: &[i64],
    ) -> Result<(Vec<[i128; 10]>, Vec<u32>), ResidentRefusal> {
        let n = a.len();
        if b.len() != n || s.len() != n || span.len() != n {
            return Err(ResidentRefusal::Declaration {
                operation: "arithmetic-control",
                what: "operand arrays of unequal length".to_owned(),
            });
        }
        self.context.make_current()?;
        let a_dev = self.alloc::<i64>(n)?;
        let b_dev = self.alloc::<i64>(n)?;
        let s_dev = self.alloc::<i32>(n)?;
        let span_dev = self.alloc::<i64>(n)?;
        let out = self.alloc::<i64>(n * 20)?;
        let refused = self.alloc::<u32>(n)?;
        a_dev.copy_from_slice(a)?;
        b_dev.copy_from_slice(b)?;
        s_dev.copy_from_slice(s)?;
        span_dev.copy_from_slice(span)?;
        refused.copy_from_slice(&vec![0u32; n.max(1)])?;
        let mut params = Params::new();
        params
            .ptr(a_dev.device_ptr())
            .ptr(b_dev.device_ptr())
            .ptr(s_dev.device_ptr())
            .ptr(span_dev.device_ptr())
            .u32(n as u32)
            .ptr(out.device_ptr())
            .ptr(refused.device_ptr());
        let function = self.function("section_arithmetic_control")?;
        let (grid, block) = self.flat_grid(n, "arithmetic-control")?;
        let stream = Stream::create()?;
        let mut pointers = params.pointers();
        function.launch_on_shared(&stream, grid, block, 0, &mut pointers)?;
        stream.synchronize()?;
        {
            let mut census = self.census.borrow_mut();
            census.control_launches += 1;
            census.synchronizations += 1;
        }
        let mut words = vec![0i64; n * 20];
        out.copy_to_slice(&mut words)?;
        let mut flags = vec![0u32; n];
        refused.copy_to_slice(&mut flags)?;
        let results = (0..n)
            .map(|i| {
                let mut row = [0i128; 10];
                for (j, slot) in row.iter_mut().enumerate() {
                    let lo = words[(i * 10 + j) * 2] as u64;
                    let hi = words[(i * 10 + j) * 2 + 1] as u64;
                    *slot = ((u128::from(hi) << 64) | u128::from(lo)) as i128;
                }
                row
            })
            .collect();
        let shrink = (n.max(1) * (8 + 8 + 4 + 8 + 160 + 4)) as u64;
        self.census.borrow_mut().resident_shrank(shrink);
        Ok((results, flags))
    }

    // -----------------------------------------------------------------------------------------
    // the tiled contraction — one law, a second realization, and a caller-declared geometry
    // -----------------------------------------------------------------------------------------

    /// The multiprocessor's declared residency ceilings, as the device stated them at mount.
    pub fn multiprocessor_limits(&self) -> MultiprocessorLimits {
        self.sm_limits
    }

    /// **The registers per thread the loaded module actually carries for one entry**, read through
    /// `cuFuncGetAttribute(CU_FUNC_ATTRIBUTE_NUM_REGS)` after the driver lowered the PTX for this
    /// card. A measurement of the apparatus, never an estimate and never a governor.
    pub fn measured_registers(&self, symbol: &str) -> Result<u32, ResidentRefusal> {
        Ok(self.function(symbol)?.num_regs()?)
    }

    /// The statically declared shared octets of one entry — excluding the dynamic extent a launch
    /// declares, which the caller's tile decides.
    pub fn measured_static_shared(&self, symbol: &str) -> Result<u32, ResidentRefusal> {
        Ok(self.function(symbol)?.static_shared_bytes()?)
    }

    /// The per-thread local surface of one entry, in octets, as the driver reports it after
    /// lowering. Nonzero means the entry spilled or holds a stack frame; zero is lawful.
    pub fn measured_local_octets(&self, symbol: &str) -> Result<u32, ResidentRefusal> {
        Ok(u32::try_from(self.function(symbol)?.local_size_bytes()?).unwrap_or(u32::MAX))
    }

    /// The block extent one entry admits, as the driver reports it after lowering.
    pub fn measured_block_ceiling(&self, symbol: &str) -> Result<u32, ResidentRefusal> {
        Ok(self.function(symbol)?.max_threads_per_block()?)
    }

    /// The predicted shape of the tiled contraction. **The octave admission is the SAME as
    /// [`ResidentSurface::shape_contract`]'s**, deliberately and by derivation: the a-priori bound
    /// `input_octaves + entry_octaves + ceil_log2(inner) + 1` is subset-monotone, so no tree over
    /// any K-partition can widen it and no new admission law is needed. What the tile adds is
    /// apparatus: the block, the dynamic shared extent and the launch count.
    pub fn shape_contract_tiled(
        &self,
        rows: usize,
        inner: usize,
        input_octaves: u32,
        map: &MountedReadout<'chart>,
        tile: TileGeometry,
    ) -> Result<LawShape, ResidentRefusal> {
        const OPERATION: &str = "contract-tiled";
        if inner != map.dim() {
            return Err(ResidentRefusal::WidthDisagrees {
                operation: OPERATION,
                left: inner,
                right: map.dim(),
            });
        }
        let out_width = map.rows();
        tile.admit(
            OPERATION,
            self.launch.block_x,
            self.launch.warp,
            self.max_shared_octets,
        )?;
        let needed = input_octaves + map.entry_octaves() + ceil_log2(inner) + 1;
        Self::admit_octaves(OPERATION, needed)?;
        let blocks = tile.blocks(rows, out_width);
        if blocks > u64::from(self.launch.max_grid_x) {
            return Err(ResidentRefusal::GridAperture {
                operation: OPERATION,
                rows,
                width: out_width,
            });
        }
        let mut work = ExactWork::predicted_product(
            rows,
            inner,
            out_width,
            u64::from(input_octaves.max(map.entry_octaves())),
        );
        work.entries_written = BigUint::from(2 * (rows * out_width) as u64);
        work.resident(2 * (rows * out_width) as u64);
        let peak = u64::from(input_octaves)
            + u64::from(map.entry_octaves())
            + u64::from(ceil_log2(inner))
            + 1;
        work.peak_bits = BigUint::from(peak);
        work.cumulative_bits = BigUint::from(2 * (rows * out_width) as u64 * peak);
        // The dependency span the geometry realizes: the serial K a lane walks, then the lane tree,
        // then (split-K only) the join tree. The scalar owner's span is `inner`.
        let lanes = u64::from(tile.lanes);
        let splits = u64::from(tile.splits.max(1));
        let serial = (inner as u64).div_ceil(lanes * splits);
        work.dependency_span = BigUint::from(
            serial
                + u64::from(ceil_log2(tile.lanes as usize))
                + u64::from(ceil_log2(tile.splits.max(1) as usize)),
        );
        let couplings = vec![CouplingPlan {
            coupling: "the inner contraction over K, folded by a fixed lane tree inside one block",
            kernel: tile.symbol(OPERATION)?,
            extent: inner as u64,
            block: tile.block(),
            predicted: {
                let mut reduction = ExactWork::nothing();
                reduction.added((rows * out_width) as u64 * (inner as u64));
                reduction.dependency_span =
                    BigUint::from(serial + u64::from(ceil_log2(tile.lanes as usize)));
                reduction
            },
        }];
        // K-complete: the semantic kernel and its census. Split-K: the partial, the join, the census.
        let launches = if tile.splits > 1 { 3 } else { 2 };
        Ok(LawShape {
            operation: OPERATION,
            rows,
            width: out_width,
            needed,
            predicted: work,
            couplings,
            launches,
            shared_octets: tile.shared_octets(),
            block: tile.block(),
        })
    }

    /// **Retain one split-K partial standing on the card.** `4` exact `i64` words per output
    /// coordinate per partial: the low and high halves of the lower accumulator, then of the upper.
    /// Nothing here is at the grain and nothing here is rounded.
    pub fn retain_partials(
        &self,
        rows: usize,
        out_width: usize,
        splits: u32,
    ) -> Result<PartialStanding, ResidentRefusal> {
        if splits == 0 || !splits.is_power_of_two() || splits > 16 {
            return Err(ResidentRefusal::Declaration {
                operation: "contract-split-k",
                what: format!("a split factor of {splits} is not a power of two in 1..=16"),
            });
        }
        let words = 4 * rows * out_width * splits as usize;
        let buffer = self.alloc::<i64>(words)?;
        let pointer = buffer.device_ptr();
        let mut held = self.partials.borrow_mut();
        held.push(buffer);
        Ok(PartialStanding {
            index: held.len() - 1,
            pointer,
            rows,
            out_width,
            splits,
            words,
        })
    }

    /// Release one retained partial standing once its join has returned.  The slot keeps its
    /// index so every other standing's address stays valid; it holds an empty buffer thereafter.
    pub fn release_partials(&self, standing: &PartialStanding) -> Result<(), ResidentRefusal> {
        let mut held = self.partials.borrow_mut();
        let slot = held
            .get_mut(standing.index)
            .ok_or_else(|| ResidentRefusal::Declaration {
                operation: "contract-split-k",
                what: "a partial standing this surface does not hold".to_owned(),
            })?;
        let released = std::mem::replace(slot, DeviceBuffer::<i64>::alloc(1)?);
        let octets = (released.len() * std::mem::size_of::<i64>()) as u64;
        drop(released);
        self.released_octets(octets);
        Ok(())
    }

    /// Zero one retained partial standing, so slots no tile writes fold as exact zeros.
    pub fn zero_partials(&self, standing: &PartialStanding) -> Result<(), ResidentRefusal> {
        let held = self.partials.borrow();
        let buffer = held
            .get(standing.index)
            .ok_or_else(|| ResidentRefusal::Declaration {
                operation: "contract-split-k",
                what: "a partial standing this surface does not hold".to_owned(),
            })?;
        let zeros = vec![0i64; standing.words];
        buffer.copy_from_slice(&zeros)?;
        self.census.borrow_mut().ingress_octets += (standing.words * 8) as u64;
        Ok(())
    }

    /// Read one retained partial standing back as its exact 128-bit accumulations, indexed
    /// `((a * rows) + row) * out_width + column`. The CPU-side replay of the declared join tree
    /// runs on exactly these words.
    pub fn read_partials(
        &self,
        standing: &PartialStanding,
    ) -> Result<Vec<(i128, i128)>, ResidentRefusal> {
        let held = self.partials.borrow();
        let buffer = held
            .get(standing.index)
            .ok_or_else(|| ResidentRefusal::Declaration {
                operation: "contract-split-k",
                what: "a partial standing this surface does not hold".to_owned(),
            })?;
        let mut words = vec![0i64; standing.words];
        buffer.copy_to_slice(&mut words)?;
        self.census.borrow_mut().egress_receipt_octets += (standing.words * 8) as u64;
        Ok((0..standing.words / 4)
            .map(|p| {
                let compose = |low: i64, high: i64| -> i128 {
                    (((high as u64 as u128) << 64) | (low as u64 as u128)) as i128
                };
                (
                    compose(words[4 * p], words[4 * p + 1]),
                    compose(words[4 * p + 2], words[4 * p + 3]),
                )
            })
            .collect())
    }

    /// Record the K-complete tiled contraction: one block owns a disjoint output tile and the whole
    /// inner extent. `tree` selects which fixed word the lanes fold under; `Descending` is the
    /// declared word and `Ascending` is the reversed control.
    #[allow(clippy::too_many_arguments)]
    pub fn record_contract_tiled(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        map: &MountedReadout<'chart>,
        tile: TileGeometry,
        admitted_node_octaves: u32,
        tree: LaneTree,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        const OPERATION: &str = "contract-tiled";
        if tile.splits != 1 {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: format!("a K-complete record with a split factor of {}", tile.splits),
            });
        }
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.rows as u32)
            .u32(input.width as u32)
            .ptr(map.raw_resident())
            .i32(map.exponent())
            .u32(map.rows() as u32)
            .i32(out.grain.0 as i32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .u32(tile.outs_per_block)
            .u32(tile.k_tile)
            .u32(admitted_node_octaves)
            .u32(tree.word())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        let blocks = tile.blocks(input.rows, map.rows());
        self.record_blocks(
            lane,
            tile.symbol(OPERATION)?,
            blocks as usize,
            tile.block(),
            tile.shared_octets(),
            &mut params,
            OPERATION,
        )
    }

    /// Record the split-K pair onto one lane: the exact 128-bit partial, then the join that folds
    /// the partials under the fixed balanced word and performs THE ONE OUTWARD ROUNDING. Both are
    /// one occurrence — one law, one output section, one census — recorded in order on one stream.
    #[allow(clippy::too_many_arguments)]
    pub fn record_contract_split_k(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        map: &MountedReadout<'chart>,
        tile: TileGeometry,
        standing: &PartialStanding,
        admitted_node_octaves: u32,
        tree: LaneTree,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        const OPERATION: &str = "contract-split-k";
        if tile.splits <= 1 {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: "a split-K record with no split".to_owned(),
            });
        }
        if standing.rows != input.rows
            || standing.out_width != map.rows()
            || standing.splits != tile.splits
        {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION,
                what: format!(
                    "the partial standing is {}x{}x{} and the launch is {}x{}x{}",
                    standing.splits,
                    standing.rows,
                    standing.out_width,
                    tile.splits,
                    input.rows,
                    map.rows()
                ),
            });
        }
        let mut partial_params = Params::new();
        partial_params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.rows as u32)
            .u32(input.width as u32)
            .ptr(map.raw_resident())
            .u32(map.rows() as u32)
            .ptr(standing.pointer)
            .u32(tile.splits)
            .u32(tile.outs_per_block)
            .u32(tile.k_tile)
            .u32(admitted_node_octaves)
            .u32(tree.word())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        let blocks = tile.blocks(input.rows, map.rows());
        self.record_blocks(
            lane,
            tile.symbol(OPERATION)?,
            blocks as usize,
            tile.block(),
            tile.shared_octets(),
            &mut partial_params,
            OPERATION,
        )?;
        let mut join_params = Params::new();
        join_params
            .ptr(standing.pointer)
            .u32(tile.splits)
            .u32(input.rows as u32)
            .u32(map.rows() as u32)
            .i32(map.exponent())
            .i32(out.grain.0 as i32)
            .u32(admitted_node_octaves)
            .u32(tree.word())
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_contract_join",
            input.rows * map.rows(),
            &mut join_params,
            OPERATION,
        )
    }

    /// **The finite candidate family for one contraction shape, from the device's own attributes
    /// and the module's MEASURED registers.** Every member is admitted: it is a whole-warp block the
    /// module carries an entry for, whose dynamic shared extent the device admits and whose grid the
    /// device can cover. Nothing here is ordered and nothing here is called optimal — domination is
    /// the caller's declared axis set, and [`non_dominated`] takes it.
    pub fn contract_candidates(
        &self,
        rows: usize,
        inner: usize,
        out_width: usize,
    ) -> Result<Vec<LaunchCandidate>, ResidentRefusal> {
        let mut family = Vec::new();
        for tile in TileGeometry::enumerate() {
            if tile
                .admit(
                    "contract-tiled",
                    self.launch.block_x,
                    self.launch.warp,
                    self.max_shared_octets,
                )
                .is_err()
            {
                continue;
            }
            let symbol = match tile.symbol(if tile.splits > 1 {
                "contract-split-k"
            } else {
                "contract-tiled"
            }) {
                Ok(symbol) => symbol,
                Err(_) => continue,
            };
            let blocks = tile.blocks(rows, out_width);
            if blocks == 0 || blocks > u64::from(self.launch.max_grid_x) {
                continue;
            }
            let registers = self.measured_registers(symbol)?;
            let shared = tile.shared_octets() + self.measured_static_shared(symbol)?;
            let block = tile.block();
            let limits = self.sm_limits;
            let warps = block.div_ceil(limits.warp.max(1)).max(1);
            let per_warp = (registers * limits.warp).div_ceil(limits.register_grain.max(1))
                * limits.register_grain.max(1);
            let by_blocks = limits.max_blocks;
            let by_threads = limits.max_threads / block.max(1);
            let by_registers = if per_warp == 0 {
                u32::MAX
            } else {
                limits.max_registers / (per_warp * warps).max(1)
            };
            let by_shared = if shared == 0 {
                u32::MAX
            } else {
                limits.max_shared_octets / shared
            };
            let resident = by_blocks.min(by_threads).min(by_registers).min(by_shared);
            let bound_by = if resident == by_registers
                && by_registers <= by_shared
                && by_registers <= by_threads
                && by_registers <= by_blocks
            {
                "registers"
            } else if resident == by_shared && by_shared <= by_threads && by_shared <= by_blocks {
                "shared"
            } else if resident == by_threads && by_threads <= by_blocks {
                "threads"
            } else {
                "blocks"
            };
            let cover = u64::from(resident) * u64::from(limits.multiprocessors);
            family.push(LaunchCandidate {
                tile,
                symbol,
                block,
                shared_octets: shared,
                registers,
                local_octets: self.function(symbol)?.local_size_bytes()? as u32,
                resident_blocks: resident,
                occupancy: (resident * block, limits.max_threads.max(1)),
                blocks,
                residency_waves: (blocks, cover.max(1)),
                lane_waves: (
                    blocks * u64::from(block),
                    u64::from(limits.max_threads) * u64::from(limits.multiprocessors),
                ),
                serial_k_per_lane: (inner as u64)
                    .div_ceil(u64::from(tile.lanes) * u64::from(tile.splits.max(1))),
                dependency_span: (inner as u64)
                    .div_ceil(u64::from(tile.lanes) * u64::from(tile.splits.max(1)))
                    + u64::from(ceil_log2(tile.lanes as usize))
                    + u64::from(ceil_log2(tile.splits.max(1) as usize)),
                bound_by,
            });
        }
        Ok(family)
    }
}
