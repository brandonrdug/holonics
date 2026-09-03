use super::*;

impl<'chart> ResidentSurface<'chart> {
    // -----------------------------------------------------------------------------------------
    // the passage: capture, launch once, read once
    // -----------------------------------------------------------------------------------------

    /// Begin binding a passage over a declared lineage: `lineage[i]` is the list of occurrences
    /// occurrence `i` reads (its predecessors in the diagram's bonds). The census array, one lane
    /// and one event per occurrence, and the **lineage array** — every occurrence's predecessor
    /// indices, sorted and deduplicated, uploaded before the capture opens — are allocated here;
    /// the capture opens with the memset that zeroes the census. Nothing launches until
    /// [`ResidentPassage::launch`].
    pub fn begin_passage(
        &'chart self,
        lineage: &[Vec<usize>],
    ) -> Result<PassageBuilder<'chart>, ResidentRefusal> {
        self.begin_passage_scheduled(lineage, Schedule::CoPresent)
    }

    /// The same passage bound with every occurrence ALSO ordered after the one opened before it —
    /// a total order over the same kernels. A control: the co-present realization and this one
    /// must return one complete receipt, or the interchange claim is refuted physically.
    pub fn begin_passage_serialized(
        &'chart self,
        lineage: &[Vec<usize>],
    ) -> Result<PassageBuilder<'chart>, ResidentRefusal> {
        self.begin_passage_scheduled(lineage, Schedule::Serialized)
    }

    /// Begin a passage under a declared [`Schedule`]. The schedule adds edges; it never removes
    /// the diagram's, and it never changes which slots a kernel reads.
    pub fn begin_passage_scheduled(
        &'chart self,
        lineage: &[Vec<usize>],
        schedule: Schedule,
    ) -> Result<PassageBuilder<'chart>, ResidentRefusal> {
        self.context.make_current()?;
        let occurrences = lineage.len();
        let mut declared: Vec<Vec<usize>> = Vec::with_capacity(occurrences);
        let mut flat: Vec<u32> = Vec::new();
        let mut offsets: Vec<(usize, usize)> = Vec::with_capacity(occurrences);
        for (index, producers) in lineage.iter().enumerate() {
            let mut sorted: Vec<usize> = producers.clone();
            sorted.sort_unstable();
            sorted.dedup();
            for producer in &sorted {
                if *producer >= index {
                    return Err(ResidentRefusal::Declaration {
                        operation: "passage",
                        what: format!(
                            "occurrence {index} declares predecessor {producer}, which is not earlier in the passage"
                        ),
                    });
                }
            }
            offsets.push((flat.len(), sorted.len()));
            flat.extend(sorted.iter().map(|p| *p as u32));
            declared.push(sorted);
        }
        let census_words = SLOT_WORDS * occurrences.max(1);
        let census_buffer = self.alloc::<u32>(census_words)?;
        let lineage_buffer = self.alloc::<u32>(flat.len().max(1))?;
        if !flat.is_empty() {
            lineage_buffer.copy_from_slice(&flat)?;
            self.census.borrow_mut().ingress_octets += (flat.len() * 4) as u64;
        }
        let origin = Stream::create()?;
        let mut lanes = Vec::with_capacity(occurrences);
        let mut events = Vec::with_capacity(occurrences);
        for _ in 0..occurrences {
            lanes.push(Stream::create()?);
            events.push(Event::create()?);
        }
        let memset_event = Event::create()?;
        origin.begin_capture()?;
        origin.memset_u32_async(census_buffer.device_ptr(), 0, census_words)?;
        memset_event.record(&origin)?;
        Ok(PassageBuilder {
            surface: self,
            origin,
            lanes,
            events,
            memset_event,
            census_buffer,
            lineage_buffer,
            lineage_words: flat.len(),
            declared,
            offsets,
            occurrences,
            nodes: 1,
            edges: 0,
            opened: vec![false; occurrences],
            closed: vec![false; occurrences],
            schedule,
            last_opened: None,
        })
    }

    pub(super) fn function(&self, symbol: &str) -> Result<mount::Function<'_>, ResidentRefusal> {
        Ok(self.module.function(symbol)?)
    }

    pub(super) fn flat_grid(
        &self,
        count: usize,
        operation: &'static str,
    ) -> Result<(Dim3, Dim3), ResidentRefusal> {
        let count32 = u32::try_from(count).map_err(|_| ResidentRefusal::GridAperture {
            operation,
            rows: count,
            width: 1,
        })?;
        let grid =
            self.launch
                .grid_for(count32.max(1))
                .map_err(|_| ResidentRefusal::GridAperture {
                    operation,
                    rows: count,
                    width: 1,
                })?;
        Ok((Dim3::x(grid), Dim3::x(self.launch.block_x)))
    }

    /// Record one flat kernel onto a lane. Counted as a captured launch.
    pub(super) fn record_flat(
        &self,
        lane: &Lane<'_, 'chart>,
        symbol: &str,
        count: usize,
        params: &mut Params,
        operation: &'static str,
    ) -> Result<(), ResidentRefusal> {
        let function = self.function(symbol)?;
        let (grid, block) = self.flat_grid(count, operation)?;
        let mut pointers = params.pointers();
        function.launch_on_shared(lane.stream, grid, block, 0, &mut pointers)?;
        self.census.borrow_mut().captured_launches += 1;
        Ok(())
    }

    pub(super) fn record_blocks(
        &self,
        lane: &Lane<'_, 'chart>,
        symbol: &str,
        blocks: usize,
        block: u32,
        shared: u32,
        params: &mut Params,
        operation: &'static str,
    ) -> Result<(), ResidentRefusal> {
        let function = self.function(symbol)?;
        let blocks32 = u32::try_from(blocks).map_err(|_| ResidentRefusal::GridAperture {
            operation,
            rows: blocks,
            width: 1,
        })?;
        if blocks32 > self.launch.max_grid_x {
            return Err(ResidentRefusal::GridAperture {
                operation,
                rows: blocks,
                width: 1,
            });
        }
        let mut pointers = params.pointers();
        function.launch_on_shared(
            lane.stream,
            Dim3::x(blocks32.max(1)),
            Dim3::x(block),
            shared,
            &mut pointers,
        )?;
        self.census.borrow_mut().captured_launches += 1;
        Ok(())
    }

    // Each `record_*` writes one occurrence's semantic kernel onto its lane. The parameter layout
    // is the kernel's signature, in order.

    pub fn record_enter(
        &self,
        lane: &Lane<'_, 'chart>,
        staged: &StagedWords<'chart>,
        scale: Dyadic,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        self.record_enter_resident_bfloat16(
            lane,
            staged.buffer.device_ptr(),
            staged.rows,
            staged.width,
            scale,
            out,
        )
    }

    /// Record the ordinary BF16 entering law from a coefficient population that is already
    /// resident.  The address is crate-private apparatus testimony; callers outside the engine
    /// cannot manufacture a resident source pointer.
    pub(crate) fn record_enter_resident_bfloat16(
        &self,
        lane: &Lane<'_, 'chart>,
        resident_words: u64,
        rows: usize,
        width: usize,
        scale: Dyadic,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let count = rows * width;
        if count != out.count() {
            return Err(ResidentRefusal::Ragged {
                operation: "enter",
                words: count,
                rows: out.rows,
                width: out.width,
            });
        }
        let mut params = Params::new();
        params
            .ptr(resident_words)
            .u32(count as u32)
            .i64(scale.significand)
            .i32(scale.exponent)
            .i32(out.grain.0 as i32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(lane, "section_from_bfloat16", count, &mut params, "enter")
    }

    pub fn record_contract(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        map: &MountedReadout<'chart>,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
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
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_contract",
            input.rows * map.rows(),
            &mut params,
            "contract",
        )
    }

    /// Record the rank-one junction as one device kernel.  The parameter order mirrors the
    /// kernel's two resident maps and keeps both factor ranges in the footprint certificate.
    pub fn record_factorized_contract(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        u: &MountedReadout<'chart>,
        v: &MountedReadout<'chart>,
        shape: &LawShape,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.rows as u32)
            .u32(input.width as u32)
            .ptr(u.raw_resident())
            .i32(u.exponent())
            .u32(u.rows() as u32)
            .ptr(v.raw_resident())
            .i32(v.exponent())
            .u32(v.rows() as u32)
            .u32(v.dim() as u32)
            .i32(out.grain.0 as i32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        // The factorized kernel is one block per input row; its shape's block and shared extent
        // are therefore part of the record rather than inferred from the final output count.
        self.record_blocks(
            lane,
            "section_factorized_contract",
            input.rows,
            shape.block,
            shape.shared_octets,
            &mut params,
            "factorized-contract",
        )
    }

    pub fn record_rms_rebase(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        group: usize,
        gain: Option<&MountedReadout<'chart>>,
        eps: Dyadic,
        shape: &LawShape,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.rows as u32)
            .u32(input.width as u32)
            .u32(group as u32)
            .ptr(gain.map(MountedReadout::raw_resident).unwrap_or(0))
            .i32(gain.map(MountedReadout::exponent).unwrap_or(0))
            .i64(eps.significand)
            .i32(eps.exponent)
            .i32(out.grain.0 as i32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        let blocks = input.rows * (input.width / group);
        self.record_blocks(
            lane,
            "section_rms_rebase",
            blocks,
            shape.block,
            shape.shared_octets,
            &mut params,
            "rms-rebase",
        )
    }

    pub fn record_chronology(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        heads: usize,
        head_width: usize,
        bands: &BandElements<'chart>,
        positions: &Positions<'chart>,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.rows as u32)
            .u32(heads as u32)
            .u32(head_width as u32)
            .ptr(bands.cos_lo.device_ptr())
            .ptr(bands.cos_hi.device_ptr())
            .ptr(bands.sin_lo.device_ptr())
            .ptr(bands.sin_hi.device_ptr())
            .i32(bands.grain as i32)
            .ptr(positions.buffer.device_ptr())
            .i32(out.grain.0 as i32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_chronology",
            input.rows * heads * (head_width / 2),
            &mut params,
            "chronology",
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn record_contact(
        &self,
        lane: &Lane<'_, 'chart>,
        q: &ResidentSection<'chart>,
        k: &ResidentSection<'chart>,
        v: &ResidentSection<'chart>,
        heads: usize,
        kv_heads: usize,
        head_width: usize,
        window: usize,
        terms: SeriesAperture,
        partition_boundaries: Option<&Positions<'chart>>,
        shape: &LawShape,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params
            .ptr(q.lo.device_ptr())
            .ptr(q.hi.device_ptr())
            .ptr(k.lo.device_ptr())
            .ptr(k.hi.device_ptr())
            .ptr(v.lo.device_ptr())
            .ptr(v.hi.device_ptr())
            .u32(q.rows as u32)
            .u32(heads as u32)
            .u32(kv_heads as u32)
            .u32(head_width as u32)
            .u32(window.max(1) as u32)
            .ptr(
                partition_boundaries
                    .map(Positions::device_ptr)
                    .unwrap_or(q.lo.device_ptr()),
            )
            .u32(
                partition_boundaries
                    .map(|boundaries| boundaries.rows() as u32)
                    .unwrap_or(0),
            )
            .i32(out.grain.0 as i32)
            .u32(terms.0)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.slot + 4)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_contact",
            q.rows * heads,
            shape.block,
            shape.shared_octets,
            &mut params,
            "contact",
        )
    }

    pub fn record_gelu_tanh(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        c1: Dyadic,
        c2: Dyadic,
        terms: SeriesAperture,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.count() as u32)
            .i64(c1.significand)
            .i32(c1.exponent)
            .i64(c2.significand)
            .i32(c2.exponent)
            .i32(out.grain.0 as i32)
            .u32(terms.0)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_gelu_tanh",
            input.count(),
            &mut params,
            "gelu-tanh",
        )
    }

    pub fn record_tanh(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        terms: SeriesAperture,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.count() as u32)
            .i32(out.grain.0 as i32)
            .u32(terms.0)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(lane, "section_tanh", input.count(), &mut params, "tanh")
    }

    pub fn record_hadamard(
        &self,
        lane: &Lane<'_, 'chart>,
        a: &ResidentSection<'chart>,
        b: &ResidentSection<'chart>,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params
            .ptr(a.lo.device_ptr())
            .ptr(a.hi.device_ptr())
            .ptr(b.lo.device_ptr())
            .ptr(b.hi.device_ptr())
            .u32(a.count() as u32)
            .i32(out.grain.0 as i32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(lane, "section_hadamard", a.count(), &mut params, "hadamard")
    }

    pub fn record_re_entry(
        &self,
        lane: &Lane<'_, 'chart>,
        a: &ResidentSection<'chart>,
        b: &ResidentSection<'chart>,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params
            .ptr(a.lo.device_ptr())
            .ptr(a.hi.device_ptr())
            .ptr(b.lo.device_ptr())
            .ptr(b.hi.device_ptr())
            .u32(a.count() as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(lane, "section_re_entry", a.count(), &mut params, "re-entry")
    }

    pub fn record_scale(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        by: DyadicEnclosure,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.count() as u32)
            .i64(by.lo)
            .i64(by.hi)
            .i32(by.grain as i32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(lane, "section_scale", input.count(), &mut params, "scale")
    }

    pub fn record_scale_by_aligned(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        coefficient: &MountedReadout<'chart>,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.count() as u32)
            .ptr(coefficient.raw_resident())
            .i32(coefficient.exponent())
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_scale_by_aligned",
            input.count(),
            &mut params,
            "scale-by-aligned",
        )
    }

    pub fn record_select_columns(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        from: usize,
        span: usize,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        if out.rows != input.rows || out.width != span {
            return Err(ResidentRefusal::Declaration {
                operation: "select-columns",
                what: "the output does not carry the declared coordinate face".to_owned(),
            });
        }
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.rows as u32)
            .u32(input.width as u32)
            .u32(from as u32)
            .u32(span as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_select_columns",
            input.rows * span,
            &mut params,
            "select-columns",
        )
    }

    pub fn record_withdraw_columns(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        from: usize,
        span: usize,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.rows as u32)
            .u32(input.width as u32)
            .u32(from as u32)
            .u32(span as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_withdraw_columns",
            input.count(),
            &mut params,
            "withdraw-columns",
        )
    }

    pub fn record_withdraw_rows(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        from: usize,
        span: usize,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.rows as u32)
            .u32(input.width as u32)
            .u32(from as u32)
            .u32(span as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_withdraw_rows",
            input.count(),
            &mut params,
            "withdraw-rows",
        )
    }

    /// Record the exact terminal-row restriction.  The source row stays resident; only the
    /// requested receiver fibre is copied into the successor section.
    pub fn record_terminal_row(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        if out.rows != 1 || out.width != input.width || input.rows == 0 {
            return Err(ResidentRefusal::Ragged {
                operation: "terminal-row",
                words: out.count(),
                rows: 1,
                width: input.width,
            });
        }
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.rows as u32)
            .u32(input.width as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_terminal_row",
            input.width,
            &mut params,
            "terminal-row",
        )
    }

    /// Record the exact terminal row of every addressed partition already mounted on the card.
    pub fn record_partition_terminal_rows(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        boundaries: &Positions<'chart>,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        if boundaries.rows() != out.rows + 1 || out.width != input.width {
            return Err(ResidentRefusal::Declaration {
                operation: "partition-terminal-rows",
                what: format!(
                    "input={}x{}, boundary population={}, output={}x{}",
                    input.rows,
                    input.width,
                    boundaries.rows(),
                    out.rows,
                    out.width
                ),
            });
        }
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.rows as u32)
            .u32(input.width as u32)
            .ptr(boundaries.device_ptr())
            .u32(out.rows as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_partition_terminal_rows",
            out.count(),
            &mut params,
            "partition-terminal-rows",
        )
    }

    /// Record the exact block means of a row partition already mounted on the card.
    pub fn record_partition_mean(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        boundaries: &Positions<'chart>,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        if boundaries.rows() != out.rows + 1 || out.width != input.width {
            return Err(ResidentRefusal::Declaration {
                operation: "partition-mean",
                what: format!(
                    "input={}x{}, boundary population={}, output={}x{}",
                    input.rows,
                    input.width,
                    boundaries.rows(),
                    out.rows,
                    out.width
                ),
            });
        }
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.rows as u32)
            .u32(input.width as u32)
            .ptr(boundaries.device_ptr())
            .u32(out.rows as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_partition_mean",
            out.count(),
            &mut params,
            "partition-mean",
        )
    }

    /// Record the block-permutation intervention; `permutation` is a mounted positions-like array of
    /// block indices (see [`ResidentSurface::mount_positions`]).
    pub fn record_permute_columns(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        block: usize,
        permutation: &Positions<'chart>,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.rows as u32)
            .u32(input.width as u32)
            .u32(block as u32)
            .ptr(permutation.device_ptr())
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_permute_columns",
            input.count(),
            &mut params,
            "permute-columns",
        )
    }

    pub fn record_collapse_control(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(input.count() as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_collapse_control",
            input.count(),
            &mut params,
            "collapse-control",
        )
    }

    /// Record the carry of a resident standing into `out`.
    pub fn record_carry(
        &self,
        lane: &Lane<'_, 'chart>,
        input: &ResidentSection<'chart>,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        if input.rows() != out.rows() || input.width() != out.width() {
            return Err(ResidentRefusal::RowsDisagree {
                operation: "carry",
                left: input.rows() * input.width(),
                right: out.rows() * out.width(),
            });
        }
        let mut params = Params::new();
        params
            .ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u32(out.count() as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(lane, "section_carry", out.count(), &mut params, "carry")
    }

    /// The census of one written section into the occurrence's slot, and the a-priori bound it was
    /// admitted under, which the census compares against.
    pub(super) fn record_census(
        &self,
        lane: &Lane<'_, 'chart>,
        out: &ResidentSection<'chart>,
        admitted_octaves: u32,
    ) -> Result<(), ResidentRefusal> {
        self.refuse_partial_warp_block("census")?;
        let mut params = Params::new();
        params
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .u32(out.count() as u32)
            .u32(admitted_octaves)
            .ptr(lane.slot);
        self.record_flat(lane, "section_census", out.count(), &mut params, "census")
    }

    /// **The fused midpoint quotient**: the collapse and this occurrence's census in one node,
    /// writing the midpoints over the predecessor's own words. Recorded by the passage rather than
    /// by the law, because the fusion is the passage's apparatus compression and the a-priori bound
    /// the census compares against is the passage's reading.
    pub fn record_midpoint_seal(
        &self,
        lane: &Lane<'_, 'chart>,
        predecessor: &ResidentSection<'chart>,
        admitted_octaves: u32,
    ) -> Result<(), ResidentRefusal> {
        self.refuse_partial_warp_block("midpoint-quotient(fused seal)")?;
        let mut params = Params::new();
        params
            .ptr(predecessor.lo.device_ptr())
            .ptr(predecessor.hi.device_ptr())
            .u32(predecessor.count() as u32)
            .u32(admitted_octaves)
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_midpoint_seal",
            predecessor.count(),
            &mut params,
            "midpoint-quotient(fused seal)",
        )
    }

    /// A warp fold with an incomplete mask is undefined, so a block that is not a whole number of
    /// warps refuses here rather than returning a plausible census. The surface's own launch
    /// derivation takes the block down to a whole number of warps, so this cannot fire on a mounted
    /// device; it is stated because the aggregation depends on it.
    pub(super) fn refuse_partial_warp_block(
        &self,
        operation: &'static str,
    ) -> Result<(), ResidentRefusal> {
        let warp = self.launch.warp.max(1);
        if self.launch.block_x % warp != 0 || self.launch.block_x / warp > CENSUS_MAX_WARPS {
            return Err(ResidentRefusal::Declaration {
                operation,
                what: format!(
                    "the block-aggregated census needs a whole number of warps, at most {CENSUS_MAX_WARPS}; the derived block is {} at warp {warp}",
                    self.launch.block_x
                ),
            });
        }
        Ok(())
    }

    /// **Both censuses, on one section, into two fresh slots** — the equality this deed measures
    /// rather than argues. `entry_refused` is the refusal word the slot carries when the census
    /// enters, so a poisoned lineage can be exhibited under both forms. Launched directly and
    /// synchronized, outside any passage, and counted as such.
    pub fn census_both(
        &self,
        section: &ResidentSection<'chart>,
        admitted_octaves: u32,
        entry_refused: u32,
    ) -> Result<(SlotReading, SlotReading), ResidentRefusal> {
        let aggregated =
            self.census_once("section_census", section, admitted_octaves, entry_refused)?;
        let control = self.census_once(
            "section_census_serial_control",
            section,
            admitted_octaves,
            entry_refused,
        )?;
        Ok((aggregated, control))
    }

    /// One census kernel on one section, into a fresh slot seeded with `entry_refused`.
    pub fn census_once(
        &self,
        symbol: &str,
        section: &ResidentSection<'chart>,
        admitted_octaves: u32,
        entry_refused: u32,
    ) -> Result<SlotReading, ResidentRefusal> {
        self.context.make_current()?;
        let slot = self.alloc::<u32>(SLOT_WORDS)?;
        let mut words = vec![0u32; SLOT_WORDS];
        words[0] = entry_refused;
        slot.copy_from_slice(&words)?;
        let count = section.count();
        let mut params = Params::new();
        params
            .ptr(section.lo.device_ptr())
            .ptr(section.hi.device_ptr())
            .u32(count as u32)
            .u32(admitted_octaves)
            .ptr(slot.device_ptr());
        let function = self.function(symbol)?;
        let count32 = u32::try_from(count).map_err(|_| ResidentRefusal::GridAperture {
            operation: "census",
            rows: count,
            width: 1,
        })?;
        let grid =
            self.launch
                .grid_for(count32.max(1))
                .map_err(|_| ResidentRefusal::GridAperture {
                    operation: "census",
                    rows: count,
                    width: 1,
                })?;
        let stream = Stream::create()?;
        let mut pointers = params.pointers();
        function.launch_on_shared(
            &stream,
            Dim3::x(grid),
            Dim3::x(self.launch.block_x),
            0,
            &mut pointers,
        )?;
        stream.synchronize()?;
        slot.copy_to_slice(&mut words)?;
        {
            let mut census = self.census.borrow_mut();
            census.captured_launches += 1;
            census.synchronizations += 1;
            census.egress_receipt_octets += (SLOT_WORDS * 4) as u64;
        }
        Ok(SlotReading::of(&words))
    }
}
