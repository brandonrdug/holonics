use super::*;

impl<'chart> ResidentSurface<'chart> {

    /// Terminal sign receiver on disjoint pairs of complex coordinates in a junction report.
    pub(crate) fn record_field_differential_receiver(
        &self, lane: &Lane<'_, 'chart>, report: &ResidentSection<'chart>,
        dimension: usize, mode: u32, first_complex: usize, pairs: usize,
        output: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "field-differential-receiver", what: "incompatible receiver chart".into(),
        };
        let words = dimension.checked_add(1)
            .and_then(|n| n.checked_mul(if mode == 1 { 4 } else { 12 })).ok_or_else(fail)?;
        if dimension == 0 || dimension % 2 != 0 || dimension > u32::MAX as usize
            || !(1..=2).contains(&mode) || !(1..=63).contains(&pairs)
            || first_complex.checked_add(2 * pairs).is_none_or(|end| end > dimension / 2)
            || report.rows != 1 || report.width != words || report.grain.0 != 0
            || output.rows != 1 || output.width != 4 || output.grain.0 != 0 {
            return Err(fail());
        }
        let mut params = Params::new();
        params.ptr(report.lo.device_ptr()).ptr(report.hi.device_ptr())
            .u32(dimension as u32).u32(mode).u32(first_complex as u32).u32(pairs as u32)
            .ptr(output.lo.device_ptr()).ptr(output.hi.device_ptr())
            .ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane, "section_field_differential_receiver", 1, self.launch.block_x,
            0, &mut params, "field-differential-receiver")
    }

    /// The same local relation/scattering construction over a complete independently addressed
    /// input field. Both departing branches are retained before receiver projection.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_constitutive_field(
        &self, lane: &Lane<'_, 'chart>, seed: &ResidentSection<'chart>,
        memory: &mut ResidentSection<'chart>, basis: &mut ResidentSection<'chart>,
        incoming: &ResidentSection<'chart>, origin: Option<&ResidentSection<'chart>>,
        frame: &ResidentSection<'chart>, origin_frame: Option<&ResidentSection<'chart>>,
        junction: Option<(&ResidentSection<'chart>, &ResidentSection<'chart>,
            &ResidentSection<'chart>, &ResidentSection<'chart>, &ResidentSection<'chart>, (u32, u32))>,
        occurrence: u64,
        output: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let fail = |what: &str| ResidentRefusal::Declaration {
            operation: "constitutive-field", what: what.into(),
        };
        let nodes = seed.rows;
        let width = nodes.checked_mul(6).filter(|v| *v <= u32::MAX as usize / 4)
            .ok_or_else(|| fail("field relation extent overflow"))?;
        let output_width = nodes.checked_mul(16).and_then(|v| v.checked_add(9))
            .ok_or_else(|| fail("field report extent overflow"))?;
        let matches = |s: &ResidentSection<'chart>, rows, columns|
            s.rows == rows && s.width == columns && s.grain.0 == 0;
        if nodes == 0 || !matches(seed, nodes, 5) || !matches(memory, nodes, 3)
            || !matches(basis, width, width) || !matches(incoming, nodes, 3)
            || !matches(frame, nodes, 3)
            || !matches(output, 1, output_width)
            || origin.is_some_and(|s| !matches(s, 1, output_width))
            || origin.is_some() != origin_frame.is_some()
            || origin_frame.is_some_and(|s| !matches(s, nodes, 3)) {
            return Err(fail("incompatible field, source or continuing relation"));
        }
        if let Some((covariance, held, next_covariance, next_report, workspace, (mode, grain))) = junction {
            if !(1..=3).contains(&mode) || (mode != 1 && !(1..=120).contains(&grain)) {
                return Err(fail("unadmitted paired junction representation"));
            }
            let matrix_width = width.checked_mul(width).and_then(|n| n.checked_add(1))
                .ok_or_else(|| fail("paired junction matrix extent overflow"))?;
            let scratch_words = width.checked_mul(width).and_then(|n| n.checked_add(if mode == 1 { 7 * width } else { 8 * width }))
                .and_then(|n| n.checked_mul(2)).ok_or_else(|| fail("paired junction scratch extent overflow"))?;
            if !matches(covariance, 1, matrix_width) || !matches(next_covariance, 1, matrix_width)
                || !matches(held, 1, if mode == 1 { 4 * (width+1) } else { 12 * (width+1) })
                || !matches(next_report, 1, held.width)
                || !matches(workspace, 1, scratch_words) {
                return Err(fail("incompatible paired junction charts"));
            }
        }
        let shared = nodes.checked_mul(24).and_then(|v| v.checked_mul(16))
            .and_then(|v| u32::try_from(v).ok())
            .filter(|v| *v <= self.declaration.max_sectiond_bytes)
            .ok_or_else(|| fail("field exact scratch exceeds the mounted aperture"))?;
        let mut params = Params::new();
        params.ptr(seed.lo.device_ptr()).ptr(memory.lo.device_ptr()).ptr(memory.hi.device_ptr())
            .ptr(basis.lo.device_ptr()).ptr(basis.hi.device_ptr()).ptr(incoming.lo.device_ptr())
            .ptr(origin.unwrap_or(incoming).lo.device_ptr()).ptr(frame.lo.device_ptr())
            .ptr(origin_frame.unwrap_or(frame).lo.device_ptr()).u32(nodes as u32)
            .u32(u32::from(origin.is_some())).u32(junction.map_or(0, |(_,_,_,_,_,(mode,_))| mode))
            .u32(junction.map_or(0, |(_,_,_,_,_,(_,grain))| grain)).u64(occurrence);
        if let Some((covariance, held, next_covariance, next_report, workspace, _)) = junction {
            params.ptr(covariance.lo.device_ptr()).ptr(held.lo.device_ptr())
                .ptr(next_covariance.lo.device_ptr()).ptr(next_covariance.hi.device_ptr())
                .ptr(next_report.lo.device_ptr()).ptr(next_report.hi.device_ptr()).ptr(workspace.lo.device_ptr());
        } else {
            for _ in 0..7 { params.ptr(0); }
        }
        params.ptr(output.lo.device_ptr()).ptr(output.hi.device_ptr())
            .ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane, "section_constitutive_field", 1, self.launch.block_x,
            shared, &mut params, "constitutive-field")
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_constitutive_field_rechart(
        &self, lane: &Lane<'_, 'chart>, seed: &ResidentSection<'chart>,
        memory: &ResidentSection<'chart>, frame: &ResidentSection<'chart>,
        basis: &ResidentSection<'chart>, change: &ResidentSection<'chart>,
        new_seed: &ResidentSection<'chart>, new_memory: &ResidentSection<'chart>,
        new_frame: &ResidentSection<'chart>, new_basis: &ResidentSection<'chart>,
        report: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let nodes = seed.rows;
        let width = nodes.checked_mul(6)
            .filter(|v| *v <= u32::MAX as usize / 4)
            .ok_or_else(|| ResidentRefusal::Declaration {
                operation: "constitutive-field-rechart",
                what: "field relation extent overflow".into(),
            })?;
        let matching = |s: &ResidentSection<'chart>, rows, columns|
            s.rows == rows && s.width == columns && s.grain.0 == 0;
        if nodes == 0
            || !matching(seed, nodes, 5)
            || !matching(memory, nodes, 3)
            || !matching(frame, nodes, 3)
            || !matching(change, nodes, 6)
            || !matching(basis, width, width)
            || !matching(new_seed, nodes, 5)
            || !matching(new_memory, nodes, 3)
            || !matching(new_frame, nodes, 3)
            || !matching(new_basis, width, width)
            || !matching(report, nodes, 9)
        {
            return Err(ResidentRefusal::Declaration {
                operation: "constitutive-field-rechart",
                what: "incompatible field phase, seed or relation charts".into(),
            });
        }
        let shared = width.checked_mul(16)
            .and_then(|v| u32::try_from(v).ok())
            .filter(|v| *v <= self.declaration.max_sectiond_bytes)
            .ok_or_else(|| ResidentRefusal::Declaration {
                operation: "constitutive-field-rechart",
                what: "exact field rechart scratch exceeds the mounted aperture".into(),
            })?;
        let mut params = Params::new();
        params.ptr(seed.lo.device_ptr()).ptr(memory.lo.device_ptr()).ptr(frame.lo.device_ptr())
            .ptr(basis.lo.device_ptr()).ptr(change.lo.device_ptr()).u32(nodes as u32)
            .ptr(new_seed.lo.device_ptr()).ptr(new_seed.hi.device_ptr())
            .ptr(new_memory.lo.device_ptr()).ptr(new_memory.hi.device_ptr())
            .ptr(new_frame.lo.device_ptr()).ptr(new_frame.hi.device_ptr())
            .ptr(new_basis.lo.device_ptr()).ptr(new_basis.hi.device_ptr())
            .ptr(report.lo.device_ptr()).ptr(report.hi.device_ptr())
            .ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane, "section_constitutive_field_rechart", 1, self.launch.block_x,
            shared, &mut params, "constitutive-field-rechart")
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_constitutive_rechart(&self,lane:&Lane<'_, 'chart>,
        seed:&ResidentSection<'chart>,memory:&ResidentSection<'chart>,frame:&ResidentSection<'chart>,
        basis:&ResidentSection<'chart>,change:&ResidentSection<'chart>,
        new_seed:&ResidentSection<'chart>,new_memory:&ResidentSection<'chart>,new_frame:&ResidentSection<'chart>,
        new_basis:&ResidentSection<'chart>,report:&ResidentSection<'chart>) -> Result<(),ResidentRefusal> {
        let nodes=seed.rows;
        let width=2*nodes+2;
        let matching=|s:&ResidentSection<'chart>,rows,columns| s.rows==rows && s.width==columns && s.grain.0==0;
        if !matching(seed,nodes,5) || !matching(memory,nodes,3) || !matching(frame,nodes,3)
            || !matching(basis,width,width) || !matching(change,nodes,6) || !matching(new_seed,nodes,5)
            || !matching(new_memory,nodes,3) || !matching(new_frame,nodes,3) || !matching(new_basis,width,width)
            || !matching(report,nodes,9) || nodes==0 {
            return Err(ResidentRefusal::Declaration { operation:"constitutive-rechart",what:"incompatible phase/seed/relation charts".into() });
        }
        let shared=width.checked_mul(16).and_then(|v|u32::try_from(v).ok())
            .filter(|v|*v<=self.declaration.max_sectiond_bytes).ok_or_else(||ResidentRefusal::Declaration {
                operation:"constitutive-rechart",what:"exact rechart scratch exceeds the mounted aperture".into() })?;
        let mut params=Params::new();
        params.ptr(seed.lo.device_ptr()).ptr(memory.lo.device_ptr()).ptr(frame.lo.device_ptr())
            .ptr(basis.lo.device_ptr()).ptr(change.lo.device_ptr()).u32(nodes as u32)
            .ptr(new_seed.lo.device_ptr()).ptr(new_seed.hi.device_ptr()).ptr(new_memory.lo.device_ptr()).ptr(new_memory.hi.device_ptr())
            .ptr(new_frame.lo.device_ptr()).ptr(new_frame.hi.device_ptr()).ptr(new_basis.lo.device_ptr()).ptr(new_basis.hi.device_ptr())
            .ptr(report.lo.device_ptr()).ptr(report.hi.device_ptr()).ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane,"section_constitutive_rechart",1,self.launch.block_x,shared,&mut params,"constitutive-rechart")
    }

    /// Joined exact wave-state / local-relation recurrence with one atomic native commit.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_constitutive_circulation(
        &self, lane: &Lane<'_, 'chart>, seed: &ResidentSection<'chart>,
        memory: &mut ResidentSection<'chart>, basis: &mut ResidentSection<'chart>,
        incoming: &ResidentSection<'chart>, origin: Option<&ResidentSection<'chart>>,
        frame: &ResidentSection<'chart>, origin_frame: Option<&ResidentSection<'chart>>,
        output: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let nodes = seed.rows;
        let width = nodes.checked_mul(2).and_then(|n| n.checked_add(2))
            .ok_or_else(|| ResidentRefusal::Declaration { operation: "constitutive-circulation",
                what: "local chart extent overflow".into() })?;
        if nodes == 0 || width > u32::MAX as usize / 4 || seed.width != 5
            || memory.rows != nodes || memory.width != 3 || basis.rows != width || basis.width != width
            || incoming.rows != 1 || incoming.width != 3 || output.rows != 1 || output.width != 6*nodes+13
            || origin.is_some_and(|s| s.rows != 1 || s.width != output.width || s.grain.0 != 0)
            || frame.rows != nodes || frame.width != 3 || frame.grain.0 != 0
            || origin.is_some() != origin_frame.is_some()
            || origin_frame.is_some_and(|s| s.rows != nodes || s.width != 3 || s.grain.0 != 0)
            || [seed.grain, memory.grain, basis.grain, incoming.grain, output.grain].iter().any(|g| g.0 != 0)
        {
            return Err(ResidentRefusal::Declaration { operation: "constitutive-circulation",
                what: "incompatible seed, current, retained source or state chart".into() });
        }
        let shared = (12*nodes+6).checked_mul(16).and_then(|n| u32::try_from(n).ok())
            .filter(|n| *n <= self.declaration.max_sectiond_bytes)
            .ok_or_else(|| ResidentRefusal::Declaration { operation: "constitutive-circulation",
                what: "local exact scratch exceeds the mounted per-block aperture".into() })?;
        let mut params = Params::new();
        params.ptr(seed.lo.device_ptr()).ptr(memory.lo.device_ptr()).ptr(memory.hi.device_ptr())
            .ptr(basis.lo.device_ptr()).ptr(basis.hi.device_ptr()).ptr(incoming.lo.device_ptr())
            .ptr(origin.unwrap_or(incoming).lo.device_ptr()).ptr(frame.lo.device_ptr())
            .ptr(origin_frame.unwrap_or(frame).lo.device_ptr()).u32(nodes as u32).u32(u32::from(origin.is_some()))
            .ptr(output.lo.device_ptr()).ptr(output.hi.device_ptr()).ptr(lane.slot).ptr(lane.census)
            .ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane, "section_constitutive_circulation", 1, self.launch.block_x,
            shared, &mut params, "constitutive-circulation")
    }

    /// One local rational-relation operation. The only continuing write is a fully checked new
    /// echelon row; its source/receiver hypotheses belong to `native_ecology::constitutive_fibre`.
    pub(crate) fn record_constitutive_fibre(
        &self,
        lane: &Lane<'_, 'chart>,
        basis: &mut ResidentSection<'chart>,
        input: &ResidentSection<'chart>,
        source_width: usize,
        paired: bool,
        output: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let width = basis.width;
        if source_width == 0 || source_width >= width || basis.rows != width
            || input.rows != 1 || input.width != width || output.rows != 1
            || output.width != width + 4 || width > u32::MAX as usize - 4
            || [basis.grain, input.grain, output.grain].iter().any(|g| g.0 != 0)
        {
            return Err(ResidentRefusal::Declaration { operation: "constitutive-fibre",
                what: "expected point integer local relation, joined current and rational return charts".into() });
        }
        let shared = width.checked_mul(32).and_then(|v| u32::try_from(v).ok())
            .ok_or_else(|| ResidentRefusal::Declaration { operation: "constitutive-fibre",
                what: "local exact scratch exceeds the apparatus chart".into() })?;
        if shared > self.declaration.max_sectiond_bytes {
            return Err(ResidentRefusal::Declaration { operation: "constitutive-fibre",
                what: "local exact scratch exceeds the mounted per-block shared-memory aperture".into() });
        }
        let mut params = Params::new();
        params.ptr(basis.lo.device_ptr()).ptr(basis.hi.device_ptr())
            .ptr(input.lo.device_ptr()).ptr(input.hi.device_ptr())
            .u32(source_width as u32).u32((width-source_width) as u32).u32(u32::from(paired))
            .ptr(output.lo.device_ptr()).ptr(output.hi.device_ptr())
            .ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane, "section_constitutive_fibre", 1, self.launch.block_x,
            shared, &mut params, "constitutive-fibre")
    }

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
    /// Finite Euclidean contact of two point observations, applied to a third interval section.
    /// Formal owner: `HolonicOrientedSiteTransport.PassiveContact.contact`. Rows are independent
    /// declared charts. This records its projected map, not a learned model binding, an inferred
    /// metric, or the lifted axis. A one-row founding section is broadcast immutably over later
    /// query rows; equal source/query rows retain row-paired behavior. Inputs remain owned by
    /// their caller as the reconstruction fibre.
    /// Non-point founding observations and unsupported arithmetic refuse on the device; no
    /// midpoint, learning gain, clipping or hidden wider ecology is substituted.
    pub fn record_passive_contact(
        &self,
        lane: &Lane<'_, 'chart>,
        source: &ResidentSection<'chart>,
        arrived: &ResidentSection<'chart>,
        query: &ResidentSection<'chart>,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        const OPERATION: &str = "passive-contact";
        if source.rows == 0 || query.rows == 0 || source.width == 0
            || (source.rows != 1 && source.rows != query.rows)
            || arrived.rows != source.rows || arrived.width != source.width
            || arrived.grain != source.grain
            || query.width != source.width || query.grain != source.grain
            || out.rows != query.rows || out.width != query.width
            || out.grain != query.grain
        {
            return Err(ResidentRefusal::Declaration {
                operation: OPERATION, what: "contact sections require one nonempty carrier chart".into(),
            });
        }
        let founding_rows = u32::try_from(source.rows).map_err(|_| ResidentRefusal::GridAperture {
            operation: OPERATION, rows: source.rows, width: source.width,
        })?;
        let rows = u32::try_from(query.rows).map_err(|_| ResidentRefusal::GridAperture {
            operation: OPERATION, rows: query.rows, width: query.width,
        })?;
        let width = u32::try_from(source.width).map_err(|_| ResidentRefusal::GridAperture {
            operation: OPERATION, rows: source.rows, width: source.width,
        })?;
        let mut params = Params::new();
        params.ptr(source.lo.device_ptr()).ptr(source.hi.device_ptr())
            .ptr(arrived.lo.device_ptr()).ptr(arrived.hi.device_ptr())
            .ptr(query.lo.device_ptr()).ptr(query.hi.device_ptr())
            .u32(rows).u32(width).u32(founding_rows)
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr())
            .ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane, "section_passive_contact", query.rows, self.launch.block_x,
            0, &mut params, OPERATION)
    }

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
