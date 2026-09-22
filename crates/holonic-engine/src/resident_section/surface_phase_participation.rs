use super::*;

impl<'c> ResidentSurface<'c> {
    fn phase_shapes(
        &self,
        rows: usize,
        n: usize,
        grain: u32,
        values: &[(&ResidentSection<'c>, usize, usize)],
        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        if rows == 0
            || rows > u32::MAX as usize
            || n == 0
            || n > u32::MAX as usize / 4
            || !(1..=120).contains(&grain)
            || !self.operative_shape(flags, rows, SLOT_WORDS / 2)
            || values.iter().any(|(v, r, d)| {
                *d == 0
                    || d % 2 != 0
                    || *d > u32::MAX as usize / 4
                    || *r > u32::MAX as usize
                    || !self.operative_shape(v, *r, 2 * (d + 1))
            })
        {
            return Err(Self::operative_error());
        }
        Ok(())
    }
    pub(crate) fn collect_phase_status(
        &self,
        lane: &Lane<'_, 'c>,
        flags: &ResidentSection<'c>,
        rows: usize,
    ) -> Result<(), ResidentRefusal> {
        let mut p = Params::new();
        p.ptr(flags.lo.device_ptr()).u32(rows as u32).ptr(lane.slot);
        self.record_blocks(
            lane,
            "section_enclosure_collect_row_status",
            rows,
            1,
            0,
            &mut p,
            "phase-row-status",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_phase_participation(
        &self,
        lane: &Lane<'_, 'c>,
        query: &ResidentSection<'c>,
        neighbors: &ResidentSection<'c>,
        rows: usize,
        n: usize,
        components: usize,
        grain: u32,
        beta: Dyadic,
        logits: &ResidentSection<'c>,

        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "phase-logits",
            what: "incompatible phase chart".into(),
        };
        let qw = components
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        let lw = n
            .checked_mul(2)
            .and_then(|v| v.checked_add(1))
            .ok_or_else(fail)?;
        if rows == 0
            || n == 0
            || components == 0
            || components % 2 != 0
            || query.rows != rows
            || query.width != qw
            || neighbors.rows != rows.checked_mul(n).ok_or_else(fail)?
            || neighbors.width != qw
            || logits.rows != rows
            || logits.width != lw * 2
            || flags.rows != rows
            || flags.width != SLOT_WORDS / 2
            || [query, neighbors, logits, flags]
                .iter()
                .any(|s| s.grain.0 != 0 || !std::ptr::eq(s.surface, self))
        {
            return Err(fail());
        }
        self.phase_shapes(
            rows,
            n,
            grain,
            &[
                (query, rows, components),
                (
                    neighbors,
                    rows.checked_mul(n).ok_or_else(Self::operative_error)?,
                    components,
                ),
                (
                    logits,
                    rows,
                    n.checked_mul(2).ok_or_else(Self::operative_error)?,
                ),
            ],
            flags,
        )?;
        let mut p = Params::new();
        p.ptr(query.lo.device_ptr())
            .ptr(query.hi.device_ptr())
            .ptr(neighbors.lo.device_ptr())
            .ptr(neighbors.hi.device_ptr())
            .u32(rows as u32)
            .u32(n as u32)
            .u32(components as u32)
            .u32(grain)
            .i64(beta.significand)
            .i32(beta.exponent)
            .ptr(logits.lo.device_ptr())
            .ptr(logits.hi.device_ptr())
            .ptr(flags.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_phase_participation",
            rows,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "phase-logits",
        )
    }
    pub(crate) fn record_phase_weighted(
        &self,
        lane: &Lane<'_, 'c>,
        neighbors: &ResidentSection<'c>,

        participation: &ResidentSection<'c>,

        rows: usize,
        n: usize,
        components: usize,
        grain: u32,
        joint: bool,
        output: &ResidentSection<'c>,

        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        self.phase_shapes(
            rows,
            n,
            grain,
            &[
                (
                    neighbors,
                    rows.checked_mul(n).ok_or_else(Self::operative_error)?,
                    components,
                ),
                (
                    participation,
                    rows,
                    n.checked_mul(2).ok_or_else(Self::operative_error)?,
                ),
                (output, rows, components),
            ],
            flags,
        )?;
        let mut p = Params::new();
        p.ptr(neighbors.lo.device_ptr())
            .ptr(neighbors.hi.device_ptr())
            .ptr(participation.lo.device_ptr())
            .ptr(participation.hi.device_ptr())
            .u32(rows as u32)
            .u32(n as u32)
            .u32(components as u32)
            .u32(grain)
            .u32(u32::from(joint))
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(flags.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_phase_participation_weighted",
            rows,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "phase-weighted",
        )
    }
    pub(crate) fn record_phase_terms(
        &self,
        lane: &Lane<'_, 'c>,
        neighbors: &ResidentSection<'c>,

        gy: &ResidentSection<'c>,

        gp: Option<&ResidentSection<'c>>,

        rows: usize,
        n: usize,
        components: usize,
        grain: u32,
        joint: bool,
        terms: &ResidentSection<'c>,

        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        self.phase_shapes(
            rows,
            n,
            grain,
            &[
                (
                    neighbors,
                    rows.checked_mul(n).ok_or_else(Self::operative_error)?,
                    components,
                ),
                (gy, rows, components),
                (
                    terms,
                    rows,
                    n.checked_mul(2).ok_or_else(Self::operative_error)?,
                ),
            ],
            flags,
        )?;
        if let Some(gp) = gp {
            self.phase_shapes(rows, n, grain, &[(gp, rows, n * 2)], flags)?;
        }
        let mut p = Params::new();
        p.ptr(neighbors.lo.device_ptr())
            .ptr(neighbors.hi.device_ptr())
            .ptr(gy.lo.device_ptr())
            .ptr(gy.hi.device_ptr())
            .ptr(gp.map_or(0, |s| s.lo.device_ptr()))
            .ptr(gp.map_or(0, |s| s.hi.device_ptr()))
            .u32(rows as u32)
            .u32(n as u32)
            .u32(components as u32)
            .u32(grain)
            .u32(u32::from(joint))
            .ptr(terms.lo.device_ptr())
            .ptr(terms.hi.device_ptr())
            .ptr(flags.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_phase_participation_terms",
            rows,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "phase-terms",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_phase_adjoint(
        &self,
        lane: &Lane<'_, 'c>,
        query: &ResidentSection<'c>,

        neighbors: &ResidentSection<'c>,

        participation: &ResidentSection<'c>,

        h: &ResidentSection<'c>,

        gy: &ResidentSection<'c>,

        rows: usize,
        n: usize,
        components: usize,
        grain: u32,
        beta: Dyadic,
        source: &ResidentSection<'c>,

        returned: &ResidentSection<'c>,

        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        self.phase_shapes(
            rows,
            n,
            grain,
            &[
                (query, rows, components),
                (
                    neighbors,
                    rows.checked_mul(n).ok_or_else(Self::operative_error)?,
                    components,
                ),
                (
                    participation,
                    rows,
                    n.checked_mul(2).ok_or_else(Self::operative_error)?,
                ),
                (h, rows, n.checked_mul(2).ok_or_else(Self::operative_error)?),
                (gy, rows, components),
                (source, rows, components),
                (
                    returned,
                    rows.checked_mul(n).ok_or_else(Self::operative_error)?,
                    components,
                ),
            ],
            flags,
        )?;
        let mut p = Params::new();
        p.ptr(query.lo.device_ptr())
            .ptr(query.hi.device_ptr())
            .ptr(neighbors.lo.device_ptr())
            .ptr(neighbors.hi.device_ptr())
            .ptr(participation.lo.device_ptr())
            .ptr(participation.hi.device_ptr())
            .ptr(h.lo.device_ptr())
            .ptr(h.hi.device_ptr())
            .ptr(gy.lo.device_ptr())
            .ptr(gy.hi.device_ptr())
            .u32(rows as u32)
            .u32(n as u32)
            .u32(components as u32)
            .u32(grain)
            .i64(beta.significand)
            .i32(beta.exponent)
            .ptr(source.lo.device_ptr())
            .ptr(source.hi.device_ptr())
            .ptr(returned.lo.device_ptr())
            .ptr(returned.hi.device_ptr())
            .ptr(flags.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_phase_participation_adjoint",
            rows,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "phase-adjoint",
        )
    }

    /// `phi_j = (beta/2) Im <q|u_j>`: the phase face of the complex pair potential.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_phase_participation_phase(
        &self,
        lane: &Lane<'_, 'c>,
        query: &ResidentSection<'c>,
        neighbors: &ResidentSection<'c>,
        rows: usize,
        n: usize,
        components: usize,
        grain: u32,
        beta: Dyadic,
        phase: &ResidentSection<'c>,
        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        if components % 2 != 0 || beta.exponent == i32::MIN {
            return Err(Self::operative_error());
        }
        self.phase_shapes(
            rows,
            n,
            grain,
            &[
                (query, rows, components),
                (
                    neighbors,
                    rows.checked_mul(n).ok_or_else(Self::operative_error)?,
                    components,
                ),
                (
                    phase,
                    rows,
                    n.checked_mul(2).ok_or_else(Self::operative_error)?,
                ),
            ],
            flags,
        )?;
        let mut p = Params::new();
        p.ptr(query.lo.device_ptr())
            .ptr(query.hi.device_ptr())
            .ptr(neighbors.lo.device_ptr())
            .ptr(neighbors.hi.device_ptr())
            .u32(rows as u32)
            .u32(n as u32)
            .u32(components as u32)
            .u32(grain)
            .i64(beta.significand)
            .i32(beta.exponent)
            .ptr(phase.lo.device_ptr())
            .ptr(phase.hi.device_ptr())
            .ptr(flags.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_phase_participation_phase",
            rows,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "phase-face",
        )
    }
    /// The adjoint of the phase face for a covector on it; additive to the magnitude adjoint.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_phase_participation_phase_adjoint(
        &self,
        lane: &Lane<'_, 'c>,
        query: &ResidentSection<'c>,
        neighbors: &ResidentSection<'c>,
        gphi: &ResidentSection<'c>,
        rows: usize,
        n: usize,
        components: usize,
        grain: u32,
        beta: Dyadic,
        source: &ResidentSection<'c>,
        returned: &ResidentSection<'c>,
        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        if components % 2 != 0 || beta.exponent == i32::MIN {
            return Err(Self::operative_error());
        }
        let many = rows.checked_mul(n).ok_or_else(Self::operative_error)?;
        self.phase_shapes(
            rows,
            n,
            grain,
            &[
                (query, rows, components),
                (neighbors, many, components),
                (
                    gphi,
                    rows,
                    n.checked_mul(2).ok_or_else(Self::operative_error)?,
                ),
                (source, rows, components),
                (returned, many, components),
            ],
            flags,
        )?;
        let mut p = Params::new();
        p.ptr(query.lo.device_ptr())
            .ptr(query.hi.device_ptr())
            .ptr(neighbors.lo.device_ptr())
            .ptr(neighbors.hi.device_ptr())
            .ptr(gphi.lo.device_ptr())
            .ptr(gphi.hi.device_ptr())
            .u32(rows as u32)
            .u32(n as u32)
            .u32(components as u32)
            .u32(grain)
            .i64(beta.significand)
            .i32(beta.exponent)
            .ptr(source.lo.device_ptr())
            .ptr(source.hi.device_ptr())
            .ptr(returned.lo.device_ptr())
            .ptr(returned.hi.device_ptr())
            .ptr(flags.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_phase_participation_phase_adjoint",
            rows,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "phase-face-adjoint",
        )
    }
}
