use super::*;

impl<'c> ResidentSurface<'c> {
    fn pair_shapes(
        &self,
        rows: usize,
        neighbors: usize,
        grain: u32,
        beta: Dyadic,
        values: &[(&ResidentSection<'c>, usize, usize)],
        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        if rows == 0
            || rows > u32::MAX as usize
            || neighbors == 0
            || neighbors > u32::MAX as usize / 4
            || !(1..=120).contains(&grain)
            || beta.significand < 0
            || beta.exponent == i32::MIN
            || !self.operative_shape(flags, rows, SLOT_WORDS / 2)
            || values.iter().any(|(s, r, d)| {
                *r == 0
                    || *r > u32::MAX as usize
                    || *d == 0
                    || d % 2 != 0
                    || *d > u32::MAX as usize / 4
                    || !self.operative_shape(s, *r, 2 * (d + 1))
            })
        {
            return Err(ResidentRefusal::Declaration {
                operation: "pair-quadrance",
                what: "incompatible geometric/value chart, scale or carrier".into(),
            });
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_pair_logits(
        &self,
        lane: &Lane<'_, 'c>,
        query: &ResidentSection<'c>,
        neighbors: &ResidentSection<'c>,
        rows: usize,
        n: usize,
        dimensions: usize,
        grain: u32,
        beta: Dyadic,
        joint: bool,
        logits: &ResidentSection<'c>,
        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let population = rows.checked_mul(n).ok_or_else(Self::operative_error)?;
        let potentials = n.checked_mul(2).ok_or_else(Self::operative_error)?;
        self.pair_shapes(
            rows,
            n,
            grain,
            beta,
            &[
                (query, rows, dimensions),
                (neighbors, population, dimensions),
                (logits, rows, potentials),
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
            .u32(dimensions as u32)
            .u32(grain)
            .i64(beta.significand)
            .i32(beta.exponent)
            .u32(u32::from(joint))
            .ptr(logits.lo.device_ptr())
            .ptr(logits.hi.device_ptr())
            .ptr(flags.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_pair_quadrance_logits",
            rows,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "pair-quadrance-logits",
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_pair_adjoint(
        &self,
        lane: &Lane<'_, 'c>,
        query: &ResidentSection<'c>,
        neighbors: &ResidentSection<'c>,
        participation: &ResidentSection<'c>,
        h: &ResidentSection<'c>,
        gy: &ResidentSection<'c>,
        rows: usize,
        n: usize,
        dimensions: usize,
        components: usize,
        grain: u32,
        beta: Dyadic,
        joint: bool,
        dq: &ResidentSection<'c>,
        du: &ResidentSection<'c>,
        dv: &ResidentSection<'c>,
        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let population = rows.checked_mul(n).ok_or_else(Self::operative_error)?;
        let potentials = n.checked_mul(2).ok_or_else(Self::operative_error)?;
        self.pair_shapes(
            rows,
            n,
            grain,
            beta,
            &[
                (query, rows, dimensions),
                (neighbors, population, dimensions),
                (participation, rows, potentials),
                (h, rows, potentials),
                (gy, rows, components),
                (dq, rows, dimensions),
                (du, population, dimensions),
                (dv, population, components),
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
            .u32(dimensions as u32)
            .u32(components as u32)
            .u32(grain)
            .i64(beta.significand)
            .i32(beta.exponent)
            .u32(u32::from(joint))
            .ptr(dq.lo.device_ptr())
            .ptr(dq.hi.device_ptr())
            .ptr(du.lo.device_ptr())
            .ptr(du.hi.device_ptr())
            .ptr(dv.lo.device_ptr())
            .ptr(dv.hi.device_ptr())
            .ptr(flags.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_pair_quadrance_adjoint",
            rows,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "pair-quadrance-adjoint",
        )
    }
}
