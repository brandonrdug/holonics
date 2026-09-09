use super::*;

impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_joined_operative_return_bounds(
        &self,
        lane: &Lane<'_, 'c>,
        ordinary: &ResidentSection<'c>,
        source: &ResidentSection<'c>,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        if [ordinary, source, out]
            .iter()
            .any(|s| !self.operative_shape(s, 1, 4))
        {
            return Err(Self::operative_error());
        }
        let mut p = Params::new();
        p.ptr(ordinary.lo.device_ptr())
            .ptr(source.lo.device_ptr())
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_operative_join_return_bounds",
            1,
            1,
            0,
            &mut p,
            "operative-map-source",
        )
    }
    pub(crate) fn record_operative_map_anchor(
        &self,
        lane: &Lane<'_, 'c>,
        anchor: &ResidentSection<'c>,
        births: &ResidentSection<'c>,
        base_count: usize,
        count: usize,
        d: usize,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        if d == 0
            || d % 2 != 0
            || d > u32::MAX as usize
            || count > u32::MAX as usize
            || base_count > count
            || !self.operative_shape(anchor, base_count.max(1), 2 * d)
            || !self.operative_shape(births, (count - base_count).max(1), 1)
            || !self.operative_shape(out, count.max(1), 2 * d)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(anchor.lo.device_ptr())
            .ptr(births.lo.device_ptr())
            .u32(base_count as u32)
            .u32(count as u32)
            .u32(d as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_operative_map_anchor",
            (2 * d * count.max(1)).div_ceil(self.launch.block_x as usize),
            self.launch.block_x,
            0,
            &mut p,
            "operative-map-source",
        )
    }

    pub(crate) fn record_operative_map_expression(
        &self,
        lane: &Lane<'_, 'c>,
        before: &ResidentSection<'c>,
        source: Option<(&ResidentSection<'c>, &ResidentSection<'c>, usize)>,
        births: &ResidentSection<'c>,
        ports: &ResidentSection<'c>,
        factors: &ResidentSection<'c>,
        count: usize,
        factor_count: usize,
        d: usize,
        grain: u32,
        out: &ResidentSection<'c>,
        scratch: &ResidentSection<'c>,
        rounds: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        let m = d / 2;
        let history_words = 2 * std::mem::size_of::<i128>() / std::mem::size_of::<i64>() + 1;
        if d == 0
            || d % 2 != 0
            || d > u32::MAX as usize
            || count > u32::MAX as usize
            || factor_count > count
            || !(1..=120).contains(&grain)
            || !self.operative_shape(before, count.max(1), 2 * d)
            || !self.operative_shape(out, count.max(1), 2 * d)
            || !self.operative_shape(ports, 2, 2 * d)
            || !self.operative_shape(factors, 2, 4 * factor_count.max(1))
            || !self.operative_shape(births, count.max(1), 2)
            || !self.operative_shape(scratch, m, 2 * history_words * count.max(1))
            || !self.operative_shape(rounds, 1, 2 * m)
            || source.is_some_and(|(map, h, k)| {
                k > factor_count
                    || map.rows < k.max(1)
                    || !self.operative_shape(map, map.rows, 2 * d)
                    || !self.operative_shape(h, k.max(1), 4)
            })
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(before.lo.device_ptr())
            .ptr(source.map_or(0, |v| v.0.lo.device_ptr()))
            .ptr(births.lo.device_ptr())
            .ptr(ports.lo.device_ptr())
            .ptr(factors.lo.device_ptr())
            .ptr(source.map_or(0, |v| v.1.lo.device_ptr()))
            .u32(count as u32)
            .u32(factor_count as u32)
            .u32(source.map_or(0, |v| v.2) as u32)
            .u32(d as u32)
            .u32(grain)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(scratch.lo.device_ptr())
            .ptr(rounds.lo.device_ptr())
            .ptr(rounds.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_operative_map_expression",
            m.div_ceil(self.launch.block_x as usize),
            self.launch.block_x,
            0,
            &mut p,
            "operative-map-source",
        )
    }

    pub(crate) fn record_operative_expression_current(
        &self,
        lane: &Lane<'_, 'c>,
        before: &ResidentSection<'c>,
        bounds: &ResidentSection<'c>,
        delta: Option<&ResidentSection<'c>>,
        delta_bounds: &ResidentSection<'c>,
        rounds: &ResidentSection<'c>,
        count: usize,
        ports: usize,
        exact: bool,
        out: &ResidentSection<'c>,
        out_bounds: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        if count > u32::MAX as usize
            || ports == 0
            || ports > u32::MAX as usize
            || !self.operative_shape(before, count.max(1), 4)
            || !self.operative_shape(bounds, 1, 4)
            || delta.is_some_and(|d| !self.operative_shape(d, count.max(1), 4))
            || !self.operative_shape(delta_bounds, 1, 4)
            || !self.operative_shape(rounds, 1, 2 * ports)
            || !self.operative_shape(out, count.max(1), 4)
            || !self.operative_shape(out_bounds, 1, 4)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(before.lo.device_ptr())
            .ptr(bounds.lo.device_ptr())
            .ptr(delta.map_or(0, |d| d.lo.device_ptr()))
            .ptr(delta_bounds.lo.device_ptr())
            .ptr(rounds.lo.device_ptr())
            .u32(count as u32)
            .u32(ports as u32)
            .u32(u32::from(exact))
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(out_bounds.lo.device_ptr())
            .ptr(out_bounds.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_operative_expression_current",
            (2 * count.max(1)).div_ceil(self.launch.block_x as usize),
            self.launch.block_x,
            0,
            &mut p,
            "operative-map-source",
        )
    }
}
