use super::*;

impl<'c> ResidentSurface<'c> {
    fn operative_shape(&self, s: &ResidentSection<'c>, rows: usize, width: usize) -> bool {
        s.rows == rows && s.width == width && s.grain.0 == 0 && std::ptr::eq(s.surface, self)
    }
    fn operative_error() -> ResidentRefusal {
        ResidentRefusal::Declaration {
            operation: "operative-contacts",
            what: "incompatible contact/current carrier".into(),
        }
    }
    pub(crate) fn record_operative_mount(
        &self,
        lane: &Lane<'_, 'c>,
        table: &ResidentSection<'c>,
        current: &ResidentSection<'c>,
        n: usize,
        count: usize,
        grain: u32,
        at: usize,
        map: &ResidentSection<'c>,
        b: &ResidentSection<'c>,
        bounds: &ResidentSection<'c>,
        scratch: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        let d = n.checked_mul(6).ok_or_else(fail)?;
        if n == 0
            || d > u32::MAX as usize
            || count > u32::MAX as usize
            || !(1..=120).contains(&grain)
            || !self.operative_shape(table, count.max(1), 7)
            || !self.operative_shape(current, 1, 12 * (d + 1))
            || !self.operative_shape(map, count.max(1), 2 * d)
            || !self.operative_shape(b, count.max(1), 4)
            || !self.operative_shape(bounds, 1, 4)
            || !self.operative_shape(scratch, count.max(1), 4 * d + 8)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(table.lo.device_ptr())
            .ptr(current.lo.device_ptr())
            .u32(n as u32)
            .u32(count as u32)
            .u32(grain)
            .u64(at as u64);
        for s in [map, b, bounds] {
            p.ptr(s.lo.device_ptr()).ptr(s.hi.device_ptr());
        }
        p.ptr(scratch.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_operative_mount",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "operative-contacts",
        )
    }
    pub(crate) fn record_operative_update(
        &self,
        lane: &Lane<'_, 'c>,
        d: usize,
        count: usize,
        grain: u32,
        old: [&ResidentSection<'c>; 3],
        delta: [&ResidentSection<'c>; 4],
        next: [&ResidentSection<'c>; 3],
        rounds: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        if d == 0
            || d % 2 != 0
            || d > u32::MAX as usize
            || count > u32::MAX as usize
            || !(1..=120).contains(&grain)
        {
            return Err(fail());
        }
        for v in [&old, &next] {
            if !self.operative_shape(v[0], count.max(1), 2 * d)
                || !self.operative_shape(v[1], count.max(1), 4)
                || !self.operative_shape(v[2], 1, 4)
            {
                return Err(fail());
            }
        }
        if !self.operative_shape(delta[0], 2, 2 * d)
            || !self.operative_shape(delta[1], 2, 4 * count.max(1))
            || !self.operative_shape(delta[2], count.max(1), 4)
            || !self.operative_shape(delta[3], 1, 4)
            || !self.operative_shape(rounds, count.max(1), 2)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for s in old.into_iter().chain(delta) {
            p.ptr(s.lo.device_ptr());
        }
        p.u32(d as u32).u32(count as u32).u32(grain);
        for s in next {
            p.ptr(s.lo.device_ptr()).ptr(s.hi.device_ptr());
        }
        p.ptr(rounds.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_operative_update",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "operative-contacts",
        )
    }
    pub(crate) fn record_operative_moments(
        &self,
        lane: &Lane<'_, 'c>,
        d: usize,
        count: usize,
        grain: u32,
        input: [&ResidentSection<'c>; 3],
        output: [&ResidentSection<'c>; 3],
        rounds: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        let m = d / 2;
        let square = m.checked_mul(m).ok_or_else(fail)?;
        if d == 0
            || d % 2 != 0
            || d > u32::MAX as usize
            || count > u32::MAX as usize
            || !(1..=120).contains(&grain)
            || !self.operative_shape(input[0], count.max(1), 2 * d)
            || !self.operative_shape(input[1], count.max(1), 4)
            || !self.operative_shape(input[2], 1, 4)
            || !self.operative_shape(output[0], 1, 4 * square)
            || !self.operative_shape(output[1], 1, 2 * d)
            || !self.operative_shape(output[2], 1, 8)
            || !self.operative_shape(rounds, 1, 2 * (square + m))
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for s in input {
            p.ptr(s.lo.device_ptr());
        }
        p.u32(d as u32).u32(count as u32).u32(grain);
        for s in output {
            p.ptr(s.lo.device_ptr()).ptr(s.hi.device_ptr());
        }
        p.ptr(rounds.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_operative_moments",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "operative-contacts",
        )
    }
}
