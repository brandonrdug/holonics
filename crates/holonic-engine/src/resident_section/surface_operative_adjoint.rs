use super::*;

impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_operative_extend_response(
        &self,
        lane: &Lane<'_, 'c>,
        input: &ResidentSection<'c>,
        old: usize,
        count: usize,
        out: &ResidentSection<'c>,
        db: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        if old > count
            || count > u32::MAX as usize / 8
            || !self.operative_shape(input, 2, 4 * old.max(1))
            || !self.operative_shape(out, 2, 4 * count.max(1))
            || !self.operative_shape(db, count.max(1), 4)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(input.lo.device_ptr())
            .u32(old as u32)
            .u32(count as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(db.lo.device_ptr())
            .ptr(db.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_operative_extend_response",
            (8 * count.max(1)).div_ceil(self.launch.block_x as usize),
            self.launch.block_x,
            0,
            &mut p,
            "operative-extend-response",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_operative_producing_map(
        &self,
        lane: &Lane<'_, 'c>,
        current: &ResidentSection<'c>,
        journal: &ResidentSection<'c>,
        returns: usize,
        d: usize,
        k: usize,
        grain: u32,
        output: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        if d == 0
            || d % 2 != 0
            || d > u32::MAX as usize
            || k > u32::MAX as usize
            || returns > u32::MAX as usize
            || !(1..=120).contains(&grain)
            || !self.operative_shape(journal, returns.max(1), 3)
            || current.width != 2 * d
            || current.rows < k.max(1)
            || current.grain.0 != 0
            || !self.operative_shape(output, k.max(1), 2 * d)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(current.lo.device_ptr())
            .ptr(journal.lo.device_ptr())
            .u32(returns as u32)
            .u32(d as u32)
            .u32(k as u32)
            .u32(grain)
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_operative_producing_map",
            (k * d / 2).max(1).div_ceil(self.launch.block_x as usize),
            self.launch.block_x,
            0,
            &mut p,
            "operative-producing-map",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_operative_material_adjoint(
        &self,
        lane: &Lane<'_, 'c>,
        input: [&ResidentSection<'c>; 7],
        n: usize,
        k: usize,
        grain: u32,
        output: [&ResidentSection<'c>; 5],
        workspace: &ResidentSection<'c>,
        dots: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        let d = n.checked_mul(6).ok_or_else(fail)?;
        let m = d / 2;
        if n == 0
            || d > u32::MAX as usize
            || k > u32::MAX as usize
            || !(1..=120).contains(&grain)
            || !self.operative_shape(input[0], k.max(1), 2 * d)
            || !self.operative_shape(input[1], k.max(1), 4)
            || !self.operative_shape(input[2], 1, 4)
            || !self.operative_shape(input[3], 1, 4 * m * m)
            || !self.operative_shape(input[4], 1, 8)
            || !self.operative_shape(input[5], 1, 12 * (d + 1))
            || !self.operative_shape(input[6], 1, 4 * (10 * n + 2 * k))
            || !self.operative_shape(output[0], 2, 2 * d)
            || !self.operative_shape(output[1], 2, 4 * k.max(1))
            || !self.operative_shape(output[2], k.max(1), 4)
            || !self.operative_shape(output[3], 1, 4)
            || !self.operative_shape(output[4], 1, 2 * (2 * d + 4 * k + 8))
            || !self.operative_shape(workspace, 1, 2 * (d * d + 3 * d + 4 * k + 2))
            || !self.operative_shape(dots, k.max(1), 10)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for v in input {
            p.ptr(v.lo.device_ptr());
        }
        p.u32(n as u32).u32(k as u32).u32(grain);
        for v in output {
            p.ptr(v.lo.device_ptr()).ptr(v.hi.device_ptr());
        }
        p.ptr(workspace.lo.device_ptr())
            .ptr(dots.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_operative_material_adjoint",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "operative-material-adjoint",
        )
    }
}
