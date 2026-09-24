use super::*;

impl<'c> ResidentSurface<'c> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_operative_current_difference(
        &self, lane: &Lane<'_, 'c>, before: &ResidentSection<'c>, after: &ResidentSection<'c>,
        factors: &ResidentSection<'c>, before_count: usize, count: usize, prefix_count: usize, encode: bool,
        output: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let component_words=std::mem::size_of::<i128>()/std::mem::size_of::<i64>();
        let current_words=2*component_words; // real and imaginary
        if before_count>count || prefix_count>count || (encode && prefix_count!=count) || count>u32::MAX as usize
            || !self.operative_shape(before,before_count.max(1),current_words)
            || !self.operative_shape(after,count.max(1),current_words)
            || !self.operative_shape(factors,if encode {2}else{1},current_words*count.max(1))
            || !self.operative_shape(output,if encode {1}else{2},current_words*prefix_count.max(1)) {
            return Err(Self::operative_error());
        }
        let mut p=Params::new();
        p.ptr(before.lo.device_ptr()).ptr(after.lo.device_ptr()).ptr(factors.lo.device_ptr())
            .u32(before_count as u32).u32(count as u32).u32(prefix_count as u32).u32(u32::from(encode))
            .ptr(output.lo.device_ptr()).ptr(output.hi.device_ptr()).ptr(lane.slot)
            .ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane,"section_field_operative_current_difference",
            (2*prefix_count).max(1).div_ceil(self.launch.block_x as usize),self.launch.block_x,0,&mut p,
            "operative-current-difference")
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
        output: [&ResidentSection<'c>; 4],
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
            || !self.operative_shape(output[2], 1, 4)
            || !self.operative_shape(output[3], 1, 2 * (2 * d + 4 * k + 8))
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
