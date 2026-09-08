use super::*;
impl<'c> ResidentSurface<'c> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_moment_source_current(
        &self,
        lane: &Lane<'_, 'c>,
        source: &ResidentSection<'c>,
        table: &ResidentSection<'c>,
        count: usize,
        weights: &ResidentSection<'c>,
        n: usize,
        grain: u32,
        output: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let shape = |s: &ResidentSection<'c>, rows, width| {
            s.rows == rows && s.width == width && s.grain.0 == 0 && std::ptr::eq(s.surface, self)
        };
        if n == 0
            || count == 0
            || count > u32::MAX as usize
            || !(1..=120).contains(&grain)
            || !shape(source, 1, 96 * n + 44)
            || !shape(table, count, 2)
            || !shape(weights, count + 1, 4)
            || !shape(output, 1, 30 * n)
        {
            return Err(ResidentRefusal::Declaration {
                operation: "moment-source-current",
                what: "incompatible moment source/factors".into(),
            });
        }
        let mut p = Params::new();
        p.ptr(source.lo.device_ptr())
            .ptr(table.lo.device_ptr())
            .u32(count as u32)
            .u32(n as u32)
            .u32(grain)
            .ptr(weights.lo.device_ptr())
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_moment_source_current",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "moment-source-current",
        )
    }
}
