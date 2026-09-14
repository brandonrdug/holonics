use super::*;

impl<'chart> ResidentSurface<'chart> {
    pub(crate) fn record_field_current_source(
        &self,
        lane: &Lane<'_, 'chart>,
        current: &ResidentSection<'chart>,
        b: &ResidentSection<'chart>,
        bounds: &ResidentSection<'chart>,
        nodes: usize,
        count: usize,
        output: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "field-current-source",
            what: "incompatible resident outgoing/internal current enclosure".into(),
        };
        let d = nodes.checked_mul(6).ok_or_else(fail)?;
        let output_width = d
            .checked_add(count.checked_mul(2).ok_or_else(fail)?)
            .and_then(|n| n.checked_add(1))
            .ok_or_else(fail)?;
        if nodes == 0
            || d > u32::MAX as usize / 12 - 1
            || output_width > u32::MAX as usize / 2
            || count > u32::MAX as usize / 4
            || current.rows != 1
            || current.width != 12 * (d + 1)
            || b.rows != count.max(1)
            || b.width != 4
            || bounds.rows != 1
            || bounds.width != 4
            || output.rows != 1
            || output.width != 2 * output_width
            || [current, b, bounds, output].iter().any(|s| s.grain.0 != 0)
            || [current, b, bounds, output]
                .iter()
                .any(|s| !std::ptr::eq(s.surface, self))
        {
            return Err(fail());
        }
        let mut params = Params::new();
        params
            .ptr(current.lo.device_ptr())
            .ptr(current.hi.device_ptr())
            .ptr(b.lo.device_ptr())
            .ptr(b.hi.device_ptr())
            .ptr(bounds.lo.device_ptr())
            .ptr(bounds.hi.device_ptr())
            .u32(d as u32)
            .u32(count as u32)
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_current_source",
            1,
            self.declaration.warp_size.max(1),
            0,
            &mut params,
            "field-current-source",
        )
    }
}
