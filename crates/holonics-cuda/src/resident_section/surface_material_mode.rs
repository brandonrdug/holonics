use super::*;
impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_ball_differential(
        &self,
        lane: &Lane<'_, 'c>,
        report: &ResidentSection<'c>,
        offset: usize,
        dimension: usize,
        pairs: usize,
        output: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let words = dimension.checked_add(1).and_then(|n| n.checked_mul(2));
        if dimension == 0
            || dimension % 2 != 0
            || dimension > u32::MAX as usize
            || !(1..=63).contains(&pairs)
            || pairs > dimension / 4
            || offset % 2 != 0
            || words
                .and_then(|w| offset.checked_add(w))
                .is_none_or(|end| end > report.width)
            || report.rows != 1
            || output.rows != 1
            || output.width != 4
            || [report, output]
                .iter()
                .any(|s| s.grain.0 != 0 || !std::ptr::eq(s.surface, self))
        {
            return Err(ResidentRefusal::Declaration {
                operation: "ball-differential",
                what: "incompatible complete complex current ball".into(),
            });
        }
        let mut p = Params::new();
        p.ptr(report.lo.device_ptr() + 8 * offset as u64)
            .ptr(report.hi.device_ptr() + 8 * offset as u64)
            .u32(dimension as u32)
            .u32(5)
            .u32(0)
            .u32(pairs as u32)
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_differential_receiver",
            1,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "ball-differential",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_complete_material_mode(
        &self,
        lane: &Lane<'_, 'c>,
        state: &ResidentSection<'c>,
        source: &ResidentSection<'c>,
        refreshed: Option<&ResidentSection<'c>>,
        receiving: Option<&ResidentSection<'c>>,
        contact: &ResidentSection<'c>,
        mode: &ResidentSection<'c>,
        left_before: &ResidentSection<'c>,
        right_before: &ResidentSection<'c>,
        factors: &ResidentSection<'c>,
        count: usize,
        nodes: usize,
        grain: u32,
        left: usize,
        right: usize,
        source_at: usize,
        cut: usize,
        mode_cut: usize,
        output: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "complete-material-mode",
            what: "incompatible coefficient, mode or chronological source chart".into(),
        };
        let report = nodes
            .checked_mul(74)
            .and_then(|n| n.checked_add(44))
            .ok_or_else(fail)?;
        let state_words = nodes
            .checked_mul(nodes)
            .and_then(|n| n.checked_mul(60))
            .and_then(|n| n.checked_add(nodes.checked_mul(22)?))
            .and_then(|n| n.checked_add(12))
            .ok_or_else(fail)?;
        let prefix = nodes
            .checked_mul(6)
            .and_then(|n| n.checked_add(1))
            .and_then(|n| n.checked_mul(12))
            .ok_or_else(fail)?;
        let contact_words = nodes
            .checked_mul(12)
            .and_then(|n| n.checked_add(2))
            .ok_or_else(fail)?;
        let result_words = nodes
            .checked_mul(92)
            .and_then(|n| n.checked_add(32))
            .ok_or_else(fail)?;
        let shape = |s: &ResidentSection<'c>, rows, width| {
            s.rows == rows && s.width == width && s.grain.0 == 0 && std::ptr::eq(s.surface, self)
        };
        if nodes == 0
            || result_words > u32::MAX as usize
            || count > u32::MAX as usize
            || !(1..=120).contains(&grain)
            || left == right
            || source_at < left.max(right)
            || cut < source_at
            || mode_cut > cut
            || mode_cut < left.max(right)
            || !shape(state, 1, state_words)
            || !shape(source, 1, report)
            || !shape(contact, 1, contact_words)
            || !shape(mode, 1, 12)
            || !shape(left_before, 1, prefix)
            || !shape(right_before, 1, prefix)
            || !shape(factors, count.max(1), 4)
            || !shape(output, 1, result_words)
            || refreshed.is_some_and(|s| !shape(s, 1, 10 * nodes))
            || receiving.is_some_and(|s| !shape(s, 1, report))
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(state.lo.device_ptr())
            .ptr(source.lo.device_ptr())
            .ptr(refreshed.map_or(0, |s| s.lo.device_ptr()))
            .ptr(receiving.map_or(0, |s| s.lo.device_ptr()))
            .ptr(contact.lo.device_ptr())
            .ptr(mode.lo.device_ptr())
            .ptr(left_before.lo.device_ptr())
            .ptr(right_before.lo.device_ptr())
            .ptr(factors.lo.device_ptr())
            .u32(count as u32)
            .u32(nodes as u32)
            .u32(grain)
            .u64(left as u64)
            .u64(right as u64)
            .u64(source_at as u64)
            .u64(cut as u64)
            .u64(mode_cut as u64)
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_complete_material_mode",
            1,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "complete-material-mode",
        )
    }
    pub(crate) fn record_material_mode_unfold(
        &self,
        lane: &Lane<'_, 'c>,
        origin: &ResidentSection<'c>,
        nodes: usize,
        steps: u64,
        output: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        if nodes == 0
            || origin.rows != 1
            || origin.width != 92 * nodes + 32
            || output.rows != 1
            || output.width != 4 * nodes + 2
            || [origin, output]
                .iter()
                .any(|s| s.grain.0 != 0 || !std::ptr::eq(s.surface, self))
        {
            return Err(ResidentRefusal::Declaration {
                operation: "material-mode-unfold",
                what: "incompatible material-mode current".into(),
            });
        }
        let mut p = Params::new();
        p.ptr(origin.lo.device_ptr())
            .u32(nodes as u32)
            .u64(steps)
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_material_mode_unfold",
            1,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "material-mode-unfold",
        )
    }
}
