use super::*;
impl<'c> ResidentSurface<'c> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_linear_material_pullback(
        &self,
        lane: &Lane<'_, 'c>,
        state: &ResidentSection<'c>,
        journal: &ResidentSection<'c>,
        source: &ResidentSection<'c>,
        returned: &ResidentSection<'c>,
        nodes: usize,
        targets: usize,
        contacts: usize,
        later: usize,
        grain: u32,
        metric: u32,
        output: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "linear-material-pullback",
            what: "incompatible operator/source chart".into(),
        };
        let coefficients = nodes
            .checked_mul(targets)
            .and_then(|v| v.checked_mul(12))
            .and_then(|v| v.checked_add(2))
            .ok_or_else(fail)?;
        let coordinates = nodes
            .checked_mul(10)
            .and_then(|v| contacts.checked_mul(2).and_then(|k| v.checked_add(k)))
            .ok_or_else(fail)?;
        if nodes == 0
            || targets == 0
            || coefficients > u32::MAX as usize
            || coordinates > u32::MAX as usize / 4
            || later >= u32::MAX as usize
            || !(1..=120).contains(&grain)
            || metric > 2
            || state.rows != 1
            || state.width != coefficients
            || journal.rows != later.max(1)
            || journal.width != 2
            || source.rows != 1
            || source.width != 24 * targets + 12 * nodes + 24
            || returned.rows != 1
            || returned.width != (if metric == 2 { 8 } else { 20 }) * targets
            || output.rows != 1
            || output.width != 4 * coordinates
            || [state, journal, source, returned, output]
                .iter()
                .any(|s| s.grain.0 != 0)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(state.lo.device_ptr())
            .ptr(journal.lo.device_ptr())
            .ptr(source.lo.device_ptr())
            .ptr(returned.lo.device_ptr())
            .u32(nodes as u32)
            .u32(targets as u32)
            .u32(contacts as u32)
            .u32(later as u32)
            .u32(grain)
            .u32(metric)
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        let block = self.declaration.warp_size.max(1);
        self.record_blocks(
            lane,
            "section_field_linear_material_pullback",
            coordinates.div_ceil(block as usize),
            block,
            0,
            &mut p,
            "linear-material-pullback",
        )
    }
}
