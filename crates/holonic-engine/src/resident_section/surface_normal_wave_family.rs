use super::*;
impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_normal_wave_family_seed(
        &self,
        lane: &Lane<'_, 'c>,
        roots: usize,
        report: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let t = roots
            .checked_mul(8)
            .and_then(|v| v.checked_add(2))
            .ok_or_else(fail)?;
        let words = t
            .checked_mul(t)
            .and_then(|v| v.checked_add(t)?.checked_add(5))
            .ok_or_else(fail)?;
        if roots == 0 || t > u32::MAX as usize - 5 || !self.operative_shape(report, 1, words) {
            return Err(fail());
        }
        let mut p = Params::new();
        p.u32(roots as u32)
            .ptr(report.lo.device_ptr())
            .ptr(report.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_wave_family_seed",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-wave-family-seed",
        )
    }
}
