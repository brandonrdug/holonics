use super::*;
impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_normal_wave_source(
        &self,
        lane: &Lane<'_, 'c>,
        joint: &ResidentSection<'c>,
        roots: usize,
        source: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let joint_width = roots
            .checked_mul(8)
            .and_then(|n| n.checked_add(2))
            .ok_or_else(fail)?;
        let source_width = roots
            .checked_mul(12)
            .and_then(|n| n.checked_add(2))
            .ok_or_else(fail)?;
        if roots == 0
            || source_width > u32::MAX as usize
            || !self.operative_shape(joint, 1, joint_width)
            || !self.operative_shape(source, 1, source_width)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(joint.lo.device_ptr())
            .ptr(joint.hi.device_ptr())
            .u32(roots as u32)
            .ptr(source.lo.device_ptr())
            .ptr(source.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_wave_source",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-wave-source",
        )
    }
}
