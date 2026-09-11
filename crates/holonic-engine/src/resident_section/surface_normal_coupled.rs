use super::*;
use crate::native_ecology::constitutive_fibre::ResidentConstitutiveCurrent;
impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_normal_family_admit(
        &self,
        lane: &Lane<'_, 'c>,
        report: &ResidentSection<'c>,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        if report.rows != 1
            || report.width < 2
            || report.grain.0 != 0
            || !std::ptr::eq(report.surface, self)
            || !self.operative_shape(out, 1, 1)
        {
            return Err(Self::operative_error());
        }
        let mut p = Params::new();
        p.ptr(report.lo.device_ptr())
            .ptr(report.hi.device_ptr())
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_family_admit",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-family-admit",
        )
    }
    pub(crate) fn record_normal_source_plane(
        &self,
        lane: &Lane<'_, 'c>,
        source: ResidentConstitutiveCurrent<'_, 'c>,
        n: usize,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        self.validate_constitutive_current_view(source)?;
        if n == 0
            || n.checked_mul(6) != Some(source.width)
            || source.width > u32::MAX as usize
            || !self.operative_shape(out, 1, 1)
        {
            return Err(Self::operative_error());
        }
        let mut p = Params::new();
        p.ptr(source.section.lo.device_ptr())
            .ptr(source.section.hi.device_ptr())
            .u32(source.offset as u32)
            .u32(source.denominator.map_or(u32::MAX, |v| v as u32))
            .u32(source.disposition.map_or(u32::MAX, |v| v as u32))
            .u32(n as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_source_plane",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-source-plane",
        )
    }
}
