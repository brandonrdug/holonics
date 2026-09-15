use super::*;
use crate::native_ecology::constitutive_fibre::ResidentNormalEnclosureView;

impl<'c> ResidentSurface<'c> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_normal_wave_basis_sections(
        &self,
        lane: &Lane<'_, 'c>,
        current: ResidentNormalEnclosureView<'_, 'c>,
        permutation: &ResidentSection<'c>,
        n: usize,
        sections: usize,
        grain: u32,
        scores: &ResidentSection<'c>,
        report: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let width = n
            .checked_mul(2)
            .and_then(|v| v.checked_mul(sections))
            .filter(|v| *v > 0)
            .ok_or_else(fail)?;
        if !(1..=120).contains(&grain)
            || current.width != width
            || !self.operative_shape(permutation, 1, n)
            || !self.operative_shape(
                scores,
                1,
                n.checked_mul(sections)
                    .ok_or_else(fail)?
                    .checked_mul(2)
                    .ok_or_else(fail)?,
            )
            || !self.operative_shape(report, 1, sections.checked_mul(10).ok_or_else(fail)?)
        {
            return Err(fail());
        }
        let needed = width
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        let end = current.offset.checked_add(needed).ok_or_else(fail)?;
        if end > u32::MAX as usize
            || n > u32::MAX as usize
            || sections > u32::MAX as usize / 10
            || current.offset % 2 != 0
            || current.grain.0 != grain
            || current.section.grain.0 != 0
            || !std::ptr::eq(current.section.surface, self)
            || current
                .section
                .rows
                .checked_mul(current.section.width)
                .is_none_or(|size| end > size)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(current.section.lo.device_ptr())
            .ptr(current.section.hi.device_ptr())
            .u32(current.offset as u32)
            .u32(width as u32)
            .u32(n as u32)
            .u32(sections as u32)
            .u32(grain)
            .ptr(permutation.lo.device_ptr())
            .ptr(permutation.hi.device_ptr())
            .ptr(scores.lo.device_ptr())
            .ptr(scores.hi.device_ptr())
            .ptr(report.lo.device_ptr())
            .ptr(report.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_wave_basis_sections",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-wave-basis-sections",
        )
    }
}
