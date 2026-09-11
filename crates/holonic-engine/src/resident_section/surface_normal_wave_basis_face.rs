use super::*;
use crate::native_ecology::constitutive_fibre::ResidentNormalEnclosureView;

impl<'c> ResidentSurface<'c> {
    /// Record the exact normal basis-face receiver. The current view is an exact packed
    /// `[Re(c_0), Im(c_0), ..., Re(c_(n-1)), Im(c_(n-1)), radius]` chart at `grain`;
    /// permutation is an exterior basis chart and is validated by the device kernel.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_normal_wave_basis_face(
        &self,
        lane: &Lane<'_, 'c>,
        current: ResidentNormalEnclosureView<'_, 'c>,
        permutation: &ResidentSection<'c>,
        n: usize,
        grain: u32,
        output: &ResidentSection<'c>,
        report: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let width = n.checked_mul(2).filter(|v| *v > 0).ok_or_else(fail)?;
        let output_width = n.checked_mul(2).ok_or_else(fail)?;
        if !(1..=120).contains(&grain)
            || current.width != width
            || current.offset > u32::MAX as usize
            || !self.operative_shape(permutation, 1, n)
            || !self.operative_shape(output, 1, output_width)
            || !self.operative_shape(report, 1, 10)
        {
            return Err(fail());
        }
        let needed = width
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        let end = current.offset.checked_add(needed).ok_or_else(fail)?;
        if width > u32::MAX as usize
            || output_width > u32::MAX as usize
            || current.offset % 2 != 0
            || end > u32::MAX as usize
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
            .u32(grain)
            .ptr(permutation.lo.device_ptr())
            .ptr(permutation.hi.device_ptr())
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(report.lo.device_ptr())
            .ptr(report.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_wave_basis_face",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-wave-basis-face",
        )
    }
}

impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_family_basis_face(
        &self,
        lane: &Lane<'_, 'c>,
        family: &ResidentSection<'c>,
        permutation: &ResidentSection<'c>,
        n: usize,
        scores: &ResidentSection<'c>,
        selection: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let fw = n
            .checked_mul(32)
            .and_then(|v| v.checked_add(8))
            .ok_or_else(fail)?;
        let sw = n
            .checked_mul(4)
            .and_then(|v| v.checked_add(2))
            .ok_or_else(fail)?;
        if n == 0
            || fw > u32::MAX as usize
            || !self.operative_shape(family, 1, fw)
            || !self.operative_shape(permutation, 1, n)
            || !self.operative_shape(scores, 1, sw)
            || !self.operative_shape(selection, 1, 8)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(family.lo.device_ptr())
            .ptr(family.hi.device_ptr())
            .ptr(permutation.lo.device_ptr())
            .ptr(permutation.hi.device_ptr())
            .u32(n as u32)
            .ptr(scores.lo.device_ptr())
            .ptr(scores.hi.device_ptr())
            .ptr(selection.lo.device_ptr())
            .ptr(selection.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_family_basis_face",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "family-basis-face",
        )
    }
}
