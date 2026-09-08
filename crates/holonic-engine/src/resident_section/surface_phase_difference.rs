use super::*;

impl<'chart> ResidentSurface<'chart> {
    pub(crate) fn record_phase_difference(
        &self,
        lane: &Lane<'_, 'chart>,
        predicted: crate::native_ecology::constitutive_fibre::ResidentConstitutiveCurrent<
            '_,
            'chart,
        >,
        observed: crate::native_ecology::constitutive_fibre::ResidentConstitutiveCurrent<
            '_,
            'chart,
        >,
        predicted_extent: usize,
        observed_extent: usize,
        predicted_from: usize,
        observed_from: usize,
        extent: usize,
        workspace: &ResidentSection<'chart>,
        output: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        self.validate_constitutive_current_view(predicted)?;
        self.validate_constitutive_current_view(observed)?;
        let fail = || ResidentRefusal::Declaration {
            operation: "phase-difference",
            what: "incompatible timed rational current overlap or scratch aperture".into(),
        };
        let width = extent
            .checked_mul(2)
            .filter(|n| *n < u32::MAX as usize)
            .ok_or_else(fail)?;
        let predicted_complex = predicted.width / 2;
        let observed_complex = observed.width / 2;
        if predicted_extent == 0
            || observed_extent == 0
            || extent == 0
            || predicted.width % 2 != 0
            || observed.width % 2 != 0
            || predicted_extent > predicted_complex
            || observed_extent > observed_complex
            || predicted_from
                .checked_add(extent)
                .is_none_or(|n| n > predicted_extent)
            || observed_from
                .checked_add(extent)
                .is_none_or(|n| n > observed_extent)
            || output.rows != 1
            || output.width != width + 1
            || output.grain.0 != 0
            || !std::ptr::eq(output.surface, self)
            || workspace.rows != 1
            || workspace.grain.0 != 0
            || !std::ptr::eq(workspace.surface, self)
        {
            return Err(fail());
        }
        let workspace_words = width
            .checked_add(4)
            .and_then(Self::constitutive_wide_workspace_words)
            .ok_or_else(fail)?;
        if workspace.width != workspace_words
            || predicted.offset > u32::MAX as usize
            || observed.offset > u32::MAX as usize
            || predicted.denominator.is_some_and(|n| n > u32::MAX as usize)
            || observed.denominator.is_some_and(|n| n > u32::MAX as usize)
            || predicted.disposition.is_some_and(|n| n > u32::MAX as usize)
            || observed.disposition.is_some_and(|n| n > u32::MAX as usize)
            || predicted_complex > u32::MAX as usize
            || observed_complex > u32::MAX as usize
            || predicted_extent > u32::MAX as usize
            || observed_extent > u32::MAX as usize
            || predicted_from > u32::MAX as usize
            || observed_from > u32::MAX as usize
        {
            return Err(fail());
        }

        let mut validation = Params::new();
        validation
            .ptr(predicted.section.lo.device_ptr())
            .ptr(predicted.section.hi.device_ptr())
            .u32(predicted.offset as u32)
            .u32(predicted.denominator.map_or(u32::MAX, |n| n as u32))
            .u32(predicted.disposition.map_or(u32::MAX, |n| n as u32))
            .ptr(observed.section.lo.device_ptr())
            .ptr(observed.section.hi.device_ptr())
            .u32(observed.offset as u32)
            .u32(observed.denominator.map_or(u32::MAX, |n| n as u32))
            .u32(observed.disposition.map_or(u32::MAX, |n| n as u32))
            .u32(predicted_complex as u32)
            .u32(observed_complex as u32)
            .u32(predicted_extent as u32)
            .u32(observed_extent as u32)
            .u32(predicted_from as u32)
            .u32(observed_from as u32)
            .u32(extent as u32)
            .ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        let block = self.declaration.warp_size.max(1);
        self.record_blocks(
            lane,
            "section_phase_difference_validate",
            1,
            block,
            0,
            &mut validation,
            "phase-difference",
        )?;

        let mut products = Params::new();
        products
            .ptr(predicted.section.lo.device_ptr())
            .ptr(predicted.section.hi.device_ptr())
            .u32(predicted.offset as u32)
            .u32(predicted.denominator.map_or(u32::MAX, |n| n as u32))
            .u32(predicted.disposition.map_or(u32::MAX, |n| n as u32))
            .ptr(observed.section.lo.device_ptr())
            .ptr(observed.section.hi.device_ptr())
            .u32(observed.offset as u32)
            .u32(observed.denominator.map_or(u32::MAX, |n| n as u32))
            .u32(observed.disposition.map_or(u32::MAX, |n| n as u32))
            .u32(predicted_complex as u32)
            .u32(observed_complex as u32)
            .u32(predicted_extent as u32)
            .u32(observed_extent as u32)
            .u32(predicted_from as u32)
            .u32(observed_from as u32)
            .u32(extent as u32)
            .ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_phase_difference_products",
            width,
            &mut products,
            "phase-difference",
        )?;

        let mut normalize = Params::new();
        normalize
            .ptr(workspace.lo.device_ptr())
            .u32(width as u32)
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_phase_convolution_normalize",
            1,
            block,
            0,
            &mut normalize,
            "phase-difference",
        )?;

        let mut pack = Params::new();
        pack.ptr(workspace.lo.device_ptr())
            .u32(width as u32)
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_phase_convolution_pack",
            (width + 1).div_ceil(block as usize),
            block,
            0,
            &mut pack,
            "phase-difference",
        )
    }
}
