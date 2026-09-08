use super::*;

impl<'chart> ResidentSurface<'chart> {
    pub(crate) fn record_phase_enclosure_lift(
        &self,
        lane: &Lane<'_, 'chart>,
        input: crate::native_ecology::constitutive_fibre::ResidentConstitutiveCurrent<'_, 'chart>,
        raw_extent: usize,
        grain: u32,
        output: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        self.validate_constitutive_current_view(input)?;
        let fail = || ResidentRefusal::Declaration {
            operation: "phase-enclosure-lift",
            what: "incompatible exact current or dyadic output aperture".into(),
        };
        let complex = input.width / 2;
        let output_width = raw_extent
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(fail)?;
        if input.width % 2 != 0
            || !(1..=120).contains(&grain)
            || raw_extent == 0
            || raw_extent > complex
            || output.rows != 1
            || output.width != output_width
            || output.grain.0 != 0
            || !std::ptr::eq(output.surface, self)
            || input.offset > u32::MAX as usize
            || input.denominator.is_some_and(|n| n > u32::MAX as usize)
            || input.disposition.is_some_and(|n| n > u32::MAX as usize)
            || complex > u32::MAX as usize
            || raw_extent > u32::MAX as usize
            || complex > (u32::MAX as usize) / 2
            || raw_extent > (u32::MAX as usize) / 4
        {
            return Err(fail());
        }
        let mut params = Params::new();
        params
            .ptr(input.section.lo.device_ptr())
            .ptr(input.section.hi.device_ptr())
            .u32(input.offset as u32)
            .u32(input.denominator.map_or(u32::MAX, |n| n as u32))
            .u32(input.disposition.map_or(u32::MAX, |n| n as u32))
            .u32(complex as u32)
            .u32(raw_extent as u32)
            .u32(grain)
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_phase_enclosure_lift",
            1,
            self.declaration.warp_size.max(1),
            0,
            &mut params,
            "phase-enclosure-lift",
        )
    }

    pub(crate) fn record_phase_enclosed_convolution(
        &self,
        lane: &Lane<'_, 'chart>,
        source: crate::native_ecology::constitutive_fibre::ResidentConstitutiveCurrent<'_, 'chart>,
        source_raw_extent: usize,
        response: &ResidentSection<'chart>,
        response_wide_at: usize,
        response_raw_extent: usize,
        grain: u32,
        workspace: &ResidentSection<'chart>,
        output: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        self.validate_constitutive_current_view(source)?;
        let fail = || ResidentRefusal::Declaration {
            operation: "phase-enclosed-convolution",
            what: "incompatible exact source, enclosed response, or scratch aperture".into(),
        };
        let source_complex = source.width / 2;
        let output_extent = source_raw_extent
            .checked_add(response_raw_extent)
            .and_then(|n| n.checked_sub(1))
            .ok_or_else(fail)?;
        let response_values = response_raw_extent
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .ok_or_else(fail)?;
        let output_width = output_extent
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(fail)?;
        let workspace_values = source_raw_extent
            .checked_mul(4)
            .and_then(|n| n.checked_add(output_extent))
            .and_then(|n| n.checked_add(4))
            .ok_or_else(fail)?;
        if source.width % 2 != 0
            || source_raw_extent == 0
            || source_raw_extent > source_complex
            || response_raw_extent == 0
            || !(1..=120).contains(&grain)
            || response.width % 2 != 0
            || response.rows != 1
            || response.grain.0 != 0
            || response_wide_at
                .checked_add(response_values)
                .is_none_or(|n| n > response.width / 2)
            || output.rows != 1
            || output.width != output_width
            || output.grain.0 != 0
            || workspace.rows != 1
            || workspace.width
                != Self::constitutive_wide_workspace_words(workspace_values).ok_or_else(fail)?
            || workspace.grain.0 != 0
            || !std::ptr::eq(response.surface, self)
            || !std::ptr::eq(output.surface, self)
            || !std::ptr::eq(workspace.surface, self)
            || source.offset > u32::MAX as usize
            || source.denominator.is_some_and(|n| n > u32::MAX as usize)
            || source.disposition.is_some_and(|n| n > u32::MAX as usize)
            || response_wide_at > u32::MAX as usize
            || source_complex > u32::MAX as usize
            || source_raw_extent > u32::MAX as usize
            || response_raw_extent > u32::MAX as usize
            || source_complex > (u32::MAX as usize) / 2
            || source_raw_extent > (u32::MAX as usize) / 4
            || response_raw_extent > (u32::MAX as usize) / 4
            || output_extent > (u32::MAX as usize) / 2
        {
            return Err(fail());
        }
        let block = self.declaration.warp_size.max(1);
        let mut validation = Params::new();
        validation
            .ptr(source.section.lo.device_ptr())
            .ptr(source.section.hi.device_ptr())
            .u32(source.offset as u32)
            .u32(source.denominator.map_or(u32::MAX, |n| n as u32))
            .u32(source.disposition.map_or(u32::MAX, |n| n as u32))
            .ptr(response.lo.device_ptr())
            .ptr(response.hi.device_ptr())
            .u32(response_wide_at as u32)
            .u32(source_complex as u32)
            .u32(source_raw_extent as u32)
            .u32(response_raw_extent as u32)
            .u32(grain)
            .ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_phase_enclosed_convolution_validate",
            1,
            block,
            0,
            &mut validation,
            "phase-enclosed-convolution",
        )?;

        let mut lift = Params::new();
        lift.ptr(source.section.lo.device_ptr())
            .u32(source.offset as u32)
            .u32(source.denominator.map_or(u32::MAX, |n| n as u32))
            .u32(source_raw_extent as u32)
            .u32(response_raw_extent as u32)
            .u32(grain)
            .ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_phase_enclosed_convolution_lift",
            source_raw_extent * 2,
            &mut lift,
            "phase-enclosed-convolution",
        )?;

        let mut products = Params::new();
        products
            .ptr(response.lo.device_ptr())
            .u32(response_wide_at as u32)
            .u32(source_raw_extent as u32)
            .u32(response_raw_extent as u32)
            .u32(grain)
            .ptr(workspace.lo.device_ptr())
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_phase_enclosed_convolution_products",
            output_extent,
            &mut products,
            "phase-enclosed-convolution",
        )?;

        let mut finish = Params::new();
        finish
            .ptr(workspace.lo.device_ptr())
            .u32(source_raw_extent as u32)
            .u32(response_raw_extent as u32)
            .u32(grain)
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_phase_enclosed_convolution_finish",
            1,
            block,
            0,
            &mut finish,
            "phase-enclosed-convolution",
        )
    }

    pub(crate) fn record_phase_enclosed_difference(
        &self,
        lane: &Lane<'_, 'chart>,
        predicted: &ResidentSection<'chart>,
        predicted_wide_at: usize,
        predicted_raw_extent: usize,
        observed: crate::native_ecology::constitutive_fibre::ResidentConstitutiveCurrent<
            '_,
            'chart,
        >,
        observed_raw_extent: usize,
        predicted_from: usize,
        observed_from: usize,
        extent: usize,
        grain: u32,
        workspace: &ResidentSection<'chart>,
        output: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        self.validate_constitutive_current_view(observed)?;
        let fail = || ResidentRefusal::Declaration {
            operation: "phase-enclosed-difference",
            what: "incompatible enclosed prediction, exact observation, or scratch aperture".into(),
        };
        let observed_complex = observed.width / 2;
        let width = extent
            .checked_mul(2)
            .filter(|n| *n < u32::MAX as usize)
            .ok_or_else(fail)?;
        let response_values = predicted_raw_extent
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .ok_or_else(fail)?;
        if observed.width % 2 != 0
            || !(1..=120).contains(&grain)
            || predicted_raw_extent == 0
            || observed_raw_extent == 0
            || extent == 0
            || predicted.width % 2 != 0
            || predicted_from
                .checked_add(extent)
                .is_none_or(|n| n > predicted_raw_extent)
            || observed_from
                .checked_add(extent)
                .is_none_or(|n| n > observed_raw_extent)
            || predicted.rows != 1
            || predicted.grain.0 != 0
            || predicted_wide_at
                .checked_add(response_values)
                .is_none_or(|n| n > predicted.width / 2)
            || output.rows != 1
            || output.width
                != width
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(2))
                    .ok_or_else(fail)?
            || output.grain.0 != 0
            || workspace.rows != 1
            || workspace.width
                != Self::constitutive_wide_workspace_words(width + 2).ok_or_else(fail)?
            || workspace.grain.0 != 0
            || !std::ptr::eq(predicted.surface, self)
            || !std::ptr::eq(output.surface, self)
            || !std::ptr::eq(workspace.surface, self)
            || observed.offset > u32::MAX as usize
            || observed.denominator.is_some_and(|n| n > u32::MAX as usize)
            || observed.disposition.is_some_and(|n| n > u32::MAX as usize)
            || observed_complex > u32::MAX as usize
            || observed_raw_extent > u32::MAX as usize
            || observed_complex > (u32::MAX as usize) / 2
            || observed_raw_extent > (u32::MAX as usize) / 4
            || predicted_wide_at > u32::MAX as usize
            || predicted_raw_extent > u32::MAX as usize
            || predicted_raw_extent > (u32::MAX as usize) / 4
            || predicted_from > u32::MAX as usize
            || observed_from > u32::MAX as usize
            || extent > (u32::MAX as usize) / 4
        {
            return Err(fail());
        }
        let block = self.declaration.warp_size.max(1);
        let mut validation = Params::new();
        validation
            .ptr(predicted.lo.device_ptr())
            .ptr(predicted.hi.device_ptr())
            .u32(predicted_wide_at as u32)
            .u32(predicted_raw_extent as u32)
            .ptr(observed.section.lo.device_ptr())
            .ptr(observed.section.hi.device_ptr())
            .u32(observed.offset as u32)
            .u32(observed.denominator.map_or(u32::MAX, |n| n as u32))
            .u32(observed.disposition.map_or(u32::MAX, |n| n as u32))
            .u32(observed_complex as u32)
            .u32(observed_raw_extent as u32)
            .u32(predicted_from as u32)
            .u32(observed_from as u32)
            .u32(extent as u32)
            .u32(grain)
            .ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_phase_enclosed_difference_validate",
            1,
            block,
            0,
            &mut validation,
            "phase-enclosed-difference",
        )?;

        let mut products = Params::new();
        products
            .ptr(predicted.lo.device_ptr())
            .u32(predicted_wide_at as u32)
            .ptr(observed.section.lo.device_ptr())
            .u32(observed.offset as u32)
            .u32(predicted_from as u32)
            .u32(observed_from as u32)
            .u32(extent as u32)
            .u32(grain)
            .ptr(workspace.lo.device_ptr())
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_phase_enclosed_difference_products",
            width,
            &mut products,
            "phase-enclosed-difference",
        )?;

        let mut finish = Params::new();
        finish
            .ptr(workspace.lo.device_ptr())
            .u32(extent as u32)
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_phase_enclosed_difference_finish",
            1,
            block,
            0,
            &mut finish,
            "phase-enclosed-difference",
        )
    }
}
