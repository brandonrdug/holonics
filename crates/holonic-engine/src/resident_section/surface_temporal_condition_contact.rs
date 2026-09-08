use super::*;

impl<'chart> ResidentSurface<'chart> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_temporal_condition_contact(
        &self,
        lane: &Lane<'_, 'chart>,
        x: crate::native_ecology::constitutive_fibre::ResidentConstitutiveCurrent<'_, 'chart>,
        y: crate::native_ecology::constitutive_fibre::ResidentConstitutiveCurrent<'_, 'chart>,
        source_extent: usize,
        response_complex: usize,
        prediction_from: usize,
        observed_from: usize,
        observed_extent: usize,
        observed_raw_extent: usize,
        prior: &ResidentSection<'chart>,
        prior_wide_at: usize,
        grain: u32,
        workspace: &ResidentSection<'chart>,
        report: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        self.validate_constitutive_current_view(x)?;
        self.validate_constitutive_current_view(y)?;
        let fail = || ResidentRefusal::Declaration {
            operation: "temporal-condition-contact",
            what: "incompatible point views, temporal support, prior ball or scratch aperture"
                .into(),
        };
        let x_complex = x
            .width
            .checked_div(2)
            .filter(|_| x.width % 2 == 0)
            .ok_or_else(fail)?;
        let y_complex = y
            .width
            .checked_div(2)
            .filter(|_| y.width % 2 == 0)
            .ok_or_else(fail)?;
        let dimension = response_complex.checked_mul(2).ok_or_else(fail)?;
        let prediction_extent = source_extent
            .checked_add(response_complex)
            .and_then(|n| n.checked_sub(1))
            .ok_or_else(fail)?;
        let matrix = dimension.checked_mul(dimension).ok_or_else(fail)?;
        let workspace_values = matrix
            .checked_mul(2)
            .and_then(|n| n.checked_add(dimension.checked_mul(6)?))
            .and_then(|n| n.checked_add(5))
            .ok_or_else(fail)?;
        let workspace_words =
            Self::constitutive_wide_workspace_words(workspace_values).ok_or_else(fail)?;
        let report_wide_values = dimension
            .checked_add(1)
            .and_then(|segment| segment.checked_mul(8))
            .and_then(|n| n.checked_add(matrix))
            .and_then(|n| n.checked_add(dimension))
            .and_then(|n| n.checked_add(3))
            .ok_or_else(fail)?;
        let report_width = report_wide_values.checked_mul(2).ok_or_else(fail)?;
        let prior_end = prior_wide_at
            .checked_add(dimension)
            .and_then(|n| n.checked_add(1))
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(fail)?;
        if source_extent == 0
            || response_complex == 0
            || observed_extent == 0
            || source_extent > x_complex
            || observed_extent > y_complex
            || observed_raw_extent == 0
            || observed_raw_extent > y_complex
            || observed_extent > observed_raw_extent
            || prediction_from
                .checked_add(observed_extent)
                .is_none_or(|n| n > prediction_extent)
            || observed_from
                .checked_add(observed_extent)
                .is_none_or(|n| n > observed_raw_extent)
            || grain == 0
            || grain > 120
            || x.offset > u32::MAX as usize
            || y.offset > u32::MAX as usize
            || x.denominator.is_some_and(|n| n > u32::MAX as usize)
            || y.denominator.is_some_and(|n| n > u32::MAX as usize)
            || x.disposition.is_some_and(|n| n > u32::MAX as usize)
            || y.disposition.is_some_and(|n| n > u32::MAX as usize)
            || x_complex > u32::MAX as usize
            || y_complex > u32::MAX as usize
            || source_extent > u32::MAX as usize
            || response_complex > u32::MAX as usize
            || prediction_from > u32::MAX as usize
            || observed_from > u32::MAX as usize
            || observed_extent > u32::MAX as usize
            || observed_raw_extent > u32::MAX as usize
            || prior.rows != 1
            || prior.grain.0 != 0
            || prior_end > prior.width
            || workspace.rows != 1
            || workspace.width != workspace_words
            || workspace.grain.0 != 0
            || report.rows != 1
            || report.width != report_width
            || report.grain.0 != 0
            || !std::ptr::eq(prior.surface, self)
            || !std::ptr::eq(workspace.surface, self)
            || !std::ptr::eq(report.surface, self)
        {
            return Err(fail());
        }

        let parameters = || {
            let mut params = Params::new();
            for current in [x, y] {
                params
                    .ptr(current.section.lo.device_ptr())
                    .ptr(current.section.hi.device_ptr())
                    .u32(current.offset as u32)
                    .u32(current.denominator.map_or(u32::MAX, |n| n as u32))
                    .u32(current.disposition.map_or(u32::MAX, |n| n as u32));
            }
            params
                .u32(x_complex as u32)
                .u32(y_complex as u32)
                .u32(source_extent as u32)
                .u32(response_complex as u32)
                .u32(prediction_from as u32)
                .u32(observed_from as u32)
                .u32(observed_extent as u32)
                .ptr(prior.lo.device_ptr())
                .ptr(prior.hi.device_ptr())
                .u32(prior_wide_at as u32)
                .u32((prior_wide_at + dimension) as u32)
                .u32(grain)
                .ptr(workspace.lo.device_ptr())
                .ptr(report.lo.device_ptr())
                .ptr(report.hi.device_ptr())
                .ptr(lane.slot)
                .ptr(lane.census)
                .ptr(lane.lineage)
                .u32(lane.lineage_count)
                .u32(observed_raw_extent as u32);
            params
        };
        let block = self.declaration.warp_size.max(1);
        let mut validate = parameters();
        self.record_blocks(
            lane,
            "section_temporal_condition_contact_validate",
            1,
            block,
            0,
            &mut validate,
            "temporal-condition-contact",
        )?;
        let mut gram = parameters();
        self.record_flat(
            lane,
            "section_temporal_condition_contact_gram",
            response_complex
                .checked_mul(response_complex)
                .ok_or_else(fail)?,
            &mut gram,
            "temporal-condition-contact",
        )?;
        let mut rhs = parameters();
        self.record_flat(
            lane,
            "section_temporal_condition_contact_rhs",
            response_complex,
            &mut rhs,
            "temporal-condition-contact",
        )?;
        let mut solve = parameters();
        self.record_blocks(
            lane,
            "section_temporal_condition_contact_solve",
            1,
            block,
            0,
            &mut solve,
            "temporal-condition-contact",
        )
    }
}
