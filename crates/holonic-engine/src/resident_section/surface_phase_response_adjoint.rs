use super::*;

impl<'chart> ResidentSurface<'chart> {
    pub(crate) fn record_phase_response_adjoint(
        &self,
        lane: &Lane<'_, 'chart>,
        source: crate::native_ecology::constitutive_fibre::ResidentConstitutiveCurrent<'_, 'chart>,
        residual: crate::native_ecology::constitutive_fibre::ResidentConstitutiveCurrent<
            '_,
            'chart,
        >,
        source_raw: usize,
        response_raw: usize,
        predicted_from: usize,
        residual_raw: usize,
        workspace: &ResidentSection<'chart>,
        output: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        self.validate_constitutive_current_view(source)?;
        self.validate_constitutive_current_view(residual)?;
        let fail = || ResidentRefusal::Declaration {
            operation: "phase-response-adjoint",
            what: "incompatible response support or scratch aperture".into(),
        };
        let width = response_raw
            .checked_mul(2)
            .filter(|n| *n < u32::MAX as usize)
            .ok_or_else(fail)?;
        let source_complex = source.width / 2;
        let residual_complex = residual.width / 2;
        let convolution_extent = source_raw
            .checked_add(response_raw)
            .and_then(|n| n.checked_sub(1))
            .ok_or_else(fail)?;
        if source_raw == 0
            || response_raw == 0
            || residual_raw == 0
            || source.width % 2 != 0
            || residual.width % 2 != 0
            || source_raw > source_complex
            || residual_raw > residual_complex
            || predicted_from
                .checked_add(residual_raw)
                .is_none_or(|n| n > convolution_extent)
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
            .checked_add(2)
            .and_then(Self::constitutive_wide_workspace_words)
            .ok_or_else(fail)?;
        if workspace.width != workspace_words
            || source.offset > u32::MAX as usize
            || residual.offset > u32::MAX as usize
            || source.denominator.is_some_and(|n| n > u32::MAX as usize)
            || residual.denominator.is_some_and(|n| n > u32::MAX as usize)
            || source.disposition.is_some_and(|n| n > u32::MAX as usize)
            || residual.disposition.is_some_and(|n| n > u32::MAX as usize)
            || source_complex > u32::MAX as usize
            || residual_complex > u32::MAX as usize
            || source_raw > u32::MAX as usize
            || response_raw > u32::MAX as usize
            || predicted_from > u32::MAX as usize
            || residual_raw > u32::MAX as usize
        {
            return Err(fail());
        }

        let mut validation = Params::new();
        validation
            .ptr(source.section.lo.device_ptr())
            .ptr(source.section.hi.device_ptr())
            .u32(source.offset as u32)
            .u32(source.denominator.map_or(u32::MAX, |n| n as u32))
            .u32(source.disposition.map_or(u32::MAX, |n| n as u32))
            .ptr(residual.section.lo.device_ptr())
            .ptr(residual.section.hi.device_ptr())
            .u32(residual.offset as u32)
            .u32(residual.denominator.map_or(u32::MAX, |n| n as u32))
            .u32(residual.disposition.map_or(u32::MAX, |n| n as u32))
            .u32(source_complex as u32)
            .u32(residual_complex as u32)
            .u32(source_raw as u32)
            .u32(response_raw as u32)
            .u32(predicted_from as u32)
            .u32(residual_raw as u32)
            .ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        let block = self.declaration.warp_size.max(1);
        self.record_blocks(
            lane,
            "section_phase_response_adjoint_validate",
            1,
            block,
            0,
            &mut validation,
            "phase-response-adjoint",
        )?;

        let mut products = Params::new();
        products
            .ptr(source.section.lo.device_ptr())
            .ptr(source.section.hi.device_ptr())
            .u32(source.offset as u32)
            .u32(source.denominator.map_or(u32::MAX, |n| n as u32))
            .u32(source.disposition.map_or(u32::MAX, |n| n as u32))
            .ptr(residual.section.lo.device_ptr())
            .ptr(residual.section.hi.device_ptr())
            .u32(residual.offset as u32)
            .u32(residual.denominator.map_or(u32::MAX, |n| n as u32))
            .u32(residual.disposition.map_or(u32::MAX, |n| n as u32))
            .u32(source_complex as u32)
            .u32(residual_complex as u32)
            .u32(source_raw as u32)
            .u32(response_raw as u32)
            .u32(predicted_from as u32)
            .u32(residual_raw as u32)
            .ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_phase_response_adjoint_products",
            response_raw,
            &mut products,
            "phase-response-adjoint",
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
            "phase-response-adjoint",
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
            "phase-response-adjoint",
        )
    }
}
