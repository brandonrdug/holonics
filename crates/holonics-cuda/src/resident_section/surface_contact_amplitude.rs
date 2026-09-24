use super::*;

impl<'c> ResidentSurface<'c> {
    /// Form a positive dyadic point proposal from a rectangular-factor cotangent.
    /// The proposal and its accepted step are fresh resident packets; no material archive
    /// or causal update is written by this operation.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_contact_amplitude_proposal(
        &self,
        lane: &Lane<'_, 'c>,
        gradient: &ResidentSection<'c>,
        rho: &ResidentSection<'c>,
        groups: usize,
        requested_step_bits: u32,
        grain: u32,
        amplitude: &ResidentSection<'c>,
        accepted_steps: &ResidentSection<'c>,
        proposal_reference: Option<&ResidentSection<'c>>,
        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        if groups == 0
            || groups > u32::MAX as usize
            || requested_step_bits > 128
            || !(1..=120).contains(&grain)
            || !self.operative_shape(gradient, groups, 6)
            || !self.operative_shape(rho, groups, 6)
            || !self.operative_shape(amplitude, groups, 6)
            || !self.operative_shape(accepted_steps, groups, 2)
            || proposal_reference.is_some_and(|s| !self.operative_shape(s, groups, 6))
            || !self.operative_shape(flags, groups, SLOT_WORDS / 2)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for section in [gradient, rho] {
            p.ptr(section.lo_device_ptr()).ptr(section.hi_device_ptr());
        }
        p.u32(groups as u32)
            .u32(requested_step_bits)
            .u32(grain)
            .ptr(amplitude.lo_device_ptr())
            .ptr(amplitude.hi_device_ptr())
            .ptr(accepted_steps.lo_device_ptr())
            .ptr(accepted_steps.hi_device_ptr());
        if let Some(reference) = proposal_reference {
            p.ptr(reference.lo_device_ptr())
                .ptr(reference.hi_device_ptr());
        } else {
            p.ptr(0).ptr(0);
        }
        p.ptr(flags.lo_device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_contact_amplitude_proposal",
            groups,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "contact-amplitude-proposal",
        )
    }

    /// Rebuild both sparse charts at a supplied point amplitude. Callers launch this
    /// wrapper once for the CSR chart and once for its transpose chart, preserving topology.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_contact_amplitude_rebuild(
        &self,
        lane: &Lane<'_, 'c>,
        offsets: &ResidentSection<'c>,
        columns: &ResidentSection<'c>,
        template_values: &ResidentSection<'c>,
        transpose_offsets: &ResidentSection<'c>,
        transpose_rows: &ResidentSection<'c>,
        template_transpose_values: &ResidentSection<'c>,
        amplitudes: &ResidentSection<'c>,
        rows: usize,
        transpose_rows_count: usize,
        nnz: usize,
        group_width: usize,
        grain: u32,
        transpose: bool,
        output_values: &ResidentSection<'c>,
        row_rounding: &ResidentSection<'c>,
        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        let offset_rows = if transpose {
            transpose_rows_count
        } else {
            rows
        };
        let csr_offsets_width = rows
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(fail)?;
        let transpose_offsets_width = transpose_rows_count
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(fail)?;
        let sparse_width = nnz.max(1).checked_mul(2).ok_or_else(fail)?;
        let value_width = nnz.max(1).checked_mul(4).ok_or_else(fail)?;
        if rows == 0
            || transpose_rows_count == 0
            || [rows, transpose_rows_count, nnz, group_width]
                .iter()
                .any(|n| *n > u32::MAX as usize)
            || nnz > u32::MAX as usize
            || group_width == 0
            || rows % group_width != 0
            || !(1..=120).contains(&grain)
            || !self.operative_shape(offsets, 1, csr_offsets_width)
            || !self.operative_shape(columns, 1, sparse_width)
            || !self.operative_shape(template_values, 1, value_width)
            || !self.operative_shape(transpose_offsets, 1, transpose_offsets_width)
            || !self.operative_shape(transpose_rows, 1, sparse_width)
            || !self.operative_shape(template_transpose_values, 1, value_width)
            || !self.operative_shape(amplitudes, rows / group_width, 6)
            || !self.operative_shape(output_values, 1, value_width)
            || !self.operative_shape(row_rounding, offset_rows, 2)
            || !self.operative_shape(flags, offset_rows, SLOT_WORDS / 2)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for section in [
            offsets,
            columns,
            template_values,
            transpose_offsets,
            transpose_rows,
            template_transpose_values,
            amplitudes,
        ] {
            p.ptr(section.lo_device_ptr()).ptr(section.hi_device_ptr());
        }
        p.u32(rows as u32)
            .u32(transpose_rows_count as u32)
            .u32(nnz as u32)
            .u32(group_width as u32)
            .u32(grain)
            .u32(u32::from(transpose))
            .ptr(output_values.lo_device_ptr())
            .ptr(output_values.hi_device_ptr())
            .ptr(row_rounding.lo_device_ptr())
            .ptr(row_rounding.hi_device_ptr())
            .ptr(flags.lo_device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_contact_amplitude_rebuild",
            offset_rows,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "contact-amplitude-rebuild",
        )
    }
}

impl<'c> ResidentSurface<'c> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_contact_amplitude_bounds(
        &self,
        lane: &Lane<'_, 'c>,
        amplitudes: &ResidentSection<'c>,
        rounding: &ResidentSection<'c>,
        template_bounds: &ResidentSection<'c>,
        current_bounds: &ResidentSection<'c>,
        groups: usize,
        rows: usize,
        grain: u32,
        output: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        if groups == 0
            || rows == 0
            || groups > u32::MAX as usize
            || rows > u32::MAX as usize
            || !(1..=120).contains(&grain)
            || !self.operative_shape(amplitudes, groups, 6)
            || !self.operative_shape(rounding, rows, 2)
            || !self.operative_shape(template_bounds, 1, 4)
            || !self.operative_shape(current_bounds, 1, 4)
            || !self.operative_shape(output, 1, 4)
        {
            return Err(Self::operative_error());
        }
        let mut p = Params::new();
        for section in [amplitudes, rounding, template_bounds, current_bounds] {
            p.ptr(section.lo_device_ptr()).ptr(section.hi_device_ptr());
        }
        p.u32(groups as u32)
            .u32(rows as u32)
            .u32(grain)
            .ptr(output.lo_device_ptr())
            .ptr(output.hi_device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_contact_amplitude_bounds",
            1,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "contact-amplitude-bounds",
        )
    }
}
