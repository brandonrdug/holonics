use super::*;

impl<'c> ResidentSurface<'c> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_contact_scale_gradient(
        &self,
        lane: &Lane<'_, 'c>,
        offsets: &ResidentSection<'c>,
        columns: &ResidentSection<'c>,
        values: &ResidentSection<'c>,
        basis_bounds: &ResidentSection<'c>,
        p: &ResidentSection<'c>,
        c: &ResidentSection<'c>,
        delta_bounds: &ResidentSection<'c>,
        d: usize,
        count: usize,
        nnz: usize,
        group_width: usize,
        grain: u32,
        output: &ResidentSection<'c>,
        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "contact-scale-gradient",
            what: "incompatible rectangular CSR contact packet".into(),
        };
        let groups = count.checked_div(group_width.max(1)).ok_or_else(fail)?;
        let offsets_width = count
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(fail)?;
        let columns_width = nnz.max(1).checked_mul(2).ok_or_else(fail)?;
        let values_width = nnz.max(1).checked_mul(4).ok_or_else(fail)?;
        if d == 0
            || d % 2 != 0
            || count == 0
            || d > u32::MAX as usize / 2
            || count > u32::MAX as usize / 4
            || group_width == 0
            || count % group_width != 0
            || !(1..=120).contains(&grain)
            || [d, count, nnz, group_width, groups]
                .iter()
                .any(|n| *n > u32::MAX as usize)
            || !self.operative_shape(offsets, 1, offsets_width)
            || !self.operative_shape(columns, 1, columns_width)
            || !self.operative_shape(values, 1, values_width)
            || !self.operative_shape(basis_bounds, 1, 4)
            || !self.operative_shape(p, 2, d.checked_mul(2).ok_or_else(fail)?)
            || !self.operative_shape(c, 2, count.checked_mul(4).ok_or_else(fail)?)
            || !self.operative_shape(delta_bounds, 1, 4)
            || !self.operative_shape(output, groups, 6)
            || !self.operative_shape(flags, groups, SLOT_WORDS / 2)
        {
            return Err(fail());
        }
        let mut params = Params::new();
        for section in [offsets, columns, values, basis_bounds, p, c, delta_bounds] {
            params
                .ptr(section.lo_device_ptr())
                .ptr(section.hi_device_ptr());
        }
        params
            .u32(d as u32)
            .u32(count as u32)
            .u32(nnz as u32)
            .u32(group_width as u32)
            .u32(grain)
            .ptr(output.lo_device_ptr())
            .ptr(output.hi_device_ptr())
            .ptr(flags.lo_device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_contact_scale_gradient",
            groups,
            self.declaration.warp_size.max(1),
            0,
            &mut params,
            "contact-scale-gradient",
        )
    }
}
