use super::*;

impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_enclosure_zero(
        &self,
        lane: &Lane<'_, 'c>,
        output: &ResidentSection<'c>,
        rows: usize,
        width: usize,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "incident-enclosure-zero",
            what: "incompatible zero enclosure chart".into(),
        };
        if rows == 0
            || width == 0
            || width % 2 != 0
            || output.rows() != rows
            || !self.operative_shape(
                output,
                rows,
                width
                    .checked_add(1)
                    .and_then(|n| n.checked_mul(2))
                    .ok_or_else(fail)?,
            )
            || rows > u32::MAX as usize
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.u32(rows as u32)
            .u32(width as u32)
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_enclosure_zero",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "incident-enclosure-zero",
        )
    }

    pub(crate) fn record_enclosure_regroup(
        &self,
        lane: &Lane<'_, 'c>,
        input: &ResidentSection<'c>,
        offset: usize,
        input_rows: usize,
        input_d: usize,
        output: &ResidentSection<'c>,
        output_d: usize,
        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "incident-enclosure-regroup",
            what: "incompatible joint and row extents".into(),
        };
        let rows = output.rows();
        let stride = |d: usize| d.checked_add(1)?.checked_mul(2);
        let required = stride(input_d)
            .and_then(|s| s.checked_mul(input_rows))
            .and_then(|s| s.checked_add(offset))
            .ok_or_else(fail)?;
        if input_rows == 0
            || rows == 0
            || input_d == 0
            || output_d == 0
            || input_d % 2 != 0
            || output_d % 2 != 0
            || [input_rows, rows, input_d, output_d]
                .iter()
                .any(|n| *n > u32::MAX as usize)
            || input_rows.checked_mul(input_d) != rows.checked_mul(output_d)
            || !std::ptr::eq(input.surface(), self)
            || input.grain().0 != 0
            || input
                .rows()
                .checked_mul(input.width())
                .is_none_or(|n| required > n)
            || !self.operative_shape(output, rows, stride(output_d).ok_or_else(fail)?)
            || !self.operative_shape(flags, rows, SLOT_WORDS / 2)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(input.lo.device_ptr())
            .ptr(input.hi.device_ptr())
            .u64(offset as u64)
            .u32(input_rows as u32)
            .u32(input_d as u32)
            .u32(rows as u32)
            .u32(output_d as u32)
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(flags.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_enclosure_regroup",
            rows,
            1,
            0,
            &mut p,
            "incident-enclosure-regroup",
        )?;
        let mut joined = Params::new();
        joined
            .ptr(flags.lo.device_ptr())
            .u32(rows as u32)
            .ptr(lane.slot);
        self.record_blocks(
            lane,
            "section_enclosure_collect_row_status",
            rows,
            1,
            0,
            &mut joined,
            "incident-row-obstruction-union",
        )
    }
}
