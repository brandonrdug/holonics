use super::*;

impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_enclosure_append_homogeneous(
        &self,
        lane: &Lane<'_, 'c>,
        source: &ResidentSection<'c>,
        rows: usize,
        components: usize,
        grain: u32,
        output: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "enclosure-append-homogeneous",
            what: "incompatible enclosure section".into(),
        };
        if rows == 0
            || rows > u32::MAX as usize
            || components > u32::MAX as usize - 3
            || !(1..=120).contains(&grain)
            || components == 0
            || components % 2 != 0
            || source.rows != rows
            || source.width != 2 * (components + 1)
            || output.rows != rows
            || output.width != 2 * (components + 3)
            || !self.operative_shape(source, rows, source.width)
            || !self.operative_shape(output, rows, output.width)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(source.lo.device_ptr())
            .ptr(source.hi.device_ptr())
            .u32(rows as u32)
            .u32(components as u32)
            .u32(grain)
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_enclosure_append_homogeneous",
            rows,
            1,
            0,
            &mut p,
            "enclosure-append-homogeneous",
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_normal_applied_enclosed_features(
        &self,
        lane: &Lane<'_, 'c>,
        state: &ResidentSection<'c>,
        source: &ResidentSection<'c>,
        rows: usize,
        source_complex: usize,
        targets: usize,
        grain: u32,
        output: &ResidentSection<'c>,
        work: &ResidentSection<'c>,
        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "normal-applied-enclosed-features",
            what: "incompatible enclosed feature chart".into(),
        };
        let d = source_complex.checked_mul(2).ok_or_else(fail)?;
        let stride = targets
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .ok_or_else(fail)?;
        let sw = crate::native_ecology::constitutive_fibre::normal_feature_state_words(
            source_complex,
            targets,
        )
        .ok_or_else(fail)?;
        let work_width = targets.checked_mul(4).ok_or_else(fail)?;
        if rows == 0
            || source_complex == 0
            || targets == 0
            || source.rows != rows
            || source.width != 2 * (d + 1)
            || !self.operative_shape(source, rows, source.width)
            || !self.operative_shape(state, 1, sw)
            || !self.operative_shape(output, rows, stride * 2)
            || !self.operative_shape(work, rows, work_width)
            || !self.operative_shape(flags, rows, SLOT_WORDS / 2)
            || !(1..=120).contains(&grain)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(state.lo.device_ptr())
            .ptr(source.lo.device_ptr())
            .ptr(source.hi.device_ptr())
            .u32(source.width as u32)
            .u32(rows as u32)
            .u32(source_complex as u32)
            .u32(targets as u32)
            .u32(grain)
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(work.lo.device_ptr())
            .ptr(flags.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_applied_enclosed_features",
            rows,
            self.launch.block_x.min(512),
            0,
            &mut p,
            "normal-applied-enclosed-features",
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
            "normal-applied-enclosed-features-status",
        )
    }
}
