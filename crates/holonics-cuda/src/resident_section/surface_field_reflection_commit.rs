use super::*;
use crate::native_ecology::constitutive_fibre::{ResidentNormalEnclosureView, ResidentNormalInput};

impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_field_reflection_current_delta(
        &self,
        lane: &Lane<'_, 'c>,
        old_b: &ResidentSection<'c>,
        bounds: &ResidentSection<'c>,
        output: ResidentNormalEnclosureView<'_, 'c>,
        d: usize,
        k: usize,
        out: [&ResidentSection<'c>; 4],
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        self.validate_normal_input(ResidentNormalInput::Enclosed(output), output.grain.0)?;
        let width = d
            .checked_add(k.checked_mul(2).ok_or_else(fail)?)
            .ok_or_else(fail)?;
        if d == 0
            || d % 2 != 0
            || width > u32::MAX as usize
            || output.width != width
            || !self.operative_shape(old_b, k.max(1), 4)
            || !self.operative_shape(bounds, 1, 4)
            || !self.operative_shape(out[0], 2, 2 * d)
            || !self.operative_shape(out[1], 2, 4)
            || !self.operative_shape(out[2], k.max(1), 4)
            || !self.operative_shape(out[3], 1, 4)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for v in [old_b, bounds, output.section] {
            p.ptr(v.lo.device_ptr()).ptr(v.hi.device_ptr());
        }
        p.u32(output.offset as u32).u32(d as u32).u32(k as u32);
        for v in out {
            p.ptr(v.lo.device_ptr()).ptr(v.hi.device_ptr());
        }
        p.ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_reflection_current_delta",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "field-reflection-current-delta",
        )
    }
    pub(crate) fn record_field_reflection_current_bound(
        &self,
        lane: &Lane<'_, 'c>,
        output: ResidentNormalEnclosureView<'_, 'c>,
        k: usize,
        bounds: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        self.validate_normal_input(output.into(), output.grain.0)?;
        if output.width > u32::MAX as usize
            || k > output.width / 2
            || !self.operative_shape(bounds, 1, 4)
        {
            return Err(Self::operative_error());
        }
        let mut p = Params::new();
        p.ptr(output.section.lo.device_ptr())
            .ptr(output.section.hi.device_ptr())
            .u32(output.offset as u32)
            .u32(output.width as u32)
            .ptr(bounds.lo.device_ptr())
            .ptr(bounds.hi.device_ptr())
            .u32(k as u32)
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_reflection_current_bound",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "field-reflection-current-bound",
        )
    }
    pub(crate) fn record_field_reflection_report(
        &self,
        lane: &Lane<'_, 'c>,
        input: ResidentNormalEnclosureView<'_, 'c>,
        output: ResidentNormalEnclosureView<'_, 'c>,
        before: &ResidentSection<'c>,
        aggregate: &ResidentSection<'c>,
        moment_bounds: &ResidentSection<'c>,
        trace: &ResidentSection<'c>,
        d: usize,
        k: usize,
        grain: u32,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        self.validate_normal_input(ResidentNormalInput::Enclosed(input), grain)?;
        self.validate_normal_input(ResidentNormalInput::Enclosed(output), grain)?;
        let width = d
            .checked_add(k.checked_mul(2).ok_or_else(fail)?)
            .ok_or_else(fail)?;
        let report_width = d
            .checked_add(1)
            .and_then(|v| v.checked_mul(12))
            .ok_or_else(fail)?;
        if d == 0
            || d % 2 != 0
            || width > u32::MAX as usize
            || input.width != width
            || output.width != width
            || !self.operative_shape(before, 1, report_width)
            || !self.operative_shape(out, 1, report_width)
            || !self.operative_shape(aggregate, 1, 2 * d)
            || !self.operative_shape(moment_bounds, 1, 8)
            || !self.operative_shape(trace, 1, 18 * d)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(input.section.lo.device_ptr())
            .ptr(input.section.hi.device_ptr())
            .u32(input.offset as u32)
            .ptr(output.section.lo.device_ptr())
            .ptr(output.section.hi.device_ptr())
            .u32(output.offset as u32);
        for v in [before, aggregate, moment_bounds, trace] {
            p.ptr(v.lo.device_ptr()).ptr(v.hi.device_ptr());
        }
        p.u32(d as u32)
            .u32(k as u32)
            .u32(grain)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_reflection_report",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "field-reflection-report",
        )
    }
}
