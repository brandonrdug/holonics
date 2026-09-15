use super::*;
use crate::native_ecology::constitutive_fibre::{ResidentNormalEnclosureView, ResidentNormalInput};
impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_field_reflection_target(
        &self,
        lane: &Lane<'_, 'c>,
        input: ResidentNormalEnclosureView<'_, 'c>,
        output: ResidentNormalEnclosureView<'_, 'c>,
        target: ResidentNormalEnclosureView<'_, 'c>,
        bounds: &ResidentSection<'c>,
        n: usize,
        k: usize,
        step_bits: u32,
        out: [&ResidentSection<'c>; 4],
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        let d = n.checked_mul(6).ok_or_else(fail)?;
        let width = d
            .checked_add(k.checked_mul(2).ok_or_else(fail)?)
            .ok_or_else(fail)?;
        let query_width = n
            .checked_mul(10)
            .and_then(|v| v.checked_add(2 * k))
            .and_then(|v| v.checked_mul(4))
            .ok_or_else(fail)?;
        for v in [input, output, target] {
            self.validate_normal_input(ResidentNormalInput::Enclosed(v), input.grain.0)?;
        }
        if n == 0
            || width > u32::MAX as usize
            || step_bits > 120
            || input.width != width
            || output.width != width
            || (target.width != d && target.width != width)
            || !self.operative_shape(bounds, 1, 4)
            || !self.operative_shape(out[0], 1, 12 * (d + 1))
            || !self.operative_shape(out[1], k.max(1), 4)
            || !self.operative_shape(out[2], 1, 4)
            || !self.operative_shape(out[3], 1, query_width)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for v in [input, output, target] {
            p.ptr(v.section.lo.device_ptr())
                .ptr(v.section.hi.device_ptr())
                .u32(v.offset as u32);
        }
        p.u32(target.width as u32)
            .ptr(bounds.lo.device_ptr())
            .ptr(bounds.hi.device_ptr())
            .u32(n as u32)
            .u32(k as u32)
            .u32(input.grain.0)
            .u32(step_bits);
        for v in out {
            p.ptr(v.lo.device_ptr()).ptr(v.hi.device_ptr());
        }
        p.ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_reflection_target",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "field-reflection-target",
        )
    }
    pub(crate) fn record_field_reflection_input_cotangent(
        &self,
        lane: &Lane<'_, 'c>,
        diagnostics: &ResidentSection<'c>,
        d: usize,
        k: usize,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        let width = d
            .checked_add(k.checked_mul(2).ok_or_else(fail)?)
            .ok_or_else(fail)?;
        if d == 0
            || d % 2 != 0
            || width > u32::MAX as usize
            || !self.operative_shape(diagnostics, 1, 2 * (2 * d + 4 * k + 8))
            || !self.operative_shape(out, 1, 2 * (width + 1))
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(diagnostics.lo.device_ptr())
            .ptr(diagnostics.hi.device_ptr())
            .u32(d as u32)
            .u32(k as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_reflection_input_cotangent",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "field-reflection-input-cotangent",
        )
    }
}
