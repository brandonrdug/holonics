use super::*;
use crate::native_ecology::constitutive_fibre::{ResidentNormalEnclosureView, ResidentNormalInput};
impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_field_target_residual_section(
        &self, lane: &Lane<'_, 'c>, output: &ResidentSection<'c>, target: &ResidentSection<'c>,
        mask: Option<&ResidentSection<'c>>, d: usize, count: usize, rows: usize, step_bits: u32,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        let width = d.checked_add(2 * count).ok_or_else(fail)?;
        let output_stride = 2usize.checked_mul(width.checked_add(1).ok_or_else(fail)?).ok_or_else(fail)?;
        let target_stride = 2usize.checked_mul(d.checked_add(1).ok_or_else(fail)?).ok_or_else(fail)?;
        if d == 0 || d % 2 != 0 || rows == 0 || step_bits > 120 || output.rows != rows
            || target.rows != rows || output.width != output_stride || target.width != target_stride
            || out.rows != rows || out.width != output_stride
            || mask.is_some_and(|m| m.rows != 1 || m.width != d / 2 || m.grain.0!=0 || !std::ptr::eq(m.surface(),self))
            || !std::ptr::eq(output.surface(), self) || !std::ptr::eq(target.surface(), self)
            || !std::ptr::eq(out.surface(), self)
        { return Err(fail()); }
        let mut p = Params::new();
        p.ptr(output.lo_device_ptr()).ptr(output.hi_device_ptr()).u32(output.width as u32)
            .ptr(target.lo_device_ptr()).ptr(target.hi_device_ptr()).u32(target.width as u32)
            .ptr(mask.map_or(0, |m| m.lo_device_ptr()))
            .ptr(mask.map_or(0, |m| m.hi_device_ptr())).u32(u32::from(mask.is_some()))
            .u32(d as u32).u32(count as u32).u32(rows as u32).u32(step_bits)
            .ptr(out.lo_device_ptr()).ptr(out.hi_device_ptr()).ptr(lane.slot).ptr(lane.census)
            .ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane, "section_field_target_residual_section", 1, self.launch.block_x, 0, &mut p, "field-target-residual-section")
    }

    pub(crate) fn record_field_reflection_target(
        &self,
        lane: &Lane<'_, 'c>,
        input: ResidentNormalEnclosureView<'_, 'c>,
        output: ResidentNormalEnclosureView<'_, 'c>,
        target: ResidentNormalEnclosureView<'_, 'c>,
        bounds: &ResidentSection<'c>,
        mask: Option<&ResidentSection<'c>>,
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
        let target_extent_ok = target.width == d
            || target.width == width
            || (mask.is_some() && target.width > 0 && target.width <= d && target.width % 2 == 0);
        for v in [input, output, target] {
            self.validate_normal_input(ResidentNormalInput::Enclosed(v), input.grain.0)?;
        }
        if n == 0
            || width > u32::MAX as usize
            || step_bits > 120
            || input.width != width
            || output.width != width
            || !target_extent_ok
            || !self.operative_shape(bounds, 1, 4)
            || !self.operative_shape(out[0], 1, 12 * (d + 1))
            || !self.operative_shape(out[1], k.max(1), 4)
            || !self.operative_shape(out[2], 1, 4)
            || !self.operative_shape(out[3], 1, query_width)
            || mask.is_some_and(|m| !self.operative_shape(m, 1, d / 2))
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
            .ptr(mask.map_or(0, |m| m.lo.device_ptr()))
            .ptr(mask.map_or(0, |m| m.hi.device_ptr()))
            .u32(u32::from(mask.is_some()))
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
