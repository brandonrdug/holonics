use super::*;
use crate::native_ecology::constitutive_fibre::ResidentNormalEnclosureView;

impl<'chart> ResidentSurface<'chart> {
    pub(crate) fn record_field_global_scale_ports(&self,lane:&Lane<'_, 'chart>,ports:&ResidentSection<'chart>,bounds:&ResidentSection<'chart>,
        d:usize,step_bits:u32,out:&ResidentSection<'chart>,next_bounds:&ResidentSection<'chart>)->Result<(),ResidentRefusal>{
        if d==0||d>u32::MAX as usize||step_bits>120||!self.operative_shape(ports,2,2*d)
            ||!self.operative_shape(bounds,1,4)||!self.operative_shape(out,2,2*d)||!self.operative_shape(next_bounds,1,4){return Err(Self::operative_error());}
        let mut p=Params::new();p.ptr(ports.lo_device_ptr()).ptr(ports.hi_device_ptr()).ptr(bounds.lo_device_ptr()).ptr(bounds.hi_device_ptr())
            .u32(d as u32).u32(step_bits).ptr(out.lo_device_ptr()).ptr(out.hi_device_ptr()).ptr(next_bounds.lo_device_ptr()).ptr(next_bounds.hi_device_ptr())
            .ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane,"section_field_global_scale_ports",1,1,0,&mut p,"field-global-factor-step")
    }
    /// Record the sparse declared-contact global action.  The D map remains contact-major on the
    /// device; the workspace contains only D/D* products, Richardson state and residuals.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_field_global_action(
        &self,
        lane: &Lane<'_, 'chart>,
        map: &ResidentSection<'chart>,
        bounds: &ResidentSection<'chart>,
        input: ResidentNormalEnclosureView<'_, 'chart>,
        d: usize,
        count: usize,
        grain: u32,
        steps: usize,
        omega_bits: u32,
        work: &ResidentSection<'chart>,
        out: &ResidentSection<'chart>,
        residual: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        let width = d
            .checked_add(count.checked_mul(2).ok_or_else(fail)?)
            .ok_or_else(fail)?;
        let work_wide = d
            .checked_mul(4)
            .and_then(|v| {
                v.checked_add(count.checked_mul(2)?)?
                    .checked_add(d)?
                    .checked_add(count.checked_mul(2)?)
            })
            .and_then(|v| v.checked_add(1))
            .ok_or_else(fail)?;
        let work_words = work_wide.checked_mul(2).ok_or_else(fail)?;
        if d == 0
            || d > u32::MAX as usize
            || count > u32::MAX as usize
            || d % 2 != 0
            || steps == 0
            || steps > u32::MAX as usize
            || (omega_bits > 120 && omega_bits != u32::MAX)
            || !(1..=120).contains(&grain)
            || !self.operative_shape(map, count.max(1), 2 * d)
            || !self.operative_shape(bounds, 1, 4)
            || !self.operative_shape(work, 1, work_words)
            || !self.operative_shape(out, 1, 2 * (width + 1))
            || !self.operative_shape(residual, 1, 2 * (d + 1))
            || input.components() != width
            || input.offset() > u32::MAX as usize
            || input.grain().0 != grain
            || !std::ptr::eq(input.surface(), self)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for section in [map, bounds, input.section()] {
            p.ptr(section.lo_device_ptr()).ptr(section.hi_device_ptr());
        }
        p.u32(input.offset() as u32)
            .u32(d as u32)
            .u32(count as u32)
            .u32(grain)
            .u32(steps as u32)
            .u32(omega_bits)
            .ptr(work.lo_device_ptr())
            .ptr(out.lo_device_ptr())
            .ptr(out.hi_device_ptr())
            .ptr(residual.lo_device_ptr())
            .ptr(residual.hi_device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_global_action",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "field-global-action",
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_field_global_pullback(
        &self,
        lane: &Lane<'_, 'chart>,
        map: &ResidentSection<'chart>,
        bounds: &ResidentSection<'chart>,
        input: ResidentNormalEnclosureView<'_, 'chart>,
        output: ResidentNormalEnclosureView<'_, 'chart>,
        covector: ResidentNormalEnclosureView<'_, 'chart>,
        d: usize,
        count: usize,
        grain: u32,
        steps: usize,
        omega_bits: u32,
        work: &ResidentSection<'chart>,
        incoming: &ResidentSection<'chart>,
        ports: &ResidentSection<'chart>,
        currents: &ResidentSection<'chart>,
        delta_bounds: &ResidentSection<'chart>,
        residual: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        let width = d
            .checked_add(count.checked_mul(2).ok_or_else(fail)?)
            .ok_or_else(fail)?;
        let work_wide = d
            .checked_mul(5)
            .and_then(|v| v.checked_add(4 * count)?.checked_add(1))
            .ok_or_else(fail)?;
        let work_words = work_wide.checked_mul(2).ok_or_else(fail)?;
        if d == 0
            || d > u32::MAX as usize
            || count > u32::MAX as usize
            || d % 2 != 0
            || steps == 0
            || steps > u32::MAX as usize
            || (omega_bits > 120 && omega_bits != u32::MAX)
            || !(1..=120).contains(&grain)
            || input.components() != width
            || output.components() != width
            || covector.components() != width
            || [input.offset(), output.offset(), covector.offset()]
                .iter()
                .any(|i| *i > u32::MAX as usize)
            || input.grain().0 != grain
            || output.grain().0 != grain
            || covector.grain().0 != grain
            || !self.operative_shape(map, count.max(1), 2 * d)
            || !self.operative_shape(bounds, 1, 4)
            || !self.operative_shape(work, 1, work_words)
            || !self.operative_shape(incoming, 1, 2 * (width + 1))
            || !self.operative_shape(ports, 2, 2 * d)
            || !self.operative_shape(currents, 2, 4 * count.max(1))
            || !self.operative_shape(delta_bounds, 1, 4)
            || !self.operative_shape(residual, 1, 2 * (d + 1))
            || !std::ptr::eq(input.surface(), self)
            || !std::ptr::eq(output.surface(), self)
            || !std::ptr::eq(covector.surface(), self)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(map.lo_device_ptr())
            .ptr(map.hi_device_ptr())
            .ptr(bounds.lo_device_ptr())
            .ptr(bounds.hi_device_ptr());
        for view in [input, output, covector] {
            p.ptr(view.section().lo_device_ptr())
                .ptr(view.section().hi_device_ptr())
                .u32(view.offset() as u32);
        }
        p.u32(d as u32)
            .u32(count as u32)
            .u32(grain)
            .u32(steps as u32)
            .u32(omega_bits)
            .ptr(work.lo_device_ptr())
            .ptr(incoming.lo_device_ptr())
            .ptr(incoming.hi_device_ptr())
            .ptr(ports.lo_device_ptr())
            .ptr(ports.hi_device_ptr())
            .ptr(currents.lo_device_ptr())
            .ptr(currents.hi_device_ptr())
            .ptr(delta_bounds.lo_device_ptr())
            .ptr(delta_bounds.hi_device_ptr())
            .ptr(residual.lo_device_ptr())
            .ptr(residual.hi_device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_global_pullback",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "field-global-pullback",
        )
    }

    pub(crate) fn record_field_global_residual_trace(
        &self,
        lane: &Lane<'_, 'chart>,
        residual: &ResidentSection<'chart>,
        d: usize,
        trace: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        if d == 0
            || d % 2 != 0
            || !self.operative_shape(residual, 1, 2 * (d + 1))
            || !self.operative_shape(trace, 1, 18 * d)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(residual.lo_device_ptr())
            .ptr(residual.hi_device_ptr())
            .u32(d as u32)
            .ptr(trace.lo_device_ptr())
            .ptr(trace.hi_device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_global_residual_trace",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "field-global-residual-trace",
        )
    }
}
