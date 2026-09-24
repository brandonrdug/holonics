use super::*;
impl<'c> ResidentSurface<'c> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_wave_family_pullback(
        &self,
        lane: &Lane<'_, 'c>,
        basis: &ResidentSection<'c>,
        left: &ResidentSection<'c>,
        ls: usize,
        right: &ResidentSection<'c>,
        rs: usize,
        t: usize,
        graph: &ResidentSection<'c>,
        joint: &ResidentSection<'c>,
        lb: &ResidentSection<'c>,
        rb: &ResidentSection<'c>,
        lo: &ResidentSection<'c>,
        ro: &ResidentSection<'c>,
        workspace: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let w = t.checked_mul(2).ok_or_else(fail)?;
        let k = w.checked_mul(2).ok_or_else(fail)?;
        let square = t.checked_mul(t).ok_or_else(fail)?;
        let report = |s: usize, target: usize| {
            target
                .checked_mul(target)?
                .checked_add(s)?
                .checked_add(target)?
                .checked_add(4)
        };
        let lw = report(ls, t).ok_or_else(fail)?;
        let rw = report(rs, t).ok_or_else(fail)?;
        let jw = report(w, w).ok_or_else(fail)?;
        let ow = report(w, t).ok_or_else(fail)?;
        let scratch = t.checked_mul(20).ok_or_else(fail)?;
        if t == 0
            || [t, w, k, square, lw, rw, jw, ow, scratch]
                .iter()
                .any(|v| *v >= u32::MAX as usize)
            || !self.operative_shape(basis, w, w)
            || !self.operative_shape(left, 1, lw)
            || !self.operative_shape(right, 1, rw)
            || !self.operative_shape(graph, k, k)
            || !self.operative_shape(joint, 1, jw)
            || !self.operative_shape(lb, t, t)
            || !self.operative_shape(rb, t, t)
            || !self.operative_shape(lo, 1, ow)
            || !self.operative_shape(ro, 1, ow)
            || !self.operative_shape(workspace, 1, scratch)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(basis.lo.device_ptr())
            .ptr(basis.hi.device_ptr())
            .ptr(left.lo.device_ptr())
            .ptr(left.hi.device_ptr())
            .u32(ls as u32)
            .ptr(right.lo.device_ptr())
            .ptr(right.hi.device_ptr())
            .u32(rs as u32)
            .u32(t as u32)
            .ptr(graph.lo.device_ptr())
            .ptr(graph.hi.device_ptr())
            .ptr(joint.lo.device_ptr())
            .ptr(joint.hi.device_ptr())
            .ptr(lb.lo.device_ptr())
            .ptr(lb.hi.device_ptr())
            .ptr(rb.lo.device_ptr())
            .ptr(rb.hi.device_ptr())
            .ptr(lo.lo.device_ptr())
            .ptr(lo.hi.device_ptr())
            .ptr(ro.lo.device_ptr())
            .ptr(ro.hi.device_ptr())
            .ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_wave_family_pullback",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "wave-family-pullback",
        )
    }
}
