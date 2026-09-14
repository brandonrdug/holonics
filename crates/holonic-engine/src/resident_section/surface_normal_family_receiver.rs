use super::*;
use crate::native_ecology::constitutive_fibre::ResidentNormalEnclosureView;
impl<'c> ResidentSurface<'c> {
    fn point_word_shape(roots: usize, steps: usize) -> Option<(usize,usize,usize)> {
        let a=roots.checked_mul(4)?;
        let w=a.checked_mul(2)?.checked_add(2)?;
        let t=steps.checked_add(1)?.checked_mul(w)?;
        let y=t.checked_sub(2+a)?;
        let report=4usize.checked_add(2*a)?.checked_add(y.checked_mul(2)?)?.checked_mul(2)?;
        if roots==0 || steps==0 || report>u32::MAX as usize || w.checked_mul(w)?.checked_mul(4)?>u32::MAX as usize {return None;}
        Some((a,w,report))
    }
    pub(crate) fn record_normal_point_word_seed(&self,lane:&Lane<'_, 'c>,family:&ResidentSection<'c>,
        source_width:usize, roots:usize, steps:usize, initial:&ResidentSection<'c>,
        state:&ResidentSection<'c>, report:&ResidentSection<'c>) -> Result<(),ResidentRefusal> {
        let fail=||Self::operative_error();
        let (a,w,rw)=Self::point_word_shape(roots,steps).ok_or_else(fail)?;
        let fw=source_width.checked_add(w).and_then(|v|v.checked_add(4)?.checked_add(w.checked_mul(w)?)).ok_or_else(fail)?;
        if source_width==0 || fw>u32::MAX as usize || !self.operative_shape(family,1,fw) ||
            !self.operative_shape(initial,1,2*(4+4*a)) || !self.operative_shape(state,1,2*(w+1)) ||
            !self.operative_shape(report,1,rw) {return Err(fail());}
        let mut p=Params::new();
        p.ptr(family.lo.device_ptr()).ptr(family.hi.device_ptr()).u32(source_width as u32)
            .u32(roots as u32).u32(steps as u32)
            .ptr(initial.lo.device_ptr()).ptr(initial.hi.device_ptr())
            .ptr(state.lo.device_ptr()).ptr(state.hi.device_ptr())
            .ptr(report.lo.device_ptr()).ptr(report.hi.device_ptr())
            .ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane,"section_normal_point_word_seed",1,self.launch.block_x,0,&mut p,"normal-point-word-source")
    }
    pub(crate) fn record_normal_point_word_step(&self,lane:&Lane<'_, 'c>,map:&ResidentSection<'c>,
        roots:usize,steps:usize,at:usize,state:&ResidentSection<'c>,report:&ResidentSection<'c>,workspace:&ResidentSection<'c>)
        ->Result<(),ResidentRefusal>{
        let fail=||Self::operative_error();
        let (_,w,rw)=Self::point_word_shape(roots,steps).ok_or_else(fail)?;
        if at==0 || at>steps || !self.operative_shape(map,2*w,2*w) ||
            !self.operative_shape(state,1,2*(w+1)) || !self.operative_shape(report,1,rw) ||
            !self.operative_shape(workspace,1,4*w) {return Err(fail());}
        let mut p=Params::new();
        p.ptr(map.lo.device_ptr()).ptr(map.hi.device_ptr()).u32(roots as u32).u32(steps as u32).u32(at as u32)
            .ptr(state.lo.device_ptr()).ptr(state.hi.device_ptr())
            .ptr(report.lo.device_ptr()).ptr(report.hi.device_ptr()).ptr(workspace.lo.device_ptr())
            .ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane,"section_normal_point_word_step",1,self.launch.block_x,0,&mut p,"normal-point-word-step")
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_normal_family_receiver(
        &self,
        lane: &Lane<'_, 'c>,
        family: &ResidentSection<'c>,
        source_width: usize,
        anchor: ResidentNormalEnclosureView<'_, 'c>,
        roots: usize,
        outputs: usize,
        joint: &ResidentSection<'c>,
        anchor_basis: &ResidentSection<'c>,
        vertical: &ResidentSection<'c>,
        graph: &ResidentSection<'c>,
        report: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let a = roots.checked_mul(4).ok_or_else(fail)?;
        let w = a.checked_add(outputs).ok_or_else(fail)?;
        let projection = a.max(outputs).checked_mul(2).ok_or_else(fail)?;
        let t = w.checked_add(2).ok_or_else(fail)?;
        let fw = t
            .checked_mul(t)
            .and_then(|v| v.checked_add(t)?.checked_add(source_width)?.checked_add(4))
            .ok_or_else(fail)?;
        let rw = w
            .checked_mul(4)
            .and_then(|v| v.checked_add(8))
            .ok_or_else(fail)?;
        let aw = a
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        let capacity = anchor
            .section
            .rows
            .checked_mul(anchor.section.width)
            .ok_or_else(fail)?;
        let end = anchor.offset.checked_add(aw).ok_or_else(fail)?;
        if roots == 0
            || outputs == 0
            || outputs > u32::MAX as usize
            || source_width == 0
            || fw > u32::MAX as usize
            || rw > u32::MAX as usize
            || end > u32::MAX as usize
            || anchor.width != a
            || !(1..=120).contains(&anchor.grain.0)
            || anchor.offset % 2 != 0
            || end > capacity
            || anchor.section.grain.0 != 0
            || !std::ptr::eq(anchor.section.surface, self)
            || !self.operative_shape(family, 1, fw)
            || !self.operative_shape(joint, w, w)
            || !self.operative_shape(anchor_basis, a, a)
            || !self.operative_shape(vertical, outputs, outputs)
            || !self.operative_shape(graph, projection, projection)
            || !self.operative_shape(report, 1, rw)
        {
            return Err(fail());
        }
        let shared = a
            .max(outputs)
            .checked_mul(5)
            .and_then(|v| v.checked_add(a.checked_mul(3)?)?.checked_add(outputs))
            .and_then(|v| v.checked_mul(16))
            .and_then(|v| u32::try_from(v).ok())
            .filter(|v| *v <= self.declaration().max_sectiond_bytes)
            .ok_or_else(fail)?;
        let mut p = Params::new();
        p.ptr(family.lo.device_ptr())
            .ptr(family.hi.device_ptr())
            .u32(source_width as u32)
            .ptr(anchor.section.lo.device_ptr())
            .ptr(anchor.section.hi.device_ptr())
            .u32(anchor.offset as u32)
            .u32(roots as u32)
            .u32(outputs as u32)
            .u32(anchor.grain.0);
        for s in [joint, anchor_basis, vertical, graph, report] {
            p.ptr(s.lo.device_ptr()).ptr(s.hi.device_ptr());
        }
        p.ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_family_receiver",
            1,
            self.launch.block_x,
            shared,
            &mut p,
            "normal-family-receiver",
        )
    }
}
