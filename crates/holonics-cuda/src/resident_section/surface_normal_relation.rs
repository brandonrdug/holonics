use super::*;
use crate::native_ecology::constitutive_fibre::normal_feature_state_words;
impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_normal_applied_relation(&self,lane:&Lane<'_, 'c>,state:&ResidentSection<'c>,
        sources:usize,graph_sources:usize,targets:usize,grain:u32,basis:&ResidentSection<'c>,work:&ResidentSection<'c>) -> Result<(),ResidentRefusal> {
        let fail=||Self::operative_error();
        let w=graph_sources.checked_add(targets).and_then(|v|v.checked_mul(2)).ok_or_else(fail)?;
        let sw=normal_feature_state_words(sources,targets).ok_or_else(fail)?;
        if sources>graph_sources || w>u32::MAX as usize || !(1..=120).contains(&grain) ||
            !self.operative_shape(state,1,sw) || !self.operative_shape(basis,w,w) ||
            !self.operative_shape(work,1,2*w) {return Err(fail());}
        let mut p=Params::new();
        p.ptr(state.lo.device_ptr()).ptr(state.hi.device_ptr()).u32(sources as u32).u32(graph_sources as u32).u32(targets as u32).u32(grain)
            .ptr(basis.lo.device_ptr()).ptr(basis.hi.device_ptr()).ptr(work.lo.device_ptr())
            .ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane,"section_normal_applied_relation",1,self.declaration.warp_size.max(1),0,&mut p,"normal-applied-relation")
    }
}
