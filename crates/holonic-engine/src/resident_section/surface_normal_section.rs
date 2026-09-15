use super::*;
use crate::native_ecology::constitutive_fibre::{
    normal_feature_report_words, normal_feature_state_words, normal_feature_workspace_words,
    ResidentConstitutiveSection, ResidentNormalEnclosureView, ResidentNormalInput,
};
impl<'c> ResidentSurface<'c> {
    pub(crate) fn normal_enclosed_batch_table(&'c self,pairs:&[(ResidentNormalEnclosureView<'_, 'c>,ResidentNormalEnclosureView<'_, 'c>)],
        sources:usize,targets:usize,grain:ResidentGrain)->Result<ResidentSection<'c>,ResidentRefusal>{
        let fail=||Self::operative_error();
        if pairs.is_empty()||pairs.len()>u32::MAX as usize||sources==0||targets==0{return Err(fail());}
        let mut values=Vec::with_capacity(pairs.len().checked_mul(6).ok_or_else(fail)?);
        for &(x,y) in pairs{
            if x.width!=2*sources||y.width!=2*targets{return Err(fail());}
            for v in [x,y]{self.validate_normal_input(ResidentNormalInput::Enclosed(v),grain.0)?;
                for raw in [v.section.lo.device_ptr(),v.section.hi.device_ptr(),v.offset as u64]{values.push((raw as i64,raw as i64));}
            }
        }
        self.mount_section_rest(&ResidentSectionRest::found(pairs.len(),6,ResidentGrain(0),64,values).map_err(|_|fail())?)
    }
    pub(crate) fn record_normal_enclosed_batch(&self,lane:&Lane<'_, 'c>,state:&ResidentSection<'c>,table:&ResidentSection<'c>,
        sources:usize,targets:usize,grain:ResidentGrain,next:&ResidentSection<'c>,work:&ResidentSection<'c>,
        input:&ResidentSection<'c>,report:&ResidentSection<'c>)->Result<(),ResidentRefusal>{
        let fail=||Self::operative_error();
        let sw=normal_feature_state_words(sources,targets).ok_or_else(fail)?;
        let rw=normal_feature_report_words(sources,targets).ok_or_else(fail)?;
        let ww=normal_feature_workspace_words(sources,targets).ok_or_else(fail)?;
        let iw=sources.checked_mul(2).and_then(|d|d.checked_add(1)?.checked_mul(4)?.checked_add(3*targets)).ok_or_else(fail)?;
        if sources==0||targets==0||sources>u32::MAX as usize/2||targets>u32::MAX as usize/2
            ||table.rows==0||table.rows>u32::MAX as usize||!(1..=120).contains(&grain.0)
            ||!self.operative_shape(table,table.rows,6)||!self.operative_shape(state,1,sw)
            ||!self.operative_shape(next,1,sw)||!self.operative_shape(work,1,ww)
            ||!self.operative_shape(input,1,iw)||!self.operative_shape(report,1,rw){return Err(fail());}
        let mut p=Params::new();p.ptr(state.lo.device_ptr()).ptr(table.lo.device_ptr()).u32(table.rows as u32)
            .u32(sources as u32).u32(targets as u32).u32(grain.0).ptr(next.lo.device_ptr()).ptr(next.hi.device_ptr())
            .ptr(work.lo.device_ptr()).ptr(input.lo.device_ptr()).ptr(report.lo.device_ptr())
            .ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane,"section_normal_material_enclosed_batch",1,self.launch.block_x,0,&mut p,"normal-enclosed-batch")
    }
    pub(crate) fn record_current_difference_section(
        &self,
        lane: &Lane<'_, 'c>,
        input: ResidentConstitutiveSection<'_, 'c>,
        source: &ResidentSection<'c>,
        observed: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "current-difference-section",
            what: "incompatible current path and local comparison support".into(),
        };
        let rows = input
            .rows()
            .checked_sub(2)
            .filter(|r| *r > 0)
            .ok_or_else(fail)?;
        let width = input.components();
        let source_width = width
            .checked_mul(3)
            .and_then(|w| w.checked_add(1))
            .ok_or_else(fail)?;
        if !self.operative_shape(
            input.section,
            input.rows(),
            width + usize::from(input.rational),
        ) || !self.operative_shape(source, rows, source_width)
            || !self.operative_shape(observed, rows, width + 1)
            || [input.section, source, observed].iter().any(|s| {
                s.rows
                    .checked_mul(s.width)
                    .is_none_or(|n| n > u32::MAX as usize)
            })
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(input.section.lo.device_ptr())
            .ptr(input.section.hi.device_ptr())
            .u32(width as u32)
            .u32(input.section.width as u32)
            .u32(u32::from(input.rational))
            .u32(rows as u32)
            .ptr(source.lo.device_ptr())
            .ptr(source.hi.device_ptr())
            .ptr(observed.lo.device_ptr())
            .ptr(observed.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_current_difference_section",
            rows * width,
            &mut p,
            "current-difference-section",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_normal_material_section(
        &self,
        lane: &Lane<'_, 'c>,
        state: &ResidentSection<'c>,
        source: ResidentConstitutiveSection<'_, 'c>,
        observed: ResidentConstitutiveSection<'_, 'c>,
        sources: usize,
        targets: usize,
        grain: u32,
        next: &ResidentSection<'c>,
        before: &ResidentSection<'c>,
        after: &ResidentSection<'c>,
        work: &ResidentSection<'c>,
        input: &ResidentSection<'c>,
        report: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "normal-material-section",
            what: "incompatible source/return section and normal chart".into(),
        };
        let d = sources.checked_mul(2).ok_or_else(fail)?;
        let r = targets.checked_mul(2).ok_or_else(fail)?;
        let sw = normal_feature_state_words(sources, targets).ok_or_else(fail)?;
        let rw = normal_feature_report_words(sources, targets).ok_or_else(fail)?;
        let ww = normal_feature_workspace_words(sources, targets).ok_or_else(fail)?;
        let iw = d
            .checked_add(1)
            .and_then(|n| n.checked_mul(4))
            .and_then(|n| targets.checked_mul(3).and_then(|t| n.checked_add(t)))
            .ok_or_else(fail)?;
        let rows = source.rows();
        let bw = r
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(fail)?;
        if sources == 0
            || targets == 0
            || rows == 0
            || rows != observed.rows()
            || !(1..=120).contains(&grain)
            || d != source.components()
            || r != observed.components()
            || [source.section, observed.section, before, after]
                .iter()
                .any(|s| {
                    s.rows
                        .checked_mul(s.width)
                        .is_none_or(|n| n > u32::MAX as usize)
                })
            || !self.operative_shape(source.section, rows, d + usize::from(source.rational))
            || !self.operative_shape(observed.section, rows, r + usize::from(observed.rational))
            || !self.operative_shape(state, 1, sw)
            || !self.operative_shape(next, 1, sw)
            || !self.operative_shape(before, rows, bw)
            || !self.operative_shape(after, rows, bw)
            || !self.operative_shape(work, 1, ww)
            || !self.operative_shape(input, 1, iw)
            || !self.operative_shape(report, 1, rw)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(state.lo.device_ptr());
        for v in [source, observed] {
            p.ptr(v.section.lo.device_ptr())
                .ptr(v.section.hi.device_ptr())
                .u32(v.section.width as u32)
                .u32(u32::from(v.rational));
        }
        p.u32(rows as u32)
            .u32(sources as u32)
            .u32(targets as u32)
            .u32(grain);
        for s in [next, before, after] {
            p.ptr(s.lo.device_ptr()).ptr(s.hi.device_ptr());
        }
        p.ptr(work.lo.device_ptr())
            .ptr(input.lo.device_ptr())
            .ptr(report.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_material_section_sources",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-material-section",
        )
    }
}
