use super::*;
use crate::native_ecology::constitutive_fibre::{
    normal_feature_report_words, normal_feature_state_words, normal_feature_workspace_words,
    ResidentConstitutiveSection, ResidentNormalEnclosureView, ResidentNormalInput,
};
impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_normal_enclosure_section(
        &self,
        lane: &Lane<'_, 'c>,
        source: ResidentConstitutiveSection<'_, 'c>,
        grain: ResidentGrain,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "normal-enclosure-section",
            what: "incompatible point section and enclosure chart".into(),
        };
        let width = source.components();
        let stride = width
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(fail)?;
        let rows = source.rows();
        if rows == 0
            || width == 0
            || width % 2 != 0
            || source.section.grain().0 != 0
            || !(1..=120).contains(&grain.0)
            || !std::ptr::eq(source.section.surface(), self)
            || !self.operative_shape(
                source.section,
                rows,
                source.width + usize::from(source.rational),
            )
            || !self.operative_shape(out, rows, stride)
            || source.section.width() > u32::MAX as usize
            || rows > u32::MAX as usize
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(source.section.lo.device_ptr())
            .ptr(source.section.hi.device_ptr())
            .u32(source.section.width() as u32)
            .u32(u32::from(source.rational))
            .u32(rows as u32)
            .u32(width as u32)
            .u32(grain.0)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_enclosure_section",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-enclosure-section",
        )
    }

    pub(crate) fn record_normal_enclosure_sum_section(
        &self,
        lane: &Lane<'_, 'c>,
        left: ResidentNormalEnclosureView<'_, 'c>,
        right: ResidentNormalEnclosureView<'_, 'c>,
        rows: usize,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let valid = |view: ResidentNormalEnclosureView<'_, 'c>| {
            view.width > 0
                && view.width % 2 == 0
                && view.offset % 2 == 0
                && view.offset <= u32::MAX as usize
                && view.width <= u32::MAX as usize
                && std::ptr::eq(view.surface, self)
                && view.grain.0 >= 1
                && view.grain.0 <= 120
                && view.section.grain().0 == 0
                && view
                    .width
                    .checked_add(1)
                    .and_then(|n| n.checked_mul(2))
                    .and_then(|span| view.offset.checked_add(span.checked_mul(rows)?))
                    .is_some_and(|end| {
                        view.section
                            .rows()
                            .checked_mul(view.section.width())
                            .is_some_and(|total| end <= total)
                    })
        };
        let width = left.width;
        let stride = width
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(fail)?;
        if rows == 0
            || rows > u32::MAX as usize
            || !valid(left)
            || !valid(right)
            || left.width != right.width
            || left.grain != right.grain
            || !self.operative_shape(out, rows, stride)
        {
            return Err(fail());
        }
        let left_stride = stride;
        let right_stride = stride;
        if left.offset.checked_add(rows.checked_mul(left_stride).ok_or_else(fail)?).is_none()
            || right.offset.checked_add(rows.checked_mul(right_stride).ok_or_else(fail)?).is_none()
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(left.section.lo.device_ptr())
            .ptr(left.section.hi.device_ptr())
            .u32(left.offset as u32)
            .ptr(right.section.lo.device_ptr())
            .ptr(right.section.hi.device_ptr())
            .u32(right.offset as u32)
            .u32(left_stride as u32)
            .u32(right_stride as u32)
            .u32(rows as u32)
            .u32(width as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_enclosure_sum_section",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-enclosure-sum-section",
        )
    }

    pub(crate) fn record_normal_enclosure_scatter_section(
        &self,
        lane: &Lane<'_, 'c>,
        source: ResidentNormalEnclosureView<'_, 'c>,
        start: usize,
        count: usize,
        destinations: &ResidentSection<'c>,
        output_rows: usize,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let output_width = output_rows
            .checked_mul(count)
            .ok_or_else(fail)?;
        let output_stride = output_width
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(fail)?;
        let valid_source = source.width > 0
            && source.width % 2 == 0
            && source.offset % 2 == 0
            && source.offset <= u32::MAX as usize
            && source.width <= u32::MAX as usize
            && start % 2 == 0
            && count > 0
            && count % 2 == 0
            && start.checked_add(count).is_some_and(|end| end <= source.width)
            && source.grain.0 >= 1
            && source.grain.0 <= 120
            && source.section.grain().0 == 0
            && std::ptr::eq(source.surface, self)
            && source.offset.checked_add(source.section.rows().checked_mul(source.section.width()).unwrap_or(usize::MAX)).is_some_and(|end| {
                source.section.rows().checked_mul(source.section.width()).is_some_and(|total| end <= total)
            });
        if !valid_source
            || source.section.rows() != destinations.rows()
            || output_rows == 0
            || output_rows > u32::MAX as usize
            || !std::ptr::eq(destinations.surface(), self)
            || destinations.width() != 1
            || destinations.grain().0 != 0
            || !self.operative_shape(destinations, destinations.rows(), 1)
            || !self.operative_shape(out, 1, output_stride)
            || destinations.rows() > u32::MAX as usize
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(source.section.lo.device_ptr())
            .ptr(source.section.hi.device_ptr())
            .u32(source.offset as u32)
            .u32(source.width as u32)
            .u32(source.section.rows() as u32)
            .u32(start as u32)
            .u32(count as u32)
            .ptr(destinations.lo.device_ptr())
            .ptr(destinations.hi.device_ptr())
            // The kernel's `dest_count` is the number of destination rows, one per source row.
            .u32(destinations.rows() as u32)
            .u32(output_rows as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_enclosure_scatter_section",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-enclosure-scatter-section",
        )
    }

    pub(crate) fn record_normal_enclosure_restrict_section(
        &self,
        lane: &Lane<'_, 'c>,
        source: ResidentNormalEnclosureView<'_, 'c>,
        start: usize,
        count: usize,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let source_stride = source
            .width
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(fail)?;
        let output_stride = count
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(fail)?;
        if source.width == 0
            || source.width % 2 != 0
            || start % 2 != 0
            || count == 0
            || count % 2 != 0
            || start.checked_add(count).is_none_or(|end| end > source.width)
            || source.grain.0 < 1
            || source.grain.0 > 120
            || source.section.grain().0 != 0
            || !std::ptr::eq(source.surface, self)
            || source.offset != 0
            || source.section.width() != source_stride
            || !self.operative_shape(out, source.section.rows(), output_stride)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(source.section.lo.device_ptr())
            .ptr(source.section.hi.device_ptr())
            .u32(source.width as u32)
            .u32(source.section.rows() as u32)
            .u32(start as u32)
            .u32(count as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_enclosure_restrict_section",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-enclosure-restrict-section",
        )
    }

    pub(crate) fn record_normal_applied_material_section(
        &self,
        lane: &Lane<'_, 'c>,
        state: &ResidentSection<'c>,
        source: ResidentConstitutiveSection<'_, 'c>,
        source_complex: usize,
        targets: usize,
        grain: u32,
        out: &ResidentSection<'c>,
        work: &ResidentSection<'c>,
        input: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "normal-applied-material-section",
            what: "incompatible source section and normal chart".into(),
        };
        let d = source_complex.checked_mul(2).ok_or_else(fail)?;
        let stride = targets
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .ok_or_else(fail)?;
        let sw = normal_feature_state_words(source_complex, targets).ok_or_else(fail)?;
        let ww = normal_feature_workspace_words(source_complex, targets).ok_or_else(fail)?;
        let iw = source_complex
            .checked_mul(2)
            .and_then(|n| n.checked_add(1)?.checked_mul(4)?.checked_add(3 * targets))
            .ok_or_else(fail)?;
        let rows = source.rows();
        let output_width = stride.checked_mul(2).ok_or_else(fail)?;
        if source_complex == 0
            || targets == 0
            || rows == 0
            || d != source.components()
            || !(1..=120).contains(&grain)
            || !self.operative_shape(
                source.section,
                rows,
                source.width + usize::from(source.rational),
            )
            || !self.operative_shape(state, 1, sw)
            || !self.operative_shape(out, rows, output_width)
            || !self.operative_shape(work, 1, ww)
            || !self.operative_shape(input, 1, iw)
            || source.section.rows.checked_mul(source.section.width).is_none_or(|n| n > u32::MAX as usize)
            || rows > u32::MAX as usize
            || source.section.width > u32::MAX as usize
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(state.lo.device_ptr())
            .ptr(source.section.lo.device_ptr())
            .ptr(source.section.hi.device_ptr())
            .u32(source.section.width as u32)
            .u32(u32::from(source.rational))
            .u32(rows as u32)
            .u32(source_complex as u32)
            .u32(targets as u32)
            .u32(grain)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(work.lo.device_ptr())
            .ptr(input.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_applied_material_section",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-applied-material-section",
        )
    }

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
