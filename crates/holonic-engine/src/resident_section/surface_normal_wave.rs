use super::*;
use crate::native_ecology::constitutive_fibre::{
    ResidentConstitutiveCurrent, ResidentNormalInput, ResidentNormalEnclosureView, normal_material_report_words,
    normal_material_state_words, normal_material_workspace_words,
};
impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_normal_enclosure_pair(&self,lane:&Lane<'_, 'c>,
        left:ResidentNormalEnclosureView<'_, 'c>,right:ResidentNormalEnclosureView<'_, 'c>,
        kind:u32,out:&ResidentSection<'c>)->Result<(),ResidentRefusal>{
        let fail=||Self::operative_error();
        let valid=|v:ResidentNormalEnclosureView<'_, 'c>| {
            v.components()>0&&v.components()%2==0&&v.offset%2==0
                &&v.offset<=u32::MAX as usize&&v.components()<u32::MAX as usize/4
                &&std::ptr::eq(v.surface,self)&&v.section.grain().0==0
                &&v.offset.checked_add(2*(v.components()+1)).is_some_and(|end|end<=v.section.rows()*v.section.width())
        };
        let width=if kind==1 {left.components().checked_add(right.components()).ok_or_else(fail)?}else{left.components()};
        if kind>2||!valid(left)||!valid(right)||left.grain()!=right.grain()
            ||(kind==2&&left.components()!=right.components())||!self.operative_shape(out,1,2*(width+1)){return Err(fail());}
        let mut p=Params::new();
        p.ptr(left.section.lo.device_ptr()).ptr(left.section.hi.device_ptr()).u32(left.offset as u32).u32(left.components() as u32)
            .ptr(right.section.lo.device_ptr()).ptr(right.section.hi.device_ptr()).u32(right.offset as u32).u32(right.components() as u32).u32(kind)
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr()).ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane,"section_normal_enclosure_pair",1,self.launch.block_x,0,&mut p,"normal-enclosure-receiver")
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_normal_source_actuation(
        &self,
        lane: &Lane<'_, 'c>,
        material: &ResidentSection<'c>,
        joint: &ResidentSection<'c>,
        source: crate::native_ecology::constitutive_fibre::ResidentConstitutiveSection<'_, 'c>,
        n: usize,
        grain: u32,
        out: &ResidentSection<'c>,
        anchors: &ResidentSection<'c>,
        frame: &ResidentSection<'c>,
        work: &ResidentSection<'c>,
        reference: bool,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let sw = normal_material_state_words(n, n).ok_or_else(fail)?;
        let r = n.checked_mul(2).filter(|r| *r > 0).ok_or_else(fail)?;
        let w = r.checked_mul(2).ok_or_else(fail)?;
        let d = r.checked_mul(3).ok_or_else(fail)?;
        if !(1..=120).contains(&grain)
            || sw > u32::MAX as usize
            || source.rows() < 2
            || source.components() != r
            || source
                .rows()
                .checked_mul(source.section.width())
                .is_none_or(|v| v > u32::MAX as usize)
            || !std::ptr::eq(source.section.surface, self)
            || source.section.grain.0 != 0
            || !self.operative_shape(material, 1, sw)
            || !self.operative_shape(joint, 1, 2 * (w + 1))
            || !self.operative_shape(out, 1, 2 * (w + 1))
            || !self.operative_shape(anchors, 1, 2 * (2 * (w + 1) + (r + 1)))
            || !self.operative_shape(frame, 1, 4 * (d + 1))
            || !self.operative_shape(work, 1, 4 * n)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(material.lo.device_ptr())
            .ptr(joint.lo.device_ptr())
            .ptr(source.section.lo.device_ptr())
            .ptr(source.section.hi.device_ptr())
            .u32(source.rows() as u32)
            .u32(u32::from(source.rational))
            .u32(n as u32)
            .u32(grain)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(anchors.lo.device_ptr())
            .ptr(frame.lo.device_ptr())
            .ptr(work.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            if reference { "section_normal_source_actuation" } else { "section_normal_source_actuation_applied" },
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-source-actuation",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_normal_wave_joint_seed(
        &self,
        lane: &Lane<'_, 'c>,
        joint: &ResidentSection<'c>,
        n: usize,
        grain: u32,
        previous: &ResidentSection<'c>,
        current: &ResidentSection<'c>,
        power: &ResidentSection<'c>,
        meta: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let r = n.checked_mul(2).filter(|r| *r > 0).ok_or_else(fail)?;
        let pw = r
            .checked_mul(r)
            .and_then(|v| v.checked_mul(4))
            .ok_or_else(fail)?;
        if !(1..=120).contains(&grain)
            || pw > u32::MAX as usize
            || !self.operative_shape(joint, 1, 2 * (2 * r + 1))
            || !self.operative_shape(previous, 1, 2 * (r + 1))
            || !self.operative_shape(current, 1, 2 * (r + 1))
            || !self.operative_shape(power, 1, pw)
            || !self.operative_shape(meta, 1, 8)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(joint.lo.device_ptr())
            .ptr(joint.hi.device_ptr())
            .u32(n as u32)
            .u32(grain);
        for v in [previous, current, power, meta] {
            p.ptr(v.lo.device_ptr()).ptr(v.hi.device_ptr());
        }
        p.ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_wave_joint_seed",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-wave-joint-seed",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_normal_wave_receive(
        &self,
        lane: &Lane<'_, 'c>,
        material: &ResidentSection<'c>,
        joint: &ResidentSection<'c>,
        received: ResidentConstitutiveCurrent<'_, 'c>,
        n: usize,
        grain: u32,
        next: &ResidentSection<'c>,
        report: &ResidentSection<'c>,
        work: &ResidentSection<'c>,
        input: &ResidentSection<'c>,
        reference: bool,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let r = n.checked_mul(2).filter(|r| *r > 0).ok_or_else(fail)?;
        let d = r.checked_mul(3).ok_or_else(fail)?;
        let sw = normal_material_state_words(n, n).ok_or_else(fail)?;
        let rw = normal_material_report_words(n, n).ok_or_else(fail)?;
        let ww = normal_material_workspace_words(n, n).ok_or_else(fail)?;
        if !(1..=120).contains(&grain)
            || sw > u32::MAX as usize
            || received.width != r
            || !self.operative_shape(material, 1, sw)
            || !self.operative_shape(next, 1, sw)
            || !self.operative_shape(joint, 1, 2 * (2 * r + 1))
            || !self.operative_shape(report, 1, rw)
            || !self.operative_shape(work, 1, ww)
            || !self.operative_shape(input, 1, 4 * (d + 1))
        {
            return Err(fail());
        }
        self.validate_constitutive_current_view(received)?;
        let mut p = Params::new();
        p.ptr(material.lo.device_ptr())
            .ptr(joint.lo.device_ptr())
            .ptr(received.section.lo.device_ptr())
            .ptr(received.section.hi.device_ptr())
            .u32(received.offset as u32)
            .u32(received.denominator.map_or(u32::MAX, |v| v as u32))
            .u32(received.disposition.map_or(u32::MAX, |v| v as u32))
            .u32(n as u32)
            .u32(grain);
        for s in [next, report] {
            p.ptr(s.lo.device_ptr()).ptr(s.hi.device_ptr());
        }
        p.ptr(work.lo.device_ptr())
            .ptr(input.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            if reference { "section_normal_wave_receive" } else { "section_normal_wave_receive_applied" },
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-wave-receive",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_normal_wave_comparison(
        &self,
        lane: &Lane<'_, 'c>,
        material: &ResidentSection<'c>,
        producing: &ResidentSection<'c>,
        joint: &ResidentSection<'c>,
        received: ResidentConstitutiveCurrent<'_, 'c>,
        n: usize,
        grain: u32,
        producing_reference: bool,
        updated_reference: bool,
        next: &ResidentSection<'c>,
        report: &ResidentSection<'c>,
        work: &ResidentSection<'c>,
        input: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let r = n.checked_mul(2).filter(|r| *r > 0).ok_or_else(fail)?;
        let d = r.checked_mul(3).ok_or_else(fail)?;
        let sw = normal_material_state_words(n, n).ok_or_else(fail)?;
        let rw = normal_material_report_words(n, n).ok_or_else(fail)?;
        let ww = normal_material_workspace_words(n, n).ok_or_else(fail)?;
        if !(1..=120).contains(&grain)
            || sw > u32::MAX as usize
            || received.width != r
            || !self.operative_shape(material, 1, sw)
            || !self.operative_shape(producing, 1, sw)
            || !self.operative_shape(next, 1, sw)
            || !self.operative_shape(joint, 1, 2 * (2 * r + 1))
            || !self.operative_shape(report, 1, rw)
            || !self.operative_shape(work, 1, ww)
            || !self.operative_shape(input, 1, 4 * (d + 1))
        {
            return Err(fail());
        }
        self.validate_constitutive_current_view(received)?;
        let mut p = Params::new();
        p.ptr(material.lo.device_ptr())
            .ptr(producing.lo.device_ptr())
            .ptr(joint.lo.device_ptr())
            .ptr(received.section.lo.device_ptr())
            .ptr(received.section.hi.device_ptr())
            .u32(received.offset as u32)
            .u32(received.denominator.map_or(u32::MAX, |v| v as u32))
            .u32(received.disposition.map_or(u32::MAX, |v| v as u32))
            .u32(n as u32)
            .u32(grain)
            .u32(u32::from(producing_reference))
            .u32(u32::from(updated_reference));
        for s in [next, report] {
            p.ptr(s.lo.device_ptr()).ptr(s.hi.device_ptr());
        }
        p.ptr(work.lo.device_ptr())
            .ptr(input.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_wave_comparison",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-wave-comparison",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_normal_wave_seed(
        &self,
        lane: &Lane<'_, 'c>,
        p: ResidentNormalInput<'_, 'c>,
        c: ResidentConstitutiveCurrent<'_, 'c>,
        n: usize,
        grain: u32,
        seed: &ResidentSection<'c>,
        bound: &ResidentSection<'c>,
        previous: &ResidentSection<'c>,
        current: &ResidentSection<'c>,
        power: &ResidentSection<'c>,
        meta: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let r = n.checked_mul(2).filter(|r| *r > 0).ok_or_else(fail)?;
        let pw = r
            .checked_mul(r)
            .and_then(|v| v.checked_mul(4))
            .ok_or_else(fail)?;
        if !(1..=120).contains(&grain)
            || p.width() != r
            || c.width != r
            || pw > u32::MAX as usize
            || !self.operative_shape(
                seed,
                if matches!(p, ResidentNormalInput::Enclosed(_)) {
                    3
                } else {
                    2
                },
                r + 1,
            )
            || !self.operative_shape(bound, 1, 2 * (2 * r + 1))
            || !self.operative_shape(previous, 1, 2 * (r + 1))
            || !self.operative_shape(current, 1, 2 * (r + 1))
            || !self.operative_shape(power, 1, pw)
            || !self.operative_shape(meta, 1, 8)
        {
            return Err(fail());
        }
        let mut params = Params::new();
        match p {
            ResidentNormalInput::Point(v) => {
                self.validate_constitutive_current_view(v)?;
                params
                    .ptr(v.section.lo.device_ptr())
                    .ptr(v.section.hi.device_ptr())
                    .u32(v.offset as u32)
                    .u32(v.denominator.map_or(u32::MAX, |d| d as u32))
                    .u32(v.disposition.map_or(u32::MAX, |d| d as u32))
                    .u32(0);
            }
            ResidentNormalInput::Enclosed(v) => {
                if v.grain.0 != grain
                    || v.offset % 2 != 0
                    || v.section.grain.0 != 0
                    || !std::ptr::eq(v.section.surface, self)
                    || v.offset
                        .checked_add(2 * (r + 1))
                        .is_none_or(|end| end > v.section.count() || end > u32::MAX as usize)
                {
                    return Err(fail());
                }
                params
                    .ptr(v.section.lo.device_ptr())
                    .ptr(v.section.hi.device_ptr())
                    .u32(v.offset as u32)
                    .u32(u32::MAX)
                    .u32(u32::MAX)
                    .u32(1);
            }
        }
        self.validate_constitutive_current_view(c)?;
        params
            .ptr(c.section.lo.device_ptr())
            .ptr(c.section.hi.device_ptr())
            .u32(c.offset as u32)
            .u32(c.denominator.map_or(u32::MAX, |d| d as u32))
            .u32(c.disposition.map_or(u32::MAX, |d| d as u32));
        params.u32(n as u32).u32(grain);
        for s in [seed, bound, previous, current, power, meta] {
            params.ptr(s.lo.device_ptr()).ptr(s.hi.device_ptr());
        }
        params
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_wave_seed",
            1,
            self.launch.block_x,
            0,
            &mut params,
            "normal-wave-seed",
        )
    }
    pub(crate) fn record_normal_wave_power(
        &self,
        lane: &Lane<'_, 'c>,
        material: &ResidentSection<'c>,
        prior: &ResidentSection<'c>,
        n: usize,
        grain: u32,
        next: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let d = n.checked_mul(2).filter(|n| *n > 0).ok_or_else(fail)?;
        let cells = d.checked_mul(d).ok_or_else(fail)?;
        let words = cells.checked_mul(4).ok_or_else(fail)?;
        let mw = normal_material_state_words(n, n).ok_or_else(fail)?;
        if !(1..=120).contains(&grain)
            || words > u32::MAX as usize
            || !self.operative_shape(material, 1, mw)
            || !self.operative_shape(prior, 1, words)
            || !self.operative_shape(next, 1, words)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(material.lo.device_ptr())
            .ptr(prior.lo.device_ptr())
            .u32(n as u32)
            .u32(grain)
            .ptr(next.lo.device_ptr())
            .ptr(next.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_normal_wave_power",
            cells,
            &mut p,
            "normal-wave-power",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_normal_wave_evaluate(
        &self,
        lane: &Lane<'_, 'c>,
        material: &ResidentSection<'c>,
        power: &ResidentSection<'c>,
        seed: &ResidentSection<'c>,
        old_meta: &ResidentSection<'c>,
        n: usize,
        grain: u32,
        steps: u64,
        meta: &ResidentSection<'c>,
        joint: &ResidentSection<'c>,
        current: &ResidentSection<'c>,
        work: &ResidentSection<'c>,
        reference: bool,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let d = n.checked_mul(2).filter(|n| *n > 0).ok_or_else(fail)?;
        let pw = d
            .checked_mul(d)
            .and_then(|v| v.checked_mul(4))
            .ok_or_else(fail)?;
        let mw = normal_material_state_words(n, n).ok_or_else(fail)?;
        if steps == 0
            || !(1..=120).contains(&grain)
            || pw > u32::MAX as usize
            || !self.operative_shape(material, 1, mw)
            || !self.operative_shape(power, 1, pw)
            || !self.operative_shape(seed, 1, 2 * (2 * d + 1))
            || !self.operative_shape(old_meta, 1, 8)
            || !self.operative_shape(meta, 1, 8)
            || !self.operative_shape(joint, 1, 2 * (2 * d + 1))
            || !self.operative_shape(current, 1, 2 * (d + 1))
            || !self.operative_shape(work, 1, 6 * d)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(material.lo.device_ptr())
            .ptr(power.lo.device_ptr())
            .ptr(seed.lo.device_ptr())
            .ptr(old_meta.lo.device_ptr())
            .u32(n as u32)
            .u32(grain)
            .u64(steps);
        for s in [meta, joint, current] {
            p.ptr(s.lo.device_ptr()).ptr(s.hi.device_ptr());
        }
        p.ptr(work.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            if reference { "section_normal_wave_evaluate" } else { "section_normal_wave_evaluate_applied" },
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-wave-evaluate",
        )
    }
}
