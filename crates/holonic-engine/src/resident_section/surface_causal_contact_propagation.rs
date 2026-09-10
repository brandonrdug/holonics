use super::*;

pub(crate) struct CausalPropagationLayout;
impl CausalPropagationLayout {
    const WIDE_WORDS: usize = std::mem::size_of::<i128>() / std::mem::size_of::<i64>();
    pub(crate) const HISTORY_WORDS: usize = 2 * Self::WIDE_WORDS + 1;
    pub(crate) const BEFORE: usize = 2;
    pub(crate) const OVERLAP: usize = Self::BEFORE + 4 * Self::WIDE_WORDS;
    pub(crate) const RADIUS: usize = Self::OVERLAP + 2 * Self::HISTORY_WORDS;
    pub(crate) const OVERLAP_ERROR: usize = Self::RADIUS + Self::WIDE_WORDS;
    pub(crate) const ROUNDS: usize =
        (Self::OVERLAP_ERROR + Self::HISTORY_WORDS).div_ceil(Self::WIDE_WORDS) * Self::WIDE_WORDS;
    pub(crate) const WORDS: usize = Self::ROUNDS + Self::WIDE_WORDS;
}

impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_operative_propagation_covector(&self,lane:&Lane<'_,'c>,paired:&ResidentSection<'c>,d:usize,count:usize,old_count:usize,out:&ResidentSection<'c>) -> Result<(),ResidentRefusal> {
        if old_count>count || d>u32::MAX as usize || count>u32::MAX as usize
            || !self.operative_shape(paired,1,2*(2*d+4*count+8)) || !self.operative_shape(out,1,2*(2*old_count+1)){return Err(Self::operative_error());}
        let mut p=Params::new();p.ptr(paired.lo.device_ptr()).u32(d as u32).u32(count as u32).u32(old_count as u32)
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr()).ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane,"section_field_operative_propagation_covector",(2*old_count+1).div_ceil(self.launch.block_x as usize),self.launch.block_x,0,&mut p,"operative-propagation-return")
    }
    pub(crate) fn record_operative_propagation_return(&self,lane:&Lane<'_,'c>,incoming:&ResidentSection<'c>,extra:&ResidentSection<'c>,d:usize,count:usize,old_count:usize,
        paired:&ResidentSection<'c>,bounds:&ResidentSection<'c>) -> Result<(),ResidentRefusal> {
        if old_count>count || d>u32::MAX as usize || count>u32::MAX as usize
            || !self.operative_shape(incoming,old_count.max(1),4) || !self.operative_shape(extra,1,4)
            || !self.operative_shape(paired,1,2*(2*d+4*count+8)) || !self.operative_shape(bounds,1,4){return Err(Self::operative_error());}
        let mut p=Params::new();p.ptr(incoming.lo.device_ptr()).ptr(extra.lo.device_ptr()).u32(d as u32).u32(count as u32).u32(old_count as u32)
            .ptr(paired.lo.device_ptr()).ptr(paired.hi.device_ptr()).ptr(bounds.lo.device_ptr()).ptr(bounds.hi.device_ptr())
            .ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane,"section_field_operative_propagation_return",(2*old_count).max(1).div_ceil(self.launch.block_x as usize),self.launch.block_x,0,&mut p,"operative-propagation-return")
    }
    pub(crate) fn record_operative_input_current_add(&self,lane:&Lane<'_,'c>,before:&ResidentSection<'c>,
        delta:&ResidentSection<'c>,count:usize,out:&ResidentSection<'c>) -> Result<(),ResidentRefusal> {
        if count>u32::MAX as usize || [before,delta,out].iter().any(|s|!self.operative_shape(s,count.max(1),4)){return Err(Self::operative_error());}
        let mut p=Params::new();p.ptr(before.lo.device_ptr()).ptr(delta.lo.device_ptr()).u32(count as u32)
            .ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr()).ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane,"section_field_operative_input_current_add",(2*count.max(1)).div_ceil(self.launch.block_x as usize),
            self.launch.block_x,0,&mut p,"operative-input-current")
    }
    pub(crate) fn record_causal_contact_pullback(
        &self,
        lane: &Lane<'_, 'c>,
        input: [&ResidentSection<'c>; 4],
        d: usize,
        count: usize,
        grain: u32,
        output: [&ResidentSection<'c>; 4],
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        if d == 0
            || d % 2 != 0
            || d > u32::MAX as usize
            || count > u32::MAX as usize
            || !(1..=120).contains(&grain)
            || input[0].rows<count.max(1) || !self.operative_shape(input[0], input[0].rows, 2 * d)
            || !self.operative_shape(input[1], 1, 4)
            || !self.operative_shape(input[2], count.max(1), CausalPropagationLayout::WORDS)
            || !self.operative_shape(input[3], 1, 2 * (2 * count + 1))
            || !self.operative_shape(output[0], count.max(1), 4)
            || !self.operative_shape(output[1], count.max(1), 4)
            || !self.operative_shape(output[2], count.max(1), 2)
            || !self.operative_shape(output[3], 1, 4)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for s in input {
            p.ptr(s.lo.device_ptr());
        }
        p.u32(d as u32).u32(count as u32).u32(grain);
        for s in output {
            p.ptr(s.lo.device_ptr()).ptr(s.hi.device_ptr());
        }
        p.ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_causal_contact_pullback",
            1,
            1,
            0,
            &mut p,
            "causal-contact-pullback",
        )
    }

    pub(crate) fn record_causal_contact_propagation(
        &self,
        lane: &Lane<'_, 'c>,
        births: &ResidentSection<'c>,
        input: [&ResidentSection<'c>; 3],
        d: usize,
        count: usize,
        grain: u32,
        current: &ResidentSection<'c>,
        bounds: &ResidentSection<'c>,
        trace: &ResidentSection<'c>,
        summary: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        if d == 0
            || d % 2 != 0
            || d > u32::MAX as usize
            || count > u32::MAX as usize
            || !(1..=120).contains(&grain)
            || !self.operative_shape(births, count.max(1), 2)
            || input[0].rows<count.max(1) || !self.operative_shape(input[0], input[0].rows, 2 * d)
            || !self.operative_shape(input[1], count.max(1), 4)
            || !self.operative_shape(input[2], 1, 4)
            || !self.operative_shape(current, count.max(1), 4)
            || !self.operative_shape(bounds, 1, 4)
            || !self.operative_shape(trace, count.max(1), CausalPropagationLayout::WORDS)
            || !self.operative_shape(summary, 1, 4)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(births.lo.device_ptr());
        for s in input {
            p.ptr(s.lo.device_ptr());
        }
        p.u32(d as u32).u32(count as u32).u32(grain);
        for s in [current, bounds, trace, summary] {
            p.ptr(s.lo.device_ptr()).ptr(s.hi.device_ptr());
        }
        p.ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_causal_contact_propagation",
            1,
            // One worker owns the dependent join word. Inactive full-block workers would
            // reserve the same wide-arithmetic registers without performing an operation.
            1,
            0,
            &mut p,
            "causal-contact-propagation",
        )
    }
}
