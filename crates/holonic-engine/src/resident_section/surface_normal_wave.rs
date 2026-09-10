use super::*;
use crate::native_ecology::constitutive_fibre::{
    normal_material_state_words, ResidentConstitutiveCurrent,
};
impl<'c> ResidentSurface<'c> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_normal_wave_seed(
        &self,
        lane: &Lane<'_, 'c>,
        p: ResidentConstitutiveCurrent<'_, 'c>,
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
            || p.width != r
            || c.width != r
            || pw > u32::MAX as usize
            || !self.operative_shape(seed, 2, r + 1)
            || !self.operative_shape(bound, 1, 2 * (2 * r + 1))
            || !self.operative_shape(previous, 1, 2 * (r + 1))
            || !self.operative_shape(current, 1, 2 * (r + 1))
            || !self.operative_shape(power, 1, pw)
            || !self.operative_shape(meta, 1, 8)
        {
            return Err(fail());
        }
        self.validate_constitutive_current_view(p)?;
        self.validate_constitutive_current_view(c)?;
        let mut params = Params::new();
        for v in [p, c] {
            params
                .ptr(v.section.lo.device_ptr())
                .ptr(v.section.hi.device_ptr())
                .u32(v.offset as u32)
                .u32(v.denominator.map_or(u32::MAX, |d| d as u32))
                .u32(v.disposition.map_or(u32::MAX, |d| d as u32));
        }
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
            "section_normal_wave_evaluate",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-wave-evaluate",
        )
    }
}
