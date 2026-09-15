use super::*;
use crate::native_ecology::constitutive_fibre::normal_feature_state_words;
use crate::native_ecology::constitutive_fibre::{
    ResidentConstitutiveCurrent, ResidentNormalEnclosureView, ResidentNormalInput,
};
impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_normal_applied_condition(
        &self,
        lane: &Lane<'_, 'c>,
        state: &ResidentSection<'c>,
        source: ResidentNormalEnclosureView<'_, 'c>,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
        targets: usize,
        joint: Option<(usize, ResidentNormalEnclosureView<'_, 'c>)>,
        identity: bool,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        if identity && (joint.is_some() || source.width != 2*targets) { return Err(fail()); }
        self.validate_normal_input(source.into(), source.grain.0)?;
        self.validate_normal_input(ResidentNormalInput::Point(condition), source.grain.0)?;
        let d = joint.map_or(source.width, |(d, _)| d);
        let tail = if joint.is_some() {
            source.width.checked_sub(d).ok_or_else(fail)?
        } else {
            0
        };
        let external = joint.map_or(source, |(_, external)| external);
        if joint.is_some() {
            self.validate_normal_input(external.into(), source.grain.0)?;
            if external.width != 2 * targets || d == 0 || d % 2 != 0 || tail % 2 != 0 {
                return Err(fail());
            }
        }
        let k = condition.width;
        let features = d
            .checked_mul(k / 2)
            .and_then(|v| v.checked_add(d)?.checked_add(k))
            .ok_or_else(fail)?;
        let words = normal_feature_state_words(features / 2, targets).ok_or_else(fail)?;
        let output_words = targets
            .checked_mul(2)
            .and_then(|v| v.checked_add(tail)?.checked_add(1)?.checked_mul(2))
            .ok_or_else(fail)?;
        if d == 0
            || k == 0
            || d % 2 != 0
            || k % 2 != 0
            || features > u32::MAX as usize
            || targets > u32::MAX as usize
            || !self.operative_shape(state, 1, words)
            || !self.operative_shape(out, 1, output_words)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(state.lo.device_ptr())
            .ptr(state.hi.device_ptr())
            .ptr(source.section.lo.device_ptr())
            .ptr(source.section.hi.device_ptr())
            .u32(source.offset as u32)
            .u32(d as u32)
            .u32(source.width as u32)
            .ptr(external.section.lo.device_ptr())
            .ptr(external.section.hi.device_ptr())
            .u32(external.offset as u32)
            .u32(if identity { 2 } else { u32::from(joint.is_some()) })
            .ptr(condition.section.lo.device_ptr())
            .ptr(condition.section.hi.device_ptr())
            .u32(condition.offset as u32)
            .u32(condition.denominator.map_or(u32::MAX, |v| v as u32))
            .u32(condition.disposition.map_or(u32::MAX, |v| v as u32))
            .u32(k as u32)
            .u32(targets as u32)
            .u32(source.grain.0)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_applied_condition",
            1,
            1,
            0,
            &mut p,
            "normal-applied-condition",
        )
    }
}
