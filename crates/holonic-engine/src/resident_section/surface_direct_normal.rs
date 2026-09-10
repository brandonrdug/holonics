use super::*;
use crate::native_ecology::constitutive_fibre::{
    normal_material_report_words, normal_material_state_words, normal_material_workspace_words,
    ResidentConstitutiveCurrent, ResidentNormalInput,
};
impl<'c> ResidentSurface<'c> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_normal_refine(
        &self,
        lane: &Lane<'_, 'c>,
        old: &ResidentSection<'c>,
        roots: usize,
        targets: usize,
        old_grain: u32,
        grain: u32,
        next: &ResidentSection<'c>,
        work: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let sw = normal_material_state_words(roots, targets).ok_or_else(fail)?;
        let ww = normal_material_workspace_words(roots, targets).ok_or_else(fail)?;
        if roots == 0
            || targets == 0
            || grain <= old_grain
            || grain > 120
            || roots > u32::MAX as usize / 6
            || targets > u32::MAX as usize / 2
            || !self.operative_shape(old, 1, sw)
            || !self.operative_shape(next, 1, sw)
            || !self.operative_shape(work, 1, ww)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(old.lo.device_ptr())
            .u32(roots as u32)
            .u32(targets as u32)
            .u32(old_grain)
            .u32(grain)
            .ptr(next.lo.device_ptr())
            .ptr(next.hi.device_ptr())
            .ptr(work.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_refine",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-refine",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_direct_normal_material(
        &self,
        lane: &Lane<'_, 'c>,
        state: &ResidentSection<'c>,
        source: ResidentNormalInput<'_, 'c>,
        observed: Option<ResidentConstitutiveCurrent<'_, 'c>>,
        roots: usize,
        targets: usize,
        grain: u32,
        next: Option<&ResidentSection<'c>>,
        before: &ResidentSection<'c>,
        after: Option<&ResidentSection<'c>>,
        work: &ResidentSection<'c>,
        input: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "direct-normal-material",
            what: "incompatible three-port current, output or normal-state chart".into(),
        };
        let d = roots.checked_mul(6).ok_or_else(fail)?;
        let r = targets.checked_mul(2).ok_or_else(fail)?;
        let state_words = normal_material_state_words(roots, targets).ok_or_else(fail)?;
        let report_words = normal_material_report_words(roots, targets).ok_or_else(fail)?;
        let work_words = normal_material_workspace_words(roots, targets).ok_or_else(fail)?;
        let input_words = d
            .checked_add(1)
            .and_then(|v| v.checked_mul(4))
            .and_then(|v| targets.checked_mul(3).and_then(|t| v.checked_add(t)))
            .ok_or_else(fail)?;
        if roots == 0
            || targets == 0
            || d > u32::MAX as usize
            || r > u32::MAX as usize
            || !(1..=120).contains(&grain)
            || source.width() != d
            || observed.is_some_and(|v| v.width != r)
            || observed.is_some() != next.is_some()
            || observed.is_some() != after.is_some()
            || !self.operative_shape(state, 1, state_words)
            || !self.operative_shape(before, 1, report_words)
            || !self.operative_shape(work, 1, work_words)
            || !self.operative_shape(input, 1, input_words)
            || next.is_some_and(|s| !self.operative_shape(s, 1, state_words))
            || after.is_some_and(|s| !self.operative_shape(s, 1, report_words))
        {
            return Err(fail());
        }
        match source {
            ResidentNormalInput::Point(v) => self.validate_constitutive_current_view(v)?,
            ResidentNormalInput::Enclosed(v) => {
                if v.grain.0 != grain
                    || v.section.grain.0 != 0
                    || !std::ptr::eq(v.section.surface, self)
                    || v.offset % 2 != 0
                    || v.offset
                        .checked_add(2 * (d + 1))
                        .is_none_or(|end| end > v.section.rows * v.section.width)
                {
                    return Err(fail());
                }
            }
        }
        if let Some(v) = observed {
            self.validate_constitutive_current_view(v)?;
        }
        let mut p = Params::new();
        p.ptr(state.lo.device_ptr());
        match source {
            ResidentNormalInput::Point(v) => {
                p.ptr(v.section.lo.device_ptr())
                    .ptr(v.section.hi.device_ptr())
                    .u32(v.offset as u32)
                    .u32(v.denominator.map_or(u32::MAX, |n| n as u32))
                    .u32(v.disposition.map_or(u32::MAX, |n| n as u32))
                    .u32(0);
            }
            ResidentNormalInput::Enclosed(v) => {
                p.ptr(v.section.lo.device_ptr())
                    .ptr(v.section.hi.device_ptr())
                    .u32(v.offset as u32)
                    .u32(u32::MAX)
                    .u32(u32::MAX)
                    .u32(1);
            }
        }
        if let Some(v) = observed {
            p.ptr(v.section.lo.device_ptr())
                .ptr(v.section.hi.device_ptr())
                .u32(v.offset as u32)
                .u32(v.denominator.map_or(u32::MAX, |n| n as u32))
                .u32(v.disposition.map_or(u32::MAX, |n| n as u32));
        } else {
            p.ptr(before.lo.device_ptr())
                .ptr(before.hi.device_ptr())
                .u32(0)
                .u32(u32::MAX)
                .u32(u32::MAX);
        }
        p.u32(roots as u32)
            .u32(targets as u32)
            .u32(grain)
            .u32(u32::from(observed.is_some()));
        // These aliases are unused by the read-only branch; it never writes state or after.
        for section in [next.unwrap_or(before), before, after.unwrap_or(before)] {
            p.ptr(section.lo.device_ptr()).ptr(section.hi.device_ptr());
        }
        p.ptr(work.lo.device_ptr())
            .ptr(input.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_direct_normal_material",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "direct-normal-material",
        )
    }
}
