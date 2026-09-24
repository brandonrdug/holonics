use super::*;
use crate::native_ecology::constitutive_fibre::{ResidentNormalEnclosureView, ResidentNormalInput};

impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_normal_held_section(
        &self,
        lane: &Lane<'_, 'c>,
        given: ResidentNormalEnclosureView<'_, 'c>,
        generated: ResidentNormalEnclosureView<'_, 'c>,
        held: &ResidentSection<'c>,
        aliased: bool,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        self.validate_normal_input(ResidentNormalInput::Enclosed(given), given.grain.0)?;
        self.validate_normal_input(ResidentNormalInput::Enclosed(generated), generated.grain.0)?;
        let complexes = given.width / 2;
        if given
            .width
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .and_then(|n| n.checked_add(given.offset.max(generated.offset)))
            .is_none_or(|n| n > u32::MAX as usize)
            || given.width == 0
            || given.width % 2 != 0
            || generated.width != given.width
            || given.grain != generated.grain
            || !std::ptr::eq(given.surface, generated.surface)
            || held.rows != 1
            || held.width != complexes
            || held.grain.0 != 0
            || !std::ptr::eq(held.surface, self)
            || !self.operative_shape(out, 1, 2 * (given.width + 1))
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for v in [given, generated] {
            p.ptr(v.section.lo.device_ptr())
                .ptr(v.section.hi.device_ptr())
                .u32(v.offset as u32);
        }
        p.ptr(held.lo.device_ptr())
            .ptr(held.hi.device_ptr())
            .u32(complexes as u32)
            .u32(u32::from(aliased))
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_held_section",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "normal-held-section",
        )
    }
}
