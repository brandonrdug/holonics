use super::*;
use crate::native_ecology::constitutive_fibre::{ResidentNormalEnclosureView, ResidentNormalInput};

impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_normal_enclosure_sum(
        &self,
        lane: &Lane<'_, 'c>,
        left: ResidentNormalEnclosureView<'_, 'c>,
        right: ResidentNormalEnclosureView<'_, 'c>,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        self.validate_normal_input(ResidentNormalInput::Enclosed(left), left.grain.0)?;
        self.validate_normal_input(ResidentNormalInput::Enclosed(right), right.grain.0)?;
        let valid = |v: ResidentNormalEnclosureView<'_, 'c>| {
            v.width > 0
                && v.width % 2 == 0
                && v.offset % 2 == 0
                && v.offset <= u32::MAX as usize
                && v.width <= u32::MAX as usize
                && std::ptr::eq(v.surface, self)
                && v.section.grain().0 == 0
                && v.width
                    .checked_add(1)
                    .and_then(|n| n.checked_mul(2))
                    .and_then(|span| v.offset.checked_add(span))
                    .is_some_and(|end| {
                        v.section
                            .rows()
                            .checked_mul(v.section.width())
                            .is_some_and(|total| end <= total)
                    })
        };
        if !valid(left)
            || !valid(right)
            || left.width != right.width
            || left.grain != right.grain
            || left
                .width
                .checked_add(1)
                .and_then(|n| n.checked_mul(2))
                .is_none_or(|words| !self.operative_shape(out, 1, words))
        {
            return Err(fail());
        }
        let mut params = Params::new();
        params
            .ptr(left.section.lo.device_ptr())
            .ptr(left.section.hi.device_ptr())
            .u32(left.offset as u32)
            .ptr(right.section.lo.device_ptr())
            .ptr(right.section.hi.device_ptr())
            .u32(right.offset as u32)
            .u32(left.width as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_enclosure_sum",
            1,
            self.launch.block_x,
            0,
            &mut params,
            "normal-enclosure-sum",
        )
    }
}
