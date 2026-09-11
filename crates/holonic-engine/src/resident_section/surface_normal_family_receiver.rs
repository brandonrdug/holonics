use super::*;
use crate::native_ecology::constitutive_fibre::ResidentNormalEnclosureView;
impl<'c> ResidentSurface<'c> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_normal_family_receiver(
        &self,
        lane: &Lane<'_, 'c>,
        family: &ResidentSection<'c>,
        source_width: usize,
        anchor: ResidentNormalEnclosureView<'_, 'c>,
        roots: usize,
        joint: &ResidentSection<'c>,
        anchor_basis: &ResidentSection<'c>,
        vertical: &ResidentSection<'c>,
        graph: &ResidentSection<'c>,
        report: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let a = roots.checked_mul(4).ok_or_else(fail)?;
        let w = a.checked_mul(2).ok_or_else(fail)?;
        let t = w.checked_add(2).ok_or_else(fail)?;
        let fw = t
            .checked_mul(t)
            .and_then(|v| v.checked_add(t)?.checked_add(source_width)?.checked_add(4))
            .ok_or_else(fail)?;
        let rw = a
            .checked_mul(8)
            .and_then(|v| v.checked_add(8))
            .ok_or_else(fail)?;
        let aw = a
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        let capacity = anchor
            .section
            .rows
            .checked_mul(anchor.section.width)
            .ok_or_else(fail)?;
        let end = anchor.offset.checked_add(aw).ok_or_else(fail)?;
        if roots == 0
            || source_width == 0
            || fw > u32::MAX as usize
            || rw > u32::MAX as usize
            || end > u32::MAX as usize
            || anchor.width != a
            || !(1..=120).contains(&anchor.grain.0)
            || anchor.offset % 2 != 0
            || end > capacity
            || anchor.section.grain.0 != 0
            || !std::ptr::eq(anchor.section.surface, self)
            || !self.operative_shape(family, 1, fw)
            || !self.operative_shape(joint, w, w)
            || !self.operative_shape(anchor_basis, a, a)
            || !self.operative_shape(vertical, a, a)
            || !self.operative_shape(graph, w, w)
            || !self.operative_shape(report, 1, rw)
        {
            return Err(fail());
        }
        let shared = a
            .checked_mul(9)
            .and_then(|v| v.checked_mul(16))
            .and_then(|v| u32::try_from(v).ok())
            .filter(|v| *v <= self.declaration().max_sectiond_bytes)
            .ok_or_else(fail)?;
        let mut p = Params::new();
        p.ptr(family.lo.device_ptr())
            .ptr(family.hi.device_ptr())
            .u32(source_width as u32)
            .ptr(anchor.section.lo.device_ptr())
            .ptr(anchor.section.hi.device_ptr())
            .u32(anchor.offset as u32)
            .u32(roots as u32)
            .u32(anchor.grain.0);
        for s in [joint, anchor_basis, vertical, graph, report] {
            p.ptr(s.lo.device_ptr()).ptr(s.hi.device_ptr());
        }
        p.ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_normal_family_receiver",
            1,
            self.launch.block_x,
            shared,
            &mut p,
            "normal-family-receiver",
        )
    }
}
