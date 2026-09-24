use super::*;
use crate::native_ecology::constitutive_fibre::{ResidentConstitutiveCurrent, WaveSourceReceiver};
impl<'c> ResidentSurface<'c> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_constitutive_wave_relation(
        &self,
        lane: &Lane<'_, 'c>,
        basis: &ResidentSection<'c>,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
        n: usize,
        k: usize,
        graph: &ResidentSection<'c>,
        derived: &ResidentSection<'c>,
        fixed: &ResidentSection<'c>,
        workspace: &ResidentSection<'c>,
        receiver: WaveSourceReceiver,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let ns = n.checked_mul(3).ok_or_else(fail)?;
        let f = ns
            .checked_mul(k)
            .and_then(|v| v.checked_add(ns)?.checked_add(k)?.checked_mul(2))
            .ok_or_else(fail)?;
        let l = n
            .checked_mul(2)
            .and_then(|v| v.checked_add(f))
            .ok_or_else(fail)?;
        let q = n
            .checked_mul(8)
            .and_then(|v| v.checked_add(2))
            .ok_or_else(fail)?;
        let u = n
            .checked_mul(10)
            .and_then(|v| v.checked_add(2))
            .ok_or_else(fail)?;
        let g = l.checked_add(u).ok_or_else(fail)?;
        let d = q.checked_mul(2).ok_or_else(fail)?;
        let hw = k.checked_mul(2).ok_or_else(fail)?;
        if n == 0
            || k == 0
            || g > u32::MAX as usize
            || d > u32::MAX as usize
            || condition.width != hw
            || !self.operative_shape(basis, l, l)
            || !self.operative_shape(graph, g, g)
            || !self.operative_shape(derived, d, d)
            || !self.operative_shape(fixed, 1, hw + 1)
        {
            return Err(fail());
        }
        self.validate_constitutive_current_view(condition)?;
        let words = l
            .checked_add(g.max(d))
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        if words > u32::MAX as usize || !self.operative_shape(workspace, 1, words) {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(basis.lo.device_ptr())
            .ptr(basis.hi.device_ptr())
            .ptr(condition.section.lo.device_ptr())
            .ptr(condition.section.hi.device_ptr())
            .u32(condition.offset as u32)
            .u32(condition.denominator.map_or(u32::MAX, |v| v as u32))
            .u32(condition.disposition.map_or(u32::MAX, |v| v as u32))
            .u32(n as u32)
            .u32(k as u32)
            .u32(u32::from(receiver == WaveSourceReceiver::UnitRealSum))
            .ptr(graph.lo.device_ptr())
            .ptr(graph.hi.device_ptr())
            .ptr(derived.lo.device_ptr())
            .ptr(derived.hi.device_ptr())
            .ptr(fixed.lo.device_ptr())
            .ptr(fixed.hi.device_ptr())
            .ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_constitutive_wave_relation",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "constitutive-wave-relation",
        )
    }
}
