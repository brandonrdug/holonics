use super::*;
use crate::native_ecology::constitutive_fibre::{
    ResidentConstitutiveCurrent, ResidentNormalEnclosureView,
};

impl<'c> ResidentSurface<'c> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_coupled_receiver_coordinates(
        &self,
        lane: &Lane<'_, 'c>,
        family: &ResidentSection<'c>,
        ps: usize,
        t: usize,
        receiver: &ResidentSection<'c>,
        graph: &ResidentSection<'c>,
        coordinates: &ResidentSection<'c>,
        report: &ResidentSection<'c>,
        workspace: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let w = t.checked_mul(2).ok_or_else(fail)?;
        let square = t.checked_mul(t).ok_or_else(fail)?;
        let fw = square
            .checked_add(ps)
            .and_then(|v| v.checked_add(t)?.checked_add(4))
            .ok_or_else(fail)?;
        let rw = square
            .checked_add(w)
            .and_then(|v| v.checked_add(4))
            .ok_or_else(fail)?;
        let ww = t.checked_mul(8).ok_or_else(fail)?;
        if t < 10
            || (t - 2) % 8 != 0
            || [ps, t, w, fw, rw, ww]
                .iter()
                .any(|v| *v >= u32::MAX as usize)
            || !self.operative_shape(family, 1, fw)
            || !self.operative_shape(receiver, 1, 4 * t)
            || !self.operative_shape(graph, w, w)
            || !self.operative_shape(coordinates, 1, t + 1)
            || !self.operative_shape(report, 1, rw)
            || !self.operative_shape(workspace, 1, ww)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(family.lo.device_ptr())
            .ptr(family.hi.device_ptr())
            .u32(ps as u32)
            .u32(t as u32)
            .ptr(receiver.lo.device_ptr())
            .ptr(receiver.hi.device_ptr())
            .ptr(graph.lo.device_ptr())
            .ptr(graph.hi.device_ptr())
            .ptr(coordinates.lo.device_ptr())
            .ptr(coordinates.hi.device_ptr())
            .ptr(report.lo.device_ptr())
            .ptr(report.hi.device_ptr())
            .ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_coupled_receiver_coordinates",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "coupled-receiver-coordinates",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_coupled_family_section(
        &self,
        lane: &Lane<'_, 'c>,
        family: &ResidentSection<'c>,
        ps: usize,
        t: usize,
        theta: &ResidentSection<'c>,
        anchor: &ResidentSection<'c>,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let square = t.checked_mul(t).ok_or_else(fail)?;
        let input = square
            .checked_add(ps)
            .and_then(|v| v.checked_add(t)?.checked_add(4))
            .ok_or_else(fail)?;
        let output = square
            .checked_add(t)
            .and_then(|v| v.checked_add(5))
            .ok_or_else(fail)?;
        let shared = u32::try_from(t.checked_mul(16).ok_or_else(fail)?).map_err(|_| fail())?;
        if t < 10
            || (t - 2) % 8 != 0
            || [ps, t, input, output]
                .iter()
                .any(|v| *v >= u32::MAX as usize)
            || shared > self.declaration.max_sectiond_bytes
            || !self.operative_shape(family, 1, input)
            || !self.operative_shape(theta, 1, t + 1)
            || !self.operative_shape(anchor, 1, t + 2)
            || !self.operative_shape(out, 1, output)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(family.lo.device_ptr())
            .ptr(family.hi.device_ptr())
            .u32(ps as u32)
            .u32(t as u32)
            .ptr(theta.lo.device_ptr())
            .ptr(theta.hi.device_ptr())
            .ptr(anchor.lo.device_ptr())
            .ptr(anchor.hi.device_ptr())
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_coupled_family_section",
            1,
            self.launch.block_x,
            shared,
            &mut p,
            "coupled-family-section",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_coupled_family_operands(
        &self,
        lane: &Lane<'_, 'c>,
        coeff: &ResidentSection<'c>,
        n: usize,
        k: usize,
        theta: &ResidentSection<'c>,
        anchor: &ResidentSection<'c>,
        source: &ResidentSection<'c>,
        eta: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let t = n
            .checked_mul(8)
            .and_then(|v| v.checked_add(2))
            .ok_or_else(fail)?;
        let s = n.checked_mul(6).ok_or_else(fail)?;
        let f = s
            .checked_mul(k)
            .and_then(|v| v.checked_add(s)?.checked_add(k.checked_mul(2)?))
            .ok_or_else(fail)?;
        let w = f.checked_add(2 * n).ok_or_else(fail)?;
        let shared = u32::try_from(n.checked_mul(128).ok_or_else(fail)?).map_err(|_| fail())?;
        if n == 0
            || k == 0
            || [t, s, f, w].iter().any(|v| *v >= u32::MAX as usize)
            || shared > self.declaration.max_sectiond_bytes
            || !self.operative_shape(coeff, t + 1, 2 * (w + 1))
            || !self.operative_shape(theta, 1, t + 1)
            || !self.operative_shape(anchor, 1, 2 * (4 * n + 2))
            || !self.operative_shape(source, 1, s + 1)
            || !self.operative_shape(eta, 1, 2 * n + 1)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(coeff.lo.device_ptr())
            .ptr(coeff.hi.device_ptr())
            .u32(n as u32)
            .u32(k as u32)
            .ptr(theta.lo.device_ptr())
            .ptr(theta.hi.device_ptr())
            .ptr(anchor.lo.device_ptr())
            .ptr(anchor.hi.device_ptr())
            .ptr(source.lo.device_ptr())
            .ptr(source.hi.device_ptr())
            .ptr(eta.lo.device_ptr())
            .ptr(eta.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_coupled_family_operands",
            1,
            self.launch.block_x,
            shared,
            &mut p,
            "coupled-family-operands",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_coupled_joint_compile(
        &self,
        lane: &Lane<'_, 'c>,
        coeff: &ResidentSection<'c>,
        basis: &ResidentSection<'c>,
        fixed: ResidentConstitutiveCurrent<'_, 'c>,
        n: usize,
        k: usize,
        left: &ResidentSection<'c>,
        right: &ResidentSection<'c>,
        receiver: &ResidentSection<'c>,
        workspace: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let t = n
            .checked_mul(8)
            .and_then(|v| v.checked_add(2))
            .ok_or_else(fail)?;
        let source = n.checked_mul(6).ok_or_else(fail)?;
        let condition = k.checked_mul(2).ok_or_else(fail)?;
        let features = source
            .checked_mul(k)
            .and_then(|v| v.checked_add(source)?.checked_add(condition))
            .ok_or_else(fail)?;
        let w = features.checked_add(2 * n).ok_or_else(fail)?;
        let params = t
            .checked_add(condition)
            .and_then(|v| v.checked_add(w))
            .ok_or_else(fail)?;
        let rank = source
            .checked_mul(condition)
            .and_then(|v| {
                v.checked_add(source)?
                    .checked_add(condition)?
                    .checked_add(2 * n)?
                    .checked_add(w)?
                    .checked_add(1)
            })
            .ok_or_else(fail)?;
        let ac = rank.checked_mul(params + 1).ok_or_else(fail)?;
        let dc = rank.checked_mul(w + condition).ok_or_else(fail)?;
        let scratch = ac
            .checked_add(dc)
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        self.validate_constitutive_current_view(fixed)?;
        if n == 0
            || k == 0
            || [t, params, rank, ac, dc, scratch]
                .iter()
                .any(|v| *v >= u32::MAX as usize)
            || fixed.offset != 0
            || fixed.width != condition
            || fixed.denominator != Some(condition)
            || fixed.disposition.is_some()
            || !self.operative_shape(coeff, t + 1, 2 * (w + 1))
            || !self.operative_shape(basis, w, w)
            || !self.operative_shape(left, 1, ac + 1)
            || !self.operative_shape(right, 1, ac + 1)
            || !self.operative_shape(receiver, 1, dc + 1)
            || !self.operative_shape(workspace, 1, scratch)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(coeff.lo.device_ptr())
            .ptr(coeff.hi.device_ptr())
            .ptr(basis.lo.device_ptr())
            .ptr(basis.hi.device_ptr())
            .ptr(fixed.section.lo.device_ptr())
            .ptr(fixed.section.hi.device_ptr())
            .u32(n as u32)
            .u32(k as u32);
        for out in [left, right, receiver] {
            p.ptr(out.lo.device_ptr()).ptr(out.hi.device_ptr());
        }
        p.ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_coupled_joint_compile",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "coupled-joint-compile",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_coupled_joint_anchor(
        &self,
        lane: &Lane<'_, 'c>,
        family: &ResidentSection<'c>,
        source_width: usize,
        anchor: ResidentNormalEnclosureView<'_, 'c>,
        n: usize,
        parameters: usize,
        theta: &ResidentSection<'c>,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let a = n.checked_mul(4).ok_or_else(fail)?;
        let t = a
            .checked_mul(2)
            .and_then(|v| v.checked_add(2))
            .ok_or_else(fail)?;
        let fw = t
            .checked_mul(t)
            .and_then(|v| v.checked_add(source_width)?.checked_add(t)?.checked_add(4))
            .ok_or_else(fail)?;
        let end = anchor.offset.checked_add(2 * (a + 1)).ok_or_else(fail)?;
        if n == 0
            || parameters < t
            || [parameters, fw, end]
                .iter()
                .any(|v| *v >= u32::MAX as usize)
            || anchor.width != a
            || anchor.offset % 2 != 0
            || !(1..=120).contains(&anchor.grain.0)
            || !std::ptr::eq(anchor.section.surface, self)
            || anchor.section.grain.0 != 0
            || end > anchor.section.rows * anchor.section.width
            || !self.operative_shape(family, 1, fw)
            || !self.operative_shape(theta, 1, parameters + 1)
            || !self.operative_shape(out, 1, 2 * (a + 2))
        {
            return Err(fail());
        }
        let shared = u32::try_from(a.checked_mul(16).ok_or_else(fail)?).map_err(|_| fail())?;
        if shared > self.declaration.max_sectiond_bytes {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(family.lo.device_ptr())
            .ptr(family.hi.device_ptr())
            .u32(source_width as u32)
            .ptr(anchor.section.lo.device_ptr())
            .ptr(anchor.section.hi.device_ptr())
            .u32(anchor.offset as u32)
            .u32(n as u32)
            .u32(anchor.grain.0)
            .ptr(theta.lo.device_ptr())
            .ptr(theta.hi.device_ptr())
            .u32(parameters as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_coupled_joint_anchor",
            1,
            self.launch.block_x,
            shared,
            &mut p,
            "coupled-joint-anchor",
        )
    }
}
