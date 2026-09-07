use super::*;
use crate::native_ecology::constitutive_fibre::ResidentConstitutiveCurrent;

impl<'chart> ResidentSurface<'chart> {
    pub(crate) fn record_field_current_input(
        &self,
        lane: &Lane<'_, 'chart>,
        current: ResidentConstitutiveCurrent<'_, 'chart>,
        output: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        self.validate_constitutive_current_view(current)?;
        if current.width == 0
            || current.width % 2 != 0
            || output.rows != current.width / 2
            || output.width != 3
            || output.grain.0 != 0
            || !std::ptr::eq(output.surface, self)
        {
            return Err(ResidentRefusal::Declaration {
                operation: "field-current-input",
                what: "incompatible phase input chart".into(),
            });
        }
        let mut p = Params::new();
        p.ptr(current.section.lo.device_ptr())
            .ptr(current.section.hi.device_ptr())
            .u32(current.offset as u32)
            .u32(current.denominator.map_or(u32::MAX, |n| n as u32))
            .u32(current.disposition.map_or(u32::MAX, |n| n as u32))
            .u32(output.rows as u32)
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_current_input",
            1,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "field-current-input",
        )
    }

    /// Stage a retained condition current, or its unit-admittance affine contact. Neither
    /// kernel mutates the supplied current or family. The caller owns successor publication.
    pub(crate) fn record_condition_contact(
        &self,
        lane: &Lane<'_, 'chart>,
        current: ResidentConstitutiveCurrent<'_, 'chart>,
        family: Option<(&ResidentSection<'chart>, usize, &ResidentSection<'chart>)>,
        output: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        self.validate_constitutive_current_view(current)?;
        let fail = || ResidentRefusal::Declaration {
            operation: "condition-contact",
            what: "incompatible condition current, affine family or contact aperture".into(),
        };
        let c = current.width;
        let k = c.checked_mul(2).ok_or_else(fail)?;
        let out = c
            .checked_mul(5)
            .and_then(|n| n.checked_add(2))
            .ok_or_else(fail)?;
        let shape = |s: &ResidentSection<'chart>, rows: usize, width: usize| {
            s.rows == rows && s.width == width && s.grain.0 == 0 && std::ptr::eq(s.surface, self)
        };
        if c == 0 || c % 2 != 0 || out > u32::MAX as usize || !shape(output, 1, out) {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(current.section.lo.device_ptr())
            .ptr(current.section.hi.device_ptr())
            .u32(current.offset as u32)
            .u32(current.denominator.map_or(u32::MAX, |n| n as u32))
            .u32(current.disposition.map_or(u32::MAX, |n| n as u32));
        let (kernel, shared) = if let Some((f, ps, graph)) = family {
            let fw = ps
                .checked_add(c)
                .and_then(|n| n.checked_add(4))
                .and_then(|n| n.checked_add(c.checked_mul(c)?))
                .ok_or_else(fail)?;
            if ps == 0 || fw > u32::MAX as usize || !shape(f, 1, fw) || !shape(graph, k, k) {
                return Err(fail());
            }
            let shared = c
                .checked_mul(9)
                .and_then(Self::constitutive_wide_scratch)
                .and_then(|n| u32::try_from(n).ok())
                .filter(|n| *n <= self.declaration.max_sectiond_bytes)
                .ok_or_else(fail)?;
            p.ptr(f.lo.device_ptr())
                .ptr(f.hi.device_ptr())
                .u32(ps as u32)
                .u32(c as u32)
                .ptr(graph.lo.device_ptr())
                .ptr(graph.hi.device_ptr());
            ("section_constitutive_condition_contact", shared)
        } else {
            p.u32(c as u32);
            ("section_constitutive_condition_current_found", 0)
        };
        p.ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            kernel,
            1,
            self.declaration.warp_size.max(1),
            shared,
            &mut p,
            "condition-contact",
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_condition_image(
        &self,
        lane: &Lane<'_, 'chart>,
        basis: &ResidentSection<'chart>,
        source: ResidentConstitutiveCurrent<'_, 'chart>,
        condition: &ResidentSection<'chart>,
        condition_source_width: usize,
        source_complex: usize,
        condition_complex: usize,
        target_width: usize,
        graph: &ResidentSection<'chart>,
        rhs: &ResidentSection<'chart>,
        joint: &ResidentSection<'chart>,
        domain_basis: &ResidentSection<'chart>,
        output_basis: &ResidentSection<'chart>,
        domain: &ResidentSection<'chart>,
        output: &ResidentSection<'chart>,
        coverage: &ResidentSection<'chart>,
        safe: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        self.validate_constitutive_current_view(source)?;
        let fail = || ResidentRefusal::Declaration {
            operation: "condition-image",
            what: "incompatible joint condition/output chart or aperture".into(),
        };
        let sw = source_complex
            .checked_mul(condition_complex)
            .and_then(|n| n.checked_add(source_complex))
            .and_then(|n| n.checked_add(condition_complex))
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(fail)?;
        let w = sw.checked_add(target_width).ok_or_else(fail)?;
        let c = condition_complex.checked_mul(2).ok_or_else(fail)?;
        let j = c.checked_add(target_width).ok_or_else(fail)?;
        let k = w.checked_add(j).ok_or_else(fail)?;
        let report = |s: usize, t: usize| {
            s.checked_add(t)
                .and_then(|n| n.checked_add(4))
                .and_then(|n| n.checked_add(t.checked_mul(t)?))
        };
        let shape = |s: &ResidentSection<'chart>, rows: usize, width: Option<usize>| {
            s.rows == rows
                && Some(s.width) == width
                && s.grain.0 == 0
                && std::ptr::eq(s.surface, self)
        };
        if source_complex == 0
            || condition_complex == 0
            || target_width == 0
            || target_width % 2 != 0
            || k > u32::MAX as usize - 4
            || source.width != 2 * source_complex
            || condition_source_width == 0
            || condition_source_width > w
            || !shape(basis, w, Some(w))
            || !shape(condition, 1, report(condition_source_width, c))
            || !shape(graph, k, Some(k))
            || !shape(rhs, 1, w.checked_add(1))
            || !shape(joint, 1, report(w, j))
            || !shape(domain_basis, c, Some(c))
            || !shape(output_basis, target_width, Some(target_width))
            || !shape(domain, 1, report(w, c))
            || !shape(output, 1, report(w, target_width))
            || !shape(coverage, 1, w.checked_add(c).and_then(|n| n.checked_add(4)))
            || !shape(safe, 1, target_width.checked_add(2))
        {
            return Err(fail());
        }
        let shared = k
            .checked_mul(2)
            .and_then(|n| n.checked_add(w))
            .and_then(Self::constitutive_wide_scratch)
            .and_then(|n| u32::try_from(n).ok())
            .filter(|n| *n <= self.declaration.max_sectiond_bytes)
            .ok_or_else(fail)?;
        let mut p = Params::new();
        p.ptr(basis.lo.device_ptr())
            .ptr(source.section.lo.device_ptr())
            .ptr(source.section.hi.device_ptr())
            .u32(source.offset as u32)
            .u32(source.denominator.map_or(u32::MAX, |n| n as u32))
            .u32(source.disposition.map_or(u32::MAX, |n| n as u32))
            .ptr(condition.lo.device_ptr())
            .ptr(condition.hi.device_ptr())
            .u32(condition_source_width as u32)
            .u32(source_complex as u32)
            .u32(condition_complex as u32)
            .u32(target_width as u32);
        for s in [
            graph,
            rhs,
            joint,
            domain_basis,
            output_basis,
            domain,
            output,
            coverage,
            safe,
        ] {
            p.ptr(s.lo.device_ptr()).ptr(s.hi.device_ptr());
        }
        p.ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_constitutive_condition_image",
            1,
            self.declaration.warp_size.max(1),
            shared,
            &mut p,
            "condition-image",
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_condition_image_receive(
        &self,
        lane: &Lane<'_, 'chart>,
        joint: &ResidentSection<'chart>,
        joint_source_width: usize,
        c: usize,
        y: usize,
        coverage: &ResidentSection<'chart>,
        observed: ResidentConstitutiveCurrent<'_, 'chart>,
        graph: &ResidentSection<'chart>,
        rhs: &ResidentSection<'chart>,
        output: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        self.validate_constitutive_current_view(observed)?;
        let fail = || ResidentRefusal::Declaration {
            operation: "condition-image-receive",
            what: "incompatible complete-domain joint fibre or receiving current".into(),
        };
        let j = c.checked_add(y).ok_or_else(fail)?;
        let k = j.checked_add(1).ok_or_else(fail)?;
        let report = j
            .checked_mul(j)
            .and_then(|n| n.checked_add(joint_source_width.checked_add(j)?.checked_add(4)?))
            .ok_or_else(fail)?;
        let out = c
            .checked_mul(c)
            .and_then(|n| n.checked_add(k.checked_add(4)?))
            .ok_or_else(fail)?;
        if c == 0
            || y == 0
            || c % 2 != 0
            || y % 2 != 0
            || k > u32::MAX as usize - 4
            || joint_source_width > u32::MAX as usize
            || observed.width != y
            || joint.rows != 1
            || joint.width != report
            || coverage.rows != 1
            || coverage.width == 0
            || graph.rows != k
            || graph.width != k
            || rhs.rows != 1
            || rhs.width != y + 2
            || output.rows != 1
            || output.width != out
            || [joint, coverage, graph, rhs, output]
                .iter()
                .any(|s| s.grain.0 != 0 || !std::ptr::eq(s.surface, self))
        {
            return Err(fail());
        }
        let shared = k
            .checked_mul(2)
            .and_then(Self::constitutive_wide_scratch)
            .and_then(|n| u32::try_from(n).ok())
            .filter(|n| *n <= self.declaration.max_sectiond_bytes)
            .ok_or_else(fail)?;
        let mut p = Params::new();
        p.ptr(joint.lo.device_ptr())
            .ptr(joint.hi.device_ptr())
            .u32(joint_source_width as u32)
            .u32(c as u32)
            .u32(y as u32)
            .ptr(coverage.lo.device_ptr())
            .ptr(coverage.hi.device_ptr())
            .ptr(observed.section.lo.device_ptr())
            .ptr(observed.section.hi.device_ptr())
            .u32(observed.offset as u32)
            .u32(observed.denominator.map_or(u32::MAX, |n| n as u32))
            .u32(observed.disposition.map_or(u32::MAX, |n| n as u32));
        for s in [graph, rhs, output] {
            p.ptr(s.lo.device_ptr()).ptr(s.hi.device_ptr());
        }
        p.ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_constitutive_condition_receive",
            1,
            self.declaration.warp_size.max(1),
            shared,
            &mut p,
            "condition-image-receive",
        )
    }
}
