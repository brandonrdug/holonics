use super::*;
use crate::native_ecology::constitutive_fibre::ResidentConstitutiveCurrent;

impl<'c> ResidentSurface<'c> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_field_context_section(
        &self,
        lane: &Lane<'_, 'c>,
        table: &ResidentSection<'c>,
        n: usize,
        grain: u32,
        basis: &ResidentSection<'c>,
        joint: &ResidentSection<'c>,
        fixed: &ResidentSection<'c>,
        base: &ResidentSection<'c>,
        endpoint: &ResidentSection<'c>,
        proof: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "field-context-section",
            what: "incompatible actual field contrast chart".into(),
        };
        let y = n.checked_mul(2).ok_or_else(fail)?;
        let j = y.checked_add(2).ok_or_else(fail)?;
        let jw = j
            .checked_mul(j)
            .and_then(|v| v.checked_add(j)?.checked_add(5))
            .ok_or_else(fail)?;
        let shape = |s: &ResidentSection<'c>, r, w| {
            s.rows == r && s.width == w && s.grain.0 == 0 && std::ptr::eq(s.surface, self)
        };
        if n == 0
            || n > (u32::MAX as usize - 4) / 6
            || !(1..=120).contains(&grain)
            || !shape(table, 2, 6)
            || !shape(basis, j, j)
            || !shape(joint, 1, jw)
            || !shape(fixed, 1, 4 * n + 1)
            || !shape(base, 1, y + 1)
            || !shape(endpoint, 1, y + 1)
            || !shape(proof, 1, 18)
        {
            return Err(fail());
        }
        let shared = n
            .checked_mul(20)
            .and_then(|v| v.checked_add(2)?.checked_mul(16))
            .and_then(|v| u32::try_from(v).ok())
            .filter(|v| *v <= self.declaration.max_sectiond_bytes)
            .ok_or_else(fail)?;
        let mut p = Params::new();
        p.ptr(table.lo.device_ptr()).u32(n as u32).u32(grain);
        for s in [basis, joint, fixed, base, endpoint, proof] {
            p.ptr(s.lo.device_ptr()).ptr(s.hi.device_ptr());
        }
        p.ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_context_section",
            1,
            self.declaration.warp_size.max(1),
            shared,
            &mut p,
            "field-context-section",
        )
    }

    pub(crate) fn record_context_output_origin(
        &self,
        lane: &Lane<'_, 'c>,
        report: &ResidentSection<'c>,
        base: &ResidentSection<'c>,
        c: usize,
        y: usize,
        output: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "context-output-origin",
            what: "incompatible returned fibre and actual output origin".into(),
        };
        let w = c.checked_add(y).ok_or_else(fail)?;
        let words = y
            .checked_mul(y)
            .and_then(|v| v.checked_add(w)?.checked_add(4))
            .ok_or_else(fail)?;
        if c == 0
            || y == 0
            || w > u32::MAX as usize - 4
            || [report, output].iter().any(|s| {
                s.rows != 1 || s.width != words || s.grain.0 != 0 || !std::ptr::eq(s.surface, self)
            })
            || base.rows != 1
            || base.width != y + 1
            || base.grain.0 != 0
            || !std::ptr::eq(base.surface, self)
        {
            return Err(fail());
        }
        let shared = w
            .checked_mul(16)
            .and_then(|v| u32::try_from(v).ok())
            .filter(|v| *v <= self.declaration.max_sectiond_bytes)
            .ok_or_else(fail)?;
        let mut p = Params::new();
        p.ptr(report.lo.device_ptr())
            .ptr(report.hi.device_ptr())
            .ptr(base.lo.device_ptr())
            .ptr(base.hi.device_ptr())
            .u32(c as u32)
            .u32(y as u32)
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_context_output_origin",
            1,
            self.declaration.warp_size.max(1),
            shared,
            &mut p,
            "context-output-origin",
        )
    }
    pub(crate) fn record_context_return_difference(
        &self,
        lane: &Lane<'_, 'c>,
        base: &ResidentSection<'c>,
        observed: ResidentConstitutiveCurrent<'_, 'c>,
        output: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        self.validate_constitutive_current_view(observed)?;
        let fail = || ResidentRefusal::Declaration {
            operation: "context-return-difference",
            what: "incompatible actual reference and receiving current".into(),
        };
        let y = observed.width;
        if y == 0
            || y % 2 != 0
            || y > u32::MAX as usize
            || [base, output].iter().any(|s| {
                s.rows != 1 || s.width != y + 1 || s.grain.0 != 0 || !std::ptr::eq(s.surface, self)
            })
        {
            return Err(fail());
        }
        let shared = y
            .checked_mul(16)
            .and_then(|v| u32::try_from(v).ok())
            .filter(|v| *v <= self.declaration.max_sectiond_bytes)
            .ok_or_else(fail)?;
        let mut p = Params::new();
        p.ptr(base.lo.device_ptr())
            .ptr(base.hi.device_ptr())
            .ptr(observed.section.lo.device_ptr())
            .ptr(observed.section.hi.device_ptr())
            .u32(observed.offset as u32)
            .u32(observed.denominator.map_or(u32::MAX, |v| v as u32))
            .u32(observed.disposition.map_or(u32::MAX, |v| v as u32))
            .u32(y as u32)
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_context_return_difference",
            1,
            self.declaration.warp_size.max(1),
            shared,
            &mut p,
            "context-return-difference",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_context_section(
        &self,
        lane: &Lane<'_, 'c>,
        basis: &ResidentSection<'c>,
        source: ResidentConstitutiveCurrent<'_, 'c>,
        ns: usize,
        nc: usize,
        y: usize,
        graph: &ResidentSection<'c>,
        derived: &ResidentSection<'c>,
        joint: &ResidentSection<'c>,
        fixed: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        self.validate_constitutive_current_view(source)?;
        let fail = || ResidentRefusal::Declaration {
            operation: "context-section",
            what: "incompatible bound source/context/return chart".into(),
        };
        let sw = ns
            .checked_mul(nc)
            .and_then(|v| v.checked_add(ns)?.checked_add(nc)?.checked_mul(2))
            .ok_or_else(fail)?;
        let w = sw.checked_add(y).ok_or_else(fail)?;
        let c = nc.checked_mul(2).ok_or_else(fail)?;
        let j = c.checked_add(y).ok_or_else(fail)?;
        let k = w.checked_add(j).ok_or_else(fail)?;
        let jw = j
            .checked_mul(j)
            .and_then(|v| v.checked_add(j)?.checked_add(5))
            .ok_or_else(fail)?;
        let shape = |s: &ResidentSection<'c>, r, width| {
            s.rows == r && s.width == width && s.grain.0 == 0 && std::ptr::eq(s.surface, self)
        };
        if ns == 0
            || nc == 0
            || y == 0
            || y % 2 != 0
            || k > u32::MAX as usize - 4
            || source.width != 2 * ns
            || !shape(basis, w, w)
            || !shape(graph, k, k)
            || !shape(derived, j, j)
            || !shape(joint, 1, jw)
            || !shape(fixed, 1, 2 * ns + 1)
        {
            return Err(fail());
        }
        let shared = w
            .checked_add(k)
            .and_then(|v| v.checked_mul(16))
            .and_then(|v| u32::try_from(v).ok())
            .filter(|v| *v <= self.declaration.max_sectiond_bytes)
            .ok_or_else(fail)?;
        let mut p = Params::new();
        p.ptr(basis.lo.device_ptr())
            .ptr(basis.hi.device_ptr())
            .ptr(source.section.lo.device_ptr())
            .ptr(source.section.hi.device_ptr())
            .u32(source.offset as u32)
            .u32(source.denominator.map_or(u32::MAX, |v| v as u32))
            .u32(source.disposition.map_or(u32::MAX, |v| v as u32))
            .u32(ns as u32)
            .u32(nc as u32)
            .u32(y as u32);
        for s in [graph, derived, joint, fixed] {
            p.ptr(s.lo.device_ptr()).ptr(s.hi.device_ptr());
        }
        p.ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_constitutive_context_section",
            1,
            self.declaration.warp_size.max(1),
            shared,
            &mut p,
            "context-section",
        )
    }
    pub(crate) fn record_context_translation(
        &self,
        lane: &Lane<'_, 'c>,
        joint: &ResidentSection<'c>,
        about: ResidentConstitutiveCurrent<'_, 'c>,
        y: usize,
        translated: &ResidentSection<'c>,
        coverage: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        self.validate_constitutive_current_view(about)?;
        let fail = || ResidentRefusal::Declaration {
            operation: "context-translation",
            what: "incompatible retained reference current and joint relation".into(),
        };
        let c = about.width;
        let j = c.checked_add(y).ok_or_else(fail)?;
        let words = j
            .checked_mul(j)
            .and_then(|v| v.checked_add(j)?.checked_add(5))
            .ok_or_else(fail)?;
        if c == 0
            || y == 0
            || c % 2 != 0
            || y % 2 != 0
            || j > u32::MAX as usize - 5
            || [joint, translated].iter().any(|s| {
                s.rows != 1 || s.width != words || s.grain.0 != 0 || !std::ptr::eq(s.surface, self)
            })
            || coverage.rows != 1
            || coverage.width != 1
            || coverage.grain.0 != 0
            || !std::ptr::eq(coverage.surface, self)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(joint.lo.device_ptr())
            .ptr(joint.hi.device_ptr())
            .ptr(about.section.lo.device_ptr())
            .ptr(about.section.hi.device_ptr())
            .u32(about.offset as u32)
            .u32(about.denominator.map_or(u32::MAX, |v| v as u32))
            .u32(about.disposition.map_or(u32::MAX, |v| v as u32))
            .u32(c as u32)
            .u32(y as u32);
        for s in [translated, coverage] {
            p.ptr(s.lo.device_ptr()).ptr(s.hi.device_ptr());
        }
        p.ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_constitutive_context_translate",
            1,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "context-translation",
        )
    }
}
