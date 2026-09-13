use super::*;

impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_wave_family_span(
        &self,
        lane: &Lane<'_, 'c>,
        family: &ResidentSection<'c>,
        source_width: usize,
        target_width: usize,
        basis: &ResidentSection<'c>,
        workspace: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "wave-family-span",
            what: "incompatible affine family or aperture".into(),
        };
        let report = source_width
            .checked_add(target_width)
            .and_then(|w| w.checked_add(4))
            .and_then(|w| w.checked_add(target_width.checked_mul(target_width)?))
            .ok_or_else(fail)?;
        if target_width < 2
            || report > u32::MAX as usize - 4
            || source_width > u32::MAX as usize
            || target_width > u32::MAX as usize
            || family.rows != 1
            || family.width != report
            || family.grain.0 != 0
            || basis.rows != target_width
            || basis.width != target_width
            || basis.grain.0 != 0
            || workspace.rows != 1
            || workspace.grain.0 != 0
            || workspace.width < target_width.checked_mul(2).ok_or_else(fail)?
            || !std::ptr::eq(family.surface, self)
            || !std::ptr::eq(basis.surface, self)
            || !std::ptr::eq(workspace.surface, self)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(family.lo.device_ptr())
            .ptr(family.hi.device_ptr())
            .u32(source_width as u32)
            .u32(target_width as u32)
            .ptr(basis.lo.device_ptr())
            .ptr(basis.hi.device_ptr())
            .ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_constitutive_wave_family_span",
            1,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "wave-family-span",
        )
    }

    /// Materialize one lifted word step.  The kernel only rearranges the exact resident
    /// relation; prefix coordinates are structural and are bounded before allocation.
    pub(crate) fn record_wave_word_lift(
        &self,
        lane: &Lane<'_, 'c>,
        basis: &ResidentSection<'c>,
        t: usize,
        prefix: usize,
        lifted: &ResidentSection<'c>,
        workspace: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "wave-word-lift",
            what: "incompatible relation or aperture".into(),
        };
        let old = t.checked_mul(2).ok_or_else(fail)?;
        let source = prefix.checked_add(t).ok_or_else(fail)?;
        let total = source
            .checked_add(source.checked_add(t).ok_or_else(fail)?)
            .ok_or_else(fail)?;
        if t == 0
            || basis.rows != old
            || basis.width != old
            || lifted.rows != total
            || lifted.width != total
            || workspace.rows != 1
            || workspace.width < total.checked_mul(2).ok_or_else(fail)?
            || basis.grain.0 != 0
            || lifted.grain.0 != 0
            || workspace.grain.0 != 0
            || !std::ptr::eq(basis.surface, self)
            || !std::ptr::eq(lifted.surface, self)
            || !std::ptr::eq(workspace.surface, self)
            || total > u32::MAX as usize - 4
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(basis.lo.device_ptr())
            .ptr(basis.hi.device_ptr())
            .u32(t as u32)
            .u32(prefix as u32)
            .ptr(lifted.lo.device_ptr())
            .ptr(lifted.hi.device_ptr())
            .ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_constitutive_wave_word_lift",
            1,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "wave-word-lift",
        )
    }

    pub(crate) fn record_fibre_image(
        &self,
        lane: &Lane<'_, 'c>,
        basis: &ResidentSection<'c>,
        source: &ResidentSection<'c>,
        source_prefix: usize,
        c: usize,
        y: usize,
        buffers: [&ResidentSection<'c>; 9],
        workspace: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "constitutive-family-image",
            what: "incompatible source family, relation or work aperture".into(),
        };
        let w = c.checked_add(y).ok_or_else(fail)?;
        let k = w.checked_mul(2).ok_or_else(fail)?;
        let report = |s: usize, t: usize| {
            s.checked_add(t)
                .and_then(|n| n.checked_add(4))
                .and_then(|n| n.checked_add(t.checked_mul(t)?))
        };
        let shape = |section: &ResidentSection<'c>, r: usize, v: Option<usize>| {
            section.rows == r
                && Some(section.width) == v
                && section.grain.0 == 0
                && std::ptr::eq(section.surface, self)
        };
        let expected = [
            (k, Some(k)),
            (1, w.checked_add(1)),
            (1, report(w, w)),
            (c, Some(c)),
            (y, Some(y)),
            (1, report(w, c)),
            (1, report(w, y)),
            (1, w.checked_add(c).and_then(|n| n.checked_add(4))),
            (1, y.checked_add(2)),
        ];
        let valid = c != 0
            && y != 0
            && k <= u32::MAX as usize - 4
            && source_prefix
                .checked_add(c)
                .is_some_and(|v| v <= u32::MAX as usize - 4)
            && shape(basis, w, Some(w))
            && shape(source, 1, report(source_prefix, c))
            && buffers
                .iter()
                .zip(expected)
                .all(|(section, (rows, width))| shape(section, rows, width));
        if !valid {
            return Err(fail());
        }
        let words = k
            .checked_mul(2)
            .and_then(|v| v.checked_add(w)?.checked_mul(2))
            .ok_or_else(fail)?;
        if words > u32::MAX as usize || !shape(workspace, 1, Some(words)) {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(basis.lo.device_ptr())
            .ptr(basis.hi.device_ptr())
            .ptr(source.lo.device_ptr())
            .ptr(source.hi.device_ptr())
            .u32(source_prefix as u32)
            .u32(c as u32)
            .u32(y as u32);
        for section in buffers {
            p.ptr(section.lo.device_ptr()).ptr(section.hi.device_ptr());
        }
        p.ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_constitutive_relation_image",
            1,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "constitutive-family-image",
        )
    }
}
