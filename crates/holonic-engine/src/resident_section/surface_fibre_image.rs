use super::*;

impl<'c> ResidentSurface<'c> {
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
