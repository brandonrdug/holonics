use super::*;
use crate::native_ecology::constitutive_fibre::ResidentNormalEnclosureView;
impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_field_factor_delta_bound(
        &self,
        lane: &Lane<'_, 'c>,
        ports: &ResidentSection<'c>,
        currents: &ResidentSection<'c>,
        bounds: &ResidentSection<'c>,
        d: usize,
        count: usize,
        grain: u32,
        out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        if d == 0
            || d % 2 != 0
            || count == 0
            || d > u32::MAX as usize / 2
            || count > u32::MAX as usize / 4
            || !(1..=120).contains(&grain)
            || !self.operative_shape(ports, 2, 2 * d)
            || !self.operative_shape(currents, 2, 4 * count)
            || !self.operative_shape(bounds, 1, 4)
            || !self.operative_shape(out, 1, 4)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for s in [ports, currents, bounds] {
            p.ptr(s.lo_device_ptr()).ptr(s.hi_device_ptr());
        }
        p.u32(d as u32)
            .u32(count as u32)
            .u32(grain)
            .ptr(out.lo_device_ptr())
            .ptr(out.hi_device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_factor_delta_bound",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "field-factor-bound",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_field_factor_append(
        &self,
        lane: &Lane<'_, 'c>,
        old: [&ResidentSection<'c>; 3],
        delta: [&ResidentSection<'c>; 3],
        rank: usize,
        d: usize,
        count: usize,
        grain: u32,
        exact: bool,
        out: [&ResidentSection<'c>; 3],
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        let next = rank.checked_add(2).ok_or_else(fail)?;
        let dw = d.checked_mul(2).ok_or_else(fail)?;
        let kw = count.checked_mul(4).ok_or_else(fail)?;
        let words = next.checked_mul(dw.max(kw)).ok_or_else(fail)?;
        if d == 0
            || d % 2 != 0
            || count == 0
            || !(1..=120).contains(&grain)
            || [d, count, rank, next]
                .iter()
                .any(|n| *n > u32::MAX as usize)
            || !self.operative_shape(old[0], rank.max(1), dw)
            || !self.operative_shape(old[1], rank.max(1), kw)
            || !self.operative_shape(old[2], rank.max(1), 2)
            || !self.operative_shape(delta[0], 2, dw)
            || !self.operative_shape(delta[1], 2, kw)
            || !self.operative_shape(delta[2], 1, 4)
            || !self.operative_shape(out[0], next, dw)
            || !self.operative_shape(out[1], next, kw)
            || !self.operative_shape(out[2], next, 2)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for s in old.into_iter().chain(delta) {
            p.ptr(s.lo_device_ptr()).ptr(s.hi_device_ptr());
        }
        p.u32(rank as u32)
            .u32(d as u32)
            .u32(count as u32)
            .u32(grain)
            .u32(u32::from(exact));
        for s in out {
            p.ptr(s.lo_device_ptr()).ptr(s.hi_device_ptr());
        }
        p.ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_factor_append",
            words.div_ceil(self.launch.block_x as usize),
            self.launch.block_x,
            0,
            &mut p,
            "field-factor-material",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_field_factor_current(
        &self,
        lane: &Lane<'_, 'c>,
        before: &ResidentSection<'c>,
        bounds: &ResidentSection<'c>,
        delta: Option<&ResidentSection<'c>>,
        delta_bounds: &ResidentSection<'c>,
        image: Option<ResidentNormalEnclosureView<'_, 'c>>,
        d: usize,
        count: usize,
        out: &ResidentSection<'c>,
        out_bounds: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        let joint = count
            .checked_mul(2)
            .and_then(|n| n.checked_add(d))
            .ok_or_else(fail)?;
        if d == 0
            || d % 2 != 0
            || count == 0
            || [d, count, joint].iter().any(|n| *n > u32::MAX as usize)
            || !self.operative_shape(before, count, 4)
            || !self.operative_shape(bounds, 1, 4)
            || delta.is_some_and(|s| !self.operative_shape(s, count, 4))
            || !self.operative_shape(delta_bounds, 1, 4)
            || !self.operative_shape(out, count, 4)
            || !self.operative_shape(out_bounds, 1, 4)
            || image.is_some_and(|v| {
                v.components() != joint
                    || v.offset() > u32::MAX as usize
                    || !std::ptr::eq(v.surface(), self)
            })
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for s in [before, bounds] {
            p.ptr(s.lo_device_ptr()).ptr(s.hi_device_ptr());
        }
        p.ptr(delta.map_or(0, |s| s.lo_device_ptr()))
            .ptr(delta.map_or(0, |s| s.hi_device_ptr()));
        p.ptr(delta_bounds.lo_device_ptr())
            .ptr(delta_bounds.hi_device_ptr());
        p.ptr(image.map_or(0, |v| v.section().lo_device_ptr()))
            .ptr(image.map_or(0, |v| v.section().hi_device_ptr()))
            .u32(image.map_or(0, |v| v.offset()) as u32)
            .u32(d as u32)
            .u32(count as u32);
        for s in [out, out_bounds] {
            p.ptr(s.lo_device_ptr()).ptr(s.hi_device_ptr());
        }
        p.ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_factor_current",
            (2 * count).div_ceil(self.launch.block_x as usize),
            self.launch.block_x,
            0,
            &mut p,
            "field-factor-current",
        )
    }
}
