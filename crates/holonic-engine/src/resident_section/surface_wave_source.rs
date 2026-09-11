use super::*;
use crate::native_ecology::constitutive_fibre::{
    ResidentConstitutiveCurrent, ResidentConstitutiveSection, WaveSourceReceiver,
};
impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_wave_source_pairs(
        &self,
        lane: &Lane<'_, 'c>,
        input: ResidentConstitutiveSection<'_, 'c>,
        out: &ResidentSection<'c>,
        workspace: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let rows = input
            .rows()
            .checked_sub(1)
            .filter(|v| *v > 0)
            .ok_or_else(fail)?;
        let width = input.components();
        let ow = width
            .checked_mul(3)
            .and_then(|v| v.checked_add(1))
            .ok_or_else(fail)?;
        if width == 0
            || !self.operative_shape(
                input.section,
                input.rows(),
                width + usize::from(input.rational),
            )
            || !self.operative_shape(out, rows, ow)
            || !self.operative_shape(workspace, rows, 2 * (ow - 1))
            || [input.section, out, workspace].iter().any(|v| {
                v.rows
                    .checked_mul(v.width)
                    .is_none_or(|w| w > u32::MAX as usize)
            })
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(input.section.lo.device_ptr())
            .ptr(input.section.hi.device_ptr())
            .u32(width as u32)
            .u32(input.section.width as u32)
            .u32(u32::from(input.rational))
            .u32(rows as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_wave_source_pairs",
            rows,
            &mut p,
            "wave-source-pairs",
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_wave_source_arrival(
        &self,
        lane: &Lane<'_, 'c>,
        source: ResidentConstitutiveCurrent<'_, 'c>,
        family: &ResidentSection<'c>,
        fs: usize,
        n: usize,
        receiver: WaveSourceReceiver,
        snapshot: &ResidentSection<'c>,
        offered: &ResidentSection<'c>,
        arrival: &ResidentSection<'c>,
        workspace: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        self.validate_constitutive_current_view(source)?;
        let fail = || Self::operative_error();
        let r = n.checked_mul(2).ok_or_else(fail)?;
        let w = r.checked_mul(2).ok_or_else(fail)?;
        let fw = fs
            .checked_add(r)
            .and_then(|v| v.checked_add(4)?.checked_add(r.checked_mul(r)?))
            .ok_or_else(fail)?;
        let aw = w
            .checked_add(6)
            .and_then(|v| v.checked_add(w.checked_mul(w)?))
            .ok_or_else(fail)?;
        if n == 0
            || aw > u32::MAX as usize
            || fw > u32::MAX as usize
            || source.width != 3 * r
            || !self.operative_shape(family, 1, fw)
            || !self.operative_shape(snapshot, 1, 3 * r + 1)
            || !self.operative_shape(offered, 1, w + 1)
            || !self.operative_shape(arrival, 1, aw)
            || !self.operative_shape(workspace, 1, 2 * (w + 2))
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(source.section.lo.device_ptr())
            .ptr(source.section.hi.device_ptr())
            .u32(source.offset as u32)
            .u32(source.denominator.map_or(u32::MAX, |v| v as u32))
            .u32(source.disposition.map_or(u32::MAX, |v| v as u32))
            .ptr(family.lo.device_ptr())
            .ptr(family.hi.device_ptr())
            .u32(fs as u32)
            .u32(n as u32)
            .u32(u32::from(receiver == WaveSourceReceiver::UnitRealSum))
            .ptr(snapshot.lo.device_ptr())
            .ptr(snapshot.hi.device_ptr())
            .ptr(offered.lo.device_ptr())
            .ptr(offered.hi.device_ptr())
            .ptr(arrival.lo.device_ptr())
            .ptr(arrival.hi.device_ptr())
            .ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_wave_source_arrival",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "wave-source-arrival",
        )
    }
    pub(crate) fn record_wave_source_map(
        &self,
        lane: &Lane<'_, 'c>,
        reaction: &ResidentSection<'c>,
        n: usize,
        basis: &ResidentSection<'c>,
        workspace: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let w = n.checked_mul(4).ok_or_else(fail)?;
        let q = w
            .checked_mul(2)
            .and_then(|v| v.checked_add(2))
            .ok_or_else(fail)?;
        let k = q.checked_mul(2).ok_or_else(fail)?;
        let rw = w
            .checked_mul(5)
            .and_then(|v| v.checked_add(2))
            .ok_or_else(fail)?;
        if n == 0
            || k > u32::MAX as usize
            || rw > u32::MAX as usize
            || !self.operative_shape(reaction, 1, rw)
            || !self.operative_shape(basis, k, k)
            || !self.operative_shape(workspace, 1, 2 * (k + w))
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(reaction.lo.device_ptr())
            .ptr(reaction.hi.device_ptr())
            .u32(n as u32)
            .ptr(basis.lo.device_ptr())
            .ptr(basis.hi.device_ptr())
            .ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_wave_source_map",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "wave-source-map",
        )
    }
}

impl<'c> ResidentSurface<'c> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_wave_source_image_rows(
        &self,
        lane: &Lane<'_, 'c>,
        basis: &ResidentSection<'c>,
        family: &ResidentSection<'c>,
        ps: usize,
        q: usize,
        validate_only: bool,
        admitted: &ResidentSection<'c>,
        mapped: &ResidentSection<'c>,
        out: &ResidentSection<'c>,
        workspace: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let k = q.checked_mul(2).ok_or_else(fail)?;
        let fw = q
            .checked_mul(q)
            .and_then(|v| v.checked_add(ps)?.checked_add(q)?.checked_add(4))
            .ok_or_else(fail)?;
        let ow = q
            .checked_mul(q)
            .and_then(|v| v.checked_add(3 * q)?.checked_add(4))
            .ok_or_else(fail)?;
        if q == 0
            || fw > u32::MAX as usize
            || ow > u32::MAX as usize
            || !self.operative_shape(basis, k, k)
            || !self.operative_shape(family, 1, fw)
            || !self.operative_shape(admitted, 1, 1)
            || !self.operative_shape(mapped, q, q)
            || !self.operative_shape(out, 1, ow)
            || !self.operative_shape(workspace, q + 1, 2 * k)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(basis.lo.device_ptr())
            .ptr(basis.hi.device_ptr())
            .ptr(family.lo.device_ptr())
            .ptr(family.hi.device_ptr())
            .u32(ps as u32)
            .u32(q as u32)
            .u32(u32::from(validate_only))
            .ptr(admitted.lo.device_ptr())
            .ptr(admitted.hi.device_ptr())
            .ptr(mapped.lo.device_ptr())
            .ptr(mapped.hi.device_ptr())
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_flat(
            lane,
            "section_wave_source_image_rows",
            if validate_only { 1 } else { q + 1 },
            &mut p,
            "wave-source-image-rows",
        )
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_wave_source_image_finish(
        &self,
        lane: &Lane<'_, 'c>,
        mapped: &ResidentSection<'c>,
        q: usize,
        basis: &ResidentSection<'c>,
        out: &ResidentSection<'c>,
        coverage: &ResidentSection<'c>,
        workspace: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let ow = q
            .checked_mul(q)
            .and_then(|v| v.checked_add(3 * q)?.checked_add(4))
            .ok_or_else(fail)?;
        if q == 0
            || ow > u32::MAX as usize
            || !self.operative_shape(mapped, q, q)
            || !self.operative_shape(basis, q, q)
            || !self.operative_shape(out, 1, ow)
            || !self.operative_shape(coverage, 1, 4 + 3 * q)
            || !self.operative_shape(workspace, q + 1, 4 * q)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(mapped.lo.device_ptr())
            .ptr(mapped.hi.device_ptr())
            .u32(q as u32)
            .ptr(basis.lo.device_ptr())
            .ptr(basis.hi.device_ptr())
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(coverage.lo.device_ptr())
            .ptr(coverage.hi.device_ptr())
            .ptr(workspace.lo.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_wave_source_image_finish",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "wave-source-image-finish",
        )
    }
}

impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_wave_observed_next(&self, lane:&Lane<'_, 'c>,
        observed:ResidentConstitutiveCurrent<'_, 'c>, n:usize, basis:&ResidentSection<'c>,
        snapshot:&ResidentSection<'c>, workspace:&ResidentSection<'c>) -> Result<(),ResidentRefusal> {
        self.validate_constitutive_current_view(observed)?;
        let fail=||Self::operative_error();
        let r=n.checked_mul(2).ok_or_else(fail)?;
        let k=n.checked_mul(16).and_then(|v|v.checked_add(4)).ok_or_else(fail)?;
        if n==0 || observed.width!=r || k.checked_mul(k).is_none_or(|v|v>u32::MAX as usize)
            || !self.operative_shape(basis,k,k) || !self.operative_shape(snapshot,1,r+1)
            || !self.operative_shape(workspace,1,2*(k+r)) {return Err(fail());}
        let mut p=Params::new();
        p.ptr(observed.section.lo.device_ptr()).ptr(observed.section.hi.device_ptr())
            .u32(observed.offset as u32).u32(observed.denominator.map_or(u32::MAX,|v|v as u32))
            .u32(observed.disposition.map_or(u32::MAX,|v|v as u32)).u32(n as u32)
            .ptr(basis.lo.device_ptr()).ptr(basis.hi.device_ptr())
            .ptr(snapshot.lo.device_ptr()).ptr(snapshot.hi.device_ptr()).ptr(workspace.lo.device_ptr())
            .ptr(lane.slot).ptr(lane.census).ptr(lane.lineage).u32(lane.lineage_count);
        self.record_blocks(lane,"section_wave_observed_next",1,self.launch.block_x,0,&mut p,"wave-observed-next")
    }
}
