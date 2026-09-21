use super::*;
use crate::native_ecology::constitutive_fibre::ResidentNormalEnclosureSection;
use crate::native_ecology::constitutive_fibre::{ResidentNormalEnclosureView, ResidentNormalInput};

impl<'chart> ResidentSurface<'chart> {
    /// Copy one complete enclosure on the resident surface.  This is used when a relaxed
    /// endpoint crosses the source/commit seam; the copy stays device resident and never
    /// detaches the endpoint into a host rest packet.
    pub(crate) fn record_field_enclosure_copy(
        &self,
        lane: &Lane<'_, 'chart>,
        source: ResidentNormalEnclosureView<'_, 'chart>,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        self.record_normal_enclosure_pair(lane, source, source, 0, out)
    }

    pub(crate) fn record_field_source_reflection_joint_section(
        &self,
        lane: &Lane<'_, 'chart>,
        map: &ResidentSection<'chart>,
        bounds: &ResidentSection<'chart>,
        factor: &ResidentSection<'chart>,
        rows: &ResidentSection<'chart>,
        d: usize,
        count: usize,
        grain: u32,
        work: &ResidentSection<'chart>,
        dots: &ResidentSection<'chart>,
        out: &ResidentSection<'chart>,
        flags: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let width = d
            .checked_add(count.checked_mul(2).ok_or_else(fail)?)
            .ok_or_else(fail)?;
        let row_stride = 2usize
            .checked_mul(width.checked_add(1).ok_or_else(fail)?)
            .ok_or_else(fail)?;
        let factor_words = d
            .checked_mul(d)
            .and_then(|n| n.checked_add(d)?.checked_mul(2))
            .ok_or_else(fail)?;
        let work_words = d
            .checked_mul(3)
            .and_then(|n| n.checked_add(count)?.checked_add(d / 2)?.checked_mul(2))
            .ok_or_else(fail)?;
        if d == 0
            || d % 2 != 0
            || rows.rows == 0
            || !(1..=120).contains(&grain)
            || rows.width != row_stride
            || out.rows != rows.rows
            || out.width != row_stride
            || !self.operative_shape(map, count.max(1), 2 * d)
            || !self.operative_shape(bounds, 1, 4)
            || !self.operative_shape(factor, 1, factor_words)
            || !self.operative_shape(work, rows.rows, work_words)
            || !self.operative_shape(
                dots,
                rows.rows.checked_mul(count.max(1)).ok_or_else(fail)?,
                10,
            )
            || !self.operative_shape(flags, rows.rows, SLOT_WORDS / 2)
            || !std::ptr::eq(rows.surface(), self)
            || !std::ptr::eq(out.surface(), self)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for v in [map, bounds, factor, rows] {
            p.ptr(v.lo_device_ptr()).ptr(v.hi_device_ptr());
        }
        p.u32(rows.width as u32)
            .u32(rows.rows as u32)
            .u32(d as u32)
            .u32(count as u32)
            .u32(grain)
            .ptr(work.lo_device_ptr())
            .ptr(dots.lo_device_ptr())
            .ptr(out.lo_device_ptr())
            .ptr(out.hi_device_ptr())
            .ptr(flags.lo_device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_source_reflection_joint_section",
            rows.rows,
            self.launch.block_x,
            0,
            &mut p,
            "field-source-reflection-joint-section",
        )?;
        let mut collect = Params::new();
        collect
            .ptr(flags.lo_device_ptr())
            .u32(rows.rows as u32)
            .ptr(lane.slot);
        self.record_blocks(
            lane,
            "section_enclosure_collect_row_status",
            rows.rows,
            1,
            0,
            &mut collect,
            "field-source-reflection-joint-status",
        )
    }

    pub(crate) fn record_field_source_reflection_section(
        &self,
        lane: &Lane<'_, 'chart>,
        map: &ResidentSection<'chart>,
        bounds: &ResidentSection<'chart>,
        factor: &ResidentSection<'chart>,
        rows: &ResidentNormalEnclosureSection<'chart>,
        source: ResidentNormalEnclosureView<'_, 'chart>,
        d: usize,
        count: usize,
        work: &ResidentSection<'chart>,
        dots: &ResidentSection<'chart>,
        trace: &ResidentSection<'chart>,
        joint_input: &ResidentSection<'chart>,
        out: &ResidentSection<'chart>,
        flags: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let width = d
            .checked_add(count.checked_mul(2).ok_or_else(fail)?)
            .ok_or_else(fail)?;
        let row_stride = 2usize
            .checked_mul(d.checked_add(1).ok_or_else(fail)?)
            .ok_or_else(fail)?;
        let out_stride = 2usize
            .checked_mul(width.checked_add(1).ok_or_else(fail)?)
            .ok_or_else(fail)?;
        let factor_words = d
            .checked_mul(d)
            .and_then(|n| n.checked_add(d)?.checked_mul(2))
            .ok_or_else(fail)?;
        let work_words = d
            .checked_mul(3)
            .and_then(|n| n.checked_add(count)?.checked_add(d / 2)?.checked_mul(2))
            .ok_or_else(fail)?;
        if d == 0
            || d % 2 != 0
            || source.components() != width
            || rows.rows() == 0
            || rows.components() != d
            || rows.grain() != source.grain()
            || !self.operative_shape(map, count.max(1), 2 * d)
            || !self.operative_shape(bounds, 1, 4)
            || !self.operative_shape(factor, 1, factor_words)
            || !self.operative_shape(work, rows.rows(), work_words)
            || !self.operative_shape(
                dots,
                rows.rows().checked_mul(count.max(1)).ok_or_else(fail)?,
                10,
            )
            || !self.operative_shape(flags, rows.rows(), SLOT_WORDS / 2)
            || !self.operative_shape(trace, rows.rows(), 18 * d)
            || !self.operative_shape(rows.resident_section(), rows.rows(), row_stride)
            || !self.operative_shape(joint_input, rows.rows(), out_stride)
            || !self.operative_shape(out, rows.rows(), out_stride)
            || !std::ptr::eq(source.surface(), self)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for v in [map, bounds, factor, rows.resident_section()] {
            p.ptr(v.lo_device_ptr()).ptr(v.hi_device_ptr());
        }
        p.u32(rows.resident_section().width() as u32)
            .u32(rows.rows() as u32)
            .ptr(source.section().lo_device_ptr())
            .ptr(source.section().hi_device_ptr())
            .u32(source.offset() as u32)
            .u32(d as u32)
            .u32(count as u32)
            .u32(source.grain().0)
            .ptr(work.lo_device_ptr())
            .ptr(dots.lo_device_ptr())
            .ptr(trace.lo_device_ptr())
            .ptr(trace.hi_device_ptr())
            .ptr(joint_input.lo_device_ptr())
            .ptr(joint_input.hi_device_ptr())
            .ptr(out.lo_device_ptr())
            .ptr(out.hi_device_ptr())
            .ptr(flags.lo_device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_source_reflection_section",
            rows.rows(),
            self.launch.block_x,
            0,
            &mut p,
            "field-source-reflection-section",
        )?;
        let mut collect = Params::new();
        collect
            .ptr(flags.lo_device_ptr())
            .u32(rows.rows() as u32)
            .ptr(lane.slot);
        self.record_blocks(
            lane,
            "section_enclosure_collect_row_status",
            rows.rows(),
            1,
            0,
            &mut collect,
            "field-source-reflection-status",
        )
    }
    pub(crate) fn record_field_source_factor(
        &self,
        lane: &Lane<'_, 'chart>,
        cov: &ResidentSection<'chart>,
        d: usize,
        grain: u32,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let square = d.checked_mul(d).ok_or_else(fail)?;
        let words = square
            .checked_add(d)
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        if d == 0
            || d % 2 != 0
            || d > u32::MAX as usize
            || !(1..=120).contains(&grain)
            || !self.operative_shape(cov, 1, square)
            || !self.operative_shape(out, 1, words)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(cov.lo.device_ptr())
            .ptr(cov.hi.device_ptr())
            .u32(d as u32)
            .u32(grain)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_source_factor",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "field-source-factor",
        )
    }
    pub(crate) fn record_field_source_reflection(
        &self,
        lane: &Lane<'_, 'chart>,
        map: &ResidentSection<'chart>,
        bounds: &ResidentSection<'chart>,
        factor: &ResidentSection<'chart>,
        input: ResidentNormalEnclosureView<'_, 'chart>,
        d: usize,
        count: usize,
        work: &ResidentSection<'chart>,
        dots: &ResidentSection<'chart>,
        residual: &ResidentSection<'chart>,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        self.validate_normal_input(ResidentNormalInput::Enclosed(input), input.grain().0)?;
        let width = d
            .checked_add(count.checked_mul(2).ok_or_else(fail)?)
            .ok_or_else(fail)?;
        let fw = d
            .checked_mul(d)
            .and_then(|v| v.checked_add(d)?.checked_mul(2))
            .ok_or_else(fail)?;
        let ww = d
            .checked_mul(3)
            .and_then(|v| v.checked_add(count)?.checked_add(d / 2)?.checked_mul(2))
            .ok_or_else(fail)?;
        if d == 0
            || d % 2 != 0
            || width > u32::MAX as usize
            || input.width != width
            || !self.operative_shape(map, count.max(1), 2 * d)
            || !self.operative_shape(bounds, 1, 4)
            || !self.operative_shape(factor, 1, fw)
            || !self.operative_shape(work, 1, ww)
            || !self.operative_shape(dots, count.max(1), 10)
            || !self.operative_shape(residual, 1, 18 * d)
            || !self.operative_shape(out, 1, 2 * (width + 1))
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for v in [map, bounds, factor, input.section] {
            p.ptr(v.lo.device_ptr()).ptr(v.hi.device_ptr());
        }
        p.u32(input.offset as u32)
            .u32(d as u32)
            .u32(count as u32)
            .u32(input.grain().0)
            .ptr(work.lo.device_ptr())
            .ptr(dots.lo.device_ptr())
            .ptr(residual.lo.device_ptr())
            .ptr(residual.hi.device_ptr())
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_source_reflection",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "field-source-reflection",
        )
    }
    pub(crate) fn record_field_material_source(
        &self,
        lane: &Lane<'_, 'chart>,
        map: &ResidentSection<'chart>,
        bounds: &ResidentSection<'chart>,
        d: usize,
        count: usize,
        out: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || Self::operative_error();
        let width = d.checked_mul(count).ok_or_else(fail)?;
        let words = width
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        if d == 0
            || d % 2 != 0
            || count == 0
            || words > u32::MAX as usize
            || !self.operative_shape(map, count, 2 * d)
            || !self.operative_shape(bounds, 1, 4)
            || !self.operative_shape(out, 1, words)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(map.lo.device_ptr())
            .ptr(map.hi.device_ptr())
            .ptr(bounds.lo.device_ptr())
            .ptr(bounds.hi.device_ptr())
            .u32(width as u32)
            .ptr(out.lo.device_ptr())
            .ptr(out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_material_source",
            1,
            self.launch.block_x,
            0,
            &mut p,
            "field-material-source",
        )
    }
    pub(crate) fn record_field_current_source(
        &self,
        lane: &Lane<'_, 'chart>,
        current: &ResidentSection<'chart>,
        b: &ResidentSection<'chart>,
        bounds: &ResidentSection<'chart>,
        nodes: usize,
        count: usize,
        output: &ResidentSection<'chart>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "field-current-source",
            what: "incompatible resident outgoing/internal current enclosure".into(),
        };
        let d = nodes.checked_mul(6).ok_or_else(fail)?;
        let output_width = d
            .checked_add(count.checked_mul(2).ok_or_else(fail)?)
            .and_then(|n| n.checked_add(1))
            .ok_or_else(fail)?;
        if nodes == 0
            || d > u32::MAX as usize / 12 - 1
            || output_width > u32::MAX as usize / 2
            || count > u32::MAX as usize / 4
            || current.rows != 1
            || current.width != 12 * (d + 1)
            || b.rows != count.max(1)
            || b.width != 4
            || bounds.rows != 1
            || bounds.width != 4
            || output.rows != 1
            || output.width != 2 * output_width
            || [current, b, bounds, output].iter().any(|s| s.grain.0 != 0)
            || [current, b, bounds, output]
                .iter()
                .any(|s| !std::ptr::eq(s.surface, self))
        {
            return Err(fail());
        }
        let mut params = Params::new();
        params
            .ptr(current.lo.device_ptr())
            .ptr(current.hi.device_ptr())
            .ptr(b.lo.device_ptr())
            .ptr(b.hi.device_ptr())
            .ptr(bounds.lo.device_ptr())
            .ptr(bounds.hi.device_ptr())
            .u32(d as u32)
            .u32(count as u32)
            .ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_current_source",
            1,
            self.declaration.warp_size.max(1),
            0,
            &mut params,
            "field-current-source",
        )
    }
}
