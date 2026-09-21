use super::*;
use crate::native_ecology::constitutive_fibre::ResidentNormalEnclosureView;

impl<'c> ResidentSurface<'c> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_field_factor_aggregate(
        &self,
        lane: &Lane<'_, 'c>,
        offsets: &ResidentSection<'c>,
        columns: &ResidentSection<'c>,
        values: &ResidentSection<'c>,
        transpose_offsets: &ResidentSection<'c>,
        transpose_rows: &ResidentSection<'c>,
        transpose_values: &ResidentSection<'c>,
        left: &ResidentSection<'c>,
        right: &ResidentSection<'c>,
        defects: &ResidentSection<'c>,
        b: &ResidentSection<'c>,
        input_bounds: &ResidentSection<'c>,
        d: usize,
        count: usize,
        nnz: usize,
        rank: usize,
        grain: u32,
        aggregate: &ResidentSection<'c>,
        moment_bounds: &ResidentSection<'c>,
        work: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        let wire = |value: usize| u32::try_from(value).map_err(|_| fail());
        let d_wire = wire(d)?;
        let count_wire = wire(count)?;
        let nnz_wire = wire(nnz)?;
        let rank_wire = wire(rank)?;
        let offsets_width = count
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        let columns_width = nnz.max(1).checked_mul(2).ok_or_else(fail)?;
        let values_width = nnz.max(1).checked_mul(4).ok_or_else(fail)?;
        let transpose_offsets_width = d
            .checked_div(2)
            .and_then(|v| v.checked_add(1))
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        let left_width = d.checked_mul(2).ok_or_else(fail)?;
        let right_width = count.checked_mul(4).ok_or_else(fail)?;
        let rank_left_rows = rank.max(1);
        let two_count = count.checked_mul(2).ok_or_else(fail)?;
        let three_rank = rank.checked_mul(3).ok_or_else(fail)?;
        let work_words = d
            .checked_add(two_count)
            .and_then(|v| v.checked_add(three_rank))
            .and_then(|v| v.checked_add(1))
            .ok_or_else(fail)?;
        let work_width = work_words.checked_mul(2).ok_or_else(fail)?;
        for extent in [
            offsets_width,
            values_width,
            transpose_offsets_width,
            left_width,
            right_width,
            work_width,
        ] {
            wire(extent)?;
        }
        if d == 0
            || d % 2 != 0
            || count == 0
            || !(1..=120).contains(&grain)
            || !self.operative_shape(offsets, 1, offsets_width)
            || !self.operative_shape(columns, 1, columns_width)
            || !self.operative_shape(values, 1, values_width)
            || !self.operative_shape(transpose_offsets, 1, transpose_offsets_width)
            || !self.operative_shape(transpose_rows, 1, columns_width)
            || !self.operative_shape(transpose_values, 1, values_width)
            || !self.operative_shape(left, rank_left_rows, left_width)
            || !self.operative_shape(right, rank_left_rows, right_width)
            || !self.operative_shape(defects, rank_left_rows, 2)
            || !self.operative_shape(b, count, 4)
            || !self.operative_shape(input_bounds, 1, 4)
            || !self.operative_shape(aggregate, 1, left_width)
            || !self.operative_shape(moment_bounds, 1, 8)
            || !self.operative_shape(work, 1, work_width)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for s in [
            offsets,
            columns,
            values,
            transpose_offsets,
            transpose_rows,
            transpose_values,
            left,
            right,
            defects,
            b,
            input_bounds,
        ] {
            p.ptr(s.lo_device_ptr()).ptr(s.hi_device_ptr());
        }
        p.u32(d_wire)
            .u32(count_wire)
            .u32(nnz_wire)
            .u32(rank_wire)
            .u32(grain)
            .ptr(aggregate.lo_device_ptr())
            .ptr(aggregate.hi_device_ptr())
            .ptr(moment_bounds.lo_device_ptr())
            .ptr(moment_bounds.hi_device_ptr())
            .ptr(work.lo_device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_factor_aggregate",
            1,
            self.launch.block_x.min(512),
            0,
            &mut p,
            "field-factor-aggregate",
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_field_factor_action(
        &self,
        lane: &Lane<'_, 'c>,
        offsets: &ResidentSection<'c>,
        columns: &ResidentSection<'c>,
        values: &ResidentSection<'c>,
        transpose_offsets: &ResidentSection<'c>,
        transpose_rows: &ResidentSection<'c>,
        transpose_values: &ResidentSection<'c>,
        left: &ResidentSection<'c>,
        right: &ResidentSection<'c>,
        defects: &ResidentSection<'c>,
        operator_bounds: &ResidentSection<'c>,
        map_bounds: &ResidentSection<'c>,
        input: ResidentNormalEnclosureView<'_, 'c>,
        d: usize,
        count: usize,
        nnz: usize,
        rank: usize,
        grain: u32,
        steps: usize,
        omega_bits: u32,
        work: &ResidentSection<'c>,
        out: &ResidentSection<'c>,
        residual: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        let wire = |value: usize| u32::try_from(value).map_err(|_| fail());
        let d_wire = wire(d)?;
        let count_wire = wire(count)?;
        let nnz_wire = wire(nnz)?;
        let rank_wire = wire(rank)?;
        let steps_wire = wire(steps)?;
        let input_offset_wire = wire(input.offset())?;
        let offsets_width = count
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        let columns_width = nnz.max(1).checked_mul(2).ok_or_else(fail)?;
        let values_width = nnz.max(1).checked_mul(4).ok_or_else(fail)?;
        let transpose_offsets_width = d
            .checked_div(2)
            .and_then(|v| v.checked_add(1))
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        let left_width = d.checked_mul(2).ok_or_else(fail)?;
        let right_width = count.checked_mul(4).ok_or_else(fail)?;
        let rank_rows = rank.max(1);
        let two_count = count.checked_mul(2).ok_or_else(fail)?;
        let four_count = count.checked_mul(4).ok_or_else(fail)?;
        let five_d = d.checked_mul(5).ok_or_else(fail)?;
        let three_rank = rank.checked_mul(3).ok_or_else(fail)?;
        let width = d.checked_add(two_count).ok_or_else(fail)?;
        let work_words = five_d
            .checked_add(four_count)
            .and_then(|v| v.checked_add(three_rank))
            .and_then(|v| v.checked_add(1))
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        let output_width = width
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        let residual_width = d
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        for extent in [
            offsets_width,
            values_width,
            transpose_offsets_width,
            left_width,
            right_width,
            work_words,
            output_width,
        ] {
            wire(extent)?;
        }
        if d == 0
            || d % 2 != 0
            || count == 0
            || steps == 0
            || (omega_bits > 120 && omega_bits != u32::MAX)
            || !(1..=120).contains(&grain)
            || !self.operative_shape(offsets, 1, offsets_width)
            || !self.operative_shape(columns, 1, columns_width)
            || !self.operative_shape(values, 1, values_width)
            || !self.operative_shape(transpose_offsets, 1, transpose_offsets_width)
            || !self.operative_shape(transpose_rows, 1, columns_width)
            || !self.operative_shape(transpose_values, 1, values_width)
            || !self.operative_shape(left, rank_rows, left_width)
            || !self.operative_shape(right, rank_rows, right_width)
            || !self.operative_shape(defects, rank_rows, 2)
            || !self.operative_shape(operator_bounds, 1, 8)
            || !self.operative_shape(map_bounds, 1, 4)
            || !self.operative_shape(work, 1, work_words)
            || !self.operative_shape(out, 1, output_width)
            || !self.operative_shape(residual, 1, residual_width)
            || input.components() != width
            || input.grain().0 != grain
            || !std::ptr::eq(input.surface(), self)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for s in [
            offsets,
            columns,
            values,
            transpose_offsets,
            transpose_rows,
            transpose_values,
            left,
            right,
            defects,
            operator_bounds,
            map_bounds,
        ] {
            p.ptr(s.lo_device_ptr()).ptr(s.hi_device_ptr());
        }
        p.ptr(input.section().lo_device_ptr())
            .ptr(input.section().hi_device_ptr())
            .u32(input_offset_wire)
            .u32(d_wire)
            .u32(count_wire)
            .u32(nnz_wire)
            .u32(rank_wire)
            .u32(grain)
            .u32(steps_wire)
            .u32(omega_bits)
            .ptr(work.lo_device_ptr())
            .ptr(out.lo_device_ptr())
            .ptr(out.hi_device_ptr())
            .ptr(residual.lo_device_ptr())
            .ptr(residual.hi_device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_factor_action",
            1,
            self.launch.block_x.min(512),
            0,
            &mut p,
            "field-factor-action",
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_field_factor_pullback(
        &self,
        lane: &Lane<'_, 'c>,
        offsets: &ResidentSection<'c>,
        columns: &ResidentSection<'c>,
        values: &ResidentSection<'c>,
        transpose_offsets: &ResidentSection<'c>,
        transpose_rows: &ResidentSection<'c>,
        transpose_values: &ResidentSection<'c>,
        left: &ResidentSection<'c>,
        right: &ResidentSection<'c>,
        input: ResidentNormalEnclosureView<'_, 'c>,
        forward: ResidentNormalEnclosureView<'_, 'c>,
        covector: ResidentNormalEnclosureView<'_, 'c>,
        incoming: &ResidentSection<'c>,
        d: usize,
        count: usize,
        nnz: usize,
        rank: usize,
        grain: u32,
        work: &ResidentSection<'c>,
        ports: &ResidentSection<'c>,
        currents: &ResidentSection<'c>,
        bounds: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = Self::operative_error;
        let wire = |value: usize| u32::try_from(value).map_err(|_| fail());
        let d_wire = wire(d)?;
        let count_wire = wire(count)?;
        let nnz_wire = wire(nnz)?;
        let rank_wire = wire(rank)?;
        let input_offset_wire = wire(input.offset())?;
        let forward_offset_wire = wire(forward.offset())?;
        let covector_offset_wire = wire(covector.offset())?;
        let offsets_width = count
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        let columns_width = nnz.max(1).checked_mul(2).ok_or_else(fail)?;
        let values_width = nnz.max(1).checked_mul(4).ok_or_else(fail)?;
        let transpose_offsets_width = d
            .checked_div(2)
            .and_then(|v| v.checked_add(1))
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        let left_width = d.checked_mul(2).ok_or_else(fail)?;
        let right_width = count.checked_mul(4).ok_or_else(fail)?;
        let rank_rows = rank.max(1);
        let two_count = count.checked_mul(2).ok_or_else(fail)?;
        let width = d.checked_add(two_count).ok_or_else(fail)?;
        let incoming_width = width
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        let ports_width = d.checked_mul(2).ok_or_else(fail)?;
        let currents_width = count.checked_mul(4).ok_or_else(fail)?;
        // wide slots: lambda[d], D*lambda[2k], contraction rounds[d+2k], scalars[2r].
        let two_d = d.checked_mul(2).ok_or_else(fail)?;
        let four_count = count.checked_mul(4).ok_or_else(fail)?;
        let two_rank = rank.checked_mul(2).ok_or_else(fail)?;
        let work_words = two_d
            .checked_add(four_count)
            .and_then(|v| v.checked_add(two_rank))
            .and_then(|v| v.checked_mul(2))
            .ok_or_else(fail)?;
        for extent in [
            offsets_width,
            values_width,
            transpose_offsets_width,
            left_width,
            right_width,
            work_words,
            incoming_width,
        ] {
            wire(extent)?;
        }
        if d == 0
            || d % 2 != 0
            || count == 0
            || !(1..=120).contains(&grain)
            || !self.operative_shape(offsets, 1, offsets_width)
            || !self.operative_shape(columns, 1, columns_width)
            || !self.operative_shape(values, 1, values_width)
            || !self.operative_shape(transpose_offsets, 1, transpose_offsets_width)
            || !self.operative_shape(transpose_rows, 1, columns_width)
            || !self.operative_shape(transpose_values, 1, values_width)
            || !self.operative_shape(left, rank_rows, left_width)
            || !self.operative_shape(right, rank_rows, right_width)
            || !self.operative_shape(incoming, 1, incoming_width)
            || !self.operative_shape(work, 1, work_words)
            || !self.operative_shape(ports, 2, ports_width)
            || !self.operative_shape(currents, 2, currents_width.max(4))
            || !self.operative_shape(bounds, 1, 4)
            || input.components() != width
            || forward.components() != width
            || covector.components() != width
            || input.grain().0 != grain
            || forward.grain().0 != grain
            || covector.grain().0 != grain
            || !std::ptr::eq(input.surface(), self)
            || !std::ptr::eq(forward.surface(), self)
            || !std::ptr::eq(covector.surface(), self)
            || !std::ptr::eq(incoming.surface, self)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        for s in [
            offsets,
            columns,
            values,
            transpose_offsets,
            transpose_rows,
            transpose_values,
            left,
            right,
        ] {
            p.ptr(s.lo_device_ptr()).ptr(s.hi_device_ptr());
        }
        for (view, offset_wire) in [
            (input, input_offset_wire),
            (forward, forward_offset_wire),
            (covector, covector_offset_wire),
        ] {
            p.ptr(view.section().lo_device_ptr())
                .ptr(view.section().hi_device_ptr())
                .u32(offset_wire);
        }
        p.ptr(incoming.lo_device_ptr())
            .ptr(incoming.hi_device_ptr())
            .u32(0)
            .u32(d_wire)
            .u32(count_wire)
            .u32(nnz_wire)
            .u32(rank_wire)
            .u32(grain)
            .ptr(work.lo_device_ptr())
            .ptr(ports.lo_device_ptr())
            .ptr(ports.hi_device_ptr())
            .ptr(currents.lo_device_ptr())
            .ptr(currents.hi_device_ptr())
            .ptr(bounds.lo_device_ptr())
            .ptr(bounds.hi_device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_field_factor_pullback",
            1,
            self.launch.block_x.min(512),
            0,
            &mut p,
            "field-factor-pullback",
        )
    }
}
