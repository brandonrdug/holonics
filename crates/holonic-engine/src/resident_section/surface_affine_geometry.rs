use super::*;

impl<'c> ResidentSurface<'c> {
    pub(crate) fn record_realification(
        &self,
        lane: &Lane<'_, 'c>,
        input: &ResidentSection<'c>,
        rows: usize,
        input_components: usize,
        output_components: usize,
        mode: u32,
        output: &ResidentSection<'c>,
        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let valid_mode = mode <= 2;
        let dimensions = input_components
            .checked_add(1)
            .and_then(|value| value.checked_mul(2));
        let output_dimensions = output_components
            .checked_add(1)
            .and_then(|value| value.checked_mul(2));
        let mode_shape_valid = match mode {
            0 => input_components
                .checked_mul(2)
                .is_some_and(|value| value == output_components),
            1 => output_components
                .checked_mul(2)
                .is_some_and(|value| value == input_components),
            2 => input_components == output_components,
            _ => false,
        };
        if rows == 0
            || rows > u32::MAX as usize
            || !valid_mode
            || !mode_shape_valid
            || input_components == 0
            || input_components % 2 != 0
            || output_components == 0
            || output_components % 2 != 0
            || input_components > u32::MAX as usize / 4
            || output_components > u32::MAX as usize / 4
            || dimensions.is_none()
            || output_dimensions.is_none()
            || !self.operative_shape(input, rows, dimensions.unwrap())
            || !self.operative_shape(output, rows, output_dimensions.unwrap())
            || !self.operative_shape(flags, rows, SLOT_WORDS / 2)
        {
            return Err(ResidentRefusal::Declaration {
                operation: "realification",
                what: "incompatible even complex chart or output mode".into(),
            });
        }
        let mut p = Params::new();
        p.ptr(input.lo_device_ptr())
            .ptr(input.hi_device_ptr())
            .u32(rows as u32)
            .u32(input_components as u32)
            .u32(output_components as u32)
            .u32(mode)
            .ptr(output.lo_device_ptr())
            .ptr(output.hi_device_ptr())
            .ptr(flags.lo_device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_realification",
            rows,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "realification",
        )
    }

    fn affine_geometry_shapes(
        &self,
        source: &ResidentSection<'c>,
        indices: &ResidentSection<'c>,
        maps: &ResidentSection<'c>,
        rows: usize,
        grain: u32,
        output: &ResidentSection<'c>,
        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "affine-geometry",
            what: "incompatible fixed complex3 source, index cut, coefficient cut or output".into(),
        };
        if rows == 0
            || rows > u32::MAX as usize
            || !(1..=120).contains(&grain)
            || source.rows() == 0
            || source.rows() > u32::MAX as usize
            || source.width() != 14
            || !self.operative_shape(source, source.rows(), 14)
            || indices.rows() != rows
            || indices.width() != 1
            || indices.grain() != ResidentGrain(0)
            || !self.operative_shape(indices, rows, 1)
            || maps.rows() != rows
            || maps.width() != 26
            || !self.operative_shape(maps, rows, 26)
            || output.rows() != rows
            || output.width() != 14
            || output.grain() != ResidentGrain(0)
            || !self.operative_shape(output, rows, 14)
            || !self.operative_shape(flags, rows, SLOT_WORDS / 2)
        {
            return Err(fail());
        }
        Ok(())
    }

    pub(crate) fn record_affine_geometry_forward(
        &self,
        lane: &Lane<'_, 'c>,
        source: &ResidentSection<'c>,
        indices: &ResidentSection<'c>,
        maps: &ResidentSection<'c>,
        rows: usize,
        grain: u32,
        project: bool,
        output: &ResidentSection<'c>,
        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        self.affine_geometry_shapes(source, indices, maps, rows, grain, output, flags)?;
        let mut p = Params::new();
        p.ptr(source.lo_device_ptr())
            .ptr(source.hi_device_ptr())
            .ptr(indices.lo_device_ptr())
            .ptr(indices.hi_device_ptr())
            .ptr(maps.lo_device_ptr())
            .ptr(maps.hi_device_ptr())
            .u32(source.rows() as u32)
            .u32(rows as u32)
            .u32(grain)
            .u32(u32::from(project))
            .ptr(output.lo_device_ptr())
            .ptr(output.hi_device_ptr())
            .ptr(flags.lo_device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_affine_geometry_forward",
            rows,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "affine-geometry-forward",
        )
    }

    pub(crate) fn record_affine_geometry_adjoint(
        &self,
        lane: &Lane<'_, 'c>,
        maps: &ResidentSection<'c>,
        gy: &ResidentSection<'c>,
        rows: usize,
        grain: u32,
        project: bool,
        output: &ResidentSection<'c>,
        flags: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        if rows == 0
            || rows > u32::MAX as usize
            || !(1..=120).contains(&grain)
            || maps.rows() != rows
            || maps.width() != 26
            || gy.rows() != rows
            || gy.width() != 14
            || output.rows() != rows
            || output.width() != 14
            || output.grain() != ResidentGrain(0)
            || !self.operative_shape(maps, rows, 26)
            || !self.operative_shape(gy, rows, 14)
            || !self.operative_shape(output, rows, 14)
            || !self.operative_shape(flags, rows, SLOT_WORDS / 2)
        {
            return Err(ResidentRefusal::Declaration {
                operation: "affine-geometry-adjoint",
                what: "incompatible fixed complex3 adjoint chart or coefficient cut".into(),
            });
        }
        let mut p = Params::new();
        p.ptr(maps.lo_device_ptr())
            .ptr(maps.hi_device_ptr())
            .ptr(gy.lo_device_ptr())
            .ptr(gy.hi_device_ptr())
            .u32(rows as u32)
            .u32(grain)
            .u32(u32::from(project))
            .ptr(output.lo_device_ptr())
            .ptr(output.hi_device_ptr())
            .ptr(flags.lo_device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_affine_geometry_adjoint",
            rows,
            self.declaration.warp_size.max(1),
            0,
            &mut p,
            "affine-geometry-adjoint",
        )
    }
}
