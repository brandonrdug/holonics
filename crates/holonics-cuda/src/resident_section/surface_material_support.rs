use super::*;
impl<'c> ResidentSurface<'c> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_material_support(
        &self,
        lane: &Lane<'_, 'c>,
        operation: u32,
        input: &ResidentSection<'c>,
        support: &ResidentSection<'c>,
        nodes: usize,
        targets: usize,
        count: usize,
        output: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "material-support",
            what: "incompatible contextual report restriction".into(),
        };
        let common = nodes
            .checked_mul(68)
            .and_then(|v| v.checked_add(96))
            .ok_or_else(fail)?;
        let dense = targets
            .checked_mul(82)
            .and_then(|v| v.checked_add(common))
            .ok_or_else(fail)?;
        let packed = count
            .checked_mul(82)
            .and_then(|v| v.checked_add(common))
            .ok_or_else(fail)?;
        if nodes == 0
            || targets == 0
            || dense > u32::MAX as usize
            || count > targets
            || operation > 3
            || [input, support, output]
                .iter()
                .any(|s| s.rows != 1 || s.grain.0 != 0)
            || support.width != targets + 1
        {
            return Err(fail());
        }
        let (iw, ow) = match operation {
            0 => (dense, targets + 1),
            1 => (dense, packed),
            2 => (packed, dense),
            _ => (packed, 4 * targets + 2),
        };
        if input.width != iw || output.width != ow {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(input.lo.device_ptr());
        if operation != 0 {
            p.ptr(support.lo.device_ptr());
        }
        p.u32(nodes as u32).u32(targets as u32);
        if operation != 0 {
            p.u32(count as u32);
        }
        if operation >= 2 {
            p.u32((operation == 3) as u32);
        }
        p.ptr(output.lo.device_ptr())
            .ptr(output.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        let block = self.declaration.warp_size.max(1);
        let (kernel, blocks) = match operation {
            0 => ("section_field_material_support", 1),
            1 => ("section_field_material_pack", ow.div_ceil(block as usize)),
            _ => ("section_field_material_unfold", targets + 1),
        };
        self.record_blocks(lane, kernel, blocks, block, 0, &mut p, "material-support")
    }
}
