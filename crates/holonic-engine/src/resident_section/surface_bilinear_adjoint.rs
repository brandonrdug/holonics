use super::*;
use crate::native_ecology::constitutive_fibre::ResidentConstitutiveSection;

impl<'c> ResidentSurface<'c> {
    /// Return one feature-covector section to both operands of the same-row bilinear source.
    /// The retained forward operands are the linearization point; they are exact point rows and
    /// are never read back. Each returned section is an enclosure with its own transported radius.
    pub(crate) fn record_bilinear_source_adjoint(
        &self,
        lane: &Lane<'_, 'c>,
        source: ResidentConstitutiveSection<'_, 'c>,
        condition: ResidentConstitutiveSection<'_, 'c>,
        covector: &ResidentSection<'c>,
        source_out: &ResidentSection<'c>,
        condition_out: &ResidentSection<'c>,
    ) -> Result<(), ResidentRefusal> {
        let fail = || ResidentRefusal::Declaration {
            operation: "bilinear-source-adjoint",
            what: "incompatible feature-covector chart or retained bilinear operands".into(),
        };
        let rows = source.rows();
        let source_complex = source.components() / 2;
        let condition_complex = condition.components() / 2;
        let width = source_complex
            .checked_mul(condition_complex)
            .and_then(|n| n.checked_add(source_complex))
            .and_then(|n| n.checked_add(condition_complex))
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(fail)?;
        let covector_words = width
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(fail)?;
        let source_words = source_complex
            .checked_mul(2)
            .and_then(|n| n.checked_add(1)?.checked_mul(2))
            .ok_or_else(fail)?;
        let condition_words = condition_complex
            .checked_mul(2)
            .and_then(|n| n.checked_add(1)?.checked_mul(2))
            .ok_or_else(fail)?;
        if rows == 0
            || rows > u32::MAX as usize
            || source_complex == 0
            || condition_complex == 0
            || source.components() % 2 != 0
            || condition.components() % 2 != 0
            || condition.rows() != rows
            || width >= u32::MAX as usize
            || source.section.width > u32::MAX as usize
            || condition.section.width > u32::MAX as usize
            || source.section.grain.0 != 0
            || condition.section.grain.0 != 0
            || !std::ptr::eq(source.section.surface, self)
            || !std::ptr::eq(condition.section.surface, self)
            || !self.operative_shape(covector, rows, covector_words)
            || !self.operative_shape(source_out, rows, source_words)
            || !self.operative_shape(condition_out, rows, condition_words)
        {
            return Err(fail());
        }
        let mut p = Params::new();
        p.ptr(source.section.lo.device_ptr())
            .ptr(source.section.hi.device_ptr())
            .u32(source.section.width as u32)
            .u32(u32::from(source.rational))
            .ptr(condition.section.lo.device_ptr())
            .ptr(condition.section.hi.device_ptr())
            .u32(condition.section.width as u32)
            .u32(u32::from(condition.rational))
            .ptr(covector.lo.device_ptr())
            .ptr(covector.hi.device_ptr())
            .u32(rows as u32)
            .u32(source_complex as u32)
            .u32(condition_complex as u32)
            .ptr(source_out.lo.device_ptr())
            .ptr(source_out.hi.device_ptr())
            .ptr(condition_out.lo.device_ptr())
            .ptr(condition_out.hi.device_ptr())
            .ptr(lane.slot)
            .ptr(lane.census)
            .ptr(lane.lineage)
            .u32(lane.lineage_count);
        self.record_blocks(
            lane,
            "section_bilinear_source_adjoint",
            1,
            1,
            0,
            &mut p,
            "bilinear-source-adjoint",
        )
    }
}
