//! Resident restrictions of the canonical joint current into incident operands.
use super::*;
use crate::resident_section::SLOT_WORDS;

fn regroup<'c>(
    surface: &'c ResidentSurface<'c>,
    input: &ResidentSection<'c>,
    offset: usize,
    input_rows: usize,
    input_d: usize,
    rows: usize,
    d: usize,
    grain: ResidentGrain,
) -> Result<ResidentNormalEnclosureSection<'c>, ConstitutiveFibreError> {
    if rows == 0 || d == 0 || d % 2 != 0 || rows > u32::MAX as usize || d > u32::MAX as usize {
        return Err(ConstitutiveFibreError::Shape);
    }
    let stride = d
        .checked_add(1)
        .and_then(|n| n.checked_mul(2))
        .ok_or(ConstitutiveFibreError::Shape)?;
    rows.checked_mul(stride).ok_or(ConstitutiveFibreError::Shape)?;
    let out = surface.fresh_section(rows, stride, ResidentGrain(0))?;
    let flags = surface.fresh_section(rows, SLOT_WORDS / 2, ResidentGrain(0))?;
    let mut pass = surface.begin_passage(&[vec![]])?;
    {
        let lane = pass.open(0, &[])?;
        surface
            .record_enclosure_regroup(&lane, input, offset, input_rows, input_d, &out, d, &flags)?;
    }
    pass.close(0, &out, 64)?;
    let receipt = pass.finish()?.launch()?;
    if !receipt.obstruction.is_empty() {
        return Err(ConstitutiveFibreError::Arithmetic(format!(
            "incident enclosure regroup: {:?}",
            receipt.obstruction
        )));
    }
    ResidentNormalEnclosureSection::from_resident(surface, out, rows, d, grain)
}

impl<'a, 'c> ResidentNormalEnclosureView<'a, 'c> {
    /// Project one joint ball into ordered equal-width row operands. The caller retains this
    /// original joint ball; the returned marginal radii do not assert independence.
    pub fn split_rows(
        self,
        rows: usize,
        components: usize,
    ) -> Result<ResidentNormalEnclosureSection<'c>, ConstitutiveFibreError> {
        if rows.checked_mul(components) != Some(self.width) {
            return Err(ConstitutiveFibreError::Shape);
        }
        regroup(
            self.surface,
            self.section,
            self.offset,
            1,
            self.width,
            rows,
            components,
            self.grain,
        )
    }
    pub fn as_section(self) -> Result<ResidentNormalEnclosureSection<'c>, ConstitutiveFibreError> {
        self.split_rows(1, self.width)
    }
}
impl<'c> ResidentNormalEnclosureSection<'c> {
    /// Allocate complete zero-radius balls on the device. `fresh_section` memory is explicitly
    /// sealed by the zero kernel before this method returns.
    pub fn zeros(
        surface: &'c ResidentSurface<'c>,
        rows: usize,
        components: usize,
        grain: ResidentGrain,
    ) -> Result<Self, ConstitutiveFibreError> {
        if rows == 0 || rows>u32::MAX as usize || components == 0 || components>=u32::MAX as usize || components % 2 != 0 || !(1..=120).contains(&grain.0) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let width = components
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        rows.checked_mul(width).ok_or(ConstitutiveFibreError::Shape)?;
        let output = surface.fresh_section(rows, width, ResidentGrain(0))?;
        let mut pass = surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            surface.record_enclosure_zero(&lane, &output, rows, components)?;
        }
        pass.close(0, &output, 64)?;
        let receipt = pass.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "zero enclosure: {:?}",
                receipt.obstruction
            )));
        }
        Self::from_resident(surface, output, rows, components, grain)
    }

    /// Join each consecutive block of rows as one ordered incident condition. The Euclidean
    /// radius is the outward integer ceiling of the participating row-radius squares.
    pub fn pack_components(&self, blocks: usize) -> Result<Self, ConstitutiveFibreError> {
        if blocks == 0 || self.rows() % blocks != 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let d = self
            .components()
            .checked_mul(blocks)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let section = self.resident_section();
        regroup(
            section.surface(),
            section,
            0,
            self.rows(),
            self.components(),
            self.rows() / blocks,
            d,
            self.grain(),
        )
    }
    /// Restrict each row to consecutive blocks. This also unpacks the ordered condition
    /// covector before its incident scatter adjoint.
    pub fn split_components(&self, parts: usize) -> Result<Self, ConstitutiveFibreError> {
        if parts == 0 || self.components() % parts != 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let rows = self
            .rows()
            .checked_mul(parts)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let section = self.resident_section();
        regroup(
            section.surface(),
            section,
            0,
            self.rows(),
            self.components(),
            rows,
            self.components() / parts,
            self.grain(),
        )
    }
}
