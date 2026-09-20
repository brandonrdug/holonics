use super::*;

impl<'c> ResidentNormalEnclosureSection<'c> {
    /// Concatenate equal-shape enclosure packets through one resident metadata table and one
    /// row-parallel copy. The table carries source endpoint pointers and row offsets; no source
    /// packet or radius is read back to the host.
    pub fn concatenate_rows(parts: &[&Self]) -> Result<Self, ConstitutiveFibreError> {
        let first = parts.first().ok_or(ConstitutiveFibreError::Shape)?;
        if parts.iter().any(|part| {
            part.width != first.width
                || part.grain != first.grain
                || !std::ptr::eq(part.surface, first.surface)
                || part.rows == 0
        }) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let total_rows = parts.iter().try_fold(0usize, |total, part| {
            total
                .checked_add(part.rows)
                .ok_or(ConstitutiveFibreError::Shape)
        })?;
        let source_width = first.section.width();
        let mut metadata = Vec::with_capacity(
            parts
                .len()
                .checked_mul(4)
                .ok_or(ConstitutiveFibreError::Shape)?,
        );
        let mut offset = 0usize;
        for part in parts {
            let row_count = i64::try_from(part.rows).map_err(|_| ConstitutiveFibreError::Shape)?;
            let row_offset = i64::try_from(offset).map_err(|_| ConstitutiveFibreError::Shape)?;
            metadata.extend(
                [
                    part.section.lo_device_ptr() as i64,
                    part.section.hi_device_ptr() as i64,
                    row_count,
                    row_offset,
                ]
                .into_iter()
                .map(|word| (word, word)),
            );
            offset = offset
                .checked_add(part.rows)
                .ok_or(ConstitutiveFibreError::Shape)?;
        }
        let table = first.surface.mount_section_rest(
            &ResidentSectionRest::found(parts.len(), 4, ResidentGrain(0), 64, metadata)
                .map_err(|_| ConstitutiveFibreError::Shape)?,
        )?;
        let output = first
            .surface
            .fresh_section(total_rows, source_width, ResidentGrain(0))?;
        first.enact_composition(
            EnclosureComposition::Concatenate {
                table: &table,
                source_count: parts.len(),
                source_width,
            },
            &[&output],
        )?;
        Self::from_resident(first.surface, output, total_rows, first.width, first.grain)
    }
}
