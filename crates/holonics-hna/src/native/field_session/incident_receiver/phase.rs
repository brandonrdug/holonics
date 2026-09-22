//! Fixed-generator phase receiver over the existing text/support normal owners.
//!
//! The field supplies an aperture of phase rows; this wrapper keeps one frozen
//! text/support producer for every row and adds the terminal stop class at the
//! final row. It introduces no new numerical law.

use super::*;
use crate::native::field_session::boundary::BoundaryMaterial;
use holonic_engine::native_ecology::constitutive_fibre::{
    NativeNormalizedFaceMeasure, NormalWaveBasisChart, ResidentNormalEnclosureSection,
};
use holonic_engine::resident_section::SeriesAperture;

pub struct GeneratorTextReceiver<'c> {
    inner: IncidentTextReceiver<'c>,
}

impl<'c> GeneratorTextReceiver<'c> {
    pub fn found(surface: &'c ResidentSurface<'c>, boundary: BoundaryMaterial<'c>) -> Result<Self> {
        if boundary.spec().output_aperture != 1 {
            return Err(invalid(
                "generator phase receiver requires output aperture one",
            ));
        }
        Ok(Self {
            inner: IncidentTextReceiver::found(surface, boundary)?,
        })
    }

    pub fn inner(&self) -> &IncidentTextReceiver<'c> {
        &self.inner
    }

    pub fn inner_mut(&mut self) -> &mut IncidentTextReceiver<'c> {
        &mut self.inner
    }

    pub fn forward(
        &self,
        phase_rows: &ResidentNormalEnclosureSection<'c>,
        terms: SeriesAperture,
    ) -> Result<IncidentTextForward<'c>> {
        let aperture = phase_rows.rows();
        if aperture < 2
            || phase_rows.components() != 2 * self.inner.boundary.spec().local_complex
            || phase_rows.grain() != self.inner.boundary.spec().grain
        {
            return Err(invalid("generator phase receiver row chart"));
        }
        let text_features = phase_rows.append_homogeneous().map_err(invalid)?;
        let mut text_materials = vec![Rc::new(self.inner.text.retained_view())];
        text_materials.extend(
            self.inner
                .cohort_materials
                .iter()
                .map(|material| Rc::new(material.retained_view())),
        );
        let text_sections = text_materials
            .iter()
            .map(|material| material.read_applied_enclosed_section(&text_features))
            .collect::<std::result::Result<Vec<_>, _>>()
            .map_err(invalid)?;
        let text_logits = super::join_cohort_sections(&text_sections)?;
        let text_classes = self
            .inner
            .cohorts
            .iter()
            .take(text_materials.len())
            .map(|cohort| cohort.class_count)
            .sum::<usize>();
        let text_cohorts = self
            .inner
            .cohorts
            .iter()
            .take(text_materials.len())
            .cloned()
            .collect();
        let text_face = text_logits
            .normalized_participation(
                text_classes,
                terms,
                NativeNormalizedFaceMeasure::ExponentialPotential,
            )
            .map_err(invalid)?;

        // The boundary material was founded for one physical row. A phase
        // receiver evaluates its support map independently on every row.
        let support_features = phase_rows.append_homogeneous().map_err(invalid)?;
        let support_logits = self
            .inner
            .support
            .retained_view()
            .read_applied_enclosed_section(&support_features)
            .map_err(invalid)?;
        let support_face = support_logits
            .normalized_participation(2, terms, NativeNormalizedFaceMeasure::ExponentialPotential)
            .map_err(invalid)?;
        Ok(IncidentTextForward {
            text_material: self.inner.text.retained_view(),
            support_material: self.inner.support.retained_view(),
            text_materials,
            text_cohorts,
            retro_provenance: None,
            text_features,
            text_logits,
            text_face,
            support_features,
            support_logits,
            support_face,
        })
    }

    /// Extend text cohorts while retaining every phase row of the producing
    /// support chart. The legacy receiver's retro path keeps one support row;
    /// the generator receiver restores the full frozen aperture and its
    /// two-class stop/continue face.
    pub fn retro_forward(
        &self,
        old: &IncidentTextForward<'c>,
        terms: SeriesAperture,
    ) -> Result<IncidentTextForward<'c>> {
        let extended = self.inner.retro_forward(old, terms)?;
        let support_features =
            super::gather_prefix(&old.support_features, old.support_features.rows())?;
        let support_logits = super::gather_prefix(&old.support_logits, old.support_logits.rows())?;
        let support_face = support_logits
            .normalized_participation(2, terms, NativeNormalizedFaceMeasure::ExponentialPotential)
            .map_err(invalid)?;
        Ok(IncidentTextForward {
            text_material: extended.text_material,
            support_material: old.support_material.clone(),
            text_materials: extended.text_materials,
            text_cohorts: extended.text_cohorts,
            retro_provenance: extended.retro_provenance,
            text_features: extended.text_features,
            text_logits: extended.text_logits,
            text_face: extended.text_face,
            support_features,
            support_logits,
            support_face,
        })
    }

    pub fn select_text(&self, forward: &IncidentTextForward<'c>) -> Result<Vec<usize>> {
        let mut selected = self.inner.select_text(forward)?;
        selected.truncate(forward.text_logits.rows().saturating_sub(1));
        Ok(selected)
    }

    pub fn select_stop(&self, forward: &IncidentTextForward<'c>) -> Result<Vec<usize>> {
        let chart =
            NormalWaveBasisChart::from_permutation(self.inner.surface, &[0, 1]).map_err(invalid)?;
        let mut selected = Vec::with_capacity(forward.support_logits.rows());
        for row in 0..forward.support_logits.rows() {
            selected.push(
                forward
                    .support_logits
                    .row(row)?
                    .read_basis_sections(&chart, 1)?
                    .selections()?
                    .into_iter()
                    .next()
                    .ok_or_else(|| invalid("generator stop selection"))?
                    .selected,
            );
        }
        Ok(selected)
    }

    pub fn choose_stop(&self, forward: &IncidentTextForward<'c>) -> Result<usize> {
        let selected = self.select_stop(forward)?;
        Ok(selected
            .iter()
            .position(|class| *class == 0)
            .unwrap_or(selected.len().saturating_sub(1)))
    }

    pub fn compare(
        &self,
        forward: &IncidentTextForward<'c>,
        target_symbols: &[usize],
        terms: SeriesAperture,
        step_bits: u32,
    ) -> Result<IncidentTextReturn<'c>> {
        let aperture = forward.text_logits.rows();
        if target_symbols.len() > aperture.saturating_sub(1) {
            return Err(invalid("generator text target exceeds phase aperture"));
        }
        let classes = forward
            .text_cohorts
            .iter()
            .map(|cohort| cohort.class_count)
            .sum::<usize>();
        let (text_covector, text_successor, text_cohort_successors) = if target_symbols.is_empty() {
            (None, None, Vec::new())
        } else {
            let target = super::mount_scalar_targets(
                self.inner.surface,
                target_symbols,
                classes,
                self.inner.boundary.spec().grain,
            )?;
            let logits = super::gather_prefix(&forward.text_logits, target_symbols.len())?;
            let features = super::gather_prefix(&forward.text_features, target_symbols.len())?;
            let face = logits
                .normalized_section_return(
                    &target,
                    classes,
                    terms,
                    NativeNormalizedFaceMeasure::PacketModulus,
                )
                .map_err(invalid)?;
            let difference = face.returned_difference().map_err(invalid)?;
            let mut blocks = Vec::new();
            let mut covectors = Vec::new();
            let mut successors = Vec::new();
            let mut offset = 0;
            for (index, material) in forward.text_materials.iter().enumerate() {
                let count = forward.text_cohorts[index].class_count;
                let block = difference
                    .restrict_components(offset * 2..(offset + count) * 2)
                    .map_err(invalid)?;
                covectors.push(
                    material
                        .pull_back_enclosed_section(&block)
                        .map_err(invalid)?,
                );
                successors.push(
                    if index == 0 {
                        self.inner
                            .text
                            .stage_covector_return(&features, &block, step_bits)
                    } else {
                        self.inner.cohort_materials[index - 1]
                            .stage_covector_return(&features, &block, step_bits)
                    }
                    .map_err(invalid)?,
                );
                blocks.push(block);
                offset += count;
            }
            let mut covectors = covectors.into_iter();
            let mut combined = covectors
                .next()
                .ok_or_else(|| invalid("empty generator text cohorts"))?;
            for covector in covectors {
                combined = combined.sum_same_shape(&covector).map_err(invalid)?;
            }
            let mut successors = successors.into_iter();
            let first = successors.next();
            (Some(combined), first, successors.collect())
        };

        let support_targets = (0..=target_symbols.len())
            .map(|row| usize::from(row != target_symbols.len()))
            .collect::<Vec<_>>();
        let support_target = super::mount_scalar_targets(
            self.inner.surface,
            &support_targets,
            2,
            self.inner.boundary.spec().grain,
        )?;
        let support_logits = super::gather_prefix(&forward.support_logits, support_targets.len())?;
        let support_features =
            super::gather_prefix(&forward.support_features, support_targets.len())?;
        let support_face = support_logits
            .normalized_section_return(
                &support_target,
                2,
                terms,
                NativeNormalizedFaceMeasure::PacketModulus,
            )
            .map_err(invalid)?;
        let support_class_covector = support_face.returned_difference().map_err(invalid)?;
        let support_covector = forward
            .support_material
            .pull_back_enclosed_section(support_class_covector)
            .map_err(invalid)?;
        let text_rows = if let Some(text) = &text_covector {
            let text = text
                .restrict_components(0..2 * self.inner.boundary.spec().local_complex)
                .map_err(invalid)?;
            if text.rows() == aperture {
                text
            } else {
                let zero = ResidentNormalEnclosureSection::zeros(
                    self.inner.surface,
                    aperture - text.rows(),
                    text.components(),
                    text.grain(),
                )
                .map_err(invalid)?;
                ResidentNormalEnclosureSection::concatenate_rows(&[&text, &zero])
                    .map_err(invalid)?
            }
        } else {
            ResidentNormalEnclosureSection::zeros(
                self.inner.surface,
                aperture,
                2 * self.inner.boundary.spec().local_complex,
                self.inner.boundary.spec().grain,
            )
            .map_err(invalid)?
        };
        let text_packed = text_rows.pack_components(aperture).map_err(invalid)?;
        let support_rows = if support_covector.rows() == aperture {
            support_covector
        } else {
            let support_zero = ResidentNormalEnclosureSection::zeros(
                self.inner.surface,
                aperture - support_covector.rows(),
                support_covector.components(),
                support_covector.grain(),
            )
            .map_err(invalid)?;
            ResidentNormalEnclosureSection::concatenate_rows(&[&support_covector, &support_zero])
                .map_err(invalid)?
        };
        let support_boundary = support_rows
            .restrict_components(0..2 * self.inner.boundary.spec().local_complex)
            .map_err(invalid)?
            .pack_components(aperture)
            .map_err(invalid)?;
        let boundary_covector = text_packed
            .sum_same_shape(&support_boundary)
            .map_err(invalid)?;
        let support_successor = self
            .inner
            .support
            .stage_covector_return(&support_features, support_class_covector, step_bits)
            .map_err(invalid)?;
        Ok(IncidentTextReturn {
            text_covector,
            source_covector: None,
            boundary_covector,
            successor: IncidentTextSuccessor {
                text: text_successor,
                text_cohorts: text_cohort_successors,
                support: support_successor,
            },
        })
    }

    pub fn publish(&mut self, successor: IncidentTextSuccessor<'c>) {
        self.inner.publish(successor)
    }

    pub fn text_rest(&self) -> Result<NormalMaterialRest> {
        self.inner.text_rest()
    }

    pub fn support_rest(&self) -> Result<NormalMaterialRest> {
        self.inner.support_rest()
    }

    pub fn remount(
        surface: &'c ResidentSurface<'c>,
        boundary: BoundaryMaterial<'c>,
        text: NormalMaterialRest,
        support: NormalMaterialRest,
    ) -> Result<Self> {
        if boundary.spec().output_aperture != 1 {
            return Err(invalid(
                "generator phase receiver requires output aperture one",
            ));
        }
        Ok(Self {
            inner: IncidentTextReceiver::remount(surface, boundary, text, support)?,
        })
    }

    pub fn remount_with_cohorts(
        surface: &'c ResidentSurface<'c>,
        boundary: BoundaryMaterial<'c>,
        text: NormalMaterialRest,
        support: NormalMaterialRest,
        cohorts: Vec<IncidentTextCohort>,
        cohort_rests: Vec<NormalMaterialRest>,
        codec_version: u64,
    ) -> Result<Self> {
        if boundary.spec().output_aperture != 1 {
            return Err(invalid(
                "generator phase receiver requires output aperture one",
            ));
        }
        Ok(Self {
            inner: IncidentTextReceiver::remount_with_cohorts(
                surface,
                boundary,
                text,
                support,
                cohorts,
                cohort_rests,
                codec_version,
            )?,
        })
    }
}

#[cfg(test)]
mod tests;
