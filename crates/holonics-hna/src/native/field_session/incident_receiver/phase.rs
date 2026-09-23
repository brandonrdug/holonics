//! Fixed-generator phase receiver over the existing text/support normal owners.
//!
//! The field supplies an aperture of phase rows; this wrapper reads the text/support maps at
//! every row and adds the terminal stop class at the final row. A receiving potential is
//! complex, `s_c = <r_c|y_j>`: selection, comparison and readings all use its one magnitude
//! face `p = softmax(Re s)` (selection by `NormalizedExponential.face_mass_le_iff`, the order of
//! `Re s`), and the comparison is the Holon ratio `l = log(psi^T/psi^H)` whose covector
//! `(q - p) + i ½ q Δ`, `Δ = φ^T − φ^H` (the lift's own branch), returns through `Im s` as well
//! as `Re s`.

use super::*;
use crate::native::field_session::boundary::BoundaryMaterial;
use holonic_engine::native_ecology::constitutive_fibre::{
    NativeNormalizedFaceMeasure, NativeNormalizedSection, NormalWaveBasisChart,
    ResidentNormalEnclosureSection,
};
use holonic_engine::resident_section::SeriesAperture;

pub struct GeneratorTextReceiver<'c> {
    inner: IncidentTextReceiver<'c>,
}

/// The ratio faces a comparison was formed on: the text rows reached by the target and the
/// stop/continue rows. Each carries `p`, `q`, `q - p`, the produced phase `phi^H = Im s / 2`
/// and the ratio covector, all at the comparison's one cut.
pub struct GeneratorRatioFaces<'c> {
    pub text: Option<NativeNormalizedSection<'c>>,
    pub stop: NativeNormalizedSection<'c>,
    pub classes: usize,
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
            text_features,
            text_logits,
            text_face,
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

    /// The Holon ratio at every receiving phase, read at the cut of `forward` (the
    /// contemporary receiver applied to the contemporary phase rows). `target` is the target
    /// Holon received through the same maps at the same cut; `branches[j]` is the branch of the
    /// ratio's own lift at receiving phase `j` (the session passes `0`: continuity of the lift).
    /// Text rows compare the observed class, the stop face continue/stop; both use the magnitude
    /// face `p = softmax(Re s)` and return `(q - p) + i (1/2) q Delta`,
    /// `Delta = phi^T - phi^H + 2 pi n` with `n` that branch, through the receiving maps:
    /// the real part is the cross-entropy covector, the imaginary part the descent of
    /// `(1/2) sum q Delta^2` through `phi = Im s / 2`. An empty target passage has no target
    /// Holon; its stop rows are read with `target = None` as agreeing phases (no phase covector).
    pub fn compare(
        &self,
        forward: &IncidentTextForward<'c>,
        target: Option<&IncidentTextForward<'c>>,
        target_symbols: &[usize],
        branches: &[i64],
        terms: SeriesAperture,
        step_bits: u32,
    ) -> Result<(IncidentTextReturn<'c>, GeneratorRatioFaces<'c>)> {
        let aperture = forward.text_logits.rows();
        if target_symbols.len() > aperture.saturating_sub(1)
            || branches.len() < target_symbols.len() + 1
            || target.is_some_and(|t| {
                t.text_logits.rows() != aperture
                    || t.text_logits.components() != forward.text_logits.components()
                    || t.support_logits.components() != forward.support_logits.components()
            })
        {
            return Err(invalid("generator text target exceeds phase aperture"));
        }
        // An empty target passage has no target Holon: its stop rows compare the produced phases
        // with themselves at branch zero, so they carry no phase covector.
        let zeros = vec![0i64; branches.len()];
        let (holon, branches) = match target {
            Some(target) => (target, branches),
            None => (forward, zeros.as_slice()),
        };
        let classes = forward
            .text_cohorts
            .iter()
            .map(|cohort| cohort.class_count)
            .sum::<usize>();
        let (text_covector, text_successor, text_cohort_successors, text_face) =
            if target_symbols.is_empty() {
                (None, None, Vec::new(), None)
            } else {
                let observed = super::mount_scalar_targets(
                    self.inner.surface,
                    target_symbols,
                    classes,
                    self.inner.boundary.spec().grain,
                )?;
                let logits = super::gather_prefix(&forward.text_logits, target_symbols.len())?;
                let holon_logits = super::gather_prefix(&holon.text_logits, target_symbols.len())?;
                let features = super::gather_prefix(&forward.text_features, target_symbols.len())?;
                let face = logits
                    .normalized_ratio_return(
                        &observed,
                        &holon_logits,
                        &branches[..target_symbols.len()],
                        classes,
                        terms,
                    )
                    .map_err(invalid)?;
                let covector = face.ratio_covector().map_err(invalid)?;
                let mut covectors = Vec::new();
                let mut successors = Vec::new();
                let mut offset = 0;
                for (index, material) in forward.text_materials.iter().enumerate() {
                    let count = forward.text_cohorts[index].class_count;
                    let block = covector
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
                (Some(combined), first, successors.collect(), Some(face))
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
        let holon_support = super::gather_prefix(&holon.support_logits, support_targets.len())?;
        let support_features =
            super::gather_prefix(&forward.support_features, support_targets.len())?;
        let support_face = support_logits
            .normalized_ratio_return(
                &support_target,
                &holon_support,
                &branches[..support_targets.len()],
                2,
                terms,
            )
            .map_err(invalid)?;
        let support_class_covector = support_face.ratio_covector().map_err(invalid)?;
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
        Ok((
            IncidentTextReturn {
                text_covector,
                source_covector: None,
                boundary_covector,
                successor: IncidentTextSuccessor {
                    text: text_successor,
                    text_cohorts: text_cohort_successors,
                    support: support_successor,
                },
            },
            GeneratorRatioFaces {
                text: text_face,
                stop: support_face,
                classes,
            },
        ))
    }

    pub fn publish(&mut self, successor: IncidentTextSuccessor<'c>) {
        self.inner.publish(successor)
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
