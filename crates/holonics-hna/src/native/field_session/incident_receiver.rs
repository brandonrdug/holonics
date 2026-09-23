//! Resident text/support receivers for the incident-field boundary.
//!
//! The receiver keeps logits, features and normalized faces on the resident surface.  Symbol
//! choices are obtained from the existing device readout; no host-side score selection enters
//! the forward or delayed comparison.

pub(super) mod phase;
use super::boundary::BoundaryMaterial;
use super::{Result, invalid};
use holonic_engine::{
    ExactWavePhaseTransport,
    native_ecology::constitutive_fibre::{
        NativeNormalPrior, NativeNormalizedFaceMeasure, NormalBasisSelection, NormalMaterialRest,
        NormalWaveBasisChart, ResidentConstitutiveSection, ResidentNormalEnclosureSection,
        ResidentNormalMaterial,
    },
    resident_section::{ResidentGrain, ResidentSectionRest, ResidentSurface, SeriesAperture},
};
use std::rc::Rc;

/// One text/support receiving aperture read at one cut: the material views it read, its
/// features, logits and normalized faces. The compare and the pullback of that cut read the same
/// views; nothing here outlives the cut (a later return reads the contemporary receiver again).
pub struct IncidentTextForward<'c> {
    /// The material views this reading was taken at (the cut's receiver).
    pub text_material:
        holonic_engine::native_ecology::constitutive_fibre::ResidentNormalMaterialView<'c>,
    pub support_material:
        holonic_engine::native_ecology::constitutive_fibre::ResidentNormalMaterialView<'c>,
    pub text_materials:
        Vec<Rc<holonic_engine::native_ecology::constitutive_fibre::ResidentNormalMaterialView<'c>>>,
    pub text_cohorts: Vec<IncidentTextCohort>,
    pub text_features: ResidentNormalEnclosureSection<'c>,
    pub text_logits: ResidentNormalEnclosureSection<'c>,
    pub text_face: holonic_engine::native_ecology::constitutive_fibre::NativeNormalizedSection<'c>,
    pub support_features: ResidentNormalEnclosureSection<'c>,
    pub support_logits: ResidentNormalEnclosureSection<'c>,
    pub support_face:
        holonic_engine::native_ecology::constitutive_fibre::NativeNormalizedSection<'c>,
}

/// Both contemporary material successors are returned together for one atomic publication.
pub struct IncidentTextSuccessor<'c> {
    /// `None` means the actual response had length zero, so R_text received no observation.
    pub text: Option<ResidentNormalMaterial<'c>>,
    pub text_cohorts: Vec<ResidentNormalMaterial<'c>>,
    pub support: ResidentNormalMaterial<'c>,
}

/// One admitted decoder row cohort. Existing cohorts retain their own observation scope and
/// are never enlarged by appending a class.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct IncidentTextCohort {
    pub class_start: usize,
    pub class_count: usize,
    pub codec_version: u64,
}

/// A fresh prior block for newly admitted decoder classes. It is published separately so an old
/// producing comparison cannot accidentally update the new cohort.
pub struct IncidentTextCohortSuccessor<'c> {
    pub cohort: IncidentTextCohort,
    pub material: ResidentNormalMaterial<'c>,
}

/// The receiver return of one cut: its covectors and the staged successor maps.
pub struct IncidentTextReturn<'c> {
    pub text_covector: Option<ResidentNormalEnclosureSection<'c>>,
    /// Covector returned through R_text into the producing E_in source rows, when a source
    /// reconstruction comparison was supplied.
    pub source_covector: Option<ResidentNormalEnclosureSection<'c>>,
    /// One q-only boundary covector with all A_out rows packed into one resident row.
    pub boundary_covector: ResidentNormalEnclosureSection<'c>,
    pub successor: IncidentTextSuccessor<'c>,
}

/// Receiver over the seeded codec boundary and two independent normal maps.
pub struct IncidentTextReceiver<'c> {
    surface: &'c ResidentSurface<'c>,
    boundary: BoundaryMaterial<'c>,
    text: ResidentNormalMaterial<'c>,
    support: ResidentNormalMaterial<'c>,
    cohorts: Vec<IncidentTextCohort>,
    cohort_materials: Vec<ResidentNormalMaterial<'c>>,
    codec_version: u64,
}

impl<'c> IncidentTextReceiver<'c> {
    pub fn found(surface: &'c ResidentSurface<'c>, boundary: BoundaryMaterial<'c>) -> Result<Self> {
        let spec = boundary.spec();
        let class_count = boundary.chart().alphabet().len();
        let text = ResidentNormalMaterial::found_features_with_prior(
            surface,
            spec.local_complex + 1,
            boundary.chart().alphabet().len(),
            spec.grain,
            boundary.text_prior()?,
        )
        .map_err(invalid)?;
        let support_source = spec
            .output_aperture
            .checked_mul(spec.local_complex)
            .and_then(|n| n.checked_add(1))
            .ok_or_else(|| invalid("support receiver feature extent"))?;
        // No length has been supplied at founding. H0=I, B0=0 gives a uniform support face
        // until an actual observation distinguishes lengths; text bootstrap geometry does
        // not provide a preferred response length.
        let support = ResidentNormalMaterial::found_features(
            surface,
            support_source,
            spec.output_aperture + 1,
            spec.grain,
        )
        .map_err(invalid)?;
        Ok(Self {
            surface,
            boundary,
            text,
            support,
            cohorts: vec![IncidentTextCohort {
                class_start: 0,
                class_count,
                codec_version: 0,
            }],
            cohort_materials: Vec::new(),
            codec_version: 0,
        })
    }

    pub fn text_material(&self) -> &ResidentNormalMaterial<'c> {
        &self.text
    }

    pub fn support_material(&self) -> &ResidentNormalMaterial<'c> {
        &self.support
    }

    pub fn cohorts(&self) -> &[IncidentTextCohort] {
        &self.cohorts
    }

    pub fn codec_version(&self) -> u64 {
        self.codec_version
    }

    pub(super) fn inspect_text_materials(&self) -> Result<Vec<serde_json::Value>> {
        std::iter::once(&self.text)
            .chain(self.cohort_materials.iter())
            .zip(&self.cohorts)
            .map(|(material, cohort)| {
                Ok(serde_json::json!({
                    "cohort": cohort,
                    "observations": material.observations(),
                    "state": material.inspect().map_err(invalid)?,
                    "prior": material.prior(),
                }))
            })
            .collect()
    }

    pub fn material_observations(&self) -> (u64, u64, Vec<u64>) {
        (
            self.text.observations(),
            self.support.observations(),
            self.cohort_materials
                .iter()
                .map(ResidentNormalMaterial::observations)
                .collect(),
        )
    }

    /// Admit a decoder cohort from the E-derived matching columns supplied by the encoder.
    /// This is the path used for codec append/rechart; it does not derive a fresh seed from class
    /// positions and therefore preserves the E/R bootstrap correspondence.
    pub fn prepare_text_cohort_with_prior(
        &self,
        surface: &'c ResidentSurface<'c>,
        class_count: usize,
        codec_version: u64,
        prior: NativeNormalPrior,
    ) -> Result<IncidentTextCohortSuccessor<'c>> {
        if class_count == 0 || codec_version <= self.codec_version {
            return Err(invalid("decoder cohort admission"));
        }
        let class_start = self
            .cohorts
            .iter()
            .map(|cohort| cohort.class_count)
            .sum::<usize>();
        let material = ResidentNormalMaterial::found_features_with_prior(
            surface,
            self.boundary.spec().local_complex + 1,
            class_count,
            self.boundary.spec().grain,
            prior,
        )
        .map_err(invalid)?;
        Ok(IncidentTextCohortSuccessor {
            cohort: IncidentTextCohort {
                class_start,
                class_count,
                codec_version,
            },
            material,
        })
    }

    pub fn publish_text_cohort(
        &mut self,
        successor: IncidentTextCohortSuccessor<'c>,
    ) -> Result<()> {
        if successor.cohort.codec_version <= self.codec_version
            || successor.cohort.class_start
                != self
                    .cohorts
                    .iter()
                    .map(|cohort| cohort.class_count)
                    .sum::<usize>()
        {
            return Err(invalid("decoder cohort publication order"));
        }
        self.cohort_materials.push(successor.material);
        self.cohorts.push(successor.cohort);
        self.codec_version = self
            .cohorts
            .last()
            .map_or(self.codec_version, |cohort| cohort.codec_version);
        // The root publication owner binds the returned material to its multi-cohort receiver.
        // The legacy map remains the original cohort until that owner installs the cohort block.
        Ok(())
    }

    /// Serialize each live receiver cut independently; root publishes both successor cuts
    /// together with the producing field transaction.
    pub fn text_rest(&self) -> Result<NormalMaterialRest> {
        self.text.rest().map_err(invalid)
    }

    pub fn support_rest(&self) -> Result<NormalMaterialRest> {
        self.support.rest().map_err(invalid)
    }

    pub fn text_cohort_rests(&self) -> Result<Vec<NormalMaterialRest>> {
        self.cohort_materials
            .iter()
            .map(ResidentNormalMaterial::rest)
            .collect::<std::result::Result<_, _>>()
            .map_err(invalid)
    }

    /// Publish both contemporary receiver successors as one caller-owned transaction.
    pub fn publish(&mut self, successor: IncidentTextSuccessor<'c>) {
        if let Some(text) = successor.text {
            self.text = text;
        }
        for (current, cohort) in self.cohort_materials.iter_mut().zip(successor.text_cohorts) {
            *current = cohort;
        }
        self.support = successor.support;
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
        if cohorts.is_empty() || cohorts.len() != cohort_rests.len() + 1 {
            return Err(invalid("decoder cohort rest extent"));
        }
        let spec = boundary.spec();
        let mut start = 0usize;
        for (cohort, rest) in cohorts
            .iter()
            .zip(std::iter::once(&text).chain(&cohort_rests))
        {
            if cohort.class_start != start
                || cohort.class_count == 0
                || rest.targets() != cohort.class_count
                || rest.source_chart().complex_sources() != Some(spec.local_complex + 1)
                || rest.grain() != spec.grain
            {
                return Err(invalid("decoder cohort material chart"));
            }
            start = start
                .checked_add(cohort.class_count)
                .ok_or_else(|| invalid("decoder class extent"))?;
        }
        if start > boundary.chart().alphabet().len()
            || cohorts.last().unwrap().codec_version != codec_version
            || cohorts
                .windows(2)
                .any(|p| p[0].codec_version >= p[1].codec_version)
            || support.targets() != spec.output_aperture + 1
            || support.source_chart().complex_sources()
                != spec
                    .output_aperture
                    .checked_mul(spec.local_complex)
                    .and_then(|n| n.checked_add(1))
            || support.grain() != spec.grain
        {
            return Err(invalid("decoder rest support/codec chart"));
        }
        let cohort_materials = cohort_rests
            .into_iter()
            .map(|rest| rest.remount(surface).map_err(invalid))
            .collect::<Result<Vec<_>>>()?;
        Ok(Self {
            surface,
            text: text.remount(surface).map_err(invalid)?,
            support: support.remount(surface).map_err(invalid)?,
            boundary,
            cohorts,
            cohort_materials,
            codec_version,
        })
    }

    /// Form both receiver maps from one complete resident boundary row set.
    /// `boundary_rows.rows()` is the actual response extent and must not exceed `A_out`.
    pub fn forward(
        &self,
        boundary_rows: &ResidentNormalEnclosureSection<'c>,
        terms: SeriesAperture,
    ) -> Result<IncidentTextForward<'c>> {
        self.forward_with_cohorts(boundary_rows, terms, true)
    }

    fn forward_with_cohorts(
        &self,
        boundary_rows: &ResidentNormalEnclosureSection<'c>,
        terms: SeriesAperture,
        include_cohorts: bool,
    ) -> Result<IncidentTextForward<'c>> {
        let output_aperture = self.boundary.spec().output_aperture;
        if output_aperture == 0 || boundary_rows.rows() != output_aperture {
            return Err(invalid("incident receiver full boundary aperture"));
        }
        if boundary_rows.components() != 2 * self.boundary.spec().local_complex
            || boundary_rows.grain() != self.boundary.spec().grain
        {
            return Err(invalid("incident receiver boundary chart"));
        }
        let text_features = boundary_rows.append_homogeneous().map_err(invalid)?;
        let mut text_materials = vec![Rc::new(self.text.retained_view())];
        if include_cohorts {
            text_materials.extend(
                self.cohort_materials
                    .iter()
                    .map(|material| Rc::new(material.retained_view())),
            );
        }
        let text_sections = text_materials
            .iter()
            .map(|material| material.read_applied_enclosed_section(&text_features))
            .collect::<std::result::Result<Vec<_>, _>>()
            .map_err(invalid)?;
        let text_logits = join_cohort_sections(&text_sections)?;
        let text_classes = self
            .cohorts
            .iter()
            .take(text_materials.len())
            .map(|cohort| cohort.class_count)
            .sum::<usize>();
        let text_cohorts = self
            .cohorts
            .iter()
            .take(text_materials.len())
            .cloned()
            .collect::<Vec<_>>();
        let text_face = text_logits
            .normalized_participation(
                text_classes,
                terms,
                NativeNormalizedFaceMeasure::ExponentialPotential,
            )
            .map_err(invalid)?;

        let support_features = self.boundary.support_from_boundary(boundary_rows)?;
        let support_logits = self
            .support
            .retained_view()
            .read_applied_enclosed_section(&support_features)
            .map_err(invalid)?;
        let support_face = support_logits
            .normalized_participation(
                output_aperture + 1,
                terms,
                NativeNormalizedFaceMeasure::ExponentialPotential,
            )
            .map_err(invalid)?;
        Ok(IncidentTextForward {
            text_material: self.text.retained_view(),
            support_material: self.support.retained_view(),
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

    /// Read nominal selections from resident real-potential logits. The normalized
    /// face remains the CE/residual operand; a broad enclosing radius can erase an
    /// ordered nominal score at the normalized midpoint. This is the resident
    /// realization of `NormalizedExponential.face_mass_le_iff`.
    pub fn select_text(&self, forward: &IncidentTextForward<'c>) -> Result<Vec<usize>> {
        Ok(self
            .select_text_receipts(forward)?
            .into_iter()
            .map(|selection| selection.selected)
            .collect())
    }

    pub fn select_text_receipts(
        &self,
        forward: &IncidentTextForward<'c>,
    ) -> Result<Vec<NormalBasisSelection>> {
        let classes = forward
            .text_cohorts
            .iter()
            .map(|c| c.class_count)
            .sum::<usize>();
        let mut coordinates = self.boundary.chart().coordinates().to_vec();
        coordinates.extend(coordinates.len()..classes);
        let chart =
            NormalWaveBasisChart::from_permutation(self.surface, &coordinates).map_err(invalid)?;
        let mut selections = Vec::with_capacity(forward.text_logits.rows());
        for row in 0..forward.text_logits.rows() {
            selections.extend(
                forward
                    .text_logits
                    .row(row)?
                    .read_basis_sections(&chart, 1)?
                    .selections()?,
            );
        }
        Ok(selections)
    }

    pub fn select_support_receipt(
        &self,
        forward: &IncidentTextForward<'c>,
    ) -> Result<NormalBasisSelection> {
        let coordinates = (0..=self.boundary.spec().output_aperture).collect::<Vec<_>>();
        let chart =
            NormalWaveBasisChart::from_permutation(self.surface, &coordinates).map_err(invalid)?;
        forward
            .support_logits
            .row(0)?
            .read_basis_sections(&chart, 1)?
            .selections()?
            .into_iter()
            .next()
            .ok_or_else(|| invalid("support receiver selection"))
    }

    /// Apply the direct CE return `target - p` to both receiver maps and return their staged
    /// contemporary successors. The target length is the actual observed response length and
    /// is never padded with zero observations.
    pub fn compare(
        &self,
        forward: &IncidentTextForward<'c>,
        target_symbols: &[usize],
        support_length: usize,
        terms: SeriesAperture,
        step_bits: u32,
    ) -> Result<IncidentTextReturn<'c>> {
        let output_aperture = self.boundary.spec().output_aperture;
        validate_target_len(output_aperture, target_symbols.len())?;
        if support_length > output_aperture {
            return Err(invalid("support target exceeds response aperture"));
        }
        let text_classes = self
            .cohorts
            .iter()
            .take(forward.text_materials.len())
            .map(|cohort| cohort.class_count)
            .sum::<usize>();
        let (text_covector, text_successor, text_cohort_successors) = if target_symbols.is_empty() {
            (None, None, Vec::new())
        } else {
            let text_target = mount_scalar_targets(
                self.surface,
                target_symbols,
                text_classes,
                self.boundary.spec().grain,
            )?;
            let text_logits = gather_prefix(&forward.text_logits, target_symbols.len())?;
            let text_features = gather_prefix(&forward.text_features, target_symbols.len())?;
            let text_face = text_logits
                .normalized_section_return(
                    &text_target,
                    text_classes,
                    terms,
                    NativeNormalizedFaceMeasure::PacketModulus,
                )
                .map_err(invalid)?;
            let difference = text_face.returned_difference().map_err(invalid)?;
            let mut class_blocks = Vec::with_capacity(forward.text_materials.len());
            let mut covectors = Vec::with_capacity(forward.text_materials.len());
            let mut successors = Vec::with_capacity(forward.text_materials.len());
            let mut offset = 0usize;
            for (index, material) in forward.text_materials.iter().enumerate() {
                let count = self.cohorts[index].class_count;
                let block = difference
                    .restrict_components(offset * 2..(offset + count) * 2)
                    .map_err(invalid)?;
                class_blocks.push(block);
                let covector = material
                    .pull_back_enclosed_section(class_blocks.last().unwrap())
                    .map_err(invalid)?;
                let successor = if index == 0 {
                    self.text
                        .stage_covector_return(
                            &text_features,
                            class_blocks.last().unwrap(),
                            step_bits,
                        )
                        .map_err(invalid)?
                } else {
                    self.cohort_materials[index - 1]
                        .stage_covector_return(
                            &text_features,
                            class_blocks.last().unwrap(),
                            step_bits,
                        )
                        .map_err(invalid)?
                };
                covectors.push(covector);
                successors.push(successor);
                offset += count;
            }
            let mut covectors = covectors.into_iter();
            let mut combined = covectors
                .next()
                .ok_or_else(|| invalid("empty decoder cohort return"))?;
            for covector in covectors {
                combined = combined.sum_same_shape(&covector).map_err(invalid)?;
            }
            let mut successors = successors.into_iter();
            let first = successors.next();
            let cohort_successors = successors.collect();
            (Some(combined), first, cohort_successors)
        };

        let support_target = mount_scalar_targets(
            self.surface,
            &[support_length],
            output_aperture + 1,
            self.boundary.spec().grain,
        )?;
        let support_face = forward
            .support_logits
            .normalized_section_return(
                &support_target,
                output_aperture + 1,
                terms,
                NativeNormalizedFaceMeasure::PacketModulus,
            )
            .map_err(invalid)?;
        let support_class_covector = support_face.returned_difference().map_err(invalid)?;
        let support_covector = forward
            .support_material
            .pull_back_enclosed_section(support_class_covector)
            .map_err(invalid)?;
        let boundary_covector = combine_boundary_covector(
            self.surface,
            text_covector.as_ref(),
            &support_covector,
            self.boundary.spec().local_complex,
            output_aperture,
            self.boundary.spec().grain,
        )?;

        let successor = IncidentTextSuccessor {
            text: text_successor,
            text_cohorts: text_cohort_successors,
            support: self
                .support
                .stage_covector_return(&forward.support_features, support_class_covector, step_bits)
                .map_err(invalid)?,
        };
        Ok(IncidentTextReturn {
            text_covector,
            source_covector: None,
            boundary_covector,
            successor,
        })
    }

    /// Compare the producing codec source rows against their admitted class indices. The source
    /// rows and their indices are retained at the producing cut; this path never reads E_in or
    /// invents a target row. Source and response CE blocks are concatenated per cohort and each
    /// contemporary R cohort is staged once; the returned source covector is then available for
    /// the matching E_in return.
    pub fn compare_with_codec(
        &self,
        forward: &IncidentTextForward<'c>,
        response_symbols: &[usize],
        support_length: usize,
        source_rows: &ResidentNormalEnclosureSection<'c>,
        source_class_indices: &[usize],
        terms: SeriesAperture,
        step_bits: u32,
    ) -> Result<IncidentTextReturn<'c>> {
        if source_rows.rows() != source_class_indices.len() || source_rows.rows() == 0 {
            return Err(invalid("codec source reconstruction extent"));
        }
        let output_aperture = self.boundary.spec().output_aperture;
        validate_target_len(output_aperture, response_symbols.len())?;
        if support_length > output_aperture {
            return Err(invalid("support target exceeds response aperture"));
        }
        let classes = forward
            .text_cohorts
            .iter()
            .map(|c| c.class_count)
            .sum::<usize>();
        let source_target = mount_scalar_targets(
            self.surface,
            source_class_indices,
            classes,
            self.boundary.spec().grain,
        )?;
        let source_features = source_rows.append_homogeneous().map_err(invalid)?;
        let source_sections = forward
            .text_materials
            .iter()
            .map(|material| material.read_applied_enclosed_section(&source_features))
            .collect::<std::result::Result<Vec<_>, _>>()
            .map_err(invalid)?;
        let source_logits = join_cohort_sections(&source_sections)?;
        let source_face = source_logits
            .normalized_section_return(
                &source_target,
                classes,
                terms,
                NativeNormalizedFaceMeasure::PacketModulus,
            )
            .map_err(invalid)?;
        let source_difference = source_face.returned_difference().map_err(invalid)?;
        let response_target = mount_scalar_targets(
            self.surface,
            response_symbols,
            classes,
            self.boundary.spec().grain,
        )?;
        let response_features = gather_prefix(&forward.text_features, response_symbols.len())?;
        let response_logits = gather_prefix(&forward.text_logits, response_symbols.len())?;
        let response_face = response_logits
            .normalized_section_return(
                &response_target,
                classes,
                terms,
                NativeNormalizedFaceMeasure::PacketModulus,
            )
            .map_err(invalid)?;
        let response_difference = response_face.returned_difference().map_err(invalid)?;
        let mut source_class_blocks = Vec::new();
        let mut response_class_blocks = Vec::new();
        let mut source_q_blocks = Vec::new();
        let mut response_q_blocks = Vec::new();
        let mut offset = 0usize;
        for (index, material) in forward.text_materials.iter().enumerate() {
            let count = forward.text_cohorts[index].class_count;
            let source_block = source_difference
                .restrict_components(offset * 2..(offset + count) * 2)
                .map_err(invalid)?;
            let response_block = response_difference
                .restrict_components(offset * 2..(offset + count) * 2)
                .map_err(invalid)?;
            source_class_blocks.push(source_block);
            response_class_blocks.push(response_block);
            source_q_blocks.push(
                material
                    .pull_back_enclosed_section(&source_class_blocks.last().unwrap())
                    .map_err(invalid)?,
            );
            response_q_blocks.push(
                material
                    .pull_back_enclosed_section(&response_class_blocks.last().unwrap())
                    .map_err(invalid)?,
            );
            offset += count;
        }
        let mut source_covectors = source_q_blocks.into_iter();
        let mut source_covector = source_covectors
            .next()
            .ok_or_else(|| invalid("codec producing decoder"))?;
        let mut response_covectors = response_q_blocks.into_iter();
        let mut response_covector = response_covectors
            .next()
            .ok_or_else(|| invalid("response producing decoder"))?;
        for covector in source_covectors {
            source_covector = source_covector.sum_same_shape(&covector).map_err(invalid)?;
        }
        for covector in response_covectors {
            response_covector = response_covector
                .sum_same_shape(&covector)
                .map_err(invalid)?;
        }
        // E_in receives the current-coordinate covector. The homogeneous receiver
        // bias is a fixed feature, not another encoder target coordinate.
        let source_covector = source_covector
            .restrict_components(0..2 * self.boundary.spec().local_complex)
            .map_err(invalid)?;
        let features = ResidentNormalEnclosureSection::concatenate_rows(&[
            &source_features,
            &response_features,
        ])
        .map_err(invalid)?;
        let mut successors = Vec::new();
        for (index, _) in forward.text_materials.iter().enumerate() {
            let covectors = ResidentNormalEnclosureSection::concatenate_rows(&[
                &source_class_blocks[index],
                &response_class_blocks[index],
            ])
            .map_err(invalid)?;
            let successor = if index == 0 {
                self.text
                    .stage_covector_return(&features, &covectors, step_bits)
            } else {
                self.cohort_materials[index - 1]
                    .stage_covector_return(&features, &covectors, step_bits)
            }
            .map_err(invalid)?;
            successors.push(successor);
        }
        let mut successors = successors.into_iter();
        let first = successors.next();
        let text_cohort_successors = successors.collect();
        let support_target = mount_scalar_targets(
            self.surface,
            &[support_length],
            output_aperture + 1,
            self.boundary.spec().grain,
        )?;
        let support_face = forward
            .support_logits
            .normalized_section_return(
                &support_target,
                output_aperture + 1,
                terms,
                NativeNormalizedFaceMeasure::PacketModulus,
            )
            .map_err(invalid)?;
        let support_class_covector = support_face.returned_difference().map_err(invalid)?;
        let support_covector = forward
            .support_material
            .pull_back_enclosed_section(support_class_covector)
            .map_err(invalid)?;
        let boundary_covector = combine_boundary_covector(
            self.surface,
            Some(&response_covector),
            &support_covector,
            self.boundary.spec().local_complex,
            output_aperture,
            self.boundary.spec().grain,
        )?;
        let support_successor = self
            .support
            .stage_covector_return(&forward.support_features, support_class_covector, step_bits)
            .map_err(invalid)?;
        Ok(IncidentTextReturn {
            text_covector: Some(response_covector),
            source_covector: Some(source_covector),
            boundary_covector,
            successor: IncidentTextSuccessor {
                text: first,
                text_cohorts: text_cohort_successors,
                support: support_successor,
            },
        })
    }
}

pub(crate) fn validate_response_len(output_aperture: usize, response_len: usize) -> Result<()> {
    if output_aperture == 0 || response_len == 0 || response_len > output_aperture {
        return Err(invalid("response length exceeds declared aperture"));
    }
    Ok(())
}

fn validate_target_len(output_aperture: usize, response_len: usize) -> Result<()> {
    if output_aperture == 0 || response_len > output_aperture {
        return Err(invalid("response target length exceeds declared aperture"));
    }
    Ok(())
}

fn gather_prefix<'c>(
    section: &ResidentNormalEnclosureSection<'c>,
    rows: usize,
) -> Result<ResidentNormalEnclosureSection<'c>> {
    if rows > section.rows() {
        return Err(invalid("resident receiver row restriction"));
    }
    section
        .gather_phase_rows(
            &(0..rows).collect::<Vec<_>>(),
            &vec![ExactWavePhaseTransport::identity(); rows],
            section.components(),
        )
        .map_err(invalid)
}

fn combine_boundary_covector<'c>(
    surface: &'c ResidentSurface<'c>,
    text_covector: Option<&ResidentNormalEnclosureSection<'c>>,
    support_covector: &ResidentNormalEnclosureSection<'c>,
    local_complex: usize,
    output_aperture: usize,
    grain: ResidentGrain,
) -> Result<ResidentNormalEnclosureSection<'c>> {
    let boundary_components = 2 * local_complex;
    let support_q = support_covector
        .restrict_components(0..2 * output_aperture * local_complex)
        .map_err(invalid)?;
    let text_rows = if let Some(text) = text_covector {
        let q = text
            .restrict_components(0..boundary_components)
            .map_err(invalid)?;
        if q.rows() == output_aperture {
            q
        } else {
            let zero = zero_rows(
                surface,
                output_aperture
                    .checked_sub(q.rows())
                    .ok_or_else(|| invalid("text boundary covector rows"))?,
                boundary_components,
                grain,
            )?;
            ResidentNormalEnclosureSection::concatenate_rows(&[&q, &zero]).map_err(invalid)?
        }
    } else {
        zero_rows(surface, output_aperture, boundary_components, grain)?
    };
    let packed = text_rows
        .pack_components(output_aperture)
        .map_err(invalid)?;
    packed.sum_same_shape(&support_q).map_err(invalid)
}

fn join_cohort_sections<'c>(
    sections: &[ResidentNormalEnclosureSection<'c>],
) -> Result<ResidentNormalEnclosureSection<'c>> {
    let first = sections
        .first()
        .ok_or_else(|| invalid("empty decoder cohorts"))?;
    if sections
        .iter()
        .any(|section| section.rows() != first.rows() || section.grain() != first.grain())
    {
        return Err(invalid("decoder cohort section chart"));
    }
    if sections.len() == 1 {
        return ResidentNormalEnclosureSection::concatenate_rows(&[first]).map_err(invalid);
    }
    let mut rows = Vec::with_capacity(first.rows());
    for row in 0..first.rows() {
        let mut joined = sections[0].row(row)?.to_owned().map_err(invalid)?;
        for section in &sections[1..] {
            let next = section.row(row)?.to_owned().map_err(invalid)?;
            joined = joined.view().join(next.view()).map_err(invalid)?;
        }
        rows.push(joined.view().as_section().map_err(invalid)?);
    }
    let refs = rows.iter().collect::<Vec<_>>();
    ResidentNormalEnclosureSection::concatenate_rows(&refs).map_err(invalid)
}

fn zero_rows<'c>(
    surface: &'c ResidentSurface<'c>,
    rows: usize,
    components: usize,
    grain: ResidentGrain,
) -> Result<ResidentNormalEnclosureSection<'c>> {
    if rows == 0 || components == 0 || components % 2 != 0 {
        return Err(invalid("zero boundary covector extent"));
    }
    let values = vec![(0, 0); rows * components];
    let rest = ResidentSectionRest::found(rows, components, ResidentGrain(0), i64::BITS, values)
        .map_err(invalid)?;
    let section = surface.mount_section_rest(&rest).map_err(invalid)?;
    ResidentNormalEnclosureSection::from_points(
        ResidentConstitutiveSection::integers(&section).map_err(invalid)?,
        grain,
    )
    .map_err(invalid)
}

fn mount_scalar_targets<'c>(
    surface: &'c ResidentSurface<'c>,
    targets: &[usize],
    classes: usize,
    grain: ResidentGrain,
) -> Result<ResidentNormalEnclosureSection<'c>> {
    if classes == 0 || targets.is_empty() || targets.iter().any(|target| *target >= classes) {
        return Err(invalid("receiver target scalar index"));
    }
    let mut values = vec![(0, 0); targets.len() * 2 * classes];
    for (row, target) in targets.iter().copied().enumerate() {
        values[row * 2 * classes + 2 * target] = (1, 1);
    }
    let rest = ResidentSectionRest::found(
        targets.len(),
        2 * classes,
        ResidentGrain(0),
        i64::BITS,
        values,
    )
    .map_err(invalid)?;
    let section = surface.mount_section_rest(&rest).map_err(invalid)?;
    ResidentNormalEnclosureSection::from_points(
        ResidentConstitutiveSection::integers(&section).map_err(invalid)?,
        grain,
    )
    .map_err(invalid)
}

#[cfg(test)]
#[path = "incident_receiver_tests.rs"]
mod tests;
