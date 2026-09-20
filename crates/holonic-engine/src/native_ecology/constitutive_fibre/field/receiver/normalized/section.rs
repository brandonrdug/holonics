//! The same normalized receiver over every row of a typed resident section.
//!
//! A region row carries its gathered slot currents as one enclosure ball; a caller-declared
//! coordinate group within that row carries the potentials of one participation. Per group
//! `p = softmax(Re prediction)`; against a comparison face `q` the row returns `q-p` and
//! `J_p(q-p)` with `J_p = diag(p) - p p^T`; and a covector on the normalized face returns
//! `J_p g` on the pre-normalization potentials. This is the single-occurrence receiver's own
//! arithmetic — `normalized_compare_faces` and its shared residual return — carried over rows in
//! one resident passage. No row is read back to the host between rows, and no second softmax
//! is written. The producing operand rows stay the caller's; this face retains no occurrence
//! lineage, because a section row is an address in an exterior chart, not a field occurrence.
use super::*;
use crate::resident_section::SLOT_WORDS;

/// The measure a declared group is normalized under. The exponential face reads the real
/// potentials of the row; the packet face reads a complete complex amplitude carrier and
/// normalizes its squared modulus. These are the two faces the occurrence receiver already
/// distinguishes by its material target chart; neither is a target logit of the other.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeNormalizedFaceMeasure {
    #[default]
    ExponentialPotential,
    PacketModulus,
}

impl NativeNormalizedFaceMeasure {
    /// The measure the declared material target chart already selects: a direct current supplies
    /// exponentiated real potentials, a tensor packet its observed squared-modulus mass.
    pub fn for_target(target: NativeMaterialTarget) -> Self {
        if target.is_direct() {
            Self::ExponentialPotential
        } else {
            Self::PacketModulus
        }
    }

    fn packet(self) -> bool {
        matches!(self, Self::PacketModulus)
    }
}

/// One row of a section face, decoded through the receiver's own report decoder. `source` and
/// `receiving` are both the row's address in this exterior chart: a section row's prediction and
/// its comparison are the same address, not two field occurrences.
pub type NativeNormalizedSectionRowReading =
    NativeNormalizedMaterialReading<usize, NativeNormalizedFaceMeasure>;

/// The resident row-sectioned normalized face. Its participation `p` is returned in the operand
/// chart of its own source section, so a later call consumes it without a host readout. With a
/// comparison operand the returned difference `q-p` and the potential covector `J_p(q-p)` are
/// returned in that same chart. This is a receiver's covector, not a committed displacement.
pub struct NativeNormalizedSection<'c> {
    surface: &'c ResidentSurface<'c>,
    report: ResidentSection<'c>,
    participation: ResidentNormalEnclosureSection<'c>,
    difference: Option<ResidentNormalEnclosureSection<'c>>,
    potential: Option<ResidentNormalEnclosureSection<'c>>,
    rows: usize,
    nodes: usize,
    group_width: usize,
    grain: ResidentGrain,
    series_terms: u32,
    measure: NativeNormalizedFaceMeasure,
}

/// The covector on the pre-normalization potentials of a row-sectioned face. The face depends on
/// the real coordinates alone, so the returned covector's imaginary coordinate is exactly zero.
pub struct NativeNormalizedSectionPullback<'c> {
    surface: &'c ResidentSurface<'c>,
    report: ResidentSection<'c>,
    potentials: ResidentNormalEnclosureSection<'c>,
    rows: usize,
    nodes: usize,
    group_width: usize,
    grain: ResidentGrain,
}

#[derive(Clone, Debug, Serialize)]
pub struct NativeNormalizedSectionPullbackReading {
    pub row: usize,
    pub group_width: usize,
    pub grain: u32,
    /// The face this covector was returned through.
    pub participation: Vec<ExactInterval>,
    /// The supplied covector on the normalized face, at its declared row enclosure.
    pub covector: Vec<ExactInterval>,
    /// g - E_p[g], retained separately from multiplication by p.
    pub centered_covector: Vec<ExactInterval>,
    /// J_p g: the covector on the pre-normalization real potentials of the same group.
    pub potential_covector: Vec<ExactInterval>,
}

/// The declared row chart of one normalized section passage, bounded before it sizes anything.
struct SectionFaceChart {
    rows: usize,
    nodes: usize,
    report_words: usize,
    ball_words: usize,
}

impl SectionFaceChart {
    fn declare(
        rows: usize,
        components: usize,
        group_width: usize,
        grain: ResidentGrain,
    ) -> Result<Self, ConstitutiveFibreError> {
        let fail = || ConstitutiveFibreError::Shape;
        if rows == 0 || components == 0 || components % 2 != 0 || !(1..=120).contains(&grain.0) {
            return Err(fail());
        }
        let nodes = components / 2;
        if group_width == 0 || nodes % group_width != 0 {
            return Err(fail());
        }
        let report_words = nodes.checked_mul(20).ok_or_else(fail)?;
        let ball_words = components
            .checked_add(1)
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(fail)?;
        rows.checked_mul(report_words).ok_or_else(fail)?;
        rows.checked_mul(ball_words).ok_or_else(fail)?;
        if rows > u32::MAX as usize || nodes > u32::MAX as usize / 20 {
            return Err(fail());
        }
        Ok(Self {
            rows,
            nodes,
            report_words,
            ball_words,
        })
    }
}

impl<'c> ResidentNormalEnclosureSection<'c> {
    /// The normalized participation of every row of this section, under the declared groups and
    /// series aperture. The returned section is an operand of this same chart: the participation
    /// in each real coordinate, exactly zero in each imaginary one, and a row radius bounding the
    /// face's own box outward. A nonzero source radius returns a nonzero radius.
    pub fn normalized_participation(
        &self,
        group_width: usize,
        terms: SeriesAperture,
        measure: NativeNormalizedFaceMeasure,
    ) -> Result<NativeNormalizedSection<'c>, ConstitutiveFibreError> {
        self.normalized_section(None, group_width, terms, measure)
    }

    /// The normalized comparison of every row of this prediction section with the observed
    /// section at the same addresses: `p`, `q`, `q-p`, `J_p(q-p)` and the centered difference,
    /// row by row. `measure` is the observed face's measure; the prediction is always the
    /// normalized exponential of its real potentials, as in the occurrence receiver.
    pub fn normalized_section_return(
        &self,
        observed: &Self,
        group_width: usize,
        terms: SeriesAperture,
        measure: NativeNormalizedFaceMeasure,
    ) -> Result<NativeNormalizedSection<'c>, ConstitutiveFibreError> {
        if observed.rows() != self.rows()
            || observed.components() != self.components()
            || observed.grain() != self.grain()
            || !std::ptr::eq(
                observed.resident_section().surface(),
                self.resident_section().surface(),
            )
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        self.normalized_section(Some(observed), group_width, terms, measure)
    }

    fn normalized_section(
        &self,
        observed: Option<&Self>,
        group_width: usize,
        terms: SeriesAperture,
        measure: NativeNormalizedFaceMeasure,
    ) -> Result<NativeNormalizedSection<'c>, ConstitutiveFibreError> {
        if terms.0 == 0 || terms.0 == u32::MAX {
            return Err(ConstitutiveFibreError::Shape);
        }
        let chart =
            SectionFaceChart::declare(self.rows(), self.components(), group_width, self.grain())?;
        let surface = self.resident_section().surface();
        let report = surface.fresh_section(chart.rows, chart.report_words, ResidentGrain(0))?;
        let participation =
            surface.fresh_section(chart.rows, chart.ball_words, ResidentGrain(0))?;
        let difference = surface.fresh_section(chart.rows, chart.ball_words, ResidentGrain(0))?;
        let potential = surface.fresh_section(chart.rows, chart.ball_words, ResidentGrain(0))?;
        let flags = surface.fresh_section(chart.rows, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_rows_normalized_receiver(
                &lane,
                self.resident_section(),
                observed.map(Self::resident_section),
                chart.rows,
                chart.nodes,
                group_width,
                self.grain().0,
                terms,
                measure.packet(),
                &report,
                &participation,
                &difference,
                &potential,
                &flags,
            )?;
            surface.collect_phase_status(&lane, &flags, chart.rows)?;
        }
        passage.close(0, &report, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "row-sectioned normalized receiver: {:?}",
                receipt.obstruction
            )));
        }
        let ball = |section| {
            Self::from_resident(
                surface,
                section,
                chart.rows,
                self.components(),
                self.grain(),
            )
        };
        Ok(NativeNormalizedSection {
            surface,
            report,
            participation: ball(participation)?,
            difference: observed.is_some().then(|| ball(difference)).transpose()?,
            potential: observed.is_some().then(|| ball(potential)).transpose()?,
            rows: chart.rows,
            nodes: chart.nodes,
            group_width,
            grain: self.grain(),
            series_terms: terms.0,
            measure,
        })
    }
}

impl<'c> NativeNormalizedSection<'c> {
    pub fn rows(&self) -> usize {
        self.rows
    }

    /// Complex coordinates per row: one participation coordinate each.
    pub fn nodes(&self) -> usize {
        self.nodes
    }

    pub fn group_width(&self) -> usize {
        self.group_width
    }

    pub fn grain(&self) -> ResidentGrain {
        self.grain
    }

    pub fn series_terms(&self) -> u32 {
        self.series_terms
    }

    pub fn measure(&self) -> NativeNormalizedFaceMeasure {
        self.measure
    }

    /// Whether a comparison face was supplied. Without one, only the participation is returned.
    pub fn compared(&self) -> bool {
        self.difference.is_some()
    }

    /// `p`, in the operand chart of the source section.
    pub fn participation(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.participation
    }

    pub fn into_participation(self) -> ResidentNormalEnclosureSection<'c> {
        self.participation
    }

    /// `q-p`, in that same chart. Present only when a comparison face was supplied.
    pub fn returned_difference(
        &self,
    ) -> Result<&ResidentNormalEnclosureSection<'c>, ConstitutiveFibreError> {
        self.difference
            .as_ref()
            .ok_or(ConstitutiveFibreError::Shape)
    }

    /// `J_p(q-p)`, in that same chart. Present only when a comparison face was supplied.
    pub fn potential_return(
        &self,
    ) -> Result<&ResidentNormalEnclosureSection<'c>, ConstitutiveFibreError> {
        self.potential.as_ref().ok_or(ConstitutiveFibreError::Shape)
    }

    fn rows_of_report(
        surface: &'c ResidentSurface<'c>,
        report: &ResidentSection<'c>,
        rows: usize,
        nodes: usize,
    ) -> Result<Vec<Vec<i128>>, ConstitutiveFibreError> {
        let rest = surface.detach_section(report, 64)?;
        let raw = material_transport::wides(&rest.intervals)?;
        if raw.len() != rows * 10 * nodes {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(raw.chunks_exact(10 * nodes).map(<[i128]>::to_vec).collect())
    }

    /// Explicit cold inspection of every row. Constructing the face reads only its launch
    /// receipt; this is the separate readout.
    pub fn inspect(
        &self,
    ) -> Result<Vec<NativeNormalizedSectionRowReading>, ConstitutiveFibreError> {
        if !self.compared() {
            return Err(ConstitutiveFibreError::Shape);
        }
        Self::rows_of_report(self.surface, &self.report, self.rows, self.nodes)?
            .into_iter()
            .enumerate()
            .map(|(row, raw)| {
                let [
                    prediction,
                    observation,
                    returned_difference,
                    potential_pullback,
                    centered_difference,
                ] = decode_normalized_report(&raw, self.nodes, self.group_width, self.grain.0)?;
                Ok(NativeNormalizedMaterialReading {
                    source: row,
                    receiving: row,
                    group_width: self.group_width,
                    grain: self.grain.0,
                    series_terms: self.series_terms,
                    target_chart: self.measure,
                    prediction,
                    observation,
                    returned_difference,
                    potential_pullback,
                    centered_difference,
                })
            })
            .collect()
    }

    /// The participation of every row on its own, available with or without a comparison face.
    pub fn read_participation(&self) -> Result<Vec<Vec<ExactInterval>>, ConstitutiveFibreError> {
        let scale = num_bigint::BigInt::one() << self.grain.0;
        Self::rows_of_report(self.surface, &self.report, self.rows, self.nodes)?
            .into_iter()
            .map(|raw| {
                (0..self.nodes)
                    .map(|i| {
                        ExactInterval::new(
                            Rat::new(raw[10 * i].into(), scale.clone()),
                            Rat::new(raw[10 * i + 1].into(), scale.clone()),
                        )
                        .map_err(|e| ConstitutiveFibreError::Arithmetic(e.to_string()))
                    })
                    .collect()
            })
            .collect()
    }

    /// Return a covector declared on this normalized face to the pre-normalization potentials of
    /// the same rows and groups: `J_p g`, with `J_p` the face's own Jacobian. The face is the
    /// normalized exponential of the real coordinates alone, so the returned imaginary
    /// coordinate is exactly zero. This is the dual of the differential, not a committed step.
    pub fn pull_back(
        &self,
        covector: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<NativeNormalizedSectionPullback<'c>, ConstitutiveFibreError> {
        if covector.rows() != self.rows
            || covector.components() != 2 * self.nodes
            || covector.grain() != self.grain
            || !std::ptr::eq(covector.resident_section().surface(), self.surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let chart =
            SectionFaceChart::declare(self.rows, 2 * self.nodes, self.group_width, self.grain)?;
        let surface = self.surface;
        let report = surface.fresh_section(chart.rows, chart.report_words, ResidentGrain(0))?;
        let potentials = surface.fresh_section(chart.rows, chart.ball_words, ResidentGrain(0))?;
        let flags = surface.fresh_section(chart.rows, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_rows_normalized_pullback(
                &lane,
                &self.report,
                covector.resident_section(),
                chart.rows,
                chart.nodes,
                self.group_width,
                self.grain.0,
                &report,
                &potentials,
                &flags,
            )?;
            surface.collect_phase_status(&lane, &flags, chart.rows)?;
        }
        passage.close(0, &report, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "row-sectioned normalized pullback: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativeNormalizedSectionPullback {
            surface,
            report,
            potentials: ResidentNormalEnclosureSection::from_resident(
                surface,
                potentials,
                chart.rows,
                2 * self.nodes,
                self.grain,
            )?,
            rows: chart.rows,
            nodes: chart.nodes,
            group_width: self.group_width,
            grain: self.grain,
        })
    }
}

impl<'c> NativeNormalizedSectionPullback<'c> {
    pub fn rows(&self) -> usize {
        self.rows
    }

    pub fn group_width(&self) -> usize {
        self.group_width
    }

    pub fn grain(&self) -> ResidentGrain {
        self.grain
    }

    /// The returned covector on the pre-normalization potentials, in the operand chart.
    pub fn potentials(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.potentials
    }

    pub fn into_potentials(self) -> ResidentNormalEnclosureSection<'c> {
        self.potentials
    }

    pub fn inspect(
        &self,
    ) -> Result<Vec<NativeNormalizedSectionPullbackReading>, ConstitutiveFibreError> {
        let rest = self.surface.detach_section(&self.report, 64)?;
        let raw = material_transport::wides(&rest.intervals)?;
        if raw.len() != self.rows * 10 * self.nodes {
            return Err(ConstitutiveFibreError::Shape);
        }
        let scale = num_bigint::BigInt::one() << self.grain.0;
        raw.chunks_exact(10 * self.nodes)
            .enumerate()
            .map(|(row, raw)| {
                let read = |offset: usize| -> Result<Vec<ExactInterval>, ConstitutiveFibreError> {
                    (0..self.nodes)
                        .map(|i| {
                            ExactInterval::new(
                                Rat::new(raw[10 * i + offset].into(), scale.clone()),
                                Rat::new(raw[10 * i + offset + 1].into(), scale.clone()),
                            )
                            .map_err(|e| ConstitutiveFibreError::Arithmetic(e.to_string()))
                        })
                        .collect()
                };
                Ok(NativeNormalizedSectionPullbackReading {
                    row,
                    group_width: self.group_width,
                    grain: self.grain.0,
                    participation: read(0)?,
                    covector: read(4)?,
                    centered_covector: read(8)?,
                    potential_covector: read(6)?,
                })
            })
            .collect()
    }
}

#[cfg(test)]
mod tests;
