//! A source-qualified normalized receiver over the material target chart. The receiver uses
//! real coordinate potentials; the original complex reports and their numerical fibres stay held.
use super::*;
use crate::exact_value::ExactInterval;
use crate::resident_section::SeriesAperture;
use num_bigint::BigInt;
use num_traits::{One, Zero};

/// Resident p, q, q-p, and J_p(q-p) for disjoint, caller-declared coordinate groups. This is
/// the receiver's returned covector, not an automatically committed developmental displacement.
pub struct NativeNormalizedMaterialReturn<
    'chart,
    Provenance = NativeFieldLineage,
    Chart = NativeMaterialTarget,
    Origin = (
        Rc<()>,
        Rc<ResidentSection<'chart>>,
        Rc<ResidentSection<'chart>>,
    ),
> {
    surface: &'chart ResidentSurface<'chart>,
    pub(in super::super) output: Rc<ResidentSection<'chart>>,
    // Source ownership is retained, not type-erased: the field owns its immutable carriers;
    // another operation may borrow its complete already-owned comparison.
    origin: Origin,
    source: Provenance,
    receiving: Provenance,
    group_width: usize,
    grain: u32,
    series_terms: u32,
    nodes: usize,
    target_chart: Chart,
}

#[derive(Clone, Debug, Serialize)]
pub struct NativeNormalizedMaterialReading<
    Provenance = NativeFieldLineage,
    Chart = NativeMaterialTarget,
> {
    pub source: Provenance,
    pub receiving: Provenance,
    pub group_width: usize,
    pub grain: u32,
    pub series_terms: u32,
    pub target_chart: Chart,
    pub prediction: Vec<ExactInterval>,
    pub observation: Vec<ExactInterval>,
    /// q-p. In this unit potential chart this is also the negative potential derivative of
    /// KL(q || p), with q held fixed. It need not be small when the probability Jacobian is.
    pub returned_difference: Vec<ExactInterval>,
    /// J_p(q-p): the negative potential derivative for half squared probability discrepancy.
    /// This is a different receiver metric from relative entropy, not a universal update law.
    pub potential_pullback: Vec<ExactInterval>,
    /// r-E_p[r], retained separately from multiplication by p.
    pub centered_difference: Vec<ExactInterval>,
}

/// The ten-wide report decoder, shared by the occurrence receiver and the row-sectioned one.
/// `raw` is one row: `10*nodes` signed wides read as five outward interval families at the
/// declared grain. Both probability faces are checked against the unit interval and against
/// their declared group sums; a face that cannot bracket one is uncertain, not repaired.
fn decode_normalized_report(
    raw: &[i128],
    nodes: usize,
    group_width: usize,
    grain: u32,
) -> Result<[Vec<ExactInterval>; 5], ConstitutiveFibreError> {
    if raw.len() != 10 * nodes || group_width == 0 || nodes % group_width != 0 {
        return Err(ConstitutiveFibreError::Shape);
    }
    let scale = BigInt::one() << grain;
    let read = |offset: usize| -> Result<Vec<ExactInterval>, ConstitutiveFibreError> {
        (0..nodes)
            .map(|i| {
                ExactInterval::new(
                    Rat::new(raw[10 * i + offset].into(), scale.clone()),
                    Rat::new(raw[10 * i + offset + 1].into(), scale.clone()),
                )
                .map_err(|e| ConstitutiveFibreError::Arithmetic(e.to_string()))
            })
            .collect()
    };
    let prediction = read(0)?;
    let observation = read(2)?;
    for family in [&prediction, &observation] {
        if family
            .iter()
            .any(|v| v.lower < Rat::zero() || v.upper > Rat::one())
        {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        for group in family.chunks_exact(group_width) {
            let lower: Rat = group.iter().map(|v| &v.lower).sum();
            let upper: Rat = group.iter().map(|v| &v.upper).sum();
            if lower > Rat::one() || upper < Rat::one() {
                return Err(ConstitutiveFibreError::Uncertain);
            }
        }
    }
    Ok([
        prediction,
        observation,
        read(4)?,
        read(6)?,
        read(8)?,
    ])
}

impl<'chart, Provenance: Clone, Chart: Clone, Origin>
    NativeNormalizedMaterialReturn<'chart, Provenance, Chart, Origin>
{
    pub fn origin(&self) -> &Origin {
        &self.origin
    }

    /// Bind the shared receiver/decoder to an actual source owner and its declared chart.
    /// Only typed native producers call this; external callers cannot forge report provenance.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn from_resident(
        surface: &'chart ResidentSurface<'chart>,
        output: Rc<ResidentSection<'chart>>,
        origin: Origin,
        source: Provenance,
        receiving: Provenance,
        group_width: usize,
        grain: u32,
        series_terms: u32,
        nodes: usize,
        target_chart: Chart,
    ) -> Self {
        Self {
            surface,
            output,
            origin,
            source,
            receiving,
            group_width,
            grain,
            series_terms,
            nodes,
            target_chart,
        }
    }
    /// Explicit cold inspection. Constructing the resident return reads only its launch receipt.
    pub fn inspect(
        &self,
    ) -> Result<NativeNormalizedMaterialReading<Provenance, Chart>, ConstitutiveFibreError> {
        let rest = self.surface.detach_section(&self.output, 64)?;
        let raw = material_transport::wides(&rest.intervals)?;
        let [prediction, observation, returned_difference, potential_pullback, centered_difference] =
            decode_normalized_report(&raw, self.nodes, self.group_width, self.grain)?;
        Ok(NativeNormalizedMaterialReading {
            source: self.source.clone(),
            receiving: self.receiving.clone(),
            group_width: self.group_width,
            grain: self.grain,
            series_terms: self.series_terms,
            target_chart: self.target_chart.clone(),
            prediction,
            observation,
            returned_difference,
            potential_pullback,
            centered_difference,
        })
    }
}

impl<'chart> NativeConstitutiveField<'chart> {
    /// Compare an actual received material occurrence with the prediction of its actual source.
    /// Grouping is an exterior receiver declaration, not native topology or an alphabet.
    /// Within each group p=softmax(Re prediction). Direct current retains its historical
    /// exponentiated-observation chart; a tensor packet uses its observed squared-modulus mass.
    /// The returned potential covector J_p(q-p) is the negative derivative of half squared
    /// receiver discrepancy with the observed face fixed. Original complex carriers stay held.
    pub fn normalized_material_return(
        &self,
        receiving: usize,
        group_width: usize,
        terms: SeriesAperture,
    ) -> Result<Option<NativeNormalizedMaterialReturn<'chart>>, ConstitutiveFibreError> {
        let target_chart = self.material_target().unwrap_or_default();
        let nodes = target_chart
            .dimension(self.nodes())
            .ok_or(ConstitutiveFibreError::Shape)?;
        if group_width == 0 || nodes % group_width != 0 || terms.0 == 0 || terms.0 == u32::MAX {
            return Err(ConstitutiveFibreError::Shape);
        }
        let event = self
            .history
            .get(receiving)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        let Some(source) = event.lineage.observed_source() else {
            return Ok(None);
        };
        let producer = self
            .history
            .get(source)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        let surface = self.relation.surface;
        let prediction = producer.with_resident(surface, |r| Ok(r.transport.clone()))?;
        let observation = event.with_resident(surface, |r| Ok(r.transport.clone()))?;
        let (Some(prediction), Some(observation)) = (prediction, observation) else {
            return Ok(None);
        };
        let report_words = self
            .material_transport_source()
            .and_then(|source| source.report_words_for(self.nodes(), target_chart))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if prediction.width() != report_words || observation.width() != report_words {
            return Err(ConstitutiveFibreError::Shape);
        }
        let grain = self.transport_grain()?;
        let words = nodes.checked_mul(20).ok_or(ConstitutiveFibreError::Shape)?;
        let output = Rc::new(surface.fresh_section(1, words, ResidentGrain(0))?);
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_field_normalized_receiver(
                &lane,
                &prediction,
                &observation,
                nodes,
                group_width,
                grain,
                terms,
                !target_chart.is_direct(),
                &output,
            )?;
        }
        passage.close(0, &output, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "normalized material return: {:?}",
                receipt.obstruction
            )));
        }
        Ok(Some(NativeNormalizedMaterialReturn {
            surface,
            output,
            origin: (self.owner.clone(), prediction, observation),
            source: producer.lineage.clone(),
            receiving: event.lineage.clone(),
            group_width,
            grain,
            series_terms: terms.0,
            nodes,
            target_chart,
        }))
    }
}

// ---------------------------------------------------------------------------------------------
// Plan phase 7: the normalized and pair receivers as core receiver elements
// ---------------------------------------------------------------------------------------------
//
// [definition] Each resident receiver here is a Holon at ports with its declared power term
// (`holonic_core::law::receiver`, `Holon/Law.lean`): the normalized face and the comparison return
// are readings at zero flow (`coholon_reading_power`) — `p = softmax(Re s)` is a nonlinear reading,
// not a current; the phase and pair participations inject the drive `y` into the field and are
// exterior drives whose delivered power `⟨e_D, y⟩` the field's balance counts
// (`exterior_drive_balance`, `EnergyBalance::joined_active`); every covector return (the normalized
// pullback `J_p g` with `J_p` symmetric, the participation adjoints and the material source
// pullback) is a pullback that preserves power (`pullback_law`, `softmaxJacobian_transpose`). The
// declarations are host-side and read only extents already carried; no kernel, launch or returned
// value changes. Ports count real-coded coordinates.

use holonic_core::law::receiver::{ActiveReceiver, ReceiverPower};

/// Real-coded coordinates of one resident enclosure section: `rows × components`.
fn real_coordinates(section: &ResidentNormalEnclosureSection<'_>) -> usize {
    section.rows() * section.components()
}

/// **The power a drive current delivers, enclosed** (plan phase 7): `⟨e_D, y⟩` over the drive's
/// returned balls against a declared real-coded drive effort `e_D`. Per row the centre pairs
/// exactly and the ball contributes at most `‖e_D‖₂ r ≤ ‖e_D‖₁ r` (Cauchy–Schwarz), so the exact
/// delivered power of every current in the returned balls lies in the returned interval. This reads
/// the drive back; it launches nothing.
fn delivered_power_enclosure(
    output: &ResidentNormalEnclosureSection<'_>,
    drive_effort: &[Rat],
) -> Result<ExactInterval, ConstitutiveFibreError> {
    let components = output.components();
    if drive_effort.len() != real_coordinates(output) {
        return Err(ConstitutiveFibreError::Shape);
    }
    let mut centre = Rat::zero();
    let mut spread = Rat::zero();
    for (ball, effort) in output
        .inspect_rows()?
        .iter()
        .zip(drive_effort.chunks_exact(components.max(1)))
    {
        if 2 * ball.center.len() != components {
            return Err(ConstitutiveFibreError::Shape);
        }
        for (current, pair) in ball.center.iter().zip(effort.chunks_exact(2)) {
            centre += &current.real * &pair[0] + &current.imaginary * &pair[1];
        }
        let l1: Rat = effort
            .iter()
            .map(|e| if e < &Rat::zero() { -e } else { e.clone() })
            .sum();
        spread += l1 * &ball.radius;
    }
    ExactInterval::new(&centre - &spread, &centre + &spread)
        .map_err(|e| ConstitutiveFibreError::Arithmetic(e.to_string()))
}

impl<Provenance: Clone, Chart: Clone, Origin>
    NativeNormalizedMaterialReturn<'_, Provenance, Chart, Origin>
{
    /// **This comparison as a receiver element**: a reading of the prediction's `nodes` real
    /// potentials at zero flow. Its `q − p` and `J_p(q − p)` are covectors returned to the caller,
    /// not currents delivered into the field.
    pub fn receiver_element(&self) -> ActiveReceiver {
        ActiveReceiver::declared(
            "normalized material return",
            self.nodes,
            ReceiverPower::Reading,
        )
    }
}

mod pullback;
pub use pullback::{
    NativeMaterialPullbackMetric, NativeMaterialSourcePullback, NativeMaterialSourcePullbackReading,
};

mod section;
pub use section::{
    NativeNormalizedFaceMeasure, NativeNormalizedSection, NativeNormalizedSectionPullback,
    NativeNormalizedSectionPullbackReading, NativeNormalizedSectionRowReading,
};

mod phase;
mod pair;
pub use pair::{NativePairParticipation, NativePairParticipationAdjoint};
pub use phase::{NativePhaseParticipation, NativePhaseParticipationAdjoint};

#[cfg(test)]
mod tests;
