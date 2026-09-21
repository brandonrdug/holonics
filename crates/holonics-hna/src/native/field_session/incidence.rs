//! Native preparation of one analytic receiving junction.
//!
//! The exterior text chart does not choose this restriction.  A declaration is compiled from
//! the validated analytic wave law, and a pre-target packet contains one exact complex current
//! for every junction in sorted identifier order.  The resident map returns the receiver current
//! and the admitted transported differences in one packet; the two current views below are only
//! borrowed charts of that single returned packet.

use super::super::field_geometry::GeometricFieldSpec;
use crate::native::NativeSessionError;
use holonic_engine::{
    AnalyticFieldArcId, AnalyticFieldJunctionId, DimensionalWaveModeId, ExactAnalyticFieldJunction,
    ExactAnalyticFieldWaveLaw, ExactWavePhaseTransport,
    exact_linear::{BilinearOperator, BilinearProductCore, BilinearRealization, ExactRatMatrix},
    native_ecology::constitutive_fibre::ResidentConstitutiveCurrent,
    resident_section::{
        ResidentBilinearMap, ResidentBilinearReturn, ResidentSection, ResidentSurface,
    },
};
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, sync::Arc};

fn invalid(message: impl ToString) -> NativeSessionError {
    NativeSessionError::Application(message.to_string())
}

/// One admitted arc at the selected receiver after its declared delay has been applied.
///
/// The source and target identifiers, arc identifier, selected mode and exact phase transport
/// are retained together.  This is the frame/incidence witness for a condition coordinate; it is
/// not a caller-authored positional offset.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeFieldIncomingArc {
    pub arc: AnalyticFieldArcId,
    pub from: AnalyticFieldJunctionId,
    pub to: AnalyticFieldJunctionId,
    pub mode: DimensionalWaveModeId,
    pub delay: u32,
    pub phase: ExactWavePhaseTransport,
}

/// Provenance for an identity self comparison which was available in the declaration but carried
/// no contrast.  Keeping this witness prevents omission from being mistaken for an unexamined
/// source port.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeFieldOmittedSelfComparison {
    pub receiver: AnalyticFieldJunctionId,
    pub phase: ExactWavePhaseTransport,
    pub reason: String,
    pub arc: Option<AnalyticFieldArcId>,
}

/// Serializable source declaration and its two exact linear restrictions.
///
/// `junctions` is sorted by identifier and gives the input packet's coordinate order.  The
/// complete geometry is retained so a checkpoint can revalidate the same analytic wave law
/// before remounting the resident map; the matrices are retained as the exact compiled chart,
/// rather than regenerated from an untrusted host array.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeFieldIncidenceDeclaration {
    pub geometry: GeometricFieldSpec,
    pub receiver: AnalyticFieldJunctionId,
    pub mode: DimensionalWaveModeId,
    pub source_complex: usize,
    pub preparation_complex: usize,
    pub junctions: Vec<ExactAnalyticFieldJunction>,
    pub incoming: Vec<NativeFieldIncomingArc>,
    pub omitted_self_comparisons: Vec<NativeFieldOmittedSelfComparison>,
    pub source_restriction: ExactRatMatrix,
    pub condition_restriction: ExactRatMatrix,
}

/// One resident incidence compiler.  Its right port is the mounted unit packet and is shared by
/// every preparation, so preparation never remounts or reads a caller-owned unit coordinate.
pub struct NativeFieldIncidence<'c> {
    declaration: Arc<NativeFieldIncidenceDeclaration>,
    combined: BilinearRealization,
    resident: ResidentBilinearMap<'c>,
    unit: ResidentSection<'c>,
}

/// The one applied output of a pre-target preparation.  `source()` and `condition()` borrow
/// disjoint component ranges of `output_packet()` and preserve the packet's exact denominator.
pub struct PreparedFieldIncidence<'c> {
    declaration: Arc<NativeFieldIncidenceDeclaration>,
    output: ResidentBilinearReturn<'c>,
}

impl NativeFieldIncidenceDeclaration {
    pub fn source_complex(&self) -> usize {
        self.source_complex
    }

    pub fn condition_complex(&self) -> usize {
        self.condition_restriction.rows() / 2
    }

    pub fn preparation_complex(&self) -> usize {
        self.preparation_complex
    }

    pub fn junction_count(&self) -> usize {
        self.junctions.len()
    }

    pub fn incoming_count(&self) -> usize {
        self.incoming.len()
    }

    pub fn source_restriction(&self) -> &ExactRatMatrix {
        &self.source_restriction
    }

    pub fn condition_restriction(&self) -> &ExactRatMatrix {
        &self.condition_restriction
    }
}

impl<'c> NativeFieldIncidence<'c> {
    /// Compile the source/condition chart for one receiving junction.
    ///
    /// `source_complex` is the constituted field's complex width (currently `3 * roots`).  It is
    /// deliberately supplied by the field owner: no alphabet or presentation chart participates
    /// in this declaration.
    pub fn compile(
        surface: &'c ResidentSurface<'c>,
        geometry: &GeometricFieldSpec,
        receiver: AnalyticFieldJunctionId,
        source_complex: usize,
    ) -> Result<Self, NativeSessionError> {
        let declaration = compile_declaration(geometry, receiver, source_complex)?;
        Self::mount_declaration(surface, declaration)
    }

    /// Remount an already serialized declaration after the same source geometry has been
    /// revalidated.  The declaration owns its matrices and phase witnesses, so this performs no
    /// host numerical read and cannot silently select a new incidence chart.
    pub fn from_declaration(
        surface: &'c ResidentSurface<'c>,
        declaration: NativeFieldIncidenceDeclaration,
    ) -> Result<Self, NativeSessionError> {
        validate_declaration(&declaration)?;
        Self::mount_declaration(surface, declaration)
    }
    fn mount_declaration(
        surface: &'c ResidentSurface<'c>,
        declaration: NativeFieldIncidenceDeclaration,
    ) -> Result<Self, NativeSessionError> {
        let declaration = Arc::new(declaration);
        let combined = combined_realization(
            &declaration.source_restriction,
            &declaration.condition_restriction,
        )?;
        let resident = ResidentBilinearMap::mount(surface, &combined).map_err(invalid)?;
        let unit = surface
            .mount_exact_rational_packet(&[Rat::one()])
            .map_err(invalid)?;
        Ok(Self {
            declaration,
            combined,
            resident,
            unit,
        })
    }

    pub fn declaration(&self) -> &NativeFieldIncidenceDeclaration {
        self.declaration.as_ref()
    }

    pub fn source_complex(&self) -> usize {
        self.declaration.source_complex()
    }

    pub fn condition_complex(&self) -> usize {
        self.declaration.condition_complex()
    }

    pub fn preparation_complex(&self) -> usize {
        self.declaration.preparation_complex()
    }

    pub fn junction_count(&self) -> usize {
        self.declaration.junction_count()
    }

    pub fn incoming_count(&self) -> usize {
        self.declaration.incoming_count()
    }

    pub fn source_restriction(&self) -> &ExactRatMatrix {
        &self.declaration.source_restriction
    }

    pub fn condition_restriction(&self) -> &ExactRatMatrix {
        &self.declaration.condition_restriction
    }

    /// Apply the restrictions to one exact rational pre-target packet.  The packet's columns are
    /// the sorted junction IDs, each carrying `source_complex` complex current coordinates.
    pub fn prepare(
        &self,
        packet: &ResidentSection<'c>,
    ) -> Result<PreparedFieldIncidence<'c>, NativeSessionError> {
        let expected_complex = self.preparation_complex();
        let expected_width = expected_complex
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .ok_or_else(|| invalid("analytic incidence preparation width overflow"))?;
        if packet.rows() != 1 || packet.width() != expected_width {
            return Err(invalid("analytic incidence preparation packet shape"));
        }
        let output = self.resident.apply(packet, &self.unit).map_err(invalid)?;
        Ok(PreparedFieldIncidence {
            declaration: self.declaration.clone(),
            output,
        })
    }

    /// A preparation can only be consumed by the compiled incidence which produced it.
    pub fn belongs_to(&self, preparation: &PreparedFieldIncidence<'c>) -> bool {
        Arc::ptr_eq(&self.declaration, &preparation.declaration)
    }

    /// The resident map is exposed for the existing operator owner; preparation should normally
    /// go through [`Self::prepare`] so the packet and incidence binding remain checked together.
    pub fn resident_map(&self) -> &ResidentBilinearMap<'c> {
        &self.resident
    }

    /// The factored linear realization used by the resident map, retained for checkpoint
    /// inspection and exact receiver rebinding.
    pub fn realization(&self) -> &BilinearRealization {
        &self.combined
    }
}

impl<'c> PreparedFieldIncidence<'c> {
    pub fn declaration(&self) -> &NativeFieldIncidenceDeclaration {
        self.declaration.as_ref()
    }

    pub fn output_packet(&self) -> &ResidentSection<'c> {
        self.output.output()
    }

    pub fn source(&self) -> Result<ResidentConstitutiveCurrent<'_, 'c>, NativeSessionError> {
        let current = ResidentConstitutiveCurrent::rational(self.output.output())?;
        let width = self
            .declaration
            .source_complex
            .checked_mul(2)
            .ok_or_else(|| invalid("source current width overflow"))?;
        Ok(current.restrict_components(0..width)?)
    }

    pub fn condition(&self) -> Result<ResidentConstitutiveCurrent<'_, 'c>, NativeSessionError> {
        let current = ResidentConstitutiveCurrent::rational(self.output.output())?;
        let start = self
            .declaration
            .source_complex
            .checked_mul(2)
            .ok_or_else(|| invalid("source current width overflow"))?;
        let end = start
            .checked_add(
                self.declaration
                    .condition_complex()
                    .checked_mul(2)
                    .ok_or_else(|| invalid("condition current width overflow"))?,
            )
            .ok_or_else(|| invalid("condition current width overflow"))?;
        Ok(current.restrict_components(start..end)?)
    }

    pub fn source_complex(&self) -> usize {
        self.declaration.source_complex()
    }

    pub fn condition_complex(&self) -> usize {
        self.declaration.condition_complex()
    }

    pub fn preparation_complex(&self) -> usize {
        self.declaration.preparation_complex()
    }

    pub fn junction_count(&self) -> usize {
        self.declaration.junction_count()
    }

    pub fn incoming_count(&self) -> usize {
        self.declaration.incoming_count()
    }
}

fn compile_declaration(
    geometry: &GeometricFieldSpec,
    receiver: AnalyticFieldJunctionId,
    source_complex: usize,
) -> Result<NativeFieldIncidenceDeclaration, NativeSessionError> {
    if source_complex == 0 || source_complex % 3 != 0 {
        return Err(invalid(
            "constituted field current width must be a nonzero multiple of 3",
        ));
    }
    let law = ExactAnalyticFieldWaveLaw::new(
        geometry.field.clone(),
        geometry.junctions.clone(),
        geometry.arcs.clone(),
        geometry.modes.clone(),
    )
    .map_err(|e| invalid(format!("analytic field law: {e}")))?;
    if !law.junctions().contains_key(&receiver) {
        return Err(invalid(
            "receiving junction is outside the analytic field law",
        ));
    }
    if !law.modes().contains_key(&geometry.mode) {
        return Err(invalid("analytic incidence mode is outside its source law"));
    }

    let junctions: Vec<_> = law.junctions().values().cloned().collect();
    let indices: BTreeMap<_, _> = junctions
        .iter()
        .enumerate()
        .map(|(index, junction)| (junction.id, index))
        .collect();
    let receiver_index = *indices
        .get(&receiver)
        .ok_or_else(|| invalid("receiving junction index is absent"))?;
    let mut incoming = Vec::new();
    let mut omitted_self_comparisons = Vec::new();
    let mut identity_self_arc = false;

    for arc in law.arcs().values().filter(|arc| arc.to == receiver) {
        let phase_step = arc
            .modal_phase_step
            .get(&geometry.mode)
            .ok_or_else(|| invalid("incoming arc does not carry the selected mode"))?;
        let phase = phase_step.pow(arc.delay);
        validate_phase(&phase)?;
        if arc.from == receiver && phase == ExactWavePhaseTransport::identity() {
            identity_self_arc = true;
            omitted_self_comparisons.push(NativeFieldOmittedSelfComparison {
                receiver,
                phase,
                reason: "identity self comparison has zero contrast".into(),
                arc: Some(arc.id),
            });
            continue;
        }
        incoming.push(NativeFieldIncomingArc {
            arc: arc.id,
            from: arc.from,
            to: arc.to,
            mode: geometry.mode,
            delay: arc.delay,
            phase,
        });
    }
    if geometry.self_comparison && !identity_self_arc {
        omitted_self_comparisons.push(NativeFieldOmittedSelfComparison {
            receiver,
            phase: ExactWavePhaseTransport::identity(),
            reason: "declared self comparison has zero contrast".into(),
            arc: None,
        });
    }
    if incoming.is_empty() {
        return Err(invalid(
            "receiving junction has no nonzero admitted incoming contrast",
        ));
    }

    let input_columns = junctions
        .len()
        .checked_mul(source_complex)
        .and_then(|n| n.checked_mul(2))
        .ok_or_else(|| invalid("analytic incidence preparation width overflow"))?;
    let preparation_complex = junctions
        .len()
        .checked_mul(source_complex)
        .ok_or_else(|| invalid("analytic incidence preparation width overflow"))?;
    let condition_complex = incoming
        .len()
        .checked_mul(source_complex)
        .ok_or_else(|| invalid("analytic incidence condition width overflow"))?;
    let source_rows = source_complex
        .checked_mul(2)
        .ok_or_else(|| invalid("analytic incidence source width overflow"))?;
    let condition_rows = condition_complex
        .checked_mul(2)
        .ok_or_else(|| invalid("analytic incidence condition width overflow"))?;
    let source_restriction = source_matrix(
        junctions.len(),
        source_complex,
        receiver_index,
        input_columns,
        source_rows,
    )?;
    let condition_restriction = condition_matrix(
        &incoming,
        &indices,
        source_complex,
        input_columns,
        condition_rows,
    )?;
    Ok(NativeFieldIncidenceDeclaration {
        geometry: geometry.clone(),
        receiver,
        mode: geometry.mode,
        source_complex,
        preparation_complex,
        junctions,
        incoming,
        omitted_self_comparisons,
        source_restriction,
        condition_restriction,
    })
}

fn validate_phase(phase: &ExactWavePhaseTransport) -> Result<(), NativeSessionError> {
    if !phase.is_unit() {
        return Err(invalid(
            "analytic incidence phase is not an exact unit conic value",
        ));
    }
    Ok(())
}

fn validate_declaration(
    declaration: &NativeFieldIncidenceDeclaration,
) -> Result<(), NativeSessionError> {
    let expected = compile_declaration(
        &declaration.geometry,
        declaration.receiver,
        declaration.source_complex,
    )?;
    if &expected != declaration {
        return Err(invalid(
            "incidence declaration does not match its analytic source law",
        ));
    }
    Ok(())
}

fn source_matrix(
    junction_count: usize,
    source_complex: usize,
    receiver: usize,
    input_columns: usize,
    rows: usize,
) -> Result<ExactRatMatrix, NativeSessionError> {
    let mut matrix = vec![vec![Rat::zero(); input_columns]; rows];
    let input_start = receiver
        .checked_mul(source_complex)
        .and_then(|n| n.checked_mul(2))
        .ok_or_else(|| invalid("receiver current offset overflow"))?;
    let expected_rows = source_complex
        .checked_mul(2)
        .ok_or_else(|| invalid("receiver current width overflow"))?;
    if receiver >= junction_count || rows != expected_rows {
        return Err(invalid("receiver current restriction dimensions"));
    }
    for component in 0..source_complex {
        matrix[2 * component][input_start + 2 * component] = Rat::one();
        matrix[2 * component + 1][input_start + 2 * component + 1] = Rat::one();
    }
    ExactRatMatrix::new(matrix).map_err(invalid)
}

fn condition_matrix(
    incoming: &[NativeFieldIncomingArc],
    indices: &BTreeMap<AnalyticFieldJunctionId, usize>,
    source_complex: usize,
    input_columns: usize,
    rows: usize,
) -> Result<ExactRatMatrix, NativeSessionError> {
    let expected_rows = incoming
        .len()
        .checked_mul(source_complex)
        .and_then(|n| n.checked_mul(2))
        .ok_or_else(|| invalid("incoming contrast width overflow"))?;
    if rows != expected_rows {
        return Err(invalid("incoming contrast restriction dimensions"));
    }
    let receiver = incoming[0].to;
    let receiver_index = *indices
        .get(&receiver)
        .ok_or_else(|| invalid("incoming contrast receiver index is absent"))?;
    let mut matrix = vec![vec![Rat::zero(); input_columns]; rows];
    for (port, arc) in incoming.iter().enumerate() {
        let source_index = *indices
            .get(&arc.from)
            .ok_or_else(|| invalid("incoming contrast source index is absent"))?;
        let source_start = source_index
            .checked_mul(source_complex)
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(|| invalid("incoming source offset overflow"))?;
        let receiver_start = receiver_index
            .checked_mul(source_complex)
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(|| invalid("incoming receiver offset overflow"))?;
        let row_start = port
            .checked_mul(source_complex)
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(|| invalid("incoming contrast row offset overflow"))?;
        for component in 0..source_complex {
            let row_real = row_start + 2 * component;
            let row_imag = row_real + 1;
            let source_real = source_start + 2 * component;
            let source_imag = source_real + 1;
            let receiver_real = receiver_start + 2 * component;
            let receiver_imag = receiver_real + 1;
            matrix[row_real][source_real] += arc.phase.cosine.clone();
            matrix[row_real][source_imag] -= arc.phase.sine.clone();
            matrix[row_imag][source_real] += arc.phase.sine.clone();
            matrix[row_imag][source_imag] += arc.phase.cosine.clone();
            matrix[row_real][receiver_real] -= Rat::one();
            matrix[row_imag][receiver_imag] -= Rat::one();
        }
    }
    ExactRatMatrix::new(matrix).map_err(invalid)
}

fn combined_realization(
    source: &ExactRatMatrix,
    condition: &ExactRatMatrix,
) -> Result<BilinearRealization, NativeSessionError> {
    if source.columns() == 0
        || source.columns() != condition.columns()
        || source.rows() == 0
        || condition.rows() == 0
    {
        return Err(invalid(
            "incidence restrictions require nonempty matching input ports",
        ));
    }
    let rows = source
        .to_rows()
        .into_iter()
        .chain(condition.to_rows())
        .collect::<Vec<_>>();
    let target_matrix = ExactRatMatrix::new(rows).map_err(invalid)?;
    let factor = target_matrix.rank_factorization().map_err(invalid)?;
    let left = if factor.derived_rank == 0 {
        ExactRatMatrix::zero(1, target_matrix.columns()).map_err(invalid)?
    } else {
        factor.right
    };
    let right = ExactRatMatrix::new(vec![vec![Rat::one()]; left.rows()]).map_err(invalid)?;
    let core = Arc::new(BilinearProductCore::new(left, right).map_err(invalid)?);
    let target =
        BilinearOperator::new(target_matrix.columns(), 1, target_matrix).map_err(invalid)?;
    core.bind(&target)
        .map_err(invalid)?
        .map_err(|_| invalid("incidence restriction factorization failed to bind"))
}

#[cfg(test)]
#[path = "incidence/tests.rs"]
mod tests;
