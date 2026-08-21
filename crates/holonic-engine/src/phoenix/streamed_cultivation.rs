//! W3's typed resident tail for the streamed Phoenix circulation.
//!
//! This owner carries no tower loop. It prices the overlay's six resident shapes, authenticates
//! the candidate identity, and returns the W3 receipt assembled by `streamed.rs`.

use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

use crate::embedding_fiber::{AlignedMaterial, ResidentReadout};
use crate::exact_work::ExactWork;
use crate::front_passage::{
    ApparatusPrediction, DeedAdmission, FrontDeedReading, FrontPassage, MaterialAdmission,
    PassageReturn, ResidentMaterial, co_present,
};
use crate::resident_law::FactorizedContract;
use crate::resident_section::ResidentSurface;
use crate::source_occurrence::OccurrenceWitness;
use num_bigint::BigUint;

use super::{Circulated, cultivation_overlay};

pub struct CultivationRequest<'a> {
    pub candidate: &'a cultivation_overlay::RankOneCandidate,
    pub derivation: &'a cultivation_overlay::RankDerivationReceipt,
    pub u: &'a AlignedMaterial,
    pub v: &'a AlignedMaterial,
    pub witness: &'a dyn OccurrenceWitness,
    pub input_bound: u32,
    pub predecessor_bound: u32,
    /// Authenticated band chronology aperture carried by the cultivated product.
    pub band_terms: usize,
}

impl<'a> CultivationRequest<'a> {
    /// Rebase the request onto the bounds returned by an authenticated W2 remount.
    pub fn with_w2_bounds(mut self, base: &Circulated) -> Self {
        self.input_bound = base.final_normed_bound;
        self.predecessor_bound = base.potential_bound;
        self
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CultivationPreAdmission {
    pub candidate_operations: usize,
    pub factor_resident_octets: u64,
    pub overlay_work: ExactWork,
    pub overlay_launches: u64,
    pub overlay_graph_identity: CultivationGraphIdentity,
    pub material_admission: MaterialAdmission,
    /// The factor admission is reconciled against the resident maps actually mounted by W3.
    /// Each tuple is `(population, predicted resident octets, measured resident octets)`.
    pub factor_material_reconciliation: Vec<(String, u64, u64)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CultivationGraphIdentity {
    pub candidate_complex_sha256: String,
    pub derivation_sha256: String,
    pub witness_kind: String,
    pub u_population: String,
    pub v_population: String,
    pub u_address: u64,
    pub v_address: u64,
    pub u_exponent: i32,
    pub v_exponent: i32,
    pub mode: String,
    pub grain: u32,
    pub rows: usize,
    pub input_width: usize,
    pub input_bound: u32,
    pub predecessor_bound: u32,
}

/// Identity of the executable deed that actually crossed the resident stream.  The launch count
/// is only one coordinate; the graph census and exact deed work bind which graph was launched.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct OverlayExecutionIdentity {
    pub graph_nodes: u64,
    pub graph_edges: u64,
    pub captured_launches: u64,
    pub deed_launches: u64,
    pub graph_execs: u64,
    pub deed_work: ExactWork,
    pub identity_sha256: String,
}

/// Returned apparatus testimony, kept separate from prelaunch predictions. Energy and utilization
/// remain unknown until a calibrated external receiver supplies them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExecutionReceipt {
    pub device_name: String,
    pub mode: String,
    pub kernel_sha256: String,
    pub memory_at_mount_free: u64,
    pub memory_at_mount_total: u64,
    pub memory_at_return_free: u64,
    pub memory_at_return_total: u64,
    pub streamed: crate::streamed_standing::StreamedCensus,
    /// Absolute before/after apparatus censuses. Keeping both avoids inventing subtraction laws
    /// for non-additive coordinates such as resident peak.
    pub resident_transfer_before: crate::resident_section::TransferCensus,
    pub resident_transfer_after: crate::resident_section::TransferCensus,
    pub overlay_transfer_before: crate::resident_section::TransferCensus,
    pub overlay_transfer_after: crate::resident_section::TransferCensus,
    pub terminal_synchronizations: u64,
    /// Physical clock telemetry is an exterior apparatus face and is never used for admission.
    pub wall_seconds: String,
    pub loop_wall_seconds: String,
    pub calibration: String,
    pub physical_energy: Option<String>,
    pub physical_utilization: Option<String>,
}

pub struct CultivatedCirculated {
    pub base: Circulated,
    pub base_potential_digest: String,
    pub cultivated_potential: Vec<(i64, i64)>,
    pub overlay_work: ExactWork,
    pub overlay_apparatus: ApparatusPrediction,
    pub total_work: ExactWork,
    pub overlay_launches: u64,
    pub total_deed_launches: u64,
    pub pre_admission: CultivationPreAdmission,
    /// The complete semantic and apparatus coordinate admission of the overlay passage, taken
    /// from the compiled deed rather than reconstructed from the prediction.
    pub overlay_admission: DeedAdmission,
    /// The returned census/front evidence after the one terminal synchronization.
    pub overlay_return: PassageReturn,
    pub overlay_fronts: Vec<FrontDeedReading>,
    pub overlay_kernels_written: bool,
    pub overlay_census_refusals: u64,
    pub factor_material_reconciliation: Vec<(String, u64, u64)>,
    pub overlay_execution: OverlayExecutionIdentity,
    pub execution: ExecutionReceipt,
    pub overlay_graph_identity: CultivationGraphIdentity,
    pub witness_stability_obligation: &'static str,
}

pub(crate) enum CirculationOutput {
    Base(Circulated),
    Cultivated(CultivatedCirculated),
}

pub(crate) fn prepare<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    readout: &'chart ResidentReadout,
    passage: &FrontPassage<'chart>,
    request: &CultivationRequest<'_>,
    token_count: usize,
    grain: crate::resident_section::ResidentGrain,
) -> Result<(ResidentMaterial<'chart>, CultivationPreAdmission), String> {
    if request.candidate.terminal_rows != token_count {
        return Err(format!(
            "W3 candidate terminal rows {} disagree with {} input tokens",
            request.candidate.terminal_rows, token_count
        ));
    }
    let (complex, events) = request
        .candidate
        .complex(Some(request.derivation))
        .map_err(|error| format!("W3 candidate refused before W2 launch: {error}"))?;
    let factor_prediction =
        passage.predict_aligned_material(&crate::front_passage::AlignedMaterialPlan::maps(vec![
            (
                request.candidate.u_population.clone(),
                request.candidate.shape.rows,
                1,
            ),
            (
                request.candidate.v_population.clone(),
                1,
                request.candidate.shape.input_width,
            ),
        ]));
    let factor_admission = passage
        .admit_material(&factor_prediction)
        .map_err(|obstruction| {
            format!("W3 factor material refused before launch: {obstruction:?}")
        })?;
    let factor_resident_octets = factor_admission.prediction.resident_octets;
    let candidate_complex_sha256 = digest_complex(&complex)?;
    let derivation_sha256 = digest_derivation(request.derivation);
    let mut candidate_material = ResidentMaterial::empty();
    cultivation_overlay::mount_factor(
        readout,
        &mut candidate_material,
        request.candidate.u_population.clone(),
        request.u,
        request.candidate.shape.rows,
        1,
    )?;
    cultivation_overlay::mount_factor(
        readout,
        &mut candidate_material,
        request.candidate.v_population.clone(),
        request.v,
        1,
        request.candidate.shape.input_width,
    )?;
    cultivation_overlay::inspect_extents(request.candidate, &candidate_material)?;
    let factor_material_reconciliation = factor_admission.reconcile(&candidate_material);
    if factor_material_reconciliation
        .iter()
        .any(|(_, predicted, measured)| predicted != measured)
    {
        return Err(format!(
            "W3 factor material admission did not reconcile: {factor_material_reconciliation:?}"
        ));
    }
    let (overlay_work, overlay_launches) =
        predict_overlay(surface, request, &candidate_material, &complex, events)?;
    let u_mounted = &candidate_material.populations[&request.candidate.u_population].readout;
    let v_mounted = &candidate_material.populations[&request.candidate.v_population].readout;
    let overlay_graph_identity = CultivationGraphIdentity {
        candidate_complex_sha256,
        derivation_sha256,
        witness_kind: request.witness.witness().to_owned(),
        u_population: request.candidate.u_population.clone(),
        v_population: request.candidate.v_population.clone(),
        u_address: u_mounted.aligned_address(),
        v_address: v_mounted.aligned_address(),
        u_exponent: u_mounted.exponent(),
        v_exponent: v_mounted.exponent(),
        mode: format!("{:?}", surface.mode()),
        grain: grain.0,
        rows: request.candidate.shape.rows,
        input_width: request.candidate.shape.input_width,
        input_bound: request.input_bound,
        predecessor_bound: request.predecessor_bound,
    };
    Ok((
        candidate_material,
        CultivationPreAdmission {
            candidate_operations: complex.operations.len(),
            factor_resident_octets,
            overlay_work,
            overlay_launches,
            overlay_graph_identity,
            material_admission: factor_admission,
            factor_material_reconciliation,
        },
    ))
}

/// Derive the execution identity from the compiled overlay, after admission and before launch.
pub(crate) fn execution_identity<'chart>(
    passage: &cultivation_overlay::OverlayPassage<'chart>,
) -> OverlayExecutionIdentity {
    let (graph, _) = passage.passage.graph();
    let apparatus = &passage.passage.apparatus_prediction;
    let deed_work = passage.passage.deed_prediction.clone();
    let identity_bytes = serde_json::to_vec(&(
        graph.nodes,
        graph.edges,
        apparatus.captured_launches,
        apparatus.deed_launches,
        apparatus.graph_execs,
        &deed_work,
    ))
    .expect("overlay execution identity is serializable");
    OverlayExecutionIdentity {
        graph_nodes: graph.nodes as u64,
        graph_edges: graph.edges as u64,
        captured_launches: apparatus.captured_launches,
        deed_launches: apparatus.deed_launches,
        graph_execs: apparatus.graph_execs,
        deed_work,
        identity_sha256: format!("{:x}", Sha256::digest(identity_bytes)),
    }
}

pub(crate) fn predict_overlay<'chart>(
    surface: &ResidentSurface<'chart>,
    request: &CultivationRequest<'_>,
    material: &ResidentMaterial<'chart>,
    complex: &crate::ported_operation::PortedOperationComplex,
    events: cultivation_overlay::OverlayEvents,
) -> Result<(ExactWork, u64), String> {
    let rows = request.candidate.terminal_rows;
    let output_width = request.candidate.shape.rows;
    let input_width = request.candidate.shape.input_width;
    let h = surface
        .shape_carry(rows, input_width, request.input_bound)
        .map_err(|error| format!("overlay h prediction: {error}"))?;
    let y0 = surface
        .shape_carry(rows, output_width, request.predecessor_bound)
        .map_err(|error| format!("overlay y0 prediction: {error}"))?;
    let withdrawn = surface
        .shape_withdraw_rows(rows, input_width, h.needed, 0, rows.saturating_sub(1))
        .map_err(|error| format!("overlay terminal withdrawal prediction: {error}"))?;
    let v = material
        .populations
        .get(&request.candidate.v_population)
        .ok_or_else(|| "overlay v factor disappeared before prediction".to_owned())?;
    let u = material
        .populations
        .get(&request.candidate.u_population)
        .ok_or_else(|| "overlay u factor disappeared before prediction".to_owned())?;
    let factorized = surface
        .shape_factorized_contract(
            rows,
            input_width,
            withdrawn.needed,
            &u.readout,
            &v.readout,
            1,
        )
        .map_err(|error| format!("overlay factorized prediction: {error}"))?;
    let factorized_output_bound = FactorizedContract {
        u_population: request.candidate.u_population.clone(),
        v_population: request.candidate.v_population.clone(),
        rank: 1,
    }
    .output_word_octaves(request.input_bound, material);
    let re_entry = surface
        .shape_re_entry(
            rows,
            output_width,
            request.predecessor_bound,
            factorized_output_bound,
        )
        .map_err(|error| format!("overlay re-entry prediction: {error}"))?;
    let shapes = BTreeMap::from([
        (events.input, h),
        (events.predecessor, y0),
        (events.terminal, withdrawn),
        (events.factorized, factorized),
        (events.re_entry, re_entry),
    ]);
    let fronts = complex
        .fronts()
        .map_err(|error| format!("overlay fronts for work prediction: {error}"))?;
    let mut work = ExactWork::nothing();
    let mut launches = 0u64;
    for front in &fronts {
        let mut front_work = ExactWork::nothing();
        for occurrence in &front.occurrences {
            let shape = shapes.get(occurrence).ok_or_else(|| {
                format!(
                    "overlay work prediction has no shape for event {:?}",
                    occurrence
                )
            })?;
            front_work = co_present(&front_work, &shape.predicted);
            launches += u64::from(shape.launches);
        }
        work = work.then(&front_work);
    }
    work.dependency_span = BigUint::from(fronts.len() as u64);
    Ok((work, launches))
}

fn frame_digest(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

pub(crate) fn digest_complex(
    complex: &crate::ported_operation::PortedOperationComplex,
) -> Result<String, String> {
    let bytes = serde_json::to_vec(complex)
        .map_err(|error| format!("overlay complex identity: {error}"))?;
    let mut hasher = Sha256::new();
    frame_digest(&mut hasher, b"holonic-engine.phoenix.w3-overlay-complex.v1");
    frame_digest(&mut hasher, &bytes);
    Ok(format!("{:x}", hasher.finalize()))
}

pub(crate) fn digest_derivation(receipt: &cultivation_overlay::RankDerivationReceipt) -> String {
    cultivation_overlay::canonical_rank_derivation_digest(receipt)
}

pub(crate) fn digest_face(
    face: &[(i64, i64)],
    grain: crate::resident_section::ResidentGrain,
) -> String {
    let mut hasher = Sha256::new();
    hasher.update(b"holonic-engine.phoenix.w2-potential-face.v1");
    hasher.update(grain.0.to_le_bytes());
    hasher.update((face.len() as u64).to_le_bytes());
    for (lower, upper) in face {
        hasher.update(lower.to_le_bytes());
        hasher.update(upper.to_le_bytes());
    }
    format!("{:x}", hasher.finalize())
}
