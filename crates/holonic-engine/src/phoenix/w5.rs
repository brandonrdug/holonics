//! The pure W5 Phoenix grade.
//!
//! W5 is a receiver over returned deeds, not a JSON admission mechanism.  Inputs are serializable
//! for artifact recording, but deliberately are not `Deserialize`: an arbitrary JSON summary may
//! not become trusted execution testimony.  The resident deed owners construct these values and
//! bind every return, work vector, and apparatus witness to its canonical receiver digest.
#[cfg(test)]
mod tests;
use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;
use serde::Serialize;
use serde_json;
use sha2::{Digest, Sha256};

use crate::exact_work::ExactWork;

const SCHEMA: &str = "holonic-engine.phoenix.w5-four-body-grade.v2";
const EVIDENCE_SCHEMA: &str = "holonic-engine.phoenix.w5-evidence.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum Body {
    ForeignSource,
    W2Predecessor,
    W3Cultivated,
    ArmN,
}

impl Body {
    pub const ALL: [Self; 4] = [
        Self::ForeignSource,
        Self::W2Predecessor,
        Self::W3Cultivated,
        Self::ArmN,
    ];

    pub const fn label(self) -> &'static str {
        match self {
            Self::ForeignSource => "foreign-source",
            Self::W2Predecessor => "w2-predecessor",
            Self::W3Cultivated => "w3-cultivated",
            Self::ArmN => "arm-n",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum ExecutionKind {
    ResidentGpu,
    NativeRuntime,
    NoMorphologyControl,
    RestMount,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Face {
    pub name: String,
    pub material_digest: String,
    /// Exact receiver intervals, retained in their declared order.
    pub intervals: Vec<(i64, i64)>,
}

impl Face {
    pub fn digest(&self) -> String {
        digest(&canonical_intervals(&self.intervals))
    }
}

/// The returned face family. Its digest is recomputed over ordered names and bytes; the supplied
/// digest is testimony and never trusted without that recomputation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReceiverReturn {
    pub faces: Vec<Face>,
    pub digest: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SourceAccessWitness {
    pub audit_identity: String,
    pub forbidden: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExecutionWitness {
    pub kind: ExecutionKind,
    pub deed_identity: String,
    pub resident_owner: String,
    pub returned_artifact_digest: String,
    pub source_access: SourceAccessWitness,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum Calibrated<T> {
    Known(T),
    Unknown { reason: String },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ApparatusUtility {
    pub device_name: String,
    pub mode: String,
    pub kernel_identity: String,
    pub launches: Calibrated<BigUint>,
    pub synchronizations: Calibrated<BigUint>,
    pub transfer_octets: Calibrated<BigUint>,
    pub active_warps: Calibrated<BigUint>,
    pub energy: Calibrated<BigUint>,
    pub calibration: BTreeMap<String, String>,
    /// Canonical UTF-8 JSON bytes of the owner-produced apparatus census/testimony.
    pub apparatus_evidence: String,
    pub apparatus_digest: String,
    pub returned_artifact_digest: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct WorkReceipt {
    pub work: ExactWork,
    pub admission_digest: String,
    /// Canonical UTF-8 JSON bytes of the exact admission testimony whose digest is carried above.
    pub admission_evidence: String,
    pub returned_artifact_digest: String,
    pub owner_receipt_digest: String,
}

/// One actual deed bound three ways to the same receiver return. Semantic work and calibrated
/// apparatus testimony are not body-level decorations: every replay, sibling, held-out return,
/// and ablation owes them at the occurrence which produced it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct BoundDeed {
    pub body: Body,
    pub execution: ExecutionWitness,
    pub work: WorkReceipt,
    pub apparatus: ApparatusUtility,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct BodyObservation {
    pub body: Body,
    pub body_digest: String,
    pub base_material_digest: String,
    /// The deed/graph closure identity. This is distinct from the source closure used by
    /// recombination absence testimony.
    pub deed_closure_digest: String,
    /// The authenticated source/W1 closure identity, when this body is bound to one.
    pub source_closure_identity: String,
    pub codebook_digest: String,
    pub codebook_extent: u32,
    pub receiver_family_digest: String,
    pub base_return_digest: String,
    pub faces: Vec<Face>,
    pub return_digest: String,
    pub deed: BoundDeed,
    pub base_replay_return_digest: String,
    pub base_replay_deed: BoundDeed,
    pub interventions: Vec<MatchedIntervention>,
    /// W3's authenticated morphology cause. Empty for the other bodies.
    pub cultivation_delta_id: String,
    /// ARM N must return a prior deed as well as its current deed; a rest mount alone is refused.
    pub prior_return: Option<ReceiverReturn>,
    pub prior_deed: Option<BoundDeed>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct InterventionManifestRow {
    pub id: String,
    pub site: String,
    pub law_digest: String,
    /// Number of ordered receiver faces which must remain identical before the intervention site.
    pub pre_intervention_prefix: usize,
    pub requires_separation: bool,
    pub order_face_control: bool,
    pub exact_control_span: Option<ControlSpan>,
    pub unseparated_control_span: Option<ControlSpan>,
}

/// A receiver-local control inside one returned face. This keeps “position zero at layer one”
/// distinct from “the first N faces”, which are different causal apertures.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct ControlSpan {
    pub face_index: usize,
    pub start: usize,
    pub extent: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MatchedIntervention {
    pub body: Body,
    pub row_id: String,
    pub site: String,
    pub law_digest: String,
    pub pre_intervention_prefix: usize,
    pub before: ReceiverReturn,
    pub after: ReceiverReturn,
    pub deed: BoundDeed,
    pub intervention_occurrence_digest: String,
    pub order_face_before_digest: String,
    pub order_face_after_digest: String,
}

impl MatchedIntervention {
    pub fn shortest_separator(&self) -> Option<ShortestSeparator> {
        shortest_separator(&self.before.faces, &self.after.faces)
    }

    pub fn prefix_holds(&self) -> bool {
        self.before
            .faces
            .iter()
            .zip(&self.after.faces)
            .take(self.pre_intervention_prefix)
            .all(|(before, after)| before.name == after.name && before.intervals == after.intervals)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum FaceRelation {
    BitIdentical,
    OverlappingDifferent,
    Separated,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct ShortestSeparator {
    pub face_index: usize,
    pub interval_index: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum HeldOutKind {
    StructuralChanged,
    SubjectDisjointUnchanged,
    MatchedFoil,
    NoOp,
    CodecVariant,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HeldOutBodyReturn {
    pub body: Body,
    pub input_lineage_digest: String,
    pub returned: ReceiverReturn,
    pub deed: BoundDeed,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HeldOutCase {
    pub kind: HeldOutKind,
    pub lineage_digest: String,
    pub input_baseline_digest: String,
    pub returns: Vec<HeldOutBodyReturn>,
    pub codec_paths: Vec<CodecVariantPath>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CodecVariantPath {
    pub path_identity: String,
    pub token_word_digest: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CondensationRemainder {
    pub prior_artifact_digest: String,
    pub prior_receiver_family: Vec<String>,
    pub enlarged_receiver_family: Vec<String>,
    pub prior_collapsed_population: BigUint,
    pub enlarged_collapsed_population: BigUint,
    pub retained_separators: Vec<Vec<u8>>,
    pub open_fibres: Vec<String>,
    pub refinement_digest: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SourceClosureAbsenceWitness {
    pub source_closure_identity: String,
    pub overlay_topology_absent: bool,
    pub absent_overlay_operation_ids: Vec<String>,
    pub absent_factor_populations: Vec<String>,
    pub held_out_difference_digest: String,
    pub witness_digest: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CauseAblation {
    pub cause_id: String,
    pub intervention_row_id: String,
    pub input_lineage_digest: String,
    pub control_kind: AblationControlKind,
    pub before: ReceiverReturn,
    pub ablated: ReceiverReturn,
    pub restored: ReceiverReturn,
    pub deeds: Vec<BoundDeed>,
    pub control_input_lineage_digest: String,
    pub control_cause_id: String,
    pub control_intervention_row_id: String,
    pub control_before: ReceiverReturn,
    pub control_after: ReceiverReturn,
    pub control_deeds: Vec<BoundDeed>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum AblationControlKind {
    CausalPrefix,
    SubjectDisjoint,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeRecombinationReceipt {
    pub held_out_lineage_digest: String,
    pub lifted_cause_ids: Vec<String>,
    pub cultivation_delta_id: String,
    pub source_closure_identity: String,
    pub source_closure_absence: SourceClosureAbsenceWitness,
    pub baseline: ReceiverReturn,
    pub recombined: ReceiverReturn,
    pub recombined_deed: BoundDeed,
    pub cause_ablations: Vec<CauseAblation>,
    pub cultivation_delta: CauseAblation,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct FourBodyInput {
    pub correspondence: SourceNativeCorrespondence,
    pub component_ledger: Vec<ComponentEvidence>,
    pub intervention_manifest: Vec<InterventionManifestRow>,
    pub condensation: CondensationRemainder,
    pub held_out: Vec<HeldOutCase>,
    pub recombination: NativeRecombinationReceipt,
    pub bodies: Vec<BodyObservation>,
}

/// The compact binding carried by a grade for its complete returned-deed evidence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EvidenceBinding {
    pub schema: &'static str,
    pub role: &'static str,
    pub input_digest: String,
    pub input_extent: u64,
    pub sidecar_digest: String,
    pub sidecar_extent: u64,
}

/// The complete validated W5 input as a content-addressed proof object.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EvidenceSidecar {
    pub schema: &'static str,
    pub role: &'static str,
    pub input_digest: String,
    pub input_extent: u64,
    pub input: FourBodyInput,
    #[serde(skip)]
    canonical_bytes: Vec<u8>,
}

impl EvidenceSidecar {
    fn from_input(input: FourBodyInput) -> Result<Self, GradeRefusal> {
        let (input_digest, input_extent) = {
            let bytes = Self::canonical_input_bytes(&input)?;
            (digest(&bytes), bytes.len() as u64)
        };
        let mut sidecar = Self {
            schema: EVIDENCE_SCHEMA,
            role: "evidence.json",
            input_digest,
            input_extent,
            input,
            canonical_bytes: Vec::new(),
        };
        sidecar.canonical_bytes = serde_json::to_vec(&sidecar).map_err(|error| {
            GradeRefusal::Invalid(format!("W5 evidence sidecar serialization: {error}"))
        })?;
        Ok(sidecar)
    }

    fn canonical_input_bytes(input: &FourBodyInput) -> Result<Vec<u8>, GradeRefusal> {
        serde_json::to_vec(input)
            .map_err(|error| GradeRefusal::Invalid(format!("W5 evidence serialization: {error}")))
    }

    /// Consume the sidecar and return its canonical bytes without cloning the large buffer.
    pub fn into_bytes(self) -> Result<Vec<u8>, GradeRefusal> {
        if self.canonical_bytes.is_empty() {
            serde_json::to_vec(&self).map_err(|error| {
                GradeRefusal::Invalid(format!("W5 evidence sidecar serialization: {error}"))
            })
        } else {
            Ok(self.canonical_bytes)
        }
    }

    pub fn binding(&self) -> Result<EvidenceBinding, GradeRefusal> {
        let (sidecar_digest, sidecar_extent) = if self.canonical_bytes.is_empty() {
            let bytes = serde_json::to_vec(self).map_err(|error| {
                GradeRefusal::Invalid(format!("W5 evidence sidecar serialization: {error}"))
            })?;
            (digest(&bytes), bytes.len() as u64)
        } else {
            (
                digest(&self.canonical_bytes),
                self.canonical_bytes.len() as u64,
            )
        };
        Ok(EvidenceBinding {
            schema: self.schema,
            role: self.role,
            input_digest: self.input_digest.clone(),
            input_extent: self.input_extent,
            sidecar_digest,
            sidecar_extent,
        })
    }

    /// Recompute the content binding from every serialized input field.
    pub fn verify(&self) -> Result<(), GradeRefusal> {
        if self.schema != EVIDENCE_SCHEMA || self.role != "evidence.json" {
            return Err(GradeRefusal::Invalid(
                "W5 evidence sidecar schema differs".to_owned(),
            ));
        }
        let bytes = Self::canonical_input_bytes(&self.input)?;
        if self.input_extent != bytes.len() as u64 || self.input_digest != digest(&bytes) {
            return Err(GradeRefusal::Invalid(
                "W5 evidence sidecar content binding drifted".to_owned(),
            ));
        }
        Ok(())
    }

    pub fn verify_against(&self, binding: &EvidenceBinding) -> Result<(), GradeRefusal> {
        self.verify()?;
        if self.binding()? != *binding {
            return Err(GradeRefusal::Invalid(
                "W5 evidence sidecar does not match the grade binding".to_owned(),
            ));
        }
        Ok(())
    }
}

pub const COMPONENT_ROW_IDS: [&str; 8] = [
    "w1-source-manifest",
    "w1-potential-active-atlas-rest",
    "station-d-source-dissection",
    "station-d-nontext-control",
    "w2-correspondence-condensation",
    "w3-cultivation-rank-adjoint-rest",
    "w4-application-fresh-inference",
    "p0-arm-n",
];

pub const COMPONENT_SCHEMAS: [&str; 8] = [
    "holonic-engine.phoenix.w1-receipt.v1",
    "holonic-engine.operation-correspondence.v1",
    "holonic-engine.phoenix.source-dissection.form.v1",
    "holonic-engine.phoenix.vision-projection.tsv.v1",
    "holonic-engine.phoenix.w2-structural-condensation.v1",
    "holonic-engine.phoenix.w3-receipt.v1",
    "holonic-engine.phoenix.w4-fresh-process.v1",
    "holonic-engine.phoenix.w5-arm-n-return.v1",
];

pub const INTERVENTION_ROW_IDS: [&str; 16] = [
    "embedding-columns",
    "ple",
    "pre-rebase-scale",
    "post-rebase-scale",
    "identity-chronology",
    "reversed-chronology",
    "receiver-permutation",
    "receiver-scale",
    "own-kv",
    "stored-kv",
    "shared-kv",
    "carried-permutation",
    "residual-reentry",
    "gate-span",
    "one-key-full-chronology",
    "final-span",
];

const INTERVENTION_SITES: [&str; 16] = [
    "EveryLayer",
    "Layer(1)",
    "Layer(1)",
    "Layer(1)",
    "Layer(1)",
    "Layer(1)",
    "Layer(1)",
    "Layer(1)",
    "Layer(1)",
    "Layer(22)",
    "Layer(24)",
    "Layer(1)",
    "Layer(1)",
    "Layer(1)",
    "Layer(5)",
    "Final",
];

const INTERVENTION_PREFIX_FACES: [usize; 16] =
    [0, 3, 3, 3, 3, 3, 3, 3, 3, 66, 72, 3, 3, 3, 15, 126];

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ComponentEvidence {
    pub row_id: String,
    pub artifact_identity: String,
    pub extent: u64,
    pub schema: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SourceNativeCorrespondence {
    pub source_codebook_digest: String,
    pub native_codebook_digest: String,
    pub source_extent: u32,
    pub native_extent: u32,
    pub source_to_native: Vec<(u32, u32)>,
    pub unresolved_source: Vec<u32>,
    pub receiver_names: Vec<String>,
    pub receiver_family_digest: String,
    pub relation_digest: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GradeItem {
    pub name: String,
    pub passed: bool,
    pub evidence: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HeldOutChange {
    pub kind: HeldOutKind,
    pub changed: Vec<(Body, bool)>,
    pub cross_chart_changed: bool,
    pub cultivated_change: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CauseAblationResult {
    pub cause_id: String,
    pub changed: bool,
    pub restored: bool,
    pub control_held: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct FourBodyGrade {
    pub schema: &'static str,
    pub passed: bool,
    pub items: Vec<GradeItem>,
    pub correspondence: SourceNativeCorrespondence,
    pub component_ledger: Vec<ComponentEvidence>,
    pub condensation: CondensationRemainder,
    pub intervention_results: Vec<InterventionResult>,
    pub held_out_changes: Vec<HeldOutChange>,
    pub ablation_results: Vec<CauseAblationResult>,
    pub exact_work: Vec<(Body, WorkReceipt)>,
    pub apparatus: Vec<(Body, ApparatusUtility)>,
    pub evidence: EvidenceBinding,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct InterventionResult {
    pub body: Body,
    pub row_id: String,
    pub relations: Vec<FaceRelation>,
    pub shortest_separator: Option<ShortestSeparator>,
    pub prefix_holds: bool,
    pub order_face_unchanged: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GradeRefusal {
    Invalid(String),
    MissingBody(Body),
    DuplicateBody(Body),
    FailedItem(String),
}

impl core::fmt::Display for GradeRefusal {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Invalid(why) => write!(f, "W5 invalid return: {why}"),
            Self::MissingBody(body) => write!(f, "missing {} observation", body.label()),
            Self::DuplicateBody(body) => write!(f, "duplicate {} observation", body.label()),
            Self::FailedItem(item) => write!(f, "W5 item failed: {item}"),
        }
    }
}

/// Validate and return the compact grade while retaining a content binding for the complete
/// evidence object. Call grade_with_evidence when the sidecar bytes must be persisted.
pub fn grade(input: FourBodyInput) -> Result<FourBodyGrade, GradeRefusal> {
    let (grade, _) = grade_with_evidence(input)?;
    Ok(grade)
}

/// Validate a W5 input and return both the compact grade and the complete typed evidence sidecar.
///
/// The grade carries the sidecar's digest and extent. The caller must persist
/// EvidenceSidecar::into_bytes beside the grade if the proof object is to survive this process.
pub fn grade_with_evidence(
    input: FourBodyInput,
) -> Result<(FourBodyGrade, EvidenceSidecar), GradeRefusal> {
    let evidence = EvidenceSidecar::from_input(input)?;
    let binding = evidence.binding()?;
    let grade = grade_validated(&evidence.input, binding)?;
    Ok((grade, evidence))
}

/// Validate a W5 input and return the compact grade together with the exact sidecar bytes to
/// persist as the sibling role named by its evidence binding.
pub fn grade_with_evidence_bytes(
    input: FourBodyInput,
) -> Result<(FourBodyGrade, Vec<u8>), GradeRefusal> {
    let (grade, evidence) = grade_with_evidence(input)?;
    let bytes = evidence.into_bytes()?;
    if grade.evidence.sidecar_digest != digest(&bytes)
        || grade.evidence.sidecar_extent != bytes.len() as u64
    {
        return Err(GradeRefusal::Invalid(
            "W5 grade/sidecar binding drifted before return".to_owned(),
        ));
    }
    Ok((grade, bytes))
}

fn grade_validated(
    input: &FourBodyInput,
    evidence: EvidenceBinding,
) -> Result<FourBodyGrade, GradeRefusal> {
    validate_correspondence(&input.correspondence)?;
    validate_component_ledger(&input.component_ledger)?;
    validate_manifest(&input.intervention_manifest)?;
    validate_condensation(&input.condensation)?;
    validate_body_set(&input.bodies)?;
    let get = |body: Body| {
        input
            .bodies
            .iter()
            .find(|item| item.body == body)
            .expect("body set checked")
    };
    for body in &input.bodies {
        validate_body(body)?;
    }
    let foreign = get(Body::ForeignSource);
    let predecessor = get(Body::W2Predecessor);
    let cultivated = get(Body::W3Cultivated);
    let arm = get(Body::ArmN);
    validate_first_three_binding(&input.correspondence, foreign, predecessor, cultivated)?;
    if foreign.return_digest != predecessor.return_digest {
        return Err(GradeRefusal::Invalid(
            "foreign/W2 base cross-chart return differs".to_owned(),
        ));
    }
    validate_base_replays(foreign, predecessor, cultivated)?;
    let mut intervention_results = Vec::new();
    intervention_results.extend(validate_interventions(
        &input.intervention_manifest,
        foreign,
    )?);
    if foreign
        .interventions
        .iter()
        .zip(&predecessor.interventions)
        .any(|(source, native)| source.after.digest != native.after.digest)
    {
        return Err(GradeRefusal::Invalid(
            "foreign/W2 intervention cross-chart return differs".to_owned(),
        ));
    }
    intervention_results.extend(validate_interventions(
        &input.intervention_manifest,
        predecessor,
    )?);
    intervention_results.extend(validate_interventions(
        &input.intervention_manifest,
        cultivated,
    )?);
    let held_out_changes = validate_held_out(&input.held_out, foreign, predecessor, cultivated)?;
    let ablation_results = validate_recombination(
        &input.recombination,
        &input.held_out,
        foreign,
        predecessor,
        cultivated,
    )?;
    validate_arm_n(arm)?;

    let mut items = Vec::new();
    item(
        &mut items,
        "distinct authenticated bodies",
        distinct_body_digests(&input.bodies),
    )?;
    item(&mut items, "source/native correspondence", true)?;
    item(&mut items, "component evidence ledger", true)?;
    item(&mut items, "complete matched intervention panel", true)?;
    item(&mut items, "held-out continuations", true)?;
    item(&mut items, "monotonic condensation remainder", true)?;
    item(&mut items, "native recombination and cause ablations", true)?;
    item(
        &mut items,
        "exact semantic work",
        input
            .bodies
            .iter()
            .all(|body| work_bound(&body.deed.work, &body.return_digest)),
    )?;
    item(
        &mut items,
        "calibrated apparatus utility",
        input
            .bodies
            .iter()
            .all(|body| apparatus_bound(&body.deed.apparatus, &body.return_digest)),
    )?;
    Ok(FourBodyGrade {
        schema: SCHEMA,
        passed: true,
        items,
        correspondence: input.correspondence.clone(),
        component_ledger: input.component_ledger.clone(),
        condensation: input.condensation.clone(),
        intervention_results,
        held_out_changes,
        ablation_results,
        exact_work: input
            .bodies
            .iter()
            .map(|body| (body.body, body.deed.work.clone()))
            .collect(),
        apparatus: input
            .bodies
            .iter()
            .map(|body| (body.body, body.deed.apparatus.clone()))
            .collect(),
        evidence,
    })
}

/// Validate one returned body at its own aperture before an expensive four-body panel begins.
/// This exposes no partial Phoenix grade; it only applies the same canonical deed/work/apparatus
/// and replay checks used by [`grade`].
pub fn validate_body_observation(body: &BodyObservation) -> Result<(), GradeRefusal> {
    validate_body(body)
}

/// Validate the common foreign/W2/W3 base, replay, correspondence, and intervention family before
/// later held-out and recombination deeds are attempted. A pass is still not a Phoenix grade.
pub fn validate_lifted_panel(
    correspondence: &SourceNativeCorrespondence,
    manifest: &[InterventionManifestRow],
    foreign: &BodyObservation,
    predecessor: &BodyObservation,
    cultivated: &BodyObservation,
) -> Result<(), GradeRefusal> {
    validate_correspondence(correspondence)?;
    validate_manifest(manifest)?;
    for body in [foreign, predecessor, cultivated] {
        validate_body(body)?;
    }
    validate_first_three_binding(correspondence, foreign, predecessor, cultivated)?;
    if foreign.return_digest != predecessor.return_digest {
        return Err(GradeRefusal::Invalid(
            "foreign/W2 base cross-chart return differs".to_owned(),
        ));
    }
    validate_base_replays(foreign, predecessor, cultivated)?;
    validate_interventions(manifest, foreign)?;
    validate_interventions(manifest, predecessor)?;
    validate_interventions(manifest, cultivated)?;
    if foreign
        .interventions
        .iter()
        .zip(&predecessor.interventions)
        .any(|(source, native)| source.after.digest != native.after.digest)
    {
        return Err(GradeRefusal::Invalid(
            "foreign/W2 intervention cross-chart return differs".to_owned(),
        ));
    }
    Ok(())
}

/// Validate the same-material held-out family after it returns and before recombination/ablation.
pub fn validate_held_out_panel(
    cases: &[HeldOutCase],
    foreign: &BodyObservation,
    predecessor: &BodyObservation,
    cultivated: &BodyObservation,
) -> Result<(), GradeRefusal> {
    validate_held_out(cases, foreign, predecessor, cultivated).map(|_| ())
}

fn item(items: &mut Vec<GradeItem>, name: &str, passed: bool) -> Result<(), GradeRefusal> {
    items.push(GradeItem {
        name: name.to_owned(),
        passed,
        evidence: if passed {
            "returned and bound"
        } else {
            "failed"
        }
        .to_owned(),
    });
    if passed {
        Ok(())
    } else {
        Err(GradeRefusal::FailedItem(name.to_owned()))
    }
}

fn validate_body_set(bodies: &[BodyObservation]) -> Result<(), GradeRefusal> {
    let mut seen = BTreeSet::new();
    for body in bodies {
        if !seen.insert(body.body) {
            return Err(GradeRefusal::DuplicateBody(body.body));
        }
    }
    for body in Body::ALL {
        if !seen.contains(&body) {
            return Err(GradeRefusal::MissingBody(body));
        }
    }
    Ok(())
}

fn validate_body(body: &BodyObservation) -> Result<(), GradeRefusal> {
    let return_digest = canonical_return_digest(&body.faces)?;
    if !is_digest(&body.body_digest)
        || !is_digest(&body.base_material_digest)
        || !is_digest(&body.deed_closure_digest)
        || !is_digest(&body.source_closure_identity)
        || body.codebook_digest.is_empty()
        || body.codebook_extent == 0
        || body.receiver_family_digest.is_empty()
        || body.base_return_digest.is_empty()
        || body.return_digest != return_digest
    {
        return Err(GradeRefusal::Invalid(format!(
            "{} return or identity is not canonical",
            body.body.label()
        )));
    }
    if body
        .faces
        .iter()
        .any(|face| face.material_digest != body.base_material_digest)
    {
        return Err(GradeRefusal::Invalid(format!(
            "{} base receiver carries another material lineage",
            body.body.label()
        )));
    }
    validate_bound_deed(&body.deed, &return_digest, body.body)?;
    if body.base_return_digest != return_digest {
        return Err(GradeRefusal::Invalid(format!(
            "{} base faces and return digest differ",
            body.body.label()
        )));
    }
    if body.base_replay_return_digest.is_empty()
        || body.base_replay_deed.execution.returned_artifact_digest
            != body.base_replay_return_digest
    {
        return Err(GradeRefusal::Invalid(format!(
            "{} base replay is not bound",
            body.body.label()
        )));
    }
    validate_bound_deed(
        &body.base_replay_deed,
        &body.base_replay_return_digest,
        body.body,
    )?;
    if body.base_replay_deed.execution.deed_identity == body.deed.execution.deed_identity {
        return Err(GradeRefusal::Invalid(format!(
            "{} base replay is not independent",
            body.body.label()
        )));
    }
    if body.body == Body::ArmN {
        validate_arm_n(body)?;
    } else if body.prior_return.is_some() || body.prior_deed.is_some() {
        return Err(GradeRefusal::Invalid(format!(
            "{} carries an ARM N prior deed",
            body.body.label()
        )));
    }
    Ok(())
}

fn validate_base_replays(
    foreign: &BodyObservation,
    predecessor: &BodyObservation,
    cultivated: &BodyObservation,
) -> Result<(), GradeRefusal> {
    for body in [foreign, predecessor, cultivated] {
        if body.base_replay_return_digest != body.base_return_digest {
            return Err(GradeRefusal::Invalid(format!(
                "{} base replay differs from base",
                body.body.label()
            )));
        }
    }
    Ok(())
}

fn validate_component_ledger(ledger: &[ComponentEvidence]) -> Result<(), GradeRefusal> {
    if ledger.len() != COMPONENT_ROW_IDS.len() {
        return Err(GradeRefusal::Invalid(
            "component evidence ledger is incomplete".to_owned(),
        ));
    }
    let expected: BTreeSet<&str> = COMPONENT_ROW_IDS.into_iter().collect();
    let mut actual = BTreeSet::new();
    for row in ledger {
        if !is_digest(&row.artifact_identity)
            || row.extent == 0
            || row.schema.is_empty()
            || !actual.insert(row.row_id.as_str())
        {
            return Err(GradeRefusal::Invalid(
                "component evidence ledger has empty or duplicate rows".to_owned(),
            ));
        }
    }
    if actual != expected {
        return Err(GradeRefusal::Invalid(
            "component evidence ledger has unexpected rows".to_owned(),
        ));
    }
    for (row_id, schema) in COMPONENT_ROW_IDS.into_iter().zip(COMPONENT_SCHEMAS) {
        let row = ledger
            .iter()
            .find(|row| row.row_id == row_id)
            .expect("component row set was checked");
        if row.schema != schema {
            return Err(GradeRefusal::Invalid(format!(
                "component {row_id} schema differs"
            )));
        }
    }
    Ok(())
}

fn is_digest(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn validate_execution(
    execution: &ExecutionWitness,
    return_digest: &str,
    body: Body,
    allow_no_morphology: bool,
) -> Result<(), GradeRefusal> {
    if !is_digest(&execution.deed_identity)
        || execution.resident_owner.is_empty()
        || execution.returned_artifact_digest != return_digest
        || !is_digest(&execution.source_access.audit_identity)
        || (body != Body::ForeignSource && !execution.source_access.forbidden.is_empty())
    {
        return Err(GradeRefusal::Invalid(format!(
            "{} execution witness is not bound",
            body.label()
        )));
    }
    if execution.kind == ExecutionKind::RestMount {
        return Err(GradeRefusal::Invalid(
            "a mount-only occurrence is not an actual deed".to_owned(),
        ));
    }
    let kind_ok = match body {
        Body::ForeignSource | Body::W2Predecessor => execution.kind == ExecutionKind::ResidentGpu,
        Body::W3Cultivated => {
            execution.kind == ExecutionKind::NativeRuntime
                || (allow_no_morphology && execution.kind == ExecutionKind::NoMorphologyControl)
        }
        Body::ArmN => execution.kind == ExecutionKind::NativeRuntime,
    };
    if !kind_ok {
        return Err(GradeRefusal::Invalid(format!(
            "{} execution kind is not admitted for this deed context",
            body.label()
        )));
    }
    Ok(())
}

fn validate_bound_deed(
    deed: &BoundDeed,
    return_digest: &str,
    body: Body,
) -> Result<(), GradeRefusal> {
    if deed.body != body {
        return Err(GradeRefusal::Invalid(format!(
            "{} deed body identity differs",
            body.label()
        )));
    }
    validate_bound_deed_with_allowance(deed, return_digest, body, false)
}

fn validate_bound_deed_with_allowance(
    deed: &BoundDeed,
    return_digest: &str,
    body: Body,
    allow_no_morphology: bool,
) -> Result<(), GradeRefusal> {
    if deed.body != body {
        return Err(GradeRefusal::Invalid(format!(
            "{} deed body identity differs",
            body.label()
        )));
    }
    if !work_bound(&deed.work, return_digest) {
        return Err(GradeRefusal::Invalid(format!(
            "{} deed exact work is unbound",
            body.label()
        )));
    }
    if !apparatus_bound(&deed.apparatus, return_digest) {
        return Err(GradeRefusal::Invalid(format!(
            "{} deed apparatus testimony is unbound",
            body.label()
        )));
    }
    validate_execution(&deed.execution, return_digest, body, allow_no_morphology)?;
    Ok(())
}

fn validate_arm_n(body: &BodyObservation) -> Result<(), GradeRefusal> {
    if body.body != Body::ArmN {
        return Ok(());
    }
    let prior = body
        .prior_return
        .as_ref()
        .ok_or_else(|| GradeRefusal::Invalid("ARM N prior deed is absent".to_owned()))?;
    let prior_digest = canonical_return_digest(&prior.faces)?;
    let prior_deed = body
        .prior_deed
        .as_ref()
        .ok_or_else(|| GradeRefusal::Invalid("ARM N prior execution is absent".to_owned()))?;
    validate_bound_deed(prior_deed, &prior_digest, Body::ArmN)?;
    if prior_deed.execution.kind == ExecutionKind::RestMount
        || prior_deed.execution.deed_identity == body.deed.execution.deed_identity
    {
        return Err(GradeRefusal::Invalid(
            "ARM N prior/current deeds are not distinct actual deeds".to_owned(),
        ));
    }
    Ok(())
}

fn validate_first_three_binding(
    correspondence: &SourceNativeCorrespondence,
    foreign: &BodyObservation,
    predecessor: &BodyObservation,
    cultivated: &BodyObservation,
) -> Result<(), GradeRefusal> {
    if foreign.codebook_digest != correspondence.source_codebook_digest
        || predecessor.codebook_digest != correspondence.native_codebook_digest
        || cultivated.codebook_digest != correspondence.native_codebook_digest
        || predecessor.codebook_extent != correspondence.native_extent
        || cultivated.codebook_extent != correspondence.native_extent
        || foreign.codebook_extent != correspondence.source_extent
    {
        return Err(GradeRefusal::Invalid(
            "foreign/W2/W3 codebook correspondence is not shared".to_owned(),
        ));
    }
    if foreign.base_material_digest != predecessor.base_material_digest
        || foreign.base_material_digest != cultivated.base_material_digest
        || foreign.source_closure_identity != predecessor.source_closure_identity
        || foreign.source_closure_identity != cultivated.source_closure_identity
    {
        return Err(GradeRefusal::Invalid(
            "foreign/W2/W3 material or source closure differs".to_owned(),
        ));
    }
    for body in [foreign, predecessor, cultivated] {
        if body.receiver_family_digest != correspondence.receiver_family_digest
            || body.receiver_family_digest
                != receiver_family_digest(&ordered_face_names(&body.faces))
            || ordered_face_names(&body.faces) != correspondence.receiver_names
        {
            return Err(GradeRefusal::Invalid(format!(
                "{} receiver family differs",
                body.body.label()
            )));
        }
    }
    Ok(())
}

fn validate_correspondence(value: &SourceNativeCorrespondence) -> Result<(), GradeRefusal> {
    if value.source_codebook_digest.is_empty()
        || value.native_codebook_digest.is_empty()
        || value.source_extent == 0
        || value.native_extent == 0
        || value.receiver_names.is_empty()
        || value.receiver_family_digest.is_empty()
    {
        return Err(GradeRefusal::Invalid(
            "source/native correspondence is incomplete".to_owned(),
        ));
    }
    validate_names(&value.receiver_names)?;
    if value.receiver_family_digest != receiver_family_digest(&value.receiver_names) {
        return Err(GradeRefusal::Invalid(
            "receiver family digest drifted".to_owned(),
        ));
    }
    let mut sources = BTreeSet::new();
    let mut natives = BTreeSet::new();
    for (source, native) in &value.source_to_native {
        if *source >= value.source_extent
            || *native >= value.native_extent
            || !sources.insert(*source)
            || !natives.insert(*native)
            || value.unresolved_source.contains(source)
        {
            return Err(GradeRefusal::Invalid(
                "source/native IDs are not a represented bijection".to_owned(),
            ));
        }
    }
    let unresolved: BTreeSet<u32> = value.unresolved_source.iter().copied().collect();
    if unresolved.len() != value.unresolved_source.len()
        || unresolved.iter().any(|id| *id >= value.source_extent)
        || sources.len() + unresolved.len() != value.source_extent as usize
    {
        return Err(GradeRefusal::Invalid(
            "source partition is incomplete or overlapping".to_owned(),
        ));
    }
    if value
        .source_to_native
        .windows(2)
        .any(|pair| pair[0].0 >= pair[1].0)
        || value
            .unresolved_source
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
    {
        return Err(GradeRefusal::Invalid(
            "source correspondence is not ordered".to_owned(),
        ));
    }
    let expected = digest(
        &serde_json::to_vec(&(
            value.source_codebook_digest.clone(),
            value.native_codebook_digest.clone(),
            value.source_extent,
            value.native_extent,
            value.source_to_native.clone(),
            value.unresolved_source.clone(),
            value.receiver_names.clone(),
            value.receiver_family_digest.clone(),
        ))
        .expect("correspondence is serializable"),
    );
    if expected != value.relation_digest {
        return Err(GradeRefusal::Invalid(
            "source/native relation digest drifted".to_owned(),
        ));
    }
    Ok(())
}

fn validate_manifest(manifest: &[InterventionManifestRow]) -> Result<(), GradeRefusal> {
    if manifest.len() != 16 {
        return Err(GradeRefusal::Invalid(
            "the complete intervention panel must contain exactly 16 rows".to_owned(),
        ));
    }
    let mut ids = BTreeSet::new();
    let mut laws = BTreeSet::new();
    for (index, row) in manifest.iter().enumerate() {
        if row.id.is_empty()
            || row.site.is_empty()
            || row.law_digest.is_empty()
            || !ids.insert(row.id.clone())
            || !laws.insert(row.law_digest.clone())
        {
            return Err(GradeRefusal::Invalid(
                "intervention manifest has empty or duplicate identity".to_owned(),
            ));
        }
        if row.id != INTERVENTION_ROW_IDS[index] {
            return Err(GradeRefusal::Invalid(
                "intervention manifest is not the fixed first-instance panel".to_owned(),
            ));
        }
        let needs_exact_span = matches!(index, 4 | 6 | 7 | 11);
        let needs_unseparated_span = index == 5;
        if row.site != INTERVENTION_SITES[index]
            || row.pre_intervention_prefix != INTERVENTION_PREFIX_FACES[index]
            || row.requires_separation != (index != 2)
            || row.order_face_control != (index == 2)
            || row.exact_control_span.is_some() != needs_exact_span
            || row.unseparated_control_span.is_some() != needs_unseparated_span
            || row
                .exact_control_span
                .into_iter()
                .chain(row.unseparated_control_span)
                .any(|span| span.extent == 0)
        {
            return Err(GradeRefusal::Invalid(
                "intervention manifest site/prefix/control contract differs".to_owned(),
            ));
        }
    }
    Ok(())
}

fn validate_interventions(
    manifest: &[InterventionManifestRow],
    body: &BodyObservation,
) -> Result<Vec<InterventionResult>, GradeRefusal> {
    if body.interventions.len() != manifest.len() {
        return Err(GradeRefusal::Invalid(format!(
            "{} intervention panel is incomplete",
            body.body.label()
        )));
    }
    let mut deeds = BTreeSet::new();
    let mut results = Vec::with_capacity(manifest.len());
    for (row, intervention) in manifest.iter().zip(&body.interventions) {
        if intervention.body != body.body
            || intervention.row_id != row.id
            || intervention.site != row.site
            || intervention.law_digest != row.law_digest
            || intervention.pre_intervention_prefix != row.pre_intervention_prefix
            || intervention.intervention_occurrence_digest.is_empty()
            || intervention.order_face_before_digest.is_empty()
            || intervention.order_face_after_digest.is_empty()
            || !deeds.insert(intervention.deed.execution.deed_identity.clone())
        {
            return Err(GradeRefusal::Invalid(format!(
                "{} intervention manifest differs",
                body.body.label()
            )));
        }
        let before_digest = canonical_return_digest(&intervention.before.faces)?;
        let after_digest = canonical_return_digest(&intervention.after.faces)?;
        let relations = face_relations(&intervention.before.faces, &intervention.after.faces);
        let shortest = shortest_separator(&intervention.before.faces, &intervention.after.faces);
        let order_unchanged =
            intervention.order_face_before_digest == intervention.order_face_after_digest;
        let exact_span_holds = row.exact_control_span.map_or(true, |span| {
            control_span_holds(
                &intervention.before.faces,
                &intervention.after.faces,
                span,
                true,
            )
        });
        let unseparated_span_holds = row.unseparated_control_span.map_or(true, |span| {
            control_span_holds(
                &intervention.before.faces,
                &intervention.after.faces,
                span,
                false,
            )
        });
        if before_digest != intervention.before.digest
            || after_digest != intervention.after.digest
            || before_digest != body.base_return_digest
            || !intervention.prefix_holds()
            || (row.requires_separation && shortest.is_none())
            || (row.order_face_control
                && (!order_unchanged
                    || relations
                        .iter()
                        .all(|relation| *relation == FaceRelation::BitIdentical)))
            || !exact_span_holds
            || !unseparated_span_holds
            || intervention
                .before
                .faces
                .iter()
                .chain(&intervention.after.faces)
                .any(|face| face.material_digest != body.base_material_digest)
        {
            return Err(GradeRefusal::Invalid(format!(
                "{} intervention row {} is not a matched base/prefix return",
                body.body.label(),
                row.id
            )));
        }
        validate_bound_deed(&intervention.deed, &after_digest, body.body)?;
        results.push(InterventionResult {
            body: body.body,
            row_id: row.id.clone(),
            relations,
            shortest_separator: shortest,
            prefix_holds: true,
            order_face_unchanged: order_unchanged,
        });
    }
    Ok(results)
}

fn control_span_holds(before: &[Face], after: &[Face], span: ControlSpan, exact: bool) -> bool {
    let (Some(left), Some(right)) = (before.get(span.face_index), after.get(span.face_index))
    else {
        return false;
    };
    if left.name != right.name {
        return false;
    }
    let Some(end) = span.start.checked_add(span.extent) else {
        return false;
    };
    let (Some(left), Some(right)) = (
        left.intervals.get(span.start..end),
        right.intervals.get(span.start..end),
    ) else {
        return false;
    };
    if exact {
        left == right
    } else {
        left.iter()
            .zip(right)
            .all(|(a, b)| !(a.1 < b.0 || b.1 < a.0))
    }
}

fn validate_held_out(
    cases: &[HeldOutCase],
    foreign: &BodyObservation,
    predecessor: &BodyObservation,
    cultivated: &BodyObservation,
) -> Result<Vec<HeldOutChange>, GradeRefusal> {
    let mut by_kind = BTreeMap::new();
    let mut input_lineages = BTreeSet::new();
    for case in cases {
        if by_kind.insert(case.kind, case).is_some() {
            return Err(GradeRefusal::Invalid("duplicate held-out kind".to_owned()));
        }
        if !is_digest(&case.lineage_digest)
            || !is_digest(&case.input_baseline_digest)
            || case.returns.len() != 3
        {
            return Err(GradeRefusal::Invalid(
                "held-out case is incomplete".to_owned(),
            ));
        }
        let mut deeds = BTreeSet::new();
        for (expected, returned) in [Body::ForeignSource, Body::W2Predecessor, Body::W3Cultivated]
            .into_iter()
            .zip(&case.returns)
        {
            let after = canonical_return_digest(&returned.returned.faces)?;
            if returned.body != expected
                || !is_digest(&returned.input_lineage_digest)
                || !input_lineages.insert(returned.input_lineage_digest.clone())
                || after != returned.returned.digest
                || returned
                    .returned
                    .faces
                    .iter()
                    .any(|face| face.material_digest != case.lineage_digest)
                || (case.kind != HeldOutKind::CodecVariant
                    && !deeds.insert(returned.deed.execution.deed_identity.clone()))
            {
                return Err(GradeRefusal::Invalid(
                    "held-out return is copied or unbound".to_owned(),
                ));
            }
            validate_bound_deed_with_allowance(
                &returned.deed,
                &after,
                returned.body,
                case.kind == HeldOutKind::NoOp && returned.body == Body::W3Cultivated,
            )?;
        }
    }
    for kind in [
        HeldOutKind::StructuralChanged,
        HeldOutKind::SubjectDisjointUnchanged,
        HeldOutKind::MatchedFoil,
        HeldOutKind::NoOp,
        HeldOutKind::CodecVariant,
    ] {
        if !by_kind.contains_key(&kind) {
            return Err(GradeRefusal::Invalid(format!(
                "held-out case {kind:?} is absent"
            )));
        }
    }
    let mut changes = Vec::new();
    for (kind, case) in by_kind {
        let changed: Vec<(Body, bool)> = case
            .returns
            .iter()
            .map(|returned| {
                (
                    returned.body,
                    returned.returned.digest != case.input_baseline_digest,
                )
            })
            .collect();
        match kind {
            HeldOutKind::StructuralChanged | HeldOutKind::MatchedFoil
                if !changed.iter().all(|(_, changed)| *changed) =>
            {
                return Err(GradeRefusal::Invalid(format!(
                    "held-out {kind:?} did not change"
                )));
            }
            HeldOutKind::SubjectDisjointUnchanged | HeldOutKind::NoOp
                if changed.iter().any(|(_, changed)| *changed) =>
            {
                return Err(GradeRefusal::Invalid(format!("held-out {kind:?} changed")));
            }
            _ => {}
        }
        let foreign_return = &case.returns[0];
        let predecessor_return = &case.returns[1];
        let cultivated_return = &case.returns[2];
        if kind == HeldOutKind::NoOp
            && cultivated_return.deed.execution.kind != ExecutionKind::NoMorphologyControl
        {
            return Err(GradeRefusal::Invalid(
                "no-op held-out row did not withhold the morphology return".to_owned(),
            ));
        }
        let w3_same = cultivated_return.returned.digest == predecessor_return.returned.digest;
        if foreign_return.returned.digest != predecessor_return.returned.digest {
            return Err(GradeRefusal::Invalid(format!(
                "held-out {kind:?} foreign/W2 cross-chart differs"
            )));
        }
        if matches!(
            kind,
            HeldOutKind::StructuralChanged | HeldOutKind::MatchedFoil
        ) && w3_same
        {
            return Err(GradeRefusal::Invalid(format!(
                "held-out {kind:?} cultivation did not change"
            )));
        }
        if matches!(
            kind,
            HeldOutKind::SubjectDisjointUnchanged | HeldOutKind::NoOp
        ) && !w3_same
        {
            return Err(GradeRefusal::Invalid(format!(
                "held-out {kind:?} cultivation changed"
            )));
        }
        if kind == HeldOutKind::CodecVariant {
            if case.codec_paths.len() != 2
                || case.codec_paths[0].path_identity.is_empty()
                || case.codec_paths[1].path_identity.is_empty()
                || case.codec_paths[0].path_identity == case.codec_paths[1].path_identity
                || case.codec_paths[0].token_word_digest.is_empty()
                || case.codec_paths[0].token_word_digest != case.codec_paths[1].token_word_digest
            {
                return Err(GradeRefusal::Invalid(
                    "codec variant paths are not distinct/equal-word".to_owned(),
                ));
            }
        }
        let cross_chart_changed = case
            .returns
            .windows(2)
            .any(|pair| pair[0].returned.digest != pair[1].returned.digest);
        let cultivated_change = case
            .returns
            .iter()
            .find(|returned| returned.body == Body::W2Predecessor)
            .unwrap()
            .returned
            .digest
            != case
                .returns
                .iter()
                .find(|returned| returned.body == Body::W3Cultivated)
                .unwrap()
                .returned
                .digest;
        changes.push(HeldOutChange {
            kind,
            changed,
            cross_chart_changed,
            cultivated_change,
        });
    }
    let _ = (foreign, predecessor, cultivated);
    Ok(changes)
}

fn validate_condensation(value: &CondensationRemainder) -> Result<(), GradeRefusal> {
    if value.prior_artifact_digest.is_empty()
        || value.prior_receiver_family.is_empty()
        || value.enlarged_receiver_family.is_empty()
        || value.retained_separators.is_empty()
        || value.open_fibres.is_empty()
        || value.refinement_digest.is_empty()
    {
        return Err(GradeRefusal::Invalid(
            "no-factor condensation remainder is incomplete".to_owned(),
        ));
    }
    validate_names(&value.prior_receiver_family)?;
    validate_names(&value.enlarged_receiver_family)?;
    let prior: BTreeSet<&String> = value.prior_receiver_family.iter().collect();
    let enlarged: BTreeSet<&String> = value.enlarged_receiver_family.iter().collect();
    if !prior.is_subset(&enlarged)
        || enlarged.len() <= prior.len()
        || value.enlarged_collapsed_population > value.prior_collapsed_population
    {
        return Err(GradeRefusal::Invalid(
            "condensation remainder violates receiver/population monotonicity".to_owned(),
        ));
    }
    let expected = digest(
        &serde_json::to_vec(&(
            value.prior_artifact_digest.clone(),
            value.prior_receiver_family.clone(),
            value.enlarged_receiver_family.clone(),
            value.prior_collapsed_population.clone(),
            value.enlarged_collapsed_population.clone(),
            value.retained_separators.clone(),
            value.open_fibres.clone(),
        ))
        .expect("condensation is serializable"),
    );
    if expected != value.refinement_digest {
        return Err(GradeRefusal::Invalid(
            "condensation refinement receipt drifted".to_owned(),
        ));
    }
    Ok(())
}

fn validate_recombination(
    value: &NativeRecombinationReceipt,
    held_out: &[HeldOutCase],
    foreign: &BodyObservation,
    predecessor: &BodyObservation,
    cultivated: &BodyObservation,
) -> Result<Vec<CauseAblationResult>, GradeRefusal> {
    if value.held_out_lineage_digest.is_empty()
        || value.lifted_cause_ids.len() < 2
        || value.cultivation_delta_id != cultivated.cultivation_delta_id
        || value.source_closure_identity != predecessor.source_closure_identity
        || value.source_closure_absence.source_closure_identity != value.source_closure_identity
        || !value.source_closure_absence.overlay_topology_absent
        || value
            .source_closure_absence
            .absent_overlay_operation_ids
            .is_empty()
        || value.source_closure_absence.absent_factor_populations.len() != 2
        || value
            .source_closure_absence
            .held_out_difference_digest
            .is_empty()
    {
        return Err(GradeRefusal::Invalid(
            "native recombination receipt lacks authenticated causes/closure".to_owned(),
        ));
    }
    let manifest_laws: BTreeSet<&str> = predecessor
        .interventions
        .iter()
        .map(|row| row.law_digest.as_str())
        .collect();
    let mut causes = BTreeSet::new();
    for cause in &value.lifted_cause_ids {
        if cause.is_empty() || !causes.insert(cause) || !manifest_laws.contains(cause.as_str()) {
            return Err(GradeRefusal::Invalid(
                "lifted cause ID is not authenticated by W2".to_owned(),
            ));
        }
    }
    let expected_absence = digest(
        &serde_json::to_vec(&(
            value.source_closure_identity.clone(),
            value.source_closure_absence.overlay_topology_absent,
            value
                .source_closure_absence
                .absent_overlay_operation_ids
                .clone(),
            value
                .source_closure_absence
                .absent_factor_populations
                .clone(),
            value
                .source_closure_absence
                .held_out_difference_digest
                .clone(),
        ))
        .expect("absence is serializable"),
    );
    if expected_absence != value.source_closure_absence.witness_digest {
        return Err(GradeRefusal::Invalid(
            "source-closure absence witness drifted".to_owned(),
        ));
    }
    let target = held_out
        .iter()
        .find(|case| case.lineage_digest == value.held_out_lineage_digest)
        .ok_or_else(|| {
            GradeRefusal::Invalid("recombination held-out lineage is absent".to_owned())
        })?;
    let target_w2 = target
        .returns
        .iter()
        .find(|returned| returned.body == Body::W2Predecessor)
        .ok_or_else(|| {
            GradeRefusal::Invalid("recombination W2 held-out return is absent".to_owned())
        })?;
    let target_w3 = target
        .returns
        .iter()
        .find(|returned| returned.body == Body::W3Cultivated)
        .ok_or_else(|| {
            GradeRefusal::Invalid("recombination W3 held-out return is absent".to_owned())
        })?;
    let expected_difference = digest(
        &serde_json::to_vec(&(
            target_w2.returned.digest.clone(),
            target_w3.returned.digest.clone(),
        ))
        .expect("held-out difference is serializable"),
    );
    let absent_operations: BTreeSet<&str> = value
        .source_closure_absence
        .absent_overlay_operation_ids
        .iter()
        .map(String::as_str)
        .collect();
    let absent_factors: BTreeSet<&str> = value
        .source_closure_absence
        .absent_factor_populations
        .iter()
        .map(String::as_str)
        .collect();
    if value.source_closure_absence.held_out_difference_digest != expected_difference
        || absent_operations.len()
            != value
                .source_closure_absence
                .absent_overlay_operation_ids
                .len()
        || absent_operations.iter().any(|identity| identity.is_empty())
        || absent_factors.len() != 2
        || absent_factors.iter().any(|identity| identity.is_empty())
    {
        return Err(GradeRefusal::Invalid(
            "source-closure absence is not bound to the held-out return".to_owned(),
        ));
    }
    let baseline_digest = canonical_return_digest(&value.baseline.faces)?;
    let recombined_digest = canonical_return_digest(&value.recombined.faces)?;
    if baseline_digest != value.baseline.digest
        || recombined_digest != value.recombined.digest
        || baseline_digest != target_w2.returned.digest
        || recombined_digest != target_w3.returned.digest
        || recombined_digest == baseline_digest
    {
        return Err(GradeRefusal::Invalid(
            "native recombination baseline/current return is invalid".to_owned(),
        ));
    }
    validate_bound_deed(
        &value.recombined_deed,
        &recombined_digest,
        Body::W3Cultivated,
    )?;
    let mut results = Vec::new();
    if value.cause_ablations.len() != value.lifted_cause_ids.len() {
        return Err(GradeRefusal::Invalid(
            "not every lifted cause has an ablation".to_owned(),
        ));
    }
    for ablation in &value.cause_ablations {
        let cause = predecessor
            .interventions
            .iter()
            .find(|intervention| intervention.row_id == ablation.intervention_row_id)
            .ok_or_else(|| {
                GradeRefusal::Invalid("ablation intervention row is absent".to_owned())
            })?;
        if cause.law_digest != ablation.cause_id
            || ablation.input_lineage_digest != target.lineage_digest
        {
            return Err(GradeRefusal::Invalid(
                "ablation cause is not bound to its row/material".to_owned(),
            ));
        }
        validate_ablation(
            ablation,
            &recombined_digest,
            &recombined_digest,
            None,
            [Body::W3Cultivated; 3],
            [Body::W3Cultivated; 2],
        )?;
        results.push(CauseAblationResult {
            cause_id: ablation.cause_id.clone(),
            changed: ablation.before.digest != ablation.ablated.digest,
            restored: ablation.restored.digest == recombined_digest,
            control_held: control_held(ablation),
        });
    }
    let cause_ids: BTreeSet<&str> = value
        .cause_ablations
        .iter()
        .map(|a| a.cause_id.as_str())
        .collect();
    if cause_ids != value.lifted_cause_ids.iter().map(String::as_str).collect()
        || value.cultivation_delta.cause_id != value.cultivation_delta_id
        || value.cultivation_delta.intervention_row_id != "cultivation-delta"
        || value.cultivation_delta.input_lineage_digest != target.lineage_digest
    {
        return Err(GradeRefusal::Invalid(
            "ablation cause coverage is incomplete".to_owned(),
        ));
    }
    validate_ablation(
        &value.cultivation_delta,
        &recombined_digest,
        &recombined_digest,
        Some(&target_w2.returned.digest),
        [Body::W3Cultivated, Body::W2Predecessor, Body::W3Cultivated],
        [Body::W3Cultivated, Body::W2Predecessor],
    )?;
    results.push(CauseAblationResult {
        cause_id: value.cultivation_delta.cause_id.clone(),
        changed: value.cultivation_delta.before.digest != value.cultivation_delta.ablated.digest,
        restored: value.cultivation_delta.restored.digest == recombined_digest,
        control_held: control_held(&value.cultivation_delta),
    });
    let _ = (foreign, cultivated);
    Ok(results)
}

fn validate_ablation(
    ablation: &CauseAblation,
    expected_before: &str,
    expected_restore: &str,
    expected_ablated: Option<&str>,
    deed_bodies: [Body; 3],
    control_bodies: [Body; 2],
) -> Result<(), GradeRefusal> {
    if ablation.cause_id.is_empty()
        || ablation.intervention_row_id.is_empty()
        || !is_digest(&ablation.input_lineage_digest)
        || !is_digest(&ablation.control_input_lineage_digest)
        || ablation.deeds.len() != 3
        || ablation.control_deeds.len() != 2
    {
        return Err(GradeRefusal::Invalid(
            "ablation identity/deed populations are incomplete".to_owned(),
        ));
    }
    if ablation.control_cause_id != ablation.cause_id
        || ablation.control_intervention_row_id != ablation.intervention_row_id
    {
        return Err(GradeRefusal::Invalid(
            "ablation control cause/row identity differs".to_owned(),
        ));
    }

    let deed_ids: BTreeSet<&str> = ablation
        .deeds
        .iter()
        .map(|deed| deed.execution.deed_identity.as_str())
        .collect();
    if deed_ids.len() != 3 {
        return Err(GradeRefusal::Invalid(
            "ablation main deed identities are not distinct".to_owned(),
        ));
    }

    let before = canonical_return_digest(&ablation.before.faces)?;
    if before != ablation.before.digest || before != expected_before {
        return Err(GradeRefusal::Invalid(
            "ablation main before return is not bound".to_owned(),
        ));
    }
    let altered = canonical_return_digest(&ablation.ablated.faces)?;
    if altered != ablation.ablated.digest || before == altered {
        return Err(GradeRefusal::Invalid(
            "ablation main return did not exhibit a changed face".to_owned(),
        ));
    }
    if expected_ablated.is_some_and(|expected| altered != expected) {
        return Err(GradeRefusal::Invalid(
            "ablation altered return differs from the expected predecessor".to_owned(),
        ));
    }
    let restored = canonical_return_digest(&ablation.restored.faces)?;
    if restored != ablation.restored.digest || restored != expected_restore {
        return Err(GradeRefusal::Invalid(
            "ablation restoration does not return the recombined face".to_owned(),
        ));
    }
    if ablation
        .before
        .faces
        .iter()
        .chain(&ablation.ablated.faces)
        .chain(&ablation.restored.faces)
        .any(|face| face.material_digest != ablation.input_lineage_digest)
    {
        return Err(GradeRefusal::Invalid(
            "ablation main returns carry the wrong material lineage".to_owned(),
        ));
    }

    for ((deed, expected), expected_body) in ablation
        .deeds
        .iter()
        .zip([before.as_str(), altered.as_str(), restored.as_str()])
        .zip(deed_bodies)
    {
        validate_bound_deed(deed, expected, expected_body).map_err(|error| {
            GradeRefusal::Invalid(format!("ablation main deed binding: {error}"))
        })?;
    }

    let control_before = canonical_return_digest(&ablation.control_before.faces)?;
    let control_after = canonical_return_digest(&ablation.control_after.faces)?;
    if control_before != ablation.control_before.digest
        || control_after != ablation.control_after.digest
    {
        return Err(GradeRefusal::Invalid(
            "ablation control return digest is not canonical".to_owned(),
        ));
    }
    if ablation
        .control_before
        .faces
        .iter()
        .chain(&ablation.control_after.faces)
        .any(|face| face.material_digest != ablation.control_input_lineage_digest)
    {
        return Err(GradeRefusal::Invalid(
            "ablation control returns carry the wrong material lineage".to_owned(),
        ));
    }
    let control_ids: BTreeSet<&str> = ablation
        .control_deeds
        .iter()
        .map(|deed| deed.execution.deed_identity.as_str())
        .collect();
    if control_ids.len() != 2 {
        return Err(GradeRefusal::Invalid(
            "ablation control deed identities are not distinct".to_owned(),
        ));
    }

    match ablation.control_kind {
        AblationControlKind::CausalPrefix => {
            if ablation.control_input_lineage_digest != ablation.input_lineage_digest {
                return Err(GradeRefusal::Invalid(
                    "causal-prefix control lineage differs from the ablated input".to_owned(),
                ));
            }
            if control_before != control_after
                || !strict_equal_prefix(&ablation.before, &ablation.ablated, &ablation.control_before)
                || ablation.control_deeds[0] != ablation.deeds[0]
                || ablation.control_deeds[1] != ablation.deeds[1]
            {
                return Err(GradeRefusal::Invalid(
                    "causal-prefix control is not the same pre-site worldline".to_owned(),
                ));
            }
            for ((deed, expected), expected_body) in ablation
                .control_deeds
                .iter()
                .zip([before.as_str(), altered.as_str()])
                .zip(control_bodies)
            {
                validate_bound_deed(deed, expected, expected_body).map_err(|error| {
                    GradeRefusal::Invalid(format!("causal-prefix control deed binding: {error}"))
                })?;
            }
        }
        AblationControlKind::SubjectDisjoint => {
            if ablation.control_input_lineage_digest == ablation.input_lineage_digest {
                return Err(GradeRefusal::Invalid(
                    "subject-disjoint control reuses the ablated input lineage".to_owned(),
                ));
            }
            if ablation.control_before != ablation.control_after {
                return Err(GradeRefusal::Invalid(
                    "subject-disjoint control before/after returns differ".to_owned(),
                ));
            }
            if ablation
                .control_deeds
                .iter()
                .any(|deed| deed.execution.deed_identity == ablation.deeds[0].execution.deed_identity
                    || deed.execution.deed_identity == ablation.deeds[1].execution.deed_identity
                    || deed.execution.deed_identity == ablation.deeds[2].execution.deed_identity)
            {
                return Err(GradeRefusal::Invalid(
                    "subject-disjoint control reused a causal deed".to_owned(),
                ));
            }
            for ((deed, expected), expected_body) in ablation
                .control_deeds
                .iter()
                .zip([control_before.as_str(), control_after.as_str()])
                .zip(control_bodies)
            {
                validate_bound_deed(deed, expected, expected_body).map_err(|error| {
                    GradeRefusal::Invalid(format!("subject-disjoint control deed binding: {error}"))
                })?;
            }
        }
    }
    Ok(())
}

fn strict_equal_prefix(
    before: &ReceiverReturn,
    after: &ReceiverReturn,
    control: &ReceiverReturn,
) -> bool {
    let extent = control.faces.len();
    extent > 0
        && extent < before.faces.len()
        && extent < after.faces.len()
        && control.faces == before.faces[..extent]
        && control.faces == after.faces[..extent]
}

fn control_held(ablation: &CauseAblation) -> bool {
    match ablation.control_kind {
        AblationControlKind::CausalPrefix => {
            strict_equal_prefix(&ablation.before, &ablation.ablated, &ablation.control_before)
        }
        AblationControlKind::SubjectDisjoint => {
            ablation.control_before == ablation.control_after
        }
    }
}


fn work_bound(value: &WorkReceipt, return_digest: &str) -> bool {
    if value.returned_artifact_digest != return_digest
        || value.admission_digest.is_empty()
        || value.admission_evidence.is_empty()
        || value.owner_receipt_digest.is_empty()
    {
        return false;
    }
    if digest(value.admission_evidence.as_bytes()) != value.admission_digest {
        return false;
    }
    let expected = digest(
        &serde_json::to_vec(&(
            value.work.clone(),
            value.admission_digest.clone(),
            value.returned_artifact_digest.clone(),
        ))
        .expect("work is serializable"),
    );
    expected == value.owner_receipt_digest
}

fn apparatus_bound(value: &ApparatusUtility, return_digest: &str) -> bool {
    let known_calibrated = |name: &str, coordinate: &Calibrated<BigUint>| match coordinate {
        Calibrated::Known(_) => value
            .calibration
            .get(name)
            .is_some_and(|text| !text.is_empty()),
        Calibrated::Unknown { reason } => !reason.is_empty(),
    };
    !value.device_name.is_empty()
        && !value.mode.is_empty()
        && !value.kernel_identity.is_empty()
        && value.returned_artifact_digest == return_digest
        && !value.apparatus_evidence.is_empty()
        && is_digest(&value.apparatus_digest)
        && digest(value.apparatus_evidence.as_bytes()) == value.apparatus_digest
        && known_calibrated("launches", &value.launches)
        && known_calibrated("synchronizations", &value.synchronizations)
        && known_calibrated("transfer_octets", &value.transfer_octets)
        && known_calibrated("active_warps", &value.active_warps)
        && known_calibrated("energy", &value.energy)
}

fn distinct_body_digests(bodies: &[BodyObservation]) -> bool {
    let mut digests = BTreeSet::new();
    bodies
        .iter()
        .all(|body| !body.body_digest.is_empty() && digests.insert(&body.body_digest))
}

fn validate_names(names: &[String]) -> Result<(), GradeRefusal> {
    let mut seen = BTreeSet::new();
    if names
        .iter()
        .any(|name| name.is_empty() || !seen.insert(name))
    {
        return Err(GradeRefusal::Invalid(
            "receiver names are empty or duplicated".to_owned(),
        ));
    }
    Ok(())
}

fn ordered_face_names(faces: &[Face]) -> Vec<String> {
    faces.iter().map(|face| face.name.clone()).collect()
}

fn receiver_family_digest(names: &[String]) -> String {
    digest(&serde_json::to_vec(names).expect("receiver family is serializable"))
}

/// First returned receiver face/interval whose enclosures are disjoint. Bit-identical and
/// overlapping-but-different faces are deliberately not separators.
pub fn shortest_separator(before: &[Face], after: &[Face]) -> Option<ShortestSeparator> {
    let extent = before.len().max(after.len());
    for face_index in 0..extent {
        let left = before
            .get(face_index)
            .map(|face| face.intervals.as_slice())
            .unwrap_or(&[]);
        let right = after
            .get(face_index)
            .map(|face| face.intervals.as_slice())
            .unwrap_or(&[]);
        let interval_extent = left.len().max(right.len());
        for interval_index in 0..interval_extent {
            let Some(a) = left.get(interval_index) else {
                return Some(ShortestSeparator {
                    face_index,
                    interval_index,
                });
            };
            let Some(b) = right.get(interval_index) else {
                return Some(ShortestSeparator {
                    face_index,
                    interval_index,
                });
            };
            if a.1 < b.0 || b.1 < a.0 {
                return Some(ShortestSeparator {
                    face_index,
                    interval_index,
                });
            }
        }
    }
    None
}

fn face_relations(before: &[Face], after: &[Face]) -> Vec<FaceRelation> {
    before
        .iter()
        .zip(after)
        .map(|(a, b)| {
            if a.name == b.name && a.intervals == b.intervals {
                FaceRelation::BitIdentical
            } else if a
                .intervals
                .iter()
                .zip(&b.intervals)
                .any(|(x, y)| x.1 < y.0 || y.1 < x.0)
                || a.intervals.len() != b.intervals.len()
            {
                FaceRelation::Separated
            } else {
                FaceRelation::OverlappingDifferent
            }
        })
        .collect()
}

fn canonical_intervals(intervals: &[(i64, i64)]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(intervals.len() * 16 + 8);
    bytes.extend((intervals.len() as u64).to_le_bytes());
    for (lower, upper) in intervals {
        bytes.extend(lower.to_le_bytes());
        bytes.extend(upper.to_le_bytes());
    }
    bytes
}

fn canonical_return_digest(faces: &[Face]) -> Result<String, GradeRefusal> {
    validate_names(&ordered_face_names(faces))?;
    if faces.iter().any(|face| {
        face.intervals.is_empty()
            || !is_digest(&face.material_digest)
            || face.intervals.iter().any(|(lower, upper)| lower > upper)
    }) {
        return Err(GradeRefusal::Invalid(
            "receiver face has empty bytes/material identity".to_owned(),
        ));
    }
    let mut bytes = Vec::new();
    for face in faces {
        frame(&mut bytes, face.name.as_bytes());
        frame(&mut bytes, face.material_digest.as_bytes());
        frame(&mut bytes, &canonical_intervals(&face.intervals));
    }
    Ok(digest(&bytes))
}

fn frame(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend((bytes.len() as u64).to_le_bytes());
    out.extend(bytes);
}

fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
