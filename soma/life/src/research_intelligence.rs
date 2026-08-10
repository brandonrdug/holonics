//! Heterogeneous executable world for one continuing laboratory-language body.
//!
//! Repository inscriptions, dialogue occurrences, exact mathematics, and Rust execution are
//! distinct receiver sections. A leader may contact several of them concurrently through its
//! own feature region. Mathematical and code results do not exist as conditioning passages until
//! the corresponding leader causes their deeds and the exterior world returns.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
    process::Command,
    time::Instant,
};

use holonic_engine::{
    ArithmeticFiberEvent, ArithmeticMonodromyEvent, ArithmeticMonodromyLaw,
    ArithmeticMonodromyStanding, CausalWorld, EulerReceiverId, EventId, IntegralQuinticProblem,
    QuinticProblemId,
};
use num_bigint::BigInt;
use serde::Serialize;
use sha2::{Digest, Sha256};

use crate::{
    causal_language::lexical_tokens,
    dialogue_lineage::{DialogueLineageOccurrence, DialogueSpeaker, ExactDialogueLineage},
    laboratory_language::{
        text_features, LaboratoryLanguageError, LaboratoryResearchLeader,
        LaboratoryReturnedSection, LaboratorySourceAtlas, LaboratorySourceKind,
        LaboratoryWorldReturn,
    },
};

const MATHEMATICS_RECEIVER: u64 = 30_000_000;
const CODE_RECEIVER_BASE: u64 = 31_000_000;

#[derive(Clone, Debug)]
pub struct ExactQuinticResearchSpec {
    pub identity: String,
    pub problem: IntegralQuinticProblem,
    pub receiver: EulerReceiverId,
    pub sigma: u32,
    pub integer_through: u64,
    /// How many affine integer-polynomial torsors one horn-resolution event may retain. Declared by
    /// whoever forms the spec; `prime_ecology` stopped picking a default on 2026-08-09
    /// (`canon/THE_CONTAMINANT_PROTOCOL.md` §2.5).
    pub horn_local_section_limit: u64,
}

impl ExactQuinticResearchSpec {
    pub fn new(
        identity: impl Into<String>,
        problem_id: QuinticProblemId,
        coefficients: Vec<BigInt>,
        receiver: EulerReceiverId,
        sigma: u32,
        integer_through: u64,
        horn_local_section_limit: u64,
    ) -> Result<Self, String> {
        if horn_local_section_limit == 0 {
            return Err("a horn local-section limit of zero admits no torsor".to_owned());
        }
        if integer_through < 11 {
            return Err(
                "an arithmetic-monodromy deed must admit integers through at least 11".to_owned(),
            );
        }
        let identity = identity.into();
        let problem = IntegralQuinticProblem::new(problem_id, identity.clone(), coefficients)
            .map_err(|error| error.to_string())?;
        Ok(Self {
            identity,
            problem,
            receiver,
            sigma,
            integer_through,
            horn_local_section_limit,
        })
    }
}

#[derive(Clone, Debug)]
pub struct RustVerificationSpec {
    pub identity: String,
    pub package: String,
    pub test_filter: String,
    /// Inherited interpretation of the named test. Success or obstruction remains returned
    /// testimony and is never copied into standing before execution.
    pub claim: String,
}

impl RustVerificationSpec {
    pub fn new(
        identity: impl Into<String>,
        package: impl Into<String>,
        test_filter: impl Into<String>,
        claim: impl Into<String>,
    ) -> Result<Self, String> {
        let spec = Self {
            identity: identity.into(),
            package: package.into(),
            test_filter: test_filter.into(),
            claim: claim.into(),
        };
        if spec.identity.trim().is_empty()
            || spec.package.trim().is_empty()
            || spec.test_filter.trim().is_empty()
            || spec.claim.trim().is_empty()
        {
            return Err(
                "a Rust verification deed requires identity, package, test, and claim".to_owned(),
            );
        }
        Ok(spec)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExactQuinticResearchReceipt {
    pub schema: String,
    pub deed: String,
    pub inherited_coefficients: Vec<String>,
    pub normalized_coefficients: Vec<String>,
    pub discriminant: String,
    pub founded_primes: usize,
    pub prime_sections: usize,
    pub unramified_euler_sections: usize,
    pub open_polynomial_discriminant_places: Vec<u64>,
    pub unique_transitive_group: Option<String>,
    pub transitive_group_fiber: Vec<String>,
    pub euler_sigma: u32,
    pub euler_product_numerator: String,
    pub euler_product_denominator: String,
    pub cross_prime_root_sheet_gluing: String,
    pub held_out_cycle_residuals: Vec<String>,
    pub lineage_reused_exactly: bool,
    /// Exterior physical observation of this deed realization. It is not part of the exact
    /// arithmetic standing or generated-answer equality.
    pub elapsed_millis: u128,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RustVerificationReceipt {
    pub schema: String,
    pub deed: String,
    pub package: String,
    pub test_filter: String,
    pub claim: String,
    pub success: bool,
    pub exit_code: Option<i32>,
    pub stdout_sha256: String,
    pub stderr_sha256: String,
    pub elapsed_millis: u128,
}

/// Logical receiver work performed by the sparse dialogue membrane. These counts are exact and
/// deterministic for one world standing; wall time and device telemetry belong to the exterior
/// experiment receipt.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
pub struct ExactResearchWorldActivityReceipt {
    pub enacted_leaders: usize,
    pub dialogue_feature_lookups: usize,
    pub dialogue_feature_hits: usize,
    pub dialogue_candidate_section_visits: usize,
    pub dialogue_returned_section_visits: usize,
    pub dialogue_unique_candidate_sections: usize,
    pub dialogue_unique_returned_sections: usize,
}

/// One exterior world joined by caused contact, not by flattening its media into one prompt.
pub struct ExactResearchWorld<'a> {
    root: PathBuf,
    repository: &'a LaboratorySourceAtlas,
    dialogue_occurrences: &'a [DialogueLineageOccurrence],
    dialogue_sections: Vec<DialogueIndexedSection>,
    dialogue_feature_incidence: BTreeMap<String, BTreeSet<usize>>,
    quintic_spec: ExactQuinticResearchSpec,
    rust_specs: Vec<RustVerificationSpec>,
    quintic_receipt: Option<ExactQuinticResearchReceipt>,
    rust_receipts: BTreeMap<String, RustVerificationReceipt>,
    enacted_mathematics_deeds: usize,
    enacted_code_deeds: usize,
    activity: ExactResearchWorldActivityReceipt,
    dialogue_unique_candidate_sections: BTreeSet<usize>,
    dialogue_unique_returned_sections: BTreeSet<usize>,
}

#[derive(Clone, Debug)]
struct DialogueIndexedSection {
    occurrence_at: usize,
    local_at: usize,
    text: String,
    features: BTreeSet<String>,
}

struct DialogueSectionLookup {
    sections: Vec<LaboratoryReturnedSection>,
    complete_population: usize,
    omitted_population: usize,
    feature_lookups: usize,
    feature_hits: usize,
    candidate_section_indices: BTreeSet<usize>,
    returned_section_indices: BTreeSet<usize>,
}

impl<'a> ExactResearchWorld<'a> {
    pub fn new(
        root: &Path,
        repository: &'a LaboratorySourceAtlas,
        dialogue: &'a ExactDialogueLineage,
        quintic_spec: ExactQuinticResearchSpec,
        rust_specs: Vec<RustVerificationSpec>,
    ) -> Result<Self, String> {
        Self::new_over_dialogue_prefix(
            root,
            repository,
            dialogue,
            dialogue.occurrences().len(),
            quintic_spec,
            rust_specs,
        )
    }

    /// Form one receiver world over a caused prefix of an already verified dialogue lineage.
    /// The prefix is a receiver restriction of the retained lineage, not a fabricated replacement
    /// receipt and not a second scan of the raw rollout.
    pub fn new_over_dialogue_prefix(
        root: &Path,
        repository: &'a LaboratorySourceAtlas,
        dialogue: &'a ExactDialogueLineage,
        occurrence_count: usize,
        quintic_spec: ExactQuinticResearchSpec,
        rust_specs: Vec<RustVerificationSpec>,
    ) -> Result<Self, String> {
        if occurrence_count > dialogue.occurrences().len() {
            return Err(format!(
                "dialogue prefix {occurrence_count} exceeds verified lineage extent {}",
                dialogue.occurrences().len()
            ));
        }
        if rust_specs.is_empty() {
            return Err("the composed research world requires at least one code deed".to_owned());
        }
        let mut identities = BTreeSet::new();
        for spec in &rust_specs {
            if !identities.insert(spec.identity.clone()) {
                return Err(format!("duplicate Rust deed {}", spec.identity));
            }
        }
        let dialogue_occurrences = &dialogue.occurrences()[..occurrence_count];
        let mut dialogue_sections = Vec::new();
        for (occurrence_at, occurrence) in dialogue_occurrences.iter().enumerate() {
            for (local_at, text) in dialogue_local_surfaces(&occurrence.text)
                .into_iter()
                .enumerate()
            {
                let features = text_features(&text);
                if features.is_empty() {
                    continue;
                }
                dialogue_sections.push(DialogueIndexedSection {
                    occurrence_at,
                    local_at,
                    text,
                    features,
                });
            }
        }
        let mut dialogue_feature_incidence = BTreeMap::<String, BTreeSet<usize>>::new();
        for (section_at, section) in dialogue_sections.iter().enumerate() {
            for feature in &section.features {
                dialogue_feature_incidence
                    .entry(feature.clone())
                    .or_default()
                    .insert(section_at);
            }
        }
        Ok(Self {
            root: root.to_owned(),
            repository,
            dialogue_occurrences,
            dialogue_sections,
            dialogue_feature_incidence,
            quintic_spec,
            rust_specs,
            quintic_receipt: None,
            rust_receipts: BTreeMap::new(),
            enacted_mathematics_deeds: 0,
            enacted_code_deeds: 0,
            activity: ExactResearchWorldActivityReceipt::default(),
            dialogue_unique_candidate_sections: BTreeSet::new(),
            dialogue_unique_returned_sections: BTreeSet::new(),
        })
    }

    pub fn enact(
        &mut self,
        leader: &LaboratoryResearchLeader,
    ) -> Result<LaboratoryWorldReturn, LaboratoryLanguageError> {
        self.activity.enacted_leaders = self
            .activity
            .enacted_leaders
            .checked_add(1)
            .ok_or(LaboratoryLanguageError::CarrierExtent)?;
        let LaboratoryWorldReturn {
            mut sections,
            mut complete_population,
            mut omitted_population,
            ..
        } = self.repository.enact(leader)?;
        let dialogue = self.dialogue_sections(leader);
        complete_population = complete_population
            .checked_add(dialogue.complete_population)
            .ok_or(LaboratoryLanguageError::CarrierExtent)?;
        omitted_population = omitted_population
            .checked_add(dialogue.omitted_population)
            .ok_or(LaboratoryLanguageError::CarrierExtent)?;
        self.activity.dialogue_feature_lookups = self
            .activity
            .dialogue_feature_lookups
            .checked_add(dialogue.feature_lookups)
            .ok_or(LaboratoryLanguageError::CarrierExtent)?;
        self.activity.dialogue_feature_hits = self
            .activity
            .dialogue_feature_hits
            .checked_add(dialogue.feature_hits)
            .ok_or(LaboratoryLanguageError::CarrierExtent)?;
        self.activity.dialogue_candidate_section_visits = self
            .activity
            .dialogue_candidate_section_visits
            .checked_add(dialogue.candidate_section_indices.len())
            .ok_or(LaboratoryLanguageError::CarrierExtent)?;
        self.activity.dialogue_returned_section_visits = self
            .activity
            .dialogue_returned_section_visits
            .checked_add(dialogue.sections.len())
            .ok_or(LaboratoryLanguageError::CarrierExtent)?;
        self.dialogue_unique_candidate_sections
            .extend(dialogue.candidate_section_indices);
        self.dialogue_unique_returned_sections
            .extend(dialogue.returned_section_indices);
        self.activity.dialogue_unique_candidate_sections =
            self.dialogue_unique_candidate_sections.len();
        self.activity.dialogue_unique_returned_sections =
            self.dialogue_unique_returned_sections.len();
        sections.extend(dialogue.sections);
        if has_anchor(&leader.region, &["quintic", "galois", "monodromy", "euler"]) {
            if self.quintic_receipt.is_none() {
                self.quintic_receipt = Some(
                    execute_quintic(&self.quintic_spec).map_err(LaboratoryLanguageError::World)?,
                );
                self.enacted_mathematics_deeds = self
                    .enacted_mathematics_deeds
                    .checked_add(1)
                    .ok_or(LaboratoryLanguageError::CarrierExtent)?;
            }
            let returned = self.mathematics_sections(leader)?;
            complete_population = complete_population
                .checked_add(returned.len())
                .ok_or(LaboratoryLanguageError::CarrierExtent)?;
            sections.extend(returned);
        }
        if has_anchor(
            &leader.region,
            &["rust", "code", "compiler", "test", "bridge", "leader"],
        ) {
            let specs = self.rust_specs.clone();
            for spec in specs {
                if !spec_contact(&leader.region, &spec) {
                    continue;
                }
                if !self.rust_receipts.contains_key(&spec.identity) {
                    let receipt =
                        execute_rust(&self.root, &spec).map_err(LaboratoryLanguageError::World)?;
                    self.rust_receipts.insert(spec.identity.clone(), receipt);
                    self.enacted_code_deeds = self
                        .enacted_code_deeds
                        .checked_add(1)
                        .ok_or(LaboratoryLanguageError::CarrierExtent)?;
                }
                sections.push(self.rust_section(leader, &spec)?);
                complete_population = complete_population
                    .checked_add(1)
                    .ok_or(LaboratoryLanguageError::CarrierExtent)?;
            }
        }
        Ok(LaboratoryWorldReturn {
            leader: leader.identity.clone(),
            sections,
            complete_population,
            omitted_population,
        })
    }

    pub const fn quintic_receipt(&self) -> Option<&ExactQuinticResearchReceipt> {
        self.quintic_receipt.as_ref()
    }

    pub fn rust_receipts(&self) -> &BTreeMap<String, RustVerificationReceipt> {
        &self.rust_receipts
    }

    pub const fn enacted_mathematics_deeds(&self) -> usize {
        self.enacted_mathematics_deeds
    }

    pub const fn enacted_code_deeds(&self) -> usize {
        self.enacted_code_deeds
    }

    pub fn dialogue_conditioned_occurrences(&self) -> usize {
        self.dialogue_occurrences.len()
    }

    pub fn dialogue_indexed_features(&self) -> usize {
        self.dialogue_feature_incidence.len()
    }

    pub fn dialogue_local_sections(&self) -> usize {
        self.dialogue_sections.len()
    }

    pub const fn activity_receipt(&self) -> &ExactResearchWorldActivityReceipt {
        &self.activity
    }

    fn dialogue_sections(&self, leader: &LaboratoryResearchLeader) -> DialogueSectionLookup {
        let mut candidate_indices = BTreeSet::new();
        let mut feature_hits = 0usize;
        for feature in &leader.region {
            if let Some(indices) = self.dialogue_feature_incidence.get(feature) {
                feature_hits = feature_hits.saturating_add(1);
                candidate_indices.extend(indices.iter().copied());
            }
        }
        // Incidence only discovers which retained source occurrences cross the receiver region.
        // The aperture then restricts that caused source chronology directly; speaker, lexical
        // match cardinality, recency, and text extent never rank semantic survivors.
        let candidate_section_indices = candidate_indices;
        let complete_population = candidate_section_indices.len();
        let mut returned_section_indices = BTreeSet::new();
        let mut sections = Vec::with_capacity(complete_population.min(leader.aperture));
        for section_at in &candidate_section_indices {
            if sections.len() >= leader.aperture {
                continue;
            }
            let Some(section) = self.dialogue_sections.get(*section_at) else {
                continue;
            };
            let Some(occurrence) = self.dialogue_occurrences.get(section.occurrence_at) else {
                continue;
            };
            if section.features.is_disjoint(&leader.region) {
                continue;
            }
            returned_section_indices.insert(*section_at);
            sections.push(LaboratoryReturnedSection {
                identity: format!(
                    "{}/{}/surface-{}",
                    leader.identity, occurrence.identity, section.local_at
                ),
                source_identity: format!("{}/surface-{}", occurrence.identity, section.local_at),
                source: format!("codex-dialogue/{}", occurrence.turn),
                receiver: occurrence.receiver(),
                line: section.local_at,
                kind: match occurrence.speaker {
                    DialogueSpeaker::User => LaboratorySourceKind::DialogueUser,
                    DialogueSpeaker::Assistant => LaboratorySourceKind::DialogueAssistant,
                },
                text: section.text.clone(),
                matched_features: section
                    .features
                    .intersection(&leader.region)
                    .cloned()
                    .collect(),
            });
        }
        let omitted_population = complete_population.saturating_sub(sections.len());
        DialogueSectionLookup {
            sections,
            complete_population,
            omitted_population,
            feature_lookups: leader.region.len(),
            feature_hits,
            candidate_section_indices,
            returned_section_indices,
        }
    }

    fn mathematics_sections(
        &self,
        leader: &LaboratoryResearchLeader,
    ) -> Result<Vec<LaboratoryReturnedSection>, LaboratoryLanguageError> {
        let receipt = self
            .quintic_receipt
            .as_ref()
            .ok_or_else(|| LaboratoryLanguageError::World("missing quintic return".to_owned()))?;
        let group = receipt
            .unique_transitive_group
            .clone()
            .unwrap_or_else(|| receipt.transitive_group_fiber.join(" or "));
        let residual_surface = if receipt.held_out_cycle_residuals.is_empty() {
            "Every later unramified prime section remains inside the certified group cycle fiber."
                .to_owned()
        } else {
            format!(
                "Later prime sections obstruct the group cycle fiber at {}.",
                receipt.held_out_cycle_residuals.join(", ")
            )
        };
        let gluing_surface = match receipt.cross_prime_root_sheet_gluing.as_str() {
            "OpenWithoutTransportWitness" => {
                "Cross prime root sheet gluing remains open without a transport witness.".to_owned()
            }
            other => format!("Cross prime root sheet gluing returns as {other}."),
        };
        let surfaces = vec![
            format!(
                "The exact arithmetic monodromy ecology certifies the inherited quintic group as {group}."
            ),
            format!(
                "The sigma {} Euler receiver carries the exact rational product {} over {} through {} unramified prime sections.",
                receipt.euler_sigma,
                receipt.euler_product_numerator,
                receipt.euler_product_denominator,
                receipt.unramified_euler_sections,
            ),
            residual_surface,
            gluing_surface,
        ];
        Ok(surfaces
            .into_iter()
            .enumerate()
            .map(|(at, text)| LaboratoryReturnedSection {
                identity: format!("{}/math/{at}", leader.identity),
                source_identity: format!("mathematics-return/{}/section-{at}", receipt.deed),
                source: format!("mathematics-return/{}", receipt.deed),
                receiver: MATHEMATICS_RECEIVER,
                line: at,
                kind: LaboratorySourceKind::MathematicsReturn,
                matched_features: text_features(&text)
                    .intersection(&leader.region)
                    .cloned()
                    .collect(),
                text,
            })
            .collect())
    }

    fn rust_section(
        &self,
        leader: &LaboratoryResearchLeader,
        spec: &RustVerificationSpec,
    ) -> Result<LaboratoryReturnedSection, LaboratoryLanguageError> {
        let receipt = self.rust_receipts.get(&spec.identity).ok_or_else(|| {
            LaboratoryLanguageError::World(format!("missing Rust return {}", spec.identity))
        })?;
        let claim = receipt.claim.trim().trim_end_matches('.');
        let text = if receipt.success {
            format!("Exact Rust execution verifies that {claim}.")
        } else {
            format!("Exact Rust execution obstructs the claim that {claim}.")
        };
        Ok(LaboratoryReturnedSection {
            identity: format!("{}/code/{}", leader.identity, spec.identity),
            source_identity: format!("code-return/{}", spec.identity),
            source: format!("code-return/{}", spec.identity),
            receiver: CODE_RECEIVER_BASE
                .checked_add(
                    u64::try_from(
                        self.rust_specs
                            .iter()
                            .position(|candidate| candidate.identity == spec.identity)
                            .unwrap_or(0),
                    )
                    .map_err(|_| LaboratoryLanguageError::CarrierExtent)?,
                )
                .ok_or(LaboratoryLanguageError::CarrierExtent)?,
            line: 0,
            kind: LaboratorySourceKind::CodeReturn,
            matched_features: text_features(&text)
                .intersection(&leader.region)
                .cloned()
                .collect(),
            text,
        })
    }
}

fn execute_quintic(spec: &ExactQuinticResearchSpec) -> Result<ExactQuinticResearchReceipt, String> {
    const PROBLEM_EVENT: EventId = EventId(8_000_000_000);
    const RECEIVER_EVENT: EventId = EventId(8_000_000_001);
    let started = Instant::now();
    let law = ArithmeticMonodromyLaw::with_horn_local_section_limit(1, spec.horn_local_section_limit)
        .map_err(|error| error.to_string())?;
    let standing =
        ArithmeticMonodromyStanding::with_horn_local_section_limit(1, spec.horn_local_section_limit)
            .map_err(|error| error.to_string())?;
    let mut world = CausalWorld::new(law, standing);
    world
        .receive(&ArithmeticMonodromyEvent::InheritQuintic {
            event: PROBLEM_EVENT,
            problem: spec.problem.clone(),
        })
        .map_err(|error| error.to_string())?;
    world
        .receive(&ArithmeticMonodromyEvent::OpenEulerReceiver {
            event: RECEIVER_EVENT,
            id: spec.receiver,
            problem: spec.problem.id,
            sigma: spec.sigma,
        })
        .map_err(|error| error.to_string())?;
    let mut admitted_after_certificate = None::<BTreeSet<Vec<u32>>>;
    let mut held_out_cycle_residuals = Vec::new();
    for value in 2..=spec.integer_through {
        let transition = world
            .receive(&ArithmeticMonodromyEvent::AdmitInteger(
                ArithmeticFiberEvent {
                    event: EventId(value),
                    value,
                },
            ))
            .map_err(|error| error.to_string())?;
        if admitted_after_certificate.is_none()
            && world.standing().problems()[&spec.problem.id]
                .galois
                .unique_certified_group()
                .is_some()
        {
            admitted_after_certificate = Some(
                world.standing().problems()[&spec.problem.id]
                    .galois
                    .admitted_future_cycle_types()
                    .map_err(|error| error.to_string())?,
            );
            continue;
        }
        if let Some(admitted) = &admitted_after_certificate {
            for section in transition.radiation[0]
                .transported_sections
                .iter()
                .filter(|section| section.problem == spec.problem.id)
            {
                if let Some(cycle_type) = &section.cycle_type {
                    if !admitted.contains(cycle_type) {
                        held_out_cycle_residuals
                            .push(format!("prime {} cycle {cycle_type:?}", section.prime));
                    }
                }
            }
        }
    }
    world
        .standing()
        .validate()
        .map_err(|error| error.to_string())?;
    let standing = world.standing();
    let problem = &standing.problems()[&spec.problem.id];
    let receiver = &standing.euler_receivers()[&spec.receiver];
    let atlas = standing
        .atlas_receipt(spec.problem.id)
        .map_err(|error| error.to_string())?;
    let lineage_reused_exactly = receiver.local_sections.iter().all(|(prime, local)| {
        problem.prime_sections[prime].source_events == local.source_events
            && problem.prime_sections[prime].euler_denominator.as_ref()
                == Some(&local.denominator_polynomial)
    });
    Ok(ExactQuinticResearchReceipt {
        schema: "life.exact-quintic-research-return.v1".to_owned(),
        deed: spec.identity.clone(),
        inherited_coefficients: problem
            .problem
            .coefficients
            .iter()
            .map(ToString::to_string)
            .collect(),
        normalized_coefficients: problem
            .normalized
            .coefficients
            .iter()
            .map(ToString::to_string)
            .collect(),
        discriminant: problem.normalized.discriminant.to_string(),
        founded_primes: standing.prime_ecology().arithmetic().prime_cells().len(),
        prime_sections: problem.prime_sections.len(),
        unramified_euler_sections: receiver.local_sections.len(),
        open_polynomial_discriminant_places: receiver.open_places.keys().copied().collect(),
        unique_transitive_group: problem
            .galois
            .unique_certified_group()
            .map(|group| format!("{group:?}")),
        transitive_group_fiber: problem
            .galois
            .transitive_candidates
            .iter()
            .map(|group| format!("{group:?}"))
            .collect(),
        euler_sigma: receiver.sigma,
        euler_product_numerator: receiver.exact_product.numer().to_string(),
        euler_product_denominator: receiver.exact_product.denom().to_string(),
        cross_prime_root_sheet_gluing: format!("{:?}", atlas.cross_prime_root_sheet_gluing),
        held_out_cycle_residuals,
        lineage_reused_exactly,
        elapsed_millis: started.elapsed().as_millis(),
    })
}

/// Enact one code deed by executing the named test in the caller's declared workspace.
///
/// `root` is the **cargo workspace root**, used verbatim. It was `root.join("src/soma")` until
/// 2026-08-10 — the archived laboratory's directory layout folded into the world executor, so the
/// deed resolved to a path that does not exist in this body and the code section of this world
/// could never return. That is `CLAUDE.md` §0's second lesson (*no absolute frame in a lineage*)
/// living inside the one organ whose whole purpose is executing in a foreign chart.
fn execute_rust(
    root: &Path,
    spec: &RustVerificationSpec,
) -> Result<RustVerificationReceipt, String> {
    let started = Instant::now();
    let output = Command::new("cargo")
        .current_dir(root)
        .env("CARGO_TERM_COLOR", "never")
        .args([
            "test",
            "-p",
            spec.package.as_str(),
            spec.test_filter.as_str(),
            "--",
            "--exact",
        ])
        .output()
        .map_err(|error| format!("execute Rust deed {}: {error}", spec.identity))?;
    Ok(RustVerificationReceipt {
        schema: "life.rust-verification-return.v1".to_owned(),
        deed: spec.identity.clone(),
        package: spec.package.clone(),
        test_filter: spec.test_filter.clone(),
        claim: spec.claim.clone(),
        success: output.status.success(),
        exit_code: output.status.code(),
        stdout_sha256: sha256_hex(&output.stdout),
        stderr_sha256: sha256_hex(&output.stderr),
        elapsed_millis: started.elapsed().as_millis(),
    })
}

fn has_anchor(region: &BTreeSet<String>, anchors: &[&str]) -> bool {
    anchors.iter().any(|anchor| region.contains(*anchor))
}

fn spec_contact(region: &BTreeSet<String>, spec: &RustVerificationSpec) -> bool {
    let mut features = text_features(&spec.claim);
    features.extend(text_features(&spec.test_filter));
    features.extend(text_features(&spec.identity));
    features.extend(text_features(&spec.package));
    features.extend(text_features("exact Rust execution code compiler test"));
    !features.is_disjoint(region)
}

fn dialogue_local_surfaces(text: &str) -> Vec<String> {
    let mut surfaces = Vec::new();
    let mut start = 0usize;
    for (at, character) in text.char_indices() {
        let boundary = matches!(character, '.' | '?' | '!' | '\n');
        if !boundary {
            continue;
        }
        let end = at + character.len_utf8();
        let surface = text[start..end].trim();
        if lexical_tokens(surface).len() >= 3 {
            surfaces.push(surface.to_owned());
        }
        start = end;
    }
    let tail = text[start..].trim();
    if lexical_tokens(tail).len() >= 3 {
        surfaces.push(tail.to_owned());
    }
    if surfaces.is_empty() && lexical_tokens(text).len() >= 3 {
        surfaces.push(text.trim().to_owned());
    }
    surfaces
}

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}
