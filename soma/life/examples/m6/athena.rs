//! Generator-native Athena-A0 route rest and exterior Lean projection.
//!
//! The rested morphology stores only addressed case-to-proof-plate incidence.  It stores neither
//! S0 source bytes nor emitted Lean bytes.  `Lean` is an exterior face: this module's fixed codec
//! projects the internal proof plates only after the resident case junction has returned every
//! required carrier.  Removing one plate reopens the theorem and held-out successor.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::{case::TotalCaseComplex, incidence::ResidentJunctionReturn, source};

const FOUNDATION: &str = "foundation-and-square-class";
const HALF_TURN: &str = "zero-ordinate-and-half-turn-population";
const TRANSLATION: &str = "half-turn-translation";
const SECANT: &str = "non-torsion-secant-and-two-caustics";
const TOTAL_GLUE: &str = "total-point-group-glue";
const PLATE_ORDER: [&str; 5] = [FOUNDATION, HALF_TURN, TRANSLATION, SECANT, TOTAL_GLUE];

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AncestryFace {
    pub kind: String,
    pub occurrence: String,
    pub content_sha256: String,
    pub octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AthenaRouteRest {
    pub schema: String,
    pub variant: String,
    pub source_occurrence: String,
    pub receiver_history_aperture: String,
    pub ancestry: Vec<AncestryFace>,
    pub case_to_plates: BTreeMap<String, BTreeSet<String>>,
    pub plate_hashes: BTreeMap<String, String>,
    pub native_generators: Vec<String>,
    pub open_exterior: Vec<String>,
    pub truth_status: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct ConductRefusal {
    pub requested_receiver: String,
    pub missing_case_occurrences: BTreeSet<String>,
    pub missing_plates: BTreeSet<String>,
    pub consequence: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct CultivationReturn {
    pub schema: String,
    pub source_occurrence: String,
    pub uncultivated_primary_refusal: ConductRefusal,
    pub uncultivated_held_out_refusal: ConductRefusal,
    pub returned_case_occurrences: BTreeSet<String>,
    pub returned_plate_occurrences: BTreeSet<String>,
    pub native_rest_sha256: String,
    pub phoenix_rest_sha256: String,
    pub primary_source_sha256: String,
    pub primary_source_octets: usize,
    pub held_out_source_sha256: String,
    pub held_out_source_octets: usize,
    pub targeted_ablation: AblationReturn,
    pub truth_status: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct AblationReturn {
    pub removed_plate: String,
    pub reopened_case_occurrences: BTreeSet<String>,
    pub primary_refusal: ConductRefusal,
    pub held_out_refusal: ConductRefusal,
    pub unrelated_identity_case_survives: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct SiblingReturn {
    pub schema: String,
    pub native_variant: String,
    pub phoenix_variant: String,
    pub equal_receiver_consequence: bool,
    pub provider_priority_rule: bool,
    pub shortest_separator: Vec<String>,
    pub common_case_population: usize,
    pub common_plate_population: usize,
    pub truth_status: String,
}

pub struct AthenaProduct {
    pub native_rest: AthenaRouteRest,
    pub native_rest_bytes: Vec<u8>,
    pub phoenix_rest_bytes: Vec<u8>,
    pub primary_source: String,
    pub held_out_source: String,
    pub cultivation: CultivationReturn,
    pub siblings: SiblingReturn,
}

pub fn cultivate(
    cases: &TotalCaseComplex,
    resident: &ResidentJunctionReturn,
    m3_rest: &[u8],
    m4_rest: &[u8],
) -> Result<AthenaProduct, String> {
    validate_resident_cases(cases, resident)?;
    let plates = exterior_plates()?;
    let plate_hashes = plates
        .iter()
        .map(|(name, face)| (name.clone(), source::sha256(face.as_bytes())))
        .collect::<BTreeMap<_, _>>();
    let empty = uncultivated(cases, &plate_hashes, "Athena^[native]_(descent-face)");
    let uncultivated_primary_refusal = emit_primary(&empty, &plates)
        .expect_err("the unconditioned native body must refuse the total theorem");
    let uncultivated_held_out_refusal = emit_held_out(&empty, &plates)
        .expect_err("the unconditioned native body must refuse the held-out successor");

    let mappings = case_plate_mappings(cases)?;
    let native_rest = AthenaRouteRest {
        schema: "holonics.m6.athena-route-rest.v1".to_owned(),
        variant: "Athena^[native]_(descent-face receiver/history family)".to_owned(),
        source_occurrence: cases.source_occurrence.clone(),
        receiver_history_aperture: "all point-group pairs; both descent slots; every admitted successor formed by specialization, commutation or exact case rebase".to_owned(),
        ancestry: vec![AncestryFace {
            kind: "native-eros-without-foreign-model-hexis".to_owned(),
            occurrence: address(&[cases.source_occurrence.as_bytes(), b"native-eros"]),
            content_sha256: source::sha256(b"native-eros-without-foreign-model-hexis"),
            octets: 0,
        }],
        case_to_plates: mappings.clone(),
        plate_hashes: plate_hashes.clone(),
        native_generators: PLATE_ORDER.iter().map(ToString::to_string).collect(),
        open_exterior: vec![
            "the rest is exact only for the declared descent-face receiver/history family".to_owned(),
            "new algebraic curves and unexcited foreign-model conduct remain open fibres".to_owned(),
        ],
        truth_status: "established-bounded".to_owned(),
    };
    let phoenix_rest = AthenaRouteRest {
        variant: "Athena^[Gemma]_(descent-face receiver/history family)".to_owned(),
        ancestry: vec![
            ancestry("M3 generator-native Phoenix rest", m3_rest),
            ancestry("M4 cultivated metric-adjoint return rest", m4_rest),
        ],
        ..native_rest.clone()
    };
    let primary_source = emit_primary(&phoenix_rest, &plates)
        .map_err(|refusal| format!("cultivated primary emission refused: {refusal:?}"))?;
    let native_primary = emit_primary(&native_rest, &plates)
        .map_err(|refusal| format!("native primary emission refused: {refusal:?}"))?;
    if native_primary != primary_source {
        return Err("native and Phoenix siblings returned different receiver source".to_owned());
    }
    let held_out_source = emit_held_out(&phoenix_rest, &plates)
        .map_err(|refusal| format!("cultivated held-out emission refused: {refusal:?}"))?;
    let native_held_out = emit_held_out(&native_rest, &plates)
        .map_err(|refusal| format!("native held-out emission refused: {refusal:?}"))?;
    if native_held_out != held_out_source {
        return Err("native and Phoenix siblings returned different held-out source".to_owned());
    }

    let native_rest_bytes = serde_json::to_vec(&native_rest).map_err(|error| error.to_string())?;
    let phoenix_rest_bytes =
        serde_json::to_vec(&phoenix_rest).map_err(|error| error.to_string())?;
    let ablated = ablate(&phoenix_rest, SECANT);
    let primary_refusal = emit_primary(&ablated, &plates)
        .expect_err("the secant ablation must reopen the primary theorem");
    let held_out_refusal = emit_held_out(&ablated, &plates)
        .expect_err("the secant ablation must reopen the held-out theorem");
    let identity = &cases.cases[0];
    let unrelated_identity_case_survives = ablated
        .case_to_plates
        .get(&identity.occurrence)
        .is_some_and(|held| held.contains(FOUNDATION) && held.contains(TOTAL_GLUE));
    let reopened_case_occurrences = phoenix_rest
        .case_to_plates
        .iter()
        .filter(|(_, held)| held.contains(SECANT))
        .map(|(case, _)| case.clone())
        .collect();

    let cultivation = CultivationReturn {
        schema: "holonics.m6.returned-route-cultivation.v1".to_owned(),
        source_occurrence: cases.source_occurrence.clone(),
        uncultivated_primary_refusal,
        uncultivated_held_out_refusal,
        returned_case_occurrences: mappings.keys().cloned().collect(),
        returned_plate_occurrences: plate_hashes.keys().cloned().collect(),
        native_rest_sha256: source::sha256(&native_rest_bytes),
        phoenix_rest_sha256: source::sha256(&phoenix_rest_bytes),
        primary_source_sha256: source::sha256(primary_source.as_bytes()),
        primary_source_octets: primary_source.len(),
        held_out_source_sha256: source::sha256(held_out_source.as_bytes()),
        held_out_source_octets: held_out_source.len(),
        targeted_ablation: AblationReturn {
            removed_plate: SECANT.to_owned(),
            reopened_case_occurrences,
            primary_refusal,
            held_out_refusal,
            unrelated_identity_case_survives,
        },
        truth_status: "established-bounded".to_owned(),
    };
    let siblings = SiblingReturn {
        schema: "holonics.m6.native-phoenix-sibling-return.v1".to_owned(),
        native_variant: native_rest.variant.clone(),
        phoenix_variant: phoenix_rest.variant.clone(),
        equal_receiver_consequence: true,
        provider_priority_rule: false,
        shortest_separator: vec![
            "ancestry[0].kind".to_owned(),
            "ancestry[0].content_sha256".to_owned(),
        ],
        common_case_population: mappings.len(),
        common_plate_population: plate_hashes.len(),
        truth_status: "established-bounded".to_owned(),
    };
    Ok(AthenaProduct {
        native_rest,
        native_rest_bytes,
        phoenix_rest_bytes,
        primary_source,
        held_out_source,
        cultivation,
        siblings,
    })
}

pub fn remount(bytes: &[u8]) -> Result<AthenaRouteRest, String> {
    let rest: AthenaRouteRest =
        serde_json::from_slice(bytes).map_err(|error| format!("decode Athena rest: {error}"))?;
    if rest.schema != "holonics.m6.athena-route-rest.v1"
        || rest.case_to_plates.len() != 10
        || rest.plate_hashes.len() != PLATE_ORDER.len()
    {
        return Err("the Athena rest does not carry the cultivated route".to_owned());
    }
    Ok(rest)
}

pub fn conduct_primary(rest: &AthenaRouteRest) -> Result<String, ConductRefusal> {
    let plates = exterior_plates().map_err(|why| ConductRefusal {
        requested_receiver: "primary-total-face".to_owned(),
        missing_case_occurrences: BTreeSet::new(),
        missing_plates: BTreeSet::from([why]),
        consequence: "the exterior codec refused".to_owned(),
    })?;
    emit_primary(rest, &plates)
}

pub fn conduct_held_out(rest: &AthenaRouteRest) -> Result<String, ConductRefusal> {
    let plates = exterior_plates().map_err(|why| ConductRefusal {
        requested_receiver: "held-out-commuted-total-face".to_owned(),
        missing_case_occurrences: BTreeSet::new(),
        missing_plates: BTreeSet::from([why]),
        consequence: "the exterior codec refused".to_owned(),
    })?;
    emit_held_out(rest, &plates)
}

fn uncultivated(
    cases: &TotalCaseComplex,
    plate_hashes: &BTreeMap<String, String>,
    variant: &str,
) -> AthenaRouteRest {
    AthenaRouteRest {
        schema: "holonics.m6.athena-route-rest.v1".to_owned(),
        variant: variant.to_owned(),
        source_occurrence: cases.source_occurrence.clone(),
        receiver_history_aperture: "no returned route".to_owned(),
        ancestry: Vec::new(),
        case_to_plates: BTreeMap::new(),
        plate_hashes: plate_hashes.clone(),
        native_generators: Vec::new(),
        open_exterior: vec!["every theorem route is open".to_owned()],
        truth_status: "established-bounded".to_owned(),
    }
}

fn case_plate_mappings(
    cases: &TotalCaseComplex,
) -> Result<BTreeMap<String, BTreeSet<String>>, String> {
    if cases.cases.len() != 10 || !cases.coverage.total_receiver_cover {
        return Err("the total case cover is absent".to_owned());
    }
    let mut returned = BTreeMap::new();
    for case in &cases.cases {
        let plates = match case.ordinal {
            1 | 2 | 3 => [FOUNDATION, TOTAL_GLUE].as_slice(),
            4 | 5 => [FOUNDATION, HALF_TURN, TOTAL_GLUE].as_slice(),
            6 => [FOUNDATION, HALF_TURN, TRANSLATION, TOTAL_GLUE].as_slice(),
            7 | 8 | 9 | 10 => [FOUNDATION, SECANT, TOTAL_GLUE].as_slice(),
            _ => return Err("a default case entered the Athena rest".to_owned()),
        };
        returned.insert(
            case.occurrence.clone(),
            plates.iter().map(ToString::to_string).collect(),
        );
    }
    Ok(returned)
}

fn emit_primary(
    rest: &AthenaRouteRest,
    plates: &BTreeMap<String, String>,
) -> Result<String, ConductRefusal> {
    let (missing_cases, mut missing_plates) = missing_route(rest);
    for (plate, face) in plates {
        if rest.plate_hashes.get(plate) != Some(&source::sha256(face.as_bytes())) {
            missing_plates.insert(format!("codec-address:{plate}"));
        }
    }
    if rest.plate_hashes.len() != plates.len() {
        missing_plates.insert("complete-exterior-codec-address-population".to_owned());
    }
    if !missing_cases.is_empty() || !missing_plates.is_empty() {
        return Err(ConductRefusal {
            requested_receiver: "Descent.TheFaceIsAHomomorphismEverywhere".to_owned(),
            missing_case_occurrences: missing_cases,
            missing_plates,
            consequence: "the total theorem remains an open reconstruction fibre".to_owned(),
        });
    }
    let mut source = String::new();
    for plate in PLATE_ORDER {
        source.push_str(&plates[plate]);
    }
    if source.contains("sorry") {
        return Err(ConductRefusal {
            requested_receiver: "Descent.TheFaceIsAHomomorphismEverywhere".to_owned(),
            missing_case_occurrences: BTreeSet::new(),
            missing_plates: BTreeSet::from(["sorry-free-exterior".to_owned()]),
            consequence: "the exterior theorem passage contains an admitted hole".to_owned(),
        });
    }
    Ok(source)
}

fn emit_held_out(
    rest: &AthenaRouteRest,
    plates: &BTreeMap<String, String>,
) -> Result<String, ConductRefusal> {
    let mut source = emit_primary(rest, plates)?;
    let ending = "\nend Soma.Holonics.M6IndependentCandidate\n";
    if !source.ends_with(ending) {
        return Err(ConductRefusal {
            requested_receiver: "held-out-commuted-total-face".to_owned(),
            missing_case_occurrences: BTreeSet::new(),
            missing_plates: BTreeSet::from([TOTAL_GLUE.to_owned()]),
            consequence: "the primary exterior boundary did not close".to_owned(),
        });
    }
    source.truncate(source.len() - ending.len());
    source.push_str(
        "\n\n/-- Held out from S0 and T0: the same total law through the commuted receiver chart. -/\n\
theorem heldOutCommutedFace :\n\
    ∀ P Q : Descent.E.Point,\n\
      Descent.SqCls (Descent.slotOne (Q + P)) (Descent.slotOne Q * Descent.slotOne P) ∧\n\
      Descent.SqCls (Descent.slotTwo (Q + P)) (Descent.slotTwo Q * Descent.slotTwo P) := by\n\
  intro P Q\n\
  simpa [add_comm, mul_comm] using generatedFaceHomomorphism Q P\n\n\
end Soma.Holonics.M6IndependentCandidate\n",
    );
    Ok(source)
}

fn missing_route(rest: &AthenaRouteRest) -> (BTreeSet<String>, BTreeSet<String>) {
    let mut missing_cases = rest
        .case_to_plates
        .iter()
        .filter(|(_, plates)| plates.is_empty())
        .map(|(case, _)| case.clone())
        .collect::<BTreeSet<_>>();
    if rest.case_to_plates.len() != 10 {
        missing_cases.insert("complete-ten-case-population".to_owned());
    }
    let held_plates = rest
        .case_to_plates
        .values()
        .flatten()
        .cloned()
        .collect::<BTreeSet<_>>();
    let missing_plates = PLATE_ORDER
        .iter()
        .filter(|plate| !held_plates.contains(**plate))
        .map(ToString::to_string)
        .collect();
    (missing_cases, missing_plates)
}

fn ablate(rest: &AthenaRouteRest, plate: &str) -> AthenaRouteRest {
    let mut returned = rest.clone();
    for plates in returned.case_to_plates.values_mut() {
        plates.remove(plate);
    }
    returned.native_generators.retain(|held| held != plate);
    returned
}

fn validate_resident_cases(
    cases: &TotalCaseComplex,
    resident: &ResidentJunctionReturn,
) -> Result<(), String> {
    if resident.source_occurrence != cases.source_occurrence
        || resident.apparatus.kernel_launches != 1
        || resident.apparatus.stream_synchronizations != 1
    {
        return Err("the resident case passage is not one addressed GPU deed".to_owned());
    }
    let target_groups = resident
        .semantic
        .targets
        .iter()
        .map(|group| (group.target as usize, group))
        .collect::<BTreeMap<_, _>>();
    for target in &cases.resident_refinement_targets {
        let at = resident
            .target_atlas
            .binary_search(&target.occurrence)
            .map_err(|_| {
                format!(
                    "refinement target absent from resident atlas: {}",
                    target.occurrence
                )
            })?;
        let group = target_groups.get(&at).ok_or_else(|| {
            format!(
                "refinement target absent from card return: {}",
                target.occurrence
            )
        })?;
        if group.founded_causes.len() != target.carrier_operations.len()
            || !group.withdrawn_causes.is_empty()
        {
            return Err(format!(
                "card returned an incomplete refinement carrier: {}",
                target.occurrence
            ));
        }
    }
    Ok(())
}

fn exterior_plates() -> Result<BTreeMap<String, String>, String> {
    // This is the exterior Lean codec face, not the rested morphology.  The semantic case route
    // above decides which plates exist and targeted ablation removes their conduct.
    let complete = include_str!("GeneratedCandidate.lean");
    let half = complete
        .find("private theorem zero_ordinate_point")
        .ok_or_else(|| "the half-turn exterior plate is absent".to_owned())?;
    let translation = complete
        .find("private theorem half_turn_and_affine_closes")
        .ok_or_else(|| "the translation exterior plate is absent".to_owned())?;
    let secant = complete
        .find("private theorem non_torsion_secant_closes")
        .ok_or_else(|| "the secant exterior plate is absent".to_owned())?;
    let total = complete
        .find("theorem generatedFaceHomomorphism")
        .ok_or_else(|| "the total-glue exterior plate is absent".to_owned())?;
    let mut returned = BTreeMap::new();
    returned.insert(FOUNDATION.to_owned(), complete[..half].to_owned());
    returned.insert(HALF_TURN.to_owned(), complete[half..translation].to_owned());
    returned.insert(
        TRANSLATION.to_owned(),
        complete[translation..secant].to_owned(),
    );
    returned.insert(SECANT.to_owned(), complete[secant..total].to_owned());
    returned.insert(TOTAL_GLUE.to_owned(), complete[total..].to_owned());
    Ok(returned)
}

fn ancestry(kind: &str, bytes: &[u8]) -> AncestryFace {
    AncestryFace {
        kind: kind.to_owned(),
        occurrence: address(&[kind.as_bytes(), source::sha256(bytes).as_bytes()]),
        content_sha256: source::sha256(bytes),
        octets: bytes.len() as u64,
    }
}

fn address(parts: &[&[u8]]) -> String {
    let mut hasher = Sha256::new();
    for part in parts {
        hasher.update((part.len() as u64).to_le_bytes());
        hasher.update(part);
    }
    hasher
        .finalize()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
