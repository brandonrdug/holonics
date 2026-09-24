//! Equality evidence for the phase-15 consolidation of the extracted operator (plan
//! `THE_HOLON_CORE_FOUNDS_THE_NATIVE_MACHINERY.md`, "Phase 15 disposition").
//!
//! Every fixture below runs on the device and reduces what it returned — emissions, traces,
//! deposits, adjoint testimony and rests — to one canonical JSON reading whose digest was recorded
//! on the tree before the consolidation (4dff57c8). The consolidated ladder must return the same
//! numbers: the digests are compared, not re-recorded. `P15_GOLDEN_DIR` writes the readings.

use std::collections::BTreeMap;

use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use super::*;
use crate::{
    embedding_fiber::ResidentReadout,
    resident_section::{ResidentGrain, ResidentSectionRest},
};

fn scrub(value: &mut Value, drop: &[&str]) {
    match value {
        Value::Object(map) => {
            for key in drop {
                map.remove(*key);
            }
            for inner in map.values_mut() {
                scrub(inner, drop);
            }
        }
        Value::Array(items) => {
            for inner in items {
                scrub(inner, drop);
            }
        }
        _ => {}
    }
}

/// The canonical reading (sorted keys) and its digest; wall-clock time never enters.
fn check(name: &str, mut value: Value, drop: &[&str], expected: &str) {
    let mut dropped = vec!["elapsed_milliseconds"];
    dropped.extend_from_slice(drop);
    scrub(&mut value, &dropped);
    let text = serde_json::to_string(&value).expect("canonical reading");
    let digest = format!("{:x}", Sha256::digest(text.as_bytes()));
    if let Ok(directory) = std::env::var("P15_GOLDEN_DIR") {
        std::fs::create_dir_all(&directory).expect("golden directory");
        std::fs::write(format!("{directory}/{name}.json"), &text).expect("golden reading");
        std::fs::write(format!("{directory}/{name}.sha256"), &digest).expect("golden digest");
    }
    eprintln!("{name} {digest}");
    if !expected.is_empty() {
        assert_eq!(
            digest, expected,
            "{name}: the consolidated ladder changed a returned number"
        );
    }
}

fn section(rest: &ResidentSectionRest) -> Value {
    json!({
        "rows": rest.rows, "width": rest.width, "grain": rest.grain.0,
        "bound": rest.bound_octaves, "intervals": rest.intervals,
    })
}

fn sections(map: &BTreeMap<NativeCarrierOrdinal, ResidentSectionRest>) -> Value {
    Value::Object(
        map.iter()
            .map(|(at, rest)| (at.0.to_string(), section(rest)))
            .collect(),
    )
}

fn tiled(rest: &Option<NativeTiledRest>) -> Value {
    rest.as_ref().map_or(Value::Null, |tiled| {
        json!({
            "carrier": tiled.carrier.0, "rows": tiled.rows, "width": tiled.width,
            "grain": tiled.grain, "sections": tiled.sections.iter().map(section).collect::<Vec<_>>(),
        })
    })
}

fn overlays(map: &BTreeMap<NativeTensorOrdinal, Vec<NativeOverlayRest>>) -> Value {
    Value::Object(
        map.iter()
            .map(|(population, atoms)| {
                let atoms = atoms
                    .iter()
                    .map(|atom| {
                        json!({
                            "rows": atom.rows, "width": atom.width, "rank": atom.rank,
                            "u": atom.u, "v": atom.v, "u_exponent": atom.u_exponent,
                            "v_exponent": atom.v_exponent, "u_octaves": atom.u_octaves,
                            "v_octaves": atom.v_octaves,
                        })
                    })
                    .collect::<Vec<_>>();
                (population.0.to_string(), Value::Array(atoms))
            })
            .collect(),
    )
}

/// The rest as a reading. `retired` omits the previous-cycle return material the consolidation
/// no longer retains across a cycle boundary (it is recomputed from the contemporary constitution).
fn rest_reading(rest: &ExtractedOperatorRest, retired: bool) -> Value {
    let mut bytes = Vec::new();
    rest.write_to(&mut bytes).expect("rest wire");
    let mut value = json!({
        "header": serde_json::to_value(&rest.header).expect("header"),
        "carriers": sections(&rest.carriers),
        "terminal_carrier": tiled(&rest.terminal_carrier),
        // Only a dissection held the tied row, and a dissection never rests.
        "terminal_contracted": Value::Null,
        "overlay": overlays(&rest.overlay),
        "passage": rest.passage.as_ref().map(|passage| json!({
            "aperture": passage.aperture,
            "pending": overlays(&passage.pending),
            "returns": passage.returns,
        })),
        "reuse": rest.reuse.as_ref().map(|reuse| json!({
            "census": reuse.census,
            "numerical": reuse.numerical.iter().map(|(at, n)| (at.0, n.clone())).collect::<Vec<_>>(),
            "standing": sections(&reuse.standing),
        })),
    });
    if !retired {
        // The recorded rests of these charts held no reacted or presented terminal carrier; the
        // one rest has no such field (its wire declares the positions absent).
        let object = value.as_object_mut().expect("object");
        object.insert("checkpoints".into(), sections(&rest.checkpoints));
        object.insert("terminal_reacted".into(), Value::Null);
        object.insert("terminal_presented".into(), Value::Null);
        object.insert(
            "wire_sha256".into(),
            Value::String(format!("{:x}", Sha256::digest(&bytes))),
        );
    }
    value
}

/// A layered graph with an additive junction, a causal contact over the occurrence rows, a column
/// selection and the tiled terminal boundary: every primitive family the cultivation, return and
/// dissection paths cross.
fn extraction_chart() -> NativeFullOperatorEcology {
    use NativeOperationPrimitive as P;
    use NativeScaleConstraint as S;
    let node = |at: u32, primitive, inputs: &[u32], coefficients: &[u32]| NativeOperatorNode {
        ordinal: at,
        layer: (at < 6).then_some(0),
        primitive,
        inputs: inputs.iter().copied().map(NativeCarrierOrdinal).collect(),
        output: NativeCarrierOrdinal(at),
        coefficients: coefficients
            .iter()
            .copied()
            .map(NativeTensorOrdinal)
            .collect(),
    };
    let unit = || S::Rational {
        numerator: 1,
        denominator: 1,
    };
    let contact = P::CausalContact {
        heads: 1,
        kv_heads: 1,
        head_width: 2,
        reach: NativeCausalReach::Window(4),
        series_terms: 14,
    };
    NativeFullOperatorEcology {
        schema: NATIVE_FULL_OPERATOR_ECOLOGY_SCHEMA.into(),
        shared_carrier_extent: 2,
        coefficient_populations: [vec![3, 2], vec![3, 2], vec![2, 3], vec![4, 1]]
            .into_iter()
            .enumerate()
            .map(|(at, shape)| NativeCoefficientPopulation {
                ordinal: NativeTensorOrdinal(at as u32),
                coefficient_population: shape.iter().product::<usize>() as u64,
                shape,
            })
            .collect(),
        carriers: [2, 3, 2, 2, 2, 1, 4, 4, 4, 4, 4]
            .into_iter()
            .enumerate()
            .map(|(at, width)| NativeCarrierChart {
                ordinal: NativeCarrierOrdinal(at as u32),
                axes: vec![
                    NativeCarrierAxis::Occurrence,
                    NativeCarrierAxis::Fixed(width),
                ],
            })
            .collect(),
        operations: vec![
            node(
                0,
                P::Lookup {
                    scale: S::Bfloat16NearestSquareRootOf(1),
                },
                &[],
                &[0],
            ),
            node(1, P::Contract, &[0], &[1]),
            node(2, P::Contract, &[1], &[2]),
            node(3, P::Add, &[0, 2], &[]),
            node(4, contact, &[3, 3, 3], &[]),
            node(5, P::Select { axis: 1, at: 0 }, &[4], &[]),
            node(6, P::Contract, &[5], &[3]),
            node(7, P::Scale { by: unit() }, &[6], &[]),
            node(8, P::Tanh, &[7], &[]),
            node(9, P::Scale { by: unit() }, &[8], &[]),
            node(10, P::Emit, &[9], &[]),
        ],
        layers: vec![NativeLayerTopology {
            ordinal: 0,
            attention: NativeAttentionTopology::Local,
            kv_standing: NativeKvStanding::Own,
            first_operation: 0,
            operation_population: 6,
        }],
        coefficient_obstructions: vec![],
    }
}

/// Coefficients `1, 1/2, -1, 1/4` repeating, as bfloat16 words.
struct Intake(Vec<usize>);

impl NativeCoefficientIntake for Intake {
    fn populations(&self) -> usize {
        self.0.len()
    }
    fn population_octets(&self, ordinal: usize) -> Result<u64, NativeOperatorResidenceError> {
        Ok(self.0[ordinal] as u64 * 2)
    }
    fn deliver(
        &mut self,
        ordinal: usize,
        sink: &mut dyn FnMut(usize, &[u8]) -> Result<(), NativeOperatorResidenceError>,
    ) -> Result<(), NativeOperatorResidenceError> {
        let words = [0x3f80u16, 0x3f00, 0xbf80, 0x3e80];
        let bytes: Vec<u8> = (0..self.0[ordinal])
            .flat_map(|at| words[(at + ordinal) % 4].to_le_bytes())
            .collect();
        sink(0, &bytes)
    }
}

fn intake(ecology: &NativeFullOperatorEcology) -> Intake {
    Intake(
        ecology
            .coefficient_populations
            .iter()
            .map(|p| p.coefficient_population as usize)
            .collect(),
    )
}

fn cycle_reading(output: &ExtractedCycleOutput) -> Value {
    json!({
        "final_emission": output.final_emission,
        "traces": output.traces,
        "passage_returns": output.passage_returns,
    })
}

/// The fixture's shared device apparatus.
fn mounted<'chart>(
    surface: &'chart crate::resident_section::ResidentSurface<'chart>,
    ecology: &NativeFullOperatorEcology,
) -> NativeOperatorResidence<'chart> {
    NativeOperatorResidence::mount_from_intake(surface, ecology, &mut intake(ecology)).unwrap()
}

#[test]
#[ignore = "requires CUDA; phase-15 equality over the cycle, the operation ladder and the rest"]
fn extracted_operator_cycles_and_rests_return_the_recorded_numbers() {
    let ecology = extraction_chart();
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = mount_operator_surface(&readout).unwrap();
    let mut residence = mounted(&surface, &ecology);
    // The plain cycle, its rest, and the continuing cycle after remount.
    let mut readings = Vec::new();
    {
        let mut session = ExtractedOperatorSession::found(&ecology, &mut residence).unwrap();
        readings.push(cycle_reading(
            &session.advance_cycle_retained(&[0]).unwrap(),
        ));
        readings.push(cycle_reading(
            &session.advance_cycle_retained(&[0, 1]).unwrap(),
        ));
        let rest = session.detach_rest().unwrap();
        readings.push(rest_reading(&rest, false));
        let mut bytes = Vec::new();
        rest.write_to(&mut bytes).unwrap();
        drop(session);
        let decoded =
            ExtractedOperatorRest::read_from(&mut &bytes[..], bytes.len() as u64).unwrap();
        let mut resumed =
            ExtractedOperatorSession::remount_rest(&ecology, &mut residence, &decoded).unwrap();
        readings.push(cycle_reading(
            &resumed.advance_cycle_retained(&[1, 2]).unwrap(),
        ));
        readings.push(json!(resumed.carrier_population()));
    }
    check(
        "plain_cycle",
        Value::Array(readings),
        &[],
        "acdaff487a90e78f2f58a49b548538bb59a0ae5aa512639dc617dd8c1f4f6dd6",
    );
}

#[test]
#[ignore = "requires CUDA; phase-15 equality over the single-operation ladder and the terminal branch"]
fn extracted_operator_single_operation_ladder_returns_the_recorded_numbers() {
    let ecology = extraction_chart();
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = mount_operator_surface(&readout).unwrap();
    let mut residence = mounted(&surface, &ecology);
    let mut readings = Vec::new();
    let mut session = ExtractedOperatorSession::found(&ecology, &mut residence).unwrap();
    for rows in [vec![0u32, 1], vec![2, 0, 1]] {
        for at in 0..6u32 {
            let occurrence = if at == 0 {
                ExtractedOperatorOccurrence::addressed(session.generation(), rows.clone())
            } else {
                ExtractedOperatorOccurrence::internal(session.generation())
            };
            assert!(session.accepts_occurrence(&occurrence));
            // Through the advance facet: the one step every executor returns.
            let step = session.advance_occurrence(occurrence).unwrap();
            readings.push(json!({"emission": step.emission, "trace": step.trace}));
            session = step.successor;
        }
        let ordinal = session.generation();
        assert!(
            !session.accepts_occurrence(&ExtractedOperatorOccurrence::entered(ordinal, vec![1]))
        );
        let branch = session
            .advance_terminal(ExtractedOperatorOccurrence::internal(ordinal))
            .unwrap();
        let carrier = branch.emissions.last().unwrap().carrier;
        readings.push(json!({"emissions": branch.emissions, "traces": branch.traces}));
        session = branch.successor;
        readings.push(json!({
            "face": session.carrier_intervals(carrier).unwrap(),
            "held": session.carrier_population(),
            "chronology": ExtractedOperatorAdvance::chronology(&session),
            "complete": session.cycle_complete(),
        }));
    }
    check(
        "operation_ladder",
        Value::Array(readings),
        &[],
        "12782b382f96e41ea0514277a38fab415c25cfdb4826fc3f972973b1071bc7c8",
    );
}

const CONTINUING_RETURN_REST: &[u8] = include_bytes!("fixtures/phase15_continuing_return_rest.bin");

/// The last three continuing cycles, their ranks and the final rest.
fn continue_from(
    ecology: &NativeFullOperatorEcology,
    residence: &mut NativeOperatorResidence<'_>,
    rest: &ExtractedOperatorRest,
) -> Vec<Value> {
    let mut readings = Vec::new();
    let mut resumed = ExtractedOperatorSession::remount_rest(ecology, residence, rest).unwrap();
    for rows in [vec![0u32, 1, 2], vec![2], vec![2, 0]] {
        readings.push(cycle_reading(
            &resumed.advance_cycle_retained(&rows).unwrap(),
        ));
        readings.push(json!(resumed.morphology_overlay_rank()));
    }
    readings.push(rest_reading(&resumed.detach_rest().unwrap(), true));
    readings
}

#[test]
#[ignore = "requires CUDA; phase-15 equality of the continuing return, across a rest"]
fn extracted_operator_continuing_return_returns_the_recorded_numbers() {
    let ecology = extraction_chart();
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = mount_operator_surface(&readout).unwrap();
    let mut residence = mounted(&surface, &ecology);
    let aperture = NativeReturnAperture {
        learning_shift: 2,
        series_terms: 14,
    };
    let mut readings = Vec::new();
    let mut bytes = Vec::new();
    {
        let mut session =
            ExtractedOperatorSession::found_with_return(&ecology, &mut residence, aperture)
                .unwrap();
        for rows in [vec![0u32], vec![0, 1]] {
            readings.push(cycle_reading(
                &session.advance_cycle_retained(&rows).unwrap(),
            ));
            readings.push(json!(session.morphology_overlay_rank()));
        }
        let rest = session.detach_rest().unwrap();
        // Retention law: the cycle boundary holds the occurrence, never the last cycle's cut.
        assert!(rest.checkpoints.is_empty());
        readings.push(rest_reading(&rest, true));
        rest.write_to(&mut bytes).unwrap();
    }
    assert!(
        bytes.len() < CONTINUING_RETURN_REST.len(),
        "the retired terminal material is gone"
    );
    let decoded = ExtractedOperatorRest::read_from(&mut &bytes[..], bytes.len() as u64).unwrap();
    let tail = continue_from(&ecology, &mut residence, &decoded);
    readings.extend(tail.iter().cloned());
    // The census of a continuing return measures its apparatus, which the consolidation changes
    // (the return reads the contemporary constitution instead of a retained terminal cut).
    let census = ["census_before", "census_after"];
    check(
        "continuing_return_tail",
        Value::Array(tail),
        &census,
        "9ba14d0c3d55e1ce3de86841af0f8bea2c109750269aa18e2637f96fdcace957",
    );
    check(
        "continuing_return",
        Value::Array(readings),
        &census,
        "faefec41a396e159bb7a69fdba63d1223e9c7802b6c9b387cf3927a1559fa327",
    );
    // The rest recorded before the consolidation still carries the previous cycle's reacted and
    // presented carriers and checkpoints: it decodes, they are released, and the continuing
    // return reads the contemporary constitution to the same deposits and faces.
    let legacy = ExtractedOperatorRest::read_from(
        &mut &CONTINUING_RETURN_REST[..],
        CONTINUING_RETURN_REST.len() as u64,
    )
    .unwrap();
    assert_eq!(legacy.header, decoded.header);
    assert_eq!(legacy.overlay, decoded.overlay);
    check(
        "continuing_return_tail",
        Value::Array(continue_from(&ecology, &mut residence, &legacy)),
        &census,
        "9ba14d0c3d55e1ce3de86841af0f8bea2c109750269aa18e2637f96fdcace957",
    );
}

#[test]
#[ignore = "requires CUDA; phase-15 equality of the joined-passage cultivation and its rest"]
fn extracted_operator_passage_cultivation_returns_the_recorded_numbers() {
    let ecology = extraction_chart();
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = mount_operator_surface(&readout).unwrap();
    let mut residence = mounted(&surface, &ecology);
    let aperture = NativeReturnAperture {
        learning_shift: 2,
        series_terms: 14,
    };
    let mut readings = Vec::new();
    let mut session =
        ExtractedOperatorSession::found_with_passage_return(&ecology, &mut residence, aperture)
            .unwrap();
    readings.push(json!(session.joined_passage_population()));
    for rows in [vec![0u32, 1], vec![0, 1], vec![1]] {
        readings.push(cycle_reading(
            &session.advance_cycle_retained(&rows).unwrap(),
        ));
        readings.push(json!(session.forward_reuse_census()));
    }
    readings.push(cycle_reading(
        &session
            .observe_passage_readout_retained(&[0, 1], NativeEmissionReadout::LastRow)
            .unwrap(),
    ));
    let rest = session.detach_rest().unwrap();
    readings.push(rest_reading(&rest, false));
    drop(session);
    let mut resumed =
        ExtractedOperatorSession::remount_rest(&ecology, &mut residence, &rest).unwrap();
    readings.push(cycle_reading(
        &resumed.advance_cycle_retained(&[1, 0]).unwrap(),
    ));
    check(
        "passage_cultivation",
        Value::Array(readings),
        &[],
        "12162e2f05fec083b91a2e17022bf7899423a0548c674836912803fcfeca89e3",
    );
}

#[test]
#[ignore = "requires CUDA; phase-15 equality of the dissection receiver"]
fn extracted_operator_dissection_returns_the_recorded_numbers() {
    let ecology = extraction_chart();
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = mount_operator_surface(&readout).unwrap();
    let mut residence = mounted(&surface, &ecology);
    let mut readings = Vec::new();
    let mut session = ExtractedOperatorSession::found_for_dissection(
        &ecology,
        &mut residence,
        NativeDissectionAperture { series_terms: 14 },
    )
    .unwrap();
    readings.push(cycle_reading(
        &session.advance_cycle_retained(&[0, 1]).unwrap(),
    ));
    readings.push(json!(session.read_face().unwrap()));
    readings.push(json!(session.excite().unwrap()));
    readings.push(json!(
        session
            .site_contributions()
            .into_iter()
            .map(|(population, contributions)| (population.0, contributions))
            .collect::<Vec<_>>()
    ));
    readings.push(json!(
        session
            .face_under_withdrawal(NativeTensorOrdinal(1), &[true, false, false])
            .unwrap()
    ));
    readings.push(json!(
        session
            .face_under_withdrawal(NativeTensorOrdinal(3), &[false, true, false, false])
            .unwrap()
    ));
    check(
        "dissection",
        Value::Array(readings),
        &[],
        "86dae268eb6039719e3a5aa6f4f576557ae87666b4caac8d60fecb84c828c7fb",
    );
}

fn recurrent_morphology() -> NativeOperatorMorphology {
    let coefficient = |word: u16| NativeDyadicCoefficient::from_bfloat16(word).unwrap();
    let matrix = |address: &str, rows: usize, columns: usize, words: &[u16]| NativeDyadicMatrix {
        address: address.into(),
        rows,
        columns,
        coefficients: (0..rows * columns)
            .map(|at| coefficient(words[at % words.len()]))
            .collect(),
    };
    NativeOperatorMorphology {
        schema: NATIVE_OPERATOR_MORPHOLOGY_SCHEMA.into(),
        carrier_extent: 4,
        interaction_extent: 2,
        matrices: vec![
            matrix(
                "operator/input-cross-section",
                2,
                4,
                &[0x3f80, 0xbf00, 0x3e80, 0x3f00, 0xbe80],
            ),
            matrix(
                "operator/output-cross-section",
                4,
                2,
                &[0x3f00, 0x3f80, 0xbf80, 0x3e80, 0x3fc0],
            ),
        ],
        norm_gain: [0x3f80u16, 0x3f00, 0x3fc0, 0x4000]
            .into_iter()
            .map(coefficient)
            .collect(),
        operations: vec![
            NativeOperatorKind::Contract {
                matrix: "operator/input-cross-section".into(),
            },
            NativeOperatorKind::GeluTanh,
            NativeOperatorKind::HadamardOccurrence,
            NativeOperatorKind::Contract {
                matrix: "operator/output-cross-section".into(),
            },
            NativeOperatorKind::RmsNorm {
                gain_population: 4,
                epsilon: relational_geometry::Rat::new(1.into(), 1_000_000.into()),
            },
            NativeOperatorKind::Reentry,
        ],
        open_exterior: vec![],
    }
}

/// The branch rest as the neutral reading recorded from its legacy wire: the operation position,
/// the chronology, the current carrier and the retained re-entry carrier.
fn recurrent_rest(rest: &ExtractedOperatorRest) -> Value {
    let header = &rest.header;
    let current = if header.generation == 0 {
        NativeCarrierOrdinal(0)
    } else {
        NativeCarrierOrdinal(2 + ((header.operation_at + 5) % 6) as u32)
    };
    let reentry = (current.0 != 0)
        .then(|| rest.carriers.get(&NativeCarrierOrdinal(0)).map(section))
        .flatten();
    json!({
        "operation_at": header.operation_at,
        "generation": header.generation,
        "chronology": header.chronology,
        "carrier": section(&rest.carriers[&current]),
        "reentry": reentry,
    })
}

/// The branch emission as recorded: its chart carrier is the output of its operation, `c(k+2)`.
fn branch_emission(emission: &ExtractedOperatorEmission<NativeOperatorKind>, at: usize) -> Value {
    assert_eq!(emission.carrier, NativeCarrierOrdinal(at as u32 + 2));
    let mut value = serde_json::to_value(emission).unwrap();
    value.as_object_mut().unwrap().remove("carrier");
    value
}

fn branch_reading(branch: &ExtractedOperatorBranch<ExtractedBranchSession<'_, '_, '_>>) -> Value {
    json!({
        "emissions": branch.emissions.iter().enumerate()
            .map(|(at, emission)| branch_emission(emission, at)).collect::<Vec<_>>(),
        "traces": branch.traces,
    })
}

fn rest_roundtrip(rest: &ExtractedOperatorRest) -> ExtractedOperatorRest {
    let mut bytes = Vec::new();
    rest.write_to(&mut bytes).unwrap();
    ExtractedOperatorRest::read_from(&mut &bytes[..], bytes.len() as u64).unwrap()
}

const BRANCH_REST: &[u8] = include_bytes!("fixtures/phase15_branch_rest.json");

#[test]
#[ignore = "requires CUDA; phase-15 equality of the host-entered per-layer operator chart"]
fn extracted_branch_chart_returns_the_recorded_numbers() {
    let morphology = recurrent_morphology();
    let chart = morphology.constitution_chart().unwrap();
    chart.validate().unwrap();
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = mount_operator_surface(&readout).unwrap();
    let resident = ResidentOperatorMorphology::mount(&surface, &morphology).unwrap();
    let carrier = [0x3f80u16, 0xbf00, 0x3e80, 0x4000];
    let grain = resident.finest_initial_grain(&carrier).unwrap();
    let mut readings = vec![
        json!(grain.0),
        json!(resident.resident_coefficient_octets()),
    ];
    let session = resident.mount_initial(&carrier, grain).unwrap();
    let branch = session.advance_branch(&[0x3f00, 0xbf80]).unwrap();
    readings.push(branch_reading(&branch));
    let rest = rest_roundtrip(&branch.successor.rest().unwrap());
    assert_eq!(
        rest.header.ecology, chart,
        "the branch rests on its constitution chart"
    );
    readings.push(recurrent_rest(&rest));
    let session = resident.remount_session(&rest).unwrap();
    let branch = session.advance_branch(&[0x3fc0, 0x3e00]).unwrap();
    readings.push(branch_reading(&branch));
    // A rest inside the branch carries the retained re-entry carrier.
    let mut session = resident
        .mount_initial(&carrier, ResidentGrain(grain.0))
        .unwrap();
    for at in 0..3 {
        let ordinal = session.generation();
        let occurrence = if at == 2 {
            ExtractedOperatorOccurrence::entered(ordinal, vec![0x3f00, 0xbf80])
        } else {
            ExtractedOperatorOccurrence::internal(ordinal)
        };
        let step = session.advance_occurrence(occurrence).unwrap();
        readings
            .push(json!({"emission": branch_emission(&step.emission, at), "trace": step.trace}));
        session = step.successor;
    }
    let rest = rest_roundtrip(&session.rest().unwrap());
    readings.push(recurrent_rest(&rest));
    // The recorded legacy wire of this same rest decodes to the same one rest.
    assert_eq!(resident.read_legacy_rest(BRANCH_REST).unwrap(), rest);
    let run_tail = |rest: &ExtractedOperatorRest| {
        let mut tail = Vec::new();
        let mut session = resident.remount_session(rest).unwrap();
        for at in 3..6 {
            let ordinal = session.generation();
            let step = session
                .advance(ExtractedOperatorOccurrence::internal(ordinal))
                .unwrap();
            tail.push(
                json!({"emission": branch_emission(&step.emission, at), "trace": step.trace}),
            );
            session = step.successor;
        }
        tail.push(json!({"chronology": session.chronology(), "at": session.operation_at()}));
        tail
    };
    let tail = run_tail(&rest);
    readings.extend(tail.iter().cloned());
    check(
        "branch_chart_tail",
        Value::Array(tail.clone()),
        &[],
        "079f5c14bdee3c440d07a4c83480804d03b9dee734e67a6672c5c4ae07e45a5d",
    );
    // The legacy wire's continuation returns the same numbers; the surface's census is
    // cumulative over this test, so only it differs from the first continuation.
    let mut legacy_tail = Value::Array(run_tail(&resident.read_legacy_rest(BRANCH_REST).unwrap()));
    let mut first_tail = Value::Array(tail.clone());
    for value in [&mut legacy_tail, &mut first_tail] {
        scrub(value, &["census_before", "census_after"]);
    }
    assert_eq!(legacy_tail, first_tail);
    check(
        "branch_chart",
        Value::Array(readings),
        &[],
        "9467616be0e538461f831511b63771b7e5d7c096b36ef3f6626ae6b8dad130bc",
    );
    // An addressed occurrence is not the branch's port.
    let session = resident.mount_initial(&carrier, grain).unwrap();
    assert!(matches!(
        session.advance(ExtractedOperatorOccurrence::addressed(0, vec![1])),
        Err(ExtractedOperatorRefusal::Occurrence)
    ));
}
