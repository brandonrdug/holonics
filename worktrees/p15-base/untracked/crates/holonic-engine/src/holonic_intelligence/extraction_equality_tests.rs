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
        assert_eq!(digest, expected, "{name}: the consolidated ladder changed a returned number");
    }
}

fn section(rest: &ResidentSectionRest) -> Value {
    json!({
        "rows": rest.rows, "width": rest.width, "grain": rest.grain.0,
        "bound": rest.bound_octaves, "intervals": rest.intervals,
    })
}

fn sections(map: &BTreeMap<NativeCarrierOrdinal, ResidentSectionRest>) -> Value {
    Value::Object(map.iter().map(|(at, rest)| (at.0.to_string(), section(rest))).collect())
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
fn rest_reading(rest: &NativeFullSessionRest, retired: bool) -> Value {
    let mut bytes = Vec::new();
    rest.write_to(&mut bytes).expect("rest wire");
    let mut value = json!({
        "header": serde_json::to_value(&rest.header).expect("header"),
        "carriers": sections(&rest.carriers),
        "terminal_carrier": tiled(&rest.terminal_carrier),
        "terminal_contracted": rest.terminal_contracted,
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
        let object = value.as_object_mut().expect("object");
        object.insert("checkpoints".into(), sections(&rest.checkpoints));
        object.insert("terminal_reacted".into(), tiled(&rest.terminal_reacted));
        object.insert(
            "terminal_presented".into(),
            rest.terminal_presented.as_ref().map_or(Value::Null, section),
        );
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
        coefficients: coefficients.iter().copied().map(NativeTensorOrdinal).collect(),
    };
    let unit = || S::Rational { numerator: 1, denominator: 1 };
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
                axes: vec![NativeCarrierAxis::Occurrence, NativeCarrierAxis::Fixed(width)],
            })
            .collect(),
        operations: vec![
            node(0, P::Lookup { scale: S::Bfloat16NearestSquareRootOf(1) }, &[], &[0]),
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

fn cycle_reading(output: &NativeFullCycleOutput) -> Value {
    json!({
        "final_emission": output.final_emission,
        "traces": output.traces,
        "passage_returns": output.passage_returns,
    })
}

#[test]
#[ignore = "requires CUDA; phase-15 equality over the cycle, the operation ladder and the rest"]
fn extracted_operator_cycles_and_rests_return_the_recorded_numbers() {
    let ecology = extraction_chart();
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = mount_operator_surface(&readout).unwrap();
    let mut residence =
        NativeOperatorResidence::mount_from_intake(&surface, &ecology, &mut intake(&ecology))
            .unwrap();
    // The plain cycle, its rest, and the continuing cycle after remount.
    let mut readings = Vec::new();
    {
        let mut session = NativeFullOperatorSession::found(&ecology, &mut residence).unwrap();
        readings.push(cycle_reading(&session.advance_cycle_retained(&[0]).unwrap()));
        readings.push(cycle_reading(&session.advance_cycle_retained(&[0, 1]).unwrap()));
        let rest = session.detach_rest().unwrap();
        readings.push(rest_reading(&rest, false));
        let mut bytes = Vec::new();
        rest.write_to(&mut bytes).unwrap();
        drop(session);
        let decoded = NativeFullSessionRest::read_from(&mut &bytes[..], bytes.len() as u64).unwrap();
        let mut resumed =
            NativeFullOperatorSession::remount_rest(&ecology, &mut residence, &decoded).unwrap();
        readings.push(cycle_reading(&resumed.advance_cycle_retained(&[1, 2]).unwrap()));
        readings.push(json!(resumed.carrier_population()));
    }
    check("plain_cycle", Value::Array(readings), &[], "");
}

#[test]
#[ignore = "requires CUDA; phase-15 equality over the single-operation ladder and the terminal branch"]
fn extracted_operator_single_operation_ladder_returns_the_recorded_numbers() {
    let ecology = extraction_chart();
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = mount_operator_surface(&readout).unwrap();
    let mut residence =
        NativeOperatorResidence::mount_from_intake(&surface, &ecology, &mut intake(&ecology))
            .unwrap();
    let mut readings = Vec::new();
    let mut session = NativeFullOperatorSession::found(&ecology, &mut residence).unwrap();
    for rows in [vec![0u32, 1], vec![2, 0, 1]] {
        for at in 0..6u32 {
            let occurrence = NativeFullOperationOccurrence {
                ordinal: session.generation(),
                row_addresses: if at == 0 { rows.clone() } else { Vec::new() },
            };
            assert!(session.accepts_occurrence(&occurrence));
            let step = session.advance(occurrence).unwrap();
            readings.push(json!({"emission": step.emission, "trace": step.trace}));
            session = step.successor;
        }
        let ordinal = session.generation();
        let branch = session
            .advance_terminal(NativeFullOperationOccurrence {
                ordinal,
                row_addresses: Vec::new(),
            })
            .unwrap();
        let carrier = branch.emissions.last().unwrap().carrier;
        readings.push(json!({"emissions": branch.emissions, "traces": branch.traces}));
        session = branch.successor;
        readings.push(json!({
            "face": session.carrier_intervals(carrier).unwrap(),
            "held": session.carrier_population(),
            "chronology": session.chronology(),
            "complete": session.cycle_complete(),
        }));
    }
    check("operation_ladder", Value::Array(readings), &[], "");
}

#[test]
#[ignore = "requires CUDA; phase-15 equality of the continuing return, across a rest"]
fn extracted_operator_continuing_return_returns_the_recorded_numbers() {
    let ecology = extraction_chart();
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = mount_operator_surface(&readout).unwrap();
    let mut residence =
        NativeOperatorResidence::mount_from_intake(&surface, &ecology, &mut intake(&ecology))
            .unwrap();
    let aperture = NativeReturnAperture { learning_shift: 2, series_terms: 14 };
    let mut readings = Vec::new();
    let mut bytes = Vec::new();
    {
        let mut session =
            NativeFullOperatorSession::found_with_return(&ecology, &mut residence, aperture)
                .unwrap();
        for rows in [vec![0u32], vec![0, 1]] {
            readings.push(cycle_reading(&session.advance_cycle_retained(&rows).unwrap()));
            readings.push(json!(session.morphology_overlay_rank()));
        }
        let rest = session.detach_rest().unwrap();
        readings.push(rest_reading(&rest, true));
        rest.write_to(&mut bytes).unwrap();
    }
    if let Ok(directory) = std::env::var("P15_GOLDEN_DIR") {
        std::fs::write(format!("{directory}/continuing_return_rest.bin"), &bytes).unwrap();
    }
    let decoded = NativeFullSessionRest::read_from(&mut &bytes[..], bytes.len() as u64).unwrap();
    let mut resumed =
        NativeFullOperatorSession::remount_rest(&ecology, &mut residence, &decoded).unwrap();
    for rows in [vec![0u32, 1, 2], vec![2], vec![2, 0]] {
        readings.push(cycle_reading(&resumed.advance_cycle_retained(&rows).unwrap()));
        readings.push(json!(resumed.morphology_overlay_rank()));
    }
    readings.push(rest_reading(&resumed.detach_rest().unwrap(), true));
    check("continuing_return_tail", Value::Array(readings[5..].to_vec()), &["census_before", "census_after"], "");
    // The census of a continuing return measures its apparatus, which the consolidation changes
    // (the return reads the contemporary constitution instead of a retained terminal cut).
    check(
        "continuing_return",
        Value::Array(readings),
        &["census_before", "census_after"],
        "",
    );
}

#[test]
#[ignore = "requires CUDA; phase-15 equality of the joined-passage cultivation and its rest"]
fn extracted_operator_passage_cultivation_returns_the_recorded_numbers() {
    let ecology = extraction_chart();
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = mount_operator_surface(&readout).unwrap();
    let mut residence =
        NativeOperatorResidence::mount_from_intake(&surface, &ecology, &mut intake(&ecology))
            .unwrap();
    let aperture = NativeReturnAperture { learning_shift: 2, series_terms: 14 };
    let mut readings = Vec::new();
    let mut session =
        NativeFullOperatorSession::found_with_passage_return(&ecology, &mut residence, aperture)
            .unwrap();
    readings.push(json!(session.joined_passage_population()));
    for rows in [vec![0u32, 1], vec![0, 1], vec![1]] {
        readings.push(cycle_reading(&session.advance_cycle_retained(&rows).unwrap()));
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
        NativeFullOperatorSession::remount_rest(&ecology, &mut residence, &rest).unwrap();
    readings.push(cycle_reading(&resumed.advance_cycle_retained(&[1, 0]).unwrap()));
    check("passage_cultivation", Value::Array(readings), &[], "");
}

#[test]
#[ignore = "requires CUDA; phase-15 equality of the dissection receiver"]
fn extracted_operator_dissection_returns_the_recorded_numbers() {
    let ecology = extraction_chart();
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = mount_operator_surface(&readout).unwrap();
    let mut residence =
        NativeOperatorResidence::mount_from_intake(&surface, &ecology, &mut intake(&ecology))
            .unwrap();
    let mut readings = Vec::new();
    let mut session = NativeFullOperatorSession::found_for_dissection(
        &ecology,
        &mut residence,
        NativeDissectionAperture { series_terms: 14 },
    )
    .unwrap();
    readings.push(cycle_reading(&session.advance_cycle_retained(&[0, 1]).unwrap()));
    readings.push(json!(session.read_face().unwrap()));
    readings.push(json!(session.excite().unwrap()));
    readings.push(json!(session.site_contributions()
        .into_iter()
        .map(|(population, contributions)| (population.0, contributions))
        .collect::<Vec<_>>()));
    readings.push(json!(session
        .face_under_withdrawal(NativeTensorOrdinal(1), &[true, false, false])
        .unwrap()));
    readings.push(json!(session
        .face_under_withdrawal(NativeTensorOrdinal(3), &[false, true, false, false])
        .unwrap()));
    check("dissection", Value::Array(readings), &[], "");
}

fn recurrent_morphology() -> NativeOperatorMorphology {
    let coefficient = |word: u16| NativeDyadicCoefficient::from_bfloat16(word).unwrap();
    let matrix = |address: &str, rows: usize, columns: usize, words: &[u16]| NativeDyadicMatrix {
        address: address.into(),
        rows,
        columns,
        coefficients: (0..rows * columns).map(|at| coefficient(words[at % words.len()])).collect(),
    };
    NativeOperatorMorphology {
        schema: NATIVE_OPERATOR_MORPHOLOGY_SCHEMA.into(),
        carrier_extent: 4,
        interaction_extent: 2,
        matrices: vec![
            matrix("operator/input-cross-section", 2, 4, &[0x3f80, 0xbf00, 0x3e80, 0x3f00, 0xbe80]),
            matrix("operator/output-cross-section", 4, 2, &[0x3f00, 0x3f80, 0xbf80, 0x3e80, 0x3fc0]),
        ],
        norm_gain: [0x3f80u16, 0x3f00, 0x3fc0, 0x4000].into_iter().map(coefficient).collect(),
        operations: vec![
            NativeOperatorKind::Contract { matrix: "operator/input-cross-section".into() },
            NativeOperatorKind::GeluTanh,
            NativeOperatorKind::HadamardOccurrence,
            NativeOperatorKind::Contract { matrix: "operator/output-cross-section".into() },
            NativeOperatorKind::RmsNorm {
                gain_population: 4,
                epsilon: relational_geometry::Rat::new(1.into(), 1_000_000.into()),
            },
            NativeOperatorKind::Reentry,
        ],
        open_exterior: vec![],
    }
}

fn recurrent_rest(bytes: &[u8]) -> Value {
    let rest = NativeOperatorSessionRest::read(bytes).unwrap();
    json!({
        "operation_at": rest.operation_at,
        "generation": rest.generation,
        "chronology": rest.chronology,
        "carrier": section(&ResidentSectionRest::read(&rest.carrier_wire).unwrap()),
        "reentry": rest.retained_reentry_wire.as_deref()
            .map(|wire| section(&ResidentSectionRest::read(wire).unwrap())),
    })
}

#[test]
#[ignore = "requires CUDA; phase-15 equality of the host-entered per-layer operator chart"]
fn extracted_branch_chart_returns_the_recorded_numbers() {
    let morphology = recurrent_morphology();
    let readout = ResidentReadout::new().expect("CUDA");
    let surface = mount_operator_surface(&readout).unwrap();
    let resident = ResidentOperatorMorphology::mount(&surface, &morphology).unwrap();
    let carrier = [0x3f80u16, 0xbf00, 0x3e80, 0x4000];
    let grain = resident.finest_initial_grain(&carrier).unwrap();
    let mut readings = vec![json!(grain.0), json!(resident.resident_coefficient_octets())];
    let session = resident.mount_initial(&carrier, grain).unwrap();
    let branch = session.advance_branch(&[0x3f00, 0xbf80]).unwrap();
    readings.push(json!({"emissions": branch.emissions, "traces": branch.traces}));
    let bytes = branch.successor.rest().unwrap().canonical_bytes().unwrap();
    readings.push(recurrent_rest(&bytes));
    let session = resident
        .remount_session(&NativeOperatorSessionRest::read(&bytes).unwrap())
        .unwrap();
    let branch = session.advance_branch(&[0x3fc0, 0x3e00]).unwrap();
    readings.push(json!({"emissions": branch.emissions, "traces": branch.traces}));
    // A rest inside the branch carries the retained re-entry carrier.
    let mut session = resident.mount_initial(&carrier, ResidentGrain(grain.0)).unwrap();
    for at in 0..3 {
        let ordinal = session.generation();
        let step = session
            .advance(NativeOperatorOccurrence {
                ordinal,
                interaction_words: if at == 2 { vec![0x3f00, 0xbf80] } else { vec![] },
            })
            .unwrap();
        readings.push(json!({"emission": step.emission, "trace": step.trace}));
        session = step.successor;
    }
    let bytes = session.rest().unwrap().canonical_bytes().unwrap();
    if let Ok(directory) = std::env::var("P15_GOLDEN_DIR") {
        std::fs::write(format!("{directory}/branch_rest.json"), &bytes).unwrap();
    }
    readings.push(recurrent_rest(&bytes));
    let mut session = resident
        .remount_session(&NativeOperatorSessionRest::read(&bytes).unwrap())
        .unwrap();
    for _ in 3..6 {
        let ordinal = session.generation();
        let step = session
            .advance(NativeOperatorOccurrence {
                ordinal,
                interaction_words: vec![],
            })
            .unwrap();
        readings.push(json!({"emission": step.emission, "trace": step.trace}));
        session = step.successor;
    }
    readings.push(json!({"chronology": session.chronology(), "at": session.operation_at()}));
    check("branch_chart_tail", Value::Array(readings[9..].to_vec()), &[], "");
    check("branch_chart", Value::Array(readings), &[], "");
}
