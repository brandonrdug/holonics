//! SKE3: identification.  The declared family (five variants of one algebraic problem) is exposed
//! to declared receivers and histories on the resident operator; the signature of an occurrence
//! is its face at every exposure; the quotient identifies equal signatures; every exposure's cone
//! is founded by joint intervention and the class cones, the extent, and the insufficiency are
//! unions of what the card returned.
//!
//! Modes, one bounded process each:
//!   `exposure root occurrence history out.json` — one (occurrence, history) on the card: the
//!     cycle, the excitation, the cone, the receipt;
//!   `quotient dir out.json` — host arithmetic over every exposure receipt in `dir`.

use std::path::Path;

use athena_alpha::AthenaTokenApplication;
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::holonic_intelligence::{
        NativeDissectionAperture, NativeExposure, NativeExposureFace, NativeFullOperatorSession,
        NativeOperatorResidence, NativeSignatureQuotient, NativeSiteBitmask,
        dismantle_full_native_operator, mount_operator_surface,
    },
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// The declared family: variants of one algebraic problem.
const FAMILY: [&str; 5] = ["7 + 5 =", "9 + 3 =", "7 + 6 =", "3 + 4 =", "8 + 8 ="];

/// The declared histories: fixed generator words appended after the model's turn marker.  The
/// empty word, and two words that ask the operator for what the occurrence already carries or
/// for its own answer; no answer is named.
const HISTORIES: [&str; 3] = ["", "The second operand is ", "The sum is "];

#[derive(Serialize, Deserialize)]
struct ExposureReceipt {
    material: String,
    history: String,
    addresses: Vec<u32>,
    face_rendered: String,
    engine_face_agrees: bool,
    replay_control_exact: bool,
    cone_population: usize,
    sites: usize,
    complement_unchanged: bool,
    cone_changed: bool,
    probes: usize,
    monotone: bool,
    elapsed_seconds: f64,
    face: NativeExposureFace,
}

#[derive(Serialize)]
struct ClassReceipt {
    ordinal: usize,
    occurrences: Vec<usize>,
    materials: Vec<String>,
    faces: Vec<(String, String)>,
    cone_population: usize,
}

#[derive(Serialize)]
struct QuotientReceipt {
    family: Vec<String>,
    histories: Vec<String>,
    exposures: usize,
    occurrences: usize,
    classes_under_empty_history: usize,
    classes: Vec<ClassReceipt>,
    separations: Vec<(usize, usize, String, String, String)>,
    sites: usize,
    extent_population: usize,
    insufficiency_population: usize,
    extent_by_population: BTreeMap<u32, usize>,
    #[serde(flatten)]
    quotient: NativeSignatureQuotient,
}

fn exposure(args: &[String]) -> Result<(), Box<dyn std::error::Error>> {
    let started = std::time::Instant::now();
    let root = args.first().cloned().unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let occurrence: usize = args.get(1).map(|a| a.parse()).transpose()?.unwrap_or(0);
    let history_index: usize = args.get(2).map(|a| a.parse()).transpose()?.unwrap_or(0);
    let out = args.get(3).cloned().unwrap_or_else(|| "ske3_exposure.json".to_owned());
    let material = FAMILY.get(occurrence).ok_or("the occurrence is outside the declared family")?;
    let history = HISTORIES.get(history_index).ok_or("the history is not declared")?;
    let application = AthenaTokenApplication::open(Path::new(&root))?;
    let mut addresses = application.encode_turn(material)?;
    let history_addresses = if history.is_empty() {
        Vec::new()
    } else {
        application.encode_plain(history)?
    };
    addresses.extend(history_addresses.iter().copied());
    let returned = dismantle_full_native_operator(Path::new(&root))?;
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence =
        NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    let session = NativeFullOperatorSession::found_for_dissection(
        &returned.native,
        &mut residence,
        NativeDissectionAperture { series_terms: 14 },
    )?;
    eprintln!("stage: cycle on {} addresses", addresses.len());
    let cycle = session.advance_cycle(&addresses)?;
    let face = application.render(&cycle.final_emission)?;
    let mut session = cycle.successor;
    eprintln!("stage: excite");
    let excitation = session.excite()?;
    let populations = session.contraction_populations();
    let (first, _, _) = populations[0];
    let sites = session.site_support(first).ok_or("no support")?.sites;
    let replay = session.face_under_withdrawal(first, &vec![false; sites])?;
    eprintln!("stage: cone by intervention");
    let cone = session.cone_by_intervention()?;
    let cones: BTreeMap<u32, NativeSiteBitmask> = cone
        .restrictions
        .iter()
        .map(|r| (r.population, NativeSiteBitmask::from_sites(&r.cone)))
        .collect();
    let receipt = ExposureReceipt {
        material: material.to_string(),
        history: history.to_string(),
        addresses,
        face_rendered: face.rendered,
        engine_face_agrees: excitation.face.selected == face.selected,
        replay_control_exact: replay.selected_unchanged && replay.exact_unchanged,
        cone_population: cone.cone_population,
        sites: cone.sites,
        complement_unchanged: cone.complement_withdrawn.selected_unchanged,
        cone_changed: !cone.cone_withdrawn.selected_unchanged,
        probes: cone.probes.len(),
        monotone: cone.monotone,
        elapsed_seconds: started.elapsed().as_secs_f64(),
        face: NativeExposureFace {
            occurrence,
            exposure: NativeExposure {
                receiver: "terminal-face".to_owned(),
                history: history_addresses,
            },
            face: excitation.face.selected,
            exact_digest: excitation.face.exact_digest.clone(),
            cones,
        },
    };
    std::fs::write(&out, serde_json::to_string(&receipt)?)?;
    println!(
        "occurrence {occurrence} {material:?} history {history:?}: face {} {:?}; replay exact {}; cone {} of {} (complement unchanged {}, cone changed {}, probes {}, monotone {}); {:.1} s",
        receipt.face.face,
        receipt.face_rendered,
        receipt.replay_control_exact,
        receipt.cone_population,
        receipt.sites,
        receipt.complement_unchanged,
        receipt.cone_changed,
        receipt.probes,
        receipt.monotone,
        receipt.elapsed_seconds
    );
    Ok(())
}

fn quotient(args: &[String]) -> Result<(), Box<dyn std::error::Error>> {
    let dir = args.first().ok_or("the receipt directory is required")?;
    let out = args.get(1).cloned().unwrap_or_else(|| "ske3_quotient.json".to_owned());
    let root = args.get(2).cloned().unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let application = AthenaTokenApplication::open(Path::new(&root))?;
    let mut receipts: Vec<ExposureReceipt> = Vec::new();
    for entry in std::fs::read_dir(dir)? {
        let path = entry?.path();
        if path.extension().is_some_and(|e| e == "json") {
            receipts.push(serde_json::from_str(&std::fs::read_to_string(&path)?)?);
        }
    }
    let faces: Vec<NativeExposureFace> = receipts.iter().map(|r| r.face.clone()).collect();
    let quotient = NativeSignatureQuotient::found(&faces)?;
    let history_text = |exposure: &NativeExposure| {
        receipts
            .iter()
            .find(|r| r.face.exposure == *exposure)
            .map(|r| r.history.clone())
            .unwrap_or_default()
    };
    let classes = quotient
        .classes
        .iter()
        .map(|class| ClassReceipt {
            ordinal: class.ordinal,
            occurrences: class.occurrences.clone(),
            materials: class.occurrences.iter().map(|o| FAMILY[*o].to_string()).collect(),
            faces: class
                .signature
                .faces
                .iter()
                .map(|(exposure, face)| {
                    (
                        history_text(exposure),
                        application.render_address(*face).unwrap_or_default(),
                    )
                })
                .collect(),
            cone_population: class.cone_population,
        })
        .collect();
    let separations = quotient
        .separations
        .iter()
        .map(|s| {
            (
                s.left,
                s.right,
                history_text(&s.exposure),
                application.render_address(s.left_face).unwrap_or_default(),
                application.render_address(s.right_face).unwrap_or_default(),
            )
        })
        .collect();
    let extent_by_population = quotient
        .extent
        .iter()
        .map(|(population, mask)| (*population, mask.population()))
        .collect();
    let receipt = QuotientReceipt {
        family: FAMILY.iter().map(|s| s.to_string()).collect(),
        histories: HISTORIES.iter().map(|s| s.to_string()).collect(),
        exposures: quotient.exposures.len(),
        occurrences: quotient.occurrences,
        classes_under_empty_history: quotient.classes_under_empty_history,
        classes,
        separations,
        sites: quotient.sites,
        extent_population: quotient.extent_population,
        insufficiency_population: quotient.insufficiency_population,
        extent_by_population,
        quotient,
    };
    std::fs::write(&out, serde_json::to_string(&receipt)?)?;
    println!(
        "exposures {} over {} occurrences: {} classes under the empty history, {} classes under every declared history, {} separations; extent {} of {} sites, insufficiency {}",
        receipt.exposures,
        receipt.occurrences,
        receipt.classes_under_empty_history,
        receipt.classes.len(),
        receipt.separations.len(),
        receipt.extent_population,
        receipt.sites,
        receipt.insufficiency_population
    );
    for class in &receipt.classes {
        println!("  class {}: {:?} faces {:?} cone {}", class.ordinal, class.materials, class.faces, class.cone_population);
    }
    for (left, right, history, a, b) in &receipt.separations {
        println!("  {:?} and {:?} separated by history {history:?}: {a:?} vs {b:?}", FAMILY[*left], FAMILY[*right]);
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("exposure") => exposure(&args[1..]),
        Some("quotient") => quotient(&args[1..]),
        _ => Err("mode: exposure root occurrence history out.json | quotient dir out.json [root]".into()),
    }
}
