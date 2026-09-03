//! SKE2: excitation and the cone by intervention.  One occurrence of the declared family enters
//! the resident operator; the cycle's own selected face is excited and its differential returns
//! through every reaction without depositing; every site of every contraction population is read
//! (support, magnitude, first-order contribution); and the cone is founded by joint withdrawal on
//! the card: the largest prefix of the contribution order whose withdrawal leaves the face
//! unchanged is the complement, the rest is the cone, and both are withdrawn as controls.  The
//! cone is reported restricted to every population with its exact sites and a magnitude control.
//!
//! One bounded process per occurrence.  Arguments: `root occurrence out.json [controls N]`, where
//! `controls N` also runs the blueprint's first-letter per-population support controls on the
//! first `N` populations as the recorded counterexample.

use std::path::Path;

use athena_alpha::AthenaTokenApplication;
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::holonic_intelligence::{
        NativeConeRestriction, NativeConeReturn, NativeConeVerdict, NativeDissectionAperture,
        NativeFullOperatorSession, NativeOperatorResidence, NativeWithdrawnFace,
        dismantle_full_native_operator, mount_operator_surface,
    },
};
use serde::Serialize;

/// The declared family: variants of one algebraic problem, each entering as one addressed
/// occurrence through the application's own turn markers so the receiver is the first face of
/// the answer.  No answer is named anywhere in this deed.
const FAMILY: [&str; 5] = ["7 + 5 =", "9 + 3 =", "7 + 6 =", "3 + 4 =", "8 + 8 ="];

#[derive(Serialize)]
struct RestrictionReceipt {
    source_name: String,
    cone_hex: String,
    #[serde(flatten)]
    restriction: NativeConeRestriction,
}

#[derive(Serialize)]
struct VerdictReceipt {
    source_name: String,
    outside_rendered: String,
    inside_rendered: String,
    #[serde(flatten)]
    verdict: NativeConeVerdict,
}

#[derive(Serialize)]
struct Receipt {
    family: Vec<String>,
    occurrence: usize,
    material: String,
    addresses: Vec<u32>,
    face_selected: u32,
    face_rendered: String,
    face_equal_population: usize,
    face_digest: String,
    engine_face_agrees: bool,
    first_cycle_milliseconds: u128,
    excitation_milliseconds: u128,
    operations_returned: usize,
    layers_replayed: usize,
    populations_read: usize,
    sites_supported: usize,
    replay_control: NativeWithdrawnFace,
    cone: NativeConeReturn,
    complement_rendered: String,
    cone_withdrawn_rendered: String,
    boundary_source_name: Option<String>,
    boundary_alone_rendered: Option<String>,
    restrictions: Vec<RestrictionReceipt>,
    support_controls: Vec<VerdictReceipt>,
    elapsed_seconds: f64,
}

fn hex_of(sites: &[bool]) -> String {
    let mut out = String::with_capacity(sites.len() / 4 + 1);
    for chunk in sites.chunks(4) {
        let mut nibble = 0u8;
        for (at, site) in chunk.iter().enumerate() {
            if *site {
                nibble |= 1 << (3 - at);
            }
        }
        out.push(char::from_digit(u32::from(nibble), 16).unwrap_or('0'));
    }
    out
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let started = std::time::Instant::now();
    let args: Vec<String> = std::env::args().skip(1).collect();
    let root = args.first().cloned().unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let occurrence: usize = args.get(1).map(|a| a.parse()).transpose()?.unwrap_or(0);
    let out = args.get(2).cloned().unwrap_or_else(|| "ske2_receipt.json".to_owned());
    let controls: usize = match (args.get(3).map(String::as_str), args.get(4)) {
        (Some("controls"), Some(count)) => count.parse()?,
        _ => 0,
    };
    let material = FAMILY
        .get(occurrence)
        .ok_or("the occurrence is outside the declared family")?;
    let application = AthenaTokenApplication::open(Path::new(&root))?;
    let addresses = application.encode_turn(material)?;
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
    let cycle_started = std::time::Instant::now();
    eprintln!("stage: cycle on {} addresses", addresses.len());
    let cycle = session.advance_cycle(&addresses)?;
    let first_cycle_milliseconds = cycle_started.elapsed().as_millis();
    let face = application.render(&cycle.final_emission)?;
    let mut session = cycle.successor;
    eprintln!("stage: excite");
    let excitation = session.excite()?;
    let populations = session.contraction_populations();
    let source_name = |population: u32| {
        returned
            .exterior
            .populations
            .iter()
            .find(|entry| entry.ordinal.0 == population)
            .map(|entry| entry.source_name.clone())
            .unwrap_or_default()
    };
    let (first, _, _) = populations[0];
    let sites = session
        .site_support(first)
        .ok_or("the first population has no support")?
        .sites;
    eprintln!("stage: replay control");
    let replay_control = session.face_under_withdrawal(first, &vec![false; sites])?;
    eprintln!("stage: cone by intervention");
    let cone = session.cone_by_intervention()?;
    let restrictions = cone
        .restrictions
        .iter()
        .map(|restriction| RestrictionReceipt {
            source_name: source_name(restriction.population),
            cone_hex: hex_of(&restriction.cone),
            restriction: restriction.clone(),
        })
        .collect();
    let mut support_controls = Vec::new();
    for (population, _, _) in populations.iter().take(controls).copied() {
        let verdict = session.cone_controls(population)?;
        support_controls.push(VerdictReceipt {
            source_name: source_name(population.0),
            outside_rendered: application.render_address(verdict.outside_withdrawn.face.selected)?,
            inside_rendered: application.render_address(verdict.inside_withdrawn.face.selected)?,
            verdict,
        });
    }
    let receipt = Receipt {
        family: FAMILY.iter().map(|s| s.to_string()).collect(),
        occurrence,
        material: material.to_string(),
        addresses,
        face_selected: face.selected,
        face_rendered: face.rendered,
        face_equal_population: face.equal_score_population.len(),
        face_digest: excitation.face.exact_digest.clone(),
        engine_face_agrees: excitation.face.selected == face.selected,
        first_cycle_milliseconds,
        excitation_milliseconds: excitation.elapsed_milliseconds,
        operations_returned: excitation.operations_returned,
        layers_replayed: excitation.layers_replayed,
        populations_read: excitation.supports.len(),
        sites_supported: excitation.supports.iter().map(|s| s.support_population).sum(),
        replay_control,
        complement_rendered: application.render_address(cone.complement_withdrawn.face.selected)?,
        cone_withdrawn_rendered: application.render_address(cone.cone_withdrawn.face.selected)?,
        boundary_source_name: cone.boundary.as_ref().map(|b| source_name(b.population)),
        boundary_alone_rendered: cone
            .boundary
            .as_ref()
            .map(|b| application.render_address(b.alone.face.selected))
            .transpose()?,
        cone,
        restrictions,
        support_controls,
        elapsed_seconds: started.elapsed().as_secs_f64(),
    };
    std::fs::write(&out, serde_json::to_string_pretty(&receipt)?)?;
    println!(
        "occurrence {occurrence} {:?}: face {} {:?}; replay control {} / {}; cone {} of {} sites, complement {} unchanged {}, cone withdrawn changed {}, probes {}, monotone {}; {:.1} s",
        receipt.material,
        receipt.face_selected,
        receipt.face_rendered,
        receipt.replay_control.selected_unchanged,
        receipt.replay_control.exact_unchanged,
        receipt.cone.cone_population,
        receipt.cone.sites,
        receipt.cone.complement_population,
        receipt.cone.complement_withdrawn.selected_unchanged,
        !receipt.cone.cone_withdrawn.selected_unchanged,
        receipt.cone.probes.len(),
        receipt.cone.monotone,
        receipt.elapsed_seconds
    );
    Ok(())
}
