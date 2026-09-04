//! SKE5: Eros composes the classes of the SKE4 return into one Athena variant and the recurrence
//! runs on it; the compression law is stated over that body.
//!
//! `deed <root> <rest> <ske4-receipts> <out>` from one command: the composed body (the rest
//! mounted with no class, the union of the class cones) is mounted once and one continuing
//! session drives every declared exposure of the family through it, its face beside the full
//! operator's (from the SKE4 exposure receipts); a second reading with the terminal unsealed
//! deposits the enclosure the composed body propagates to every coordinate of the face beside the
//! full operator's, rebased to one grain; an occurrence outside the family and an undeclared
//! history are refused at admission and never driven; then the species by remainder on that
//! domain, the declared decoder with its measured cost, the product vector, the saturation
//! receipt over the enlargement of the declared exposures, and the release receiver are returned
//! as one receipt.  A guard aborts the process when no card step completes for 180 s.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};

use athena_alpha::{
    class_cone_roles, saturation, species_over_family, width_difference, AthenaTokenApplication,
    ComposedFace, ComposedVariant, DeclaredDecoder, ProductVector, ReceiptDerivation,
    ReleaseReceipt, COMPOSED_VARIANT_SCHEMA,
};
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::holonic_intelligence::{
        declared_roles, mount_operator_surface, NativeConeRestrictedEcology, NativeExposure,
        NativeExposureFace, NativeFullOperatorSession, NativeOperatorResidence, NativeRoleGrain,
        NativeTerminalRemainder,
    },
};
use serde::Deserialize;

type Error = Box<dyn std::error::Error>;

const FAMILY: [&str; 5] = ["7 + 5 =", "9 + 3 =", "7 + 6 =", "3 + 4 =", "8 + 8 ="];
const HISTORIES: [&str; 3] = ["", "The second operand is ", "The sum is "];
const RECEIVER: &str = "terminal-face";

static LAST_STEP: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static BEGAN: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();

fn step(label: &str) {
    let began = *BEGAN.get_or_init(std::time::Instant::now);
    eprintln!("step {label} at {:.0} s", began.elapsed().as_secs_f64());
    LAST_STEP.store(
        began.elapsed().as_secs(),
        std::sync::atomic::Ordering::Relaxed,
    );
}

fn guard() {
    let began = *BEGAN.get_or_init(std::time::Instant::now);
    std::thread::spawn(move || loop {
        std::thread::sleep(std::time::Duration::from_secs(5));
        let last = LAST_STEP.load(std::sync::atomic::Ordering::Relaxed);
        if began.elapsed().as_secs().saturating_sub(last) > 180 {
            eprintln!("DEED STALLED: no card step completed for 180 s");
            std::process::exit(124);
        }
    });
}

/// The SKE4 exposure receipt, as far as this deed reads it.
#[derive(Deserialize)]
struct ExposureReceipt {
    addresses: Vec<u32>,
    history_addresses: Vec<u32>,
    face: u32,
    exact_digest: String,
    remainder: NativeTerminalRemainder,
}

fn exposure_name(occurrence: usize, history: usize) -> String {
    format!("occ{occurrence}_hist{history}")
}

fn read_widths(path: &Path) -> Result<Vec<u32>, Error> {
    let octets = std::fs::read(path)?;
    Ok(octets
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect())
}

fn residual_files_present(variant: &ComposedVariant, directory: &Path) -> bool {
    variant.residual_files.len() == variant.propagated.len()
        && variant
            .residual_files
            .iter()
            .zip(&variant.propagated)
            .all(|(file, remainder)| {
                let path = Path::new(file);
                path.components()
                    .all(|part| matches!(part, std::path::Component::Normal(_)))
                    && std::fs::metadata(directory.join(path)).is_ok_and(|metadata| {
                        metadata.is_file()
                            && (remainder.coordinates as u64).checked_mul(4) == Some(metadata.len())
                    })
            })
}

/// Recompute the finite relations and deed-field checks from deposited observations. The
/// original measurements are preserved; the original cone-union apparatus result is testimony.
/// This mode prints a corrected receipt and never initializes a device or mounts a model.
fn project_recorded(args: &[String]) -> Result<(), Error> {
    let path = Path::new(args.first().ok_or("receipt")?);
    let source_revision = args.get(1).ok_or("source revision")?;
    let mut value: serde_json::Value = serde_json::from_slice(&std::fs::read(path)?)?;
    let faces: Vec<ComposedFace> = serde_json::from_value(value["faces"].clone())?;
    let exposures: Vec<NativeExposure> = value["saturation"]["steps"]
        .as_array()
        .ok_or("recorded exposure order missing")?
        .iter()
        .map(|step| serde_json::from_value(step["exposure"].clone()))
        .collect::<Result<_, _>>()?;
    let observed: Vec<_> = faces
        .iter()
        .map(|f| NativeExposureFace {
            occurrence: f.occurrence,
            exposure: f.exposure.clone(),
            face: f.full_face,
            exact_digest: String::new(),
            cones: BTreeMap::new(),
        })
        .collect();
    let extent = usize::try_from(value["extent_roles"].as_u64().ok_or("extent missing")?)?;
    let roles = usize::try_from(value["roles"].as_u64().ok_or("roles missing")?)?;
    let refusals = usize::from(value["refused_outside_family"].is_string())
        + usize::from(value["refused_undeclared_history"].is_string());
    let extent_is_union = value["release"]["extent_is_union_of_class_cones"]
        .as_bool()
        .ok_or("recorded cone-union check missing")?;
    value["schema"] = COMPOSED_VARIANT_SCHEMA.into();
    value["saturation"] =
        serde_json::to_value(saturation(&observed, &exposures, extent, roles, refusals)?)?;
    value["release"] = serde_json::to_value(ReleaseReceipt::default())?;
    value["derivation"] = serde_json::to_value(ReceiptDerivation {
        source_revision: source_revision.clone(),
        method: "Exact identified-pair relations and observed consequence growth re-read from the existing faces in the recorded exposure order; deed fields and retained residual-file lengths checked. All measurement fields and the prior cone-union apparatus testimony are unchanged. This is not a new repository release or GPU run.".into(),
        new_gpu_run: false,
    })?;
    let mut variant: ComposedVariant = serde_json::from_value(value)?;
    variant.release = variant.assess_deed(
        residual_files_present(&variant, path.parent().ok_or("receipt directory")?),
        extent_is_union,
    );
    println!("{}", serde_json::to_string_pretty(&variant)?);
    Ok(())
}

fn deed(args: &[String]) -> Result<(), Error> {
    guard();
    let root = args.first().ok_or("root")?;
    let rest = PathBuf::from(args.get(1).ok_or("rest")?);
    let receipts = PathBuf::from(args.get(2).ok_or("ske4 receipts")?);
    let out = PathBuf::from(args.get(3).ok_or("out")?);
    std::fs::create_dir_all(&out)?;
    let application = AthenaTokenApplication::open(Path::new(root))?;
    let restricted = NativeConeRestrictedEcology::read_rest(&rest)?;
    let roles = declared_roles(&restricted.ecology, NativeRoleGrain::LayerBlock)?;
    let (class_cone_roles_per_class, cone_roles_by_occurrence) =
        class_cone_roles(&restricted, &roles);
    let extent_roles: BTreeSet<u32> = cone_roles_by_occurrence
        .values()
        .flatten()
        .copied()
        .collect();
    step("composed");
    let mut full: BTreeMap<(usize, usize), ExposureReceipt> = BTreeMap::new();
    for occurrence in 0..FAMILY.len() {
        for history in 0..HISTORIES.len() {
            let r: ExposureReceipt = serde_json::from_slice(&std::fs::read(receipts.join(
                format!("exposure_{}.json", exposure_name(occurrence, history)),
            ))?)?;
            full.insert((occurrence, history), r);
        }
    }
    let dismantle: serde_json::Value =
        serde_json::from_slice(&std::fs::read(receipts.join("dismantle.json"))?)?;
    let rest_sha256 = std::fs::read_to_string(receipts.join("rest.sha256"))
        .map(|s| s.trim().to_owned())
        .unwrap_or_default();
    let full_resident_octets =
        std::fs::read(receipts.join("../session_census_one_cycle_segments.json"))
            .ok()
            .and_then(|b| serde_json::from_slice::<serde_json::Value>(&b).ok())
            .and_then(|v| {
                v["resident_octets_now"]
                    .as_u64()
                    .or_else(|| v["resident_octets_peak"].as_u64())
            });
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let mount_started = std::time::Instant::now();
    let mut residence = {
        let mut intake = restricted.intake(None)?;
        NativeOperatorResidence::mount_from_intake(&surface, &restricted.ecology, &mut intake)?
    };
    let mount_seconds_milli = mount_started.elapsed().as_millis() as u64;
    step("mounted");
    // Admission of every declared exposure, before any is driven.
    for occurrence in 0..FAMILY.len() {
        for history in 0..HISTORIES.len() {
            let r = &full[&(occurrence, history)];
            let occurrence_addresses =
                &r.addresses[..r.addresses.len() - r.history_addresses.len()];
            restricted
                .admit(occurrence_addresses, &r.history_addresses)
                .map_err(|_| "a declared exposure of the family was refused")?;
        }
    }
    // One continuing session over the family: every cycle advances the same successor line.
    let mut session = NativeFullOperatorSession::found(&restricted.ecology, &mut residence)?;
    let composed_resident_octets = session.census().resident_octets_now;
    let mut cycle_milliseconds = Vec::new();
    let mut launches_per_cycle = Vec::new();
    let mut session_generations = Vec::new();
    let (mut read_outs, mut ingress, mut egress) = (0u64, 0u64, 0u64);
    let mut composed_faces: BTreeMap<(usize, usize), u32> = BTreeMap::new();
    for occurrence in 0..FAMILY.len() {
        for history in 0..HISTORIES.len() {
            let r = &full[&(occurrence, history)];
            let before = session.census();
            let predecessor = session.generation();
            let started = std::time::Instant::now();
            let cycle = session.advance_cycle(&r.addresses)?;
            let elapsed = started.elapsed().as_millis();
            let after = cycle.successor.census();
            let rendered = application.render(&cycle.final_emission)?;
            session = cycle.successor;
            session_generations.push((predecessor, session.generation()));
            cycle_milliseconds.push(elapsed);
            launches_per_cycle.push(after.deed_launches - before.deed_launches);
            read_outs += after.section_read_outs - before.section_read_outs;
            ingress += after.ingress_octets - before.ingress_octets;
            egress += after.egress_section_octets - before.egress_section_octets;
            composed_faces.insert((occurrence, history), rendered.selected);
            eprintln!(
                "{}: full {} composed {} {:?} equal {} (generation {} -> {})",
                exposure_name(occurrence, history),
                r.face,
                rendered.selected,
                rendered.rendered,
                rendered.selected == r.face,
                predecessor,
                session.generation()
            );
            step(&format!("cycle {}", exposure_name(occurrence, history)));
        }
    }
    drop(session);
    // The propagated remainder on the composed body: a second reading with the terminal
    // unsealed, beside the full operator's per coordinate at one grain.
    let mut faces = Vec::new();
    let mut propagated = Vec::new();
    let mut residual_files = Vec::new();
    let mut difference_grain = 0u32;
    for occurrence in 0..FAMILY.len() {
        for history in 0..HISTORIES.len() {
            let r = &full[&(occurrence, history)];
            let unsealed = NativeFullOperatorSession::found(&restricted.ecology, &mut residence)?
                .with_terminal_remainder();
            let cycle_unsealed = unsealed.advance_cycle(&r.addresses)?;
            let emission = &cycle_unsealed.final_emission;
            let last = &emission.intervals[(emission.rows - 1) * emission.width..];
            let composed_widths: Vec<u32> = last.iter().map(|(lo, hi)| (hi - lo) as u32).collect();
            let file = format!(
                "composed_remainder_{}.bin",
                exposure_name(occurrence, history)
            );
            let mut octets = Vec::with_capacity(composed_widths.len() * 4);
            for w in &composed_widths {
                octets.extend_from_slice(&w.to_le_bytes());
            }
            std::fs::write(out.join(&file), octets)?;
            residual_files.push(file);
            let full_widths = read_widths(&receipts.join(format!(
                "remainder_{}.bin",
                exposure_name(occurrence, history)
            )))?;
            let (difference, grain) = width_difference(
                &full_widths,
                r.remainder.grain,
                &composed_widths,
                emission.grain,
            );
            difference_grain = grain;
            let mut histogram: BTreeMap<u64, usize> = BTreeMap::new();
            for w in &composed_widths {
                *histogram.entry(u64::from(*w)).or_default() += 1;
            }
            propagated.push(NativeTerminalRemainder {
                exposure: NativeExposure {
                    receiver: RECEIVER.to_owned(),
                    history: r.history_addresses.clone(),
                },
                occurrence,
                coordinates: composed_widths.len(),
                nonpoint_coordinates: composed_widths.iter().filter(|w| **w > 0).count(),
                widest_grains: composed_widths.iter().copied().max().unwrap_or(0).into(),
                grain: emission.grain,
                widths: histogram.into_iter().collect(),
            });
            let composed_face = composed_faces[&(occurrence, history)];
            faces.push(ComposedFace {
                occurrence,
                exposure: NativeExposure {
                    receiver: RECEIVER.to_owned(),
                    history: r.history_addresses.clone(),
                },
                full_face: r.face,
                composed_face,
                equal: composed_face == r.face,
                width_difference: difference,
            });
            step(&format!("remainder {}", exposure_name(occurrence, history)));
        }
    }
    drop(residence);
    let outside = application.encode_turn("11 + 2 =")?;
    let undeclared = application.encode_plain("The difference is ")?;
    let member = restricted.classes[0].fibre[0].addresses.clone();
    let refused_outside_family = restricted
        .admit(&outside, &[])
        .err()
        .map(|i| format!("{:?}", i.cause));
    let refused_undeclared_history = restricted
        .admit(&member, &undeclared)
        .err()
        .map(|i| format!("{:?}", i.cause));
    let (collapsed, species) = species_over_family(&faces);
    // Saturation: the declared exposures enlarged in their declared order over the fixed family.
    let exposures_in_order: Vec<NativeExposure> = (0..HISTORIES.len())
        .map(|history| NativeExposure {
            receiver: RECEIVER.to_owned(),
            history: full[&(0, history)].history_addresses.clone(),
        })
        .collect();
    let family_faces: Vec<NativeExposureFace> = full
        .iter()
        .map(|((occurrence, _), r)| NativeExposureFace {
            occurrence: *occurrence,
            exposure: NativeExposure {
                receiver: RECEIVER.to_owned(),
                history: r.history_addresses.clone(),
            },
            face: r.face,
            exact_digest: r.exact_digest.clone(),
            cones: BTreeMap::new(),
        })
        .collect();
    let refusals = usize::from(refused_outside_family.is_some())
        + usize::from(refused_undeclared_history.is_some());
    let saturation = saturation(
        &family_faces,
        &exposures_in_order,
        extent_roles.len(),
        roles.len(),
        refusals,
    )?;
    let cycles = faces.len() as u64;
    let product = ProductVector {
        rest_octets: std::fs::metadata(&rest)?.len(),
        retained_rows: dismantle["retained_rows_by_restriction"].as_object().map(|m| m.iter().map(|(k, v)| (k.clone(), v.as_u64().unwrap_or(0) as usize)).collect()).unwrap_or_default(),
        rest_sha256,
        decoder: DeclaredDecoder {
            mount: "holonic_engine::native_ecology::holonic_intelligence::NativeOperatorResidence::mount_from_intake over NativeConeRestrictedEcology::intake(None)".to_owned(),
            recurrence: "NativeFullOperatorSession::advance_cycle, one continuing session (the segment session under the 2026-08-18 contract)".to_owned(),
            receiver: "the selected face at the terminal position, read once".to_owned(),
            mount_seconds_milli,
            cycle_milliseconds: cycle_milliseconds.clone(),
            launches_per_cycle: launches_per_cycle.clone(),
            passages_per_cycle: launches_per_cycle.clone(),
        },
        retained_fibres: restricted.classes.iter().flat_map(|c| c.fibre.iter().map(|r| (r.occurrence, r.addresses.clone()))).collect(),
        operations_per_cycle: restricted.ecology.operations.len(),
        deed_launches_per_cycle: launches_per_cycle.iter().sum::<u64>() / cycles.max(1),
        section_read_outs_per_cycle: read_outs / cycles.max(1),
        occurrences: FAMILY.len(),
        histories: HISTORIES.len(),
        exposures: faces.len(),
        composed_resident_octets,
        full_resident_octets,
        full_coefficient_octets: dismantle["full_coefficient_octets"].as_u64().unwrap_or(0),
        ingress_octets_per_cycle: ingress / cycles.max(1),
        egress_section_octets_per_cycle: egress / cycles.max(1),
    };
    let extent_is_union = restricted.validate().is_ok();
    let mut variant = ComposedVariant {
        schema: COMPOSED_VARIANT_SCHEMA.to_owned(),
        derivation: None,
        classes: restricted.classes.iter().map(|c| c.ordinal).collect(),
        class_cone_roles: class_cone_roles_per_class,
        extent_roles: extent_roles.len(),
        roles: roles.len(),
        faces,
        refused_outside_family,
        refused_undeclared_history,
        collapsed,
        species,
        propagated,
        residual_files,
        difference_grain,
        product,
        saturation,
        session_generations,
        release: ReleaseReceipt::default(),
    };
    variant.release = variant.assess_deed(residual_files_present(&variant, &out), extent_is_union);
    std::fs::write(
        out.join("ske5_composed_variant.json"),
        serde_json::to_string_pretty(&variant)?,
    )?;
    println!(
        "composed variant: {} classes, extent {} of {} roles; one session {}; faces equal {}/{}; collapsed {}; species {:?}; refused outside {}, undeclared {}; difference grain {}; last enlargement identification saturated {:?}, added no observed consequences {:?}; deed passed {}; DEED DONE",
        variant.classes.len(),
        variant.extent_roles,
        variant.roles,
        variant.release.one_session_over_the_family,
        variant.faces.iter().filter(|f| f.equal).count(),
        variant.faces.len(),
        variant.collapsed.len(),
        variant.species,
        variant.release.outside_occurrence_refused,
        variant.release.undeclared_history_refused,
        variant.difference_grain,
        variant.saturation.last_enlargement_identification_saturated,
        variant.saturation.last_enlargement_added_no_observed_consequences,
        variant.release.passed
    );
    Ok(())
}

fn main() -> Result<(), Error> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("deed") => deed(&args[1..]),
        Some("project-recorded") => project_recorded(&args[1..]),
        _ => Err("mode: deed <root> <rest> <ske4-receipts> <out> | project-recorded <receipt> <source-revision>".into()),
    }
}
