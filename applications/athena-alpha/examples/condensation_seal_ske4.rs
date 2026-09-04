//! SKE4: condensation and seal at the role grain, through `soulkiller::dismantle`.
//!
//! The family of SKE2/SKE3 (five occurrences, three declared histories) declares its withdrawals
//! as roles at the layer-block grain (`operative_roles.rs`): every block of contractions that
//! flow into one another without crossing a residual sum (an attention block, a gated block, the
//! prologue's projection).  `deed <root> <dir>` runs the whole deed from one command: every card
//! step is a child process on a fresh device context (the exact carrier's allocator fragments
//! over a few hundred thousand section allocations) with a guard that aborts it when no card
//! step completes for 180 s; the host steps run in the parent.  The other modes are the same
//! steps singly:
//!
//! - `exposure <root> <occ> <hist> <dir>`: one cycle on the exposure, the excitation, the
//!   contributions per site, and one unsealed cycle for the propagated remainder at the face.
//! - `orders <root> <dir>`: the signature classes from the faces, and one role order per class and
//!   one for the family from the greatest share of the excitation over the exposures.
//! - `roles <root> <occ> <hist> <dir> <from> <to>`: the face under withdrawal of each single
//!   role in `[from, to)`: the declared withdrawals, one at a time.
//! - `found <root> <dir>`: per exposure the roles whose withdrawal changed the face (with any
//!   extension already read), the class cones as unions over member exposures, the family cone
//!   as the union over all.
//! - `extend <root> <occ> <hist> <dir>`: the class cone's complement withdrawn jointly, and,
//!   when that changes the face, roles restored along the class order until it does not; the
//!   same for the family cone.
//! - `extend-joint <root> <order-name> <dir>`: the same extension founded jointly over every
//!   exposure of one class: one withdrawal, every member face read under it.
//! - `verify <root> <occ> <hist> <dir>`: under each class lens (the class cone's complement
//!   withdrawn) and under the family cone's complement, this exposure's face; and the class cone
//!   withdrawn, for members.
//! - `refuse <root> <rest>`: the insufficiency lane refuses an occurrence outside the family and
//!   an undeclared history, and admits a member under a declared history to its class.
//! - `dismantle <root> <dir> <rest>`: the return across the boundary, the rest written, the
//!   species per class by its remainder.
//! - `body <root> <rest> <class> <occ> <hist>`: the class body mounted from the rest alone
//!   returns its face at a declared exposure, against the response the return carries.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};

use athena_alpha::AthenaTokenApplication;
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::holonic_intelligence::{
        NativeClassRemainder, NativeCollapsedPair, NativeConeRestrictedEcology,
        NativeDissectionAperture, NativeExposure, NativeExposureFace, NativeExposureTestimony,
        NativeFoundedClassCone, NativeFoundedCones, NativeFullOperationError,
        NativeFullOperatorDismantlingReturn, NativeFullOperatorEcology, NativeFullOperatorSession,
        NativeOperatorResidence, NativeRetainedOccurrence, NativeRoleGrain, NativeRoleOrder,
        NativeSignatureQuotient, NativeSiteBitmask, NativeSiteContributions, NativeSiteSelection,
        NativeTensorOrdinal, NativeTerminalRemainder, NativeWithdrawnFace, ResidentExcitationDismantling,
        cone_of_roles, declared_roles, dismantle_full_native_operator, mount_operator_surface,
        role_shares, role_sizes, selection_of_roles,
    },
    soulkiller,
};
use serde::{Deserialize, Serialize};

type Error = Box<dyn std::error::Error>;

const FAMILY: [&str; 5] = ["7 + 5 =", "9 + 3 =", "7 + 6 =", "3 + 4 =", "8 + 8 ="];
const HISTORIES: [&str; 3] = ["", "The second operand is ", "The sum is "];
const RECEIVER: &str = "terminal-face";
const GRAIN: NativeRoleGrain = NativeRoleGrain::LayerBlock;

fn exposure_name(occurrence: usize, history: usize) -> String {
    format!("occ{occurrence}_hist{history}")
}

#[derive(Serialize, Deserialize)]
struct ExposureReceipt {
    occurrence: usize,
    history_index: usize,
    material: String,
    history: String,
    addresses: Vec<u32>,
    history_addresses: Vec<u32>,
    face: u32,
    face_rendered: String,
    exact_digest: String,
    engine_face_agrees: bool,
    grain: NativeRoleGrain,
    roles: usize,
    role_contributions: Vec<u128>,
    cycle_milliseconds: u128,
    excitation_milliseconds: u128,
    remainder: NativeTerminalRemainder,
    elapsed_seconds: f64,
}

fn apparatus(root: &str) -> Result<(AthenaTokenApplication, NativeFullOperatorDismantlingReturn, ResidentReadout), Error> {
    let application = AthenaTokenApplication::open(Path::new(root))?;
    let returned = dismantle_full_native_operator(Path::new(root))?;
    let readout = ResidentReadout::new()?;
    Ok((application, returned, readout))
}

fn exposure_addresses(application: &AthenaTokenApplication, occurrence: usize, history: usize) -> Result<(Vec<u32>, Vec<u32>), Error> {
    let material = FAMILY.get(occurrence).ok_or("the occurrence is outside the declared family")?;
    let word = HISTORIES.get(history).ok_or("the history is not declared")?;
    let mut addresses = application.encode_turn(material)?;
    let history_addresses = if word.is_empty() { Vec::new() } else { application.encode_plain(word)? };
    addresses.extend(history_addresses.iter().copied());
    Ok((addresses, history_addresses))
}

fn exposure_of(history_addresses: &[u32]) -> NativeExposure {
    NativeExposure {
        receiver: RECEIVER.to_owned(),
        history: history_addresses.to_vec(),
    }
}

fn widths_histogram(intervals: &[(i64, i64)]) -> Vec<(u64, usize)> {
    let mut histogram: BTreeMap<u64, usize> = BTreeMap::new();
    for (lo, hi) in intervals {
        *histogram.entry((hi - lo) as u64).or_default() += 1;
    }
    histogram.into_iter().collect()
}

/// The face under a withdrawal, or the apparatus's refusal of that withdrawal (an exact carrier
/// could not hold the operator under it): no face is returned and the withdrawal founds nothing.
fn face_or_refusal(
    session: &mut NativeFullOperatorSession<'_, '_>,
    selection: &NativeSiteSelection,
) -> Result<Result<NativeWithdrawnFace, (u32, u32)>, Error> {
    match session.face_under_withdrawals(selection) {
        Ok(face) => Ok(Ok(face)),
        Err(NativeFullOperationError::ResidentObstruction { operation, flags }) => Ok(Err((operation, flags))),
        Err(error) => Err(error.into()),
    }
}

/// Found a dissection session on an exposure and read its face (no excitation).
fn faced_session<'r, 'c>(
    application: &AthenaTokenApplication,
    ecology: &'r NativeFullOperatorEcology,
    residence: &'r mut NativeOperatorResidence<'c>,
    addresses: &[u32],
) -> Result<(NativeFullOperatorSession<'r, 'c>, u32, String), Error> {
    let session = NativeFullOperatorSession::found_for_dissection(
        ecology,
        residence,
        NativeDissectionAperture { series_terms: 14 },
    )?;
    let cycle = session.advance_cycle(addresses)?;
    let rendered = application.render(&cycle.final_emission)?;
    let mut session = cycle.successor;
    let face = session.read_face()?;
    if face.selected != rendered.selected {
        return Err("the read face disagrees with the emission".into());
    }
    Ok((session, face.selected, face.exact_digest))
}

fn exposure_mode(args: &[String]) -> Result<(), Error> {
    let root = args.first().ok_or("root")?;
    let occurrence: usize = args.get(1).ok_or("occurrence")?.parse()?;
    let history: usize = args.get(2).ok_or("history")?.parse()?;
    let dir = PathBuf::from(args.get(3).ok_or("dir")?);
    std::fs::create_dir_all(&dir)?;
    let (application, returned, readout) = apparatus(root)?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence = NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    exposure_on(&application, &returned, &mut residence, occurrence, history, &dir)
}

fn exposure_on(application: &AthenaTokenApplication, returned: &NativeFullOperatorDismantlingReturn, residence: &mut NativeOperatorResidence<'_>, occurrence: usize, history: usize, dir: &Path) -> Result<(), Error> {
    let started = std::time::Instant::now();
    let (addresses, history_addresses) = exposure_addresses(application, occurrence, history)?;
    let roles = declared_roles(&returned.native, GRAIN)?;
    let (face, face_rendered, exact_digest, engine_face_agrees, contributions, cycle_milliseconds, excitation_milliseconds) = {
        let session = NativeFullOperatorSession::found_for_dissection(
            &returned.native,
            residence,
            NativeDissectionAperture { series_terms: 14 },
        )?;
        eprintln!("stage: cycle on {} addresses", addresses.len());
        let cycle_started = std::time::Instant::now();
        let cycle = session.advance_cycle(&addresses)?;
        let cycle_milliseconds = cycle_started.elapsed().as_millis();
        let rendered = application.render(&cycle.final_emission)?;
        let mut session = cycle.successor;
        eprintln!("stage: excite");
        let excitation = session.excite()?;
        let contributions = NativeSiteContributions::from_map(&session.site_contributions());
        (
            excitation.face.selected,
            rendered.rendered,
            excitation.face.exact_digest.clone(),
            excitation.face.selected == rendered.selected,
            contributions,
            cycle_milliseconds,
            excitation.elapsed_milliseconds,
        )
    };
    let role_contributions = contributions.per_role(&roles)?;
    contributions.write(&dir.join(format!("contributions_{}.bin", exposure_name(occurrence, history))))?;
    // The propagated remainder: the same cycle with the terminal read unsealed at the receiver.
    eprintln!("stage: remainder");
    let remainder = {
        let session = NativeFullOperatorSession::found(&returned.native, residence)?.with_terminal_remainder();
        let cycle = session.advance_cycle(&addresses)?;
        let emission = &cycle.final_emission;
        let last = &emission.intervals[(emission.rows - 1) * emission.width..];
        let rendered = application.render(emission)?;
        if rendered.selected != face {
            return Err(format!("the unsealed face {} disagrees with the sealed face {face}", rendered.selected).into());
        }
        let widths: Vec<u32> = last.iter().map(|(lo, hi)| (hi - lo) as u32).collect();
        let mut octets = Vec::with_capacity(widths.len() * 4);
        for width in &widths {
            octets.extend_from_slice(&width.to_le_bytes());
        }
        std::fs::write(dir.join(format!("remainder_{}.bin", exposure_name(occurrence, history))), octets)?;
        NativeTerminalRemainder {
            exposure: exposure_of(&history_addresses),
            occurrence,
            coordinates: last.len(),
            nonpoint_coordinates: last.iter().filter(|(lo, hi)| hi > lo).count(),
            widest_grains: last.iter().map(|(lo, hi)| (hi - lo) as u64).max().unwrap_or(0),
            grain: emission.grain,
            widths: widths_histogram(last),
        }
    };
    let receipt = ExposureReceipt {
        occurrence,
        history_index: history,
        material: FAMILY[occurrence].to_owned(),
        history: HISTORIES[history].to_owned(),
        addresses,
        history_addresses,
        face,
        face_rendered,
        exact_digest,
        engine_face_agrees,
        grain: GRAIN,
        roles: roles.len(),
        role_contributions,
        cycle_milliseconds,
        excitation_milliseconds,
        remainder,
        elapsed_seconds: started.elapsed().as_secs_f64(),
    };
    std::fs::write(dir.join(format!("exposure_{}.json", exposure_name(occurrence, history))), serde_json::to_string(&receipt)?)?;
    println!(
        "exposure {} {:?} {:?}: face {} {:?}, {} roles, remainder {} of {} coordinates nonpoint (widest {} grains), {:.1} s",
        exposure_name(occurrence, history),
        receipt.material,
        receipt.history,
        receipt.face,
        receipt.face_rendered,
        receipt.roles,
        receipt.remainder.nonpoint_coordinates,
        receipt.remainder.coordinates,
        receipt.remainder.widest_grains,
        receipt.elapsed_seconds
    );
    Ok(())
}

fn read_exposures(dir: &Path) -> Result<Vec<ExposureReceipt>, Error> {
    let mut receipts = Vec::new();
    for occurrence in 0..FAMILY.len() {
        for history in 0..HISTORIES.len() {
            let path = dir.join(format!("exposure_{}.json", exposure_name(occurrence, history)));
            let receipt: ExposureReceipt = serde_json::from_slice(&std::fs::read(&path)?)?;
            receipts.push(receipt);
        }
    }
    Ok(receipts)
}

fn faces_of(receipts: &[ExposureReceipt], cones: &BTreeMap<usize, BTreeMap<u32, NativeSiteBitmask>>) -> Vec<NativeExposureFace> {
    receipts
        .iter()
        .map(|r| NativeExposureFace {
            occurrence: r.occurrence,
            exposure: exposure_of(&r.history_addresses),
            face: r.face,
            exact_digest: r.exact_digest.clone(),
            cones: cones.get(&r.occurrence).cloned().unwrap_or_default(),
        })
        .collect()
}

#[derive(Serialize, Deserialize)]
struct OrdersReceipt {
    classes: Vec<Vec<usize>>,
    roles: usize,
    orders: Vec<String>,
}

fn orders_mode(args: &[String]) -> Result<(), Error> {
    let root = args.first().ok_or("root")?;
    let dir = PathBuf::from(args.get(1).ok_or("dir")?);
    let returned = dismantle_full_native_operator(Path::new(root))?;
    let roles = declared_roles(&returned.native, GRAIN)?;
    let receipts = read_exposures(&dir)?;
    let quotient = NativeSignatureQuotient::found(&faces_of(&receipts, &BTreeMap::new()))?;
    let shares: BTreeMap<(usize, usize), Vec<u128>> = receipts
        .iter()
        .map(|r| ((r.occurrence, r.history_index), role_shares(&r.role_contributions)))
        .collect();
    let mut orders = Vec::new();
    for class in &quotient.classes {
        let exposures: Vec<Vec<u128>> = shares
            .iter()
            .filter(|((occurrence, _), _)| class.occurrences.contains(occurrence))
            .map(|(_, s)| s.clone())
            .collect();
        let order = NativeRoleOrder::found(&roles, &exposures)?;
        let name = format!("order_class{}", class.ordinal);
        std::fs::write(dir.join(format!("{name}.json")), serde_json::to_string(&order)?)?;
        orders.push(name);
    }
    let family: Vec<Vec<u128>> = shares.values().cloned().collect();
    let order = NativeRoleOrder::found(&roles, &family)?;
    std::fs::write(dir.join("order_family.json"), serde_json::to_string(&order)?)?;
    orders.push("order_family".to_owned());
    let receipt = OrdersReceipt {
        classes: quotient.classes.iter().map(|c| c.occurrences.clone()).collect(),
        roles: roles.len(),
        orders,
    };
    std::fs::write(dir.join("orders.json"), serde_json::to_string_pretty(&receipt)?)?;
    println!("{} classes {:?}, {} roles, orders written", receipt.classes.len(), receipt.classes, receipt.roles);
    Ok(())
}

#[derive(Serialize, Deserialize, Clone)]
struct RoleReading {
    role: u32,
    layer: Option<u16>,
    sites: usize,
    face: u32,
    selected_unchanged: bool,
    exact_unchanged: bool,
    refused: Option<(u32, u32)>,
    elapsed_milliseconds: u128,
}

#[derive(Serialize, Deserialize)]
struct RolesReceipt {
    occurrence: usize,
    history_index: usize,
    face: u32,
    readings: Vec<RoleReading>,
    elapsed_seconds: f64,
}

fn roles_mode(args: &[String]) -> Result<(), Error> {
    let root = args.first().ok_or("root")?;
    let occurrence: usize = args.get(1).ok_or("occurrence")?.parse()?;
    let history: usize = args.get(2).ok_or("history")?.parse()?;
    let dir = PathBuf::from(args.get(3).ok_or("dir")?);
    let from: usize = args.get(4).ok_or("from")?.parse()?;
    let to: usize = args.get(5).ok_or("to")?.parse()?;
    let (application, returned, readout) = apparatus(root)?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence = NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    roles_on(&application, &returned, &mut residence, occurrence, history, &dir, from, to)
}

fn roles_on(application: &AthenaTokenApplication, returned: &NativeFullOperatorDismantlingReturn, residence: &mut NativeOperatorResidence<'_>, occurrence: usize, history: usize, dir: &Path, from: usize, to: usize) -> Result<(), Error> {
    let started = std::time::Instant::now();
    let roles = declared_roles(&returned.native, GRAIN)?;
    let sizes = role_sizes(&roles);
    let (addresses, _) = exposure_addresses(application, occurrence, history)?;
    let (mut session, face, _) = faced_session(application, &returned.native, residence, &addresses)?;
    let mut readings = Vec::new();
    for role in from..to.min(roles.len()) {
        let selection = selection_of_roles(&roles, &sizes, std::iter::once(role as u32));
        let probe_started = std::time::Instant::now();
        let reading = match face_or_refusal(&mut session, &selection)? {
            Ok(returned_face) => RoleReading {
                role: role as u32,
                layer: roles[role].layer,
                sites: roles[role].sites(),
                face: returned_face.face.selected,
                selected_unchanged: returned_face.selected_unchanged,
                exact_unchanged: returned_face.exact_unchanged,
                refused: None,
                elapsed_milliseconds: returned_face.elapsed_milliseconds,
            },
            Err(refusal) => RoleReading {
                role: role as u32,
                layer: roles[role].layer,
                sites: roles[role].sites(),
                face: u32::MAX,
                selected_unchanged: false,
                exact_unchanged: false,
                refused: Some(refusal),
                elapsed_milliseconds: probe_started.elapsed().as_millis(),
            },
        };
        eprintln!(
            "role {} (layer {:?}, {} sites): face {} unchanged {} refused {:?}",
            role, reading.layer, reading.sites, reading.face, reading.selected_unchanged, reading.refused
        );
        step(&format!("role {role}"));
        readings.push(reading);
    }
    let path = dir.join(format!("roles_{}.json", exposure_name(occurrence, history)));
    let mut all: Vec<RoleReading> = std::fs::read(&path)
        .ok()
        .and_then(|bytes| serde_json::from_slice::<RolesReceipt>(&bytes).ok())
        .map(|r| r.readings)
        .unwrap_or_default();
    all.retain(|r| (r.role as usize) < from || (r.role as usize) >= to);
    all.extend(readings);
    all.sort_by_key(|r| r.role);
    let receipt = RolesReceipt {
        occurrence,
        history_index: history,
        face,
        readings: all,
        elapsed_seconds: started.elapsed().as_secs_f64(),
    };
    std::fs::write(&path, serde_json::to_string(&receipt)?)?;
    println!(
        "roles {} [{from}, {to}): {} readings held, {:.1} s",
        exposure_name(occurrence, history),
        receipt.readings.len(),
        receipt.elapsed_seconds
    );
    Ok(())
}

#[derive(Serialize, Deserialize, Clone)]
struct ExposureCone {
    occurrence: usize,
    history_index: usize,
    /// Roles whose single withdrawal changed the face.
    load_bearing: Vec<u32>,
    /// Roles whose single withdrawal the apparatus refused.
    refused: Vec<u32>,
    /// Roles restored by the extension so a cone's complement leaves the face.
    extension: Vec<u32>,
}

#[derive(Serialize, Deserialize, Clone)]
struct FoundedCone {
    order: String,
    occurrences: Vec<usize>,
    roles: Vec<u32>,
    sites: usize,
    complement_roles: usize,
}

#[derive(Serialize, Deserialize)]
struct FoundReceipt {
    grain: NativeRoleGrain,
    roles: usize,
    sites: usize,
    exposures: Vec<ExposureCone>,
    cones: Vec<FoundedCone>,
}

#[derive(Serialize, Deserialize, Clone)]
struct ExtensionProbe {
    restored_roles: usize,
    face: u32,
    selected_unchanged: bool,
    refused: Option<(u32, u32)>,
}

#[derive(Serialize, Deserialize)]
struct ExtendReading {
    order: String,
    cone_roles_before: usize,
    initial_unchanged: bool,
    initial_refused: Option<(u32, u32)>,
    probes: Vec<ExtensionProbe>,
    extension: Vec<u32>,
    final_unchanged: bool,
}

#[derive(Serialize, Deserialize)]
struct ExtendReceipt {
    occurrence: usize,
    history_index: usize,
    face: u32,
    readings: Vec<ExtendReading>,
    elapsed_seconds: f64,
}

fn found_mode(args: &[String]) -> Result<(), Error> {
    let root = args.first().ok_or("root")?;
    let dir = PathBuf::from(args.get(1).ok_or("dir")?);
    let returned = dismantle_full_native_operator(Path::new(root))?;
    let roles = declared_roles(&returned.native, GRAIN)?;
    let sizes = role_sizes(&roles);
    let orders: OrdersReceipt = serde_json::from_slice(&std::fs::read(dir.join("orders.json"))?)?;
    let mut exposures = Vec::new();
    for occurrence in 0..FAMILY.len() {
        for history in 0..HISTORIES.len() {
            let receipt: RolesReceipt = serde_json::from_slice(&std::fs::read(dir.join(format!("roles_{}.json", exposure_name(occurrence, history))))?)?;
            if receipt.readings.len() != roles.len() {
                return Err(format!("exposure {} holds {} of {} role readings", exposure_name(occurrence, history), receipt.readings.len(), roles.len()).into());
            }
            let load_bearing: Vec<u32> = receipt.readings.iter().filter(|r| r.refused.is_none() && !r.selected_unchanged).map(|r| r.role).collect();
            let refused: Vec<u32> = receipt.readings.iter().filter(|r| r.refused.is_some()).map(|r| r.role).collect();
            let extension: Vec<u32> = std::fs::read(dir.join(format!("extend_{}.json", exposure_name(occurrence, history))))
                .ok()
                .and_then(|bytes| serde_json::from_slice::<ExtendReceipt>(&bytes).ok())
                .map(|e| e.readings.iter().flat_map(|r| r.extension.iter().copied()).collect::<BTreeSet<u32>>().into_iter().collect())
                .unwrap_or_default();
            exposures.push(ExposureCone {
                occurrence,
                history_index: history,
                load_bearing,
                refused,
                extension,
            });
        }
    }
    let cone_of = |occurrences: &[usize]| -> Vec<u32> {
        let mut cone: BTreeSet<u32> = BTreeSet::new();
        for e in exposures.iter().filter(|e| occurrences.contains(&e.occurrence)) {
            cone.extend(e.load_bearing.iter().copied());
            cone.extend(e.extension.iter().copied());
        }
        cone.into_iter().collect()
    };
    let mut cones: Vec<FoundedCone> = Vec::new();
    for (at, name) in orders.orders.iter().enumerate() {
        let occurrences: Vec<usize> = if name == "order_family" { (0..FAMILY.len()).collect() } else { orders.classes[at].clone() };
        let mut set: BTreeSet<u32> = cone_of(&occurrences).into_iter().collect();
        // The family cone, the extent, is the union of the class cones (`DeclaredFamily.extent`)
        // together with whatever the family's own joint extension found.
        if name == "order_family" {
            for class_cone in &cones {
                set.extend(class_cone.roles.iter().copied());
            }
        }
        // A joint extension over the exposures, when one was read.
        if let Some(joint) = std::fs::read(dir.join(format!("extend_joint_{name}.json")))
            .ok()
            .and_then(|bytes| serde_json::from_slice::<ExtendJointReceipt>(&bytes).ok())
        {
            set.extend(joint.extension.iter().copied());
        }
        let cone: Vec<u32> = set.into_iter().collect();
        let sites: usize = cone.iter().map(|r| roles[*r as usize].sites()).sum();
        cones.push(FoundedCone {
            order: name.clone(),
            occurrences,
            complement_roles: roles.len() - cone.len(),
            roles: cone,
            sites,
        });
    }
    let receipt = FoundReceipt {
        grain: GRAIN,
        roles: roles.len(),
        sites: sizes.values().sum(),
        exposures,
        cones,
    };
    std::fs::write(dir.join("found.json"), serde_json::to_string_pretty(&receipt)?)?;
    for e in &receipt.exposures {
        println!(
            "{}: {} load-bearing, {} refused, {} extension",
            exposure_name(e.occurrence, e.history_index), e.load_bearing.len(), e.refused.len(), e.extension.len()
        );
    }
    for cone in &receipt.cones {
        println!("{}: occurrences {:?}, {} of {} roles ({} of {} sites)", cone.order, cone.occurrences, cone.roles.len(), receipt.roles, cone.sites, receipt.sites);
    }
    Ok(())
}

fn extend_mode(args: &[String]) -> Result<(), Error> {
    let started = std::time::Instant::now();
    let root = args.first().ok_or("root")?;
    let occurrence: usize = args.get(1).ok_or("occurrence")?.parse()?;
    let history: usize = args.get(2).ok_or("history")?.parse()?;
    let dir = PathBuf::from(args.get(3).ok_or("dir")?);
    let found: FoundReceipt = serde_json::from_slice(&std::fs::read(dir.join("found.json"))?)?;
    let (application, returned, readout) = apparatus(root)?;
    let roles = declared_roles(&returned.native, GRAIN)?;
    let sizes = role_sizes(&roles);
    let (addresses, _) = exposure_addresses(&application, occurrence, history)?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence = NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    let (mut session, face, _) = faced_session(&application, &returned.native, &mut residence, &addresses)?;
    let mut readings = Vec::new();
    for cone in found.cones.iter().filter(|c| c.occurrences.contains(&occurrence)) {
        let order: NativeRoleOrder = serde_json::from_slice(&std::fs::read(dir.join(format!("{}.json", cone.order)))?)?;
        let kept: BTreeSet<u32> = cone.roles.iter().copied().collect();
        let complement: Vec<u32> = order.order.iter().copied().filter(|r| !kept.contains(r)).collect();
        let mut probes = Vec::new();
        let mut probe = |session: &mut NativeFullOperatorSession<'_, '_>, restored: &[u32]| -> Result<(bool, Option<(u32, u32)>), Error> {
            let restored_set: BTreeSet<u32> = restored.iter().copied().collect();
            let selection = selection_of_roles(&roles, &sizes, complement.iter().copied().filter(|r| !restored_set.contains(r)));
            let outcome = face_or_refusal(session, &selection)?;
            let (face_seen, unchanged, refused) = match &outcome {
                Ok(f) => (f.face.selected, f.selected_unchanged, None),
                Err(r) => (u32::MAX, false, Some(*r)),
            };
            eprintln!("{}: {} restored: face {} unchanged {} refused {:?}", cone.order, restored.len(), face_seen, unchanged, refused);
            probes.push(ExtensionProbe {
                restored_roles: restored.len(),
                face: face_seen,
                selected_unchanged: unchanged,
                refused,
            });
            Ok((unchanged, refused))
        };
        let (initial_unchanged, initial_refused) = probe(&mut session, &[])?;
        let mut extension: Vec<u32> = Vec::new();
        let mut final_unchanged = initial_unchanged;
        if !initial_unchanged {
            // Restore along the order in chunks until the face is unchanged, then release the
            // roles of the last chunk one at a time from its end while it stays unchanged.
            let chunk = (complement.len() / 8).max(1);
            let mut restored = 0usize;
            while restored < complement.len() {
                restored = (restored + chunk).min(complement.len());
                let (unchanged, _) = probe(&mut session, &complement[..restored])?;
                if unchanged {
                    final_unchanged = true;
                    break;
                }
            }
            if final_unchanged {
                let mut keep = restored;
                let floor = restored.saturating_sub(chunk);
                while keep > floor + 1 {
                    let (unchanged, _) = probe(&mut session, &complement[..keep - 1])?;
                    if unchanged {
                        keep -= 1;
                    } else {
                        break;
                    }
                }
                extension = complement[..keep].to_vec();
            } else {
                extension = complement.clone();
            }
        }
        readings.push(ExtendReading {
            order: cone.order.clone(),
            cone_roles_before: cone.roles.len(),
            initial_unchanged,
            initial_refused,
            probes,
            extension,
            final_unchanged,
        });
    }
    let receipt = ExtendReceipt {
        occurrence,
        history_index: history,
        face,
        readings,
        elapsed_seconds: started.elapsed().as_secs_f64(),
    };
    std::fs::write(dir.join(format!("extend_{}.json", exposure_name(occurrence, history))), serde_json::to_string(&receipt)?)?;
    for r in &receipt.readings {
        println!(
            "extend {} {}: initially unchanged {}, {} probes, extension {} roles, finally unchanged {}",
            exposure_name(occurrence, history), r.order, r.initial_unchanged, r.probes.len(), r.extension.len(), r.final_unchanged
        );
    }
    Ok(())
}

#[derive(Serialize, Deserialize, Clone)]
struct JointProbe {
    restored_roles: usize,
    faces: Vec<(usize, usize, u32, bool, Option<(u32, u32)>)>,
    all_unchanged: bool,
}

#[derive(Serialize, Deserialize)]
struct ExtendJointReceipt {
    order: String,
    occurrences: Vec<usize>,
    cone_roles_before: usize,
    probes: Vec<JointProbe>,
    extension: Vec<u32>,
    final_all_unchanged: bool,
    elapsed_seconds: f64,
}

/// The extension founded jointly over every exposure of a class: one withdrawal, every member
/// face read under it, restored along the class order until every member face stands.
fn extend_joint_mode(args: &[String]) -> Result<(), Error> {
    guard();
    let root = args.first().ok_or("root")?;
    let name = args.get(1).ok_or("order name")?;
    let dir = PathBuf::from(args.get(2).ok_or("dir")?);
    let (application, returned, readout) = apparatus(root)?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence = NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    extend_joint_on(&application, &returned, &mut residence, name, &dir)
}

fn extend_joint_on(application: &AthenaTokenApplication, returned: &NativeFullOperatorDismantlingReturn, residence: &mut NativeOperatorResidence<'_>, name: &str, dir: &Path) -> Result<(), Error> {
    let started = std::time::Instant::now();
    let found: FoundReceipt = serde_json::from_slice(&std::fs::read(dir.join("found.json"))?)?;
    let cone = found.cones.iter().find(|c| c.order == name).ok_or("the order is not founded")?;
    let order: NativeRoleOrder = serde_json::from_slice(&std::fs::read(dir.join(format!("{name}.json")))?)?;
    let roles = declared_roles(&returned.native, GRAIN)?;
    let sizes = role_sizes(&roles);
    let exposures: Vec<(usize, usize, Vec<u32>)> = cone
        .occurrences
        .iter()
        .flat_map(|o| (0..HISTORIES.len()).map(move |h| (*o, h)))
        .map(|(o, h)| exposure_addresses(application, o, h).map(|(a, _)| (o, h, a)))
        .collect::<Result<Vec<_>, _>>()?;
    let kept: BTreeSet<u32> = cone.roles.iter().copied().collect();
    let complement: Vec<u32> = order.order.iter().copied().filter(|r| !kept.contains(r)).collect();
    let mut probes: Vec<JointProbe> = Vec::new();
    let mut probe = |residence: &mut NativeOperatorResidence<'_>, restored: &[u32]| -> Result<bool, Error> {
        let restored_set: BTreeSet<u32> = restored.iter().copied().collect();
        let selection = selection_of_roles(&roles, &sizes, complement.iter().copied().filter(|r| !restored_set.contains(r)));
        let mut faces = Vec::new();
        let mut all = true;
        for (o, h, addresses) in &exposures {
            let (mut session, _, _) = faced_session(application, &returned.native, residence, addresses)?;
            let (face_seen, unchanged, refused) = match face_or_refusal(&mut session, &selection)? {
                Ok(f) => (f.face.selected, f.selected_unchanged, None),
                Err(r) => (u32::MAX, false, Some(r)),
            };
            all &= unchanged;
            faces.push((*o, *h, face_seen, unchanged, refused));
        }
        eprintln!("{name}: {} restored: all unchanged {all} {:?}", restored.len(), faces);
        step(&format!("{name} joint probe with {} restored", restored.len()));
        probes.push(JointProbe { restored_roles: restored.len(), faces, all_unchanged: all });
        Ok(all)
    };
    let initial = probe(residence, &[])?;
    let mut extension = Vec::new();
    let mut final_all = initial;
    if !initial {
        let chunk = (complement.len() / 8).max(1);
        let mut restored = 0usize;
        while restored < complement.len() {
            restored = (restored + chunk).min(complement.len());
            if probe(residence, &complement[..restored])? {
                final_all = true;
                break;
            }
        }
        if final_all {
            let mut keep = restored;
            let floor = restored.saturating_sub(chunk);
            while keep > floor + 1 {
                if probe(residence, &complement[..keep - 1])? {
                    keep -= 1;
                } else {
                    break;
                }
            }
            extension = complement[..keep].to_vec();
        } else {
            extension = complement.clone();
        }
    }
    let receipt = ExtendJointReceipt {
        order: name.to_owned(),
        occurrences: cone.occurrences.clone(),
        cone_roles_before: cone.roles.len(),
        probes,
        extension,
        final_all_unchanged: final_all,
        elapsed_seconds: started.elapsed().as_secs_f64(),
    };
    std::fs::write(dir.join(format!("extend_joint_{name}.json")), serde_json::to_string(&receipt)?)?;
    println!(
        "extend-joint {name}: initially all unchanged {initial}, {} probes, extension {} roles, finally {}, {:.1} s",
        receipt.probes.len(), receipt.extension.len(), receipt.final_all_unchanged, receipt.elapsed_seconds
    );
    Ok(())
}

/// The insufficiency lane: an occurrence outside the family, and an undeclared history, are
/// refused by the return, never given a face.
fn refuse_mode(args: &[String]) -> Result<(), Error> {
    let root = args.first().ok_or("root")?;
    let rest = PathBuf::from(args.get(1).ok_or("rest")?);
    let application = AthenaTokenApplication::open(Path::new(root))?;
    let restricted = NativeConeRestrictedEcology::read_rest_header(&rest)?;
    let outside = application.encode_turn("11 + 2 =")?;
    let undeclared = application.encode_plain("The difference is ")?;
    let member = restricted.classes[0].fibre[0].addresses.clone();
    let first = restricted.admit(&outside, &[]);
    let second = restricted.admit(&member, &undeclared);
    let third = restricted.admit(&member, &[]);
    println!(
        "{}",
        serde_json::to_string_pretty(&serde_json::json!({
            "occurrence_outside_family": first.as_ref().err().map(|i| serde_json::json!({"cause": format!("{:?}", i.cause), "insufficiency_population": i.insufficiency_population, "declared_histories": i.declared_histories.len(), "retained_occurrences": i.retained_occurrences.len()})),
            "history_undeclared": second.as_ref().err().map(|i| format!("{:?}", i.cause)),
            "member_under_declared_history_admitted_to_class": third.as_ref().ok().map(|c| c.ordinal),
        }))?
    );
    Ok(())
}

#[derive(Serialize, Deserialize)]
struct LensReading {
    order: String,
    member: bool,
    complement_withdrawn_face: u32,
    complement_unchanged: bool,
    complement_exact_unchanged: bool,
    complement_refused: Option<(u32, u32)>,
    cone_withdrawn_face: Option<u32>,
    cone_changed: Option<bool>,
    cone_refused: Option<(u32, u32)>,
}

#[derive(Serialize, Deserialize)]
struct VerifyReceipt {
    occurrence: usize,
    history_index: usize,
    face: u32,
    exact_digest: String,
    lenses: Vec<LensReading>,
    elapsed_seconds: f64,
}

fn verify_mode(args: &[String]) -> Result<(), Error> {
    guard();
    let root = args.first().ok_or("root")?;
    let occurrence: usize = args.get(1).ok_or("occurrence")?.parse()?;
    let history: usize = args.get(2).ok_or("history")?.parse()?;
    let dir = PathBuf::from(args.get(3).ok_or("dir")?);
    let (application, returned, readout) = apparatus(root)?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence = NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    verify_on(&application, &returned, &mut residence, occurrence, history, &dir)
}

fn verify_on(application: &AthenaTokenApplication, returned: &NativeFullOperatorDismantlingReturn, residence: &mut NativeOperatorResidence<'_>, occurrence: usize, history: usize, dir: &Path) -> Result<(), Error> {
    let started = std::time::Instant::now();
    let found: FoundReceipt = serde_json::from_slice(&std::fs::read(dir.join("found.json"))?)?;
    let roles = declared_roles(&returned.native, GRAIN)?;
    let sizes = role_sizes(&roles);
    let (addresses, _) = exposure_addresses(application, occurrence, history)?;
    let (mut session, face, exact_digest) = faced_session(application, &returned.native, residence, &addresses)?;
    let mut lenses = Vec::new();
    for cone in &found.cones {
        let member = cone.occurrences.contains(&occurrence);
        let kept: BTreeSet<u32> = cone.roles.iter().copied().collect();
        let complement = selection_of_roles(&roles, &sizes, (0..roles.len() as u32).filter(|r| !kept.contains(r)));
        let (complement_withdrawn_face, complement_unchanged, complement_exact_unchanged, complement_refused) =
            match face_or_refusal(&mut session, &complement)? {
                Ok(f) => (f.face.selected, f.selected_unchanged, f.exact_unchanged, None),
                Err(refusal) => (u32::MAX, false, false, Some(refusal)),
            };
        let (cone_withdrawn_face, cone_changed, cone_refused) = if member {
            match face_or_refusal(&mut session, &selection_of_roles(&roles, &sizes, cone.roles.iter().copied()))? {
                Ok(withdrawn) => (Some(withdrawn.face.selected), Some(!withdrawn.selected_unchanged), None),
                Err(refusal) => (None, None, Some(refusal)),
            }
        } else {
            (None, None, None)
        };
        eprintln!(
            "lens {} (member {member}): complement withdrawn face {} unchanged {} refused {:?}; cone withdrawn {:?} refused {:?}",
            cone.order, complement_withdrawn_face, complement_unchanged, complement_refused, cone_withdrawn_face, cone_refused
        );
        step(&format!("lens {}", cone.order));
        lenses.push(LensReading {
            order: cone.order.clone(),
            member,
            complement_withdrawn_face,
            complement_unchanged,
            complement_exact_unchanged,
            complement_refused,
            cone_withdrawn_face,
            cone_changed,
            cone_refused,
        });
    }
    let receipt = VerifyReceipt {
        occurrence,
        history_index: history,
        face,
        exact_digest,
        lenses,
        elapsed_seconds: started.elapsed().as_secs_f64(),
    };
    std::fs::write(dir.join(format!("verify_{}.json", exposure_name(occurrence, history))), serde_json::to_string(&receipt)?)?;
    println!("verify {}: {} lenses, {:.1} s", exposure_name(occurrence, history), receipt.lenses.len(), receipt.elapsed_seconds);
    Ok(())
}

#[derive(Serialize)]
struct ClassSummary {
    ordinal: usize,
    occurrences: Vec<usize>,
    materials: Vec<String>,
    cone_roles: usize,
    cone_sites: usize,
    species: String,
    collapsed_pairs: usize,
    member_faces_changed: usize,
    cone_withdrawn_changed_everywhere: bool,
    propagated_nonpoint: Vec<usize>,
}

#[derive(Serialize)]
struct DismantleReceipt {
    grain: NativeRoleGrain,
    roles: usize,
    sites: usize,
    extent_roles: usize,
    extent_sites: usize,
    insufficiency_sites: usize,
    family_complement_unchanged_everywhere: bool,
    classes: Vec<ClassSummary>,
    rest_octets: u64,
    rest_sha256: String,
    full_coefficient_octets: u64,
    retained_rows_by_restriction: BTreeMap<String, usize>,
    elapsed_seconds: f64,
}

fn dismantle_mode(args: &[String]) -> Result<(), Error> {
    let started = std::time::Instant::now();
    let root = args.first().ok_or("root")?;
    let dir = PathBuf::from(args.get(1).ok_or("dir")?);
    let rest = PathBuf::from(args.get(2).ok_or("rest")?);
    let returned = dismantle_full_native_operator(Path::new(root))?;
    let roles = declared_roles(&returned.native, GRAIN)?;
    let sizes = role_sizes(&roles);
    let receipts = read_exposures(&dir)?;
    let found: FoundReceipt = serde_json::from_slice(&std::fs::read(dir.join("found.json"))?)?;
    let mut verifies: BTreeMap<(usize, usize), VerifyReceipt> = BTreeMap::new();
    for occurrence in 0..FAMILY.len() {
        for history in 0..HISTORIES.len() {
            let receipt: VerifyReceipt = serde_json::from_slice(&std::fs::read(dir.join(format!("verify_{}.json", exposure_name(occurrence, history))))?)?;
            verifies.insert((occurrence, history), receipt);
        }
    }
    let full_face = |occurrence: usize, history: usize| -> u32 {
        receipts.iter().find(|r| r.occurrence == occurrence && r.history_index == history).map(|r| r.face).unwrap_or(u32::MAX)
    };
    let exposure_at = |history: usize| -> NativeExposure {
        exposure_of(&receipts.iter().find(|r| r.history_index == history).map(|r| r.history_addresses.clone()).unwrap_or_default())
    };
    let mut class_cones: Vec<NativeFoundedClassCone> = Vec::new();
    let mut class_cone_by_occurrence: BTreeMap<usize, BTreeMap<u32, NativeSiteBitmask>> = BTreeMap::new();
    let mut remainders: Vec<NativeClassRemainder> = Vec::new();
    let mut summaries = Vec::new();
    let mut family_complement_unchanged = true;
    let mut extent_mask: BTreeMap<u32, NativeSiteBitmask> = BTreeMap::new();
    let mut extent_roles = 0usize;
    for (at, cone) in found.cones.iter().enumerate() {
        let mask = cone_of_roles(&roles, &sizes, cone.roles.iter().copied());
        if cone.order == "order_family" {
            extent_mask = mask.clone();
            extent_roles = cone.roles.len();
            for verify in verifies.values() {
                if let Some(lens) = verify.lenses.iter().find(|l| l.order == cone.order) {
                    family_complement_unchanged &= lens.complement_unchanged;
                }
            }
            continue;
        }
        for occurrence in &cone.occurrences {
            class_cone_by_occurrence.insert(*occurrence, mask.clone());
        }
        let mut lens_faces = Vec::new();
        let mut member_faces_changed = Vec::new();
        let mut cone_withdrawn_changed = true;
        for occurrence in 0..FAMILY.len() {
            for history in 0..HISTORIES.len() {
                let verify = &verifies[&(occurrence, history)];
                let lens = verify.lenses.iter().find(|l| l.order == cone.order).ok_or("a lens reading is missing")?;
                let full = full_face(occurrence, history);
                lens_faces.push((occurrence, exposure_at(history), lens.complement_withdrawn_face, full));
                if lens.member {
                    if !lens.complement_unchanged {
                        member_faces_changed.push((occurrence, exposure_at(history), lens.complement_withdrawn_face, full));
                    }
                    cone_withdrawn_changed &= lens.cone_changed.unwrap_or(false);
                }
            }
        }
        let collapsed: Vec<NativeCollapsedPair> = NativeClassRemainder::collapsed_pairs(&lens_faces);
        let propagated: Vec<NativeTerminalRemainder> = receipts
            .iter()
            .filter(|r| cone.occurrences.contains(&r.occurrence))
            .map(|r| r.remainder.clone())
            .collect();
        let species = NativeClassRemainder::species_of(&collapsed, &propagated);
        summaries.push(ClassSummary {
            ordinal: at,
            occurrences: cone.occurrences.clone(),
            materials: cone.occurrences.iter().map(|o| FAMILY[*o].to_owned()).collect(),
            cone_roles: cone.roles.len(),
            cone_sites: cone.sites,
            species: format!("{species:?}").to_lowercase(),
            collapsed_pairs: collapsed.len(),
            member_faces_changed: member_faces_changed.len(),
            cone_withdrawn_changed_everywhere: cone_withdrawn_changed,
            propagated_nonpoint: propagated.iter().map(|p| p.nonpoint_coordinates).collect(),
        });
        remainders.push(NativeClassRemainder {
            lens_faces,
            collapsed,
            member_faces_changed,
            propagated,
            species,
        });
        class_cones.push(NativeFoundedClassCone {
            occurrences: cone.occurrences.clone(),
            cone: mask,
        });
    }
    let faces = faces_of(&receipts, &class_cone_by_occurrence);
    let fibre: Vec<NativeRetainedOccurrence> = (0..FAMILY.len())
        .map(|occurrence| NativeRetainedOccurrence {
            occurrence,
            addresses: receipts
                .iter()
                .find(|r| r.occurrence == occurrence && r.history_index == 0)
                .map(|r| r.addresses.clone())
                .unwrap_or_default(),
        })
        .collect();
    let histories: Vec<Vec<u32>> = (0..HISTORIES.len())
        .map(|history| receipts.iter().find(|r| r.history_index == history).map(|r| r.history_addresses.clone()).unwrap_or_default())
        .collect();
    let testimony: Vec<NativeExposureTestimony> = receipts
        .iter()
        .map(|r| {
            let verify = &verifies[&(r.occurrence, r.history_index)];
            let class_lens = verify.lenses.iter().find(|l| l.member && l.order != "order_family");
            let exposure_cone = found.exposures.iter().find(|e| e.occurrence == r.occurrence && e.history_index == r.history_index);
            NativeExposureTestimony {
                occurrence: r.occurrence,
                history: r.history_addresses.clone(),
                face: r.face,
                exact_digest: r.exact_digest.clone(),
                cone_population: class_cone_by_occurrence
                    .get(&r.occurrence)
                    .map(|m| m.values().map(NativeSiteBitmask::population).sum())
                    .unwrap_or(0),
                complement_unchanged: class_lens.is_some_and(|l| l.complement_unchanged),
                cone_changed: class_lens.and_then(|l| l.cone_changed).unwrap_or(false),
                probes: exposure_cone.map(|e| e.load_bearing.len() + e.refused.len()).unwrap_or(0),
                monotone: true,
            }
        })
        .collect();
    let extent_sites: usize = extent_mask.values().map(NativeSiteBitmask::population).sum();
    let sites: usize = sizes.values().sum();
    let input = ResidentExcitationDismantling {
        realization: returned,
        faces,
        fibre,
        histories,
        testimony,
        founded: NativeFoundedCones {
            extent: extent_mask,
            classes: class_cones,
        },
        remainders,
    };
    let dismantled = soulkiller::dismantle(input)?;
    let productive: NativeConeRestrictedEcology = dismantled.native;
    let insufficiency = dismantled.insufficiency;
    productive.validate()?;
    let rest_sha256 = productive.write_rest(&rest)?;
    let rest_octets = std::fs::metadata(&rest)?.len();
    let full_coefficient_octets: u64 = productive
        .ecology
        .coefficient_populations
        .iter()
        .map(|p| p.coefficient_population * 2)
        .sum();
    let mut retained_rows_by_restriction: BTreeMap<String, usize> = BTreeMap::new();
    for section in &productive.cross_sections {
        *retained_rows_by_restriction.entry(format!("{:?}", section.restriction).to_lowercase()).or_default() += section.retained_rows.len();
    }
    let receipt = DismantleReceipt {
        grain: GRAIN,
        roles: roles.len(),
        sites,
        extent_roles,
        extent_sites,
        insufficiency_sites: insufficiency.insufficiency_population,
        family_complement_unchanged_everywhere: family_complement_unchanged,
        classes: summaries,
        rest_octets,
        rest_sha256,
        full_coefficient_octets,
        retained_rows_by_restriction,
        elapsed_seconds: started.elapsed().as_secs_f64(),
    };
    std::fs::write(dir.join("dismantle.json"), serde_json::to_string_pretty(&receipt)?)?;
    println!("{}", serde_json::to_string_pretty(&receipt)?);
    Ok(())
}

#[derive(Serialize)]
struct BodyReceipt {
    class: usize,
    occurrence: usize,
    history_index: usize,
    addresses: Vec<u32>,
    expected_face: u32,
    returned_face: u32,
    returned_rendered: String,
    face_agrees: bool,
    mount_seconds: f64,
    cycle_milliseconds: u128,
    retained_rows_by_restriction: BTreeMap<String, usize>,
}

fn body_mode(args: &[String]) -> Result<(), Error> {
    let root = args.first().ok_or("root")?;
    let rest = PathBuf::from(args.get(1).ok_or("rest")?);
    let class_ordinal: usize = args.get(2).ok_or("class")?.parse()?;
    let occurrence: usize = args.get(3).ok_or("occurrence")?.parse()?;
    let history: usize = args.get(4).ok_or("history")?.parse()?;
    let out = args.get(5).cloned();
    let application = AthenaTokenApplication::open(Path::new(root))?;
    let restricted = NativeConeRestrictedEcology::read_rest(&rest)?;
    let class = restricted.classes.iter().find(|c| c.ordinal == class_ordinal).ok_or("the class is not in the return")?.clone();
    let (addresses, history_addresses) = exposure_addresses(&application, occurrence, history)?;
    let mut retained_rows_by_restriction: BTreeMap<String, usize> = BTreeMap::new();
    for section in &restricted.cross_sections {
        *retained_rows_by_restriction.entry(format!("{:?}", section.restriction).to_lowercase()).or_default() +=
            restricted.class_rows(&class, section).len();
    }
    let expected = if class.fibre.iter().any(|r| r.occurrence == occurrence) {
        let admitted = restricted
            .admit(&class.fibre.iter().find(|r| r.occurrence == occurrence).map(|r| r.addresses.as_slice()).unwrap_or(&[]), &history_addresses)
            .map_err(|_| "a declared exposure of a member was refused")?;
        if admitted.ordinal != class_ordinal {
            return Err("the admitted class disagrees".into());
        }
        class.response.iter().find(|r| r.exposure.history == history_addresses).map(|r| r.face).ok_or("no response at the exposure")?
    } else {
        class
            .remainder
            .lens_faces
            .iter()
            .find(|(o, e, _, _)| *o == occurrence && e.history == history_addresses)
            .map(|(_, _, lens, _)| *lens)
            .ok_or("no lens face at the exposure")?
    };
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let mount_started = std::time::Instant::now();
    let mut residence = {
        let mut intake = restricted.intake(Some(class_ordinal))?;
        NativeOperatorResidence::mount_from_intake(&surface, &restricted.ecology, &mut intake)?
    };
    let mount_seconds = mount_started.elapsed().as_secs_f64();
    let session = NativeFullOperatorSession::found(&restricted.ecology, &mut residence)?;
    let cycle_started = std::time::Instant::now();
    let cycle = session.advance_cycle(&addresses)?;
    let cycle_milliseconds = cycle_started.elapsed().as_millis();
    let rendered = application.render(&cycle.final_emission)?;
    let receipt = BodyReceipt {
        class: class_ordinal,
        occurrence,
        history_index: history,
        addresses,
        expected_face: expected,
        returned_face: rendered.selected,
        returned_rendered: rendered.rendered,
        face_agrees: rendered.selected == expected,
        mount_seconds,
        cycle_milliseconds,
        retained_rows_by_restriction,
    };
    if let Some(out) = out {
        std::fs::write(out, serde_json::to_string_pretty(&receipt)?)?;
    }
    println!("{}", serde_json::to_string_pretty(&receipt)?);
    Ok(())
}

/// The last completed card step, in seconds since the deed began; the guard aborts the process
/// when no step completes for 180 s (the rule's purpose: no awaiting of a hung process), and
/// says where it stalled.
static LAST_STEP: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static STALL_LABEL: std::sync::Mutex<String> = std::sync::Mutex::new(String::new());
static BEGAN: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();

/// Mark a completed card step: the guard measures from the last mark.
fn step(label: &str) {
    let began = *BEGAN.get_or_init(std::time::Instant::now);
    eprintln!("step {label} at {:.0} s", began.elapsed().as_secs_f64());
    LAST_STEP.store(began.elapsed().as_secs(), std::sync::atomic::Ordering::Relaxed);
    if let Ok(mut stall) = STALL_LABEL.lock() {
        stall.clear();
        stall.push_str(label);
    }
}

/// Arm the guard: the process aborts with a report when no card step completes for 180 s.
fn guard() {
    let began = *BEGAN.get_or_init(std::time::Instant::now);
    std::thread::spawn(move || loop {
        std::thread::sleep(std::time::Duration::from_secs(5));
        let last = LAST_STEP.load(std::sync::atomic::Ordering::Relaxed);
        if began.elapsed().as_secs().saturating_sub(last) > 180 {
            let label = STALL_LABEL.lock().map(|s| s.clone()).unwrap_or_default();
            eprintln!("DEED STALLED: no card step completed for 180 s after `{label}`");
            std::process::exit(124);
        }
    });
}

/// One exposure as one process: its cycle, excitation, remainder, and every single-role
/// withdrawal, on one mounted residence.
fn deed_exposure_mode(args: &[String]) -> Result<(), Error> {
    guard();
    let root = args.first().ok_or("root")?;
    let occurrence: usize = args.get(1).ok_or("occurrence")?.parse()?;
    let history: usize = args.get(2).ok_or("history")?.parse()?;
    let dir = PathBuf::from(args.get(3).ok_or("dir")?);
    std::fs::create_dir_all(&dir)?;
    let (application, returned, readout) = apparatus(root)?;
    let roles = declared_roles(&returned.native, GRAIN)?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence = NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    step("mounted");
    exposure_on(&application, &returned, &mut residence, occurrence, history, &dir)?;
    step("exposure");
    roles_on(&application, &returned, &mut residence, occurrence, history, &dir, 0, roles.len())?;
    step("roles");
    Ok(())
}

/// Run one step of the deed as a child process with a fresh device context: the exact carrier's
/// allocator fragments over a few hundred thousand section allocations, and a step is the unit
/// that stays whole.  The child carries the hang guard; the parent waits.
fn child(args: &[&str]) -> Result<(), Error> {
    let exe = std::env::current_exe()?;
    eprintln!("deed: {}", args.join(" "));
    let status = std::process::Command::new(exe).args(args).status()?;
    if !status.success() {
        return Err(format!("the step `{}` failed with {status}", args.join(" ")).into());
    }
    Ok(())
}

/// The whole deed from one command: every exposure, the founding, every joint extension, every
/// verification, the dismantle, the class bodies from the rest, and the insufficiency lane.
/// Each card step runs as a child process on a fresh device context; the host steps run here.
fn deed_mode(args: &[String]) -> Result<(), Error> {
    let began = std::time::Instant::now();
    let root = args.first().ok_or("root")?;
    let dir = PathBuf::from(args.get(1).ok_or("dir")?);
    std::fs::create_dir_all(&dir)?;
    let dir_text = dir.to_string_lossy().into_owned();
    // The rest is written where the fourth argument says, else beside the receipts; it is the
    // size of the retained coefficients (several GB) and belongs on a disk, not a memory-backed
    // temporary file system.
    let rest = args.get(3).map(PathBuf::from).unwrap_or_else(|| dir.join("rest.bin"));
    let rest_text = rest.to_string_lossy().into_owned();
    // A stage to resume from: exposures (default), extend, verify, or dismantle; earlier stages'
    // receipts must already be in `dir`.
    let from = args.get(2).map(String::as_str).unwrap_or("exposures");
    let stage = |name: &str| ["exposures", "extend", "verify", "dismantle"].iter().position(|s| *s == name).unwrap_or(0);
    if stage(from) <= stage("exposures") {
        for occurrence in 0..FAMILY.len() {
            for history in 0..HISTORIES.len() {
                child(&["deed-exposure", root, &occurrence.to_string(), &history.to_string(), &dir_text])?;
            }
        }
        orders_mode(&[root.clone(), dir_text.clone()])?;
    }
    if stage(from) <= stage("extend") {
        found_mode(&[root.clone(), dir_text.clone()])?;
        let orders: OrdersReceipt = serde_json::from_slice(&std::fs::read(dir.join("orders.json"))?)?;
        for name in &orders.orders {
            if from != "exposures" && dir.join(format!("extend_joint_{name}.json")).exists() {
                continue;
            }
            child(&["extend-joint", root, name, &dir_text])?;
        }
        found_mode(&[root.clone(), dir_text.clone()])?;
    }
    if stage(from) <= stage("verify") {
        for occurrence in 0..FAMILY.len() {
            for history in 0..HISTORIES.len() {
                child(&["verify", root, &occurrence.to_string(), &history.to_string(), &dir_text])?;
            }
        }
    }
    dismantle_mode(&[root.clone(), dir_text.clone(), rest_text.clone()])?;
    child(&["bodies", root, &rest_text, &dir_text])?;
    refuse_mode(&[root.clone(), rest_text.clone()])?;
    println!("DEED DONE in {:.0} s", began.elapsed().as_secs_f64());
    Ok(())
}

#[derive(Serialize)]
struct BodiesReceipt {
    class: usize,
    mount_seconds: f64,
    /// (occurrence, history, expected, returned, agrees) for the class's own occurrences.
    faces: Vec<(usize, usize, u32, u32, bool)>,
    member_faces_agree: usize,
    member_faces: usize,
    /// Non-member occurrences the class refuses at admission (its fibre does not retain them).
    non_members_refused: usize,
    non_members: usize,
}

/// Every class body mounted once from the rest and driven through the declared exposures of its
/// own occurrences: the stored presentation against the response the return carries.  A
/// non-member occurrence is outside the class's fibre and is refused at admission, never driven:
/// the class body retains the rows its own occurrences addressed and no others.
fn bodies_mode(args: &[String]) -> Result<(), Error> {
    guard();
    let root = args.first().ok_or("root")?;
    let rest = PathBuf::from(args.get(1).ok_or("rest")?);
    let dir = PathBuf::from(args.get(2).ok_or("dir")?);
    let application = AthenaTokenApplication::open(Path::new(root))?;
    let restricted = NativeConeRestrictedEcology::read_rest(&rest)?;
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let mut receipts = Vec::new();
    for class in &restricted.classes {
        let mount_started = std::time::Instant::now();
        let mut residence = {
            let mut intake = restricted.intake(Some(class.ordinal))?;
            NativeOperatorResidence::mount_from_intake(&surface, &restricted.ecology, &mut intake)?
        };
        let mount_seconds = mount_started.elapsed().as_secs_f64();
        let mut faces = Vec::new();
        let (mut member_agree, mut members, mut refused, mut non_members) = (0usize, 0usize, 0usize, 0usize);
        for occurrence in 0..FAMILY.len() {
            for history in 0..HISTORIES.len() {
                let (addresses, history_addresses) = exposure_addresses(&application, occurrence, history)?;
                let member = class.fibre.iter().any(|r| r.occurrence == occurrence);
                if !member {
                    non_members += 1;
                    let occurrence_addresses = addresses[..addresses.len() - history_addresses.len()].to_vec();
                    match restricted.admit(&occurrence_addresses, &history_addresses) {
                        Ok(admitted) if admitted.ordinal != class.ordinal => refused += 1,
                        Err(_) => refused += 1,
                        Ok(_) => {}
                    }
                    continue;
                }
                let expected = class.response.iter().find(|r| r.exposure.history == history_addresses).map(|r| r.face).ok_or("no response")?;
                let session = NativeFullOperatorSession::found(&restricted.ecology, &mut residence)?;
                let cycle = session.advance_cycle(&addresses)?;
                let rendered = application.render(&cycle.final_emission)?;
                let agrees = rendered.selected == expected;
                eprintln!("body class {} {}: expected {expected} returned {} {:?} agrees {agrees}", class.ordinal, exposure_name(occurrence, history), rendered.selected, rendered.rendered);
                step(&format!("body class {} {}", class.ordinal, exposure_name(occurrence, history)));
                members += 1;
                member_agree += usize::from(agrees);
                faces.push((occurrence, history, expected, rendered.selected, agrees));
            }
        }
        receipts.push(BodiesReceipt { class: class.ordinal, mount_seconds, faces, member_faces_agree: member_agree, member_faces: members, non_members_refused: refused, non_members });
        drop(residence);
    }
    std::fs::write(dir.join("bodies.json"), serde_json::to_string_pretty(&receipts)?)?;
    for r in &receipts {
        println!("bodies class {}: members {}/{} agree, non-members refused at admission {}/{}, mount {:.1} s", r.class, r.member_faces_agree, r.member_faces, r.non_members_refused, r.non_members, r.mount_seconds);
    }
    Ok(())
}

/// Locate a disagreement between the in-session lens (a class cone's complement withdrawn) and
/// the class body mounted from the rest, for one exposure: the faces under the withdrawal of
/// the roles outside the family cone (in-session), of the class cone's complement (in-session),
/// the body mounted from the rest at the extent (no class), and the class body.
fn compare_mode(args: &[String]) -> Result<(), Error> {
    let root = args.first().ok_or("root")?;
    let rest = PathBuf::from(args.get(1).ok_or("rest")?);
    let class_ordinal: usize = args.get(2).ok_or("class")?.parse()?;
    let occurrence: usize = args.get(3).ok_or("occurrence")?.parse()?;
    let history: usize = args.get(4).ok_or("history")?.parse()?;
    let (application, returned, readout) = apparatus(root)?;
    let roles = declared_roles(&returned.native, GRAIN)?;
    let sizes = role_sizes(&roles);
    let (addresses, _) = exposure_addresses(&application, occurrence, history)?;
    let restricted = NativeConeRestrictedEcology::read_rest_header(&rest)?;
    let class = restricted.classes.iter().find(|c| c.ordinal == class_ordinal).ok_or("class")?;
    // Roles from bitmasks: a role is in a cone when all its sites are.
    let roles_in = |mask: &BTreeMap<u32, NativeSiteBitmask>| -> Vec<u32> {
        roles.iter().filter(|r| r.members.iter().all(|m| {
            mask.get(&m.population).map(|b| { let s = b.to_sites(); (m.first..m.first + m.sites).all(|i| s.get(i).copied().unwrap_or(false)) }).unwrap_or(false)
        })).map(|r| r.ordinal).collect()
    };
    let class_roles = roles_in(&class.cone);
    let extent_roles = roles_in(&restricted.extent);
    println!("class {} cone roles {} extent roles {}", class_ordinal, class_roles.len(), extent_roles.len());
    let surface = mount_operator_surface(&readout)?;
    let mut faces = serde_json::Map::new();
    {
        let mut residence = NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
        let (mut session, face, _) = faced_session(&application, &returned.native, &mut residence, &addresses)?;
        faces.insert("full".into(), face.into());
        let outside_extent = selection_of_roles(&roles, &sizes, (0..roles.len() as u32).filter(|r| !extent_roles.contains(r)));
        let f = session.face_under_withdrawals(&outside_extent)?;
        faces.insert("lens_outside_extent".into(), f.face.selected.into());
        let outside_class = selection_of_roles(&roles, &sizes, (0..roles.len() as u32).filter(|r| !class_roles.contains(r)));
        let f = session.face_under_withdrawals(&outside_class)?;
        faces.insert("lens_outside_class".into(), f.face.selected.into());
        let f = session.face_under_withdrawals(&outside_class)?;
        faces.insert("lens_outside_class_again".into(), f.face.selected.into());
        // The same withdrawal from a session founded afresh on the same residence.
        drop(session);
        let (mut session, _, _) = faced_session(&application, &returned.native, &mut residence, &addresses)?;
        let f = session.face_under_withdrawals(&outside_class)?;
        faces.insert("lens_outside_class_fresh_session".into(), f.face.selected.into());
    }
    let restricted = NativeConeRestrictedEcology::read_rest(&rest)?;
    for (label, which) in [("body_extent", None), ("body_class", Some(class_ordinal))] {
        let mut residence = {
            let mut intake = restricted.intake(which)?;
            NativeOperatorResidence::mount_from_intake(&surface, &restricted.ecology, &mut intake)?
        };
        let session = NativeFullOperatorSession::found(&restricted.ecology, &mut residence)?;
        let cycle = session.advance_cycle(&addresses)?;
        let rendered = application.render(&cycle.final_emission)?;
        faces.insert(label.into(), rendered.selected.into());
    }
    for (k, v) in &faces {
        let rendered = v.as_u64().and_then(|a| application.render_address(a as u32).ok()).unwrap_or_default();
        println!("{k}: {v} {rendered:?}");
    }
    Ok(())
}

/// The face under the joint withdrawal of listed roles, in-session: several lists separated by
/// `;`, each `a,b,c` role ordinals, or `Ax` / `Bx` for the first or second member of role x alone.
fn withdraw_mode(args: &[String]) -> Result<(), Error> {
    let root = args.first().ok_or("root")?;
    let occurrence: usize = args.get(1).ok_or("occurrence")?.parse()?;
    let history: usize = args.get(2).ok_or("history")?.parse()?;
    let lists = args.get(3).ok_or("lists")?;
    let (application, returned, readout) = apparatus(root)?;
    let roles = declared_roles(&returned.native, GRAIN)?;
    let sizes = role_sizes(&roles);
    let (addresses, _) = exposure_addresses(&application, occurrence, history)?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence = NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    let (mut session, face, _) = faced_session(&application, &returned.native, &mut residence, &addresses)?;
    println!("full face {face} {:?}", application.render_address(face)?);
    for list in lists.split(';') {
        let mut selection = NativeSiteSelection::founded(&sizes);
        for item in list.split(',').filter(|s| !s.is_empty()) {
            let (member, ordinal): (Option<usize>, u32) = match item.chars().next() {
                Some('A') => (Some(0), item[1..].parse()?),
                Some('B') => (Some(1), item[1..].parse()?),
                _ => (None, item.parse()?),
            };
            let role = &roles[ordinal as usize];
            for (at, m) in role.members.iter().enumerate() {
                if member.is_none_or(|which| which == at) {
                    for site in m.first..m.first + m.sites {
                        selection.withdraw(NativeTensorOrdinal(m.population), site);
                    }
                }
            }
        }
        let withdrawn = selection.withdrawn_population();
        match face_or_refusal(&mut session, &selection)? {
            Ok(f) => println!("withdraw [{list}] ({withdrawn} sites): face {} {:?} unchanged {}", f.face.selected, application.render_address(f.face.selected)?, f.selected_unchanged),
            Err(r) => println!("withdraw [{list}] ({withdrawn} sites): refused {r:?}"),
        }
    }
    Ok(())
}

/// The in-session withdrawal on a body mounted from the rest at the extent: the same base as the
/// class body, so a difference between withdrawing outputs and withdrawing rows is isolated.
fn withdraw_on_body_mode(args: &[String]) -> Result<(), Error> {
    let root = args.first().ok_or("root")?;
    let rest = PathBuf::from(args.get(1).ok_or("rest")?);
    let occurrence: usize = args.get(2).ok_or("occurrence")?.parse()?;
    let history: usize = args.get(3).ok_or("history")?.parse()?;
    let lists = args.get(4).ok_or("lists")?;
    let application = AthenaTokenApplication::open(Path::new(root))?;
    let restricted = NativeConeRestrictedEcology::read_rest(&rest)?;
    let roles = declared_roles(&restricted.ecology, GRAIN)?;
    let sizes = role_sizes(&roles);
    let (addresses, _) = exposure_addresses(&application, occurrence, history)?;
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence = {
        let mut intake = restricted.intake(None)?;
        NativeOperatorResidence::mount_from_intake(&surface, &restricted.ecology, &mut intake)?
    };
    let (mut session, face, _) = faced_session(&application, &restricted.ecology, &mut residence, &addresses)?;
    println!("extent body face {face} {:?}", application.render_address(face)?);
    for list in lists.split(';') {
        let mut selection = NativeSiteSelection::founded(&sizes);
        for item in list.split(',').filter(|s| !s.is_empty()) {
            let (member, ordinal): (Option<usize>, u32) = match item.chars().next() {
                Some('A') => (Some(0), item[1..].parse()?),
                Some('B') => (Some(1), item[1..].parse()?),
                _ => (None, item.parse()?),
            };
            for (at, m) in roles[ordinal as usize].members.iter().enumerate() {
                if member.is_none_or(|which| which == at) {
                    for site in m.first..m.first + m.sites {
                        selection.withdraw(NativeTensorOrdinal(m.population), site);
                    }
                }
            }
        }
        match face_or_refusal(&mut session, &selection)? {
            Ok(f) => println!("withdraw-on-body [{list}]: face {} {:?} unchanged {}", f.face.selected, application.render_address(f.face.selected)?, f.selected_unchanged),
            Err(r) => println!("withdraw-on-body [{list}]: refused {r:?}"),
        }
    }
    Ok(())
}

fn main() -> Result<(), Error> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("deed") => deed_mode(&args[1..]),
        Some("deed-exposure") => deed_exposure_mode(&args[1..]),
        Some("exposure") => exposure_mode(&args[1..]),
        Some("orders") => orders_mode(&args[1..]),
        Some("roles") => roles_mode(&args[1..]),
        Some("found") => found_mode(&args[1..]),
        Some("extend") => extend_mode(&args[1..]),
        Some("extend-joint") => extend_joint_mode(&args[1..]),
        Some("refuse") => refuse_mode(&args[1..]),
        Some("verify") => verify_mode(&args[1..]),
        Some("dismantle") => dismantle_mode(&args[1..]),
        Some("body") => body_mode(&args[1..]),
        Some("bodies") => bodies_mode(&args[1..]),
        Some("compare") => compare_mode(&args[1..]),
        Some("withdraw") => withdraw_mode(&args[1..]),
        Some("withdraw-on-body") => withdraw_on_body_mode(&args[1..]),
        _ => Err("mode: deed <root> <dir> [stage] [rest] | exposure | orders | roles | found | extend | extend-joint | verify | dismantle | body | refuse".into()),
    }
}
