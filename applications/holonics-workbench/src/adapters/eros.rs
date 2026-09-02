use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use holonic_engine::lean_development::{join, read_development, DeclarationGrain};
use life::exposure_codec::{ladder, ExposureApertures, LadderStop};
use life::material_incidence::{
    face_quotient, lean_atlas, prose_atlas, rust_atlas, rust_items_of_section, MaterialAtlas,
};
use serde_json::json;

use crate::adapters::AdapterReturn;
use crate::discovery::dominant_source_extension;
use crate::runtime::WorkbenchError;
use crate::ErosCommand;

pub fn execute(command: ErosCommand) -> Result<AdapterReturn, WorkbenchError> {
    match command {
        ErosCommand::Mouth {
            directory,
            extension,
            radius,
            scales,
            octet_budget,
        } => mouth(directory, extension, radius, scales, octet_budget),
        ErosCommand::Atlas {
            directory,
            extension,
            octet_budget,
        } => atlas(directory, extension, octet_budget),
    }
}

fn mouth(
    directory: PathBuf,
    mut extension: String,
    radius: usize,
    scales: usize,
    octet_budget: usize,
) -> Result<AdapterReturn, WorkbenchError> {
    if extension == "auto" {
        extension = dominant_source_extension(&directory)?;
    }
    let files = read_files(&directory, &extension)?;
    let mut carried = 0usize;
    let exposures = files
        .iter()
        .filter_map(|(_, octets)| {
            if carried + octets.len() > octet_budget {
                None
            } else {
                carried += octets.len();
                Some(octets.clone())
            }
        })
        .collect::<Vec<_>>();
    if exposures.is_empty() {
        return Err(WorkbenchError::Owner(
            "the declared octet budget admits no complete exposure".to_owned(),
        ));
    }
    let returned = ladder(
        exposures,
        ExposureApertures::declared(radius, 8_000_000),
        scales,
    )
    .map_err(|error| WorkbenchError::Owner(error.to_string()))?;
    let rungs = returned
        .rungs
        .iter()
        .map(|rung| {
            json!({
                "scale": rung.scale,
                "candidates": rung.candidates,
                "alphabet": rung.recovery.alphabet.len(),
                "refusals": rung.recovery.refusals.len(),
                "founded_units": rung.founded_units.len(),
                "parts": rung.parts,
                "compound_units": rung.founded_units.iter().filter(|unit| unit.len() > 1).take(16).map(|unit| String::from_utf8_lossy(unit).into_owned()).collect::<Vec<_>>()
            })
        })
        .collect::<Vec<_>>();
    let stop = match returned.stopped {
        LadderStop::NoCoarsening { scale } => format!("no-coarsening at scale {scale}"),
        LadderStop::Obstructed {
            scale,
            obstructions,
        } => format!("obstructed at scale {scale}: {obstructions:?}"),
        LadderStop::Refused {
            scale,
            candidates,
            refusal,
        } => format!("refused at scale {scale} over {candidates} candidates: {refusal}"),
        LadderStop::CeilingReached { scales } => format!("ceiling reached at {scales} scales"),
    };
    Ok(AdapterReturn::consequence(
        "eros/mouth",
        format!(
            "recovered {} rung(s) from {} complete file exposure(s), {carried} octets",
            rungs.len(),
            files.len()
        ),
        json!({
            "directory": directory,
            "extension": extension,
            "files": files.len(),
            "carried_octets": carried,
            "radius": radius,
            "rungs": rungs,
            "stop": stop
        }),
    ))
}

fn atlas(
    directory: PathBuf,
    mut extension: String,
    octet_budget: usize,
) -> Result<AdapterReturn, WorkbenchError> {
    if extension == "auto" {
        extension = dominant_source_extension(&directory)?;
    }
    let atlas = atlas_of(&directory, &extension, octet_budget)?;
    let (heights, storage, top) = atlas.heights();
    let quotient = face_quotient(&atlas);
    let contacts = atlas
        .contacts()
        .iter()
        .take(32)
        .map(|contact| {
            json!({
                "from": atlas.constituents().get(contact.from),
                "species": contact.species.name(),
                "to": atlas.constituents().get(contact.to)
            })
        })
        .collect::<Vec<_>>();
    Ok(AdapterReturn::consequence(
        "eros/atlas",
        format!(
            "returned {} constituents, {} contacts, and top dependency height {top}",
            atlas.constituents().len(),
            atlas.contacts().len()
        ),
        json!({
            "directory": directory,
            "extension": extension,
            "constituents": atlas.constituents().len(),
            "contacts": atlas.contacts().len(),
            "heights": heights.len(),
            "storage_ordinals": storage.len(),
            "top_height": top,
            "rank_gauge": format!("{:?}", atlas.rank_gauge_orbit()),
            "first_contacts": contacts,
            "face_quotient": {
                "declared": quotient.declared,
                "blocks": quotient.blocks,
                "rounds": quotient.rounds,
                "enclosed_faces": quotient.enclosed_faces,
                "separators": quotient.separated
            }
        }),
    ))
}

fn read_files(root: &Path, extension: &str) -> Result<Vec<(String, Vec<u8>)>, WorkbenchError> {
    let mut found = Vec::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(here) = pending.pop() {
        let listing = fs::read_dir(&here).map_err(|error| WorkbenchError::Io {
            path: here.clone(),
            reason: error.to_string(),
        })?;
        for entry in listing.flatten() {
            let path = entry.path();
            if path.is_dir() {
                pending.push(path);
            } else if path.extension().and_then(|value| value.to_str()) == Some(extension) {
                let octets = fs::read(&path).map_err(|error| WorkbenchError::Io {
                    path: path.clone(),
                    reason: error.to_string(),
                })?;
                if !octets.is_empty() {
                    found.push((path.display().to_string(), octets));
                }
            }
        }
    }
    found.sort();
    if found.is_empty() {
        return Err(WorkbenchError::Owner(format!(
            "no .{extension} file under {}",
            root.display()
        )));
    }
    Ok(found)
}

fn atlas_of(root: &Path, extension: &str, budget: usize) -> Result<MaterialAtlas, WorkbenchError> {
    let files = read_files(root, extension)?;
    let mut carried = 0usize;
    match extension {
        "rs" => {
            let mut items = Vec::new();
            for (ordinal, (path, octets)) in files.iter().enumerate() {
                if carried + octets.len() > budget {
                    break;
                }
                carried += octets.len();
                items.extend(rust_items_of_section(
                    path,
                    ordinal as u64,
                    &String::from_utf8_lossy(octets),
                ));
            }
            rust_atlas(&items, files.len() as u64)
                .map_err(|error| WorkbenchError::Owner(format!("{error:?}")))
        }
        "lean" => {
            let mut readings = Vec::new();
            for (_, octets) in &files {
                if carried + octets.len() > budget {
                    break;
                }
                carried += octets.len();
                readings.push(read_development(
                    &String::from_utf8_lossy(octets),
                    DeclarationGrain::EveryTopLevelDeclaration,
                ));
            }
            let reading = join(readings);
            let recruitment = reading.declared_recruitment_qualified();
            let order = reading
                .declarations
                .iter()
                .filter(|form| !form.anonymous)
                .map(|form| form.qualified())
                .collect::<Vec<_>>();
            let open = reading
                .open_recruitment()
                .values()
                .map(|symbols| symbols.len() as u64)
                .sum();
            lean_atlas(
                &recruitment,
                &BTreeMap::new(),
                &order,
                open,
                files.len() as u64,
            )
            .map_err(|error| WorkbenchError::Owner(format!("{error:?}")))
        }
        _ => {
            let mut occurrences = Vec::new();
            for (path, octets) in &files {
                if carried + octets.len() > budget {
                    break;
                }
                carried += octets.len();
                occurrences.push((path.clone(), String::from_utf8_lossy(octets).into_owned()));
            }
            prose_atlas(&occurrences, 2)
                .map_err(|error| WorkbenchError::Owner(format!("{error:?}")))
        }
    }
}
