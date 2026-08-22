//! Narrow exterior admission for the M5 physical-fold occurrence.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use serde::Serialize;
use sha2::{Digest, Sha256};

pub const DESIGN_UUID: &str = "c29097fd-ea46-5842-8b8f-b38ad7e732ae";

const TABLE_MEMBERS: &[&str] = &[
    "README.md",
    "docs/COLUMNS.md",
    "docs/DATA_NOTES.md",
    "docs/INSILICO.md",
    "docs/LOOKUP_TABLES.md",
    "docs/PROVENANCE.md",
    "docs/WETLAB.md",
    "tables/design_summary.csv",
];

const STRUCTURE_MEMBERS: &[(&str, &str, &str)] = &[
    (
        "designed-free-rbx1.cif",
        "designs/RBX1/mythos_preview_multi_target_rbx1_rank05/designed/designed.cif",
        "ed57855f8acfd75efd9f534b8e6c95673a93c1de2635dd4608f3c7f25b34e09e",
    ),
    (
        "ptxv2-free-rbx1-seed2.cif",
        "designs/RBX1/mythos_preview_multi_target_rbx1_rank05/ptxv2/seed_2/model.cif",
        "a1cc83749c04e45da6ad269e5b65f8904bccd8fd18d55c632314310c380a6c3f",
    ),
    (
        "ptxv2-free-rbx1-seed2-pae.npz",
        "designs/RBX1/mythos_preview_multi_target_rbx1_rank05/ptxv2/seed_2/pae.npz",
        "46894290eaa3675dc0b189a8874e7d78d581d8306791195e95c39ffd0d3d3d0c",
    ),
    (
        "ptxv2-cul1-rbx1-seed0.cif",
        "designs/RBX1/mythos_preview_multi_target_rbx1_rank05/ptxv2_rbx1_cul1_zn/seed_0/model.cif",
        "8f8bb2f39beb8654bba4b095114ae7733125312ec8c2368e34518bcc118a2476",
    ),
    (
        "ptxv2-cul1-rbx1-seed0-pae.npz",
        "designs/RBX1/mythos_preview_multi_target_rbx1_rank05/ptxv2_rbx1_cul1_zn/seed_0/pae.npz",
        "9721930cfea81ed18ff18a0564b65e6d9349d7a90bee2f632ea0b838532e4a3f",
    ),
];

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SourceMember {
    pub local_path: String,
    pub release_path: String,
    pub octets: u64,
    pub sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AssayOccurrence {
    pub vendor: String,
    pub presented_form: String,
    pub response: String,
    pub quantitative_face: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AdmittedFamily {
    pub schema: String,
    pub uuid: String,
    pub full_name: String,
    pub target: String,
    pub design_model: String,
    pub design_model_status: String,
    pub rank: u32,
    pub binder_length: usize,
    pub binder_sequence: String,
    pub designed_epitope: Vec<String>,
    pub table_vendor_agreement: String,
    pub assays: Vec<AssayOccurrence>,
    pub documentation_founds_target_form_shift: bool,
    pub selection_law: String,
    pub exterior_testimony_boundary: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct InputMount {
    pub schema: String,
    pub table_root: String,
    pub structure_root: String,
    pub table_archive: SourceMember,
    pub table_members: Vec<SourceMember>,
    pub structure_manifest: SourceMember,
    pub structure_members: Vec<SourceMember>,
    pub family: AdmittedFamily,
    #[serde(skip)]
    pub table_root_path: PathBuf,
    #[serde(skip)]
    pub structure_root_path: PathBuf,
}

pub fn mount() -> Result<InputMount, String> {
    let table_root = std::env::var_os("HOLONICS_M5_TABLE_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            PathBuf::from(
                "/home/b/Downloads/holonics-m5-protein-binder-docs-tables/protein_binder_design_data_release",
            )
        });
    let structure_root = std::env::var_os("HOLONICS_M5_STRUCTURE_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/home/b/Downloads/holonics-m5-rbx1-rank05"));
    if !table_root.is_dir() || !structure_root.is_dir() {
        return Err(format!(
            "M5 source roots are absent: table={} structure={}",
            table_root.display(),
            structure_root.display()
        ));
    }
    let table_archive_path = std::env::var_os("HOLONICS_M5_TABLE_ARCHIVE")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            PathBuf::from("/home/b/Downloads/protein_binder_design_data_release_docs_tables.zip")
        });
    let table_archive = authenticate(
        &table_archive_path,
        "protein_binder_design_data_release_docs_tables.zip",
        "bb7d45f9957bee70e715191566577d59e69363e42f18981aa96468b4b6547dec",
        None,
    )?;

    let table_manifest_path = table_root.join("MANIFEST.sha256");
    let table_manifest = read_manifest(&table_manifest_path)?;
    let mut table_members = Vec::new();
    for member in TABLE_MEMBERS {
        let (expected_hash, expected_octets) = table_manifest
            .get(*member)
            .ok_or_else(|| format!("table manifest does not address {member}"))?;
        table_members.push(authenticate(
            &table_root.join(member),
            member,
            expected_hash,
            Some(*expected_octets),
        )?);
    }

    let structure_manifest_path = structure_root.join("STRUCTURE_MANIFEST.sha256");
    let structure_manifest_hash = digest_path(&structure_manifest_path)?;
    if structure_manifest_hash
        != "39325f6b6627ff8021dc4509008c0217ca621dde9d44bab44866a51b34c92bdf"
    {
        return Err(format!(
            "the structure manifest occurrence changed: {structure_manifest_hash}"
        ));
    }
    let structure_manifest_text =
        std::fs::read_to_string(&structure_manifest_path).map_err(|error| error.to_string())?;
    let structure_manifest = structure_manifest_text
        .lines()
        .filter_map(|line| {
            let (hash, path) = line.split_once("  ")?;
            Some((path.trim().to_owned(), hash.trim().to_owned()))
        })
        .collect::<BTreeMap<_, _>>();
    let mut structure_members = Vec::new();
    for (local, release, expected) in STRUCTURE_MEMBERS {
        if structure_manifest.get(*release).map(String::as_str) != Some(*expected) {
            return Err(format!(
                "the official structure manifest does not bind {release} to {expected}"
            ));
        }
        structure_members.push(authenticate(
            &structure_root.join(local),
            release,
            expected,
            None,
        )?);
    }

    // The documentation/table tier is admitted before coordinates. It selects one occurrence by
    // its lineaged, cross-assay target-form disagreement; none of these labels routes geometry.
    let csv = std::fs::read_to_string(table_root.join("tables/design_summary.csv"))
        .map_err(|error| error.to_string())?;
    let records = parse_csv(&csv)?;
    let row = records
        .into_iter()
        .find(|row| row.get("uuid").map(String::as_str) == Some(DESIGN_UUID))
        .ok_or_else(|| format!("design_summary.csv has no occurrence {DESIGN_UUID}"))?;
    let required = |name: &str| -> Result<String, String> {
        row.get(name)
            .cloned()
            .ok_or_else(|| format!("the selected design row has no {name} face"))
    };
    if required("target")? != "RBX1"
        || required("adaptyv_binding")? != "binder"
        || required("twist_binding")? != "non_binder"
        || required("vendor_agreement")? != "adaptyv_only_bind"
    {
        return Err("the predeclared RBX1 target-form disagreement is absent".to_owned());
    }
    let binder_sequence = required("sequence")?;
    let binder_length = required("binder_length")?
        .parse::<usize>()
        .map_err(|error| error.to_string())?;
    if binder_sequence.len() != binder_length {
        return Err(format!(
            "the ordered binder sequence has {} octets but declares {binder_length} residues",
            binder_sequence.len()
        ));
    }
    let data_notes = std::fs::read_to_string(table_root.join("docs/DATA_NOTES.md"))
        .map_err(|error| error.to_string())?;
    let wetlab = std::fs::read_to_string(table_root.join("docs/WETLAB.md"))
        .map_err(|error| error.to_string())?;
    let documentation_founds_target_form_shift = data_notes.contains(
        "RBX1: free RBX1 at Adaptyv, CUL1-RBX1 complex at Twist",
    ) && wetlab.contains("RBX1 as the CUL1-RBX1 complex (Adaptyv used RBX1 alone)");
    if !documentation_founds_target_form_shift {
        return Err("the admitted documentation no longer founds the RBX1 form shift".to_owned());
    }
    let family = AdmittedFamily {
        schema: "holonics.m5.admitted-physical-family.v1".to_owned(),
        uuid: required("uuid")?,
        full_name: required("full_name")?,
        target: required("target")?,
        design_model: required("design_model")?,
        design_model_status: required("design_model_status")?,
        rank: required("rank")?
            .parse::<u32>()
            .map_err(|error| error.to_string())?,
        binder_length,
        binder_sequence,
        designed_epitope: required("epitope_residues")?
            .split(';')
            .map(str::to_owned)
            .collect(),
        table_vendor_agreement: required("vendor_agreement")?,
        assays: vec![
            AssayOccurrence {
                vendor: "Adaptyv Bio".to_owned(),
                presented_form: "free RBX1".to_owned(),
                response: required("adaptyv_binding")?,
                quantitative_face: format!(
                    "K_D={} nM; fit-bound status belongs to the exterior assay chart",
                    required("adaptyv_kd_nM")?
                ),
            },
            AssayOccurrence {
                vendor: "Twist Bioscience".to_owned(),
                presented_form: "CUL1-RBX1 complex".to_owned(),
                response: required("twist_binding")?,
                quantitative_face: "no fitted K_D in design_summary.csv".to_owned(),
            },
        ],
        documentation_founds_target_form_shift,
        selection_law: format!(
            "the documentation/table tier addressed UUID {DESIGN_UUID}: RBX1, Adaptyv binder, Twist non-binder, vendor_agreement=adaptyv_only_bind; only its designed, ptxv2 free and ptxv2 CUL1-RBX1 payloads were then mounted"
        ),
        exterior_testimony_boundary: "assay calls, predictor names, target labels and dataset assessments selected the occurrence and remain exterior testimony; exact incidence is derived only from authenticated coordinate/PAE payloads".to_owned(),
    };
    Ok(InputMount {
        schema: "holonics.m5.incremental-source-mount.v1".to_owned(),
        table_root: table_root.display().to_string(),
        structure_root: structure_root.display().to_string(),
        table_archive,
        table_members,
        structure_manifest: SourceMember {
            local_path: structure_manifest_path.display().to_string(),
            release_path: "STRUCTURE_MANIFEST.sha256".to_owned(),
            octets: std::fs::metadata(&structure_manifest_path)
                .map_err(|error| error.to_string())?
                .len(),
            sha256: structure_manifest_hash,
        },
        structure_members,
        family,
        table_root_path: table_root,
        structure_root_path: structure_root,
    })
}

fn authenticate(
    path: &Path,
    release_path: &str,
    expected_hash: &str,
    expected_octets: Option<u64>,
) -> Result<SourceMember, String> {
    let octets = std::fs::metadata(path)
        .map_err(|error| format!("stat {}: {error}", path.display()))?
        .len();
    if let Some(expected) = expected_octets {
        if octets != expected {
            return Err(format!(
                "{} has {octets} octets, manifest says {expected}",
                path.display()
            ));
        }
    }
    let sha256 = digest_path(path)?;
    if sha256 != expected_hash {
        return Err(format!(
            "{} has sha256 {sha256}, manifest says {expected_hash}",
            path.display()
        ));
    }
    Ok(SourceMember {
        local_path: path.display().to_string(),
        release_path: release_path.to_owned(),
        octets,
        sha256,
    })
}

fn read_manifest(path: &Path) -> Result<BTreeMap<String, (String, u64)>, String> {
    let text = std::fs::read_to_string(path).map_err(|error| error.to_string())?;
    text.lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            let mut fields = line.split_whitespace();
            let hash = fields.next().ok_or_else(|| "manifest hash absent".to_owned())?;
            let octets = fields
                .next()
                .ok_or_else(|| "manifest extent absent".to_owned())?
                .parse::<u64>()
                .map_err(|error| error.to_string())?;
            let member = fields.collect::<Vec<_>>().join(" ");
            Ok((member, (hash.to_owned(), octets)))
        })
        .collect()
}

pub fn digest_path(path: &Path) -> Result<String, String> {
    let bytes = std::fs::read(path).map_err(|error| error.to_string())?;
    Ok(Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect())
}

fn parse_csv(text: &str) -> Result<Vec<BTreeMap<String, String>>, String> {
    let mut rows = Vec::<Vec<String>>::new();
    let mut row = Vec::<String>::new();
    let mut field = String::new();
    let mut quoted = false;
    let mut chars = text.chars().peekable();
    while let Some(ch) = chars.next() {
        match ch {
            '"' if quoted && chars.peek() == Some(&'"') => {
                field.push('"');
                chars.next();
            }
            '"' => quoted = !quoted,
            ',' if !quoted => row.push(std::mem::take(&mut field)),
            '\n' if !quoted => {
                row.push(std::mem::take(&mut field));
                rows.push(std::mem::take(&mut row));
            }
            '\r' if !quoted => {}
            other => field.push(other),
        }
    }
    if quoted {
        return Err("design_summary.csv ends inside a quoted field".to_owned());
    }
    if !field.is_empty() || !row.is_empty() {
        row.push(field);
        rows.push(row);
    }
    let headers = rows
        .first()
        .cloned()
        .ok_or_else(|| "design_summary.csv is empty".to_owned())?;
    rows.into_iter()
        .skip(1)
        .map(|values| {
            if values.len() != headers.len() {
                return Err(format!(
                    "CSV row has {} fields under {} headers",
                    values.len(),
                    headers.len()
                ));
            }
            Ok(headers.iter().cloned().zip(values).collect())
        })
        .collect()
}
