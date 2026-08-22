//! Persist and grade the complete M5 return as inspectable exterior artifacts.

use std::path::{Path, PathBuf};
use std::process::Command;

use serde::{Deserialize, Serialize};

use super::fold::PhysicalFoldReturn;
use super::visual::{ExactMesh, derive};

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LeanReturn {
    pub schema: String,
    pub source_path: String,
    pub source_sha256: String,
    pub command: String,
    pub exit_status: i32,
    pub stdout: String,
    pub stderr: String,
    pub abstract_theorems: Vec<String>,
    pub theorem_bodies_contain_sorry: bool,
    pub accepted: bool,
    pub boundary: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GradeItem {
    pub requirement: String,
    pub passed: bool,
    pub evidence: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct M5Grade {
    pub schema: String,
    pub truth_status: String,
    pub passed: bool,
    pub score: String,
    pub items: Vec<GradeItem>,
    pub limits: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArtifactEntry {
    pub path: String,
    pub octets: u64,
    pub sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArtifactManifest {
    pub schema: String,
    pub root: String,
    pub entries: Vec<ArtifactEntry>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ArtifactReturn {
    pub root: String,
    pub grade: M5Grade,
    pub manifest: ArtifactManifest,
}

pub fn emit(returned: &PhysicalFoldReturn) -> Result<ArtifactReturn, String> {
    let repository = repository_root()?;
    let output = repository.join(
        "output/the_physical_fold_returns_as_an_exact_constraint_complex",
    );
    std::fs::create_dir_all(&output).map_err(|error| error.to_string())?;

    let visual = derive(
        &returned.cul1_rbx1_complex,
        returned.device_receipt.common_decimal_denominator,
    )?;
    let lean = lean_return(&repository)?;
    if !lean.accepted {
        return Err(format!("the abstract Lean return refused: {}", lean.stderr));
    }
    let grade = grade(returned, &visual.mesh, &lean)?;
    if !grade.passed {
        return Err("the assembled M5 grade is open".to_owned());
    }

    let cultivation_boundary = serde_json::json!({
        "schema": "holonics.m5.cultivation-boundary.v1",
        "cultivation_founded": returned.cultivation_founded,
        "consequence": returned.cultivation_consequence,
    });
    let summary = serde_json::json!({
        "schema": "holonics.m5.compact-return.v1",
        "truth_status": "[established-bounded]",
        "source_uuid": returned.source_mount.family.uuid,
        "source_design": returned.source_mount.family.full_name,
        "device": returned.device_receipt.device,
        "contact_population": returned.device_receipt.contact_population,
        "free_inside": inside_count(&returned.free_complex),
        "complex_binder_inside": family_inside(&returned.cul1_rbx1_complex, 0),
        "complex_accompanying_inside": family_inside(&returned.cul1_rbx1_complex, 1),
        "shared_inside": returned.cross_presentation_fibre.shared_inside.len(),
        "shared_outside": returned.cross_presentation_fibre.shared_outside.len(),
        "left_only_inside": returned.cross_presentation_fibre.left_only_inside.len(),
        "right_only_inside": returned.cross_presentation_fibre.right_only_inside.len(),
        "unresolved": returned.cross_presentation_fibre.unresolved.len(),
        "shortest_separator": returned.cross_presentation_fibre.shortest_separator,
        "shared_higher_faces": returned.higher_face_invariant.shared_faces.len(),
        "free_higher_faces": returned.free_complex.faces.len(),
        "complex_higher_faces": returned.cul1_rbx1_complex.faces.len(),
        "environment_response_changed": returned.environment_return.response_changed,
        "binder_contact_fibre_reopened": returned.environment_return.binder_contact_fibre_reopened,
        "lean_accepted": lean.accepted,
        "visual_incidence_preserved": visual.mesh.incidence_preserved,
        "cultivation_founded": returned.cultivation_founded,
    });

    let mut paths = Vec::new();
    paths.push(write_json(&output, "00-summary.json", &summary)?);
    paths.push(write_json(&output, "01-source-mount.json", &returned.source_mount)?);
    paths.push(write_json(
        &output,
        "02-coordinate-presentations.json",
        &returned.coordinate_presentations,
    )?);
    paths.push(write_json(
        &output,
        "03-uncertainty-presentations.json",
        &returned.uncertainty_presentations,
    )?);
    paths.push(write_json(&output, "04-device-receipt.json", &returned.device_receipt)?);
    paths.push(write_json(
        &output,
        "05-designed-contact-face.json",
        &returned.designed_contact_face,
    )?);
    paths.push(write_ron(
        &output,
        "06-free-constraint-complex.ron",
        &returned.free_complex,
    )?);
    paths.push(write_ron(
        &output,
        "07-cul1-rbx1-constraint-complex.ron",
        &returned.cul1_rbx1_complex,
    )?);
    paths.push(write_json(
        &output,
        "08-cross-presentation-fibre.json",
        &returned.cross_presentation_fibre,
    )?);
    paths.push(write_json(
        &output,
        "09-higher-face-invariant.json",
        &returned.higher_face_invariant,
    )?);
    paths.push(write_json(
        &output,
        "10-environment-return.json",
        &returned.environment_return,
    )?);
    paths.push(write_json(
        &output,
        "11-cultivation-boundary.json",
        &cultivation_boundary,
    )?);
    paths.push(write_json(&output, "12-lean-return.json", &lean)?);
    paths.push(write_json(&output, "13-exact-mesh.json", &visual.mesh)?);
    let svg_path = output.join("14-complex.svg");
    std::fs::write(&svg_path, visual.svg.as_bytes()).map_err(|error| error.to_string())?;
    paths.push(svg_path);
    paths.push(write_json(&output, "15-grade.json", &grade)?);

    let entries = paths
        .iter()
        .map(|path| {
            Ok(ArtifactEntry {
                path: path
                    .strip_prefix(&repository)
                    .map_err(|error| error.to_string())?
                    .display()
                    .to_string(),
                octets: std::fs::metadata(path)
                    .map_err(|error| error.to_string())?
                    .len(),
                sha256: super::input::digest_path(path)?,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let manifest = ArtifactManifest {
        schema: "holonics.m5.artifact-manifest.v1".to_owned(),
        root: output
            .strip_prefix(&repository)
            .map_err(|error| error.to_string())?
            .display()
            .to_string(),
        entries,
    };
    write_json(&output, "MANIFEST.json", &manifest)?;
    Ok(ArtifactReturn {
        root: output.display().to_string(),
        grade,
        manifest,
    })
}

pub fn refresh_visual() -> Result<String, String> {
    let repository = repository_root()?;
    let output = repository.join(
        "output/the_physical_fold_returns_as_an_exact_constraint_complex",
    );
    let complex_file = std::fs::File::open(output.join("07-cul1-rbx1-constraint-complex.ron"))
        .map_err(|error| error.to_string())?;
    let complex: holonic_engine::physical_constraint_complex::PhysicalConstraintComplex =
        ron::de::from_reader(complex_file).map_err(|error| error.to_string())?;
    let device: super::fold::DeviceContactReceipt = serde_json::from_reader(
        std::fs::File::open(output.join("04-device-receipt.json"))
            .map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let visual = derive(&complex, device.common_decimal_denominator)?;
    let mesh_path = write_json(&output, "13-exact-mesh.json", &visual.mesh)?;
    let svg_path = output.join("14-complex.svg");
    std::fs::write(&svg_path, visual.svg.as_bytes()).map_err(|error| error.to_string())?;

    let manifest_path = output.join("MANIFEST.json");
    let mut manifest: ArtifactManifest = serde_json::from_reader(
        std::fs::File::open(&manifest_path).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    for path in [&mesh_path, &svg_path] {
        let relative = path
            .strip_prefix(&repository)
            .map_err(|error| error.to_string())?
            .display()
            .to_string();
        let entry = manifest
            .entries
            .iter_mut()
            .find(|entry| entry.path == relative)
            .ok_or_else(|| format!("the artifact manifest has no {relative}"))?;
        entry.octets = std::fs::metadata(path)
            .map_err(|error| error.to_string())?
            .len();
        entry.sha256 = super::input::digest_path(path)?;
    }
    write_json(&output, "MANIFEST.json", &manifest)?;
    Ok(output.display().to_string())
}

fn lean_return(repository: &Path) -> Result<LeanReturn, String> {
    let formal = repository.join("soma/formal/elementary-holonics");
    let relative = Path::new("ElementaryHolonics/Millennium/Rigidity.lean");
    let source = formal.join(relative);
    let text = std::fs::read_to_string(&source).map_err(|error| error.to_string())?;
    let abstract_theorems = [
        "theSharedJunctionFibreIsTheIntersection",
        "removingTheSecondConstraintCanOnlyEnlargeTheFibre",
        "aContinuationSeenOnlyByTheSecondConstraintIsASeparator",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect::<Vec<_>>();
    for theorem in &abstract_theorems {
        if !text.contains(&format!("theorem {theorem}")) {
            return Err(format!("the M5 Lean source has no abstract theorem {theorem}"));
        }
    }
    let theorem_start = text
        .find("theorem theSharedJunctionFibreIsTheIntersection")
        .ok_or_else(|| "the shared-junction theorem body is absent".to_owned())?;
    let theorem_bodies_contain_sorry = text[theorem_start..]
        .lines()
        .any(|line| line.split_whitespace().any(|word| word == "sorry" || word == "admit"));
    let output = Command::new("lake")
        .args(["env", "lean", relative.to_string_lossy().as_ref()])
        .current_dir(&formal)
        .output()
        .map_err(|error| error.to_string())?;
    let exit_status = output.status.code().unwrap_or(-1);
    Ok(LeanReturn {
        schema: "holonics.m5.abstract-lean-return.v1".to_owned(),
        source_path: source
            .strip_prefix(repository)
            .map_err(|error| error.to_string())?
            .display()
            .to_string(),
        source_sha256: super::input::digest_path(&source)?,
        command: format!("cd {} && lake env lean {}", formal.display(), relative.display()),
        exit_status,
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        abstract_theorems,
        theorem_bodies_contain_sorry,
        accepted: output.status.success() && !theorem_bodies_contain_sorry,
        boundary: "Lean checks the abstract linear shared-junction/intersection and separator laws. It does not certify the protein occurrence, CUDA execution, coordinate payload, or assay testimony.".to_owned(),
    })
}

fn grade(
    returned: &PhysicalFoldReturn,
    mesh: &ExactMesh,
    lean: &LeanReturn,
) -> Result<M5Grade, String> {
    let fibre_population = returned.cross_presentation_fibre.shared_inside.len()
        + returned.cross_presentation_fibre.shared_outside.len()
        + returned.cross_presentation_fibre.left_only_inside.len()
        + returned.cross_presentation_fibre.right_only_inside.len()
        + returned.cross_presentation_fibre.unresolved.len();
    let contact_population = returned.free_complex.contact_families[0].readings.len();
    let items = vec![
        item(
            "exact addressed source and uncertainty lineage",
            returned.source_mount.structure_members.len() == 5
                && returned
                    .uncertainty_presentations
                    .iter()
                    .all(|atlas| atlas.refused_nonfinite_words == 0),
            "authenticated docs/table archive, member manifests, five addressed structure payloads and every finite binary16 PAE word",
        ),
        item(
            "complete constraint complex, boundary, chart changes and fibres",
            !returned.free_complex.vertices.is_empty()
                && returned.cul1_rbx1_complex.contact_families.len() == 2
                && fibre_population == contact_population
                && returned.device_receipt.resident_decimal_places
                    <= returned.device_receipt.source_maximum_decimal_places,
            "both predictor-backed occurrences retain all contact classes and PAE words; polygonal and higher incidence, algebraic boundary, source-to-resident chart aperture and every cross-presentation pair class are returned",
        ),
        item(
            "nontrivial invariant and shortest separator",
            !returned.cross_presentation_fibre.shared_inside.is_empty()
                && !returned.higher_face_invariant.shared_faces.is_empty()
                && returned.cross_presentation_fibre.shortest_separator.is_some(),
            "shared contact and two-cell populations are nonempty; the first lexicographic class disagreement is exhibited",
        ),
        item(
            "environment/assay change or explicit refusal",
            returned.environment_return.response_changed
                && returned.environment_return.binder_contact_fibre_reopened
                && !returned.environment_return.refusal.is_empty(),
            "free-RBX1 binder versus CUL1-RBX1 non-binder testimony and an exact structural reopening return together, with molecular causation explicitly refused",
        ),
        item(
            "GPU-resident held-out conduct with telemetry separated",
            returned.device_receipt.contact_population > 0
                && returned.device_receipt.paired_population == contact_population
                && returned.device_receipt.launches == 2
                && returned.device_receipt.terminal_synchronizations == 1,
            "all contact classes and the matched ordered-pair successor execute as two kernels under one terminal synchronization; exact semantic audit and apparatus counts have separate fields",
        ),
        item(
            "detached remount and ablation if cultivation is founded",
            !returned.cultivation_founded,
            "no durable morphology was changed, so the conditional remount/ablation obligation is not founded and no counterfeit training claim is made",
        ),
        item(
            "abstract Lean shared-junction/transport return",
            lean.accepted && !lean.theorem_bodies_contain_sorry,
            "Lean accepts ker(F.prod G)=ker F inf ker G, monotone enlargement on removal, and an abstract separating continuation",
        ),
        item(
            "vector/mesh derived from exact complex with gauge-safe incidence",
            mesh.incidence_preserved
                && mesh.topology_sha256_before == mesh.topology_sha256_after
                && !mesh.vertices.is_empty()
                && !mesh.triangles.is_empty(),
            "the mesh and SVG project the same addressed vertices/edges/faces; an exact nonzero translation changes coordinates while the complete topology digest remains identical",
        ),
    ];
    let passed = items.iter().all(|item| item.passed);
    Ok(M5Grade {
        schema: "holonics.m5.complete-grade.v1".to_owned(),
        truth_status: "[established-bounded]".to_owned(),
        passed,
        score: format!("{}/{}", items.iter().filter(|item| item.passed).count(), items.len()),
        items,
        limits: vec![
            "The contact receiver is C-alpha distance not greater than eight angstroms under explicit outward coordinate intervals; it is not binding energy or atom-complete chemistry.".to_owned(),
            "PAE is exact testimony about stored predictor words, not a physical measurement or a coordinate enclosure.".to_owned(),
            "Assay and structural co-variation do not prove why binding changed; the causal fibre remains open.".to_owned(),
            "Only one lineaged RBX1 design and two predicted presentations are graded; no general protein-folding capability is claimed.".to_owned(),
            "No cultivation occurred, so M5 establishes transport of the calculus into one physical constraint ecology, not learned reusable protein conduct.".to_owned(),
        ],
    })
}

fn item(requirement: &str, passed: bool, evidence: &str) -> GradeItem {
    GradeItem {
        requirement: requirement.to_owned(),
        passed,
        evidence: evidence.to_owned(),
    }
}

fn inside_count(complex: &holonic_engine::physical_constraint_complex::PhysicalConstraintComplex) -> usize {
    complex
        .contact_families
        .iter()
        .map(|family| {
            family
                .readings
                .iter()
                .filter(|reading| {
                    reading.class
                        == holonic_engine::physical_constraint_complex::ContactClass::Inside
                })
                .count()
        })
        .sum()
}

fn family_inside(
    complex: &holonic_engine::physical_constraint_complex::PhysicalConstraintComplex,
    family: usize,
) -> usize {
    complex.contact_families[family]
        .readings
        .iter()
        .filter(|reading| {
            reading.class == holonic_engine::physical_constraint_complex::ContactClass::Inside
        })
        .count()
}

fn write_json<T: Serialize>(directory: &Path, name: &str, value: &T) -> Result<PathBuf, String> {
    let path = directory.join(name);
    let file = std::fs::File::create(&path).map_err(|error| error.to_string())?;
    serde_json::to_writer_pretty(file, value).map_err(|error| error.to_string())?;
    Ok(path)
}

fn write_ron<T: Serialize>(directory: &Path, name: &str, value: &T) -> Result<PathBuf, String> {
    let path = directory.join(name);
    let file = std::fs::File::create(&path).map_err(|error| error.to_string())?;
    ron::Options::default()
        .to_io_writer(file, value)
        .map_err(|error| error.to_string())?;
    Ok(path)
}

fn repository_root() -> Result<PathBuf, String> {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .map(Path::to_owned)
        .ok_or_else(|| "the life package is not inside the repository root".to_owned())
}
