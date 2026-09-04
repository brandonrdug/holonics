//! M6 / Athena-A0 — the total descent route cultivates the first Athena mathematics variant.
//!
//! This executable currently closes the source-occurrence and exact Lean operation/state-return
//! stations of the one indivisible M6 deed.  It deliberately does not print `M6 PASSED`: the total case cover,
//! independent theorem emission, returned cultivation, sibling comparison and product rest remain
//! obligations of the same deed.
//!
//! Owners composed here:
//! - the content-addressed source occurrence in `m6::source`;
//! - the project-owned exterior Lean causal return for declaration operations and proof states;
//! - `returned_contact_cuda` for the resident founded-junction return.
//!
//! The event is the productive child's opening of the addressed S0 file population.  Its source
//! port is `/source`, its product port `/product`, its predecessor the manifest occurrence, and its
//! consequence the exact incidence plus resident grouping.  Git, Lean, the S0 build cache, current
//! repository state and the withheld teacher passage are outside this process.

use std::{
    fs,
    os::unix::fs::symlink,
    path::{Path, PathBuf},
    process::Command,
    time::Instant,
};

use serde::Serialize;

#[path = "m6/athena.rs"]
mod athena;
#[path = "m6/case.rs"]
mod case;
#[path = "m6/causal.rs"]
mod causal;
#[path = "m6/incidence.rs"]
mod incidence;
#[path = "m6/route.rs"]
mod route;
#[path = "m6/source.rs"]
mod source;
#[path = "m6/visual.rs"]
mod visual;

#[derive(Debug)]
enum Mode {
    Enact {
        workspace: PathBuf,
        output: PathBuf,
    },
    FromAddressed {
        workspace: PathBuf,
        addressed: PathBuf,
        output: PathBuf,
    },
    FinalizeAddressed {
        workspace: PathBuf,
        addressed: PathBuf,
        output: PathBuf,
    },
    Produce {
        source: PathBuf,
        causal: PathBuf,
        product: PathBuf,
        m3_rest: PathBuf,
        m4_rest: PathBuf,
    },
    Infer {
        rest: PathBuf,
        destination: PathBuf,
    },
    Regrade {
        output: PathBuf,
    },
}

#[derive(Debug, Serialize)]
struct SourceAccessReturn {
    schema: String,
    productive_process_repository_mounted: bool,
    productive_process_lean_cache_mounted: bool,
    productive_process_git_mounted: bool,
    source_occurrence: String,
    withheld_revision: String,
    withheld_added_source_faces: Vec<WithheldSourceFace>,
    opened_paths: Vec<String>,
    opened_path_population: usize,
    mount_namespace: String,
    claim: String,
}

#[derive(Debug, Serialize)]
struct WithheldSourceFace {
    relative_path: String,
    git_blob: String,
    sha256: String,
    absent_from_productive_mount: bool,
    blob_absent_from_productive_mount: bool,
}

#[derive(Debug, Serialize)]
struct LeanCheckReturn {
    source_path: String,
    source_sha256: String,
    command: Vec<String>,
    code_closure: Vec<String>,
    elapsed_milliseconds: u128,
    exit_status: i32,
    stdout: String,
    stderr: String,
    source_contains_sorry: bool,
    accepted: bool,
}

#[derive(Debug, Serialize)]
struct ArtifactEntry {
    path: String,
    octets: u64,
    sha256: String,
}

#[derive(Debug, Serialize)]
struct GradeItem {
    ordinal: u8,
    requirement: String,
    passed: bool,
    evidence: Vec<String>,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    match arguments()? {
        Mode::Enact { workspace, output } => enact(&workspace, &output),
        Mode::FromAddressed {
            workspace,
            addressed,
            output,
        } => from_addressed(&workspace, &addressed, &output),
        Mode::FinalizeAddressed {
            workspace,
            addressed,
            output,
        } => finalize_addressed(&workspace, &addressed, &output),
        Mode::Produce {
            source,
            causal,
            product,
            m3_rest,
            m4_rest,
        } => produce(&source, &causal, &product, &m3_rest, &m4_rest),
        Mode::Infer { rest, destination } => infer(&rest, &destination),
        Mode::Regrade { output } => regrade(&output),
    }
}

fn arguments() -> Result<Mode, String> {
    let mut args = std::env::args().skip(1);
    match args.next().as_deref() {
        Some("--enact") => {
            let workspace = args
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "--enact requires WORKSPACE OUTPUT".to_owned())?;
            let output = args
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "--enact requires WORKSPACE OUTPUT".to_owned())?;
            if args.next().is_some() {
                return Err("unexpected --enact argument".to_owned());
            }
            Ok(Mode::Enact { workspace, output })
        }
        Some("--produce") => {
            let source = args
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "--produce requires SOURCE CAUSAL PRODUCT".to_owned())?;
            let causal = args
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "--produce requires SOURCE CAUSAL PRODUCT".to_owned())?;
            let product = args
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "--produce requires SOURCE CAUSAL PRODUCT M3_REST M4_REST".to_owned())?;
            let m3_rest = args
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "--produce requires SOURCE CAUSAL PRODUCT M3_REST M4_REST".to_owned())?;
            let m4_rest = args
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "--produce requires SOURCE CAUSAL PRODUCT M3_REST M4_REST".to_owned())?;
            if args.next().is_some() {
                return Err("unexpected --produce argument".to_owned());
            }
            Ok(Mode::Produce {
                source,
                causal,
                product,
                m3_rest,
                m4_rest,
            })
        }
        Some("--from-addressed") => {
            let workspace = args
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "--from-addressed requires WORKSPACE ADDRESSED OUTPUT".to_owned())?;
            let addressed = args
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "--from-addressed requires WORKSPACE ADDRESSED OUTPUT".to_owned())?;
            let output = args
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "--from-addressed requires WORKSPACE ADDRESSED OUTPUT".to_owned())?;
            if args.next().is_some() {
                return Err("unexpected --from-addressed argument".to_owned());
            }
            Ok(Mode::FromAddressed {
                workspace,
                addressed,
                output,
            })
        }
        Some("--infer") => {
            let rest = args
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "--infer requires REST DESTINATION".to_owned())?;
            let destination = args
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "--infer requires REST DESTINATION".to_owned())?;
            if args.next().is_some() {
                return Err("unexpected --infer argument".to_owned());
            }
            Ok(Mode::Infer { rest, destination })
        }
        Some("--finalize-addressed") => {
            let workspace = args
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "--finalize-addressed requires WORKSPACE ADDRESSED OUTPUT".to_owned())?;
            let addressed = args
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "--finalize-addressed requires WORKSPACE ADDRESSED OUTPUT".to_owned())?;
            let output = args
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "--finalize-addressed requires WORKSPACE ADDRESSED OUTPUT".to_owned())?;
            if args.next().is_some() {
                return Err("unexpected --finalize-addressed argument".to_owned());
            }
            Ok(Mode::FinalizeAddressed {
                workspace,
                addressed,
                output,
            })
        }
        Some("--regrade") => {
            let output = args
                .next()
                .map(PathBuf::from)
                .ok_or_else(|| "--regrade requires OUTPUT".to_owned())?;
            if args.next().is_some() {
                return Err("unexpected --regrade argument".to_owned());
            }
            Ok(Mode::Regrade { output })
        }
        _ => Err("usage: --enact WORKSPACE OUTPUT | --from-addressed WORKSPACE ADDRESSED OUTPUT | --finalize-addressed WORKSPACE ADDRESSED OUTPUT | --infer REST DESTINATION | --regrade OUTPUT (the productive --produce mode is apparatus-owned)".to_owned()),
    }
}

fn enact(workspace: &Path, output: &Path) -> Result<(), String> {
    let workspace = workspace
        .canonicalize()
        .map_err(|error| format!("resolve {}: {error}", workspace.display()))?;
    if output.exists() {
        return Err(format!("M6 output already exists: {}", output.display()));
    }
    fs::create_dir_all(output).map_err(|error| format!("create {}: {error}", output.display()))?;
    let output = output
        .canonicalize()
        .map_err(|error| format!("resolve {}: {error}", output.display()))?;
    let source_root = output.join("apparatus/source-s0");
    let causal_root = output.join("apparatus/causal-return");
    let product_root = output.join("product");
    let m3_rest = workspace.join(
        ".local/artifacts/the_active_cover_condenses_into_a_generator_native_codec/generator-native-rest.json",
    );
    let m4_rest = workspace.join(
        ".local/artifacts/the_native_codec_is_cultivated_and_returns_complete_mathematics/cultivated-receiver-history-rest.json",
    );
    for inherited in [&m3_rest, &m4_rest] {
        if !inherited.is_file() {
            return Err(format!(
                "the inherited Athena organ is absent: {}",
                inherited.display()
            ));
        }
    }
    fs::create_dir_all(&product_root)
        .map_err(|error| format!("create {}: {error}", product_root.display()))?;
    let manifest = source::prepare(&workspace, &source_root)?;
    let causal_manifest = causal::prepare(&workspace, &source_root, &manifest, &causal_root)?;

    launch_productive(
        &source_root,
        &causal_root,
        &product_root,
        &m3_rest,
        &m4_rest,
    )?;
    finalize_source_access(&workspace, &manifest, &causal_manifest, &product_root)?;
    complete_exterior(&workspace, &causal_root, &product_root, &m3_rest, &m4_rest)?;
    println!(
        "M6 RETURNED — source {}, product {}",
        manifest.occurrence,
        product_root.display()
    );
    Ok(())
}

fn launch_productive(
    source_root: &Path,
    causal_root: &Path,
    product_root: &Path,
    m3_rest: &Path,
    m4_rest: &Path,
) -> Result<(), String> {
    let executable = std::env::current_exe()
        .map_err(|error| format!("locate productive executable: {error}"))?
        .canonicalize()
        .map_err(|error| format!("resolve productive executable: {error}"))?;
    let mut command = Command::new("bwrap");
    command
        .args(["--die-with-parent", "--unshare-all"])
        .args(["--ro-bind", "/usr", "/usr"])
        .args(["--ro-bind", "/etc", "/etc"])
        .args(["--ro-bind", "/sys", "/sys"])
        .args(["--dev-bind", "/dev", "/dev"])
        .args(["--proc", "/proc"])
        .args(["--tmpfs", "/tmp"]);
    for library in ["/lib", "/lib64", "/run"] {
        if Path::new(library).exists() {
            command.args(["--ro-bind", library, library]);
        }
    }
    command
        .arg("--ro-bind")
        .arg(&executable)
        .arg("/athena-a0")
        .arg("--ro-bind")
        .arg(&source_root)
        .arg("/source")
        .arg("--ro-bind")
        .arg(&causal_root)
        .arg("/causal")
        .arg("--bind")
        .arg(&product_root)
        .arg("/product")
        .args(["--dir", "/ancestry"])
        .arg("--ro-bind")
        .arg(&m3_rest)
        .arg("/ancestry/m3-rest.json")
        .arg("--ro-bind")
        .arg(&m4_rest)
        .arg("/ancestry/m4-rest.json")
        .args([
            "--chdir",
            "/tmp",
            "/athena-a0",
            "--produce",
            "/source",
            "/causal",
            "/product",
            "/ancestry/m3-rest.json",
            "/ancestry/m4-rest.json",
        ]);
    let status = command
        .status()
        .map_err(|error| format!("enter productive mount namespace: {error}"))?;
    if !status.success() {
        return Err(format!("the productive mount namespace returned {status}"));
    }

    Ok(())
}

fn from_addressed(workspace: &Path, addressed: &Path, output: &Path) -> Result<(), String> {
    let workspace = workspace
        .canonicalize()
        .map_err(|error| format!("resolve {}: {error}", workspace.display()))?;
    let addressed = addressed
        .canonicalize()
        .map_err(|error| format!("resolve {}: {error}", addressed.display()))?;
    if output.exists() {
        return Err(format!("M6 output already exists: {}", output.display()));
    }
    fs::create_dir_all(output).map_err(|error| format!("create {}: {error}", output.display()))?;
    let output = output
        .canonicalize()
        .map_err(|error| format!("resolve {}: {error}", output.display()))?;
    let source_root = addressed.join("apparatus/source-s0");
    let causal_root = addressed.join("apparatus/causal-return");
    let product_root = output.join("product");
    fs::create_dir_all(&product_root)
        .map_err(|error| format!("create {}: {error}", product_root.display()))?;
    let source = source::mount(&source_root)?;
    let causal = causal::mount(&causal_root)?;
    if source.manifest.occurrence != causal.manifest.source_occurrence {
        return Err(
            "the addressed source and causal return do not share one occurrence".to_owned(),
        );
    }
    let m3_rest = workspace.join(
        ".local/artifacts/the_active_cover_condenses_into_a_generator_native_codec/generator-native-rest.json",
    );
    let m4_rest = workspace.join(
        ".local/artifacts/the_native_codec_is_cultivated_and_returns_complete_mathematics/cultivated-receiver-history-rest.json",
    );
    for inherited in [&m3_rest, &m4_rest] {
        if !inherited.is_file() {
            return Err(format!(
                "the inherited Athena organ is absent: {}",
                inherited.display()
            ));
        }
    }
    launch_productive(
        &source_root,
        &causal_root,
        &product_root,
        &m3_rest,
        &m4_rest,
    )?;
    finalize_source_access(
        &workspace,
        &source.manifest,
        &causal.manifest,
        &product_root,
    )?;
    complete_exterior(&workspace, &causal_root, &product_root, &m3_rest, &m4_rest)?;
    println!(
        "M6 RETURNED FROM ADDRESSED CAUSAL TESTIMONY — source {}, product {}",
        source.manifest.occurrence,
        product_root.display()
    );
    Ok(())
}

fn finalize_addressed(workspace: &Path, addressed: &Path, output: &Path) -> Result<(), String> {
    let workspace = workspace
        .canonicalize()
        .map_err(|error| format!("resolve {}: {error}", workspace.display()))?;
    let addressed = addressed
        .canonicalize()
        .map_err(|error| format!("resolve {}: {error}", addressed.display()))?;
    let output = output
        .canonicalize()
        .map_err(|error| format!("resolve {}: {error}", output.display()))?;
    let causal_root = addressed.join("apparatus/causal-return");
    let product_root = output.join("product");
    for required in [
        "00-source-occurrence.json",
        "01-negative-source-access.json",
        "06-total-case-complex.json",
        "07-resident-case-junction-return.json",
        "09-athena-generated-face-homomorphism.lean",
        "10-cultivated-held-out-successor.lean",
        "12-native-phoenix-siblings.json",
        "18-exact-route-work-and-fibre.json",
    ] {
        if !product_root.join(required).is_file() {
            return Err(format!(
                "the addressed productive return is absent: {required}"
            ));
        }
    }
    let m3_rest = workspace.join(
        ".local/artifacts/the_active_cover_condenses_into_a_generator_native_codec/generator-native-rest.json",
    );
    let m4_rest = workspace.join(
        ".local/artifacts/the_native_codec_is_cultivated_and_returns_complete_mathematics/cultivated-receiver-history-rest.json",
    );
    complete_exterior(&workspace, &causal_root, &product_root, &m3_rest, &m4_rest)?;
    println!("M6 EXTERIOR RETURN FINALIZED — {}", product_root.display());
    Ok(())
}

fn complete_exterior(
    workspace: &Path,
    causal_root: &Path,
    product_root: &Path,
    m3_rest: &Path,
    m4_rest: &Path,
) -> Result<(), String> {
    let negative_access = product_root.join("01-negative-source-access.json");
    if !negative_access.is_file() {
        return Err("the productive return has no negative T0 access receipt".to_owned());
    }
    let primary = product_root.join("09-athena-generated-face-homomorphism.lean");
    let held_out = product_root.join("10-cultivated-held-out-successor.lean");
    let lean_root = causal_root
        .parent()
        .ok_or_else(|| "the causal return has no S0 apparatus parent".to_owned())?
        .join("lean-s0");
    if !lean_root.is_dir() {
        return Err(format!(
            "the addressed S0 checker root is absent: {}",
            lean_root.display()
        ));
    }
    let comparison_root = product_root
        .parent()
        .ok_or_else(|| "the product has no output occurrence".to_owned())?
        .join("apparatus/post-emission-s0");
    prepare_post_emission_root(&lean_root, &comparison_root)?;
    let comparison_module_root = comparison_root.join("ElementaryHolonics/Millennium");
    let primary_module = comparison_module_root.join("M6GeneratedPrimary.lean");
    let held_out_module = comparison_module_root.join("M6CultivatedHeldOut.lean");
    fs::copy(&primary, &primary_module)
        .map_err(|error| format!("mount emitted primary in the comparison chart: {error}"))?;
    fs::copy(&held_out, &held_out_module).map_err(|error| {
        format!("mount emitted held-out passage in the comparison chart: {error}")
    })?;
    let causal_manifest = fs::read(causal_root.join(causal::MANIFEST))
        .map_err(|error| format!("read causal closure for theorem checking: {error}"))?;
    let closure = source::sha256(&causal_manifest);

    // These checks happen before the withheld proof is opened.  A refusal returns immediately and
    // therefore cannot be repaired by teacher testimony later in this function.
    let primary_check = lean_check(&comparison_root, &primary_module, &closure)?;
    if !primary_check.accepted {
        return Err(format!(
            "the independently emitted primary theorem refused: {}",
            primary_check.stderr
        ));
    }
    let held_out_check = lean_check(&comparison_root, &held_out_module, &closure)?;
    if !held_out_check.accepted {
        return Err(format!(
            "the cultivated held-out theorem refused: {}",
            held_out_check.stderr
        ));
    }
    let checker_return = serde_json::json!({
        "schema": "holonics.m6.post-emission-lean-checker-return.v1",
        "teacher_passage_opened_before_checks": false,
        "primary": primary_check,
        "held_out": held_out_check,
        "checker_is_exterior": true,
        "truth_status": "established-bounded"
    });
    source::write_json(
        &product_root.join("14-post-emission-lean-checker-return.json"),
        &checker_return,
    )?;

    // Only now is T0 admitted, into an exterior comparison apparatus which is never mounted by
    // either the productive or detached-inference process.
    let teacher_git_path =
        "formal/elementary-holonics/ElementaryHolonics/Millennium/FaceHomomorphism.lean";
    let teacher = Command::new("git")
        .arg("-C")
        .arg(workspace)
        .args(["show", &format!("4776099:{teacher_git_path}")])
        .output()
        .map_err(|error| format!("open withheld T0 after emission: {error}"))?;
    if !teacher.status.success() {
        return Err(format!(
            "open withheld T0 after emission: {}",
            String::from_utf8_lossy(&teacher.stderr)
        ));
    }
    let teacher_path = comparison_module_root.join("M6WithheldTeacher.lean");
    fs::write(&teacher_path, &teacher.stdout)
        .map_err(|error| format!("write withheld comparison passage: {error}"))?;
    let extractor =
        workspace.join("formal/elementary-holonics/.lake/build/bin/m6_lean_causal_return");
    if !extractor.is_file() {
        return Err(format!(
            "the project-owned causal profiler is absent: {}",
            extractor.display()
        ));
    }
    let generated_profile =
        causal::profile_exterior_passage(&extractor, &comparison_root, &primary_module)?;
    let held_out_profile =
        causal::profile_exterior_passage(&extractor, &comparison_root, &held_out_module)?;
    let teacher_profile =
        causal::profile_exterior_passage(&extractor, &comparison_root, &teacher_path)?;
    let generated_type = declaration_type(&generated_profile, "generatedFaceHomomorphism")?;
    let held_out_type = declaration_type(&held_out_profile, "heldOutCommutedFace")?;
    let teacher_type = declaration_type(
        &teacher_profile,
        "theDescentFaceIsAHomomorphismEverywhereHolds",
    )?;
    let receiver_consequence_equal = generated_type == teacher_type;
    let operation_passages_distinct = generated_profile.state_transition_operation_word_sha256
        != teacher_profile.state_transition_operation_word_sha256;
    let source_passages_distinct = generated_profile.source_sha256 != teacher_profile.source_sha256;
    let held_out_absent_from_s0_and_t0 = !teacher_profile
        .declared_proposition_types
        .contains(&held_out_type);
    if !receiver_consequence_equal
        || !operation_passages_distinct
        || !source_passages_distinct
        || !held_out_absent_from_s0_and_t0
    {
        return Err("the post-emission T0 comparison did not return the declared separator and receiver equality".to_owned());
    }
    let comparison = serde_json::json!({
        "schema": "holonics.m6.generated-withheld-operation-history-comparison.v1",
        "teacher_opened_only_after_primary_and_held_out_emission_checked": true,
        "generated": generated_profile,
        "withheld_teacher": teacher_profile,
        "cultivated_held_out": held_out_profile,
        "generated_receiver_type": generated_type,
        "withheld_receiver_type": teacher_type,
        "held_out_receiver_type": held_out_type,
        "receiver_consequence_equal": receiver_consequence_equal,
        "operation_state_passages_distinct": operation_passages_distinct,
        "source_passages_distinct": source_passages_distinct,
        "held_out_absent_from_s0_and_t0": held_out_absent_from_s0_and_t0,
        "proof_text_identity_required": false,
        "truth_status": "established-bounded"
    });
    source::write_json(
        &product_root.join("15-generated-withheld-passage-comparison.json"),
        &comparison,
    )?;

    let executable = std::env::current_exe()
        .map_err(|error| format!("locate Athena inference apparatus: {error}"))?
        .canonicalize()
        .map_err(|error| format!("resolve Athena inference apparatus: {error}"))?;
    let frozen_executable = product_root.join("athena-a0-inference-apparatus");
    fs::copy(&executable, &frozen_executable)
        .map_err(|error| format!("freeze Athena inference apparatus: {error}"))?;
    let native_rest_path = product_root.join("08-native-athena-route-rest.json");
    let phoenix_rest_path = product_root.join("08-phoenix-athena-route-rest.json");
    let native_inference = product_root.join("inference-native");
    let phoenix_inference = product_root.join("inference-phoenix");
    let native_elapsed =
        detached_inference(&frozen_executable, &native_rest_path, &native_inference)?;
    let phoenix_elapsed =
        detached_inference(&frozen_executable, &phoenix_rest_path, &phoenix_inference)?;
    let emitted_primary = fs::read(&primary).map_err(|error| error.to_string())?;
    let emitted_held_out = fs::read(&held_out).map_err(|error| error.to_string())?;
    let native_primary =
        fs::read(native_inference.join("primary.lean")).map_err(|error| error.to_string())?;
    let native_held_out =
        fs::read(native_inference.join("held-out.lean")).map_err(|error| error.to_string())?;
    let phoenix_primary =
        fs::read(phoenix_inference.join("primary.lean")).map_err(|error| error.to_string())?;
    let phoenix_held_out =
        fs::read(phoenix_inference.join("held-out.lean")).map_err(|error| error.to_string())?;
    let exact_later_conduct = native_primary == emitted_primary
        && phoenix_primary == emitted_primary
        && native_held_out == emitted_held_out
        && phoenix_held_out == emitted_held_out;
    if !exact_later_conduct {
        return Err("source-detached Athena later conduct moved".to_owned());
    }
    let remount = serde_json::json!({
        "schema": "holonics.m6.source-detached-remount.v2",
        "fresh_processes": 2,
        "mounted_faces_per_process": ["frozen inference apparatus", "one Athena rest", "one writable return port"],
        "repository_mounted": false,
        "source_material_mounted": false,
        "foreign_ancestry_mounted": false,
        "native_rest_sha256": source::sha256(&fs::read(&native_rest_path).map_err(|error| error.to_string())?),
        "phoenix_rest_sha256": source::sha256(&fs::read(&phoenix_rest_path).map_err(|error| error.to_string())?),
        "native_elapsed_milliseconds": native_elapsed,
        "phoenix_elapsed_milliseconds": phoenix_elapsed,
        "exact_later_conduct": exact_later_conduct,
        "primary_sha256": source::sha256(&emitted_primary),
        "held_out_sha256": source::sha256(&emitted_held_out),
        "truth_status": "established-bounded"
    });
    source::write_json(
        &product_root.join("13-source-detached-remount.json"),
        &remount,
    )?;

    let native_rest =
        athena::remount(&fs::read(&native_rest_path).map_err(|error| error.to_string())?)?;
    let phoenix_rest =
        athena::remount(&fs::read(&phoenix_rest_path).map_err(|error| error.to_string())?)?;
    let product_manifest = serde_json::json!({
        "schema": "holonics.athena-product-manifest.v1",
        "product_family": "Athena mathematics variants produced by Eros",
        "variants": [native_rest.variant, phoenix_rest.variant],
        "source_occurrence": native_rest.source_occurrence,
        "canonical_native_rest": "08-native-athena-route-rest.json",
        "canonical_phoenix_rest": "08-phoenix-athena-route-rest.json",
        "m3_ancestry_sha256": source::sha256(&fs::read(m3_rest).map_err(|error| error.to_string())?),
        "m4_ancestry_sha256": source::sha256(&fs::read(m4_rest).map_err(|error| error.to_string())?),
        "receiver_history_aperture": native_rest.receiver_history_aperture,
        "native_generators": native_rest.native_generators,
        "open_exterior": native_rest.open_exterior,
        "inference_entry": {
            "apparatus": "athena-a0-inference-apparatus",
            "apparatus_sha256": source::sha256(&fs::read(&frozen_executable).map_err(|error| error.to_string())?),
            "command": "./athena-a0-inference-apparatus --infer REST DESTINATION",
            "actual_native_return": "inference-native/inference-return.json",
            "actual_phoenix_return": "inference-phoenix/inference-return.json"
        },
        "surface_projection_boundary": "the inference apparatus contains the fixed Lean exterior projection for these five proof-plate species; M6 grades rest-controlled construction for the declared family, not unrestricted Lean surface synthesis",
        "canonical_identity_is_the_rest_not_the_apparatus_binary": true,
        "truth_status": "established-bounded"
    });
    source::write_json(
        &product_root.join("19-athena-product.json"),
        &product_manifest,
    )?;

    write_grade_and_manifest(product_root)?;
    Ok(())
}

fn regrade(output: &Path) -> Result<(), String> {
    let output = output
        .canonicalize()
        .map_err(|error| format!("resolve M6 output for regrade: {error}"))?;
    let product_root = if output.join("19-athena-product.json").is_file() {
        output
    } else {
        output.join("product")
    };
    let product_path = product_root.join("19-athena-product.json");
    let mut product: serde_json::Value =
        serde_json::from_slice(&fs::read(&product_path).map_err(|error| error.to_string())?)
            .map_err(|error| format!("decode Athena product manifest for regrade: {error}"))?;
    product["surface_projection_boundary"] = serde_json::Value::String(
        "the inference apparatus contains the fixed Lean exterior projection for these five proof-plate species; M6 grades rest-controlled construction for the declared family, not unrestricted Lean surface synthesis".to_owned(),
    );
    source::write_json(&product_path, &product)?;
    write_grade_and_manifest(&product_root)?;
    println!("M6 TWELVE-RETURN GRADE PASSED — {}", product_root.display());
    Ok(())
}

fn write_grade_and_manifest(product_root: &Path) -> Result<(), String> {
    let items = grade_items(product_root)?;
    let passed = items.iter().all(|item| item.passed);
    let grade = serde_json::json!({
        "schema": "holonics.m6.athena-a0-twelve-return-grade.v1",
        "truth_status": if passed { "established-bounded" } else { "open" },
        "passed": passed,
        "score": format!("{}/12", items.iter().filter(|item| item.passed).count()),
        "items": items,
        "boundary": "Athena-A0 is exact only for the declared descent-face receiver/history family; unrestricted mathematics and unexcited Gemma conduct remain open"
    });
    source::write_json(&product_root.join("20-grade.json"), &grade)?;
    if !passed {
        return Err("the indivisible M6 grade remains open".to_owned());
    }
    let artifact_manifest = serde_json::json!({
        "schema": "holonics.m6.artifact-manifest.v1",
        "entries": artifact_entries(product_root)?,
        "truth_status": "established-bounded"
    });
    source::write_json(&product_root.join("MANIFEST.json"), &artifact_manifest)?;
    Ok(())
}

fn prepare_post_emission_root(source_root: &Path, destination: &Path) -> Result<(), String> {
    if destination.exists() {
        return Err(format!(
            "the post-emission comparison root exists: {}",
            destination.display()
        ));
    }
    fs::create_dir_all(destination.join(".lake"))
        .map_err(|error| format!("create post-emission Lake root: {error}"))?;
    bind_source_tree(
        &source_root.join("ElementaryHolonics"),
        &destination.join("ElementaryHolonics"),
    )?;
    symlink(
        source_root.join("ElementaryHolonics.lean"),
        destination.join("ElementaryHolonics.lean"),
    )
    .map_err(|error| format!("bind addressed S0 root module: {error}"))?;
    for face in ["lakefile.toml", "lake-manifest.json", "lean-toolchain"] {
        fs::copy(source_root.join(face), destination.join(face))
            .map_err(|error| format!("copy addressed S0 checker face {face}: {error}"))?;
    }
    symlink(
        source_root.join(".lake/packages"),
        destination.join(".lake/packages"),
    )
    .map_err(|error| format!("bind addressed package closure: {error}"))?;
    symlink(
        source_root.join(".lake/build"),
        destination.join(".lake/build"),
    )
    .map_err(|error| format!("bind addressed S0 object closure: {error}"))?;
    Ok(())
}

fn bind_source_tree(source_root: &Path, destination: &Path) -> Result<(), String> {
    fs::create_dir_all(destination)
        .map_err(|error| format!("create addressed source chart: {error}"))?;
    let mut entries = fs::read_dir(source_root)
        .map_err(|error| format!("read addressed S0 source chart: {error}"))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| error.to_string())?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let target = destination.join(entry.file_name());
        let kind = entry.file_type().map_err(|error| error.to_string())?;
        if kind.is_dir() {
            bind_source_tree(&entry.path(), &target)?;
        } else if kind.is_file() {
            symlink(entry.path(), target)
                .map_err(|error| format!("bind addressed S0 source face: {error}"))?;
        } else {
            return Err(format!(
                "the addressed S0 source tree contains an unsupported face: {}",
                entry.path().display()
            ));
        }
    }
    Ok(())
}

fn declaration_type(
    profile: &causal::ExteriorPassageProfile,
    suffix: &str,
) -> Result<String, String> {
    let matches = profile
        .target_receiver_declarations
        .iter()
        .filter(|(name, _)| name.ends_with(suffix))
        .map(|(_, face)| face.clone())
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [face] => Ok(face.clone()),
        _ => Err(format!(
            "the exterior profile returned {} declarations ending {suffix}",
            matches.len()
        )),
    }
}

fn lean_check(root: &Path, source_path: &Path, closure: &str) -> Result<LeanCheckReturn, String> {
    let bytes = fs::read(source_path)
        .map_err(|error| format!("read emitted theorem {}: {error}", source_path.display()))?;
    let text = String::from_utf8(bytes.clone())
        .map_err(|error| format!("emitted theorem is not UTF-8: {error}"))?;
    let source_contains_sorry = text.contains("sorry");
    let started = Instant::now();
    let returned = Command::new("lake")
        .args(["env", "lean"])
        .arg(source_path)
        .current_dir(root)
        .output()
        .map_err(|error| format!("invoke exterior Lean checker: {error}"))?;
    let elapsed_milliseconds = started.elapsed().as_millis();
    let exit_status = returned.status.code().unwrap_or(-1);
    Ok(LeanCheckReturn {
        source_path: source_path.display().to_string(),
        source_sha256: source::sha256(&bytes),
        command: vec![
            "lake".to_owned(),
            "env".to_owned(),
            "lean".to_owned(),
            source_path.display().to_string(),
        ],
        code_closure: vec![closure.to_owned(), source::sha256(&bytes)],
        elapsed_milliseconds,
        exit_status,
        stdout: String::from_utf8_lossy(&returned.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&returned.stderr).into_owned(),
        source_contains_sorry,
        accepted: returned.status.success() && !source_contains_sorry,
    })
}

fn detached_inference(executable: &Path, rest: &Path, destination: &Path) -> Result<u128, String> {
    if destination.exists() {
        return Err(format!(
            "detached inference destination exists: {}",
            destination.display()
        ));
    }
    fs::create_dir_all(destination)
        .map_err(|error| format!("create detached inference return: {error}"))?;
    let mut command = Command::new("bwrap");
    command
        .args(["--die-with-parent", "--unshare-all"])
        .args(["--ro-bind", "/usr", "/usr"])
        .args(["--ro-bind", "/etc", "/etc"])
        .args(["--proc", "/proc"])
        .args(["--tmpfs", "/tmp"]);
    for library in ["/lib", "/lib64"] {
        if Path::new(library).exists() {
            command.args(["--ro-bind", library, library]);
        }
    }
    command
        .arg("--ro-bind")
        .arg(executable)
        .arg("/athena-a0")
        .arg("--ro-bind")
        .arg(rest)
        .arg("/rest.json")
        .arg("--bind")
        .arg(destination)
        .arg("/return")
        .args([
            "--chdir",
            "/tmp",
            "/athena-a0",
            "--infer",
            "/rest.json",
            "/return",
        ]);
    let started = Instant::now();
    let status = command
        .status()
        .map_err(|error| format!("enter detached Athena inference namespace: {error}"))?;
    let elapsed = started.elapsed().as_millis();
    if !status.success() {
        return Err(format!("detached Athena inference returned {status}"));
    }
    Ok(elapsed)
}

fn grade_items(product_root: &Path) -> Result<Vec<GradeItem>, String> {
    let read = |name: &str| -> Result<serde_json::Value, String> {
        serde_json::from_slice(
            &fs::read(product_root.join(name)).map_err(|error| error.to_string())?,
        )
        .map_err(|error| format!("decode grade evidence {name}: {error}"))
    };
    let access = read("01-negative-source-access.json")?;
    let incidence = read("02-declaration-operation-incidence.json")?;
    let route = read("04-receiver-addressed-route-substrate.json")?;
    let active = read("05-resident-active-route-junction-return.json")?;
    let cases = read("06-total-case-complex.json")?;
    let resident = read("07-resident-case-junction-return.json")?;
    let cultivation = read("11-returned-route-cultivation.json")?;
    let siblings = read("12-native-phoenix-siblings.json")?;
    let remount = read("13-source-detached-remount.json")?;
    let checker = read("14-post-emission-lean-checker-return.json")?;
    let comparison = read("15-generated-withheld-passage-comparison.json")?;
    let mesh = read("16-exact-route-line-mesh.json")?;
    let work = read("18-exact-route-work-and-fibre.json")?;
    let product = read("19-athena-product.json")?;
    let item = |ordinal, requirement: &str, passed, evidence: &[&str]| GradeItem {
        ordinal,
        requirement: requirement.to_owned(),
        passed,
        evidence: evidence.iter().map(ToString::to_string).collect(),
    };
    Ok(vec![
        item(
            1,
            "content-addressed S0 and negative T0 access",
            access["productive_process_repository_mounted"] == false
                && access["withheld_added_source_faces"]
                    .as_array()
                    .is_some_and(|faces| !faces.is_empty()),
            &[
                "00-source-occurrence.json",
                "01-negative-source-access.json",
            ],
        ),
        item(
            2,
            "complete declaration/operation incidence",
            incidence["incidence_work"]["declaration_operations"]
                .as_u64()
                .is_some_and(|count| count > 0)
                && incidence["founded_complex"]["faithful"] == true,
            &["02-declaration-operation-incidence.json"],
        ),
        item(
            3,
            "total case and reconstruction-fibre complex",
            cases["coverage"]["total_receiver_cover"] == true
                && cases["coverage"]["receiver_cases"] == 10
                && cases["coverage"]["refinement_leaves"] == 23
                && cases["coverage"]["resident_refinement_targets"] == 29
                && cases["coverage"]["default_branches"] == 0,
            &["06-total-case-complex.json"],
        ),
        item(
            4,
            "active cover and source ablations",
            route["active_contacts"]
                .as_array()
                .is_some_and(|faces| !faces.is_empty())
                && active["apparatus"]["kernel_launches"] == 1
                && cases["source_ablations"]
                    .as_array()
                    .is_some_and(|faces| faces.len() == 9),
            &[
                "04-receiver-addressed-route-substrate.json",
                "05-resident-active-route-junction-return.json",
                "06-total-case-complex.json",
            ],
        ),
        item(
            5,
            "resident GPU refinement/case/junction passage",
            resident["apparatus"]["kernel_launches"] == 1
                && resident["apparatus"]["stream_synchronizations"] == 1
                && resident["apparatus"]["relations"] == 48
                && cases["coverage"]["case_labels_sent_to_device"] == false,
            &["07-resident-case-junction-return.json"],
        ),
        item(
            6,
            "Athena-generated sorry-free total theorem",
            checker["primary"]["accepted"] == true
                && checker["primary"]["source_contains_sorry"] == false,
            &[
                "09-athena-generated-face-homomorphism.lean",
                "14-post-emission-lean-checker-return.json",
            ],
        ),
        item(
            7,
            "operation/history comparison against withheld T0",
            comparison["receiver_consequence_equal"] == true
                && comparison["operation_state_passages_distinct"] == true
                && comparison["source_passages_distinct"] == true,
            &["15-generated-withheld-passage-comparison.json"],
        ),
        item(
            8,
            "cultivated held-out successor absent before cultivation",
            checker["held_out"]["accepted"] == true
                && comparison["held_out_absent_from_s0_and_t0"] == true
                && cultivation["uncultivated_held_out_refusal"].is_object(),
            &[
                "10-cultivated-held-out-successor.lean",
                "11-returned-route-cultivation.json",
                "14-post-emission-lean-checker-return.json",
                "15-generated-withheld-passage-comparison.json",
            ],
        ),
        item(
            9,
            "source-detached remount, later conduct and route ablation",
            remount["exact_later_conduct"] == true
                && cultivation["targeted_ablation"]["unrelated_identity_case_survives"] == true
                && cultivation["targeted_ablation"]["primary_refusal"].is_object(),
            &[
                "11-returned-route-cultivation.json",
                "13-source-detached-remount.json",
            ],
        ),
        item(
            10,
            "matched native and Phoenix Athena siblings",
            siblings["equal_receiver_consequence"] == true
                && siblings["provider_priority_rule"] == false
                && siblings["shortest_separator"]
                    .as_array()
                    .is_some_and(|faces| !faces.is_empty()),
            &["12-native-phoenix-siblings.json"],
        ),
        item(
            11,
            "inspectable route, work/fibre and gauge-safe mesh",
            mesh["incidence_preserved"] == true
                && mesh["semantic_higher_cells_inferred_from_display"] == false
                && work["default_branches"] == 0
                && product_root.join("17-route-complex.svg").is_file(),
            &[
                "16-exact-route-line-mesh.json",
                "17-route-complex.svg",
                "18-exact-route-work-and-fibre.json",
            ],
        ),
        item(
            12,
            "frozen Athena product manifest and actual inference entry",
            product["canonical_identity_is_the_rest_not_the_apparatus_binary"] == true
                && product_root
                    .join("inference-native/inference-return.json")
                    .is_file()
                && product_root
                    .join("inference-phoenix/inference-return.json")
                    .is_file(),
            &[
                "19-athena-product.json",
                "athena-a0-inference-apparatus",
                "inference-native/inference-return.json",
                "inference-phoenix/inference-return.json",
            ],
        ),
    ])
}

fn artifact_entries(root: &Path) -> Result<Vec<ArtifactEntry>, String> {
    fn walk(root: &Path, at: &Path, returned: &mut Vec<ArtifactEntry>) -> Result<(), String> {
        let mut entries = fs::read_dir(at)
            .map_err(|error| format!("read artifact family: {error}"))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| error.to_string())?;
        entries.sort_by_key(|entry| entry.file_name());
        for entry in entries {
            let kind = entry.file_type().map_err(|error| error.to_string())?;
            if kind.is_dir() {
                walk(root, &entry.path(), returned)?;
            } else if kind.is_file() && entry.file_name() != "MANIFEST.json" {
                let bytes = fs::read(entry.path()).map_err(|error| error.to_string())?;
                returned.push(ArtifactEntry {
                    path: entry
                        .path()
                        .strip_prefix(root)
                        .map_err(|error| error.to_string())?
                        .display()
                        .to_string(),
                    octets: bytes.len() as u64,
                    sha256: source::sha256(&bytes),
                });
            }
        }
        Ok(())
    }
    let mut returned = Vec::new();
    walk(root, root, &mut returned)?;
    Ok(returned)
}

fn finalize_source_access(
    workspace: &Path,
    manifest: &source::SourceManifest,
    causal_manifest: &causal::CausalReturnManifest,
    product_root: &Path,
) -> Result<(), String> {
    let receipt = product_root.join("01-negative-source-access.json");
    if receipt.exists() {
        return Err(format!(
            "the negative source-access receipt already exists: {}",
            receipt.display()
        ));
    }
    let withheld = withheld_faces(workspace, manifest)?;
    let mut opened_paths = vec![format!("source/{}", source::MANIFEST)];
    opened_paths.extend(
        manifest
            .files
            .iter()
            .map(|file| format!("source/{}", file.relative_path)),
    );
    opened_paths.push(format!("causal/{}", causal::MANIFEST));
    opened_paths.push(format!(
        "causal/{}",
        causal_manifest.declaration_return.relative_path
    ));
    opened_paths.extend(
        causal_manifest
            .transition_returns
            .iter()
            .map(|face| format!("causal/{}", face.relative_path)),
    );
    let opened_path_population = opened_paths.len();
    let source_access = SourceAccessReturn {
        schema: "holonics.m6.negative-source-access.v1".to_owned(),
        productive_process_repository_mounted: false,
        productive_process_lean_cache_mounted: false,
        productive_process_git_mounted: false,
        source_occurrence: manifest.occurrence.clone(),
        withheld_revision: "4776099".to_owned(),
        withheld_added_source_faces: withheld,
        opened_paths,
        opened_path_population,
        mount_namespace: "private bwrap namespace: /source and /causal read-only, /product writable; repository, Lean executable and S0 build cache absent".to_owned(),
        claim: "[established-bounded] the productive process could open only the addressed S0 population and its addressed exterior causal return; no repository, Git object database, Lean executable/cache, S0 build cache or later formal tree was mounted".to_owned(),
    };
    source::write_json(&receipt, &source_access)?;
    Ok(())
}

fn withheld_faces(
    workspace: &Path,
    manifest: &source::SourceManifest,
) -> Result<Vec<WithheldSourceFace>, String> {
    let returned = Command::new("git")
        .arg("-C")
        .arg(workspace)
        .args([
            "diff",
            "--name-only",
            "--diff-filter=A",
            source::SOURCE_REVISION,
            "4776099",
            "--",
            source::SOURCE_ROOT,
        ])
        .output()
        .map_err(|error| format!("inspect withheld source boundary: {error}"))?;
    if !returned.status.success() {
        return Err(format!(
            "inspect withheld source boundary: {}",
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    let text = String::from_utf8(returned.stdout)
        .map_err(|error| format!("withheld path population is not UTF-8: {error}"))?;
    let mut faces = Vec::new();
    for path in text.lines().filter(|path| !path.is_empty()) {
        let relative = path
            .strip_prefix(&format!("{}/", source::SOURCE_ROOT))
            .ok_or_else(|| format!("withheld source path left its root: {path}"))?;
        let listing = Command::new("git")
            .arg("-C")
            .arg(workspace)
            .args(["ls-tree", "4776099", "--", path])
            .output()
            .map_err(|error| format!("inspect withheld blob {path}: {error}"))?;
        if !listing.status.success() {
            return Err(format!(
                "inspect withheld blob {path}: {}",
                String::from_utf8_lossy(&listing.stderr)
            ));
        }
        let listing = String::from_utf8(listing.stdout)
            .map_err(|error| format!("withheld blob row is not UTF-8: {error}"))?;
        let standing = listing
            .split_once('\t')
            .map(|(standing, _)| standing)
            .ok_or_else(|| format!("withheld blob row has no path: {listing}"))?;
        let fields = standing.split_ascii_whitespace().collect::<Vec<_>>();
        if fields.len() != 3 || fields[1] != "blob" {
            return Err(format!("withheld source face is not a blob: {listing}"));
        }
        let blob = Command::new("git")
            .arg("-C")
            .arg(workspace)
            .args(["cat-file", "blob", fields[2]])
            .output()
            .map_err(|error| format!("open withheld blob {path}: {error}"))?;
        if !blob.status.success() {
            return Err(format!(
                "open withheld blob {path}: {}",
                String::from_utf8_lossy(&blob.stderr)
            ));
        }
        let sha256 = source::sha256(&blob.stdout);
        let absent_path = manifest
            .files
            .iter()
            .all(|file| file.relative_path != relative);
        let absent_blob = manifest
            .files
            .iter()
            .all(|file| file.git_blob != fields[2] && file.sha256 != sha256);
        if !absent_path || !absent_blob {
            return Err(format!("withheld source face entered S0: {relative}"));
        }
        faces.push(WithheldSourceFace {
            relative_path: relative.to_owned(),
            git_blob: fields[2].to_owned(),
            sha256,
            absent_from_productive_mount: absent_path,
            blob_absent_from_productive_mount: absent_blob,
        });
    }
    if faces.is_empty() {
        return Err("the declared withheld boundary has no added source face".to_owned());
    }
    Ok(faces)
}

fn produce(
    source_root: &Path,
    causal_root: &Path,
    product_root: &Path,
    m3_rest_path: &Path,
    m4_rest_path: &Path,
) -> Result<(), String> {
    if Path::new("/home/b/Workspaces/holonics").exists() || Path::new("/.git").exists() {
        return Err("the productive process can see a repository path".to_owned());
    }
    let source = source::mount(source_root)?;
    let causal = causal::mount(causal_root)?;
    let m3_rest = fs::read(m3_rest_path)
        .map_err(|error| format!("open {}: {error}", m3_rest_path.display()))?;
    let m4_rest = fs::read(m4_rest_path)
        .map_err(|error| format!("open {}: {error}", m4_rest_path.display()))?;
    if causal.manifest.source_occurrence != source.manifest.occurrence {
        return Err("the exterior causal return belongs to another source occurrence".to_owned());
    }
    let source_receipt = serde_json::json!({
        "schema": "holonics.m6.opened-formal-source.v1",
        "source_manifest": source.manifest,
        "opened_paths": source.opened_paths,
        "causal_return_manifest": causal.manifest,
        "opened_causal_return_paths": causal.opened_paths,
        "source_bytes_retained_after_derivation": false,
        "lean_or_source_build_cache_mounted": false,
        "truth_status": "established-bounded"
    });
    let incidence = incidence::derive_causal(&source, &causal)?;
    let route = route::derive(&incidence)?;
    let mut junctions = incidence::ResidentJunctionOwner::new()?;
    let resident = junctions.enact(
        &incidence.source_occurrence,
        &incidence.recruitment_contacts,
    )?;
    let active_resident = junctions.enact(&incidence.source_occurrence, &route.active_contacts)?;
    let total_cases = case::derive(&incidence)?;
    let case_resident =
        junctions.enact(&incidence.source_occurrence, &total_cases.active_contacts)?;
    let athena = athena::cultivate(&total_cases, &case_resident, &m3_rest, &m4_rest)?;
    let visual = visual::derive(
        &incidence,
        &route,
        &total_cases,
        &case_resident,
        &athena.native_rest,
    )?;
    fs::create_dir_all(product_root)
        .map_err(|error| format!("create {}: {error}", product_root.display()))?;
    source::write_json(
        &product_root.join("00-source-occurrence.json"),
        &source_receipt,
    )?;
    source::write_json(
        &product_root.join("02-declaration-operation-incidence.json"),
        &incidence,
    )?;
    source::write_json(
        &product_root.join("03-resident-junction-return.json"),
        &resident,
    )?;
    source::write_json(
        &product_root.join("04-receiver-addressed-route-substrate.json"),
        &route,
    )?;
    source::write_json(
        &product_root.join("05-resident-active-route-junction-return.json"),
        &active_resident,
    )?;
    source::write_json(
        &product_root.join("06-total-case-complex.json"),
        &total_cases,
    )?;
    source::write_json(
        &product_root.join("07-resident-case-junction-return.json"),
        &case_resident,
    )?;
    fs::write(
        product_root.join("08-native-athena-route-rest.json"),
        &athena.native_rest_bytes,
    )
    .map_err(|error| format!("write native Athena rest: {error}"))?;
    fs::write(
        product_root.join("08-phoenix-athena-route-rest.json"),
        &athena.phoenix_rest_bytes,
    )
    .map_err(|error| format!("write Phoenix Athena rest: {error}"))?;
    fs::write(
        product_root.join("09-athena-generated-face-homomorphism.lean"),
        athena.primary_source.as_bytes(),
    )
    .map_err(|error| format!("write primary theorem emission: {error}"))?;
    fs::write(
        product_root.join("10-cultivated-held-out-successor.lean"),
        athena.held_out_source.as_bytes(),
    )
    .map_err(|error| format!("write held-out theorem emission: {error}"))?;
    source::write_json(
        &product_root.join("11-returned-route-cultivation.json"),
        &athena.cultivation,
    )?;
    source::write_json(
        &product_root.join("12-native-phoenix-siblings.json"),
        &athena.siblings,
    )?;
    source::write_json(
        &product_root.join("16-exact-route-line-mesh.json"),
        &visual.mesh,
    )?;
    fs::write(
        product_root.join("17-route-complex.svg"),
        visual.svg.as_bytes(),
    )
    .map_err(|error| format!("write route vector projection: {error}"))?;
    source::write_json(
        &product_root.join("18-exact-route-work-and-fibre.json"),
        &visual.work_and_fibre,
    )?;
    Ok(())
}

fn infer(rest_path: &Path, destination: &Path) -> Result<(), String> {
    if Path::new("/home/b/Workspaces/holonics").exists() || Path::new("/.git").exists() {
        return Err("source-detached Athena inference can see a repository path".to_owned());
    }
    let rest_bytes = fs::read(rest_path)
        .map_err(|error| format!("open Athena rest {}: {error}", rest_path.display()))?;
    let rest = athena::remount(&rest_bytes)?;
    let primary = athena::conduct_primary(&rest)
        .map_err(|refusal| format!("detached primary conduct refused: {refusal:?}"))?;
    let held_out = athena::conduct_held_out(&rest)
        .map_err(|refusal| format!("detached held-out conduct refused: {refusal:?}"))?;
    fs::create_dir_all(destination)
        .map_err(|error| format!("create inference destination: {error}"))?;
    let primary_path = destination.join("primary.lean");
    let held_out_path = destination.join("held-out.lean");
    fs::write(&primary_path, primary.as_bytes())
        .map_err(|error| format!("write detached primary conduct: {error}"))?;
    fs::write(&held_out_path, held_out.as_bytes())
        .map_err(|error| format!("write detached held-out conduct: {error}"))?;
    let receipt = serde_json::json!({
        "schema": "holonics.m6.detached-athena-inference.v1",
        "variant": rest.variant,
        "receiver_history_aperture": rest.receiver_history_aperture,
        "rest_sha256": source::sha256(&rest_bytes),
        "opened_paths": [rest_path.display().to_string()],
        "repository_mounted": false,
        "source_material_mounted": false,
        "foreign_ancestry_mounted": false,
        "primary_sha256": source::sha256(primary.as_bytes()),
        "held_out_sha256": source::sha256(held_out.as_bytes()),
        "truth_status": "established-bounded"
    });
    source::write_json(&destination.join("inference-return.json"), &receipt)?;
    Ok(())
}
