//! W4 fresh-process receiver: two independent `eros phoenix infer --product --card` processes.
//!
//! This is a grade harness, not a runtime. It consumes the standing application's returned
//! `PHOENIX_RETURN` JSON, compares the source-detached semantic return, exercises the two CLI
//! refusals, and deposits the complete child receipts under the named output directory.

use serde_json::{Map, Value, json};
use std::path::{Path, PathBuf};
use std::process::Command;

const DEFAULT_EROS: &str = "target/release/eros";
const PRODUCT: &str =
    ".local/artifacts/the_lifted_body_is_cultivated_and_the_delta_survives_native_rest/product";
const MATERIAL_MANIFEST: &str = ".local/artifacts/the_lifted_body_is_cultivated_and_the_delta_survives_native_rest/material_manifest.json";
const TEXTS: [&str; 3] = [
    "Geometry returns through another chart",
    "A crystal carries the reflected current",
    "Discrete faces close around a curved path",
];
const OUTPUT: &str = ".local/artifacts/the_application_infers_from_the_cultivated_phoenix_rest_on_the_card";

struct Child {
    status: Option<i32>,
    stdout: String,
    stderr: String,
}

fn child(eros: &Path, args: &[&str]) -> Result<Child, String> {
    let output = Command::new(eros)
        .args(args)
        .output()
        .map_err(|error| format!("{} {args:?}: {error}", eros.display()))?;
    Ok(Child {
        status: output.status.code(),
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    })
}

fn returned(child: &Child) -> Result<Value, String> {
    let line = child
        .stdout
        .lines()
        .find_map(|line| line.strip_prefix("PHOENIX_RETURN "))
        .ok_or_else(|| format!("child returned no PHOENIX_RETURN: {}", child.stdout))?;
    serde_json::from_str(line).map_err(|error| format!("PHOENIX_RETURN JSON: {error}"))
}

/// Rebase only the finite capacity magnitude of an admission. Required work, the admitted
/// consequence, ceiling species/declarer and every unbounded reason remain exact.
fn admission_consequence(value: &Value) -> Value {
    match value {
        Value::Object(object) => {
            let mut kept = Map::new();
            for (key, value) in object {
                if key == "free_octets_at_admission" {
                    continue;
                }
                if key == "Bounded" {
                    let mut bounded = value.as_object().cloned().unwrap_or_default();
                    bounded.remove("ceiling");
                    kept.insert(key.clone(), Value::Object(bounded));
                } else {
                    kept.insert(key.clone(), admission_consequence(value));
                }
            }
            Value::Object(kept)
        }
        Value::Array(values) => Value::Array(values.iter().map(admission_consequence).collect()),
        other => other.clone(),
    }
}

fn execution_consequence(value: &Value) -> Value {
    let mut execution = value.as_object().cloned().unwrap_or_default();
    for key in [
        "memory_at_mount_free",
        "memory_at_return_free",
        "wall_seconds",
        "loop_wall_seconds",
    ] {
        execution.remove(key);
    }
    Value::Object(execution)
}

fn stable_receipt(value: &Value) -> Value {
    let mut stable = Map::new();
    for key in [
        "product_identity",
        "predecessor_identity",
        "morphology_identity",
        "codec_companion_identities",
        "runtime_law",
        "frozen_members_verified",
        "input",
        "generated",
        "reconstruction_identity",
        "codec_identity",
        "total_work",
        "overlay_work",
        "apparatus_prediction",
        "overlay_execution",
        "streamed",
    ] {
        stable.insert(
            key.to_owned(),
            value.get(key).cloned().unwrap_or(Value::Null),
        );
    }
    stable.insert(
        "admission".to_owned(),
        admission_consequence(value.get("admission").unwrap_or(&Value::Null)),
    );
    stable.insert(
        "execution".to_owned(),
        execution_consequence(value.get("execution").unwrap_or(&Value::Null)),
    );
    Value::Object(stable)
}

fn material_is_unseen(receipt: &Value) -> Result<bool, String> {
    let material: Value = serde_json::from_slice(
        &std::fs::read(MATERIAL_MANIFEST)
            .map_err(|error| format!("{MATERIAL_MANIFEST}: {error}"))?,
    )
    .map_err(|error| format!("material manifest: {error}"))?;
    let input = receipt
        .pointer("/input/native_ids")
        .ok_or("runtime receipt lacks input/native_ids")?;
    let entries = material
        .get("entries")
        .and_then(Value::as_array)
        .ok_or("material manifest lacks entries")?;
    Ok(entries
        .iter()
        .all(|entry| entry.get("token_ids") != Some(input)))
}

fn shallow_missing_companion(product: &Path) -> Result<PathBuf, String> {
    let nonce = format!(
        "w4-product-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_err(|e| e.to_string())?
            .as_nanos()
    );
    // The 16 GB predecessor must remain one addressed body. Put the disposable control beside the
    // W4 artifact so its base member can be hard-linked rather than copied across filesystems.
    let root = Path::new(OUTPUT).join(nonce);
    std::fs::create_dir_all(&root).map_err(|e| e.to_string())?;
    let manifest: Value = serde_json::from_slice(
        &std::fs::read(product.join("manifest.json")).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    for member in ["manifest.json", "cultivated.rest", "morphology.safetensors"] {
        std::fs::copy(product.join(member), root.join(member))
            .map_err(|e| format!("copy {member}: {e}"))?;
    }
    let predecessor = manifest
        .get("predecessor")
        .and_then(Value::as_str)
        .ok_or("manifest predecessor absent")?;
    std::fs::hard_link(product.join(predecessor), root.join(predecessor))
        .map_err(|e| format!("hard-link predecessor: {e}"))?;
    let companion = manifest
        .get("codec_companions")
        .and_then(Value::as_array)
        .and_then(|values| values.first())
        .and_then(|value| value.get("path"))
        .and_then(Value::as_str)
        .ok_or("manifest codec companion absent")?;
    for value in manifest
        .get("codec_companions")
        .and_then(Value::as_array)
        .ok_or("codec companions absent")?
    {
        let path = value
            .get("path")
            .and_then(Value::as_str)
            .ok_or("codec path absent")?;
        if path != companion {
            std::fs::copy(product.join(path), root.join(path))
                .map_err(|e| format!("copy codec {path}: {e}"))?;
        }
    }
    Ok(root)
}

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut eros = PathBuf::from(DEFAULT_EROS);
    for argument in std::env::args().skip(1) {
        if let Some(path) = argument.strip_prefix("--eros=") {
            eros = PathBuf::from(path);
        } else {
            return Err(format!("unknown argument {argument}; use --eros=PATH"));
        }
    }
    let product = Path::new(PRODUCT);
    if !eros.exists() || !product.is_dir() {
        return Err(format!(
            "build {}/provide {} before this harness",
            eros.display(),
            product.display()
        ));
    }
    std::fs::create_dir_all(OUTPUT).map_err(|e| e.to_string())?;

    let mut family = Vec::new();
    let mut stable_return = true;
    let mut exact_fields = true;
    let mut admission_stands = true;
    let mut actual_execution = true;
    let mut source_lived = true;
    let mut unseen = true;
    let mut source_clean = true;
    let mut frozen = true;
    let mut children_stood = true;
    for text in TEXTS {
        let first = child(
            &eros,
            &[
                "phoenix",
                "infer",
                "--product",
                PRODUCT,
                "--text",
                text,
                "--card",
            ],
        )?;
        let second = child(
            &eros,
            &[
                "phoenix",
                "infer",
                "--product",
                PRODUCT,
                "--text",
                text,
                "--card",
            ],
        )?;
        let first_receipt = returned(&first)?;
        let second_receipt = returned(&second)?;
        let stable = stable_receipt(&first_receipt) == stable_receipt(&second_receipt);
        let exact = [
            "/runtime_law",
            "/input",
            "/generated",
            "/reconstruction_identity",
            "/codec_identity",
            "/total_work",
            "/overlay_work",
        ]
        .iter()
        .all(|path| first_receipt.pointer(path) == second_receipt.pointer(path));
        let admission = first_receipt.pointer("/admission").is_some_and(|value| {
            admission_consequence(value)
                == admission_consequence(
                    second_receipt.pointer("/admission").unwrap_or(&Value::Null),
                )
        });
        let execution = [
            "/execution/terminal_synchronizations",
            "/execution/streamed/graph_launches",
            "/execution/streamed/terminal_synchronizations",
        ]
        .iter()
        .all(|path| {
            first_receipt
                .pointer(path)
                .and_then(Value::as_u64)
                .is_some_and(|value| value > 0)
        });
        let live = [&first_receipt, &second_receipt].iter().all(|receipt| {
            receipt
                .pointer("/source_access/descriptors")
                .and_then(Value::as_array)
                .is_some_and(|items| {
                    let rendered = items.iter().filter_map(Value::as_str).collect::<Vec<_>>();
                    rendered.iter().any(|item| item.contains("base.w1.rest"))
                        && rendered.iter().any(|item| item.contains("/dev/nvidia"))
                })
        });
        let clean = [
            first_receipt.pointer("/source_access/forbidden"),
            second_receipt.pointer("/source_access/forbidden"),
        ]
        .iter()
        .all(|value| {
            value
                .and_then(Value::as_array)
                .is_some_and(|items| items.is_empty())
        });
        let pair_unseen = material_is_unseen(&first_receipt)?;
        let pair_frozen = first_receipt.get("frozen_members_verified") == Some(&Value::Bool(true))
            && second_receipt.get("frozen_members_verified") == Some(&Value::Bool(true));
        let pair_stood = first.status == Some(0) && second.status == Some(0);
        stable_return &= stable;
        exact_fields &= exact;
        admission_stands &= admission;
        actual_execution &= execution;
        source_lived &= live;
        unseen &= pair_unseen;
        source_clean &= clean;
        frozen &= pair_frozen;
        children_stood &= pair_stood;
        family.push(json!({
            "text": text,
            "unseen_against_w3_material": pair_unseen,
            "stable": stable,
            "children": [
                {"status": first.status, "receipt": first_receipt, "stderr": first.stderr},
                {"status": second.status, "receipt": second_receipt, "stderr": second.stderr}
            ]
        }));
    }

    let control_text = TEXTS[0];
    let old_rest = child(
        &eros,
        &[
            "phoenix",
            "infer",
            "--product",
            PRODUCT,
            "--rest",
            "not-used",
            "--text",
            control_text,
            "--card",
        ],
    )?;
    let old_rest_rejected =
        old_rest.status != Some(0) && !old_rest.stdout.contains("PHOENIX_RETURN");
    let shallow = shallow_missing_companion(product)?;
    let shallow_run = child(
        &eros,
        &[
            "phoenix",
            "infer",
            "--product",
            shallow
                .to_str()
                .ok_or("temporary product path is not unicode")?,
            "--text",
            control_text,
            "--card",
        ],
    )?;
    let shallow_refused =
        shallow_run.status != Some(0) && !shallow_run.stdout.contains("PHOENIX_RETURN");
    std::fs::remove_dir_all(&shallow)
        .map_err(|error| format!("remove temporary product {}: {error}", shallow.display()))?;

    let grade = children_stood
        && stable_return
        && exact_fields
        && admission_stands
        && actual_execution
        && source_lived
        && unseen
        && source_clean
        && frozen
        && old_rest_rejected
        && shallow_refused;
    let artifact = json!({
        "schema": "holonic-engine.phoenix.w4-fresh-process.v1",
        "grade": grade,
        "input_family": family,
        "controls": {
            "old_rest_with_card_rejected": old_rest_rejected,
            "old_rest_with_card_stderr": old_rest.stderr,
            "missing_codec_companion_rejected": shallow_refused,
            "missing_codec_companion_stderr": shallow_run.stderr,
            "stable_return": stable_return,
            "all_fresh_children_stood": children_stood,
            "exact_semantic_fields": exact_fields,
            "admission_consequences": admission_stands,
            "actual_execution_counters": actual_execution,
            "live_native_rest_and_card_descriptors": source_lived,
            "source_audit_clean": source_clean,
            "frozen_members": frozen
        }
    });
    std::fs::write(
        format!("{OUTPUT}/receipt.json"),
        serde_json::to_vec_pretty(&artifact).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    println!("W4_RECEIPT {OUTPUT}/receipt.json");
    println!("W4_GRADE {grade}");
    if !grade {
        return Err("W4 fresh-process grade failed; inspect receipt.json".to_owned());
    }
    Ok(())
}
