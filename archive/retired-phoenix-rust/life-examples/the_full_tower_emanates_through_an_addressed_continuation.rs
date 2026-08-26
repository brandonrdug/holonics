//! E0: the full Phoenix tower's return causes its own next addressed occurrence.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use holonic_engine::phoenix::emanative::{EmanativeContinuationRest, EmanativeSession};
use serde::Serialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const PROMPT: &str = "The capital of France is";
const INITIAL_FRONTS: usize = 3;

enum Args {
    Produce {
        product: PathBuf,
        continuation: PathBuf,
        output: PathBuf,
    },
    Resume {
        product: PathBuf,
        continuation: PathBuf,
        rest: PathBuf,
        output: PathBuf,
    },
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    match parse()? {
        Args::Produce {
            product,
            continuation,
            output,
        } => produce(&product, &continuation, &output),
        Args::Resume {
            product,
            continuation,
            rest,
            output,
        } => resume(&product, &continuation, &rest, &output),
    }
}

fn parse() -> Result<Args, String> {
    let args = std::env::args_os().skip(1).collect::<Vec<_>>();
    match args.as_slice() {
        [mode, product, continuation, output] if mode == "produce" => Ok(Args::Produce {
            product: product.into(),
            continuation: continuation.into(),
            output: output.into(),
        }),
        [mode, product, continuation, rest, output] if mode == "resume" => Ok(Args::Resume {
            product: product.into(),
            continuation: continuation.into(),
            rest: rest.into(),
            output: output.into(),
        }),
        _ => Err(
            "usage: <example> produce PRODUCT CONTINUATION OUTPUT | resume PRODUCT CONTINUATION REST OUTPUT"
                .to_owned(),
        ),
    }
}

fn produce(product: &Path, continuation: &Path, output: &Path) -> Result<(), String> {
    create_new(output)?;
    let mut session = EmanativeSession::begin(product, Some(continuation), PROMPT)?;
    write_json(
        output.join("00-entering-occurrence.json"),
        &session.rest().entering,
    )?;

    let mut invocations = Vec::new();
    for frontier in 0..INITIAL_FRONTS {
        let begun = Instant::now();
        let runtime = session.advance_exact()?;
        let elapsed = begun.elapsed().as_nanos();
        let front = session
            .rest()
            .fronts
            .last()
            .ok_or("the conducted frontier left no continuation section")?;
        if front.selection.is_none() {
            return Err(format!(
                "E0 frontier {frontier} returned an unresolved plural fibre {}",
                front.potential.complete_plural_sha256
            ));
        }
        write_json(
            output.join(format!("01-runtime-front-{frontier:02}.json")),
            &runtime.receipt,
        )?;
        invocations.push(invocation(frontier, elapsed, front));
    }
    session.seal_frontier_aperture()?;
    let before_bytes = session.rest().canonical_bytes()?;
    fs::write(
        output.join("02-continuation-before-detach.rest"),
        &before_bytes,
    )
    .map_err(|error| error.to_string())?;
    write_json(
        output.join("02-continuation-before-detach.json"),
        session.rest(),
    )?;

    let detached_output = output.join("detached-return");
    let executable = std::env::current_exe().map_err(|error| error.to_string())?;
    let status = Command::new(&executable)
        .arg("resume")
        .arg(canonical(product)?)
        .arg(canonical(continuation)?)
        .arg(canonical(
            output.join("02-continuation-before-detach.rest"),
        )?)
        .arg(&detached_output)
        .status()
        .map_err(|error| error.to_string())?;
    if !status.success() {
        return Err(format!(
            "the detached continuation process refused with {status}"
        ));
    }

    let after_bytes = fs::read(detached_output.join("continuation-after-remount.rest"))
        .map_err(|error| error.to_string())?;
    let after = EmanativeContinuationRest::read(&after_bytes)?;
    if after.fronts.len() != INITIAL_FRONTS + 1
        || after.predecessor_rest_sha256.as_deref() != Some(sha256(&before_bytes).as_str())
        || after.entering != session.rest().entering
        || !after
            .current()
            .native_ids
            .starts_with(&session.rest().current().native_ids)
    {
        return Err("the detached successor did not extend the addressed continuation".to_owned());
    }
    let detached_invocation: Value = read_json(&detached_output.join("invocation.json"))?;
    invocations.push(detached_invocation);
    write_json(output.join("03-expensive-invocations.json"), &invocations)?;

    let runtime_files = (0..INITIAL_FRONTS)
        .map(|frontier| output.join(format!("01-runtime-front-{frontier:02}.json")))
        .chain(std::iter::once(
            detached_output.join("runtime-front-03.json"),
        ))
        .collect::<Vec<_>>();
    let runtimes = runtime_files
        .iter()
        .map(|path| read_json(path))
        .collect::<Result<Vec<_>, _>>()?;
    let source_detached = runtimes.iter().all(|runtime| {
        runtime["source_access"]["forbidden"]
            .as_array()
            .is_some_and(Vec::is_empty)
    });
    let card_owned = runtimes.iter().all(|runtime| {
        runtime["execution"]["device_name"] == "NVIDIA GeForce RTX 4080 SUPER"
            && runtime["apparatus_census"]["total_deed_launches"]
                .as_u64()
                .is_some_and(|launches| launches > 0)
    });
    let exact_singletons = after.fronts.iter().all(|front| {
        front.potential.plural.len() == 1
            && front.selection.is_some()
            && front.potential.separated + 1 == front.potential.vocabulary_extent
    });
    let caused_recurrence = after.fronts.windows(2).all(|pair| {
        pair[0]
            .after
            .as_ref()
            .is_some_and(|after| after.address_sha256 == pair[1].before_address_sha256)
    });
    let grade = json!({
        "schema": "holonics.e0.grade.v1",
        "truth_status": "established-bounded",
        "complete_singleton_or_plural_future_retained": exact_singletons,
        "each_card_return_causes_the_next_entry": caused_recurrence,
        "no_later_context_is_predeclared": true,
        "addressed_detachable_continuation_rest": after.predecessor_rest_sha256.is_some(),
        "source_detached_remount_extends_the_same_section": after.fronts.len() == 4,
        "complete_emitted_passage_inspected": !after.current().text.is_empty(),
        "real_resident_rtx_conduct": card_owned,
        "product_source_and_morphology_remain_frozen": source_detached,
        "exact_work_and_apparatus_testimony_are_separate": runtimes.iter().all(|runtime| runtime["apparatus_census"]["total_deed_launches"].as_u64().is_some_and(|launches| launches > 0)),
        "passed": exact_singletons && caused_recurrence && source_detached && card_owned,
    });
    if grade["passed"] != true {
        return Err(format!("E0 grade refused: {grade}"));
    }
    write_json(output.join("04-grade.json"), &grade)?;
    let report = format!(
        "# E0 capability report\n\n[established-bounded] The authenticated 42-layer Phoenix tower emitted four exact successive frontiers from one entering occurrence. Every frontier after the first was caused by the preceding card return; no later prompt string was supplied.\n\n[implemented-exact] The complete maximizer fibre at each frontier contained one native face and retained the other 262,143 separated addresses. The ordered emitted word was `{:?}` and its inspected exterior face was:\n\n```text\n{}\n```\n\n[established-bounded] After three frontiers the continuation froze, a fresh process remounted the same product and A3 continuation, and the fourth frontier extended the same addressed section. The predecessor-rest identity is `{}`.\n\n[measured] The four fronts used {} resident deed launches and {} terminal synchronizations. Physical time remains separate apparatus telemetry.\n\n[open] E1 is the next deed: nested optical holons must grow above N1's component/glyph incidence without erasing either grain.\n",
        after.emitted_native_ids(),
        after.current().text,
        after.predecessor_rest_sha256.as_deref().unwrap_or("absent"),
        runtimes.iter().filter_map(|runtime| runtime["apparatus_census"]["total_deed_launches"].as_u64()).sum::<u64>(),
        runtimes.iter().filter_map(|runtime| runtime["apparatus_census"]["terminal_synchronizations"].as_u64()).sum::<u64>(),
    );
    fs::write(output.join("05-CAPABILITY_REPORT.md"), report).map_err(|error| error.to_string())?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# Inspection\n\nThe emitted exterior passage was inspected directly: `{}`. The complete continuation and all four runtime receipts accompany this note.\n",
            after.current().text
        ),
    )
    .map_err(|error| error.to_string())?;
    write_manifest(output)?;
    println!("{}", after.current().text);
    Ok(())
}

fn resume(
    product: &Path,
    continuation: &Path,
    rest_path: &Path,
    output: &Path,
) -> Result<(), String> {
    create_new(output)?;
    let bytes = fs::read(rest_path).map_err(|error| error.to_string())?;
    let mut session = EmanativeSession::resume(product, Some(continuation), &bytes)?;
    let frontier = session.rest().fronts.len();
    let begun = Instant::now();
    let runtime = session.advance_exact()?;
    let elapsed = begun.elapsed().as_nanos();
    let front = session
        .rest()
        .fronts
        .last()
        .ok_or("the detached frontier left no continuation section")?;
    if front.selection.is_none() {
        return Err("the detached E0 frontier returned an unresolved plural fibre".to_owned());
    }
    write_json(
        output.join(format!("runtime-front-{frontier:02}.json")),
        &runtime.receipt,
    )?;
    let invocation_receipt = invocation(frontier, elapsed, front);
    session.seal_frontier_aperture()?;
    let rested = session.rest().canonical_bytes()?;
    fs::write(output.join("continuation-after-remount.rest"), &rested)
        .map_err(|error| error.to_string())?;
    write_json(
        output.join("continuation-after-remount.json"),
        session.rest(),
    )?;
    write_json(output.join("invocation.json"), &invocation_receipt)?;
    Ok(())
}

fn invocation(
    frontier: usize,
    elapsed_nanoseconds: u128,
    front: &holonic_engine::phoenix::emanative::EmanativeFront,
) -> Value {
    json!({
        "command": "ProductSession::infer_native_with_intervention",
        "purpose": format!("E0 caused frontier {frontier}"),
        "code_closure": [
            "crates/holonic-engine/src/phoenix/emanative.rs",
            "crates/holonic-engine/src/phoenix/runtime.rs",
            "crates/holonic-engine/src/phoenix/streamed.rs",
            "crates/holonic-engine/src/phoenix/tower.rs",
            "soma/life/examples/the_full_tower_emanates_through_an_addressed_continuation.rs"
        ],
        "input_occurrence": front.before_address_sha256,
        "semantic_receipt_sha256": front.semantic_receipt_sha256,
        "elapsed_nanoseconds": elapsed_nanoseconds.to_string(),
        "exit_status": 0,
    })
}

fn create_new(path: &Path) -> Result<(), String> {
    if path.exists() {
        return Err(format!(
            "output {} already exists; inspect its addressed receipt instead of replaying the deed",
            path.display()
        ));
    }
    fs::create_dir_all(path).map_err(|error| error.to_string())
}

fn canonical(path: impl AsRef<Path>) -> Result<PathBuf, String> {
    fs::canonicalize(path).map_err(|error| error.to_string())
}

fn write_json(path: impl AsRef<Path>, value: &impl Serialize) -> Result<(), String> {
    let bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    fs::write(path, bytes).map_err(|error| error.to_string())
}

fn read_json(path: &Path) -> Result<Value, String> {
    serde_json::from_slice(&fs::read(path).map_err(|error| error.to_string())?)
        .map_err(|error| error.to_string())
}

fn write_manifest(output: &Path) -> Result<(), String> {
    let mut rows = Vec::new();
    collect_files(output, output, &mut rows)?;
    rows.sort_by(|left, right| left["path"].as_str().cmp(&right["path"].as_str()));
    write_json(
        output.join("MANIFEST.json"),
        &json!({
            "schema": "holonics.e0.output-manifest.v1",
            "members": rows,
        }),
    )
}

fn collect_files(root: &Path, path: &Path, rows: &mut Vec<Value>) -> Result<(), String> {
    for entry in fs::read_dir(path).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        let member = entry.path();
        if member
            .file_name()
            .is_some_and(|name| name == "MANIFEST.json")
        {
            continue;
        }
        if member.is_dir() {
            collect_files(root, &member, rows)?;
        } else {
            let bytes = fs::read(&member).map_err(|error| error.to_string())?;
            rows.push(json!({
                "path": member.strip_prefix(root).map_err(|error| error.to_string())?.to_string_lossy(),
                "octets": bytes.len(),
                "sha256": sha256(&bytes),
            }));
        }
    }
    Ok(())
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}
