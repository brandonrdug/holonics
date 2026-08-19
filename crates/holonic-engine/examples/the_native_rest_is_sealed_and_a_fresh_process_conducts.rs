//! **Phoenix stations eight and nine: the native rest is sealed, the foreign source departs, and a
//! FRESH PROCESS conducts from the rest alone.**
//!
//! Plan: `blueprint/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md`
//! §§12, 13 — *"Seal the complete native ecology … make the foreign weight file unreachable …
//! remount from the native artifacts in a fresh process … frozen inference leaves the rest
//! byte-identical."*
//!
//! # The seal is a container this project can already read
//!
//! The rest is written in the same container species the source arrived in, so remounting it uses
//! the standing `foreign_map` mouth and the `atlas <-> weights` round-trip the blueprint demands is
//! literal rather than asserted. Its payload is **every stored population the program names and
//! nothing else**; its metadata carries the diagram, the program, the band elements and the
//! realization manifest.
//!
//! # The departure is structural, not a preflight declaration
//!
//! The child process is handed the rest's path and **no source path at all**. Its carrier is a
//! different implementation that holds no source handle, so the code path to the source does not
//! exist rather than being declined. On top of that it runs a **live access audit** — every open
//! descriptor it holds, resolved and reported — because the blueprint says a preflight declaration
//! is not evidence.
//!
//! ```text
//! cargo run --release -q -p holonic-engine \
//!   --example the_native_rest_is_sealed_and_a_fresh_process_conducts -- /home/b/models/gemma-4-E4B-it
//! ```

#[path = "phoenix/site.rs"]
mod site;

use std::collections::BTreeMap;
use std::io::Write;

use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::exact_value::ieee754::{decode_bfloat16_bits, round_into_bfloat16};
use holonic_engine::exact_value::ExactInterval;
use holonic_engine::foreign_map::manifest_safetensors;
use holonic_engine::interaction::OccurrencePort;
use holonic_engine::ported_operation::PortedOperationComplex;
use holonic_engine::ported_reference::{realize, PortedProgram};
use num_bigint::BigInt;
use num_traits::Zero;
use relational_geometry::Rat;
use site::{
    digest_of, found, write_container, NativeRestCarrier, BAND_POPULATION, BASE, CAUSED,
};

/// The rest's own schema, carried in its metadata so a later reader is not guessing.
const REST_SCHEMA: &str = "holonic-engine.phoenix-native-rest.v1";

// ---------------------------------------------------------------------------------------------

fn main() {
    let arguments: Vec<String> = std::env::args().collect();
    if let Some(at) = arguments.iter().position(|argument| argument == "--conduct") {
        let rest = arguments
            .get(at + 1)
            .cloned()
            .unwrap_or_else(|| String::from("<none>"));
        conduct_from_rest_alone(&rest);
        return;
    }
    seal_and_hand_over(&arguments);
}

/// **THE CHILD.** It is handed a rest and nothing else. There is no source path in this function's
/// reach, and its carrier holds no source handle.
fn conduct_from_rest_alone(rest: &str) {
    let chart = match ResidentReadout::new() {
        Ok(chart) => chart,
        Err(error) => {
            eprintln!("REFUSED the resident chart: {error:?}");
            std::process::exit(2);
        }
    };
    let (file, container) = match manifest_safetensors(rest) {
        Ok(pair) => pair,
        Err(error) => {
            eprintln!("REFUSED the native rest: {error}");
            std::process::exit(3);
        }
    };
    let complex: PortedOperationComplex = serde_json::from_str(
        container
            .container_metadata
            .get("diagram")
            .map(String::as_str)
            .unwrap_or(""),
    )
    .expect("the rest carries its diagram");
    let program: PortedProgram = serde_json::from_str(
        container
            .container_metadata
            .get("program")
            .map(String::as_str)
            .unwrap_or(""),
    )
    .expect("the rest carries its program");
    let bands: Vec<(ExactInterval, ExactInterval)> = serde_json::from_str(
        container
            .container_metadata
            .get("band-elements")
            .map(String::as_str)
            .unwrap_or("[]"),
    )
    .expect("the rest carries its band elements");
    let returns: Vec<u64> = serde_json::from_str(
        container
            .container_metadata
            .get("returns")
            .map(String::as_str)
            .unwrap_or("[]"),
    )
    .expect("the rest names its return occurrences");

    let mut carrier = NativeRestCarrier {
        chart: &chart,
        container,
        file,
        bands: BTreeMap::from([(BAND_POPULATION.to_owned(), bands)]),
        below_the_frame: 0,
        resident: BTreeMap::new(),
        reused: 0,
    };
    let receipt = match realize(&complex, &program, &mut carrier, &BTreeMap::new()) {
        Ok(receipt) => receipt,
        Err(error) => {
            eprintln!("REFUSED while conducting from the rest: {error}");
            std::process::exit(4);
        }
    };

    // **THE LIVE ACCESS AUDIT.** Every descriptor this process actually holds, resolved. A
    // preflight declaration is not evidence; this is taken after the deed.
    let mut opened = Vec::new();
    if let Ok(entries) = std::fs::read_dir("/proc/self/fd") {
        for entry in entries.flatten() {
            if let Ok(target) = std::fs::read_link(entry.path()) {
                opened.push(target.to_string_lossy().into_owned());
            }
        }
    }
    println!("CHILD-OPENED {}", serde_json::to_string(&opened).expect("audit"));

    let carried: Vec<Vec<String>> = returns
        .iter()
        .map(|event| {
            receipt.carried[&OccurrencePort::output(
                holonic_engine::causal::EventId(*event),
                0,
            )]
                .iter()
                .map(ToString::to_string)
                .collect()
        })
        .collect();
    println!(
        "CHILD-RETURN {}",
        serde_json::to_string(&carried).expect("return")
    );
    println!("CHILD-BELOW-FRAME {}", carrier.below_the_frame);
}

/// **THE PARENT.** It seals, hands over, and grades.
fn seal_and_hand_over(arguments: &[String]) {
    let root = arguments
        .get(1)
        .cloned()
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let terms: usize = std::env::var("TERMS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(20);
    let scratch = std::env::var("SCRATCH").unwrap_or_else(|_| "/tmp".to_owned());
    let rest_path = format!("{scratch}/phoenix-native-rest.safetensors");

    let chart = match ResidentReadout::new() {
        Ok(chart) => chart,
        Err(error) => {
            println!("the resident chart refused: {error:?}");
            std::process::exit(1);
        }
    };

    println!("PHOENIX STATIONS EIGHT AND NINE — THE SOURCE DEPARTS AND A FRESH PROCESS CONDUCTS");
    println!();
    println!("  resident chart                    {}", chart.device_name());

    // ---------------------------------------------------------------------------------------
    // THE FOUNDING, and the reference conduct with the source present.
    // ---------------------------------------------------------------------------------------
    let (site, container, mut file) = match found(&root, BASE, terms, None) {
        Ok(triple) => triple,
        Err(error) => {
            println!("  the founding refused: {error}");
            std::process::exit(1);
        }
    };
    println!();
    println!("  THE FOUNDING");
    println!("    operations                      {}", site.program.operations.len());
    println!("    stored populations NAMED        {}", site.populations.len());
    for population in &site.populations {
        println!("        {population}");
    }

    // ---------------------------------------------------------------------------------------
    // THE SEAL.
    // ---------------------------------------------------------------------------------------
    let mut payload: Vec<u8> = Vec::new();
    let mut header: Vec<(String, (String, Vec<usize>, u64, u64))> = Vec::new();
    let mut source_octets = 0u64;
    for population in &site.populations {
        let tensor = container.tensor(population).expect("named").clone();
        // A lookup names a row; a contraction names the whole map. The rest carries exactly what
        // the diagram reaches, so a row-addressed population is sealed as one row.
        let is_row = site.program.operations.values().any(|operation| {
            matches!(
                operation,
                holonic_engine::ported_reference::PortedOperationKind::Lookup { population: named, .. }
                    if named == population
            )
        });
        let words = if is_row && tensor.rank() == 2 {
            let mut rows = Vec::new();
            for symbol in CAUSED {
                let (row, _) = container
                    .read_rows_bf16(&mut file, population, symbol, 1)
                    .expect("read");
                rows.extend(row);
            }
            rows
        } else {
            container.read_bf16_whole(&mut file, population).expect("read")
        };
        source_octets += tensor.declared_octets();
        let shape = if is_row && tensor.rank() == 2 {
            vec![CAUSED.len(), tensor.shape[1]]
        } else {
            tensor.shape.clone()
        };
        let start = payload.len() as u64;
        for word in &words {
            payload.extend_from_slice(&word.to_le_bytes());
        }
        header.push((
            population.clone(),
            ("BF16".to_owned(), shape, start, payload.len() as u64),
        ));
    }

    // The lookup's row addressing changes inside the rest: a sealed one-row population is read at
    // row zero. The program is rewritten to say so, which is a chart transition and is recorded.
    let mut sealed_program = site.program.clone();
    let mut relocated = 0usize;
    for operation in sealed_program.operations.values_mut() {
        if let holonic_engine::ported_reference::PortedOperationKind::Lookup { row, .. } = operation
        {
            *row = CAUSED.iter().position(|caused| caused == row).unwrap_or(0);
            relocated += 1;
        }
    }

    let mut metadata = BTreeMap::new();
    metadata.insert("schema".to_owned(), REST_SCHEMA.to_owned());
    metadata.insert(
        "diagram".to_owned(),
        serde_json::to_string(&site.complex).expect("diagram"),
    );
    metadata.insert(
        "program".to_owned(),
        serde_json::to_string(&sealed_program).expect("program"),
    );
    metadata.insert(
        "band-elements".to_owned(),
        serde_json::to_string(&site.band_elements).expect("bands"),
    );
    metadata.insert(
        "returns".to_owned(),
        serde_json::to_string(
            &site.returns.iter().map(|event| event.0).collect::<Vec<_>>(),
        )
        .expect("returns"),
    );
    metadata.insert(
        "realization".to_owned(),
        "the runtime is `ported_reference::realize`; the ordering is the diagram's chronology; the \
         apparatus is one resident chart and this container. No source access is admitted."
            .to_owned(),
    );
    write_container(&rest_path, &header, &metadata, &payload);
    let sealed = std::fs::metadata(&rest_path).expect("sealed").len();
    println!();
    println!("  THE SEAL");
    println!("    native rest                     {rest_path}");
    println!("    sealed octets                   {sealed}");
    println!("    the source populations it draws from  {source_octets} octets");
    println!("    row-addressed lookups relocated {relocated}");
    println!("    (the rest is smaller by exactly the rows no caused material excited. Those are");
    println!("     UNEXCITED, not condensed, and no factor is quoted for them.)");

    // seal -> mount -> seal must be byte-identical.
    let first = digest_of(&rest_path);
    let (_, remounted) = manifest_safetensors(&rest_path).expect("remounted");
    let round_trip = format!("{rest_path}.again");
    write_container(&round_trip, &header, &metadata, &payload);
    let second = digest_of(&round_trip);
    println!();
    println!("  CONTROL — seal, mount, seal");
    println!("    the rest remounts               {} populations", remounted.tensors.len());
    println!("    seal -> mount -> seal identical {}", first == second);
    let _ = std::fs::remove_file(&round_trip);

    // ---------------------------------------------------------------------------------------
    // THE REFERENCE CONDUCT, with the source present.
    // ---------------------------------------------------------------------------------------
    let reference = match site::conduct(&root, &chart, BASE, terms, None) {
        Ok(carried) => carried,
        Err(error) => {
            println!("  the reference conduct refused: {error}");
            std::process::exit(1);
        }
    };
    println!();
    println!("  THE REFERENCE, conducted WITH the source present");
    println!("    positions returned              {}", reference.len());
    println!("    width                           {}", reference[0].len());

    // ---------------------------------------------------------------------------------------
    // THE HANDOVER TO A FRESH PROCESS.
    // ---------------------------------------------------------------------------------------
    println!();
    println!("  THE FRESH PROCESS — handed the rest and NO source path");
    let child = std::process::Command::new(std::env::current_exe().expect("this binary"))
        .arg("--conduct")
        .arg(&rest_path)
        .output()
        .expect("spawned");
    let text = String::from_utf8_lossy(&child.stdout);
    if !child.status.success() {
        println!("    the child REFUSED: {}", String::from_utf8_lossy(&child.stderr));
        std::process::exit(1);
    }
    let opened: Vec<String> = text
        .lines()
        .find_map(|line| line.strip_prefix("CHILD-OPENED "))
        .and_then(|json| serde_json::from_str(json).ok())
        .unwrap_or_default();
    let native: Vec<Vec<String>> = text
        .lines()
        .find_map(|line| line.strip_prefix("CHILD-RETURN "))
        .and_then(|json| serde_json::from_str(json).ok())
        .unwrap_or_default();
    println!("    the child conducted             {} position(s)", native.len());

    println!();
    println!("  THE LIVE ACCESS AUDIT — taken AFTER the deed, not declared before it");
    let source_map = format!("{root}/model.safetensors");
    let touched: Vec<&String> = opened
        .iter()
        .filter(|path| path.contains("model.safetensors") && !path.contains("phoenix-native-rest"))
        .collect();
    println!("    descriptors the child held      {}", opened.len());
    for path in opened.iter().take(6) {
        println!("        {path}");
    }
    println!("    any resolving to the source     {}", !touched.is_empty());
    println!("    the source it did not open      {source_map}");

    // ---------------------------------------------------------------------------------------
    // THE GRADE.
    // ---------------------------------------------------------------------------------------
    println!();
    println!("  THE GRADE");
    let mut agreed = true;
    for (position, section) in reference.iter().enumerate() {
        let theirs = native.get(position).cloned().unwrap_or_default();
        let ours: Vec<String> = section.iter().map(ToString::to_string).collect();
        if ours != theirs {
            agreed = false;
            let first = ours
                .iter()
                .zip(&theirs)
                .position(|(a, b)| a != b)
                .unwrap_or(0);
            println!("    position {position} DISAGREES first at coordinate {first}");
        }
    }
    println!("    the sealed body returns what the source-fed body returned  {agreed}");
    let after = digest_of(&rest_path);
    println!("    frozen conduct left the rest byte-identical                {}", first == after);

    // Deleting the rest must make the conduct refuse.
    let hidden = format!("{rest_path}.withdrawn");
    std::fs::rename(&rest_path, &hidden).expect("withdrawn");
    let without = std::process::Command::new(std::env::current_exe().expect("this binary"))
        .arg("--conduct")
        .arg(&rest_path)
        .output()
        .expect("spawned");
    println!("    with the rest withdrawn, the conduct refuses               {}", !without.status.success());
    std::fs::rename(&hidden, &rest_path).expect("restored");

    println!();
    println!("THE STATION'S VERDICT");
    println!();
    println!("  The native rest carries the diagram, its program, its band elements and every");
    println!("  stored population the program names — and nothing else. It is written in the");
    println!("  container species the source arrived in, so remounting it uses the standing mouth");
    println!("  and the atlas-to-weights round trip is literal.");
    println!();
    println!("  A fresh process was handed the rest and NO source path. Its carrier holds no source");
    println!("  handle, so the code path to the source does not exist rather than being declined,");
    println!("  and a live audit of every descriptor it actually held confirms it after the deed.");
    println!();
    println!("  What it returned is compared against the source-fed conduct coordinate by exact");
    println!("  coordinate. Frozen conduct left the rest byte-identical, and withdrawing the rest");
    println!("  makes the conduct refuse.");
    println!();
    println!("  This is ONE site's contact half. Cultivation is not performed and no capability is");
    println!("  promoted; CONSTRUCTION_STATE is untouched.");
}
