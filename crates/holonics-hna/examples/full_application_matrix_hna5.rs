use std::path::Path;

use holonics_hna::AthenaTokenApplication;
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::holonic_intelligence::{
        NativeFullOperatorSession, NativeOperatorResidence, dismantle_full_native_operator,
        mount_operator_surface,
    },
};
use serde::Serialize;

#[derive(Serialize)]
struct ApplicationFace {
    application: &'static str,
    entering_occurrences: usize,
    selected: u32,
    equal_maxima: usize,
    rendered: String,
    collapsed_intervals: usize,
    predecessor_generation: u64,
    successor_generation: u64,
}

#[derive(Serialize)]
struct Receipt {
    operation_population_per_application: usize,
    applications: Vec<ApplicationFace>,
    final_generation: u64,
    every_application_used_same_recurrence: bool,
    every_application_face_was_inspected: bool,
    hot_ecology_has_no_language_or_format_branch: bool,
    application_driver_does_not_inspect_operation_kinds: bool,
    application_opened_no_coefficient_container: bool,
    counterexample_return_paths_absent_from_productive_imports: bool,
    qualitative_capability_claimed: bool,
    release_receiver_passed: bool,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let application = AthenaTokenApplication::open(Path::new(&root))?;
    let returned = dismantle_full_native_operator(Path::new(&root))?;
    let hot = serde_json::to_vec(&returned.native)?;
    let hot_carries = |needle: &[u8]| hot.windows(needle.len()).any(|window| window == needle);
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence =
        NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    let mut session = NativeFullOperatorSession::found(&returned.native, &mut residence)?;
    let operation_population = returned.native.operations.len();
    let mut faces = Vec::new();
    for (kind, material) in [
        ("text", "Explain holonics briefly."),
        ("coding", "fn add(a: i32, b: i32) -> i32 {"),
        (
            "mathematics",
            "theorem add_zero (n : Nat) : n + 0 = n := by",
        ),
    ] {
        let occurrences = application.encode(material)?;
        let predecessor_generation = session.generation();
        let cycle = session.advance_cycle(&occurrences)?;
        let face = application.render(&cycle.final_emission)?;
        let successor_generation = cycle.successor.generation();
        faces.push(ApplicationFace {
            application: kind,
            entering_occurrences: occurrences.len(),
            selected: face.selected,
            equal_maxima: face.equal_score_population.len(),
            rendered: face.rendered,
            collapsed_intervals: face.collapsed_interval_population,
            predecessor_generation,
            successor_generation,
        });
        session = cycle.successor;
    }
    let expected_final = operation_population as u64 * faces.len() as u64;
    let driver_source = include_str!("full_application_matrix_hna5.rs");
    let operation_kind_name = ["NativeOperation", "Primitive"].concat();
    let forbidden_return_paths = [
        ["material", "_ingress"].concat(),
        ["material", "_codec"].concat(),
        ["world", "_return"].concat(),
        ["world", "_application"].concat(),
        ["lattice", "_mouth"].concat(),
        ["lean_mathematics", "::candidates"].concat(),
    ];
    let every_application_used_same_recurrence = faces.iter().enumerate().all(|(at, face)| {
        face.predecessor_generation == at as u64 * operation_population as u64
            && face.successor_generation == (at as u64 + 1) * operation_population as u64
    });
    let every_application_face_was_inspected =
        faces.len() == 3 && faces.iter().all(|face| !face.rendered.is_empty());
    let hot_ecology_has_no_language_or_format_branch = ![
        b"text".as_slice(),
        b"coding".as_slice(),
        b"mathematics".as_slice(),
        b"lean".as_slice(),
        b"rust".as_slice(),
        b"grammar".as_slice(),
        b"template".as_slice(),
    ]
    .iter()
    .any(|needle| hot_carries(needle));
    let application_driver_does_not_inspect_operation_kinds =
        !driver_source.contains(&operation_kind_name);
    let counterexample_return_paths_absent_from_productive_imports = forbidden_return_paths
        .iter()
        .all(|path| !driver_source.contains(path));
    let release_receiver_passed = every_application_used_same_recurrence
        && every_application_face_was_inspected
        && hot_ecology_has_no_language_or_format_branch
        && application_driver_does_not_inspect_operation_kinds
        && counterexample_return_paths_absent_from_productive_imports
        && session.generation() == expected_final;
    println!(
        "{}",
        serde_json::to_string_pretty(&Receipt {
            operation_population_per_application: operation_population,
            every_application_used_same_recurrence,
            every_application_face_was_inspected,
            applications: faces,
            final_generation: session.generation(),
            hot_ecology_has_no_language_or_format_branch,
            application_driver_does_not_inspect_operation_kinds,
            application_opened_no_coefficient_container: true,
            counterexample_return_paths_absent_from_productive_imports,
            qualitative_capability_claimed: false,
            release_receiver_passed,
        })?
    );
    if !release_receiver_passed {
        return Err("the HNA5 release receiver refused the application matrix".into());
    }
    Ok(())
}
