//! HNP1 observed-passage application: the target is the actual joined output, not its partner.
//! The driver supplies only SKE-admitted material; the native session owns every return.
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::holonic_intelligence::{
        mount_operator_surface, NativeConeRestrictedEcology, NativeFullOperatorSession,
        NativeOperatorResidence, NativeReturnAperture,
    },
};
use serde_json::json;
use std::{collections::BTreeMap, path::Path};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let rest = std::env::args()
        .nth(1)
        .ok_or("native restricted rest path")?;
    let shift: u32 = std::env::args()
        .nth(2)
        .unwrap_or_else(|| "16".into())
        .parse()?;
    let output = std::env::args().nth(3);
    let layout = std::env::args().nth(4).unwrap_or_else(|| "compact".into());
    if !["compact", "expanded", "compare", "compare-reuse"].contains(&layout.as_str()) {
        return Err("layout must be compact, expanded, compare or compare-reuse".into());
    }
    eprintln!("HNP1: reading the native rest");
    let started = std::time::Instant::now();
    let header = NativeConeRestrictedEcology::read_rest_header(Path::new(&rest))?;
    let preflight = header.ecology.joined_passages()?;
    if preflight.is_empty() {
        return Err("the body has no admitted additive contact".into());
    }
    eprintln!(
        "HNP1: {} native contacts preflighted; loading coefficients",
        preflight.len()
    );
    drop(header);
    let restricted = NativeConeRestrictedEcology::read_rest(Path::new(&rest))?;
    eprintln!(
        "HNP1: coefficient rest read in {:?}; mounting",
        started.elapsed()
    );
    let family: BTreeMap<_, _> = restricted
        .classes
        .iter()
        .flat_map(|class| {
            class
                .fibre
                .iter()
                .map(|held| (held.occurrence, held.addresses.clone()))
        })
        .collect();
    let history = restricted.histories.first().ok_or("empty history family")?;
    let mut occurrences = Vec::new();
    for (_, addresses) in family.into_iter().take(3) {
        restricted
            .admit(&addresses, history)
            .map_err(|e| format!("admission: {e:?}"))?;
        let mut enacted = addresses;
        enacted.extend_from_slice(history);
        occurrences.push(enacted);
    }
    if occurrences.len() != 3
        || occurrences
            .windows(2)
            .any(|pair| pair[1].len() > pair[0].len() && pair[1].starts_with(&pair[0]))
    {
        return Err("this receiver needs three already-admitted non-prefix occurrences".into());
    }
    let outside_refused = restricted.admit(&[u32::MAX], &[]).is_err();
    let receipt = if layout == "compare" || layout == "compare-reuse" {
        let compare_reuse = layout == "compare-reuse";
        let (expanded, left) = run(&restricted, &rest, shift, &occurrences, outside_refused, !compare_reuse, !compare_reuse)?;
        let (compact, right) = run(&restricted, &rest, shift, &occurrences, outside_refused, false, true)?;
        let correspondence = left == right;
        let mut receipt = json!({"schema":if compare_reuse {"holonics.hnp2.segment-reuse-control.v1"} else {"holonics.hnp2.resident-layout-control.v1"},
            "complete_observed_continuation_equal":correspondence,
            "comparison_scope":"all seven terminal sections, three deposit-return words, generations and factor extents; not a serialized full-state comparison",
            });
        if compare_reuse {
            receipt["reference"] = expanded; receipt["candidate"] = compact;
        } else {
            receipt["expanded"] = expanded; receipt["compact"] = compact;
        }
        if !correspondence { return Err("compact and expanded continuation receivers differ".into()); }
        receipt
    } else {
        run(&restricted, &rest, shift, &occurrences, outside_refused, layout == "expanded", true)?.0
    };
    if let Some(output) = output {
        use std::io::Write;
        let output = Path::new(&output);
        if let Some(parent) = output.parent() { std::fs::create_dir_all(parent)?; }
        let mut file = std::fs::OpenOptions::new().write(true).create_new(true).open(output)?;
        file.write_all(serde_json::to_string_pretty(&receipt)?.as_bytes())?;
        println!("{}", json!({"receipt":output,"layout":layout,"passed":true}));
    } else {
        println!("{}", serde_json::to_string_pretty(&receipt)?);
    }
    Ok(())
}

fn run(restricted: &NativeConeRestrictedEcology, rest: &str, shift: u32,
    occurrences: &[Vec<u32>], outside_refused: bool, expanded: bool, reuse: bool,
) -> Result<(serde_json::Value, serde_json::Value), Box<dyn std::error::Error>> {
    let started = std::time::Instant::now();
    eprintln!("HNP2: mounting {} layout", if expanded { "expanded" } else { "compact" });
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let mut intake = restricted.intake(None)?;
    let mut residence = if expanded {
        NativeOperatorResidence::mount_expanded_reference(&surface, &restricted.ecology, &mut intake)?
    } else {
        NativeOperatorResidence::mount_from_intake(&surface, &restricted.ecology, &mut intake)?
    };
    let residence_receipt = residence.receipt().clone();
    let mount_millis = started.elapsed().as_millis();
    eprintln!("HNP1: resident mount complete at {:?}", started.elapsed());
    let mut session = NativeFullOperatorSession::found_with_passage_return(
        &restricted.ecology,
        &mut residence,
        NativeReturnAperture {
            learning_shift: shift,
            series_terms: 14,
        },
    )?;
    if !reuse { session = session.without_forward_reuse(); }
    let contact_population = session.joined_passage_population();
    eprintln!("HNP1: baseline receiver over {contact_population} derived contacts");
    let baseline = session.observe_passage_cycle(&occurrences[0])?;
    let baseline_face = baseline.final_emission.intervals;
    session = baseline.successor;
    let mut cycles = Vec::new();
    let mut semantic_cycles = Vec::new();
    for (at, occurrence) in occurrences.iter().enumerate() {
        eprintln!("HNP1: developmental cycle {at}");
        let before_rank = session.morphology_overlay_rank();
        let before = session.census();
        let reuse_before = session.forward_reuse_census();
        let cycle_started = std::time::Instant::now();
        let cycle = session.advance_cycle(occurrence)?;
        let elapsed_millis = cycle_started.elapsed().as_millis();
        let after = cycle.successor.census();
        let lineage_valid = cycle.traces.iter().all(|trace| trace.numerical_origin.as_ref().is_none_or(|origin|
            origin.occurrence < trace.occurrence && origin.operation == trace.operation.ordinal));
        if !lineage_valid { return Err("a reused numerical passage lost its prior occurrence/operation address".into()); }
        let first_reuse = cycle.traces.iter().find_map(|trace| trace.numerical_origin.as_ref().map(|origin|
            json!({"new_native_occurrence":trace.occurrence,"retained_computation":origin})));
        semantic_cycles.push(json!({"emission":cycle.final_emission,
            "generation":cycle.successor.generation(), "rank":cycle.successor.morphology_overlay_rank(),
            "contacts":cycle.passage_returns}));
        cycles.push(json!({
            "ordinal": at, "before_rank": before_rank,
            "after_rank": cycle.successor.morphology_overlay_rank(),
            "successor_generation": cycle.successor.generation(),
            "section_read_outs": after.section_read_outs - before.section_read_outs,
            "contacts": cycle.passage_returns,
            "elapsed_millis":elapsed_millis,"census_before":before,"census_after":after,
            "reuse_before":reuse_before,"reuse_after":cycle.successor.forward_reuse_census(),
            "prior_numerical_lineage_valid":lineage_valid,"first_reuse":first_reuse,
        }));
        session = cycle.successor;
    }
    eprintln!("HNP1: cultivated receiver");
    let trained = session.observe_passage_cycle(&occurrences[0])?;
    let trained_face = trained.final_emission.intervals;
    session = trained.successor;
    let separator = baseline_face.iter().zip(&trained_face).enumerate()
        .find(|(_, (before, after))| before != after)
        .map(|(coordinate, (before, after))| json!({"coordinate":coordinate,"before":before,"after":after}));
    eprintln!("HNP1: targeted withdrawal");
    let delta = session.withdraw_passage_changes()?;
    let withdrawn_rank = delta.factor_rank();
    let ablated = session.observe_passage_cycle(&occurrences[0])?;
    let ablation_equal = ablated.final_emission.intervals == baseline_face;
    session = ablated.successor;
    session
        .restore_passage_changes(delta)
        .map_err(|(error, _held)| error)?;
    eprintln!("HNP1: restoration receiver");
    let restored = session.observe_passage_cycle(&occurrences[0])?;
    let restoration_equal = restored.final_emission.intervals == trained_face;
    let final_generation = restored.successor.generation();
    let final_rank = restored.successor.morphology_overlay_rank();
    let final_chronology = restored.successor.chronology().to_vec();
    let reuse_census = restored.successor.forward_reuse_census();
    drop(restored.successor);
    let receipt = json!({
        "schema":"holonics.hnp1.observed-passage-control.v1", "source":rest,
        "layout":if expanded {"expanded"} else {"compact"},
        "residence":residence_receipt,"mount_millis":mount_millis,
        "decoder_census":residence.decoder_census(),
        "forward_reuse":reuse,"reuse_census":reuse_census,
        "learning_shift":shift, "occurrences":occurrences,
        "comparison":"actual-joining-output-minus-transported-input",
        "outside_family_refused":outside_refused, "contact_population":contact_population,
        "cycles":cycles, "changed_conduct":separator.is_some(), "separator":separator,
        "withdrawn_rank":withdrawn_rank, "ablation_recovers_baseline":ablation_equal,
        "restoration_recovers_cultivated":restoration_equal,
        "final_generation":final_generation,
        "final_rank":final_rank,
        "total_millis":started.elapsed().as_millis(),
    });
    if separator.is_none() || !ablation_equal || !restoration_equal || !outside_refused {
        return Err("the native contact attribution receiver did not close".into());
    }
    let semantics = json!({"baseline":baseline_face,"trained":trained_face,
        "final_generation":final_generation,"final_rank":final_rank,"chronology":final_chronology,
        "cycles":semantic_cycles,"ablation_recovers_baseline":ablation_equal,
        "restoration_recovers_cultivated":restoration_equal});
    Ok((receipt, semantics))
}
