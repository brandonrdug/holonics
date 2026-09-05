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
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let mut intake = restricted.intake(None)?;
    let mut residence =
        NativeOperatorResidence::mount_from_intake(&surface, &restricted.ecology, &mut intake)?;
    eprintln!("HNP1: resident mount complete at {:?}", started.elapsed());
    let mut session = NativeFullOperatorSession::found_with_passage_return(
        &restricted.ecology,
        &mut residence,
        NativeReturnAperture {
            learning_shift: shift,
            series_terms: 14,
        },
    )?;
    let contact_population = session.joined_passage_population();
    eprintln!("HNP1: baseline receiver over {contact_population} derived contacts");
    let baseline = session.observe_passage_cycle(&occurrences[0])?;
    let baseline_face = baseline.final_emission.intervals;
    session = baseline.successor;
    let mut cycles = Vec::new();
    for (at, occurrence) in occurrences.iter().enumerate() {
        eprintln!("HNP1: developmental cycle {at}");
        let before_rank = session.morphology_overlay_rank();
        let before = session.census();
        let cycle = session.advance_cycle(occurrence)?;
        let after = cycle.successor.census();
        cycles.push(json!({
            "ordinal": at, "before_rank": before_rank,
            "after_rank": cycle.successor.morphology_overlay_rank(),
            "successor_generation": cycle.successor.generation(),
            "section_read_outs": after.section_read_outs - before.section_read_outs,
            "contacts": cycle.passage_returns,
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
    let receipt = json!({
        "schema":"holonics.hnp1.observed-passage-control.v1", "source":rest,
        "learning_shift":shift, "occurrences":occurrences,
        "comparison":"actual-joining-output-minus-transported-input",
        "outside_family_refused":outside_refused, "contact_population":contact_population,
        "cycles":cycles, "changed_conduct":separator.is_some(), "separator":separator,
        "withdrawn_rank":withdrawn_rank, "ablation_recovers_baseline":ablation_equal,
        "restoration_recovers_cultivated":restoration_equal,
        "final_generation":restored.successor.generation(),
        "final_rank":restored.successor.morphology_overlay_rank(),
    });
    if let Some(output) = output {
        use std::io::Write;
        let output = Path::new(&output);
        if let Some(parent) = output.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(output)?;
        file.write_all(serde_json::to_string_pretty(&receipt)?.as_bytes())?;
        println!(
            "{}",
            json!({"receipt":output,"changed_conduct":separator.is_some(),
            "ablation_recovers_baseline":ablation_equal,"restoration_recovers_cultivated":restoration_equal})
        );
    } else {
        println!("{}", serde_json::to_string_pretty(&receipt)?);
    }
    if separator.is_none() || !ablation_equal || !restoration_equal || !outside_refused {
        return Err("the native contact attribution receiver did not close".into());
    }
    Ok(())
}
