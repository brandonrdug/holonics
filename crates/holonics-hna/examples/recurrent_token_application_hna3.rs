use std::path::PathBuf;

use holonics_hna::AthenaTextOccurrenceApplication;
use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::holonic_intelligence::{
        ResidentOperatorMorphology, dismantle_native_operator, mount_operator_surface,
    },
};
use serde::Serialize;

#[derive(Serialize)]
struct Receipt {
    schema: &'static str,
    prompt: String,
    prompt_token_population: usize,
    entering_token: u32,
    first_emitted_token: u32,
    first_emitted_surface: String,
    second_emitted_token: u32,
    second_emitted_surface: String,
    first_equal_score_population: usize,
    second_equal_score_population: usize,
    first_collapsed_intervals: usize,
    second_collapsed_intervals: usize,
    score_population: usize,
    first_generation: u64,
    second_generation: u64,
    complete_chronology: Vec<u64>,
    emitted_token_entered_next_occurrence: bool,
    successor_rest_roundtrip_exact: bool,
    remounted_successor_generation: u64,
}

fn complete_branch<'resident, 'morphology, 'chart>(
    session: holonic_engine::native_ecology::holonic_intelligence::NativeOperatorSession<
        'resident,
        'morphology,
        'chart,
    >,
    interaction: &[u16],
) -> Result<
    (
        holonic_engine::native_ecology::holonic_intelligence::NativeOperatorSession<
            'resident,
            'morphology,
            'chart,
        >,
        holonic_engine::native_ecology::holonic_intelligence::NativeOperatorEmission,
    ),
    Box<dyn std::error::Error>,
> {
    let branch = session.advance_branch(interaction)?;
    Ok((
        branch.successor,
        branch.emissions.into_iter().last().ok_or("the branch emitted nothing")?,
    ))
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = std::env::args_os()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/home/b/models/gemma-4-E4B-it"));
    let prompt = std::env::args()
        .nth(2)
        .unwrap_or_else(|| "The receiver".to_owned());
    let returned = dismantle_native_operator(&root, 0)?;
    let mut application = AthenaTextOccurrenceApplication::open(
        &root,
        0,
        returned.native.carrier_extent,
        returned.native.interaction_extent,
    )?;
    let prompt_tokens = application.encode(&prompt)?;
    let entering_token = *prompt_tokens.last().ok_or("the prompt encoded to nothing")?;
    let (carrier, interaction) = application.occurrence_carriers(entering_token)?;

    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let resident = ResidentOperatorMorphology::mount(&surface, &returned.native)?;
    let vocabulary = application.mount_vocabulary(&readout)?;
    let grain = resident.finest_initial_grain(&carrier)?;
    let session = resident.mount_initial(&carrier, grain)?;
    let (session, first_native) = complete_branch(session, &interaction)?;
    let first = application.render_token(&vocabulary, &first_native)?;

    let successor_rest = session.rest()?;
    let successor_wire = successor_rest.canonical_bytes()?;
    let read_rest = holonic_engine::native_ecology::holonic_intelligence::NativeOperatorSessionRest::read(
        &successor_wire,
    )?;
    let successor_rest_roundtrip_exact = read_rest.canonical_bytes()? == successor_wire;
    let session = resident.remount_session(&read_rest)?;
    let remounted_successor_generation = session.generation();
    let (_, second_interaction) = application.occurrence_carriers(first.selected)?;
    let (session, second_native) = complete_branch(session, &second_interaction)?;
    let second = application.render_token(&vocabulary, &second_native)?;
    let emitted_token_entered_next_occurrence = !second_interaction.is_empty()
        && session.generation() == 12
        && session.chronology() == (0..12u64).collect::<Vec<_>>()
        && successor_rest_roundtrip_exact
        && remounted_successor_generation == 6;
    if !emitted_token_entered_next_occurrence {
        return Err("the emitted application token did not enter the successor recurrence".into());
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&Receipt {
            schema: "athena-alpha.recurrent-token-application-hna3.v1",
            prompt,
            prompt_token_population: prompt_tokens.len(),
            entering_token,
            first_emitted_token: first.selected,
            first_emitted_surface: first.rendered,
            second_emitted_token: second.selected,
            second_emitted_surface: second.rendered,
            first_equal_score_population: first.equal_score_population.len(),
            second_equal_score_population: second.equal_score_population.len(),
            first_collapsed_intervals: first.collapsed_interval_population,
            second_collapsed_intervals: second.collapsed_interval_population,
            score_population: first.score_population,
            first_generation: first_native.generation,
            second_generation: second_native.generation,
            complete_chronology: session.chronology().to_vec(),
            emitted_token_entered_next_occurrence,
            successor_rest_roundtrip_exact,
            remounted_successor_generation,
        })?
    );
    Ok(())
}
