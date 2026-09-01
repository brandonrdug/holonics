use std::{collections::BTreeSet, env, error::Error, path::PathBuf};

use holonic_engine::{
    native_ecology::holonic_intelligence::{
        compare_contact_charts, conduct_repeated_inference,
        read_complete_gemma4_excitation_receipt, Bf16ExcitationDismantling, ContactEdge,
        ExteriorModality, ForeignBf16Excitation, NativeContinuationDecision,
        NativeContinuationReceiver, NativeCycleDisposition, NativeInferenceAddress,
        NativeInferenceRequest, NativeVariableGrainEmission,
    },
    receiver_exact_compression::{Observation, ReceiverId},
    soulkiller::dismantle,
    BoundaryId, EventId, ExactComplexWaveCurrent,
};
use life::native_intelligence::{
    consume_dismantling_return, ReturnedScaffoldInteraction, ScaffoldCultivatedRest,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::Serialize;
use serde_json::json;

#[derive(Clone, Copy, Debug, Serialize)]
#[serde(rename_all = "kebab-case")]
enum Experiment {
    TextToText,
    ImageToText,
    AudioToText,
    SampledVideoToText,
    InterleavedMultimodalToText,
}

#[derive(Serialize)]
struct ExperimentReturn {
    experiment: Experiment,
    excitation_population: usize,
    cold_coordinates_absent: bool,
    cold_label_mutation_preserved_native_routing: bool,
    circulation_cuts: usize,
    variable_grain_population: usize,
    source_detached_consequence_preserved: bool,
    cultivated_ablation_removed_conduct: bool,
    outside_cone_morphology_unchanged: bool,
    causal_cone_population: usize,
    final_hot_thread_population: usize,
    departed_inherited_thread_population: usize,
    contact_chart_population: usize,
    richer_receiver_reopening_population: usize,
}

struct CultivateAtFirst {
    occurrence: EventId,
    emitting_boundary: BoundaryId,
    exterior_current: ExactComplexWaveCurrent,
    storage: Rat,
}

impl NativeContinuationReceiver<ReturnedScaffoldInteraction> for CultivateAtFirst {
    fn receive(
        &self,
        emission: &NativeVariableGrainEmission,
        _successors: &[NativeInferenceRequest],
    ) -> NativeContinuationDecision<ReturnedScaffoldInteraction> {
        let returned = ReturnedScaffoldInteraction::found(
            emission.address.clone(),
            self.occurrence,
            self.emitting_boundary,
            self.exterior_current.clone(),
            self.storage.clone(),
            BTreeSet::new(),
        )
        .expect("the fixture supplies a nonzero later exterior interaction");
        NativeContinuationDecision::Cultivate {
            returned_occurrence: returned.occurrence,
            returned,
        }
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let root = env::args()
        .nth(1)
        .map(PathBuf::from)
        .ok_or("usage: complete_native_transport_scaffold_cycle_scf6 RETURN_DIR")?;
    let receipt = read_complete_gemma4_excitation_receipt(&root)?;
    let text = family(&receipt.families, ExteriorModality::Text)?;
    let image = family(&receipt.families, ExteriorModality::Image)?;
    let audio = family(&receipt.families, ExteriorModality::Audio)?;
    let video = family(&receipt.families, ExteriorModality::Video)?;
    let groups = vec![
        (Experiment::TextToText, text),
        (Experiment::ImageToText, image),
        (Experiment::AudioToText, audio),
        (Experiment::SampledVideoToText, video),
        (
            Experiment::InterleavedMultimodalToText,
            receipt.interleaved(),
        ),
    ];
    let returns = groups
        .into_iter()
        .enumerate()
        .map(|(at, (experiment, excitations))| run(experiment, excitations, at as u64))
        .collect::<Result<Vec<_>, Box<dyn Error>>>()?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema": "holonics.scf6.complete-native-transport-scaffold-cycle.v1",
            "generated_surfaces_are_probes": true,
            "surface_selected_native_routing": false,
            "foreign_executor_reachable_after_handoff": false,
            "experiments": returns,
        }))?
    );
    Ok(())
}

fn family(
    families: &[holonic_engine::native_ecology::holonic_intelligence::Gemma4ExcitationFamily],
    modality: ExteriorModality,
) -> Result<Vec<ForeignBf16Excitation>, Box<dyn Error>> {
    families
        .iter()
        .find(|family| family.modality == modality)
        .map(|family| family.excitations.clone())
        .ok_or_else(|| "complete modality family absent".into())
}

fn run(
    experiment: Experiment,
    excitations: Vec<ForeignBf16Excitation>,
    ordinal: u64,
) -> Result<ExperimentReturn, Box<dyn Error>> {
    if excitations.len() < 2 {
        return Err("an SCF6 experiment requires an intervention-separated return".into());
    }
    let receiver = ReceiverId(100 + ordinal);
    let lifted = dismantle(Bf16ExcitationDismantling {
        receiver,
        excitations: excitations.clone(),
    })?;
    let native_wire = lifted.native.canonical_bytes()?;
    let native_text = String::from_utf8(native_wire.clone())?.to_ascii_lowercase();
    let cold_coordinates_absent = ["text", "image", "audio", "video", "source-sha256"]
        .iter()
        .all(|coordinate| !native_text.contains(coordinate));

    let mut relabeled = excitations.clone();
    for (at, excitation) in relabeled.iter_mut().enumerate() {
        excitation.source_occurrence = format!("renamed-cold-occurrence/{at}");
        excitation.exterior_modality = ExteriorModality::Text;
    }
    let relabeled_native = dismantle(Bf16ExcitationDismantling {
        receiver,
        excitations: relabeled,
    })?;
    let cold_label_mutation_preserved_native_routing =
        relabeled_native.native.canonical_bytes()? == native_wire;

    let spool = &lifted.native.spools[0];
    let source_thread = &spool.threads[0];
    let source_occurrence = source_thread.occurrences[0].occurrence;
    let source = NativeInferenceAddress {
        spool: spool.address.clone(),
        thread: source_thread.address.clone(),
        occurrence: source_occurrence,
    };
    let returned_occurrence = EventId(
        spool
            .threads
            .iter()
            .flat_map(|thread| &thread.occurrences)
            .map(|occurrence| occurrence.occurrence.0)
            .max()
            .ok_or("native occurrence population absent")?
            + 1,
    );
    let request = NativeInferenceRequest {
        address: source.clone(),
        receiver,
    };
    let repeated = conduct_repeated_inference(
        &lifted.native,
        request,
        &CultivateAtFirst {
            occurrence: returned_occurrence,
            emitting_boundary: BoundaryId(10_000 + ordinal),
            exterior_current: ExactComplexWaveCurrent::new(
                Rat::from_integer(BigInt::from(ordinal + 1)),
                Rat::from_integer(BigInt::from(1)),
            ),
            storage: Rat::from_integer(BigInt::from(1)),
        },
    )?;
    let circulation_cuts = repeated.cuts.len();
    let variable_grain_population = repeated
        .emissions
        .iter()
        .map(|emission| emission.grains.len())
        .sum();
    let returned = match repeated.dispositions.as_slice() {
        [NativeCycleDisposition::Cultivate { returned, .. }] => returned.clone(),
        _ => return Err("the common public cycle did not return cultivation".into()),
    };
    drop(repeated);

    let states = lifted.native.spools[0]
        .native_population
        .iter()
        .copied()
        .collect::<Vec<_>>();
    let recurrent = lifted.native.spools[0]
        .threads
        .iter()
        .flat_map(|thread| &thread.occurrences)
        .map(|occurrence| ContactEdge {
            from: occurrence.entering_native,
            to: occurrence.emitting_native,
        })
        .collect::<Vec<_>>();
    let current_founded = recurrent.clone();
    let coarse = states
        .iter()
        .map(|state| (*state, Observation(0)))
        .collect::<Vec<_>>();
    let rich = states
        .iter()
        .map(|state| (*state, Observation(state.0)))
        .collect::<Vec<_>>();
    let charts = compare_contact_charts(
        &states,
        &recurrent,
        &current_founded,
        receiver,
        &coarse,
        &rich,
    )?;

    let (hot, departed) = consume_dismantling_return(lifted)?;
    let cultivated = ScaffoldCultivatedRest::cultivate(hot, source, returned)?;
    let released = cultivated.release()?;
    Ok(ExperimentReturn {
        experiment,
        excitation_population: departed.cold_witness.excitations.len(),
        cold_coordinates_absent,
        cold_label_mutation_preserved_native_routing,
        circulation_cuts,
        variable_grain_population,
        source_detached_consequence_preserved: released.receipt.declared_consequence_preserved,
        cultivated_ablation_removed_conduct: released.receipt.cultivated_ablation_removed_conduct,
        outside_cone_morphology_unchanged: released.receipt.outside_cone_morphology_unchanged,
        causal_cone_population: released.receipt.causal_cone_population,
        final_hot_thread_population: released
            .hot
            .native()
            .spools
            .iter()
            .map(|spool| spool.threads.len())
            .sum(),
        departed_inherited_thread_population: released.departed_inherited.len(),
        contact_chart_population: charts.returns.len(),
        richer_receiver_reopening_population: charts.richer_receiver_reopenings.len(),
    })
}
