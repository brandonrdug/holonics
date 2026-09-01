//! Conduct one complete native scaffold through the codec-neutral HIF3 circulation.

use std::{collections::BTreeSet, env, fs};

use holonic_engine::native_ecology::holonic_intelligence::{
    BinaryEmissionCodec, ExteriorEmissionCodec, InferenceCirculation, NativeInferenceAddress,
    NativeInferenceRequest, Utf8InspectionCodec, conduct_native_inference,
};
use holonic_engine::native_spool::NativeTransportScaffold;
use serde_json::json;

fn main() -> Result<(), String> {
    let address = env::args()
        .nth(1)
        .ok_or("usage: inspect_native_inference_circulation_hif3 NATIVE_SPOOL_BUNDLE")?;
    let scaffold =
        NativeTransportScaffold::read(&fs::read(&address).map_err(display)?).map_err(display)?;
    let caused_predecessors = scaffold
        .spools
        .iter()
        .flat_map(|spool| &spool.threads)
        .flat_map(|thread| &thread.occurrences)
        .filter_map(|occurrence| occurrence.predecessor)
        .collect::<BTreeSet<_>>();
    let (spool, thread, occurrence) = scaffold
        .spools
        .iter()
        .flat_map(|spool| {
            spool.threads.iter().flat_map(move |thread| {
                thread
                    .occurrences
                    .iter()
                    .map(move |occurrence| (spool, thread, occurrence))
            })
        })
        .find(|(_, _, occurrence)| caused_predecessors.contains(&occurrence.occurrence))
        .or_else(|| {
            scaffold.spools.iter().find_map(|spool| {
                spool.threads.iter().find_map(|thread| {
                    thread
                        .occurrences
                        .first()
                        .map(|occurrence| (spool, thread, occurrence))
                })
            })
        })
        .ok_or("empty occurrence population")?;
    let receiver = *spool
        .receiver_family
        .first()
        .ok_or("empty receiver family")?;
    let circulation = conduct_native_inference(
        &scaffold,
        NativeInferenceRequest {
            address: NativeInferenceAddress {
                spool: spool.address.clone(),
                thread: thread.address.clone(),
                occurrence: occurrence.occurrence,
            },
            receiver,
        },
    )
    .map_err(display)?;
    let text = Utf8InspectionCodec
        .render(circulation.face())
        .map_err(display)?;
    let binary = BinaryEmissionCodec
        .render(circulation.face())
        .map_err(display)?;
    let binary_round_trip = BinaryEmissionCodec::read(&binary).map_err(display)?;
    let successor_request_population = circulation.successor_requests().len();
    let later_current = circulation
        .successor_requests()
        .first()
        .cloned()
        .map(|request| conduct_native_inference(&scaffold, request).map_err(display))
        .transpose()?;
    let receipt = json!({
        "schema":"holonic-engine.native-inference-circulation-inspection.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "scaffold":scaffold.address,
        "entering_occurrence":circulation.entering_occurrence().occurrence.0,
        "receiver":circulation.receiver().0,
        "word_population":circulation.face().ordered_word.len(),
        "plural_future_population":circulation.face().plural_futures.len(),
        "emitted":circulation.emitted_occurrence(),
        "reconstruction_fibre_population":circulation.reconstruction().fibres.len(),
        "shortest_separator_population":circulation.reconstruction().shortest_separators.len(),
        "open_obligation_population":circulation.open_obligations().len(),
        "successor_request_population":successor_request_population,
        "later_current_conducted":later_current.is_some(),
        "later_plural_future_population":later_current
            .as_ref()
            .map(|returned| returned.face().plural_futures.len()),
        "text_surface_octets":text.len(),
        "binary_surface_octets":binary.len(),
        "binary_round_trip_exact":binary_round_trip == *circulation.face(),
        "morphology_fixed":circulation.morphology_is_fixed(),
        "resident_device":circulation.conducted_section().device,
        "resident_launches":circulation.conducted_section().apparatus.launches,
        "invariant_transport_reuploaded":circulation
            .conducted_section()
            .apparatus
            .invariant_transport_reuploaded,
        "codec_selected_native_conduct":false,
        "authored_response_extent":false,
        "foreign_executor_reachable":false,
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&receipt).map_err(display)?
    );
    Ok(())
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
