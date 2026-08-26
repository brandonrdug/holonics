//! Compact M2 artifact and executable grade.

use std::path::Path;

use sha2::{Digest, Sha256};

use super::deed::M2Return;

const OUT: &str = "output/the_mathematics_codec_excites_the_active_transport_cover";

pub fn write(root: &Path, returned: &M2Return) -> Result<(), String> {
    let out = root.join(OUT);
    std::fs::create_dir_all(&out).map_err(|error| error.to_string())?;
    // The support carrier can contain millions of exact half-open runs.  Whitespace is an
    // exterior rendering choice and must not multiply the semantic artifact's storage cost.
    let semantic = serde_json::to_vec(returned).map_err(|error| error.to_string())?;
    let semantic_path = out.join("active-transport-cover.json");
    std::fs::write(&semantic_path, &semantic).map_err(|error| error.to_string())?;
    let semantic_sha256 = digest(&semantic);

    let family_count = returned.families.len();
    let response_count = returned
        .families
        .iter()
        .map(|family| family.responses.len())
        .sum::<usize>();
    let every_cochain_complete = returned.families.iter().all(|family| {
        family.responses.iter().all(|response| {
            response.cochain.faces.len() == holonic_engine::phoenix::tower::LAYERS * 3 + 2
        })
    });
    let every_family_has_nerve = returned
        .families
        .iter()
        .all(|family| !family.overlap_nerve.is_empty());
    let every_family_resident = returned.families.iter().all(|family| {
        family.apparatus.graph_launches > 0
            && family.apparatus.terminal_synchronizations > 0
            && family.residency.admitted_resident_octets > 0
            && family
                .responses
                .iter()
                .all(|response| !response.realization.phases.is_empty())
    });
    let separated_transports = returned
        .families
        .iter()
        .flat_map(|family| &family.responses)
        .filter(|response| response.support.first_separator.is_some())
        .count();
    let unchanged_controls_held = returned
        .families
        .iter()
        .flat_map(|family| &family.unchanged_controls)
        .chain(&returned.cross_occurrence_controls)
        .all(|control| control.held && control.first_separator.is_none());
    let source_words_returned = returned.families.iter().all(|family| {
        !family.excitation.generator_octets.is_empty()
            && !family.excitation.source_occurrences.is_empty()
            && !family.excitation.particle_word.is_empty()
    });
    let complete_open_fibres = !returned.inherited_m1_open_fibres.is_empty()
        && returned
            .families
            .iter()
            .all(|family| !family.open_fibres.is_empty());
    let passed = family_count == 5
        && response_count == family_count * 19
        && every_cochain_complete
        && every_family_has_nerve
        && every_family_resident
        && separated_transports > 0
        && unchanged_controls_held
        && source_words_returned
        && complete_open_fibres;
    let grade = format!(
        "M2 ACTIVE TRANSPORT COVER\n\
truth-status: {}\n\
semantic-artifact: {}\n\
semantic-sha256: {}\n\
families: {}\n\
responses: {}\n\
ordered-cochains-complete: {}\n\
every-family-has-witnessed-overlap-nerve: {}\n\
four-activity-faces-returned: {}\n\
receiver-separated-transports: {}\n\
unchanged-controls-held: {}\n\
source-generators-and-words-returned: {}\n\
open-fibres-retained: {}\n\
boundary: bounded five-excitation frozen-W1 Gemma cover; no generator-native quotient, compression, cultivation, theorem proof, or M3/M4 completion\n",
        if passed {
            "established-bounded"
        } else {
            "refuted"
        },
        semantic_path
            .strip_prefix(root)
            .map_err(|_| "M2 artifact left workspace".to_owned())?
            .display(),
        semantic_sha256,
        family_count,
        response_count,
        every_cochain_complete,
        every_family_has_nerve,
        every_family_resident,
        separated_transports,
        unchanged_controls_held,
        source_words_returned,
        complete_open_fibres,
    );
    std::fs::write(out.join("grade.form"), grade.as_bytes()).map_err(|error| error.to_string())?;
    println!(
        "M2 {} — {} families, {} responses, {} receiver-separated transports, semantic sha256 {}",
        if passed { "PASSED" } else { "REFUTED" },
        family_count,
        response_count,
        separated_transports,
        semantic_sha256
    );
    if passed {
        Ok(())
    } else {
        Err("M2 grade refused the returned cover".to_owned())
    }
}

fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
