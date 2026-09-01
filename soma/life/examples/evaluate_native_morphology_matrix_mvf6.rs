use std::{env, error::Error, path::PathBuf};

use holonic_engine::{
    native_ecology::holonic_intelligence::{
        read_complete_gemma4_excitation_receipt, ExteriorModality, ForeignBf16Excitation,
        Gemma4ExcitationFamily,
    },
    receiver_exact_compression::ReceiverId,
    ExactComplexWaveCurrent,
};
use life::native_intelligence::{
    evaluate_morphology_configuration, MorphologyExperimentInput, MorphologyExperimentReceipt,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::Serialize;
use serde_json::json;

#[derive(Serialize)]
struct MatrixEntry {
    aperture: String,
    same_configuration_repeat_performed: bool,
    receipt: MorphologyExperimentReceipt,
}

#[derive(Serialize)]
struct CrossConfigurationPair {
    left: String,
    right: String,
    complete_receiver_history_equivalent: bool,
}

fn main() -> Result<(), Box<dyn Error>> {
    let root = env::args()
        .nth(1)
        .map(PathBuf::from)
        .ok_or("usage: evaluate_native_morphology_matrix_mvf6 RETURN_DIR [APERTURE]")?;
    let aperture_filter = env::args().nth(2);
    let receipt = read_complete_gemma4_excitation_receipt(&root)?;
    let controls = vec![
        (
            "text-to-text".to_owned(),
            family(&receipt.families, ExteriorModality::Text)?,
        ),
        (
            "rendered-image-to-text".to_owned(),
            family(&receipt.families, ExteriorModality::Image)?,
        ),
        (
            "spoken-audio-to-text".to_owned(),
            family(&receipt.families, ExteriorModality::Audio)?,
        ),
        (
            "temporal-video-to-text".to_owned(),
            family(&receipt.families, ExteriorModality::Video)?,
        ),
        (
            "mixed-chronological-to-text".to_owned(),
            receipt
                .families
                .iter()
                .filter_map(|family| family.excitations.first().cloned())
                .collect(),
        ),
    ]
    .into_iter()
    .filter(|(aperture, _)| {
        aperture_filter
            .as_ref()
            .is_none_or(|filter| filter == aperture)
    })
    .collect::<Vec<_>>();
    if controls.is_empty() {
        return Err("requested aperture is absent".into());
    }
    let mut entries = Vec::new();
    for (ordinal, (aperture, excitations)) in controls.into_iter().enumerate() {
        let input = MorphologyExperimentInput {
            aperture: aperture.clone(),
            excitations,
            receiver: ReceiverId(100 + ordinal as u64),
            exterior_current: ExactComplexWaveCurrent::new(
                Rat::from_integer(BigInt::from(ordinal + 1)),
                Rat::from_integer(BigInt::from(1)),
            ),
            storage: Rat::from_integer(BigInt::from(1)),
        };
        let first = evaluate_morphology_configuration(input)?;
        entries.push(MatrixEntry {
            aperture,
            same_configuration_repeat_performed: false,
            receipt: first,
        });
    }
    let mut pairs = Vec::new();
    for left in 0..entries.len() {
        for right in left + 1..entries.len() {
            let left_receipt = &entries[left].receipt.stable;
            let right_receipt = &entries[right].receipt.stable;
            let equivalent = left_receipt.native_thread_order == right_receipt.native_thread_order
                && left_receipt.before_withdrawal == right_receipt.before_withdrawal
                && left_receipt.after_source_detached_remount
                    == right_receipt.after_source_detached_remount
                && left_receipt.anatomy == right_receipt.anatomy;
            pairs.push(CrossConfigurationPair {
                left: entries[left].aperture.clone(),
                right: entries[right].aperture.clone(),
                complete_receiver_history_equivalent: equivalent,
            });
        }
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema": "holonics.mvf6.configuration-matrix.v1",
            "same_proposition_is_exterior_control": true,
            "same_configuration_repeat_is_a_separate_control": true,
            "qualitative_surfaces_are_probes": true,
            "cross_codec_equivalence_requires_complete_receiver_history": true,
            "entries": entries,
            "cross_configuration_pairs": pairs,
        }))?
    );
    Ok(())
}

fn family(
    families: &[Gemma4ExcitationFamily],
    modality: ExteriorModality,
) -> Result<Vec<ForeignBf16Excitation>, Box<dyn Error>> {
    families
        .iter()
        .find(|family| family.modality == modality)
        .map(|family| family.excitations.clone())
        .ok_or_else(|| format!("complete {modality:?} family absent").into())
}
