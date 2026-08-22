//! The real M2 circulation over the source-detached W1 Gemma rest.

use std::collections::BTreeMap;
use std::path::Path;

use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::foreign_codec_rest::ExteriorCodecArtifact;
use holonic_engine::native_rest::MountedNativeRest;
use holonic_engine::phoenix::cohort::circulate_cohort;
use holonic_engine::phoenix::native_streamed::NativeMaterialSource;
use holonic_engine::phoenix::tower::Chart;
use holonic_engine::resident_section::{ResidentGrain, ResidentSurface, SeriesAperture};
use life::mathematical_particle::{
    return_active_transport_family, unchanged_control, ActiveTransportFamily, ExactResponseCochain,
    OpenTransportFibre, UnchangedControl,
};
use serde::Serialize;

use super::{excitation, panel};
use crate::particle::Construction;

const NATIVE_REST: &str =
    "output/the_whole_foreign_map_crosses_into_native_rest/gemma_native_rest.bin";
const NATIVE_PRODUCT: &str = "output/the_whole_foreign_map_crosses_into_native_rest";
/// The established H5 exact receiver and band apertures.  These are inherited experimental
/// controls, not semantic dimensions or retry bounds.
const RECEIVER_GRAIN: u32 = 48;
const SERIES_TERMS: u32 = 14;
const BAND_APERTURE: usize = 12;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct InheritedOpenFibre {
    pub occurrence: String,
    pub question: String,
    pub candidates: Vec<String>,
    pub would_be_decided_by: Vec<String>,
}

#[derive(Serialize)]
pub struct M2Return {
    pub schema: String,
    pub particle_occurrence: String,
    pub native_rest: String,
    pub native_rest_source_identity: String,
    pub receiver_grain: u32,
    pub series_terms: u32,
    pub band_aperture: usize,
    pub families: Vec<ActiveTransportFamily>,
    pub cross_occurrence_controls: Vec<UnchangedControl>,
    pub inherited_m1_open_fibres: Vec<InheritedOpenFibre>,
    pub m2_open_fibres: Vec<OpenTransportFibre>,
}

pub fn run(root: &Path, construction: &Construction) -> Result<M2Return, String> {
    let rest_path = root.join(NATIVE_REST);
    let rest = MountedNativeRest::open(&rest_path).map_err(|error| error.to_string())?;
    let descriptor = rest
        .codebook()
        .codec
        .as_ref()
        .ok_or_else(|| "the W1 rest carries no detached codec descriptor".to_owned())?;
    let product = root.join(NATIVE_PRODUCT).join("codec");
    let tokenizer = product.join(&descriptor.tokenizer_json_sha256);
    let config = descriptor
        .tokenizer_config_sha256
        .as_ref()
        .map(|digest| product.join(digest));
    let codec = ExteriorCodecArtifact::from_paths(&tokenizer, config.as_ref())
        .map_err(|error| error.to_string())?;
    rest.codebook()
        .validate_with_codec(&codec)
        .map_err(|error| error.to_string())?;

    let readout: &'static ResidentReadout =
        Box::leak(Box::new(ResidentReadout::new().map_err(|e| e.to_string())?));
    let surface: &'static ResidentSurface<'static> = Box::leak(Box::new(
        ResidentSurface::on(readout).map_err(|e| e.to_string())?,
    ));
    println!(
        "M2 resident surface: {} · {} free of {} octets",
        surface.device_name(),
        surface.memory_at_mount().free_bytes,
        surface.memory_at_mount().total_bytes
    );

    let typed = construction
        .particle
        .passages()
        .first()
        .ok_or_else(|| "M1 returned no typed passage".to_owned())?;
    let mut families = Vec::new();
    let mut exact = BTreeMap::<String, ExactResponseCochain>::new();
    for generator in &construction.excitation_generators {
        let excitation = excitation::passage(
            generator,
            construction.particle.occurrence(),
            typed,
            &rest,
            &codec,
        )?;
        println!(
            "M2 excitation {}: {} source occurrences · {} presentation octets · {} codewords",
            excitation.occurrence,
            excitation.source_occurrences.len(),
            excitation.generator_octets.len(),
            excitation.codewords.len()
        );
        let declarations = panel::declarations(excitation.codewords.len());
        let mut source = NativeMaterialSource::from_mounted(&rest);
        let cohorted = circulate_cohort(
            surface,
            readout,
            &mut source,
            &excitation.codewords,
            ResidentGrain(RECEIVER_GRAIN),
            SeriesAperture(SERIES_TERMS),
            Chart::Midpoint,
            &declarations,
            BAND_APERTURE,
        )?;
        let returned = return_active_transport_family(excitation, &cohorted)
            .map_err(|refusal| format!("active transport refused: {refusal:?}"))?;
        println!(
            "  returned {} response cochains · {} overlap cells · {} open fibres · {} graph launches",
            returned.receipt.responses.len(),
            returned.receipt.overlap_nerve.len(),
            returned.receipt.open_fibres.len(),
            returned.receipt.apparatus.graph_launches
        );
        exact.insert(
            returned.receipt.excitation.occurrence.clone(),
            returned.base_exact,
        );
        families.push(returned.receipt);
    }

    let cross_occurrence_controls = vec![
        cross_control(
            "baseline-to-reflow receiver control",
            "affine-baseline-excitation",
            "affine-reflow-excitation",
            &exact,
        )?,
        cross_control(
            "same-presentation different-M1-word receiver control",
            "affine-baseline-excitation",
            "quantity-on-affine-presentation-excitation",
            &exact,
        )?,
    ];
    let inherited_m1_open_fibres = construction
        .particle
        .open_fibres()
        .iter()
        .map(|fibre| InheritedOpenFibre {
            occurrence: fibre.occurrence.clone(),
            question: fibre.question.clone(),
            candidates: fibre.candidates.iter().cloned().collect(),
            would_be_decided_by: fibre.would_be_decided_by.iter().cloned().collect(),
        })
        .collect();
    let m2_open_fibres = families
        .iter()
        .flat_map(|family| family.open_fibres.iter().cloned())
        .collect();
    Ok(M2Return {
        schema: "holonics.m2.active-transport-cover.v1".to_owned(),
        particle_occurrence: construction.particle.occurrence().to_owned(),
        native_rest: NATIVE_REST.to_owned(),
        native_rest_source_identity: rest
            .source()
            .container_content_sha256
            .clone()
            .unwrap_or_else(|| rest.source().container_header_sha256.clone()),
        receiver_grain: RECEIVER_GRAIN,
        series_terms: SERIES_TERMS,
        band_aperture: BAND_APERTURE,
        families,
        cross_occurrence_controls,
        inherited_m1_open_fibres,
        m2_open_fibres,
    })
}

fn cross_control(
    occurrence: &str,
    left: &str,
    right: &str,
    exact: &BTreeMap<String, ExactResponseCochain>,
) -> Result<UnchangedControl, String> {
    unchanged_control(
        occurrence,
        exact
            .get(left)
            .ok_or_else(|| format!("{left} exact cochain is absent"))?,
        exact
            .get(right)
            .ok_or_else(|| format!("{right} exact cochain is absent"))?,
    )
    .map_err(|refusal| format!("cross-occurrence control refused: {refusal:?}"))
}
