use std::fs;
use std::path::{Path, PathBuf};

use holonic_engine::phoenix::inference_ecology::InferenceEcologyRest;
use life::mathematical_particle::{
    DynamicMorphologyRest, LongHorizonRetainedBoundary, MultimodalTransportRest,
    ProductionAthenaRest,
};

use super::artifact;

pub const OUTPUT_NAME: &str = "the_bounded_athena_mathematics_physics_ecology_freezes";

pub fn found(root: &Path) -> Result<ProductionAthenaRest, String> {
    let i5 = root.join("output/the_athena_gemma_ecology_infers_returns_and_remounts/native-rest");
    let inference = InferenceEcologyRest::read(
        &read(i5.join("recurrent-standing.json"))?,
        &read(i5.join("recurrent-decoder.json"))?,
        &read(i5.join("recurrent-fibres.json"))?,
        &read(i5.join("heterogeneous-standing.json"))?,
        &read(i5.join("heterogeneous-decoder.json"))?,
        &read(i5.join("heterogeneous-fibres.json"))?,
        &read(i5.join("inference-junction.json"))?,
    )
    .map_err(|error| error.to_string())?;
    let morphology = DynamicMorphologyRest::read(&read(root.join(
        "output/the_returned_constraints_found_dynamic_local_morphology/04-source-detached-dynamic-morphology-rest.json",
    ))?)
    .map_err(|error| error.to_string())?;
    let r4 = root
        .join("output/the_retained_causal_boundary_carries_the_long_horizon_inquiry/native-rest");
    let retained = LongHorizonRetainedBoundary::read(
        &read(r4.join("standing.json"))?,
        &read(r4.join("decoder.json"))?,
        &read(r4.join("fibres.json"))?,
    )
    .map_err(|error| error.to_string())?;
    let r5 =
        root.join("output/the_mathematical_and_physical_faces_share_native_transport/native-rest");
    let media = MultimodalTransportRest::read(
        &read(r5.join("standing.json"))?,
        &read(r5.join("decoder.bin"))?,
        &read(r5.join("fibres.json"))?,
    )
    .map_err(|error| error.to_string())?;
    ProductionAthenaRest::found(
        inference,
        morphology,
        retained,
        media,
        development_closure(root)?,
        "r6/production-junction/declined-before-world-return".to_owned(),
    )
    .map_err(|error| error.to_string())
}

pub fn write(
    rest: &ProductionAthenaRest,
    directory: &Path,
) -> Result<(PathBuf, PathBuf, PathBuf), String> {
    fs::create_dir_all(directory).map_err(|error| error.to_string())?;
    let standing = directory.join("standing.bin");
    let decoder = directory.join("decoder.bin");
    let fibres = directory.join("fibres.bin");
    fs::write(
        &standing,
        rest.standing_bytes().map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    fs::write(
        &decoder,
        rest.decoder_bytes().map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    fs::write(
        &fibres,
        rest.fibre_bytes().map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let reopened = ProductionAthenaRest::read(&read(&standing)?, &read(&decoder)?, &read(&fibres)?)
        .map_err(|error| error.to_string())?;
    if reopened
        .canonical_identity()
        .map_err(|error| error.to_string())?
        != rest
            .canonical_identity()
            .map_err(|error| error.to_string())?
    {
        return Err("the written production rest did not reopen as the same ecology".to_owned());
    }
    Ok((standing, decoder, fibres))
}

fn development_closure(root: &Path) -> Result<Vec<String>, String> {
    let families = [
        "the_rich_mathematical_inquiry_returns_the_i5_baseline_boundary",
        "the_rich_intake_returns_one_codec_neutral_operation_world_tube",
        "the_material_derivation_recurs_until_the_requested_receiver_returns_or_obstructs",
        "the_returned_constraints_found_dynamic_local_morphology",
        "the_retained_causal_boundary_carries_the_long_horizon_inquiry",
        "the_mathematical_and_physical_faces_share_native_transport",
    ];
    let mut closure = Vec::new();
    for family in families {
        let directory = root.join("output").join(family);
        for path in artifact::regular_files(&directory)? {
            let bytes = read(&path)?;
            let relative = path
                .strip_prefix(root)
                .map_err(|error| error.to_string())?
                .to_string_lossy();
            closure.push(format!(
                "development/{relative}/{}",
                artifact::digest(&bytes)
            ));
        }
    }
    closure.sort();
    closure.dedup();
    Ok(closure)
}

fn read(path: impl AsRef<Path>) -> Result<Vec<u8>, String> {
    let path = path.as_ref();
    fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))
}
