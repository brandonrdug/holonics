use std::fs;
use std::path::{Path, PathBuf};

use holonic_engine::{
    generator_native_rest::GeneratorNativeRest,
    receiver_history_cultivation::CultivatedReceiverHistoryRest,
};
use life::mathematical_particle::{LaboratoryAthenaRest, ProductionAthenaRest};

use super::source;

pub const OUTPUT_NAME: &str = "the_laboratory_chronology_cultivates_the_athena_mathematics_ecology";

pub fn found(root: &Path) -> Result<LaboratoryAthenaRest, String> {
    let r6 = root.join("output/the_bounded_athena_mathematics_physics_ecology_freezes/native-rest");
    let production = ProductionAthenaRest::read(
        &read(r6.join("standing.bin"))?,
        &read(r6.join("decoder.bin"))?,
        &read(r6.join("fibres.bin"))?,
    )
    .map_err(|error| error.to_string())?;
    let native_bytes = read(root.join(
        "output/the_active_cover_condenses_into_a_generator_native_codec/generator-native-rest.json",
    ))?;
    let native = GeneratorNativeRest::read(&native_bytes).map_err(|error| error.to_string())?;
    let cultivated_bytes = read(root.join(
        "output/the_native_codec_is_cultivated_and_returns_complete_mathematics/cultivated-receiver-history-rest.json",
    ))?;
    let cultivated_history: CultivatedReceiverHistoryRest = serde_json::from_slice(&cultivated_bytes)
        .map_err(|error| error.to_string())?;
    CultivatedReceiverHistoryRest::mount(&cultivated_bytes, &native_bytes)
        .map_err(|error| error.to_string())?;
    LaboratoryAthenaRest::found(
        production,
        native,
        cultivated_history,
        source::mount(root)?,
        "l0/laboratory-junction/declined-before-lean-return".to_owned(),
    )
    .map_err(|error| error.to_string())
}

pub fn write(
    rest: &LaboratoryAthenaRest,
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
    let reopened = LaboratoryAthenaRest::read(&read(&standing)?, &read(&decoder)?, &read(&fibres)?)
        .map_err(|error| error.to_string())?;
    if reopened
        .canonical_identity()
        .map_err(|error| error.to_string())?
        != rest
            .canonical_identity()
            .map_err(|error| error.to_string())?
    {
        return Err("the written L0 rest did not reopen as the same ecology".to_owned());
    }
    Ok((standing, decoder, fibres))
}

fn read(path: impl AsRef<Path>) -> Result<Vec<u8>, String> {
    let path = path.as_ref();
    fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))
}
