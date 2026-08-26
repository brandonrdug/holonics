use std::fs;
use std::path::{Path, PathBuf};

use life::mathematical_particle::{FamilyCultivatedAthenaRest, LaboratoryAthenaRest};

use super::source;

pub const OUTPUT_NAME: &str = "returned_theorem_families_cultivate_the_continuing_laboratory_rest";

pub fn found(root: &Path) -> Result<FamilyCultivatedAthenaRest, String> {
    let l0 = root.join(
        "output/the_laboratory_chronology_cultivates_the_athena_mathematics_ecology/native-rest",
    );
    let predecessor = LaboratoryAthenaRest::read(
        &read(l0.join("standing.bin"))?,
        &read(l0.join("decoder.bin"))?,
        &read(l0.join("fibres.bin"))?,
    )
    .map_err(|error| error.to_string())?;
    FamilyCultivatedAthenaRest::found(
        predecessor,
        source::mount(root)?,
        "l1/family-junction/no-returned-plates".to_owned(),
    )
    .map_err(|error| error.to_string())
}

pub fn write(
    rest: &FamilyCultivatedAthenaRest,
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
    let reopened =
        FamilyCultivatedAthenaRest::read(&read(&standing)?, &read(&decoder)?, &read(&fibres)?)
            .map_err(|error| error.to_string())?;
    if reopened
        .canonical_identity()
        .map_err(|error| error.to_string())?
        != rest
            .canonical_identity()
            .map_err(|error| error.to_string())?
    {
        return Err("the written L1 rest did not reopen as the same ecology".to_owned());
    }
    Ok((standing, decoder, fibres))
}

fn read(path: impl AsRef<Path>) -> Result<Vec<u8>, String> {
    let path = path.as_ref();
    fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))
}
