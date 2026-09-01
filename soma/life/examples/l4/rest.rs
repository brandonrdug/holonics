use std::fs;
use std::path::{Path, PathBuf};

use life::mathematical_particle::NativeTerrainRest;

pub fn write(
    rest: &NativeTerrainRest,
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
    let reopened = NativeTerrainRest::read(&read(&standing)?, &read(&decoder)?, &read(&fibres)?)
        .map_err(|error| error.to_string())?;
    if reopened
        .canonical_identity()
        .map_err(|error| error.to_string())?
        != rest
            .canonical_identity()
            .map_err(|error| error.to_string())?
    {
        return Err("the L4 rest did not reopen as the same production ecology".to_owned());
    }
    Ok((standing, decoder, fibres))
}

pub fn read(path: impl AsRef<Path>) -> Result<Vec<u8>, String> {
    let path = path.as_ref();
    fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))
}
