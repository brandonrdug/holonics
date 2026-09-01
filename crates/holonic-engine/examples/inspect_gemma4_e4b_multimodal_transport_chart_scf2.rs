use std::{env, error::Error, fs, path::PathBuf};

use holonic_engine::{
    foreign_map::manifest_safetensors,
    native_ecology::holonic_intelligence::{
        ForeignConfigurationChart, Gemma4ExteriorTransportChart,
    },
};

fn main() -> Result<(), Box<dyn Error>> {
    let root = env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/home/b/models/gemma-4-E4B-it"));
    let config_path = root.join("config.json");
    let processor_path = root.join("processor_config.json");
    let weights_path = root.join("model.safetensors");
    let configuration = ForeignConfigurationChart::read(
        config_path.display().to_string(),
        fs::read(&config_path)?,
    )?;
    let processor = ForeignConfigurationChart::read(
        processor_path.display().to_string(),
        fs::read(&processor_path)?,
    )?;
    let (_file, container) = manifest_safetensors(&weights_path.display().to_string())?;
    let chart = Gemma4ExteriorTransportChart::from_charts(&configuration, &processor, &container)?;
    println!("{}", serde_json::to_string_pretty(&chart)?);
    Ok(())
}
