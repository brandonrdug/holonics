//! Phoenix W1: seal the complete Gemma foreign occurrence into a source-detached native rest.
//!
//! This is a construction-boundary deed only.  It does not conduct inference or choose a
//! cultivation law.  The parent admits Station B, founds the 45 operation complexes, streams all
//! 2,130 populations once, and then starts this same executable as a source-detached child.

use std::fs::{self, File};
use std::io::{self, Read, Write};
use std::path::Path;
use std::process::Command;

use holonic_engine::foreign_codec_rest::ExteriorCodecArtifact;
use holonic_engine::native_rest::{MountedNativeRest, NativeRest, NativeRestInput};
use holonic_engine::operation_correspondence::{
    OperationCorrespondenceSeal, PopulationCorrespondence, PopulationResolution,
};
use sha2::{Digest, Sha256};

#[path = "phoenix/resident_layer.rs"]
mod resident_layer;
#[path = "phoenix/tower.rs"]
mod tower;
#[path = "phoenix/w1_admission.rs"]
mod w1_admission;
#[path = "phoenix/w1_correspondence.rs"]
mod w1_correspondence;

const EXPECTED_COMPLEXES: usize = 45;
const EXPECTED_OPERATIONS: usize = 1_466;
const EXPECTED_POPULATIONS: usize = 2_130;
const EXPECTED_VOCABULARY: usize = 262_144;

fn digest_bytes(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn write_codec_companions(dir: &Path, artifact: &ExteriorCodecArtifact) -> io::Result<()> {
    fs::create_dir_all(dir)?;
    let descriptor = artifact.descriptor();
    fs::write(
        dir.join(&descriptor.tokenizer_json_sha256),
        &artifact.tokenizer_json,
    )?;
    if let (Some(hash), Some(bytes)) = (
        &descriptor.tokenizer_config_sha256,
        &artifact.tokenizer_config_json,
    ) {
        fs::write(dir.join(hash), bytes)?;
    }
    Ok(())
}

fn all_population_correspondence(
    mut seal: OperationCorrespondenceSeal,
    names: impl Iterator<Item = String>,
) -> Result<OperationCorrespondenceSeal, String> {
    seal.source_populations = names.collect();
    seal.source_populations.sort();
    seal.populations = seal
        .source_populations
        .iter()
        .map(|name| PopulationCorrespondence {
            source_population: name.clone(),
            resolution: PopulationResolution::Native {
                native_population: name.clone(),
            },
        })
        .collect();
    seal.seal()
        .map_err(|error| format!("complete population correspondence refused: {error:?}"))
}

fn child(rest: &Path, codec_dir: &Path) -> Result<(), String> {
    let mounted =
        MountedNativeRest::open(rest).map_err(|error| format!("child remount: {error:?}"))?;
    let descriptor = mounted
        .codebook()
        .codec
        .as_ref()
        .ok_or("native rest has no codec descriptor")?;
    let tokenizer =
        fs::read(codec_dir.join(&descriptor.tokenizer_json_sha256)).map_err(|e| e.to_string())?;
    let config = descriptor
        .tokenizer_config_sha256
        .as_ref()
        .map(|hash| fs::read(codec_dir.join(hash)))
        .transpose()
        .map_err(|e| e.to_string())?;
    let artifact = ExteriorCodecArtifact::from_bytes(tokenizer, config);
    mounted
        .codebook()
        .validate_with_codec(&artifact)
        .map_err(|error| format!("child codec: {error}"))?;
    let operations = mounted.correspondence().source_operations.len();
    let complexes = mounted.topologies().len();
    if mounted.populations().len() != EXPECTED_POPULATIONS
        || mounted.codebook().entries.len() != EXPECTED_VOCABULARY
        || operations != EXPECTED_OPERATIONS
        || complexes != EXPECTED_COMPLEXES
    {
        return Err(format!(
            "child counts drifted: complexes={complexes} operations={operations} populations={} vocabulary={}",
            mounted.populations().len(),
            mounted.codebook().entries.len()
        ));
    }
    let picks = [0usize, EXPECTED_POPULATIONS / 2, EXPECTED_POPULATIONS - 1];
    let mut hashes = Vec::new();
    for index in picks {
        let descriptor = &mounted.populations()[index];
        let population = &descriptor.source.population;
        let mut sink = DigestSink::default();
        mounted
            .read_population_to(population, &mut sink)
            .map_err(|e| format!("population {population}: {e:?}"))?;
        let actual = sink.finish();
        if descriptor.source.sha256.as_deref() != Some(actual.as_str()) {
            return Err(format!(
                "population {population} returned digest {actual}, source descriptor disagrees"
            ));
        }
        hashes.push((population.clone(), actual));
    }
    for entry in fs::read_dir("/proc/self/fd").map_err(|e| e.to_string())? {
        let entry = entry.map_err(|e| e.to_string())?;
        if let Ok(target) = fs::read_link(entry.path()) {
            let text = target.to_string_lossy();
            if text.contains("model.safetensors")
                || text.contains("modeling_gemma4.py")
                || text.contains("config.json")
                || text.contains("tokenizer.json")
            {
                return Err(format!("source path leaked into child fd: {text}"));
            }
        }
    }
    let returned = serde_json::json!({
        "return": "source-detached-native-rest",
        "complexes": complexes,
        "operations": operations,
        "populations": mounted.populations().len(),
        "vocabulary": mounted.codebook().entries.len(),
        "sample_hashes": hashes,
    });
    println!("CHILD_RETURN {returned}");
    Ok(())
}

#[derive(Default)]
struct DigestSink(Sha256);
impl Write for DigestSink {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.0.update(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
impl DigestSink {
    fn finish(self) -> String {
        format!("{:x}", self.0.finalize())
    }
}

fn parent(root: &Path, station_b: &Path, codebook_path: &Path, out: &Path) -> Result<(), String> {
    fs::create_dir_all(out).map_err(|e| e.to_string())?;
    let mut admission = w1_admission::admit(root, station_b, codebook_path)
        .map_err(|e| format!("admission: {e}"))?;
    if admission.source.container.regions.len() != EXPECTED_POPULATIONS
        || admission.codebook.entries.len() != EXPECTED_VOCABULARY
    {
        return Err("Station B closure counts drifted".into());
    }
    let topology = w1_correspondence::found(&mut admission.source)?;
    if topology.complexes.len() != EXPECTED_COMPLEXES
        || topology.correspondence.operations.len() != EXPECTED_OPERATIONS
    {
        return Err(format!(
            "topology census drifted: complexes={} operations={}",
            topology.complexes.len(),
            topology.correspondence.operations.len()
        ));
    }
    let correspondence = all_population_correspondence(
        topology.correspondence,
        admission.source.container.regions.keys().cloned(),
    )?;
    if correspondence.populations.len() != EXPECTED_POPULATIONS {
        return Err(format!(
            "population correspondence drifted: {}",
            correspondence.populations.len()
        ));
    }
    let correspondence_json = correspondence
        .stable_json()
        .map_err(|error| format!("correspondence serialization: {error}"))?;
    fs::write(
        out.join("operation_correspondence.json"),
        &correspondence_json,
    )
    .map_err(|error| error.to_string())?;
    let codec_dir = out.join("codec");
    write_codec_companions(&codec_dir, &admission.codec).map_err(|e| e.to_string())?;
    let rest_path = out.join("gemma_native_rest.bin");
    let temp = out.join("gemma_native_rest.bin.partial");
    let input = NativeRestInput {
        topology: topology.complexes,
        source: admission.source,
        populations: admission.populations,
        laws: topology.laws,
        tilings: topology.tilings,
        reductions: topology.reductions,
        correspondence,
        codebook: admission.codebook,
    };
    let mut file = File::create(&temp).map_err(|e| e.to_string())?;
    if let Err(error) = NativeRest::seal_streamed(input, &mut file) {
        drop(file);
        let _ = fs::remove_file(&temp);
        return Err(format!("streamed seal: {error:?}"));
    }
    file.sync_all().map_err(|e| e.to_string())?;
    drop(file);
    fs::rename(&temp, &rest_path).map_err(|e| e.to_string())?;
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    let child = Command::new(exe)
        .arg("--child")
        .arg(&rest_path)
        .arg(&codec_dir)
        .output()
        .map_err(|error| error.to_string())?;
    if !child.status.success() {
        return Err(format!(
            "source-detached child failed: {}",
            String::from_utf8_lossy(&child.stderr)
        ));
    }
    let child_stdout = String::from_utf8(child.stdout)
        .map_err(|error| format!("child return is not UTF-8: {error}"))?;
    let child_return = child_stdout
        .lines()
        .find_map(|line| line.strip_prefix("CHILD_RETURN "))
        .ok_or_else(|| format!("child returned no inspected artifact: {child_stdout}"))?;
    let _: serde_json::Value = serde_json::from_str(child_return)
        .map_err(|error| format!("child return is not JSON: {error}"))?;
    let receipt = out.join("w1_receipt.json");
    let descriptor = admission.codec.descriptor();
    let receipt_body = serde_json::json!({
        "rest": rest_path,
        "rest_sha256": digest_file(&rest_path)?,
        "correspondence_sha256": digest_bytes(correspondence_json.as_bytes()),
        "tokenizer_sha256": descriptor.tokenizer_json_sha256,
        "tokenizer_config_sha256": descriptor.tokenizer_config_sha256,
        "complexes": EXPECTED_COMPLEXES,
        "operations": EXPECTED_OPERATIONS,
        "populations": EXPECTED_POPULATIONS,
        "vocabulary": EXPECTED_VOCABULARY,
        "child_return": serde_json::from_str::<serde_json::Value>(child_return)
            .map_err(|error| error.to_string())?,
    });
    fs::write(
        &receipt,
        serde_json::to_vec_pretty(&receipt_body).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    println!("W1 native rest sealed: {}", receipt.display());
    Ok(())
}

fn digest_file(path: &Path) -> Result<String, String> {
    let mut file = File::open(path).map_err(|error| error.to_string())?;
    let mut digest = Sha256::new();
    let mut chunk = vec![0u8; 1 << 20];
    loop {
        let read = file.read(&mut chunk).map_err(|error| error.to_string())?;
        if read == 0 {
            return Ok(format!("{:x}", digest.finalize()));
        }
        digest.update(&chunk[..read]);
    }
}

fn main() -> Result<(), String> {
    let args: Vec<_> = std::env::args().collect();
    if args.get(1).map(String::as_str) == Some("--child") {
        return child(
            Path::new(args.get(2).ok_or("child rest path")?),
            Path::new(args.get(3).ok_or("child codec dir")?),
        );
    }
    if args.len() != 5 {
        return Err(format!("usage: {} ROOT STATION_B CODEBOOK OUT", args[0]));
    }
    parent(
        Path::new(&args[1]),
        Path::new(&args[2]),
        Path::new(&args[3]),
        Path::new(&args[4]),
    )
}
