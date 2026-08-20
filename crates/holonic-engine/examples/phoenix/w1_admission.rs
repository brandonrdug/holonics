//! Station-B admission for Phoenix W1.
//!
//! This owner reads the already returned Station-B manifest and receipt.  It does not run the
//! safetensors census again and it never expands the model into memory.  The source occurrence is
//! rebuilt from the authenticated header-shaped regions, while the later native-rest deed receives
//! one external locator for each exact population and streams each region once.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Read;
use std::path::Path;

use holonic_engine::foreign_codec_rest::{ExteriorCodebookRest, ExteriorCodecArtifact};
use holonic_engine::native_rest::{NativePopulation, NativePopulationPayload};
use holonic_engine::source_occurrence::{RegionIdentity, SourceOccurrence};
use sha2::{Digest, Sha256};

use super::resident_layer;

pub const EXPECTED_POPULATIONS: usize = 2_130;
pub const EXPECTED_VOCABULARY: u32 = 262_144;
pub const MANIFEST_NAME: &str = "gemma-4-E4B-it.manifest.tsv";
pub const RECEIPT_NAME: &str = "receipt.form";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StationBReceipt {
    pub content_sha256: String,
    pub file_octets: u64,
    pub payload_octets: u64,
    pub header_octets: u64,
    pub header_sha256: String,
    pub tensors: usize,
}

#[derive(Debug)]
pub struct W1Admission {
    pub source: SourceOccurrence,
    pub populations: Vec<NativePopulation>,
    pub codebook: ExteriorCodebookRest,
    pub codec: ExteriorCodecArtifact,
}

#[derive(Debug)]
pub enum AdmissionError {
    Io(String),
    Receipt(String),
    Manifest(String),
    Drift(String),
    Codebook(String),
    Source(String),
}

impl std::fmt::Display for AdmissionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(message)
            | Self::Receipt(message)
            | Self::Manifest(message)
            | Self::Drift(message)
            | Self::Codebook(message)
            | Self::Source(message) => f.write_str(message),
        }
    }
}

impl std::error::Error for AdmissionError {}

fn valid_sha(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn parse_u64(value: &str, field: &str) -> Result<u64, AdmissionError> {
    value
        .parse::<u64>()
        .map_err(|error| AdmissionError::Manifest(format!("{field}: {error}")))
}

fn parse_shape(value: &str) -> Result<Vec<usize>, AdmissionError> {
    let trimmed = value.trim();
    if trimmed == "[]" {
        return Ok(Vec::new());
    }
    let inner = trimmed
        .strip_prefix('[')
        .and_then(|value| value.strip_suffix(']'))
        .ok_or_else(|| AdmissionError::Manifest(format!("malformed shape {value:?}")))?;
    inner
        .split(',')
        .map(|part| {
            part.trim().parse::<usize>().map_err(|error| {
                AdmissionError::Manifest(format!("shape element {part:?}: {error}"))
            })
        })
        .collect()
}

fn parse_manifest(path: &Path, payload_octets: u64) -> Result<Vec<RegionIdentity>, AdmissionError> {
    let text = std::fs::read_to_string(path)
        .map_err(|error| AdmissionError::Io(format!("{}: {error}", path.display())))?;
    let mut lines = text.lines();
    let header = lines
        .next()
        .ok_or_else(|| AdmissionError::Manifest("manifest has no header".to_owned()))?;
    let expected = [
        "population",
        "dtype",
        "shape",
        "rank",
        "start",
        "end",
        "octets",
        "sha256",
        "codewords",
        "finite",
        "non_finite",
        "zero",
        "subnormal",
        "exponent_min",
        "exponent_max",
        "admission",
        "transport",
        "bound_by",
        "load_bearing",
    ];
    let columns: Vec<&str> = header.split('\t').collect();
    if columns.len() != expected.len()
        || expected
            .iter()
            .enumerate()
            .any(|(index, name)| columns[index] != *name)
    {
        return Err(AdmissionError::Manifest(
            "Station-B manifest header drifted".to_owned(),
        ));
    }
    let mut regions = Vec::with_capacity(EXPECTED_POPULATIONS);
    let mut names = BTreeSet::new();
    for (line_number, line) in lines.enumerate() {
        if line.is_empty() {
            continue;
        }
        let fields: Vec<&str> = line.split('\t').collect();
        if fields.len() != expected.len() {
            return Err(AdmissionError::Manifest(format!(
                "line {} has {} fields",
                line_number + 2,
                fields.len()
            )));
        }
        let population = fields[0].to_owned();
        if population.is_empty() || !names.insert(population.clone()) {
            return Err(AdmissionError::Manifest(format!(
                "duplicate or empty population at line {}",
                line_number + 2
            )));
        }
        let start = parse_u64(fields[4], "start")?;
        let end = parse_u64(fields[5], "end")?;
        let octets = parse_u64(fields[6], "octets")?;
        let shape = parse_shape(fields[2])?;
        let rank = fields[3].parse::<usize>().map_err(|error| {
            AdmissionError::Manifest(format!("{} has malformed rank: {error}", population))
        })?;
        let elements = shape
            .iter()
            .try_fold(1u64, |product, extent| product.checked_mul(*extent as u64))
            .ok_or_else(|| AdmissionError::Manifest(format!("{population} shape overflows")))?;
        if fields[1] != "Bf16" {
            return Err(AdmissionError::Manifest(format!(
                "{} is {}, expected Bf16",
                population, fields[1]
            )));
        }
        let declared_octets = elements.checked_mul(2).ok_or_else(|| {
            AdmissionError::Manifest(format!("{population} BF16 extent overflows"))
        })?;
        if rank != shape.len() || octets != declared_octets {
            return Err(AdmissionError::Manifest(format!(
                "{} has rank/shape/octet drift",
                population
            )));
        }
        if fields[15] != "decoded exactly" {
            return Err(AdmissionError::Manifest(format!(
                "{} is not admitted as decoded exactly",
                population
            )));
        }
        if end < start || end - start != octets {
            return Err(AdmissionError::Manifest(format!(
                "{} has inconsistent region extent",
                population
            )));
        }
        if !valid_sha(fields[7]) {
            return Err(AdmissionError::Manifest(format!(
                "{} has an invalid region digest",
                population
            )));
        }
        regions.push(RegionIdentity {
            population,
            dtype: fields[1].to_owned(),
            shape,
            start,
            end,
            sha256: Some(fields[7].to_owned()),
        });
    }
    if regions.len() != EXPECTED_POPULATIONS {
        return Err(AdmissionError::Manifest(format!(
            "expected {EXPECTED_POPULATIONS} regions, found {}",
            regions.len()
        )));
    }
    let mut intervals: Vec<(&str, u64, u64)> = regions
        .iter()
        .map(|region| (region.population.as_str(), region.start, region.end))
        .collect();
    intervals.sort_by_key(|(_, start, _)| *start);
    let mut cursor = 0u64;
    for (population, start, end) in intervals {
        if start != cursor {
            return Err(AdmissionError::Manifest(format!(
                "payload coverage gap or overlap before {population}: expected {cursor}, found {start}"
            )));
        }
        cursor = end;
    }
    if cursor != payload_octets {
        return Err(AdmissionError::Manifest(format!(
            "payload coverage ends at {cursor}, receipt declares {payload_octets}"
        )));
    }
    Ok(regions)
}

fn parse_census_line(line: &str) -> Result<(u64, u64, u64, usize), AdmissionError> {
    let fields: Vec<&str> = line.split_whitespace().collect();
    let labels = [
        (0, "container"),
        (1, "file"),
        (2, "octets"),
        (4, "payload"),
        (5, "octets"),
        (7, "header"),
        (8, "octets"),
        (10, "tensors"),
    ];
    if fields.len() != 14
        || labels.iter().any(|(index, label)| fields[*index] != *label)
        || fields[12] != "refused"
    {
        return Err(AdmissionError::Receipt(
            "container census sequence drifted".to_owned(),
        ));
    }
    let file_octets = fields[3]
        .parse::<u64>()
        .map_err(|error| AdmissionError::Receipt(format!("file octets: {error}")))?;
    let payload_octets = fields[6]
        .parse::<u64>()
        .map_err(|error| AdmissionError::Receipt(format!("payload octets: {error}")))?;
    let header_octets = fields[9]
        .parse::<u64>()
        .map_err(|error| AdmissionError::Receipt(format!("header octets: {error}")))?;
    let tensors = fields[11]
        .parse::<usize>()
        .map_err(|error| AdmissionError::Receipt(format!("tensor count: {error}")))?;
    let refused = fields[13]
        .parse::<usize>()
        .map_err(|error| AdmissionError::Receipt(format!("refused count: {error}")))?;
    if refused != 0 {
        return Err(AdmissionError::Receipt(format!(
            "Station B receipt declares {refused} refused populations"
        )));
    }
    Ok((file_octets, payload_octets, header_octets, tensors))
}

fn parse_receipt(path: &Path) -> Result<StationBReceipt, AdmissionError> {
    let text = std::fs::read_to_string(path)
        .map_err(|error| AdmissionError::Io(format!("{}: {error}", path.display())))?;
    let content_sha256 = text
        .lines()
        .find_map(|line| line.strip_prefix("content sha256 "))
        .ok_or_else(|| AdmissionError::Receipt("content digest is absent".to_owned()))?
        .trim()
        .to_owned();
    let header_sha256 = text
        .lines()
        .find_map(|line| line.strip_prefix("header sha256 "))
        .ok_or_else(|| AdmissionError::Receipt("header digest is absent".to_owned()))?
        .trim()
        .to_owned();
    if !valid_sha(&content_sha256) || !valid_sha(&header_sha256) {
        return Err(AdmissionError::Receipt(
            "receipt digest is malformed".to_owned(),
        ));
    }
    let census = text
        .lines()
        .find(|line| line.starts_with("container file octets "))
        .ok_or_else(|| AdmissionError::Receipt("container census is absent".to_owned()))?;
    let (file_octets, payload_octets, header_octets, tensors) = parse_census_line(census)?;
    if tensors != EXPECTED_POPULATIONS {
        return Err(AdmissionError::Receipt(format!(
            "receipt declares {tensors} tensors, expected {EXPECTED_POPULATIONS}"
        )));
    }
    Ok(StationBReceipt {
        content_sha256,
        file_octets,
        payload_octets,
        header_octets,
        header_sha256,
        tensors,
    })
}

fn authenticate_source(
    root: &Path,
    regions: BTreeMap<String, RegionIdentity>,
    receipt: &StationBReceipt,
) -> Result<SourceOccurrence, AdmissionError> {
    let model_path = root.join("model.safetensors");
    let model_octets = std::fs::metadata(&model_path)
        .map_err(|error| AdmissionError::Io(format!("{}: {error}", model_path.display())))?
        .len();
    if model_octets != receipt.file_octets {
        return Err(AdmissionError::Drift(format!(
            "current model extent {model_octets} differs from Station B {}",
            receipt.file_octets
        )));
    }
    // Station B's streamed census hashes the JSON body; `AuthenticatedContainer` hashes the
    // eight-octet extent together with that body. They are two declared receiver apertures, so
    // W1 verifies the Station-B body face here and retains the framed face in `source`.
    let mut model = std::fs::File::open(&model_path)
        .map_err(|error| AdmissionError::Io(format!("{}: {error}", model_path.display())))?;
    let mut length_word = [0u8; 8];
    model
        .read_exact(&mut length_word)
        .map_err(|error| AdmissionError::Io(format!("{}: {error}", model_path.display())))?;
    let header_octets = u64::from_le_bytes(length_word);
    let mut header = vec![
        0u8;
        usize::try_from(header_octets).map_err(|_| {
            AdmissionError::Drift(format!(
                "header extent {header_octets} exceeds this process"
            ))
        })?
    ];
    model
        .read_exact(&mut header)
        .map_err(|error| AdmissionError::Io(format!("{}: {error}", model_path.display())))?;
    let header_body_sha256 = format!("{:x}", Sha256::digest(&header));
    let root = root
        .to_str()
        .ok_or_else(|| AdmissionError::Source("root is not UTF-8".to_owned()))?;
    let source =
        resident_layer::source_occurrence(root, regions, Some(receipt.content_sha256.clone()))
            .map_err(AdmissionError::Source)?;
    if source.container.octets != receipt.file_octets
        || source.container.header_octets != receipt.header_octets
        || header_body_sha256 != receipt.header_sha256
        || source.container.content_sha256.as_deref() != Some(receipt.content_sha256.as_str())
    {
        return Err(AdmissionError::Drift(format!(
            "the current source header/extent disagrees with Station B: file {} != {}; header extent {} != {}; header digest {} != {}; content {:?} != {}",
            source.container.octets,
            receipt.file_octets,
            source.container.header_octets,
            receipt.header_octets,
            header_body_sha256,
            receipt.header_sha256,
            source.container.content_sha256,
            receipt.content_sha256,
        )));
    }
    Ok(source)
}

fn authenticate_codebook(
    root: &Path,
    codebook_path: &Path,
    receipt: &StationBReceipt,
) -> Result<(ExteriorCodebookRest, ExteriorCodecArtifact), AdmissionError> {
    let compact = ExteriorCodebookRest::read_tsv(codebook_path)
        .map_err(|error| AdmissionError::Codebook(error.to_string()))?;
    if compact.vocabulary_extent != EXPECTED_VOCABULARY
        || compact.entries.len() != EXPECTED_VOCABULARY as usize
        || compact.coverage.represented_token_ids != EXPECTED_VOCABULARY
        || compact.source.model_content_sha256 != receipt.content_sha256
    {
        return Err(AdmissionError::Drift(
            "the codebook source or complete vocabulary coverage drifted".to_owned(),
        ));
    }
    let tokenizer = root.join("tokenizer.json");
    let tokenizer_config = root.join("tokenizer_config.json");
    let artifact = ExteriorCodecArtifact::from_paths(&tokenizer, Some(&tokenizer_config))
        .map_err(|error| AdmissionError::Codebook(error.to_string()))?;
    // Consume the compact rows exactly once.  The 262,144 entries and the tokenizer bytes are
    // large continuing owners; cloning either here would create a second source population.
    let source = compact.source;
    let extent = compact.vocabulary_extent;
    let entries = compact.entries;
    let coverage = compact.coverage;
    let open = compact.open;
    let codebook = ExteriorCodebookRest::seal_with_codec_ref(
        source,
        extent,
        entries,
        coverage,
        open,
        Some(&artifact),
    )
    .map_err(|error| AdmissionError::Codebook(error.to_string()))?;
    Ok((codebook, artifact))
}

pub fn admit(
    root: impl AsRef<Path>,
    station_b_dir: impl AsRef<Path>,
    codebook_path: impl AsRef<Path>,
) -> Result<W1Admission, AdmissionError> {
    let root = root.as_ref().to_owned();
    let station_b_dir = station_b_dir.as_ref();
    let receipt = parse_receipt(&station_b_dir.join(RECEIPT_NAME))?;
    let regions = parse_manifest(&station_b_dir.join(MANIFEST_NAME), receipt.payload_octets)?;
    let region_map: BTreeMap<_, _> = regions
        .iter()
        .cloned()
        .map(|region| (region.population.clone(), region))
        .collect();
    let source = authenticate_source(&root, region_map, &receipt)?;
    let (codebook, codec) = authenticate_codebook(&root, codebook_path.as_ref(), &receipt)?;
    let model_path = root.join("model.safetensors");
    let populations = regions
        .iter()
        .cloned()
        .map(|region| NativePopulation {
            native_name: region.population.clone(),
            source: region,
            payload: NativePopulationPayload::External {
                locator: model_path.to_string_lossy().into_owned(),
            },
        })
        .collect();
    Ok(W1Admission {
        source,
        populations,
        codebook,
        codec,
    })
}

#[cfg(test)]
mod tests {
    use super::{parse_census_line, parse_shape, valid_sha};

    #[test]
    fn station_b_shapes_are_exactly_parsed() {
        assert_eq!(parse_shape("[]").expect("scalar"), Vec::<usize>::new());
        assert_eq!(parse_shape("[2, 2560]").expect("matrix"), vec![2, 2560]);
    }

    #[test]
    fn digests_must_be_content_addressed() {
        assert!(valid_sha(&"a".repeat(64)));
        assert!(!valid_sha("short"));
        assert!(!valid_sha(&format!("{}z", "a".repeat(63))));
    }

    #[test]
    fn receipt_census_parses_the_fixed_label_sequence() {
        let line = "container file octets 15992595884 payload octets 15992314836 header octets 281040 tensors 2130 refused 0";
        assert_eq!(
            parse_census_line(line).expect("literal Station-B census"),
            (15992595884, 15992314836, 281040, 2130)
        );
    }
}
