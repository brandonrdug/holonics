use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use life::mathematical_source::{
    ArtifactIdentity, CoTestimonyFiber, ExactBox, ExactExtent, PlacedCarrier,
    SourceLayoutTestimony, SourceLayoutWorkCover, TestimonyChart, correspond,
    correspondence_demand, derive_layout, exact_decimal, layout_demand,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde_json::Value;
use sha2::{Digest, Sha256};

const M0_RETURN: &str =
    "output/m0_mathematical_source_circulation/m0-mathematical-source-circulation.json";
const M0_SHA256: &str = "3ca6c0342f7eb9dba5a7ee4b06f448036dc7af4f149981eacbfb95b901991ef8";
const BASELINE_SHA256: &str = "1dd12cd9bcb9f1cbbe5015fd5cbe2e2437e2ce887b5e8288a5280d5f25b8cbb2";
const REFLOW_SHA256: &str = "856fed32025d7afd0df114a39541b597270639aaee90409e5b528476d5ec66e4";
const PAGE5_SHA256: &str = "1db3f71ba4db5ceafc9499cf91075179484f3746f99dda7398c1b2dfbae47e25";
const PAGE5_VECTOR_SHA256: &str =
    "ce87e1919298af9b85d370d1e01ec2b678672bcb81f71e271dad5bda2a7d0e35";
const ATLAS_SHA256: &str = "9b09ffc2d28117accc4be65206f615b188f25f623589147ffca337499df8c257";

pub struct RemountedM0 {
    pub baseline: SourceLayoutTestimony,
    pub reflow: SourceLayoutTestimony,
    pub presentation: Option<CoTestimonyFiber>,
    pub natural_page5: SourceLayoutTestimony,
    pub natural_page5_vector: ArtifactIdentity,
    pub equation_atlas: SourceLayoutTestimony,
    pub baseline_words: Vec<Vec<u8>>,
    pub reflow_words: Vec<Vec<u8>>,
}

pub fn remount(root: &Path) -> Result<RemountedM0, String> {
    let m0_bytes = fs::read(root.join(M0_RETURN)).map_err(|error| error.to_string())?;
    if digest(&m0_bytes) != M0_SHA256 {
        return Err("the admitted M0 semantic return moved".to_owned());
    }
    let m0: Value = serde_json::from_slice(&m0_bytes).map_err(|error| error.to_string())?;
    let baseline_artifact = artifact(
        &m0,
        &["testimony", "synthetic_baseline_text", "artifact"],
        BASELINE_SHA256,
    )?;
    let reflow_artifact = artifact(
        &m0,
        &["testimony", "synthetic_reflow_text", "artifact"],
        REFLOW_SHA256,
    )?;
    let page5_artifact = artifact(
        &m0,
        &["testimony", "natural_page_5_text", "artifact"],
        PAGE5_SHA256,
    )?;
    let page5_vector_artifact = artifact(
        &m0,
        &["testimony", "natural_page_5_vector", "artifact"],
        PAGE5_VECTOR_SHA256,
    )?;
    let atlas_artifact = artifact(
        &m0,
        &["testimony", "equation_atlas_equations", "artifact"],
        ATLAS_SHA256,
    )?;
    let (baseline, baseline_words) = remount_bbox(root, baseline_artifact)?;
    let (reflow, reflow_words) = remount_bbox(root, reflow_artifact)?;
    let (natural_page5, _) = remount_bbox(root, page5_artifact)?;
    let equation_atlas = remount_lines(root, atlas_artifact)?;
    let demand = correspondence_demand(&baseline, &reflow).map_err(|error| error.to_string())?;
    let presentation = correspond(&baseline, &reflow, &SourceLayoutWorkCover::exactly(&demand))
        .map_err(|error| error.to_string())?;
    Ok(RemountedM0 {
        baseline,
        reflow,
        presentation: Some(presentation),
        natural_page5,
        natural_page5_vector: page5_vector_artifact,
        equation_atlas,
        baseline_words,
        reflow_words,
    })
}

pub fn span_addresses(
    testimony: &SourceLayoutTestimony,
    artifact_sha256: &str,
    ordinals: &[usize],
) -> Result<BTreeSet<String>, String> {
    if testimony.artifact.sha256 != artifact_sha256 {
        return Err("an independent proposal reached the wrong M0 artifact".to_owned());
    }
    ordinals
        .iter()
        .map(|ordinal| {
            testimony
                .occurrences
                .get(*ordinal)
                .map(|occurrence| occurrence.address.clone())
                .ok_or_else(|| format!("proposal ordinal {ordinal} left the M0 occurrence family"))
        })
        .collect()
}

pub const fn baseline_sha256() -> &'static str {
    BASELINE_SHA256
}

pub const fn reflow_sha256() -> &'static str {
    REFLOW_SHA256
}

pub const fn page5_sha256() -> &'static str {
    PAGE5_SHA256
}

pub const fn atlas_sha256() -> &'static str {
    ATLAS_SHA256
}

fn artifact(
    root: &Value,
    path: &[&str],
    expected_sha256: &str,
) -> Result<ArtifactIdentity, String> {
    let mut value = root;
    for segment in path {
        value = value
            .get(*segment)
            .ok_or_else(|| format!("M0 omitted {}", path.join("/")))?;
    }
    let occurrence = string(value, "occurrence")?;
    let locator = string(value, "locator")?;
    let sha256 = string(value, "sha256")?;
    if sha256 != expected_sha256 {
        return Err(format!("M0 artifact {locator} moved to {sha256}"));
    }
    let bytes = fs::read(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join(&locator),
    )
    .map_err(|error| error.to_string())?;
    ArtifactIdentity::of_bytes(occurrence, locator, &bytes).map_err(|error| error.to_string())
}

fn remount_bbox(
    root: &Path,
    artifact: ArtifactIdentity,
) -> Result<(SourceLayoutTestimony, Vec<Vec<u8>>), String> {
    let bytes = fs::read(root.join(&artifact.locator)).map_err(|error| error.to_string())?;
    if digest(&bytes) != artifact.sha256 {
        return Err(format!("{} moved after M0", artifact.locator));
    }
    let text = std::str::from_utf8(&bytes).map_err(|error| error.to_string())?;
    let page_start = text
        .find("<page ")
        .ok_or_else(|| "Poppler page tag absent".to_owned())?;
    let page_end = text[page_start..]
        .find('>')
        .map(|offset| page_start + offset + 1)
        .ok_or_else(|| "Poppler page tag open".to_owned())?;
    let page = &text[page_start..page_end];
    let extent = ExactExtent::new(
        exact_attribute(page, "width")?,
        exact_attribute(page, "height")?,
    )
    .map_err(|error| error.to_string())?;
    let mut words = Vec::new();
    let mut occurrences = Vec::new();
    let mut cursor = 0usize;
    while let Some(offset) = text[cursor..].find("<word ") {
        let start = cursor + offset;
        let open_end = text[start..]
            .find('>')
            .map(|found| start + found)
            .ok_or_else(|| "Poppler word tag open".to_owned())?;
        let close = text[open_end + 1..]
            .find("</word>")
            .map(|found| open_end + 1 + found)
            .ok_or_else(|| "Poppler word tag close".to_owned())?;
        let tag = &text[start..=open_end];
        let payload = text.as_bytes()[open_end + 1..close].to_vec();
        let ordinal = u64::try_from(occurrences.len()).map_err(|_| "word extent".to_owned())?;
        words.push(payload.clone());
        occurrences.push(
            PlacedCarrier::new(
                &artifact,
                ordinal,
                payload,
                Some(ordinal),
                ExactBox::new(
                    exact_attribute(tag, "xMin")?,
                    exact_attribute(tag, "yMin")?,
                    exact_attribute(tag, "xMax")?,
                    exact_attribute(tag, "yMax")?,
                )
                .map_err(|error| error.to_string())?,
            )
            .map_err(|error| error.to_string())?,
        );
        cursor = close + "</word>".len();
    }
    let demand = layout_demand(&occurrences).map_err(|error| error.to_string())?;
    let testimony = derive_layout(
        TestimonyChart::BornDigital,
        artifact,
        extent,
        occurrences,
        &SourceLayoutWorkCover::exactly(&demand),
    )
    .map_err(|error| error.to_string())?;
    Ok((testimony, words))
}

fn exact_attribute(tag: &str, name: &str) -> Result<Rat, String> {
    let lexeme = attribute(tag, name).ok_or_else(|| format!("attribute {name} absent"))?;
    let admitted_digit_population = lexeme
        .bytes()
        .filter(|octet| octet.is_ascii_digit())
        .count();
    exact_decimal(lexeme, admitted_digit_population).map_err(|error| error.to_string())
}

fn remount_lines(root: &Path, artifact: ArtifactIdentity) -> Result<SourceLayoutTestimony, String> {
    let bytes = fs::read(root.join(&artifact.locator)).map_err(|error| error.to_string())?;
    if digest(&bytes) != artifact.sha256 {
        return Err(format!("{} moved after M0", artifact.locator));
    }
    let lines = bytes
        .split(|octet| *octet == b'\n')
        .filter(|line| !line.is_empty())
        .collect::<Vec<_>>();
    let width = lines.iter().map(|line| line.len()).max().unwrap_or(0);
    let extent = ExactExtent::new(integer(width as i64), integer(lines.len() as i64))
        .map_err(|error| error.to_string())?;
    let mut occurrences = Vec::with_capacity(lines.len());
    for (at, line) in lines.iter().copied().enumerate() {
        let ordinal = u64::try_from(at).map_err(|_| "atlas line extent".to_owned())?;
        occurrences.push(
            PlacedCarrier::new(
                &artifact,
                ordinal,
                line.to_vec(),
                Some(ordinal),
                ExactBox::new(
                    integer(0),
                    integer(at as i64),
                    integer(line.len() as i64),
                    integer((at + 1) as i64),
                )
                .map_err(|error| error.to_string())?,
            )
            .map_err(|error| error.to_string())?,
        );
    }
    let demand = layout_demand(&occurrences).map_err(|error| error.to_string())?;
    derive_layout(
        TestimonyChart::ExteriorAtlas,
        artifact,
        extent,
        occurrences,
        &SourceLayoutWorkCover::exactly(&demand),
    )
    .map_err(|error| error.to_string())
}

fn attribute<'a>(tag: &'a str, name: &str) -> Option<&'a str> {
    let bytes = tag.as_bytes();
    let needle = name.as_bytes();
    let mut at = 0usize;
    while at + needle.len() <= bytes.len() {
        let found = tag[at..].find(name)? + at;
        let before_ok = found == 0
            || bytes
                .get(found.wrapping_sub(1))
                .is_some_and(|octet| octet.is_ascii_whitespace() || *octet == b'<');
        let after = found + needle.len();
        if before_ok && bytes.get(after) == Some(&b'=') {
            let quote = *bytes.get(after + 1)?;
            let start = after + 2;
            let end = bytes[start..].iter().position(|octet| *octet == quote)? + start;
            return tag.get(start..end);
        }
        at = after.max(at + 1);
    }
    None
}

fn string(value: &Value, field: &str) -> Result<String, String> {
    value
        .get(field)
        .and_then(Value::as_str)
        .map(str::to_owned)
        .ok_or_else(|| format!("M0 artifact omitted {field}"))
}

fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}
