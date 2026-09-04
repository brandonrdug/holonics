use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use life::mathematical_particle::{
    ExactMediaAxis, ExactSpatialDeclaration, FamilyCorrespondenceFibre, MathematicalMediaPort,
    MediaCandidatePair, MediaSourceFamily, MediaSourceInterior, UnmatchedMediaMember,
};
use serde_json::Value;

use super::artifact;

pub const M0_PRODUCT: &str =
    ".local/artifacts/m0_mathematical_source_circulation/m0-mathematical-source-circulation.json";
pub const M0_SOURCE: &str = ".local/scratch/previous/pdfs/2608.13553-heat-kernel-geometry.pdf";

pub struct MountedMediaSource {
    pub m0_bytes: Vec<u8>,
    pub m0: Value,
    pub families: Vec<MediaSourceFamily>,
    pub heldout_pair_anchor: Vec<u32>,
    pub heldout_pair_port: Vec<u32>,
    pub source_artifact_octets: u64,
    pub source_face_paths: Vec<PathBuf>,
}

pub fn mount(root: &Path) -> Result<MountedMediaSource, String> {
    let product_path = root.join(M0_PRODUCT);
    let (m0_bytes, m0) = artifact::read_json(&product_path)?;
    let source_bytes = fs::read(root.join(M0_SOURCE)).map_err(|error| error.to_string())?;
    if artifact::digest(&source_bytes) != m0["natural_source"]["sha256"] {
        return Err("the M0 natural source changed beneath its admitted occurrence".to_owned());
    }
    let mut source_face_paths = Vec::new();
    let families = [5_u32, 10_u32]
        .into_iter()
        .enumerate()
        .map(|(family, page)| {
            family_from_page(root, &m0, family as u32, page, &mut source_face_paths)
        })
        .collect::<Result<Vec<_>, _>>()?;
    source_face_paths.sort();
    source_face_paths.dedup();
    let source_artifact_octets = source_face_paths.iter().try_fold(
        m0_bytes.len() as u64 + source_bytes.len() as u64,
        |total, path| {
            fs::metadata(path)
                .map_err(|error| error.to_string())
                .and_then(|metadata| {
                    total
                        .checked_add(metadata.len())
                        .ok_or_else(|| "source artifact extent overflow".to_owned())
                })
        },
    )?;
    let (heldout_pair_anchor, heldout_pair_port) = pair_wire(&families[1].correspondences);
    Ok(MountedMediaSource {
        m0_bytes,
        m0,
        families,
        heldout_pair_anchor,
        heldout_pair_port,
        source_artifact_octets,
        source_face_paths,
    })
}

fn family_from_page(
    root: &Path,
    m0: &Value,
    family: u32,
    page: u32,
    paths: &mut Vec<PathBuf>,
) -> Result<MediaSourceFamily, String> {
    let name = format!("natural_page_{page}");
    let notation = &m0["testimony"][format!("{name}_text")];
    let vector = &m0["testimony"][format!("{name}_vector")];
    let raster = &m0["raster_reconstruction_fibers"][&name];
    let co = &m0["co_testimony"][&name];
    for source in [notation, vector, &raster["four_testimony"]] {
        let locator = string(&source["artifact"]["locator"])?;
        let path = root.join(locator);
        let bytes = fs::read(&path).map_err(|error| format!("read {}: {error}", path.display()))?;
        if artifact::digest(&bytes) != string(&source["artifact"]["sha256"])? {
            return Err(format!(
                "the admitted media artifact changed: {}",
                path.display()
            ));
        }
        paths.push(path);
    }
    let correspondence = correspondence(family, notation, vector, raster, co)?;
    let uncertainty = artifact::digest(&serde_json::to_vec(co).map_err(|error| error.to_string())?);
    Ok(MediaSourceFamily {
        family,
        occurrence: format!("m0/{name}/heat-kernel-fisher-geometry"),
        notation: interior_from_testimony(
            family,
            MathematicalMediaPort::Notation,
            notation,
            uncertainty.clone(),
            1,
            1,
        )?,
        vector: interior_from_testimony(
            family,
            MathematicalMediaPort::Vector,
            vector,
            uncertainty.clone(),
            1,
            1,
        )?,
        raster: raster_interior(family, raster, uncertainty)?,
        correspondences: correspondence,
    })
}

fn interior_from_testimony(
    family: u32,
    port: MathematicalMediaPort,
    testimony: &Value,
    uncertainty: String,
    scale_numerator: u32,
    scale_denominator: u32,
) -> Result<MediaSourceInterior, String> {
    let canonical = serde_json::to_vec(testimony).map_err(|error| error.to_string())?;
    let artifact_sha256 = string(&testimony["artifact"]["sha256"])?.to_owned();
    Ok(MediaSourceInterior {
        family,
        port,
        artifact_occurrence: string(&testimony["artifact"]["occurrence"])?.to_owned(),
        artifact_sha256: artifact_sha256.clone(),
        chart: string(&testimony["chart"])?.to_owned(),
        occurrence_population: population(&testimony["occurrences"])?,
        contact_population: population(&testimony["contacts"])?,
        incidence_sha256: artifact::digest(&canonical),
        spatial: spatial(
            testimony,
            uncertainty,
            artifact_sha256,
            scale_numerator,
            scale_denominator,
        )?,
        canonical_interior: canonical,
    })
}

fn raster_interior(
    family: u32,
    raster: &Value,
    uncertainty: String,
) -> Result<MediaSourceInterior, String> {
    let four = &raster["four_testimony"];
    let eight = &raster["eight_testimony"];
    let canonical = serde_json::to_vec(raster).map_err(|error| error.to_string())?;
    let artifact_sha256 = string(&four["artifact"]["sha256"])?.to_owned();
    let occurrence_population = population(&four["occurrences"])?
        .checked_add(population(&eight["occurrences"])?)
        .ok_or("raster occurrence population overflow")?;
    let contact_population = population(&four["contacts"])?
        .checked_add(population(&eight["contacts"])?)
        .ok_or("raster contact population overflow")?;
    let spatial_source = serde_json::json!({"extent": raster["extent"]});
    Ok(MediaSourceInterior {
        family,
        port: MathematicalMediaPort::RasterVision,
        artifact_occurrence: format!(
            "{}+{}",
            string(&four["artifact"]["occurrence"])?,
            string(&eight["artifact"]["occurrence"])?
        ),
        artifact_sha256: artifact_sha256.clone(),
        chart: "RasterFourAndEightConnected".to_owned(),
        occurrence_population,
        contact_population,
        incidence_sha256: artifact::digest(&canonical),
        spatial: spatial(&spatial_source, uncertainty, artifact_sha256, 1, 2)?,
        canonical_interior: canonical,
    })
}

fn spatial(
    testimony: &Value,
    uncertainty_fibre_sha256: String,
    source_lineage_sha256: String,
    common_scale_numerator: u32,
    common_scale_denominator: u32,
) -> Result<ExactSpatialDeclaration, String> {
    let extent = &testimony["extent"];
    Ok(ExactSpatialDeclaration {
        dimension: 2,
        axes: vec![
            ExactMediaAxis {
                name: "x".to_owned(),
                extent_numerator: exact_word(&extent["width"], 0)?,
                extent_denominator: exact_word(&extent["width"], 1)?,
                common_scale_numerator,
                common_scale_denominator,
                forward_hand: 1,
            },
            ExactMediaAxis {
                name: "y".to_owned(),
                extent_numerator: exact_word(&extent["height"], 0)?,
                extent_denominator: exact_word(&extent["height"], 1)?,
                common_scale_numerator,
                common_scale_denominator,
                // M0's exact boxes have top < bottom: this chart's vertical coordinate descends.
                forward_hand: -1,
            },
        ],
        uncertainty_fibre_sha256,
        source_lineage_sha256,
    })
}

fn correspondence(
    family: u32,
    notation: &Value,
    vector: &Value,
    raster: &Value,
    co: &Value,
) -> Result<FamilyCorrespondenceFibre, String> {
    let notation_map = addresses(&notation["occurrences"])?;
    let vector_map = addresses(&vector["occurrences"])?;
    let four_map = addresses(&raster["four_testimony"]["occurrences"])?;
    let eight_map = addresses(&raster["eight_testimony"]["occurrences"])?;
    let tv = &co["text_vector"];
    let tr4 = &co["text_raster_four"];
    let tr8 = &co["text_raster_eight"];
    let mut unmatched = Vec::new();
    unmatched.extend(unmatched_side(tv, "unmatched_left", &notation_map, 0)?);
    unmatched.extend(unmatched_side(tv, "unmatched_right", &vector_map, 1)?);
    unmatched.extend(unmatched_side(tr4, "unmatched_right", &four_map, 2)?);
    unmatched.extend(unmatched_side(tr8, "unmatched_right", &eight_map, 3)?);
    Ok(FamilyCorrespondenceFibre {
        family,
        anchor_population: notation_map.len() as u32,
        vector_population: vector_map.len() as u32,
        raster_four_population: four_map.len() as u32,
        raster_eight_population: eight_map.len() as u32,
        text_vector: pairs(tv, &notation_map, &vector_map)?,
        text_raster_four: pairs(tr4, &notation_map, &four_map)?,
        text_raster_eight: pairs(tr8, &notation_map, &eight_map)?,
        unmatched,
    })
}

fn addresses(occurrences: &Value) -> Result<BTreeMap<String, u32>, String> {
    occurrences
        .as_array()
        .ok_or("occurrence population is not an array")?
        .iter()
        .enumerate()
        .map(|(at, occurrence)| Ok((string(&occurrence["address"])?.to_owned(), at as u32)))
        .collect()
}

fn pairs(
    testimony: &Value,
    left: &BTreeMap<String, u32>,
    right: &BTreeMap<String, u32>,
) -> Result<Vec<MediaCandidatePair>, String> {
    testimony["candidates"]
        .as_array()
        .ok_or("candidate population is not an array")?
        .iter()
        .map(|pair| {
            Ok(MediaCandidatePair {
                anchor: *left
                    .get(string(&pair["left"])?)
                    .ok_or("left candidate absent")?,
                member: *right
                    .get(string(&pair["right"])?)
                    .ok_or("right candidate absent")?,
            })
        })
        .collect()
}

fn unmatched_side(
    testimony: &Value,
    field: &str,
    addresses: &BTreeMap<String, u32>,
    kind: u32,
) -> Result<Vec<UnmatchedMediaMember>, String> {
    testimony[field]
        .as_array()
        .ok_or("unmatched population is not an array")?
        .iter()
        .map(|address| {
            let at = *addresses
                .get(string(address)?)
                .ok_or("unmatched address absent")?;
            Ok(match kind {
                0 => UnmatchedMediaMember::Notation(at),
                1 => UnmatchedMediaMember::Vector(at),
                2 => UnmatchedMediaMember::RasterFour(at),
                _ => UnmatchedMediaMember::RasterEight(at),
            })
        })
        .collect()
}

pub fn pair_wire(fibre: &FamilyCorrespondenceFibre) -> (Vec<u32>, Vec<u32>) {
    let mut anchors = (0..fibre.anchor_population).collect::<Vec<_>>();
    let mut ports = vec![MathematicalMediaPort::Notation.device_ordinal(); anchors.len()];
    for pair in &fibre.text_vector {
        anchors.push(pair.anchor);
        ports.push(MathematicalMediaPort::Vector.device_ordinal());
    }
    for pair in fibre
        .text_raster_four
        .iter()
        .chain(&fibre.text_raster_eight)
    {
        anchors.push(pair.anchor);
        ports.push(MathematicalMediaPort::RasterVision.device_ordinal());
    }
    (anchors, ports)
}

fn exact_word(value: &Value, part: usize) -> Result<u32, String> {
    let word = value
        .get(part)
        .and_then(|entry| entry.get(1))
        .and_then(|words| words.get(0))
        .and_then(Value::as_u64)
        .ok_or("exact extent word absent")?;
    u32::try_from(word).map_err(|_| "exact extent exceeds u32".to_owned())
}

fn population(value: &Value) -> Result<u32, String> {
    u32::try_from(value.as_array().ok_or("population is not an array")?.len())
        .map_err(|_| "population exceeds u32".to_owned())
}

fn string(value: &Value) -> Result<&str, String> {
    value
        .as_str()
        .ok_or_else(|| "expected source string".to_owned())
}
