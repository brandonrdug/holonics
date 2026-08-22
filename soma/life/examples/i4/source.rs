//! I4 exterior source conduct: exact text-codeword and vision-patch entry passages.
//!
//! The codec crossings and file reads happen on the CPU apparatus boundary. The vision affine
//! law is the actual Gemma patch projection plus its two positional rows, enacted as exact integer
//! numerators on the resident card. No image is converted to text and no source-output similarity
//! founds the shared generator.

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use holonic_engine::embedding_fiber::{AlignedMaterial, ResidentReadout};
use holonic_engine::foreign_map::{ForeignContainer, manifest_safetensors};
use holonic_engine::phoenix::heterogeneous_fusion::{
    ModalityPort, SourcePortResponse, tokenize_exterior_occurrence,
};
use image::RgbImage;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const TEXT_EMBED: &str = "model.language_model.embed_tokens.weight";
const VISION_INPUT: &str = "model.vision_tower.patch_embedder.input_proj.weight";
const VISION_POSITION: &str = "model.vision_tower.patch_embedder.position_embedding_table";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Crop {
    pub x: u32,
    pub y: u32,
    pub side: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TextTokenFace {
    pub token_id: u32,
    pub byte_start: usize,
    pub byte_end: usize,
    pub embedding_row_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TextSourceConduct {
    pub family: u32,
    pub state: u32,
    pub occurrence: String,
    pub occurrence_sha256: String,
    pub tokens: Vec<TextTokenFace>,
    pub exact_embedding_scale: String,
    pub consequence_sha256: String,
    pub incidence_sha256: String,
    pub source_weight_octets_read: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactPatchScore {
    pub x: u32,
    pub y: u32,
    pub numerator: Vec<i128>,
    pub dyadic_exponent: i32,
    pub denominator: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VisionSourceConduct {
    pub family: u32,
    pub state: u32,
    pub occurrence: String,
    pub occurrence_sha256: String,
    pub crop: Crop,
    pub image_extent: [u32; 2],
    pub patch_grid: [u32; 2],
    pub scores: Vec<ExactPatchScore>,
    pub consequence_sha256: String,
    pub incidence_sha256: String,
    pub source_weight_octets_read: u64,
    pub exact_multiply_accumulates: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceApparatus {
    pub resident_chart: String,
    pub patch_projection_rows: usize,
    pub patch_projection_width: usize,
    pub valid_patch_queries: usize,
    pub masked_padding_queries_elided_by_receiver_factor: usize,
    pub resident_projection_octets: u64,
    pub source_weight_octets_read: u64,
    pub query_ingress_octets: u64,
    pub result_egress_octets: u64,
    pub exact_multiply_accumulates: u64,
    pub dependency_span: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceConduct {
    pub schema: String,
    pub truth_status: String,
    pub source_model_sha256: String,
    pub source_model_path: String,
    pub processor_law: String,
    pub crop_found_from_development_pair_only: Crop,
    pub changed_development_pixels: u64,
    pub changed_held_out_pixels: u64,
    pub text: Vec<TextSourceConduct>,
    pub vision: Vec<VisionSourceConduct>,
    pub responses: Vec<SourcePortResponse>,
    pub apparatus: SourceApparatus,
    pub open_exterior: Vec<String>,
}

struct ModelSource {
    file: std::fs::File,
    container: ForeignContainer,
}

impl ModelSource {
    fn open(root: &Path) -> Result<Self, String> {
        let locator = root.join("model.safetensors");
        let (file, container) = manifest_safetensors(
            locator
                .to_str()
                .ok_or_else(|| format!("non-UTF8 model path {}", locator.display()))?,
        )
        .map_err(|error| error.to_string())?;
        Ok(Self { file, container })
    }

    fn rows(&mut self, population: &str, from: usize, count: usize) -> Result<Vec<u16>, String> {
        self.container
            .read_rows_bf16(&mut self.file, population, from, count)
            .map(|(words, _)| words)
            .map_err(|error| error.to_string())
    }

    fn whole(&mut self, population: &str) -> Result<Vec<u16>, String> {
        self.container
            .read_bf16_whole(&mut self.file, population)
            .map_err(|error| error.to_string())
    }

    fn bf16_span(&mut self, population: &str, from: u64, count: u64) -> Result<Vec<u16>, String> {
        self.container
            .read_bf16(&mut self.file, population, from, count)
            .map_err(|error| error.to_string())
    }
}

pub struct SourceInputs<'a> {
    pub model_root: &'a Path,
    pub source_model_sha256: &'a str,
    pub baseline_text: &'a Path,
    pub perturbed_text: &'a Path,
    pub development_baseline_image: &'a Path,
    pub development_perturbed_image: &'a Path,
    pub held_out_baseline_image: &'a Path,
    pub held_out_perturbed_image: &'a Path,
    pub patch_size: u32,
    pub pooling_kernel_size: u32,
    pub max_soft_tokens: usize,
}

pub fn conduct(inputs: SourceInputs<'_>) -> Result<SourceConduct, String> {
    if inputs.source_model_sha256.len() != 64
        || inputs.patch_size == 0
        || inputs.pooling_kernel_size == 0
        || inputs.max_soft_tokens == 0
    {
        return Err("I4 source declaration is malformed".to_owned());
    }
    let side = inputs
        .patch_size
        .checked_mul(inputs.pooling_kernel_size)
        .ok_or("vision pooling-cell extent overflow")?;
    let development_baseline = read_rgb(inputs.development_baseline_image)?;
    let development_perturbed = read_rgb(inputs.development_perturbed_image)?;
    let (crop, changed_development_pixels) =
        derive_crop(&development_baseline, &development_perturbed, side)?;
    let held_out_baseline = read_rgb(inputs.held_out_baseline_image)?;
    let held_out_perturbed = read_rgb(inputs.held_out_perturbed_image)?;
    let changed_held_out_pixels =
        changed_inside_crop(&held_out_baseline, &held_out_perturbed, crop)?;
    if changed_held_out_pixels == 0 {
        return Err(
            "the held-out PDF raster does not witness the declared perturbation".to_owned(),
        );
    }

    let tokenizer_json =
        fs::read(inputs.model_root.join("tokenizer.json")).map_err(|error| error.to_string())?;
    let baseline_text_bytes = fs::read(inputs.baseline_text).map_err(|error| error.to_string())?;
    let perturbed_text_bytes =
        fs::read(inputs.perturbed_text).map_err(|error| error.to_string())?;
    let baseline_text =
        std::str::from_utf8(&baseline_text_bytes).map_err(|error| error.to_string())?;
    let perturbed_text =
        std::str::from_utf8(&perturbed_text_bytes).map_err(|error| error.to_string())?;
    let baseline_tokens = tokenize_exterior_occurrence(&tokenizer_json, baseline_text, true)
        .map_err(|error| error.to_string())?;
    let perturbed_tokens = tokenize_exterior_occurrence(&tokenizer_json, perturbed_text, true)
        .map_err(|error| error.to_string())?;

    let mut source = ModelSource::open(inputs.model_root)?;
    let mut row_cache = BTreeMap::<u32, (String, u64)>::new();
    let mut text = Vec::new();
    for family in 0..2 {
        for (state, path, bytes, tokens) in [
            (
                0,
                inputs.baseline_text,
                &baseline_text_bytes,
                &baseline_tokens,
            ),
            (
                1,
                inputs.perturbed_text,
                &perturbed_text_bytes,
                &perturbed_tokens,
            ),
        ] {
            let mut token_faces = Vec::with_capacity(tokens.ids.len());
            let mut consequence = Sha256::new();
            let mut incidence = Sha256::new();
            let mut source_weight_octets_read = 0u64;
            for (at, (token_id, (start, end))) in tokens
                .ids
                .iter()
                .copied()
                .zip(tokens.byte_offsets.iter().copied())
                .enumerate()
            {
                let (row_sha256, octets) = match row_cache.get(&token_id) {
                    Some(entry) => entry.clone(),
                    None => {
                        let words = source.rows(TEXT_EMBED, token_id as usize, 1)?;
                        let entry = (sha_words(&words), (words.len() * 2) as u64);
                        row_cache.insert(token_id, entry.clone());
                        entry
                    }
                };
                source_weight_octets_read += octets;
                consequence.update(token_id.to_le_bytes());
                consequence.update(row_sha256.as_bytes());
                incidence.update((at as u64).to_le_bytes());
                incidence.update((start as u64).to_le_bytes());
                incidence.update((end as u64).to_le_bytes());
                token_faces.push(TextTokenFace {
                    token_id,
                    byte_start: start,
                    byte_end: end,
                    embedding_row_sha256: row_sha256,
                });
            }
            consequence.update(b"scale=16*sqrt(10)");
            let occurrence_sha256 = sha(bytes);
            let consequence_sha256 = hex(consequence.finalize());
            let incidence_sha256 = hex(incidence.finalize());
            text.push(TextSourceConduct {
                family,
                state,
                occurrence: path.display().to_string(),
                occurrence_sha256,
                tokens: token_faces,
                exact_embedding_scale: "16·√10 (the positive algebraic root of s²=2560)".to_owned(),
                consequence_sha256,
                incidence_sha256,
                source_weight_octets_read,
            });
        }
    }

    let patch_size = inputs.patch_size as usize;
    let positions = patch_positions(inputs.pooling_kernel_size);
    let projection = source.whole(VISION_INPUT)?;
    let projection_tensor = source
        .container
        .tensor(VISION_INPUT)
        .map_err(|error| error.to_string())?;
    let output_width = projection_tensor.shape[0];
    let input_width = projection_tensor.shape[1];
    if input_width != patch_size * patch_size * 3 || projection.len() != output_width * input_width
    {
        return Err(
            "Gemma vision input projection does not match the processor patch extent".to_owned(),
        );
    }
    let position_tensor = source
        .container
        .tensor(VISION_POSITION)
        .map_err(|error| error.to_string())?;
    if position_tensor.shape.len() != 3
        || position_tensor.shape[0] != 2
        || position_tensor.shape[2] != output_width
    {
        return Err("Gemma vision position table does not match the patch projection".to_owned());
    }
    let position_extent = position_tensor.shape[1];
    let mut position_rows = Vec::with_capacity(positions.len() * 2);
    for (x, y) in &positions {
        if *x as usize >= position_extent || *y as usize >= position_extent {
            return Err("patch position exceeds Gemma's position table".to_owned());
        }
        position_rows.push(source.bf16_span(
            VISION_POSITION,
            *x as u64 * output_width as u64,
            output_width as u64,
        )?);
        position_rows.push(source.bf16_span(
            VISION_POSITION,
            (position_extent as u64 + *y as u64) * output_width as u64,
            output_width as u64,
        )?);
    }
    let augmented_width = input_width + position_rows.len();
    let mut augmented = Vec::with_capacity(output_width * augmented_width);
    for row in 0..output_width {
        augmented.extend_from_slice(&projection[row * input_width..(row + 1) * input_width]);
        for position in &position_rows {
            augmented.push(position[row]);
        }
    }

    let image_occurrences = [
        (
            0,
            0,
            inputs.development_baseline_image,
            &development_baseline,
        ),
        (
            0,
            1,
            inputs.development_perturbed_image,
            &development_perturbed,
        ),
        (1, 0, inputs.held_out_baseline_image, &held_out_baseline),
        (1, 1, inputs.held_out_perturbed_image, &held_out_perturbed),
    ];
    let mut all_queries = Vec::new();
    let mut image_query_ranges = Vec::new();
    for (_, _, _, image) in &image_occurrences {
        let start = all_queries.len();
        all_queries.extend(patch_queries(image, crop, patch_size, augmented_width)?);
        image_query_ranges.push(start..all_queries.len());
    }
    let chart = ResidentReadout::new().map_err(|error| error.to_string())?;
    let mounted = chart
        .mount_bfloat16(&augmented, augmented_width)
        .map_err(|error| error.to_string())?;
    let borrowed = all_queries.iter().collect::<Vec<_>>();
    let returned = mounted
        .score_many(&borrowed)
        .map_err(|error| error.to_string())?;
    if returned.len() != all_queries.len() {
        return Err(
            "the resident vision passage returned an incomplete query population".to_owned(),
        );
    }

    let source_position_octets = (position_rows.iter().map(Vec::len).sum::<usize>() * 2) as u64;
    let source_projection_octets = (projection.len() * 2) as u64;
    let mut vision = Vec::new();
    for ((family, state, path, image), range) in
        image_occurrences.into_iter().zip(image_query_ranges)
    {
        let mut scores = Vec::new();
        let mut consequence = Sha256::new();
        for (position, score) in positions.iter().zip(&returned[range]) {
            for value in &score.scores {
                consequence.update(value.to_le_bytes());
            }
            consequence.update(score.readout_exponent.to_le_bytes());
            consequence.update(255u32.to_le_bytes());
            scores.push(ExactPatchScore {
                x: position.0,
                y: position.1,
                numerator: score.scores.clone(),
                dyadic_exponent: score.readout_exponent,
                denominator: 255,
            });
        }
        let incidence_sha256 = vision_incidence(image, crop, &positions)?;
        vision.push(VisionSourceConduct {
            family,
            state,
            occurrence: path.display().to_string(),
            occurrence_sha256: sha(&fs::read(path).map_err(|error| error.to_string())?),
            crop,
            image_extent: [image.width(), image.height()],
            patch_grid: [inputs.pooling_kernel_size, inputs.pooling_kernel_size],
            scores,
            consequence_sha256: hex(consequence.finalize()),
            incidence_sha256,
            source_weight_octets_read: source_projection_octets + source_position_octets,
            exact_multiply_accumulates: (positions.len() * output_width * augmented_width) as u64,
        });
    }

    let mut responses = Vec::with_capacity(text.len() + vision.len());
    responses.extend(text.iter().map(|conduct| SourcePortResponse {
        family: conduct.family,
        state: conduct.state,
        port: ModalityPort::TextCodeword,
        occurrence: conduct.occurrence.clone(),
        occurrence_sha256: conduct.occurrence_sha256.clone(),
        consequence_sha256: conduct.consequence_sha256.clone(),
        incidence_sha256: conduct.incidence_sha256.clone(),
        semantic_units: conduct.tokens.len() as u64,
    }));
    responses.extend(vision.iter().map(|conduct| SourcePortResponse {
        family: conduct.family,
        state: conduct.state,
        port: ModalityPort::VisionPatch,
        occurrence: conduct.occurrence.clone(),
        occurrence_sha256: conduct.occurrence_sha256.clone(),
        consequence_sha256: conduct.consequence_sha256.clone(),
        incidence_sha256: conduct.incidence_sha256.clone(),
        semantic_units: conduct.scores.len() as u64,
    }));

    let text_octets = text
        .iter()
        .map(|entry| entry.source_weight_octets_read)
        .sum::<u64>();
    let exact_work = vision
        .iter()
        .map(|entry| entry.exact_multiply_accumulates)
        .sum::<u64>();
    let query_ingress_octets = all_queries
        .iter()
        .map(|query| query.entries.len() * std::mem::size_of::<i64>())
        .sum::<usize>() as u64;
    let result_egress_octets = returned
        .iter()
        .map(|scores| scores.scores.len() * std::mem::size_of::<i128>())
        .sum::<usize>() as u64;
    let valid_patches = all_queries.len();
    let padded_per_image = inputs
        .max_soft_tokens
        .checked_mul((inputs.pooling_kernel_size * inputs.pooling_kernel_size) as usize)
        .and_then(|extent| extent.checked_sub(positions.len()))
        .ok_or("processor padding extent is narrower than the valid crop")?;
    Ok(SourceConduct {
        schema: "holonics.i4.source-conduct.v1".to_owned(),
        truth_status: "implemented-exact".to_owned(),
        source_model_sha256: inputs.source_model_sha256.to_owned(),
        source_model_path: inputs.model_root.display().to_string(),
        processor_law: "Gemma4ImageProcessor(do_resize=false) exact RGB /255; patchify C,H,W -> patch-y,patch-x,inside-y,inside-x,C; Gemma4VisionPatchEmbedder computes W·(2p-255)/255 + P[x] + P[y]".to_owned(),
        crop_found_from_development_pair_only: crop,
        changed_development_pixels,
        changed_held_out_pixels,
        text,
        vision,
        responses,
        apparatus: SourceApparatus {
            resident_chart: chart.device_name().to_owned(),
            patch_projection_rows: output_width,
            patch_projection_width: augmented_width,
            valid_patch_queries: valid_patches,
            masked_padding_queries_elided_by_receiver_factor: padded_per_image * 4,
            resident_projection_octets: mounted.resident_octets() as u64,
            source_weight_octets_read: source_projection_octets
                + source_position_octets
                + text_octets,
            query_ingress_octets,
            result_egress_octets,
            exact_multiply_accumulates: exact_work,
            dependency_span: augmented_width as u64,
        },
        open_exterior: vec![
            "the sixteen-layer vision encoder, pooler, multimodal RMS rebase and 768→2560 projection remain an unexecuted source-path fibre".to_owned(),
            "the text transformer interior remains inherited standing; I4 conducts the real token embedding boundary only".to_owned(),
            "audio and video source ports remain unavailable executable-path obstructions in I4".to_owned(),
        ],
    })
}

fn read_rgb(path: &Path) -> Result<RgbImage, String> {
    image::load_from_memory(&fs::read(path).map_err(|error| error.to_string())?)
        .map_err(|error| error.to_string())
        .map(|image| image.to_rgb8())
}

fn derive_crop(left: &RgbImage, right: &RgbImage, side: u32) -> Result<(Crop, u64), String> {
    if left.dimensions() != right.dimensions() || side == 0 {
        return Err("the development image pair does not share one exact raster chart".to_owned());
    }
    let mut lower = [u32::MAX, u32::MAX];
    let mut upper = [0u32, 0u32];
    let mut changed = 0u64;
    for y in 0..left.height() {
        for x in 0..left.width() {
            if left.get_pixel(x, y) != right.get_pixel(x, y) {
                changed += 1;
                lower[0] = lower[0].min(x);
                lower[1] = lower[1].min(y);
                upper[0] = upper[0].max(x);
                upper[1] = upper[1].max(y);
            }
        }
    }
    if changed == 0 {
        return Err("the development image passage has no changed pixel face".to_owned());
    }
    let crop = Crop {
        x: lower[0] / side * side,
        y: lower[1] / side * side,
        side,
    };
    if upper[0] >= crop.x + side
        || upper[1] >= crop.y + side
        || crop.x + side > left.width()
        || crop.y + side > left.height()
    {
        return Err(
            "the changed development face does not fit one material-derived pooling cell"
                .to_owned(),
        );
    }
    Ok((crop, changed))
}

fn changed_inside_crop(left: &RgbImage, right: &RgbImage, crop: Crop) -> Result<u64, String> {
    if left.dimensions() != right.dimensions()
        || crop.x + crop.side > left.width()
        || crop.y + crop.side > left.height()
    {
        return Err("the held-out raster does not admit the development crop".to_owned());
    }
    Ok((crop.y..crop.y + crop.side)
        .flat_map(|y| (crop.x..crop.x + crop.side).map(move |x| (x, y)))
        .filter(|(x, y)| left.get_pixel(*x, *y) != right.get_pixel(*x, *y))
        .count() as u64)
}

fn patch_positions(extent: u32) -> Vec<(u32, u32)> {
    (0..extent)
        .flat_map(|y| (0..extent).map(move |x| (x, y)))
        .collect()
}

fn patch_queries(
    image: &RgbImage,
    crop: Crop,
    patch_size: usize,
    augmented_width: usize,
) -> Result<Vec<AlignedMaterial>, String> {
    let grid = crop.side as usize / patch_size;
    let position_columns = augmented_width - patch_size * patch_size * 3;
    if position_columns != 2 * grid * grid {
        return Err("the augmented patch projection and spatial incidence disagree".to_owned());
    }
    let mut queries = Vec::with_capacity(grid * grid);
    for patch_y in 0..grid {
        for patch_x in 0..grid {
            let mut entries = Vec::with_capacity(augmented_width);
            let mut negatives = 0u64;
            let mut widest = 0u32;
            for inside_y in 0..patch_size {
                for inside_x in 0..patch_size {
                    let pixel = image.get_pixel(
                        crop.x + (patch_x * patch_size + inside_x) as u32,
                        crop.y + (patch_y * patch_size + inside_y) as u32,
                    );
                    for channel in pixel.0 {
                        let value = 2 * i64::from(channel) - 255;
                        negatives += u64::from(value < 0);
                        widest = widest.max(value.unsigned_abs().ilog2() + 1);
                        entries.push(value);
                    }
                }
            }
            entries.resize(augmented_width, 0);
            let slot = patch_y * grid + patch_x;
            entries[patch_size * patch_size * 3 + 2 * slot] = 255;
            entries[patch_size * patch_size * 3 + 2 * slot + 1] = 255;
            queries.push(AlignedMaterial {
                entries,
                exponent: 0,
                entry_octaves: widest.max(8),
                negatives,
            });
        }
    }
    Ok(queries)
}

fn vision_incidence(
    image: &RgbImage,
    crop: Crop,
    positions: &[(u32, u32)],
) -> Result<String, String> {
    if crop.x + crop.side > image.width() || crop.y + crop.side > image.height() {
        return Err("vision incidence crop leaves the raster".to_owned());
    }
    let mut hasher = Sha256::new();
    hasher.update(image.width().to_le_bytes());
    hasher.update(image.height().to_le_bytes());
    hasher.update(crop.x.to_le_bytes());
    hasher.update(crop.y.to_le_bytes());
    hasher.update(crop.side.to_le_bytes());
    for (ordinal, (x, y)) in positions.iter().enumerate() {
        hasher.update((ordinal as u64).to_le_bytes());
        hasher.update(x.to_le_bytes());
        hasher.update(y.to_le_bytes());
        if ordinal > 0 {
            hasher.update((ordinal as u64 - 1).to_le_bytes());
            hasher.update((ordinal as u64).to_le_bytes());
        }
    }
    Ok(hex(hasher.finalize()))
}

fn sha_words(words: &[u16]) -> String {
    let mut hasher = Sha256::new();
    for word in words {
        hasher.update(word.to_le_bytes());
    }
    hex(hasher.finalize())
}

pub fn sha(bytes: &[u8]) -> String {
    hex(Sha256::digest(bytes))
}

fn hex(bytes: impl AsRef<[u8]>) -> String {
    bytes
        .as_ref()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}
