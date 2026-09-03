use std::path::Path;

use holonic_engine::{
    embedding_fiber::{ResidentReadout, align_bfloat16, score_serially},
    foreign_map::manifest_safetensors,
    native_ecology::holonic_intelligence::{
        NativeOperatorResidence, dismantle_full_native_operator, mount_operator_surface,
    },
};
use serde::Serialize;

#[derive(Serialize)]
struct Receipt<'a> {
    residence:
        &'a holonic_engine::native_ecology::holonic_intelligence::NativeOperatorResidenceReceipt,
    widest_population: u32,
    first_tile_rows: usize,
    first_tile_width: usize,
    first_tile_frame: i32,
    second_tile_frame: i32,
    one_alignment_pool_reused: bool,
    all_source_coefficients_resident: bool,
    complete_matrix_rows: usize,
    complete_matrix_width: usize,
    resident_and_serial_exact_scores_agree: bool,
    resident_and_complete_matrix_frames_agree: bool,
    exact_multiply_accumulates: u64,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let returned = dismantle_full_native_operator(Path::new(&root))?;
    let widest = returned
        .native
        .coefficient_populations
        .iter()
        .max_by_key(|population| population.shape.last().copied().unwrap_or(0))
        .ok_or("no coefficient population")?
        .ordinal;
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence =
        NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    let requested_rows = residence.receipt().tile_rows;
    let (first_address, first_rows, first_width, first_frame) = {
        let tile = residence.align_tile(widest, 0, requested_rows)?;
        (
            tile.mounted.readout.aligned_address(),
            tile.mounted.readout.rows(),
            tile.mounted.readout.width(),
            tile.mounted.readout.exponent(),
        )
    };
    let (second_address, second_frame) = {
        let tile = residence.align_tile(widest, requested_rows, 1)?;
        (
            tile.mounted.readout.aligned_address(),
            tile.mounted.readout.exponent(),
        )
    };
    let matrix_name = "model.language_model.layers.0.per_layer_input_gate.weight";
    let matrix_ordinal = returned
        .exterior
        .populations
        .iter()
        .find(|population| population.source_name == matrix_name)
        .ok_or("the complete matrix is absent")?
        .ordinal;
    let (mut source_file, source_container) =
        manifest_safetensors(&format!("{root}/model.safetensors"))?;
    let matrix_words = source_container.read_bf16_whole(&mut source_file, matrix_name)?;
    let matrix = align_bfloat16(&matrix_words)?;
    let (query_words, query_width) = source_container.read_rows_bf16(
        &mut source_file,
        "model.language_model.embed_tokens.weight",
        818,
        1,
    )?;
    let query = align_bfloat16(&query_words)?;
    let serial_scores = score_serially(&matrix, &query, query_width, None)?;
    let (resident_scores, resident_matrix_frame, exact_multiply_accumulates) = {
        let tile = residence.align_tile(matrix_ordinal, 0, 256)?;
        let scores = tile.mounted.readout.score(&query, None)?;
        (
            scores.scores,
            scores.readout_exponent,
            scores.exact_multiply_accumulates,
        )
    };
    println!(
        "{}",
        serde_json::to_string_pretty(&Receipt {
            residence: residence.receipt(),
            widest_population: widest.0,
            first_tile_rows: first_rows,
            first_tile_width: first_width,
            first_tile_frame: first_frame,
            second_tile_frame: second_frame,
            one_alignment_pool_reused: first_address == second_address,
            all_source_coefficients_resident: residence.receipt().raw_coefficient_octets
                == returned.native.coefficient_octets()?,
            complete_matrix_rows: 256,
            complete_matrix_width: query_width,
            resident_and_serial_exact_scores_agree: resident_scores == serial_scores,
            resident_and_complete_matrix_frames_agree: resident_matrix_frame == matrix.exponent,
            exact_multiply_accumulates,
        })?
    );
    Ok(())
}
