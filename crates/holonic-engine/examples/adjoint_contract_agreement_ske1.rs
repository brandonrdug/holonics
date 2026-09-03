//! SKE1, first owner: the adjoint of the contraction agrees exactly with the serial chart.
//!
//! A returning differential crosses one cross-section transposed on the card, tile by tile under
//! the single alignment pool, and the result is compared coordinate by coordinate with an exact
//! serial evaluation of the same words on the host. Two populations: one that fits one tile and
//! the tied embedding, which crosses sixteen tiles folded once through the wide partial standing.

use std::path::Path;

use holonic_engine::{
    embedding_fiber::{ResidentReadout, align_bfloat16},
    foreign_map::manifest_safetensors,
    native_ecology::holonic_intelligence::{
        NativeDifferentialSupport, NativeOperatorResidence, adjoint_contract,
        differential_support, dismantle_full_native_operator, mount_operator_surface,
    },
    resident_section::{ResidentGrain, ResidentSectionRest},
};
use serde::Serialize;

#[derive(Serialize)]
struct Agreement {
    population: String,
    cross_section_rows: usize,
    cross_section_width: usize,
    differential_rows: usize,
    tiles: usize,
    map_exponent: i32,
    coordinates: usize,
    exact_agreements: usize,
    enclosed_within_tile_width: usize,
    widest_enclosure: u64,
    all_agree: bool,
    returned_support: NativeDifferentialSupport,
    elapsed_milliseconds: u128,
}

fn differential_word(row: usize, column: usize) -> i64 {
    ((column % 5) as i64 - 2) * (row as i64 + 1) * if column % 3 == 0 { 1 } else { -1 }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let returned = dismantle_full_native_operator(Path::new(&root))?;
    let readout = ResidentReadout::new()?;
    let surface = mount_operator_surface(&readout)?;
    let mut residence =
        NativeOperatorResidence::mount(&surface, &returned.native, &returned.exterior)?;
    let (mut source_file, source_container) =
        manifest_safetensors(&format!("{root}/model.safetensors"))?;
    let grain = ResidentGrain(20);
    let mut agreements = Vec::new();
    for (name, rows) in [
        ("model.language_model.layers.0.per_layer_input_gate.weight", 2usize),
        ("model.language_model.embed_tokens.weight", 1usize),
    ] {
        let started = std::time::Instant::now();
        let population = returned
            .exterior
            .populations
            .iter()
            .find(|population| population.source_name == name)
            .ok_or("the population is absent")?
            .ordinal;
        let descriptor = &returned.native.coefficient_populations[population.0 as usize];
        let [out_rows, inner] = descriptor.shape.as_slice() else {
            return Err("the population is not a matrix".into());
        };
        let intervals: Vec<(i64, i64)> = (0..rows)
            .flat_map(|row| (0..*out_rows).map(move |column| {
                let word = differential_word(row, column);
                (word, word)
            }))
            .collect();
        let bound_octaves = intervals
            .iter()
            .map(|(lo, hi)| 64 - lo.unsigned_abs().max(hi.unsigned_abs()).leading_zeros())
            .max()
            .unwrap_or(1)
            .max(1);
        let differential = surface.mount_section_rest(&ResidentSectionRest {
            rows,
            width: *out_rows,
            grain,
            bound_octaves,
            intervals: intervals.clone(),
        })?;
        let adjoint = adjoint_contract(&mut residence, population, &differential, bound_octaves)?;
        let resident = surface.read_out(&adjoint.section)?;
        let words = source_container.read_bf16_whole(&mut source_file, name)?;
        let aligned = align_bfloat16(&words)?;
        let map_exponent = aligned.exponent;
        let mut exact_agreements = 0usize;
        let mut enclosed = 0usize;
        let mut widest_enclosure = 0u64;
        for row in 0..rows {
            for column in 0..*inner {
                let mut acc: i128 = 0;
                for o in 0..*out_rows {
                    acc += i128::from(aligned.entries[o * inner + column])
                        * i128::from(differential_word(row, o));
                }
                let (floor, ceil) = if map_exponent >= 0 {
                    let shifted = acc << map_exponent;
                    (shifted, shifted)
                } else {
                    let k = (-map_exponent) as u32;
                    (acc >> k, -((-acc) >> k))
                };
                let (lo, hi) = resident[row * inner + column];
                if i128::from(lo) == floor && i128::from(hi) == ceil {
                    exact_agreements += 1;
                }
                // Across tiles every partial is placed once; the join of `tiles` directed
                // placements encloses the exact value with width at most `tiles` grains.
                if i128::from(lo) <= floor
                    && ceil <= i128::from(hi)
                    && lo.abs_diff(hi) <= adjoint.tiles as u64
                {
                    enclosed += 1;
                }
                widest_enclosure = widest_enclosure.max(lo.abs_diff(hi));
            }
        }
        let coordinates = rows * inner;
        agreements.push(Agreement {
            population: name.to_owned(),
            cross_section_rows: *out_rows,
            cross_section_width: *inner,
            differential_rows: rows,
            tiles: adjoint.tiles,
            map_exponent,
            coordinates,
            exact_agreements,
            enclosed_within_tile_width: enclosed,
            widest_enclosure,
            all_agree: exact_agreements == coordinates,
            returned_support: differential_support(rows, *inner, &resident),
            elapsed_milliseconds: started.elapsed().as_millis(),
        });
    }
    let all = agreements.iter().all(|agreement| agreement.all_agree);
    println!("{}", serde_json::to_string_pretty(&agreements)?);
    if !all {
        return Err("the resident adjoint disagreed with the serial chart".into());
    }
    Ok(())
}
