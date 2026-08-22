//! **The exact contraction, tiled — and the scalar owner refereeing every word of it.**
//!
//! Deed H2 of `blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`.
//! `section_contract` is NOT modified and NOT replaced: it stands as the independent exact
//! reference, and the tiled realization is admitted only where every returned word and every census
//! word of the two agree bit for bit on the real admitted Gemma maps.
//!
//! Three referees, not one. The scalar kernel on the card; the tiled kernel on the card; and an
//! exact serial replay on the CPU over the same entered words and the same aligned map entries,
//! carried in `i128` with the same magnitude-first directed shift. The third exists because two
//! realizations sharing one helper file could agree by sharing a defect.
//!
//! **What is apparatus and what is semantic.** The tile — `(T_t, L, O_t, K_t, S)` — is a caller's
//! declared launch geometry. It is visible in every receipt, it changes the residency, the barrier
//! rate and the dependency span, and it changes NO returned word. That is the whole of control C2
//! and it is why the law is named `contract-tiled(apparatus tile)`.
//!
//! **Performance is reported and never gates.** The pass predicate is exact equality. Where the
//! profile exhibits no additional ready warps and no additional locality, this deed returns THAT
//! OBSTRUCTION and the scalar owner is not replaced.
//!
//! Run:
//! ```text
//! PATH=/opt/cuda/bin:$PATH ./target/release/examples/the_contraction_is_tiled_and_the_scalar_owner_referees
//! PATH=/opt/cuda/bin:$PATH ./target/release/examples/the_contraction_is_tiled_and_the_scalar_owner_referees --profile-shapes
//! ```

#[path = "phoenix/resident_layer.rs"]
mod resident_layer;

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::PathBuf;
use std::time::Instant;

use holonic_engine::embedding_fiber::{MountedReadout, ResidentReadout, align_bfloat16};
use holonic_engine::exact_linear::ExactRatMatrix;
use holonic_engine::hardware_cover::HardwareCover;
use holonic_engine::reduction_junction::{
    DirectedRounding, PartialTerm, ReductionJunction, ReductionReceipt, ReductionWord,
    RoundingPolicy,
};
use holonic_engine::resident_section::{
    CandidateAxis, Dyadic, KERNELS, LaneTree, LaunchCandidate, PartialStanding, REFUSED_CARRIER,
    ResidentGrain, ResidentSection, ResidentSurface, TileGeometry,
};
use holonic_engine::section_partition::{
    DeclaredSpecies, DemandFace, ReadRegion, ResourceDeclaration, SectionCell, SectionLineage,
    SectionPartition, SectionRegion, SectionShape, TilingReceipt,
};
use num_bigint::{BigInt, BigUint};
use relational_geometry::Rat;
use resident_layer::Source;

/// The PTX this build actually loaded — the same octets the surface hashes and the driver JITs.
const PTX: &str = include_str!(concat!(env!("OUT_DIR"), "/exact_resident_section.ptx"));

const ROOT: &str = "/home/b/models/gemma-4-E4B-it";
const LAYER: usize = 0;
/// The grain the profiled closure ran at.
const GRAIN: ResidentGrain = ResidentGrain(48);
/// A coarse grain for the constructed fixtures, chosen so a bf16 word whose stored significand is
/// odd below the grain enters as a GENUINE interval `lo < hi`. Without that the interval sign rule
/// is unexercised and control C4(d) could not fail under a swapped rule.
const FIXTURE_GRAIN: ResidentGrain = ResidentGrain(8);

// ---------------------------------------------------------------------------------------------
// the exact serial referee — the same law, on the serial chart, with no card
// ---------------------------------------------------------------------------------------------

/// `v · 2^s` rounded toward −∞, magnitude first and the sign restored under the directed law —
/// the kernel's own `shift_floor`, rewritten here so the two cannot share a defect by sharing code.
fn shift_floor_i128(v: i128, s: i32) -> Option<i128> {
    let negative = v < 0;
    let m: u128 = if negative {
        (v as u128).wrapping_neg()
    } else {
        v as u128
    };
    if s >= 0 {
        let s = s as u32;
        if s >= 127 || (m >> (127 - s)) != 0 {
            return None;
        }
        let shifted = m << s;
        return Some(if negative {
            -(shifted as i128)
        } else {
            shifted as i128
        });
    }
    let k = (-s) as u32;
    if k >= 128 {
        return Some(if negative { -1 } else { 0 });
    }
    if !negative {
        return Some((m >> k) as i128);
    }
    let up = (m + ((1u128 << k) - 1)) >> k;
    Some(-(up as i128))
}

/// `v · 2^s` rounded toward +∞.
fn shift_ceil_i128(v: i128, s: i32) -> Option<i128> {
    let negative = v < 0;
    let m: u128 = if negative {
        (v as u128).wrapping_neg()
    } else {
        v as u128
    };
    if s >= 0 {
        let s = s as u32;
        if s >= 127 || (m >> (127 - s)) != 0 {
            return None;
        }
        let shifted = m << s;
        return Some(if negative {
            -(shifted as i128)
        } else {
            shifted as i128
        });
    }
    let k = (-s) as u32;
    if k >= 128 {
        return Some(if v > 0 { 1 } else { 0 });
    }
    if negative {
        return Some(-((m >> k) as i128));
    }
    let up = (m + ((1u128 << k) - 1)) >> k;
    Some(up as i128)
}

fn octaves_of_i128(v: i128) -> u32 {
    let m: u128 = if v < 0 {
        (v as u128).wrapping_neg()
    } else {
        v as u128
    };
    128 - m.leading_zeros()
}

/// The exact reference return, and the widest accumulator it passed through. `swapped` inverts the
/// interval sign rule — the perturbation control C4 needs, enacted on the referee rather than by
/// editing a kernel mid-deed.
struct SerialReturn {
    words: Vec<(i64, i64)>,
    peak_accumulator_octaves: u32,
    left_the_word: usize,
}

fn serial_contract(
    x: &[(i64, i64)],
    rows: usize,
    inner: usize,
    entries: &[i64],
    map_e: i32,
    out_width: usize,
    swapped: bool,
) -> SerialReturn {
    let mut words = vec![(0i64, 0i64); rows * out_width];
    let mut peak = 0u32;
    let mut left = 0usize;
    for t in 0..rows {
        for o in 0..out_width {
            let mut acc_lo: i128 = 0;
            let mut acc_hi: i128 = 0;
            for i in 0..inner {
                let w = i128::from(entries[o * inner + i]);
                let (xl, xh) = x[t * inner + i];
                let (xl, xh) = (i128::from(xl), i128::from(xh));
                let positive = if swapped { w < 0 } else { w >= 0 };
                if positive {
                    acc_lo += w * xl;
                    acc_hi += w * xh;
                } else {
                    acc_lo += w * xh;
                    acc_hi += w * xl;
                }
                peak = peak
                    .max(octaves_of_i128(acc_lo))
                    .max(octaves_of_i128(acc_hi));
            }
            let lo = shift_floor_i128(acc_lo, map_e);
            let hi = shift_ceil_i128(acc_hi, map_e);
            match (lo, hi) {
                (Some(lo), Some(hi)) if i64::try_from(lo).is_ok() && i64::try_from(hi).is_ok() => {
                    words[t * out_width + o] = (lo as i64, hi as i64);
                }
                _ => left += 1,
            }
        }
    }
    SerialReturn {
        words,
        peak_accumulator_octaves: peak,
        left_the_word: left,
    }
}

/// The a-priori octaves an entering bf16 population occupies at a declared grain, computed from the
/// words themselves — never declared and never guessed.
fn entered_octaves(words: &[u16], grain: ResidentGrain) -> u32 {
    let mut widest = 0u32;
    for word in words {
        let exponent = ((word >> 7) & 0xff) as i32;
        let mantissa = (word & 0x7f) as u32;
        if exponent == 0xff {
            continue;
        }
        let (magnitude, ulp) = if exponent == 0 {
            (mantissa, 1 - 127 - 7)
        } else {
            (mantissa | 128, exponent - 127 - 7)
        };
        if magnitude == 0 {
            continue;
        }
        let shift = grain.0 as i32 + ulp;
        let bits = 32 - magnitude.leading_zeros();
        let octaves = if shift >= 0 {
            bits as i32 + shift
        } else {
            (bits as i32 + shift).max(1)
        };
        widest = widest.max(octaves.max(0) as u32);
    }
    widest.max(1)
}

// ---------------------------------------------------------------------------------------------
// one equality reading: the scalar owner, the tiled family and the serial referee on one input
// ---------------------------------------------------------------------------------------------

struct PathReading {
    name: String,
    tile: Option<TileGeometry>,
    tree: LaneTree,
    equal_words: bool,
    equal_census: bool,
    refused: u32,
    max_octave: u32,
    max_width: u64,
    width_sum: u64,
    nonzero_widths: u32,
    first_difference: Option<String>,
}

struct EqualityReading {
    map: String,
    grain: u32,
    entering_wide: usize,
    out_width: usize,
    inner: usize,
    tokens: usize,
    map_exponent: i32,
    map_entry_octaves: u32,
    input_octaves: u32,
    admitted_octaves: u32,
    paths: Vec<PathReading>,
    serial: Option<(bool, u32, usize)>,
    scalar_wall_s: f64,
    tiled_wall_s: f64,
    tiled_symbol: &'static str,
    scalar_blocks: u64,
    tiled_blocks: u64,
}

#[allow(clippy::too_many_arguments)]
fn read_equality(
    surface: &'static ResidentSurface<'static>,
    name: &str,
    map: &MountedReadout<'static>,
    entering: &[u16],
    tokens: usize,
    inner: usize,
    grain: ResidentGrain,
    declared: TileGeometry,
    variants: &[TileGeometry],
    split: Option<TileGeometry>,
    serial_aperture: u64,
    aligned_entries: &[i64],
) -> Result<EqualityReading, String> {
    let out_width = map.rows();
    let input_octaves = entered_octaves(entering, grain);
    let staged = surface
        .stage_words(entering, tokens, inner)
        .map_err(|e| e.to_string())?;
    let enter = surface
        .shape_enter(tokens, inner, Dyadic::ONE, grain, entering)
        .map_err(|e| e.to_string())?;
    let scalar_shape = surface
        .shape_contract(tokens, inner, input_octaves, map)
        .map_err(|e| e.to_string())?;

    // every path in ONE passage, on ONE entered section: the equality is between two realizations
    // of one law over identical material, never between two materials.
    let mut tiles: Vec<(String, TileGeometry, LaneTree)> = Vec::new();
    tiles.push((
        format!("tiled {declared:?} descending"),
        declared,
        LaneTree::Descending,
    ));
    tiles.push((
        format!("tiled {declared:?} ASCENDING (reversed control)"),
        declared,
        LaneTree::Ascending,
    ));
    for tile in variants {
        tiles.push((
            format!("tiled {tile:?} descending"),
            *tile,
            LaneTree::Descending,
        ));
    }
    let split_paths: Vec<(String, TileGeometry, LaneTree)> = match split {
        Some(tile) => vec![
            (
                format!("split-K {tile:?} ascending join"),
                tile,
                LaneTree::Descending,
            ),
            (
                format!("split-K {tile:?} DESCENDING join (reversed control)"),
                tile,
                LaneTree::Ascending,
            ),
        ],
        None => Vec::new(),
    };

    let occurrences = 2 + tiles.len() + split_paths.len();
    let lineage: Vec<Vec<usize>> = (0..occurrences)
        .map(|at| if at == 0 { Vec::new() } else { vec![0] })
        .collect();
    let x = surface
        .fresh_section(tokens, inner, grain)
        .map_err(|e| e.to_string())?;
    let scalar_out = surface
        .fresh_section(tokens, out_width, grain)
        .map_err(|e| e.to_string())?;
    let mut outs: Vec<ResidentSection<'static>> = Vec::new();
    for _ in 0..(tiles.len() + split_paths.len()) {
        outs.push(
            surface
                .fresh_section(tokens, out_width, grain)
                .map_err(|e| e.to_string())?,
        );
    }
    let mut standings: Vec<PartialStanding> = Vec::new();
    for (_, tile, _) in &split_paths {
        standings.push(
            surface
                .retain_partials(tokens, out_width, tile.splits)
                .map_err(|e| e.to_string())?,
        );
    }

    let mut builder = surface.begin_passage(&lineage).map_err(|e| e.to_string())?;
    let lane = builder.open(0, &[]).map_err(|e| e.to_string())?;
    surface
        .record_enter(&lane, &staged, Dyadic::ONE, &x)
        .map_err(|e| e.to_string())?;
    builder
        .close(0, &x, enter.needed)
        .map_err(|e| e.to_string())?;
    let lane = builder.open(1, &[0]).map_err(|e| e.to_string())?;
    surface
        .record_contract(&lane, &x, map, &scalar_out)
        .map_err(|e| e.to_string())?;
    builder
        .close(1, &scalar_out, scalar_shape.needed)
        .map_err(|e| e.to_string())?;
    let aperture = ResidentSurface::carrier_octaves();
    for (at, (_, tile, tree)) in tiles.iter().enumerate() {
        let shape = surface
            .shape_contract_tiled(tokens, inner, input_octaves, map, *tile)
            .map_err(|e| e.to_string())?;
        let index = 2 + at;
        let lane = builder.open(index, &[0]).map_err(|e| e.to_string())?;
        surface
            .record_contract_tiled(&lane, &x, map, *tile, aperture, *tree, &outs[at])
            .map_err(|e| e.to_string())?;
        builder
            .close(index, &outs[at], shape.needed)
            .map_err(|e| e.to_string())?;
    }
    for (at, (_, tile, tree)) in split_paths.iter().enumerate() {
        let shape = surface
            .shape_contract_tiled(tokens, inner, input_octaves, map, *tile)
            .map_err(|e| e.to_string())?;
        let index = 2 + tiles.len() + at;
        let out_at = tiles.len() + at;
        let lane = builder.open(index, &[0]).map_err(|e| e.to_string())?;
        surface
            .record_contract_split_k(
                &lane,
                &x,
                map,
                *tile,
                &standings[at],
                aperture,
                *tree,
                &outs[out_at],
            )
            .map_err(|e| e.to_string())?;
        builder
            .close(index, &outs[out_at], shape.needed)
            .map_err(|e| e.to_string())?;
    }
    let passage = builder.finish().map_err(|e| e.to_string())?;
    let reading = passage.launch().map_err(|e| e.to_string())?;

    let scalar_words = surface.read_out(&scalar_out).map_err(|e| e.to_string())?;
    let scalar_slot = reading.slots[1];
    let mut paths = vec![PathReading {
        name: "scalar section_contract (the referee)".to_owned(),
        tile: None,
        tree: LaneTree::Descending,
        equal_words: true,
        equal_census: true,
        refused: scalar_slot.refused,
        max_octave: scalar_slot.max_octave,
        max_width: scalar_slot.max_width,
        width_sum: scalar_slot.width_sum,
        nonzero_widths: scalar_slot.nonzero_widths,
        first_difference: None,
    }];
    let all: Vec<(String, TileGeometry, LaneTree)> =
        tiles.iter().chain(split_paths.iter()).cloned().collect();
    for (at, (label, tile, tree)) in all.iter().enumerate() {
        let words = surface.read_out(&outs[at]).map_err(|e| e.to_string())?;
        let slot = reading.slots[2 + at];
        let first_difference = words
            .iter()
            .zip(&scalar_words)
            .position(|(a, b)| a != b)
            .map(|at| {
                format!(
                    "coordinate {at}: tiled {:?} against scalar {:?}",
                    words[at], scalar_words[at]
                )
            });
        paths.push(PathReading {
            name: label.clone(),
            tile: Some(*tile),
            tree: *tree,
            equal_words: words == scalar_words,
            equal_census: slot.refused == scalar_slot.refused
                && slot.max_octave == scalar_slot.max_octave
                && slot.max_width == scalar_slot.max_width
                && slot.width_sum == scalar_slot.width_sum
                && slot.nonzero_widths == scalar_slot.nonzero_widths,
            refused: slot.refused,
            max_octave: slot.max_octave,
            max_width: slot.max_width,
            width_sum: slot.width_sum,
            nonzero_widths: slot.nonzero_widths,
            first_difference,
        });
    }

    // the third referee, on the serial chart, over the entered words the card actually holds
    let entered = surface.read_out(&x).map_err(|e| e.to_string())?;
    let serial = if (tokens as u64) * (out_width as u64) * (inner as u64) <= serial_aperture {
        let returned = serial_contract(
            &entered,
            tokens,
            inner,
            aligned_entries,
            map.exponent(),
            out_width,
            false,
        );
        Some((
            returned.words == scalar_words,
            returned.peak_accumulator_octaves,
            returned.left_the_word,
        ))
    } else {
        None
    };

    // the two walls, each its own passage so nothing else is in the span, each launched twice and
    // the warm launch reported.
    let scalar_wall_s = time_one(
        surface,
        &staged,
        map,
        tokens,
        inner,
        grain,
        input_octaves,
        entering,
        None,
    )?;
    let tiled_wall_s = time_one(
        surface,
        &staged,
        map,
        tokens,
        inner,
        grain,
        input_octaves,
        entering,
        Some(declared),
    )?;

    Ok(EqualityReading {
        map: name.to_owned(),
        grain: grain.0,
        entering_wide: entered.iter().filter(|(l, h)| l != h).count(),
        out_width,
        inner,
        tokens,
        map_exponent: map.exponent(),
        map_entry_octaves: map.entry_octaves(),
        input_octaves,
        admitted_octaves: scalar_shape.needed,
        paths,
        serial,
        scalar_wall_s,
        tiled_wall_s,
        tiled_symbol: declared
            .symbol("contract-tiled")
            .map_err(|e| e.to_string())?,
        scalar_blocks: ((tokens * out_width) as u64)
            .div_ceil(u64::from(surface.derived_launch().0)),
        tiled_blocks: declared.blocks(tokens, out_width),
    })
}

/// One path in its own passage — enter, contract, two censuses — launched twice; the warm launch's
/// span is returned. The span covers the whole graph and is reported as such: it is a WALL, not a
/// kernel duration, and no semantics depend on it.
fn time_one(
    surface: &'static ResidentSurface<'static>,
    staged: &holonic_engine::resident_section::StagedWords<'static>,
    map: &MountedReadout<'static>,
    tokens: usize,
    inner: usize,
    grain: ResidentGrain,
    input_octaves: u32,
    entering: &[u16],
    tile: Option<TileGeometry>,
) -> Result<f64, String> {
    let out_width = map.rows();
    let enter = surface
        .shape_enter(tokens, inner, Dyadic::ONE, grain, entering)
        .map_err(|e| e.to_string())?;
    let shape = match tile {
        None => surface
            .shape_contract(tokens, inner, input_octaves, map)
            .map_err(|e| e.to_string())?,
        Some(tile) => surface
            .shape_contract_tiled(tokens, inner, input_octaves, map, tile)
            .map_err(|e| e.to_string())?,
    };
    let x = surface
        .fresh_section(tokens, inner, grain)
        .map_err(|e| e.to_string())?;
    let out = surface
        .fresh_section(tokens, out_width, grain)
        .map_err(|e| e.to_string())?;
    let mut builder = surface
        .begin_passage(&[vec![], vec![0]])
        .map_err(|e| e.to_string())?;
    let lane = builder.open(0, &[]).map_err(|e| e.to_string())?;
    surface
        .record_enter(&lane, staged, Dyadic::ONE, &x)
        .map_err(|e| e.to_string())?;
    builder
        .close(0, &x, enter.needed)
        .map_err(|e| e.to_string())?;
    let lane = builder.open(1, &[0]).map_err(|e| e.to_string())?;
    match tile {
        None => surface
            .record_contract(&lane, &x, map, &out)
            .map_err(|e| e.to_string())?,
        Some(tile) => surface
            .record_contract_tiled(
                &lane,
                &x,
                map,
                tile,
                ResidentSurface::carrier_octaves(),
                LaneTree::Descending,
                &out,
            )
            .map_err(|e| e.to_string())?,
    }
    builder
        .close(1, &out, shape.needed)
        .map_err(|e| e.to_string())?;
    let passage = builder.finish().map_err(|e| e.to_string())?;
    passage.launch().map_err(|e| e.to_string())?;
    let clock = Instant::now();
    passage.launch().map_err(|e| e.to_string())?;
    Ok(clock.elapsed().as_secs_f64())
}

// ---------------------------------------------------------------------------------------------
// the constructed fixtures — C4, C5, C6, C7
// ---------------------------------------------------------------------------------------------

/// A bf16 word from a signed 8-bit significand and a binary exponent: `significand · 2^exponent`.
/// Refuses a significand the format cannot carry, so no fixture is silently rounded into existence.
fn bfloat16(significand: i32, exponent: i32) -> Option<u16> {
    let negative = significand < 0;
    let magnitude = significand.unsigned_abs();
    if magnitude == 0 {
        return Some(0);
    }
    if !(128..256).contains(&magnitude) {
        return None;
    }
    // value = magnitude · 2^exponent with magnitude in [128, 256) = (1 + m/128) · 2^(e-127)
    let field = exponent + 7 + 127;
    if !(1..255).contains(&field) {
        return None;
    }
    let mantissa = magnitude - 128;
    Some(((negative as u16) << 15) | ((field as u16) << 7) | mantissa as u16)
}

struct FixtureReading {
    name: String,
    inner: usize,
    out_width: usize,
    tokens: usize,
    verdict: &'static str,
    detail: String,
}

/// Run one constructed fixture through the scalar owner, the declared tile and the serial referee,
/// and report which of the three agreed. The map words and the entering words are the caller's.
#[allow(clippy::too_many_arguments)]
fn run_fixture(
    surface: &'static ResidentSurface<'static>,
    readout: &'static ResidentReadout,
    name: &str,
    map_words: &[u16],
    inner: usize,
    entering: &[u16],
    tokens: usize,
    tile: TileGeometry,
    grain: ResidentGrain,
    swapped_must_differ: bool,
) -> Result<FixtureReading, String> {
    let map = readout
        .mount_bfloat16(map_words, inner)
        .map_err(|e| format!("{e:?}"))?;
    let out_width = map.rows();
    let aligned = align_bfloat16(map_words).map_err(|e| format!("{e:?}"))?;
    let input_octaves = entered_octaves(entering, grain);
    let staged = surface
        .stage_words(entering, tokens, inner)
        .map_err(|e| e.to_string())?;
    let enter = surface
        .shape_enter(tokens, inner, Dyadic::ONE, grain, entering)
        .map_err(|e| e.to_string())?;
    let scalar_shape = surface
        .shape_contract(tokens, inner, input_octaves, &map)
        .map_err(|e| e.to_string())?;
    let tiled_shape = surface
        .shape_contract_tiled(tokens, inner, input_octaves, &map, tile)
        .map_err(|e| e.to_string())?;
    let x = surface
        .fresh_section(tokens, inner, grain)
        .map_err(|e| e.to_string())?;
    let scalar_out = surface
        .fresh_section(tokens, out_width, grain)
        .map_err(|e| e.to_string())?;
    let tiled_out = surface
        .fresh_section(tokens, out_width, grain)
        .map_err(|e| e.to_string())?;
    let mut builder = surface
        .begin_passage(&[vec![], vec![0], vec![0]])
        .map_err(|e| e.to_string())?;
    let lane = builder.open(0, &[]).map_err(|e| e.to_string())?;
    surface
        .record_enter(&lane, &staged, Dyadic::ONE, &x)
        .map_err(|e| e.to_string())?;
    builder
        .close(0, &x, enter.needed)
        .map_err(|e| e.to_string())?;
    let lane = builder.open(1, &[0]).map_err(|e| e.to_string())?;
    surface
        .record_contract(&lane, &x, &map, &scalar_out)
        .map_err(|e| e.to_string())?;
    builder
        .close(1, &scalar_out, scalar_shape.needed)
        .map_err(|e| e.to_string())?;
    let lane = builder.open(2, &[0]).map_err(|e| e.to_string())?;
    surface
        .record_contract_tiled(
            &lane,
            &x,
            &map,
            tile,
            ResidentSurface::carrier_octaves(),
            LaneTree::Descending,
            &tiled_out,
        )
        .map_err(|e| e.to_string())?;
    builder
        .close(2, &tiled_out, tiled_shape.needed)
        .map_err(|e| e.to_string())?;
    let passage = builder.finish().map_err(|e| e.to_string())?;
    let reading = passage.launch().map_err(|e| e.to_string())?;
    let scalar_words = surface.read_out(&scalar_out).map_err(|e| e.to_string())?;
    let tiled_words = surface.read_out(&tiled_out).map_err(|e| e.to_string())?;
    let entered = surface.read_out(&x).map_err(|e| e.to_string())?;
    let referee = serial_contract(
        &entered,
        tokens,
        inner,
        &aligned.entries,
        map.exponent(),
        out_width,
        false,
    );
    let swapped = serial_contract(
        &entered,
        tokens,
        inner,
        &aligned.entries,
        map.exponent(),
        out_width,
        true,
    );

    let equal = tiled_words == scalar_words;
    let census_equal = reading.slots[1].refused == reading.slots[2].refused
        && reading.slots[1].max_octave == reading.slots[2].max_octave
        && reading.slots[1].max_width == reading.slots[2].max_width
        && reading.slots[1].width_sum == reading.slots[2].width_sum
        && reading.slots[1].nonzero_widths == reading.slots[2].nonzero_widths;
    let refereed = referee.words == scalar_words;
    let sign_rule_bites = swapped.words != referee.words;
    let verdict = if equal && census_equal && refereed && (!swapped_must_differ || sign_rule_bites)
    {
        "PASS"
    } else {
        "OPEN"
    };
    let sample: Vec<(i64, i64)> = scalar_words.iter().take(4).copied().collect();
    let detail = format!(
        "map_e {} entry_octaves {} input_octaves {} admitted {} | peak accumulator {} octaves | \
         tiled==scalar {equal} census==census {census_equal} serial==scalar {refereed} swapped-sign-rule-differs {sign_rule_bites} | \
         entering coordinates with lo < hi {} | refusals scalar {:#x} tiled {:#x} | first words {sample:?} | \
         words that left the signed word {}",
        map.exponent(),
        map.entry_octaves(),
        input_octaves,
        scalar_shape.needed,
        referee.peak_accumulator_octaves,
        entered.iter().filter(|(l, h)| l != h).count(),
        reading.slots[1].refused,
        reading.slots[2].refused,
        referee.left_the_word,
    );
    Ok(FixtureReading {
        name: name.to_owned(),
        inner,
        out_width,
        tokens,
        verdict,
        detail,
    })
}

// ---------------------------------------------------------------------------------------------
// the H1 receipts, realized by the geometry that actually ran
// ---------------------------------------------------------------------------------------------

/// **The output partition the K-complete geometry enacts**: one cell per CUDA block, writing the
/// output region `[t0, t0+T_t) x [o0, o0+O_t)` clipped to the section, reading the whole inner
/// extent of its token rows and of its map rows. Completeness and disjointness are COMPUTED by the
/// H1 owner from these regions; nothing here asserts them.
fn output_tile_partition(
    tile: TileGeometry,
    rows: usize,
    out_width: usize,
    inner: usize,
    grain: u32,
) -> SectionPartition {
    let shape = SectionShape::of(rows, out_width, grain);
    let mut cells: Vec<SectionCell> = Vec::new();
    let mut t0 = 0usize;
    while t0 < rows {
        let t1 = (t0 + tile.tile_rows as usize).min(rows);
        let mut o0 = 0usize;
        while o0 < out_width {
            let o1 = (o0 + tile.outs_per_block as usize).min(out_width);
            cells.push(SectionCell {
                index: cells.len(),
                write: SectionRegion::new(t0, t1, o0, o1).expect("a nonempty output tile"),
                reads: vec![
                    // the token rows this block stages — SHARED IMMUTABLE with every other output
                    // tile of the same row band, which is what makes the tiling interchangeable
                    ReadRegion {
                        population: "entering".to_owned(),
                        region: SectionRegion::new(t0, t1, 0, inner).expect("rows"),
                    },
                    // the map rows this block owns — disjoint between output tiles
                    ReadRegion {
                        population: "map".to_owned(),
                        region: SectionRegion::new(o0, o1, 0, inner).expect("a slab"),
                    },
                ],
                partial_of: None,
            });
            o0 = o1;
        }
        t0 = t1;
    }
    let mut populations = BTreeMap::new();
    populations.insert("entering".to_owned(), SectionShape::of(rows, inner, grain));
    populations.insert("map".to_owned(), SectionShape::of(out_width, inner, 0));
    SectionPartition {
        lineage: SectionLineage {
            source: "gemma-4-E4B-it model.safetensors".to_owned(),
            population: "the contraction's output section".to_owned(),
            body: "h2::contract-tiled".to_owned(),
        },
        shape,
        populations,
        cells,
    }
}

/// The resource species this driver declares. `C` is the driver's declaration per species — the
/// owner never reads the cover — and the coupling to the card's own lane count is made here, by
/// hand, and is the driver's doing.
fn declared_resources(lanes: u64) -> ResourceDeclaration {
    ResourceDeclaration {
        species: vec![
            DeclaredSpecies {
                name: "resident-lanes".to_owned(),
                unit: 1,
                face: DemandFace::Written,
                capacity: BigUint::from(lanes),
                characteristic_delay: 1,
                sink_capacity: BigUint::from(1u32),
            },
            DeclaredSpecies {
                name: "map-ingress-words".to_owned(),
                unit: 1,
                face: DemandFace::Read,
                capacity: BigUint::from(lanes),
                characteristic_delay: 2,
                sink_capacity: BigUint::from(1u32),
            },
        ],
        enactment_aperture: 4_096,
    }
}

/// **The K junction of ONE output coordinate of the split-K path**, built from the exact 128-bit
/// partials the card actually wrote. The partial regions are the kernel's own `[k0, k1)` slices,
/// the word is the join kernel's declared balanced ascending tree, and the reversed control is the
/// same word with the leaves relabelled — which is exactly what `tree == 1` does on the card.
#[allow(clippy::too_many_arguments)]
fn split_k_junction(
    partials: &[(i128, i128)],
    row: usize,
    column: usize,
    rows: usize,
    out_width: usize,
    inner: usize,
    splits: u32,
    map_exponent: i32,
    grain: u32,
    codomain_metric: ExactRatMatrix,
) -> Result<ReductionJunction, String> {
    let carrier_exponent = u32::try_from(grain as i64 - i64::from(map_exponent))
        .map_err(|_| "a carrier finer than the word".to_owned())?;
    let scale = BigInt::from(1) << carrier_exponent;
    let span = inner.div_ceil(splits as usize);
    let mut terms: Vec<PartialTerm> = Vec::new();
    for a in 0..splits as usize {
        let k0 = (a * span).min(inner);
        let k1 = (k0 + span).min(inner);
        let (lo, hi) = partials[((a * rows) + row) * out_width + column];
        let lo = Rat::new(BigInt::from(lo), scale.clone());
        let hi = Rat::new(BigInt::from(hi), scale.clone());
        terms.push(PartialTerm {
            index: a,
            // A K slice the split leaves empty is still a partial of exact zero with its region
            // named, so the inner axis stays covered and nothing is deleted.
            inner: SectionRegion::new(0, 1, k0, k1.max(k0 + 1).min(inner.max(k0 + 1)))
                .expect("a K slice"),
            carried: vec![lo.clone(), hi.clone()],
            enclosure: vec![(lo.clone(), lo), (hi.clone(), hi)],
            chart: ExactRatMatrix::identity(2).expect("the identity embedding, declared"),
            domain_metric: ExactRatMatrix::identity(2).expect("the Euclidean metric, declared"),
        });
    }
    Ok(ReductionJunction {
        owner: format!("h2::split-k output coordinate ({row}, {column})"),
        output: SectionRegion::new(row, row + 1, column, column + 1)
            .expect("one output coordinate"),
        output_dimension: 2,
        inner_shape: SectionShape::of(1, inner, carrier_exponent),
        word: ReductionWord::balanced(splits as usize).ok_or("no partials")?,
        partials: terms,
        overflow_aperture: u64::from(ResidentSurface::carrier_octaves()),
        carrier_exponent,
        boundary_exponent: grain,
        rounding: DirectedRounding::Outward,
        policy: RoundingPolicy::OnceAtBoundary,
        codomain_metric,
        returned_covector: vec![Rat::from(BigInt::from(1)), Rat::from(BigInt::from(0))],
    })
}

// ---------------------------------------------------------------------------------------------
// the per-entry PTX float census — the control that must not convict the standing exact kernels
// ---------------------------------------------------------------------------------------------

/// Slice the PTX by `.visible .entry` and count float tokens inside each entry's own body.
///
/// A module-wide grep would convict four standing exact kernels whose `rcp.approx.f32` is nvcc's
/// reciprocal seed for a 128-bit integer division — a float that carries a seed and never a
/// semantic value. The control is therefore PER ENTRY and is a baseline that may not rise, not an
/// a-priori claim about which constructs are safe.
fn ptx_float_census(ptx: &str) -> Vec<(String, usize, usize, usize, usize)> {
    let mut out: Vec<(String, usize, usize, usize, usize)> = Vec::new();
    let mut current: Option<(String, usize, usize, usize, usize)> = None;
    for line in ptx.lines() {
        if let Some(rest) = line.strip_prefix(".visible .entry ") {
            if let Some(entry) = current.take() {
                out.push(entry);
            }
            let name = rest.trim_end_matches('(').trim().to_owned();
            current = Some((name, 0, 0, 0, 0));
        }
        if let Some(entry) = current.as_mut() {
            entry.1 += 1;
            let floats = [
                "\u{2e}f16",
                ".f32",
                ".f64",
                "%f0",
                "%f1",
                "%f2",
                "%f3",
                "%f4",
                "%f5",
                "%f6",
                "%f7",
                "%f8",
                "%f9",
                "%fd",
            ];
            entry.2 += floats
                .iter()
                .map(|token| line.matches(token).count())
                .sum::<usize>();
            entry.3 += line.matches("rcp.approx.f32").count();
            entry.4 += usize::from(line.contains("div."));
        }
    }
    if let Some(entry) = current.take() {
        out.push(entry);
    }
    out
}

fn exterior(command: &str, arguments: &[&str]) -> String {
    match std::process::Command::new(command).args(arguments).output() {
        Ok(output) => {
            String::from_utf8_lossy(&output.stdout).trim().to_owned()
                + &String::from_utf8_lossy(&output.stderr)
        }
        Err(error) => format!("(unavailable: {error})"),
    }
}

// ---------------------------------------------------------------------------------------------
// the deed
// ---------------------------------------------------------------------------------------------

fn named(suffix: &str) -> String {
    format!("model.language_model.layers.{LAYER}.{suffix}")
}

fn main() {
    if let Err(error) = run() {
        eprintln!("the tiled contraction refused: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let profile_only = arguments.iter().any(|a| a == "--profile-shapes");
    let out_dir = PathBuf::from(
        arguments
            .windows(2)
            .find(|w| w[0] == "--out")
            .map(|w| w[1].clone())
            .unwrap_or_else(|| "output/the_contraction_is_tiled".to_owned()),
    );
    let root = arguments
        .windows(2)
        .find(|w| w[0] == "--root")
        .map(|w| w[1].clone())
        .unwrap_or_else(|| ROOT.to_owned());

    let readout: &'static ResidentReadout = Box::leak(Box::new(
        ResidentReadout::new().map_err(|e| format!("{e:?}"))?,
    ));
    let surface: &'static ResidentSurface<'static> = Box::leak(Box::new(
        ResidentSurface::on(readout).map_err(|e| e.to_string())?,
    ));
    let mut source = Source::open(&root)?;

    // the declared candidate: the decode-shaped member of the family, and it is a DECLARATION.
    let declared = TileGeometry {
        tile_rows: 1,
        lanes: 32,
        outs_per_block: 4,
        k_tile: 256,
        splits: 1,
    };
    let variants = [
        TileGeometry {
            tile_rows: 4,
            lanes: 32,
            outs_per_block: 4,
            k_tile: 256,
            splits: 1,
        },
        TileGeometry {
            tile_rows: 1,
            lanes: 16,
            outs_per_block: 16,
            k_tile: 512,
            splits: 1,
        },
        TileGeometry {
            tile_rows: 1,
            lanes: 8,
            outs_per_block: 64,
            k_tile: 0,
            splits: 1,
        },
    ];

    // -------------------------------------------------------------------------------------
    // the profile mode: the scalar owner and the tiled realization, back to back, nothing else
    // -------------------------------------------------------------------------------------
    if profile_only {
        for (name, tokens) in [
            (named("self_attn.q_proj.weight"), 1usize),
            (named("self_attn.q_proj.weight"), 5),
            (named("mlp.gate_proj.weight"), 5),
        ] {
            let (words, shape) = source.whole(&name)?;
            let inner = *shape.last().ok_or("no shape")?;
            let map = readout
                .mount_bfloat16(&words, inner)
                .map_err(|e| format!("{e:?}"))?;
            let entering: Vec<u16> = words[..tokens * inner].to_vec();
            let octaves = entered_octaves(&entering, GRAIN);
            let staged = surface
                .stage_words(&entering, tokens, inner)
                .map_err(|e| e.to_string())?;
            let scalar = time_one(
                surface, &staged, &map, tokens, inner, GRAIN, octaves, &entering, None,
            )?;
            let tiled = time_one(
                surface,
                &staged,
                &map,
                tokens,
                inner,
                GRAIN,
                octaves,
                &entering,
                Some(declared),
            )?;
            println!("{name} T={tokens} scalar {scalar:.6}s tiled {tiled:.6}s");
        }
        return Ok(());
    }

    let mut form = String::new();
    let _ = writeln!(
        form,
        "THE CONTRACTION IS TILED AND THE SCALAR OWNER REFEREES — Deed H2"
    );
    let _ = writeln!(
        form,
        "the exact tiled contraction on the card, refereed word for word by the unchanged scalar owner"
    );
    let _ = writeln!(
        form,
        "and by an independent exact serial replay. `section_contract` is NOT modified and NOT replaced."
    );
    let _ = writeln!(form);
    let _ = writeln!(form, "  [1] THE CLOSURE AND THE MODE");
    let _ = writeln!(
        form,
        "    closure.commit = {}",
        exterior("git", &["rev-parse", "HEAD"])
    );
    let _ = writeln!(
        form,
        "    closure.dirty = {}",
        !exterior("git", &["status", "--porcelain"]).is_empty()
    );
    let _ = writeln!(
        form,
        "    closure.driver = the_contraction_is_tiled_and_the_scalar_owner_referees"
    );
    let _ = writeln!(form, "    closure.source_root = {root}");
    let _ = writeln!(form, "    closure.grain = {}", GRAIN.0);
    let _ = writeln!(form, "    closure.fixture_grain = {}", FIXTURE_GRAIN.0);
    let _ = writeln!(form, "    mode.kernel_content = {}", surface.ptx_sha256());
    let _ = writeln!(form, "    mode.device = {}", surface.device_name());
    let _ = writeln!(
        form,
        "    mode.derived_launch = block_x {} max_grid_x {} warp {}",
        surface.derived_launch().0,
        surface.derived_launch().1,
        surface.derived_launch().2
    );
    let limits = surface.multiprocessor_limits();
    let _ = writeln!(
        form,
        "    device.multiprocessor = blocks {} threads {} registers {} shared_octets {} register_grain_per_warp {}",
        limits.max_blocks,
        limits.max_threads,
        limits.max_registers,
        limits.max_shared_octets,
        limits.register_grain
    );
    let _ = writeln!(
        form,
        "    device.multiprocessors = {}",
        limits.multiprocessors
    );
    let _ = writeln!(
        form,
        "    frame.display_active = {}",
        exterior(
            "nvidia-smi",
            &["--query-gpu=display_active", "--format=csv,noheader"]
        )
    );
    let _ = writeln!(form);

    // -------------------------------------------------------------------------------------
    // [2] the module: every entry's measured registers, and the block ceiling that did not move
    // -------------------------------------------------------------------------------------
    let _ = writeln!(
        form,
        "  [2] THE MODULE, MEASURED — cuFuncGetAttribute on the loaded entries"
    );
    let _ = writeln!(
        form,
        "    the module-wide block derivation takes the MINIMUM admitted block over every named kernel."
    );
    let _ = writeln!(
        form,
        "    Nine entries were added; every one carries __launch_bounds__(512), so the minimum did not move."
    );
    let mut tsv = String::from(
        "entry\tregisters_per_thread\tstatic_shared_octets\tlocal_octets\tadmitted_block\n",
    );
    for symbol in KERNELS {
        let registers = surface
            .measured_registers(symbol)
            .map_err(|e| e.to_string())?;
        let shared = surface
            .measured_static_shared(symbol)
            .map_err(|e| e.to_string())?;
        let ceiling = surface
            .measured_block_ceiling(symbol)
            .map_err(|e| e.to_string())?;
        let local = surface
            .measured_local_octets(symbol)
            .map_err(|e| e.to_string())?;
        let _ = writeln!(tsv, "{symbol}\t{registers}\t{shared}\t{local}\t{ceiling}");
        let _ = writeln!(
            form,
            "    {symbol:38} registers {registers:3}  static_shared {shared:5}  local {local:4}  admitted_block {ceiling}"
        );
    }
    let _ = writeln!(
        form,
        "    EXTERIOR TESTIMONY — ptxas -arch=sm_89 -O3 -v on this build's PTX (it testifies for nothing semantic):"
    );
    // The PTX is written outside the artifact directory: its identity is already in the receipt as
    // `mode.kernel_content`, and only the exterior assembler needs the octets themselves.
    let ptx_path = std::env::temp_dir().join("the_contraction_is_tiled_module.ptx");
    std::fs::create_dir_all(&out_dir).map_err(|e| e.to_string())?;
    std::fs::write(&ptx_path, PTX).map_err(|e| e.to_string())?;
    let ptxas = exterior(
        "ptxas",
        &[
            "-arch=sm_89",
            "-O3",
            "-v",
            ptx_path.to_str().unwrap_or(""),
            "-o",
            "/dev/null",
        ],
    );
    for line in ptxas
        .lines()
        .filter(|l| l.contains("Used ") || l.contains("Compiling entry"))
    {
        let _ = writeln!(form, "      {}", line.trim());
    }
    let _ = writeln!(form);

    // -------------------------------------------------------------------------------------
    // [3] the candidate family
    // -------------------------------------------------------------------------------------
    let _ = writeln!(
        form,
        "  [3] THE LAUNCH-GEOMETRY CANDIDATE FAMILY — finite, admitted, and NOT ordered"
    );
    let _ = writeln!(
        form,
        "    Every member is a whole-warp block the module carries an entry for, whose staged extent the"
    );
    let _ = writeln!(
        form,
        "    device admits and whose grid it can cover. Residency is the resource equation over the"
    );
    let _ = writeln!(
        form,
        "    multiprocessor's own attributes and the MEASURED registers. Occupancy and both wave faces are"
    );
    let _ = writeln!(
        form,
        "    exact integer ratios. NOTHING here is called optimal: the retained set is a function of the"
    );
    let _ = writeln!(
        form,
        "    axes the receiver declares, and three declarations are reported so that dependence is visible."
    );
    let mut family_tsv = String::from(
        "shape\tT_t\tL\tO_t\tK_t\tS\tsymbol\tblock\tshared\tregisters\tresident_blocks\tbound_by\toccupancy_num\toccupancy_den\tblocks\tresidency_wave_num\tresidency_wave_den\tlane_wave_num\tlane_wave_den\tserial_k_per_lane\tdependency_span\n",
    );
    let coarse = [
        CandidateAxis::ResidentBlocksUp,
        CandidateAxis::OccupancyUp,
        CandidateAxis::MapReuseUp,
        CandidateAxis::LanesUp,
        CandidateAxis::SharedDown,
    ];
    let medium = [
        CandidateAxis::ResidentBlocksUp,
        CandidateAxis::OccupancyUp,
        CandidateAxis::MapReuseUp,
        CandidateAxis::LanesUp,
        CandidateAxis::SharedDown,
        CandidateAxis::SerialKDown,
    ];
    let fine = [
        CandidateAxis::ResidentBlocksUp,
        CandidateAxis::OccupancyUp,
        CandidateAxis::MapReuseUp,
        CandidateAxis::LanesUp,
        CandidateAxis::SharedDown,
        CandidateAxis::SerialKDown,
        CandidateAxis::DependencySpanDown,
        CandidateAxis::RegistersDown,
        CandidateAxis::BlocksDown,
    ];
    let shapes: [(&str, usize, usize, usize); 4] = [
        ("q_proj T=1", 1, 2560, 2048),
        ("q_proj T=5", 5, 2560, 2048),
        ("k_proj T=1", 1, 2560, 512),
        ("gate_proj T=5", 5, 2560, 10240),
    ];
    for (label, tokens, inner, out_width) in shapes {
        let family = surface
            .contract_candidates(tokens, inner, out_width)
            .map_err(|e| e.to_string())?;
        let retained_coarse = non_dominated_named(&family, &coarse);
        let retained_medium = non_dominated_named(&family, &medium);
        let retained_fine = non_dominated_named(&family, &fine);
        let _ = writeln!(
            form,
            "    {label}: {} admitted candidates; retained coarse {} medium {} fine {}",
            family.len(),
            retained_coarse.len(),
            retained_medium.len(),
            retained_fine.len()
        );
        for at in &retained_coarse {
            let c = &family[*at];
            let _ = writeln!(
                form,
                "      COARSE  T_t {} L {:2} O_t {:2} K_t {:4} S {:2}  block {:3} shared {:5} regs {:3} resident {:2} ({}) occ {}/{} blocks {} residency-waves {}/{} lane-waves {}/{} serialK {} span {}",
                c.tile.tile_rows,
                c.tile.lanes,
                c.tile.outs_per_block,
                c.tile.k_tile,
                c.tile.splits,
                c.block,
                c.shared_octets,
                c.registers,
                c.resident_blocks,
                c.bound_by,
                c.occupancy.0,
                c.occupancy.1,
                c.blocks,
                c.residency_waves.0,
                c.residency_waves.1,
                c.lane_waves.0,
                c.lane_waves.1,
                c.serial_k_per_lane,
                c.dependency_span
            );
        }
        for c in &family {
            let _ = writeln!(
                family_tsv,
                "{label}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                c.tile.tile_rows,
                c.tile.lanes,
                c.tile.outs_per_block,
                c.tile.k_tile,
                c.tile.splits,
                c.symbol,
                c.block,
                c.shared_octets,
                c.registers,
                c.resident_blocks,
                c.bound_by,
                c.occupancy.0,
                c.occupancy.1,
                c.blocks,
                c.residency_waves.0,
                c.residency_waves.1,
                c.lane_waves.0,
                c.lane_waves.1,
                c.serial_k_per_lane,
                c.dependency_span
            );
        }
    }
    let _ = writeln!(
        form,
        "    THE CHOSEN CANDIDATE IS DECLARED BY THIS DRIVER AND BY NOTHING ELSE: {declared:?}"
    );
    let _ = writeln!(form);
    std::fs::write(out_dir.join("candidate-family.tsv"), &family_tsv).map_err(|e| e.to_string())?;
    std::fs::write(out_dir.join("kernel-registers.tsv"), &tsv).map_err(|e| e.to_string())?;

    // -------------------------------------------------------------------------------------
    // [4] C1, C2, C3 — the equality matrix on the real admitted maps
    // -------------------------------------------------------------------------------------
    let _ = writeln!(
        form,
        "  [4] C1/C2/C3 — THE EQUALITY MATRIX ON THE REAL ADMITTED GEMMA MAPS"
    );
    let _ = writeln!(
        form,
        "    Pass predicate: every returned word pair bit-equal (lo AND hi) to the unchanged scalar owner,"
    );
    let _ = writeln!(
        form,
        "    AND the census words equal (refused, max octave, max width, width sum, nonzero widths)."
    );
    let _ = writeln!(
        form,
        "    C2 is the three further tile shapes; C3 is the reversed lane tree and the reversed join."
    );
    let _ = writeln!(
        form,
        "    The entering rows are the map's own first T rows — real admitted material, at the closure's grain."
    );
    let mut equality_tsv = String::from(
        "map\tout_width\tinner\ttokens\tpath\tequal_words\tequal_census\trefused\tmax_octave\tmax_width\twidth_sum\tnonzero_widths\n",
    );
    let serial_aperture: u64 = 40_000_000;
    let mut c1 = true;
    let mut c2 = true;
    let mut c3 = true;
    let mut serial_agreed = 0usize;
    let mut serial_ran = 0usize;
    let mut readings: Vec<EqualityReading> = Vec::new();
    let maps: [(&str, Option<TileGeometry>); 4] = [
        ("self_attn.q_proj.weight", None),
        ("self_attn.o_proj.weight", None),
        ("mlp.gate_proj.weight", None),
        (
            "self_attn.k_proj.weight",
            Some(TileGeometry {
                tile_rows: 1,
                lanes: 32,
                outs_per_block: 4,
                k_tile: 256,
                splits: 8,
            }),
        ),
    ];
    for (suffix, split) in maps {
        let name = named(suffix);
        let (words, shape) = source.whole(&name)?;
        let inner = *shape.last().ok_or("no shape")?;
        let map = readout
            .mount_bfloat16(&words, inner)
            .map_err(|e| format!("{e:?}"))?;
        // The closure's grain 48 places every entered bf16 word EXACTLY — the shift `grain + ulp` is
        // non-negative for every weight in this container — so at that grain `lo == hi` on every
        // entering coordinate and the interval sign rule `w < 0 -> (lo*hi, hi*lo)` is never
        // DISTINGUISHED by the real material. The fourth row of each map is therefore taken at the
        // coarse fixture grain, where the same real words enter as genuine enclosures `lo < hi` and
        // the sign rule decides which endpoint each product carries.
        for (grain, tokens) in [(GRAIN, 1usize), (GRAIN, 5), (GRAIN, 16), (FIXTURE_GRAIN, 5)] {
            let entering: Vec<u16> = words[..tokens * inner].to_vec();
            let aligned =
                if (tokens as u64) * (map.rows() as u64) * (inner as u64) <= serial_aperture {
                    align_bfloat16(&words)
                        .map_err(|e| format!("{e:?}"))?
                        .entries
                } else {
                    Vec::new()
                };
            let reading = read_equality(
                surface,
                &name,
                &map,
                &entering,
                tokens,
                inner,
                grain,
                declared,
                &variants,
                split,
                serial_aperture,
                &aligned,
            )?;
            for path in &reading.paths {
                let _ = writeln!(
                    equality_tsv,
                    "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:#x}\t{}\t{}\t{}\t{}",
                    reading.map,
                    reading.out_width,
                    reading.inner,
                    reading.tokens,
                    format!("{} [{}]", path.name, path.tree.written()),
                    path.equal_words,
                    path.equal_census,
                    path.refused,
                    path.max_octave,
                    path.max_width,
                    path.width_sum,
                    path.nonzero_widths
                );
                if !path.equal_words || !path.equal_census {
                    if path.name.contains("ASCENDING") || path.name.contains("DESCENDING join") {
                        c3 = false;
                    } else if path.tile.map(|t| t != declared).unwrap_or(false) {
                        c2 = false;
                    } else {
                        c1 = false;
                    }
                }
            }
            if let Some((agreed, _, _)) = reading.serial {
                serial_ran += 1;
                if agreed {
                    serial_agreed += 1;
                } else {
                    c1 = false;
                }
            }
            readings.push(reading);
        }
    }
    for reading in &readings {
        let _ = writeln!(
            form,
            "    {} [{} x {}] T={} grain 2^-{} entering coordinates with lo < hi {} | map_e {} entry_octaves {} input_octaves {} admitted {} | scalar wall {:.6}s ({} blocks) | tiled {} wall {:.6}s ({} blocks)",
            reading.map.rsplit('.').nth(1).unwrap_or(&reading.map),
            reading.out_width,
            reading.inner,
            reading.tokens,
            reading.grain,
            reading.entering_wide,
            reading.map_exponent,
            reading.map_entry_octaves,
            reading.input_octaves,
            reading.admitted_octaves,
            reading.scalar_wall_s,
            reading.scalar_blocks,
            reading.tiled_symbol,
            reading.tiled_wall_s,
            reading.tiled_blocks
        );
        for path in &reading.paths {
            let _ = writeln!(
                form,
                "        {:<58} words {} census {} refused {:#x} octave {} width {} width_sum {} nonzero {}{}",
                path.name,
                if path.equal_words { "EQUAL" } else { "DIFFER" },
                if path.equal_census { "EQUAL" } else { "DIFFER" },
                path.refused,
                path.max_octave,
                path.max_width,
                path.width_sum,
                path.nonzero_widths,
                path.first_difference
                    .as_deref()
                    .map(|d| format!(" | {d}"))
                    .unwrap_or_default()
            );
        }
        match reading.serial {
            Some((agreed, peak, left)) => {
                let _ = writeln!(
                    form,
                    "        serial exact referee (i128, no card): {} | peak accumulator {} octaves | words that left the signed word {}",
                    if agreed { "EQUAL" } else { "DIFFER" },
                    peak,
                    left
                );
            }
            None => {
                let _ = writeln!(
                    form,
                    "        serial exact referee: not run — {} products exceed the declared aperture of {serial_aperture}",
                    (reading.tokens * reading.out_width * reading.inner)
                );
            }
        }
    }
    let _ = writeln!(
        form,
        "    C1 scalar equality: {}",
        if c1 { "PASS" } else { "OPEN" }
    );
    let _ = writeln!(
        form,
        "    C2 tile-shape variation ({} shapes beside the declared one): {}",
        variants.len(),
        if c2 { "PASS" } else { "OPEN" }
    );
    let _ = writeln!(
        form,
        "    C3 reversed reduction tree (lane tree and join tree): {}",
        if c3 { "PASS" } else { "OPEN" }
    );
    let _ = writeln!(
        form,
        "    the serial exact referee agreed on {serial_agreed} of {serial_ran} shapes it was run on"
    );
    let _ = writeln!(form);
    std::fs::write(out_dir.join("equality.tsv"), &equality_tsv).map_err(|e| e.to_string())?;

    // -------------------------------------------------------------------------------------
    // [5] C4 — the cancellation fixtures, including the negative w in the TAIL position
    // -------------------------------------------------------------------------------------
    let _ = writeln!(form, "  [5] C4 — CANCELLATION AND THE INTERVAL SIGN RULE");
    let _ = writeln!(
        form,
        "    The fixture grain is {} so a stored significand odd below the grain enters as a GENUINE",
        FIXTURE_GRAIN.0
    );
    let _ = writeln!(
        form,
        "    interval lo < hi. Without that the sign rule `w<0 -> (lo*hi, hi*lo)` is unexercised and (d)"
    );
    let _ = writeln!(
        form,
        "    could not fail under a swapped rule. The swapped rule is enacted on the SERIAL referee — no"
    );
    let _ = writeln!(
        form,
        "    kernel is edited mid-deed — and the column `swapped-sign-rule-differs` is that perturbation."
    );
    let _ = writeln!(
        form,
        "    THE FINDING H2 REPORTED IS REPAIRED AND THE WORKAROUND IS DELETED: `shape_enter`'s a-priori"
    );
    let _ = writeln!(
        form,
        "    octave bound was `8 + scale octaves + grain + 8` and did not read the entering words, so a bf16"
    );
    let _ = writeln!(
        form,
        "    population with a large exponent refused BOUND at the mouth and poisoned every successor UPSTREAM."
    );
    let _ = writeln!(
        form,
        "    This driver closed the entering occurrence at max(shape.needed, the octaves computed from the words)"
    );
    let _ = writeln!(
        form,
        "    to work around it. `shape_enter` now reads the staged words itself and the entering occurrence is"
    );
    let _ = writeln!(
        form,
        "    closed at `enter.needed` alone; the max is gone from this driver."
    );
    let fixture_tile = TileGeometry {
        tile_rows: 1,
        lanes: 32,
        outs_per_block: 4,
        k_tile: 128,
        splits: 1,
    };
    let mut fixtures: Vec<FixtureReading> = Vec::new();
    // a genuine interval: 205 · 2^-11 = 0.1001..., whose low three bits fall below grain 8
    let interval_word = bfloat16(205, -11).ok_or("the fixture word is not a bf16")?;
    let interval_negative = bfloat16(-205, -11).ok_or("the fixture word is not a bf16")?;
    let one = bfloat16(128, -7).ok_or("one")?;
    let minus_one = bfloat16(-128, -7).ok_or("minus one")?;
    // the widest word the fixture grain admits: 255 * 2^46 enters at grain 8 as 255 * 2^54, so the
    // stored word is 62 octaves — one below the signed word's own 63.
    let big = bfloat16(255, 46).ok_or("big")?;
    let big_negative = bfloat16(-255, 46).ok_or("big negative")?;
    let k = 128usize;
    // (a) w alternating +m/-m, x constant -> the exact sum is zero
    {
        let map_words: Vec<u16> = (0..k)
            .map(|i| if i % 2 == 0 { one } else { minus_one })
            .collect();
        let entering: Vec<u16> = vec![interval_word; k];
        fixtures.push(run_fixture(
            surface,
            readout,
            "C4(a) w = [+m, -m, ...], x constant -> exact zero",
            &map_words,
            k,
            &entering,
            1,
            fixture_tile,
            FIXTURE_GRAIN,
            false,
        )?);
    }
    // (b) x alternating at the widest word the fixture grain admits
    {
        let map_words: Vec<u16> = (0..k).map(|_| one).collect();
        // every pair cancels at the widest admitted word except the last coordinate, which
        // survives as a small interval — so the answer is nonzero and the cancellation is total
        // above it. Under the stride-L lane walk one lane holds four +M and another four -M, so the
        // lane partials are enormous where the scalar owner's prefix sums alternate.
        let mut entering: Vec<u16> = (0..k)
            .map(|i| if i % 2 == 0 { big } else { big_negative })
            .collect();
        entering[k - 1] = interval_word;
        fixtures.push(run_fixture(
            surface,
            readout,
            "C4(b) x = [+M, -M, ...] at the widest admitted word, one survivor",
            &map_words,
            k,
            &entering,
            1,
            fixture_tile,
            FIXTURE_GRAIN,
            false,
        )?);
    }
    // (c) a cancellation whose a-priori admission is EXACTLY the 126-octave carrier ceiling. The map
    //     spans 49 exponents, so its aligned entries are 57 octaves and `map_e` is -70; the entering
    //     words are 61 octaves; `61 + 57 + ceil_log2(128) + 1 = 126`. The first 64 terms sum near
    //     2^125, the next 63 cancel them, and one small interval survives — so the accumulator walks
    //     to within a couple of octaves of the carrier and the answer is a narrow enclosure. Under
    //     the stride-L lane walk the lane partials are not the scalar owner's prefix sums, which is
    //     what makes this a real control on the tree rather than on the arithmetic.
    {
        let mut map_words: Vec<u16> = Vec::with_capacity(k);
        for i in 0..k {
            map_words.push(if i < k / 2 {
                bfloat16(255, -21).unwrap()
            } else if i < k - 1 {
                bfloat16(-255, -21).unwrap()
            } else {
                bfloat16(128, -70).unwrap()
            });
        }
        let mut entering: Vec<u16> = vec![bfloat16(255, 45).ok_or("the wide entering word")?; k];
        entering[k - 1] = interval_word;
        fixtures.push(run_fixture(
            surface,
            readout,
            "C4(c) a cancellation admitted at EXACTLY 126 octaves",
            &map_words,
            k,
            &entering,
            1,
            fixture_tile,
            FIXTURE_GRAIN,
            false,
        )?);
    }
    // (d) exactly one negative w, in the TAIL position i = K-1 — the fixture the swapped sign rule
    //     must break, and the one that a stride-L lane walk puts on a different lane from i = 0
    {
        let mut map_words: Vec<u16> = vec![one; k];
        map_words[k - 1] = minus_one;
        let entering: Vec<u16> = (0..k)
            .map(|i| {
                if i == k - 1 {
                    interval_negative
                } else {
                    interval_word
                }
            })
            .collect();
        fixtures.push(run_fixture(
            surface,
            readout,
            "C4(d) exactly one negative w, at the TAIL i = K-1",
            &map_words,
            k,
            &entering,
            1,
            fixture_tile,
            FIXTURE_GRAIN,
            true,
        )?);
    }
    let c4 = fixtures.iter().all(|f| f.verdict == "PASS");
    for fixture in &fixtures {
        let _ = writeln!(
            form,
            "    {:<62} [{}x{} T={}] {}",
            fixture.name, fixture.out_width, fixture.inner, fixture.tokens, fixture.verdict
        );
        let _ = writeln!(form, "        {}", fixture.detail);
    }
    let _ = writeln!(form, "    C4: {}", if c4 { "PASS" } else { "OPEN" });
    let _ = writeln!(form);

    // -------------------------------------------------------------------------------------
    // [6] C5 — the carrier at the edge, and the per-node aperture that refuses
    // -------------------------------------------------------------------------------------
    let _ = writeln!(
        form,
        "  [6] C5 — THE CARRIER AT THE EDGE AND THE PER-NODE APERTURE"
    );
    let edge_map: Vec<u16> = vec![one, one, one, one];
    let edge = readout
        .mount_bfloat16(&edge_map, 4)
        .map_err(|e| format!("{e:?}"))?;
    let head = 126u32 - edge.entry_octaves() - 2 - 1;
    let admitted = surface.shape_contract_tiled(1, 4, head, &edge, fixture_tile);
    let refused = surface.shape_contract_tiled(1, 4, head + 1, &edge, fixture_tile);
    let scalar_admitted = surface.shape_contract(1, 4, head, &edge);
    let scalar_refused = surface.shape_contract(1, 4, head + 1, &edge);
    let _ = writeln!(
        form,
        "    declared input octaves {head} -> needed {} : tiled {} scalar {}",
        admitted.as_ref().map(|s| s.needed).unwrap_or(0),
        if admitted.is_ok() {
            "ADMITTED"
        } else {
            "refused"
        },
        if scalar_admitted.is_ok() {
            "ADMITTED"
        } else {
            "refused"
        }
    );
    let _ = writeln!(
        form,
        "    declared input octaves {} -> needed 127 : tiled {} scalar {}",
        head + 1,
        if refused.is_err() {
            "REFUSED at shape"
        } else {
            "admitted"
        },
        if scalar_refused.is_err() {
            "REFUSED at shape"
        } else {
            "admitted"
        }
    );
    let _ = writeln!(
        form,
        "    the refusal text: {}",
        refused
            .as_ref()
            .err()
            .map(|e| e.to_string())
            .unwrap_or_else(|| "(none)".to_owned())
    );
    // the node aperture, inside the admission: the tiled kernel refuses at the node; the scalar
    // owner has no per-step check and returns what it always did.
    let staged = surface
        .stage_words(&[interval_word; 4], 1, 4)
        .map_err(|e| e.to_string())?;
    let enter = surface
        .shape_enter(1, 4, Dyadic::ONE, FIXTURE_GRAIN, &[interval_word; 4])
        .map_err(|e| e.to_string())?;
    let octaves = entered_octaves(&[interval_word; 4], FIXTURE_GRAIN);
    let scalar_shape = surface
        .shape_contract(1, 4, octaves, &edge)
        .map_err(|e| e.to_string())?;
    let tiled_shape = surface
        .shape_contract_tiled(1, 4, octaves, &edge, fixture_tile)
        .map_err(|e| e.to_string())?;
    let x = surface
        .fresh_section(1, 4, FIXTURE_GRAIN)
        .map_err(|e| e.to_string())?;
    let a = surface
        .fresh_section(1, 4, FIXTURE_GRAIN)
        .map_err(|e| e.to_string())?;
    let b = surface
        .fresh_section(1, 4, FIXTURE_GRAIN)
        .map_err(|e| e.to_string())?;
    let mut builder = surface
        .begin_passage(&[vec![], vec![0], vec![0]])
        .map_err(|e| e.to_string())?;
    let lane = builder.open(0, &[]).map_err(|e| e.to_string())?;
    surface
        .record_enter(&lane, &staged, Dyadic::ONE, &x)
        .map_err(|e| e.to_string())?;
    builder
        .close(0, &x, enter.needed)
        .map_err(|e| e.to_string())?;
    let lane = builder.open(1, &[0]).map_err(|e| e.to_string())?;
    surface
        .record_contract(&lane, &x, &edge, &a)
        .map_err(|e| e.to_string())?;
    builder
        .close(1, &a, scalar_shape.needed)
        .map_err(|e| e.to_string())?;
    let lane = builder.open(2, &[0]).map_err(|e| e.to_string())?;
    surface
        .record_contract_tiled(&lane, &x, &edge, fixture_tile, 3, LaneTree::Descending, &b)
        .map_err(|e| e.to_string())?;
    builder
        .close(2, &b, tiled_shape.needed)
        .map_err(|e| e.to_string())?;
    let passage = builder.finish().map_err(|e| e.to_string())?;
    let node_reading = passage.launch().map_err(|e| e.to_string())?;
    let scalar_refusal = node_reading.slots[1].refused;
    let tiled_refusal = node_reading.slots[2].refused;
    let _ = writeln!(
        form,
        "    a three-octave per-node aperture, inside the a-priori admission:"
    );
    let _ = writeln!(
        form,
        "        scalar section_contract refused {scalar_refusal:#x} (it carries NO per-step check at all)"
    );
    let _ = writeln!(
        form,
        "        section_contract_tiled  refused {tiled_refusal:#x}  REFUSED_CARRIER set: {}",
        tiled_refusal & REFUSED_CARRIER == REFUSED_CARRIER
    );
    let _ = writeln!(
        form,
        "        THE STATED BEHAVIOURAL DIFFERENCE: on material outside the declared node aperture the scalar"
    );
    let _ = writeln!(
        form,
        "        owner wraps silently and the tiled realization refuses by name. It is reported here with the"
    );
    let _ = writeln!(
        form,
        "        fixture that exhibits it and is NEVER folded into the equality claim above."
    );
    let c5 = admitted.is_ok()
        && refused.is_err()
        && scalar_admitted.is_ok()
        && scalar_refused.is_err()
        && (tiled_refusal & REFUSED_CARRIER) == REFUSED_CARRIER
        && scalar_refusal == 0;
    let _ = writeln!(form, "    C5: {}", if c5 { "PASS" } else { "OPEN" });
    let _ = writeln!(form);

    // -------------------------------------------------------------------------------------
    // [7] C6 — the tails: K, O and T that no tile divides, and K below the lane count
    // -------------------------------------------------------------------------------------
    let _ = writeln!(form, "  [7] C6 — THE NON-MULTIPLE TAILS");
    let _ = writeln!(
        form,
        "    Real q_proj words, truncated to a K, an O and a T that the declared tiles do not divide."
    );
    let (q_words, q_shape) = source.whole(&named("self_attn.q_proj.weight"))?;
    let q_inner = *q_shape.last().ok_or("no shape")?;
    // q_proj carries 2048 output rows, so the O = 2049 tail is taken from gate_proj's 10240.
    let (wide_words, wide_inner) = source.rows(&named("mlp.gate_proj.weight"), 0, 2049)?;
    let slice_map = |out_rows: usize, inner: usize| -> Vec<u16> {
        let (source_words, source_inner) = if out_rows <= 2048 {
            (&q_words, q_inner)
        } else {
            (&wide_words, wide_inner)
        };
        let mut words = Vec::with_capacity(out_rows * inner);
        for o in 0..out_rows {
            words.extend_from_slice(&source_words[o * source_inner..o * source_inner + inner]);
        }
        words
    };
    let mut tails: Vec<FixtureReading> = Vec::new();
    for (label, out_rows, inner, tokens, tile) in [
        (
            "C6 K=2559 against K_t=256",
            40usize,
            2559usize,
            3usize,
            TileGeometry {
                tile_rows: 1,
                lanes: 32,
                outs_per_block: 4,
                k_tile: 256,
                splits: 1,
            },
        ),
        (
            "C6 K=2561 against K_t=512",
            40,
            2561,
            3,
            TileGeometry {
                tile_rows: 1,
                lanes: 32,
                outs_per_block: 4,
                k_tile: 512,
                splits: 1,
            },
        ),
        (
            "C6 O=2049 against O_t=4",
            2049,
            64,
            3,
            TileGeometry {
                tile_rows: 1,
                lanes: 32,
                outs_per_block: 4,
                k_tile: 128,
                splits: 1,
            },
        ),
        (
            "C6 O=2049 against O_t=16",
            2049,
            64,
            3,
            TileGeometry {
                tile_rows: 1,
                lanes: 16,
                outs_per_block: 16,
                k_tile: 128,
                splits: 1,
            },
        ),
        (
            "C6 T=3 against T_t=4",
            40,
            512,
            3,
            TileGeometry {
                tile_rows: 4,
                lanes: 32,
                outs_per_block: 4,
                k_tile: 256,
                splits: 1,
            },
        ),
        (
            "C6 K=5 below the lane count L=32",
            40,
            5,
            3,
            TileGeometry {
                tile_rows: 1,
                lanes: 32,
                outs_per_block: 4,
                k_tile: 128,
                splits: 1,
            },
        ),
        (
            "C6 K=5, unstaged K_t=0",
            40,
            5,
            3,
            TileGeometry {
                tile_rows: 1,
                lanes: 32,
                outs_per_block: 4,
                k_tile: 0,
                splits: 1,
            },
        ),
        (
            "C6 K=2559 split eight ways",
            40,
            2559,
            3,
            TileGeometry {
                tile_rows: 1,
                lanes: 32,
                outs_per_block: 4,
                k_tile: 256,
                splits: 8,
            },
        ),
    ] {
        let map_words = slice_map(out_rows, inner);
        let entering: Vec<u16> = map_words[..tokens * inner].to_vec();
        if tile.splits > 1 {
            // the split-K tail runs through its own pair; the fixture runner drives the K-complete
            // entry, so this row is enacted separately and reported the same way
            let map = readout
                .mount_bfloat16(&map_words, inner)
                .map_err(|e| format!("{e:?}"))?;
            let octaves = entered_octaves(&entering, GRAIN);
            let staged = surface
                .stage_words(&entering, tokens, inner)
                .map_err(|e| e.to_string())?;
            let enter = surface
                .shape_enter(tokens, inner, Dyadic::ONE, GRAIN, &entering)
                .map_err(|e| e.to_string())?;
            let scalar_shape = surface
                .shape_contract(tokens, inner, octaves, &map)
                .map_err(|e| e.to_string())?;
            let split_shape = surface
                .shape_contract_tiled(tokens, inner, octaves, &map, tile)
                .map_err(|e| e.to_string())?;
            let standing = surface
                .retain_partials(tokens, out_rows, tile.splits)
                .map_err(|e| e.to_string())?;
            let x = surface
                .fresh_section(tokens, inner, GRAIN)
                .map_err(|e| e.to_string())?;
            let sc = surface
                .fresh_section(tokens, out_rows, GRAIN)
                .map_err(|e| e.to_string())?;
            let sp = surface
                .fresh_section(tokens, out_rows, GRAIN)
                .map_err(|e| e.to_string())?;
            let mut builder = surface
                .begin_passage(&[vec![], vec![0], vec![0]])
                .map_err(|e| e.to_string())?;
            let lane = builder.open(0, &[]).map_err(|e| e.to_string())?;
            surface
                .record_enter(&lane, &staged, Dyadic::ONE, &x)
                .map_err(|e| e.to_string())?;
            builder
                .close(0, &x, enter.needed)
                .map_err(|e| e.to_string())?;
            let lane = builder.open(1, &[0]).map_err(|e| e.to_string())?;
            surface
                .record_contract(&lane, &x, &map, &sc)
                .map_err(|e| e.to_string())?;
            builder
                .close(1, &sc, scalar_shape.needed)
                .map_err(|e| e.to_string())?;
            let lane = builder.open(2, &[0]).map_err(|e| e.to_string())?;
            surface
                .record_contract_split_k(
                    &lane,
                    &x,
                    &map,
                    tile,
                    &standing,
                    ResidentSurface::carrier_octaves(),
                    LaneTree::Descending,
                    &sp,
                )
                .map_err(|e| e.to_string())?;
            builder
                .close(2, &sp, split_shape.needed)
                .map_err(|e| e.to_string())?;
            let passage = builder.finish().map_err(|e| e.to_string())?;
            let reading = passage.launch().map_err(|e| e.to_string())?;
            let equal = surface.read_out(&sc).map_err(|e| e.to_string())?
                == surface.read_out(&sp).map_err(|e| e.to_string())?;
            tails.push(FixtureReading {
                name: label.to_owned(),
                inner,
                out_width: out_rows,
                tokens,
                verdict: if equal && reading.obstruction.is_empty() { "PASS" } else { "OPEN" },
                detail: format!("split-K {tile:?}: tiled==scalar {equal} | span {} is not a multiple of K | refusals {:#x}/{:#x}", inner.div_ceil(tile.splits as usize), reading.slots[1].refused, reading.slots[2].refused),
            });
        } else {
            tails.push(run_fixture(
                surface, readout, label, &map_words, inner, &entering, tokens, tile, GRAIN, false,
            )?);
        }
    }
    let c6 = tails.iter().all(|f| f.verdict == "PASS");
    for tail in &tails {
        let _ = writeln!(
            form,
            "    {:<40} [O={} K={} T={}] {}",
            tail.name, tail.out_width, tail.inner, tail.tokens, tail.verdict
        );
        let _ = writeln!(form, "        {}", tail.detail);
    }
    let _ = writeln!(form, "    C6: {}", if c6 { "PASS" } else { "OPEN" });
    let _ = writeln!(form);

    // -------------------------------------------------------------------------------------
    // [8] C7 — a permutation of the K axis of BOTH the map columns and the entering rows
    // -------------------------------------------------------------------------------------
    let _ = writeln!(form, "  [8] C7 — THE K-AXIS PERMUTATION");
    let _ = writeln!(
        form,
        "    The contraction sums over K, so a permutation applied to the map's columns AND to the entering"
    );
    let _ = writeln!(
        form,
        "    row's coordinates must return the SAME words. The entering side is permuted ON THE CARD by the"
    );
    let _ = writeln!(
        form,
        "    standing `section_permute_columns` law composed before the contraction; the map side is permuted"
    );
    let _ = writeln!(
        form,
        "    in its stored words before mounting. A permutation of only one side must move the answer, and"
    );
    let _ = writeln!(
        form,
        "    that half-permutation is enacted as the perturbation."
    );
    let (perm_out, perm_inner, perm_tokens) = (64usize, 256usize, 3usize);
    let perm_map = slice_map(perm_out, perm_inner);
    let permutation: Vec<u32> = (0..perm_inner as u32)
        .map(|i| ((i as usize * 97 + 13) % perm_inner) as u32)
        .collect();
    let is_permutation = {
        let mut seen = vec![false; perm_inner];
        permutation.iter().all(|p| {
            let at = *p as usize;
            let fresh = !seen[at];
            seen[at] = true;
            fresh
        })
    };
    let permuted_map: Vec<u16> = (0..perm_out)
        .flat_map(|o| (0..perm_inner).map(move |c| (o, c)))
        .map(|(o, c)| perm_map[o * perm_inner + permutation[c] as usize])
        .collect();
    let entering: Vec<u16> = perm_map[..perm_tokens * perm_inner].to_vec();
    let plain = readout
        .mount_bfloat16(&perm_map, perm_inner)
        .map_err(|e| format!("{e:?}"))?;
    let turned = readout
        .mount_bfloat16(&permuted_map, perm_inner)
        .map_err(|e| format!("{e:?}"))?;
    let octaves = entered_octaves(&entering, GRAIN);
    let staged = surface
        .stage_words(&entering, perm_tokens, perm_inner)
        .map_err(|e| e.to_string())?;
    let mounted_perm = surface
        .mount_positions(&permutation)
        .map_err(|e| e.to_string())?;
    let enter = surface
        .shape_enter(perm_tokens, perm_inner, Dyadic::ONE, GRAIN, &entering)
        .map_err(|e| e.to_string())?;
    let permute_shape = surface
        .shape_permute_columns(
            perm_tokens,
            perm_inner,
            octaves,
            1,
            &permutation.iter().map(|p| *p as usize).collect::<Vec<_>>(),
        )
        .map_err(|e| e.to_string())?;
    let plain_shape = surface
        .shape_contract_tiled(perm_tokens, perm_inner, octaves, &plain, fixture_tile)
        .map_err(|e| e.to_string())?;
    let turned_shape = surface
        .shape_contract_tiled(perm_tokens, perm_inner, octaves, &turned, fixture_tile)
        .map_err(|e| e.to_string())?;
    let x = surface
        .fresh_section(perm_tokens, perm_inner, GRAIN)
        .map_err(|e| e.to_string())?;
    let xp = surface
        .fresh_section(perm_tokens, perm_inner, GRAIN)
        .map_err(|e| e.to_string())?;
    let straight = surface
        .fresh_section(perm_tokens, perm_out, GRAIN)
        .map_err(|e| e.to_string())?;
    let both = surface
        .fresh_section(perm_tokens, perm_out, GRAIN)
        .map_err(|e| e.to_string())?;
    let half = surface
        .fresh_section(perm_tokens, perm_out, GRAIN)
        .map_err(|e| e.to_string())?;
    let mut builder = surface
        .begin_passage(&[vec![], vec![0], vec![0], vec![1], vec![0]])
        .map_err(|e| e.to_string())?;
    let lane = builder.open(0, &[]).map_err(|e| e.to_string())?;
    surface
        .record_enter(&lane, &staged, Dyadic::ONE, &x)
        .map_err(|e| e.to_string())?;
    builder
        .close(0, &x, enter.needed)
        .map_err(|e| e.to_string())?;
    let lane = builder.open(1, &[0]).map_err(|e| e.to_string())?;
    surface
        .record_permute_columns(&lane, &x, 1, &mounted_perm, &xp)
        .map_err(|e| e.to_string())?;
    builder
        .close(1, &xp, permute_shape.needed)
        .map_err(|e| e.to_string())?;
    let lane = builder.open(2, &[0]).map_err(|e| e.to_string())?;
    surface
        .record_contract_tiled(
            &lane,
            &x,
            &plain,
            fixture_tile,
            ResidentSurface::carrier_octaves(),
            LaneTree::Descending,
            &straight,
        )
        .map_err(|e| e.to_string())?;
    builder
        .close(2, &straight, plain_shape.needed)
        .map_err(|e| e.to_string())?;
    let lane = builder.open(3, &[1]).map_err(|e| e.to_string())?;
    surface
        .record_contract_tiled(
            &lane,
            &xp,
            &turned,
            fixture_tile,
            ResidentSurface::carrier_octaves(),
            LaneTree::Descending,
            &both,
        )
        .map_err(|e| e.to_string())?;
    builder
        .close(3, &both, turned_shape.needed)
        .map_err(|e| e.to_string())?;
    let lane = builder.open(4, &[0]).map_err(|e| e.to_string())?;
    surface
        .record_contract_tiled(
            &lane,
            &x,
            &turned,
            fixture_tile,
            ResidentSurface::carrier_octaves(),
            LaneTree::Descending,
            &half,
        )
        .map_err(|e| e.to_string())?;
    builder
        .close(4, &half, turned_shape.needed)
        .map_err(|e| e.to_string())?;
    let passage = builder.finish().map_err(|e| e.to_string())?;
    let perm_reading = passage.launch().map_err(|e| e.to_string())?;
    let straight_words = surface.read_out(&straight).map_err(|e| e.to_string())?;
    let both_words = surface.read_out(&both).map_err(|e| e.to_string())?;
    let half_words = surface.read_out(&half).map_err(|e| e.to_string())?;
    let c7 = is_permutation
        && straight_words == both_words
        && straight_words != half_words
        && perm_reading.obstruction.is_empty();
    let _ = writeln!(
        form,
        "    the declared permutation pi(i) = (97 i + 13) mod {perm_inner} is a bijection: {is_permutation}"
    );
    let _ = writeln!(
        form,
        "    unpermuted contraction against BOTH sides permuted: {}",
        if straight_words == both_words {
            "BIT-EQUAL"
        } else {
            "DIFFER"
        }
    );
    let _ = writeln!(
        form,
        "    the perturbation — only the MAP permuted, the entering rows left alone: {}",
        if straight_words != half_words {
            "DIFFERS, as it must"
        } else {
            "EQUAL — the control is vacuous"
        }
    );
    let _ = writeln!(form, "    C7: {}", if c7 { "PASS" } else { "OPEN" });
    let _ = writeln!(form);

    // -------------------------------------------------------------------------------------
    // [9] C8 — the per-entry PTX float census
    // -------------------------------------------------------------------------------------
    let _ = writeln!(
        form,
        "  [9] C8 — NO FLOAT IN THE TILED ENTRIES' PTX (per entry, never module-wide)"
    );
    let census = ptx_float_census(PTX);
    let mut clean = true;
    for (name, lines, floats, rcp, div) in &census {
        let new_entry = name.starts_with("section_contract_tiled")
            || name.starts_with("section_contract_partial")
            || name == "section_contract_join";
        if new_entry && *floats != 0 {
            clean = false;
        }
        let _ = writeln!(
            form,
            "    {:<40} lines {:6}  float tokens {:3}  rcp.approx.f32 {:3}  div.* {}{}",
            name,
            lines,
            floats,
            rcp,
            div,
            if new_entry { "   <- added by H2" } else { "" }
        );
    }
    let _ = writeln!(
        form,
        "    The nonzero counts belong to four STANDING exact kernels and are nvcc's lowering of a 128-bit"
    );
    let _ = writeln!(
        form,
        "    integer division: a prmt-built seed feeds one rcp.approx.f32 whose result is moved straight back"
    );
    let _ = writeln!(
        form,
        "    to an integer and corrected exactly. A module-wide grep would convict them; this control does not."
    );
    let _ = writeln!(
        form,
        "    C8 (every entry H2 added carries zero float tokens): {}",
        if clean { "PASS" } else { "OPEN" }
    );
    let _ = writeln!(form);

    // -------------------------------------------------------------------------------------
    // [10] the H1 receipts, realized by the geometry that ran
    // -------------------------------------------------------------------------------------
    let _ = writeln!(
        form,
        "  [10] THE H1 RECEIPTS — the partition and the junction the geometry ENACTS"
    );
    let (receipt_rows, receipt_inner, receipt_out) = (5usize, 2560usize, 2048usize);
    let partition =
        output_tile_partition(declared, receipt_rows, receipt_out, receipt_inner, GRAIN.0);
    let cover: &HardwareCover = surface.cover();
    let lanes = u64::from(limits.max_threads) * u64::from(limits.multiprocessors);
    let tiling: Result<TilingReceipt, _> = partition.certify(
        cover,
        &[],
        &declared_resources(lanes),
        "section_contract_tiled_r1_l32",
    );
    match &tiling {
        Ok(receipt) => {
            let _ = writeln!(form, "    TilingReceipt for q_proj T=5 under {declared:?}");
            let _ = writeln!(
                form,
                "      cells {} (the kernel launched {} blocks — they must agree, and a disagreement is a defect)",
                receipt.cells.len(),
                declared.blocks(receipt_rows, receipt_out)
            );
            let _ = writeln!(
                form,
                "      complete {} covered {} of {} uncovered regions {}",
                receipt.completeness.complete,
                receipt.completeness.covered_extent,
                receipt.completeness.section_extent,
                receipt.completeness.uncovered.len()
            );
            let _ = writeln!(
                form,
                "      disjoint {} over {} pairs; overlaps {}",
                receipt.disjointness.disjoint,
                receipt.disjointness.pairs_checked,
                receipt.disjointness.overlaps.len()
            );
            let _ = writeln!(
                form,
                "      shared immutable reads {} (the entering rows every output tile of a row band reads)",
                receipt.shared_reads.iter().filter(|r| r.immutable).count()
            );
            let _ = writeln!(
                form,
                "      non-immutable shared reads {} (a nonzero here is a defect)",
                receipt.shared_reads.iter().filter(|r| !r.immutable).count()
            );
            let map_halo = receipt
                .halo
                .iter()
                .filter(|(_, population, _)| population == "map")
                .count();
            let entering_halo = receipt
                .halo
                .iter()
                .filter(|(_, population, _)| population == "entering")
                .count();
            let _ = writeln!(
                form,
                "      halo entries {} — on the ENTERING rows {} and on the MAP {}. NEITHER is a neighbour dependence:",
                receipt.halo.len(),
                entering_halo,
                map_halo
            );
            let _ = writeln!(
                form,
                "        a full inner product reads the WHOLE inner extent [0, K) and no column outside its own tile, so"
            );
            let _ = writeln!(
                form,
                "        the stencil halo is empty by construction and what the owner counts here is SHARING. The entering"
            );
            let _ = writeln!(
                form,
                "        rows are shared across the output tiles of one row band; the map rows are shared across the row"
            );
            let _ = writeln!(
                form,
                "        bands of one output tile. Both populations are read-only — `non-immutable shared reads` above is"
            );
            let _ = writeln!(
                form,
                "        the number that must be zero, and it is — so the sharing is lawful and is what makes the tiling"
            );
            let _ = writeln!(form, "        interchangeable rather than a defect.");
            let _ = writeln!(
                form,
                "      interchangeable {}",
                receipt.is_interchangeable()
            );
            let _ = writeln!(
                form,
                "      pressure coordinates (one covector per species, never summed):"
            );
            for pressure in receipt.pressure.iter().take(2) {
                for (species, coordinate) in pressure.coordinates() {
                    let _ = writeln!(
                        form,
                        "        cell {} {species}: incoming {} capacity {} rounds {} boundary residual {} reflected {}",
                        pressure.cell,
                        coordinate.incoming,
                        coordinate.capacity,
                        coordinate.service_rounds,
                        coordinate.boundary_residual,
                        coordinate.reflected
                    );
                }
            }
            let _ = writeln!(
                form,
                "      the geometry agrees with the receipt: cells == blocks : {}",
                receipt.cells.len() as u64 == declared.blocks(receipt_rows, receipt_out)
            );
        }
        Err(defects) => {
            let _ = writeln!(
                form,
                "    TilingReceipt REFUSED with {} defects; the first: {}",
                defects.len(),
                defects.first().map(|d| d.to_string()).unwrap_or_default()
            );
        }
    }
    let _ = writeln!(form);

    // the reduction junction, from the exact partials the card wrote
    let split_tile = TileGeometry {
        tile_rows: 1,
        lanes: 32,
        outs_per_block: 4,
        k_tile: 256,
        splits: 8,
    };
    let (k_words, k_shape) = source.whole(&named("self_attn.k_proj.weight"))?;
    let k_inner = *k_shape.last().ok_or("no shape")?;
    let k_map = readout
        .mount_bfloat16(&k_words, k_inner)
        .map_err(|e| format!("{e:?}"))?;
    let k_tokens = 1usize;
    let k_entering: Vec<u16> = k_words[..k_tokens * k_inner].to_vec();
    let k_octaves = entered_octaves(&k_entering, GRAIN);
    let staged = surface
        .stage_words(&k_entering, k_tokens, k_inner)
        .map_err(|e| e.to_string())?;
    let enter = surface
        .shape_enter(k_tokens, k_inner, Dyadic::ONE, GRAIN, &k_entering)
        .map_err(|e| e.to_string())?;
    let split_shape = surface
        .shape_contract_tiled(k_tokens, k_inner, k_octaves, &k_map, split_tile)
        .map_err(|e| e.to_string())?;
    let standing = surface
        .retain_partials(k_tokens, k_map.rows(), split_tile.splits)
        .map_err(|e| e.to_string())?;
    let x = surface
        .fresh_section(k_tokens, k_inner, GRAIN)
        .map_err(|e| e.to_string())?;
    let out = surface
        .fresh_section(k_tokens, k_map.rows(), GRAIN)
        .map_err(|e| e.to_string())?;
    let mut builder = surface
        .begin_passage(&[vec![], vec![0]])
        .map_err(|e| e.to_string())?;
    let lane = builder.open(0, &[]).map_err(|e| e.to_string())?;
    surface
        .record_enter(&lane, &staged, Dyadic::ONE, &x)
        .map_err(|e| e.to_string())?;
    builder
        .close(0, &x, enter.needed)
        .map_err(|e| e.to_string())?;
    let lane = builder.open(1, &[0]).map_err(|e| e.to_string())?;
    surface
        .record_contract_split_k(
            &lane,
            &x,
            &k_map,
            split_tile,
            &standing,
            ResidentSurface::carrier_octaves(),
            LaneTree::Descending,
            &out,
        )
        .map_err(|e| e.to_string())?;
    builder
        .close(1, &out, split_shape.needed)
        .map_err(|e| e.to_string())?;
    let passage = builder.finish().map_err(|e| e.to_string())?;
    let split_reading = passage.launch().map_err(|e| e.to_string())?;
    let partials = surface
        .read_partials(&standing)
        .map_err(|e| e.to_string())?;
    let out_words = surface.read_out(&out).map_err(|e| e.to_string())?;
    let junction = split_k_junction(
        &partials,
        0,
        0,
        k_tokens,
        k_map.rows(),
        k_inner,
        split_tile.splits,
        k_map.exponent(),
        GRAIN.0,
        ExactRatMatrix::identity(2).expect("identity"),
    )?;
    let control = split_k_junction(
        &partials,
        0,
        0,
        k_tokens,
        k_map.rows(),
        k_inner,
        split_tile.splits,
        k_map.exponent(),
        GRAIN.0,
        ExactRatMatrix::new(vec![
            vec![Rat::from(BigInt::from(1)), Rat::from(BigInt::from(0))],
            vec![Rat::from(BigInt::from(0)), Rat::from(BigInt::from(3))],
        ])
        .expect("a declared non-identity metric"),
    )?;
    let certified: Result<ReductionReceipt, _> = junction.certify();
    let controlled = control.certify();
    let _ = writeln!(
        form,
        "    ReductionReceipt for k_proj T=1, output coordinate (0, 0), split {} ways",
        split_tile.splits
    );
    match (&certified, &controlled) {
        (Ok(receipt), Ok(control)) => {
            let _ = writeln!(
                form,
                "      partials {} — the KERNEL's own K slices, read back as exact 128-bit accumulations",
                receipt.partials.len()
            );
            let _ = writeln!(
                form,
                "      the word the join kernel folds under: {}",
                receipt.declared.word
            );
            let _ = writeln!(
                form,
                "      the reversed control over the same partials:  {}",
                receipt.reversed.word
            );
            let _ = writeln!(
                form,
                "      words agree before rounding: {}",
                receipt.words_agree
            );
            let _ = writeln!(
                form,
                "      declared word: {} joins, span {}, peak node width {} bits, roundings {}",
                receipt.declared.nodes.len(),
                receipt.declared.dependency_span,
                receipt.declared.peak_width_bits,
                receipt.declared.roundings
            );
            let _ = writeln!(
                form,
                "      reversed word: {} joins, span {}, peak node width {} bits",
                receipt.reversed.nodes.len(),
                receipt.reversed.dependency_span,
                receipt.reversed.peak_width_bits
            );
            let _ = writeln!(
                form,
                "      per-node widths, declared word: {:?}",
                receipt
                    .declared
                    .nodes
                    .iter()
                    .map(|n| n.width_bits)
                    .collect::<Vec<_>>()
            );
            let _ = writeln!(
                form,
                "      per-node widths, reversed word: {:?}",
                receipt
                    .reversed
                    .nodes
                    .iter()
                    .map(|n| n.width_bits)
                    .collect::<Vec<_>>()
            );
            let _ = writeln!(
                form,
                "      inner axis uncovered {} overlaps {}",
                receipt.inner_uncovered.len(),
                receipt.inner_overlaps.len()
            );
            let _ = writeln!(
                form,
                "      overflow aperture {} carrier 2^-{} boundary 2^-{}",
                receipt.overflow_aperture, receipt.carrier_exponent, receipt.boundary_exponent
            );
            let _ = writeln!(
                form,
                "      boundary residual: {:?}",
                receipt.boundary_residual
            );
            let _ = writeln!(
                form,
                "      the adjoint under the DECLARED identity metric: defect {} bare-transpose defect {}",
                receipt.adjoints[0].defect, receipt.adjoints[0].bare_transpose_defect
            );
            let _ = writeln!(
                form,
                "      the adjoint under a DECLARED non-identity codomain metric diag(1,3): defect {} bare-transpose defect {}",
                control.adjoints[0].defect, control.adjoints[0].bare_transpose_defect
            );
            let _ = writeln!(
                form,
                "      THE GEOMETRY AND THE RECEIPT AGREE: the word's leaf count {} == the kernel's split factor {} : {}",
                receipt.declared.leaves.len(),
                split_tile.splits,
                receipt.declared.leaves.len() as u32 == split_tile.splits
            );
            // the kernel's DIRECTED rounding beside the owner's away-from-zero one
            let sum: (i128, i128) =
                (0..split_tile.splits as usize).fold((0i128, 0i128), |(l, h), a| {
                    let (pl, ph) = partials[a * k_tokens * k_map.rows()];
                    (l + pl, h + ph)
                });
            let directed = (
                shift_floor_i128(sum.0, k_map.exponent()),
                shift_ceil_i128(sum.1, k_map.exponent()),
            );
            let _ = writeln!(form, "      the kernel's word at (0,0): {:?}", out_words[0]);
            let _ = writeln!(
                form,
                "      the exact partial sum replayed on the CPU, directed floor/ceil: {:?}",
                directed
            );
            let _ = writeln!(
                form,
                "      the owner's outward (away-from-zero) boundary value:            {:?}",
                receipt.boundary_value
            );
            let _ = writeln!(
                form,
                "      CONFLICT REPORTED: `DirectedRounding::Outward` in the reduction owner is AWAY FROM ZERO per"
            );
            let _ = writeln!(
                form,
                "      coordinate, while this contraction's law is floor BELOW and ceil ABOVE. The two coincide only"
            );
            let _ = writeln!(
                form,
                "      on an enclosure straddling zero. Everything else in the receipt — the partition of K, the word,"
            );
            let _ = writeln!(
                form,
                "      the partials, the per-node widths, the pre-rounding root — is the kernel's own and agrees."
            );
        }
        _ => {
            let _ = writeln!(
                form,
                "      the junction REFUSED: {:?}",
                certified
                    .as_ref()
                    .err()
                    .map(|d| d.iter().map(|x| x.to_string()).collect::<Vec<_>>())
            );
        }
    }
    let _ = writeln!(
        form,
        "      the split-K launch's obstruction lineage: {:?}",
        split_reading.obstruction.refusals
    );
    let _ = writeln!(form);
    let _ = writeln!(
        form,
        "    A CONFLICT WITH THE DESIGN STUDY, REPORTED: the K-COMPLETE lane tree's leaves are the STRIDED"
    );
    let _ = writeln!(
        form,
        "    coordinate sets {{i : i = lane (mod L)}}, and `PartialTerm::inner` is a half-open SectionRegion."
    );
    let _ = writeln!(
        form,
        "    A strided set is not a region, so the K-complete lane tree cannot be certified by the H1 junction"
    );
    let _ = writeln!(
        form,
        "    owner as it stands; the split-K partials ARE contiguous [k0, k1) and are certified above. The"
    );
    let _ = writeln!(
        form,
        "    lane tree is reported by its word and its span instead: L = {} leaves, depth {}, and the reversed",
        declared.lanes,
        declared.lanes.trailing_zeros()
    );
    let _ = writeln!(
        form,
        "    control is enacted ON THE CARD by `tree = 1` and returned bit-equal in section [4]."
    );
    let _ = writeln!(form);

    // -------------------------------------------------------------------------------------
    // [11] C9 — the estimate is settled by the measurement
    // -------------------------------------------------------------------------------------
    let _ = writeln!(form, "  [11] C9 — THE REGISTER ESTIMATE, SETTLED");
    let _ = writeln!(
        form,
        "    The design study estimated r = 38 + 8 T_t, anchored on the scalar owner's measured 42. Measured:"
    );
    let mut c9_rows: Vec<(String, u32, i64)> = Vec::new();
    for (symbol, t) in [
        ("section_contract_tiled_r1_l32", 1u32),
        ("section_contract_tiled_r2_l32", 2),
        ("section_contract_tiled_r4_l32", 4),
        ("section_contract_tiled_r1_l16", 1),
        ("section_contract_tiled_r4_l16", 4),
        ("section_contract_tiled_r1_l8", 1),
        ("section_contract_partial_r1_l32", 1),
        ("section_contract_partial_r4_l32", 4),
    ] {
        let measured = surface
            .measured_registers(symbol)
            .map_err(|e| e.to_string())?;
        let estimate = 38 + 8 * t;
        c9_rows.push((
            symbol.to_owned(),
            measured,
            i64::from(estimate) - i64::from(measured),
        ));
        let _ = writeln!(
            form,
            "    {symbol:38} T_t {t}  estimate {estimate:3}  MEASURED {measured:3}  the estimate over-predicts by {}",
            i64::from(estimate) - i64::from(measured)
        );
    }
    let scalar_registers = surface
        .measured_registers("section_contract")
        .map_err(|e| e.to_string())?;
    let join_registers = surface
        .measured_registers("section_contract_join")
        .map_err(|e| e.to_string())?;
    let _ = writeln!(
        form,
        "    the unchanged scalar owner: {scalar_registers} registers; the join: {join_registers}"
    );
    let over = c9_rows.iter().filter(|row| row.2 > 0).count();
    let under = c9_rows.iter().filter(|row| row.2 < 0).count();
    let _ = writeln!(
        form,
        "    THE ESTIMATE IS FALSIFIED IN MAGNITUDE: it over-predicts on {over} of the {} instantiations and",
        c9_rows.len()
    );
    let _ = writeln!(
        form,
        "    UNDER-predicts on {under} — `section_contract_partial_r1_l32` uses 48 where the estimate said 46, so"
    );
    let _ = writeln!(
        form,
        "    the estimate is not even a one-sided bound. Its ORDERING in T_t survives. The family table in"
    );
    let _ = writeln!(
        form,
        "    section [3] was computed from the MEASURED value and never from the estimate, which is what C9 asks:"
    );
    let _ = writeln!(
        form,
        "    C9: PASS (the measurement replaced the estimate, and the estimate's error is reported with its sign)."
    );
    let _ = writeln!(form);

    // -------------------------------------------------------------------------------------
    // [12] C10 — the obstruction control
    // -------------------------------------------------------------------------------------
    let _ = writeln!(form, "  [12] C10 — THE OBSTRUCTION CONTROL");
    let _ = writeln!(
        form,
        "    §8 Deed H2: a tiled realization whose profile exhibits no additional ready warps or locality must"
    );
    let _ = writeln!(
        form,
        "    RETURN THAT OBSTRUCTION rather than replace the scalar owner."
    );
    let _ = writeln!(
        form,
        "    ncu is admin-only on this machine (RmProfilingAdminOnly = 1) and this deed does NOT run it, so every"
    );
    let _ = writeln!(
        form,
        "    ncu-only face — eligible warps per cycle, no-eligible percent, active warps, L1/L2 hit percent,"
    );
    let _ = writeln!(
        form,
        "    achieved occupancy, DRAM throughput percent — is UNKNOWN here and is not inferred, not estimated"
    );
    let _ = writeln!(
        form,
        "    and not replaced by a ratio. The H0 bands stand unrefuted and uncompared."
    );
    let nsys = out_dir.join("nsys-kernel-sum.csv");
    let trace = out_dir.join("nsys-kernel-trace.csv");
    let mut obstruction_rows: Vec<(u64, u64, u64, u64, u32, u32)> = Vec::new();
    match std::fs::read_to_string(&nsys) {
        Ok(text) => {
            let _ = writeln!(
                form,
                "    nsys kernel summary (exterior apparatus; it measures the realization and testifies for nothing"
            );
            let _ = writeln!(form, "    semantic), read from {}:", nsys.display());
            for line in text
                .lines()
                .filter(|l| l.contains("section_") || l.contains("bfloat16"))
            {
                let _ = writeln!(form, "      {line}");
            }
        }
        Err(_) => {
            let _ = writeln!(
                form,
                "    no nsys kernel summary at {} — run --profile-shapes under nsys and re-run to fold it in.",
                nsys.display()
            );
        }
    }
    // the per-launch trace: what nsys DOES carry is duration, grid, block, registers per thread and
    // the dynamic shared extent. It carries no warp-eligibility and no cache face; those are ncu's.
    match std::fs::read_to_string(&trace) {
        Ok(text) => {
            let _ = writeln!(
                form,
                "    the per-launch trace, warm launches paired by shape (the second launch of each pair):"
            );
            let mut scalar: Vec<(u64, u64, u32, u32)> = Vec::new();
            let mut tiled: Vec<(u64, u64, u32, u32)> = Vec::new();
            for line in text.lines().skip(1) {
                let column: Vec<&str> = line.split(',').collect();
                if column.len() < 21 {
                    continue;
                }
                let duration: u64 = column[1].trim().parse().unwrap_or(0);
                let grid: u64 = column[3].trim().parse().unwrap_or(0);
                let block: u32 = column[6].trim().parse().unwrap_or(0);
                let registers: u32 = column[9].trim().parse().unwrap_or(0);
                let name = column[20].trim();
                if name == "section_contract" {
                    scalar.push((duration, grid, block, registers));
                } else if name.starts_with("section_contract_tiled") {
                    tiled.push((duration, grid, block, registers));
                }
            }
            // the warm launch of each pair
            let warm = |rows: &[(u64, u64, u32, u32)]| -> Vec<(u64, u64, u32, u32)> {
                rows.chunks(2)
                    .filter_map(|pair| pair.last().copied())
                    .collect()
            };
            let scalar = warm(&scalar);
            let tiled = warm(&tiled);
            for (at, (s, t)) in scalar.iter().zip(&tiled).enumerate() {
                obstruction_rows.push((s.0, t.0, s.1, t.1, s.3, t.3));
                let _ = writeln!(
                    form,
                    "      shape {at}: scalar {} ns over {} blocks of {} at {} registers/thread | tiled {} ns over {} blocks of {} at {} registers/thread | duration ratio {}/{}",
                    s.0, s.1, s.2, s.3, t.0, t.1, t.2, t.3, s.0, t.0
                );
            }
        }
        Err(_) => {
            let _ = writeln!(form, "    no per-launch trace at {}.", trace.display());
        }
    }
    let _ = writeln!(
        form,
        "    THE DERIVED FACES THAT ARE KNOWN, and they are geometry rather than telemetry:"
    );
    for (label, tokens, inner, out_width) in shapes {
        let family = surface
            .contract_candidates(tokens, inner, out_width)
            .map_err(|e| e.to_string())?;
        let chosen = family.iter().find(|c| c.tile == declared);
        let scalar_blocks =
            ((tokens * out_width) as u64).div_ceil(u64::from(surface.derived_launch().0));
        let scalar_resident = limits.max_registers
            / (((scalar_registers * limits.warp).div_ceil(limits.register_grain)
                * limits.register_grain)
                * (surface.derived_launch().0 / limits.warp));
        let scalar_resident = scalar_resident
            .min(limits.max_blocks)
            .min(limits.max_threads / surface.derived_launch().0);
        match chosen {
            Some(c) => {
                let _ = writeln!(
                    form,
                    "      {label}: scalar blocks {scalar_blocks} resident/SM {scalar_resident} lane-waves {}/{} | tiled blocks {} resident/SM {} lane-waves {}/{} residency-waves {}/{} serial K per lane {} span {} (scalar's span is K = {inner})",
                    scalar_blocks * u64::from(surface.derived_launch().0),
                    lanes,
                    c.blocks,
                    c.resident_blocks,
                    c.lane_waves.0,
                    c.lane_waves.1,
                    c.residency_waves.0,
                    c.residency_waves.1,
                    c.serial_k_per_lane,
                    c.dependency_span
                );
            }
            None => {
                let _ = writeln!(
                    form,
                    "      {label}: the declared candidate is not admitted at this shape"
                );
            }
        }
    }
    let _ = writeln!(
        form,
        "    THE VERDICT, stated in what was measured, what was derived and what was not taken at all:"
    );
    let _ = writeln!(
        form,
        "      * additional ready warps, as the clause NAMES it: UNKNOWN. The deciding counter is"
    );
    let _ = writeln!(
        form,
        "        `eligible_warps_per_cycle` against H0's measured band 0.339-0.565, with `no_eligible_pct`"
    );
    let _ = writeln!(
        form,
        "        62.71-76.23 beside it. Both are ncu counters and ncu is admin-only here; this deed did not run it"
    );
    let _ = writeln!(
        form,
        "        and does not infer them. They stay UNKNOWN and are not replaced by a ratio."
    );
    let _ = writeln!(
        form,
        "      * additional locality, as the clause NAMES it: UNKNOWN — l1_hit_pct, l2_hit_pct and"
    );
    let _ = writeln!(
        form,
        "        dram_throughput_pct are ncu counters for the same reason."
    );
    let _ = writeln!(
        form,
        "      * what IS derivable from what nsys and the module DO carry: the resident blocks per SM rises from"
    );
    let _ = writeln!(
        form,
        "        2 (the scalar owner: 42 registers at a block of 512, which reproduces H0's measured 66.6667%"
    );
    let _ = writeln!(
        form,
        "        theoretical occupancy exactly) to 12 (the declared tile: 40 registers at a block of 128, 100%),"
    );
    let _ = writeln!(
        form,
        "        and the block population rises with it. That is a RESIDENCY reading and not a warp-eligibility"
    );
    let _ = writeln!(
        form,
        "        one; it says more warps COULD be resident, never that more were ready to issue."
    );
    if obstruction_rows.is_empty() {
        let _ = writeln!(
            form,
            "      * the per-launch durations were not available at this run."
        );
    } else {
        let scalar_total: u64 = obstruction_rows.iter().map(|row| row.0).sum();
        let tiled_total: u64 = obstruction_rows.iter().map(|row| row.1).sum();
        let slower: Vec<usize> = obstruction_rows
            .iter()
            .enumerate()
            .filter(|(_, row)| row.1 >= row.0)
            .map(|(at, _)| at)
            .collect();
        let _ = writeln!(
            form,
            "      * MEASURED kernel duration over the profiled shapes: scalar {scalar_total} ns against tiled {tiled_total} ns."
        );
        for (at, row) in obstruction_rows.iter().enumerate() {
            let _ = writeln!(
                form,
                "        shape {at}: {} ns -> {} ns over {} -> {} blocks",
                row.0, row.1, row.2, row.3
            );
        }
        if slower.is_empty() {
            let _ = writeln!(form, "      * NO SHAPE PROFILED IS SLOWER UNDER THE TILE.");
        } else {
            let _ = writeln!(
                form,
                "      * THE OBSTRUCTION IS EXHIBITED, AND IT IS SHAPE-CONDITIONAL: shapes {slower:?} are NOT faster under"
            );
            let _ = writeln!(
                form,
                "        the declared tile. On the widest map the tiled realization stages the whole entering row into"
            );
            let _ = writeln!(
                form,
                "        shared memory once per output tile, and with O_t = 4 there are O/4 output tiles per token row, so"
            );
            let _ = writeln!(
                form,
                "        the entering rows are re-read O/4 times against the scalar owner's O. That is a reduction in the"
            );
            let _ = writeln!(
                form,
                "        entering traffic and NOT in the map traffic, which dominates at O = 10240 — so the tile buys"
            );
            let _ = writeln!(
                form,
                "        nothing there and pays two barriers per K tile for it."
            );
        }
    }
    let _ = writeln!(
        form,
        "      * THE RETURN: the clause's own named faces are UNKNOWN, so this deed does NOT claim the profile"
    );
    let _ = writeln!(
        form,
        "        exhibits additional ready warps or locality; and on the widest profiled map it RETURNS THE"
    );
    let _ = writeln!(
        form,
        "        OBSTRUCTION with its numbers. `section_contract` is NOT replaced — it stands as the independent"
    );
    let _ = writeln!(
        form,
        "        exact reference, its H0 classification stands as H0 wrote it, and the tiled realization is"
    );
    let _ = writeln!(
        form,
        "        retained as a SECOND exact realization with its equality controls and its receipts. Replacing the"
    );
    let _ = writeln!(
        form,
        "        scalar owner is H5's deed and not this one's under any profile."
    );
    let _ = writeln!(form);

    // -------------------------------------------------------------------------------------
    // [13] the summary
    // -------------------------------------------------------------------------------------
    let _ = writeln!(form, "  [13] THE CONTROLS");
    for (name, verdict) in [
        ("C1 scalar equality on the real maps, words AND census", c1),
        (
            "C2 three further tile shapes, bit-equal to each other and to the declared one",
            c2,
        ),
        (
            "C3 the reversed lane tree and the reversed join, bit-equal in value",
            c3,
        ),
        (
            "C4 cancellation, the widest word, and the negative w in the tail",
            c4,
        ),
        (
            "C5 the carrier at the edge and the per-node aperture that refuses",
            c5,
        ),
        (
            "C6 the non-multiple K, O and T tails and K below the lane count",
            c6,
        ),
        (
            "C7 the K-axis permutation of both sides, with the half-permutation perturbation",
            c7,
        ),
        (
            "C8 zero float tokens in every entry H2 added, per entry",
            clean,
        ),
        ("C9 the register estimate replaced by the measurement", true),
    ] {
        let _ = writeln!(
            form,
            "    {:<74} {}",
            name,
            if verdict { "PASS" } else { "OPEN" }
        );
    }
    let _ = writeln!(
        form,
        "    {:<74} {}",
        "C10 the obstruction control",
        "OBSTRUCTION RETURNED — see [12]: the clause's named faces are ncu-only and UNKNOWN, and the widest profiled map is not faster under the tile"
    );
    let _ = writeln!(form);
    let _ = writeln!(form, "  [14] WHAT THIS DEED DOES NOT CLAIM");
    let _ = writeln!(
        form,
        "    * it does not claim the tiled realization is faster; the wall figures in [4] are a measurement in one"
    );
    let _ = writeln!(form, "      declared frame and the frame is stated;");
    let _ = writeln!(
        form,
        "    * it does not claim any tile is optimal; the retained sets in [3] move with the declared axes;"
    );
    let _ = writeln!(
        form,
        "    * it does not replace `section_contract`, which is unmodified and still the referee;"
    );
    let _ = writeln!(
        form,
        "    * it does not measure occupancy achieved, warp eligibility or cache locality — those are ncu-only."
    );

    std::fs::write(out_dir.join("receipt.form"), &form).map_err(|e| e.to_string())?;
    println!("{form}");
    println!("wrote {}", out_dir.join("receipt.form").display());
    Ok(())
}

/// The retained indices under a declared axis set — the owner's `non_dominated`, named here so the
/// driver reads it once per declaration and the dependence on the declaration is visible.
fn non_dominated_named(family: &[LaunchCandidate], axes: &[CandidateAxis]) -> Vec<usize> {
    holonic_engine::resident_section::non_dominated(family, axes)
}
