//! **How much dimension a trained circuit actually carries — exactly, over integers.**
//!
//! Brandon, 2026-08-18: *"Quantisation is not a problem in holonics, because I am pretty sure that
//! instead of linearly scaling floating point representations, you could just alter the dimensions
//! of layers and heads, and it would encode the same performance while still compressing… We don't
//! respect floats, but we'll reverse engineer them so they go away and we can work with pure
//! integers again."*
//!
//! That thesis is checkable and this checks it. **Quantisation shrinks the precision of each entry
//! and keeps the shape; the alternative shrinks the shape and keeps every entry exact.** The second
//! is only available if the trained circuits are actually rank-deficient, and rank is not a
//! well-posed question in floating point — an SVD returns a spectrum and a human picks a cutoff.
//!
//! Over integers it is exact. `align_bfloat16` returns a real Gemma circuit as an **integer matrix
//! times one shared power of two, with zero remainder**, and the rank of an integer matrix is a
//! definite number.
//!
//! **The rank is taken modulo a declared prime, and the prime is a declared receiver.** Rank over
//! `F_p` is a lower bound for the rank over `Q` and equals it for all but finitely many primes, so
//! two primes agreeing is a two-frame reading rather than one measurement. Where they disagree the
//! smaller is a receiver that cannot see a factor, and that is reported rather than averaged.

use std::collections::BTreeMap;

use holonic_engine::embedding_fiber::{align_bfloat16, safetensors};

const MAP: &str = "/home/b/models/gemma-4-E4B-it/model.safetensors";

/// Declared receivers. Two large primes: agreement is the two-frame reading.
const PRIMES: [i128; 2] = [2_147_483_647, 2_147_483_629];

/// The circuits read, each as `(name, rows, columns, head width)`. A head width of zero means the
/// whole block is one circuit.
fn circuits() -> Vec<(String, usize)> {
    let mut held = Vec::new();
    for layer in 0..42 {
        for circuit in ["q_proj", "k_proj", "v_proj"] {
            held.push((
                format!("model.language_model.layers.{layer}.self_attn.{circuit}.weight"),
                256,
            ));
        }
        held.push((
            format!("model.language_model.layers.{layer}.per_layer_input_gate.weight"),
            256,
        ));
    }
    held
}

fn main() {
    if let Err(reason) = run() {
        eprintln!("REFUSED: {reason}");
        std::process::exit(1);
    }
}

/// Rank over `F_p` by Gaussian elimination. Exact: every operation is integer arithmetic modulo a
/// declared prime and no tolerance appears anywhere.
fn rank_mod(rows: &[Vec<i128>], prime: i128) -> usize {
    let mut matrix: Vec<Vec<i128>> = rows
        .iter()
        .map(|row| row.iter().map(|entry| entry.rem_euclid(prime)).collect())
        .collect();
    let height = matrix.len();
    let width = matrix.first().map_or(0, Vec::len);
    let mut rank = 0usize;
    let mut column = 0usize;
    while rank < height && column < width {
        let Some(pivot) = (rank..height).find(|row| matrix[*row][column] != 0) else {
            column += 1;
            continue;
        };
        matrix.swap(rank, pivot);
        let inverse = mod_inverse(matrix[rank][column], prime);
        for at in column..width {
            matrix[rank][at] = matrix[rank][at] * inverse % prime;
        }
        for row in 0..height {
            if row == rank || matrix[row][column] == 0 {
                continue;
            }
            let factor = matrix[row][column];
            for at in column..width {
                matrix[row][at] = (matrix[row][at] - factor * matrix[rank][at]).rem_euclid(prime);
            }
        }
        rank += 1;
        column += 1;
    }
    rank
}

fn mod_inverse(value: i128, prime: i128) -> i128 {
    let mut result = 1i128;
    let mut base = value.rem_euclid(prime);
    let mut exponent = prime - 2;
    while exponent > 0 {
        if exponent & 1 == 1 {
            result = result * base % prime;
        }
        base = base * base % prime;
        exponent >>= 1;
    }
    result
}

fn run() -> Result<(), String> {
    let (mut file, header) = safetensors::read_header(MAP)?;
    println!("EXACT RANK OF TRAINED CIRCUITS — integers, no tolerance, no cutoff\n");
    println!(
        "  {:<52} {:>10} {:>8} {:>8}  {}",
        "circuit", "shape", "rank", "deficit", "frames"
    );

    let mut totals: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    for (name, head) in circuits() {
        let name = name.as_str();
        let entry = header.entry(name)?;
        let rows_declared = entry.shape[0];
        let width = entry.shape[1];
        let take = if head == 0 { rows_declared } else { head };
        let (words, returned) = safetensors::read_rows(&mut file, &header, name, 0, take)?;
        if returned != width {
            return Err(format!("{name}: intake returned width {returned}"));
        }

        // The dyadic mouth: a real trained circuit as EXACT INTEGERS over one shared power of two,
        // with zero remainder. The floats are gone before any arithmetic happens.
        let aligned = match align_bfloat16(&words) {
            Ok(aligned) => aligned,
            Err(error) => {
                println!("  {name:<52} MOUTH REFUSED: {error}");
                continue;
            }
        };
        let matrix: Vec<Vec<i128>> = aligned
            .entries
            .chunks_exact(width)
            .map(|row| row.iter().map(|entry| i128::from(*entry)).collect())
            .collect();

        let bound = take.min(width);
        let mut ranks = Vec::new();
        for prime in PRIMES {
            ranks.push(rank_mod(&matrix, prime));
        }
        let rank = ranks.iter().copied().max().unwrap_or(0);
        let agree = ranks.iter().all(|held| *held == rank);
        let short = name.trim_start_matches("model.language_model.");
        println!(
            "  {:<52} {:>4}x{:<5} {:>8} {:>8}  {}",
            short,
            take,
            width,
            rank,
            bound - rank,
            if agree { "agree" } else { "DISAGREE" }
        );
        totals.insert(name.to_owned(), (rank, bound));
    }

    println!();
    println!("THE READING");
    let full: Vec<&String> = totals
        .iter()
        .filter(|(_, (rank, bound))| rank == bound)
        .map(|(name, _)| name)
        .collect();
    let deficient: Vec<(&String, usize)> = totals
        .iter()
        .filter(|(_, (rank, bound))| rank != bound)
        .map(|(name, (rank, bound))| (name, bound - rank))
        .collect();
    println!(
        "  {} of {} circuits are FULL RANK for their own shape.",
        full.len(),
        totals.len()
    );
    for (name, deficit) in &deficient {
        println!("  DEFICIT {deficit:>4}  {}", name.trim_start_matches("model.language_model."));
    }
    println!("  A full-rank circuit carries every dimension it declares: there is no free");
    println!("  low-rank factorisation of it, and shrinking its shape WOULD lose something exact.");
    println!("  A rank-deficient one carries less than it declares, and the deficit is dimension");
    println!("  that can be removed with a NAMED cokernel rather than a rounding error.");
    println!();
    println!("  This is the honest test of dimension-instead-of-precision, and it is a measurement");
    println!("  about THESE circuits, not a claim about the thesis in general. Where the rank is");
    println!("  full the compression must come from somewhere else — from the material's own");
    println!("  structure rather than from the trained matrix's redundancy.");
    Ok(())
}
