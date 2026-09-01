//! **STATION ONE — the Hankel rank, which is the width an Athena container can have.**
//!
//! For a linear representation of a weighted automaton — vectors `u`, `v`, per-germ matrices `A_a`,
//! with `f(a₁…a_n) = uᵀ A_{a₁}…A_{a_n} v` — **the minimal dimension is exactly the rank of the
//! Hankel matrix** `H[x, y] = f(xy)`. Fliess–Kalman realization theory: nothing smaller is exact and
//! one of that size always exists. So this number is not an estimate and not a cutoff; it is *the*
//! width, and Athena's file size is `rows × width × 2`.
//!
//! `f` here is the **occurrence count**, which the atlas already carries: the folded multiplicity of
//! the class a word lands in is `|endpos|`, the number of times that word occurs. So every entry of
//! `H` is one walk, and the whole matrix is exact integers with no model in between.
//!
//! **The rank is taken modulo declared primes.** Rank over `F_p` is a lower bound for the rank over
//! `Q` and equals it for all but finitely many `p`, so two primes agreeing is a two-frame reading.
//!
//! **The vacuity arm is the point of the sweep.** A small aperture is trivially low rank, and a rank
//! that tracks the aperture measures the aperture rather than the material. What decides the design
//! is whether the rank **saturates** as the block grows.
//!
//! ```text
//!   cargo run --release -p life --example the_hankel_rank_is_the_width_athena_can_have
//! ```

use std::collections::BTreeSet;

use body::num::Cog;
use life::causal_language::{
    lexical_tokens, token_germs_public, CausalLanguageEcology, CausalLanguagePassage,
};
use life::suffix_ecology::ExactSuffixEcology;
use soma_abi::active::ActionCurrent;

const MATERIAL: &[(&str, u64)] = &[
    ("canon/THE_DOCUMENT_LAW.md", 1),
    ("canon/TABLET_THE_OPERATIONS.md", 2),
    ("canon/THE_RECOVERED_LAW.md", 3),
    ("canon/TABLET_THE_COMPRESSION.md", 4),
];

/// Declared receivers. Agreement across both is the two-frame reading.
const PRIMES: [u64; 2] = [2_147_483_647, 2_147_483_629];

/// The apertures swept. What each excludes is reported, never dropped.
const APERTURES: [usize; 6] = [64, 128, 256, 512, 1024, 2048];

fn main() {
    if let Err(reason) = run() {
        eprintln!("REFUSED: {reason}");
        std::process::exit(1);
    }
}

fn current() -> Result<ActionCurrent, String> {
    ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "the action current is dark".to_owned())
}

/// `f(w)` — how many times `w` occurs in the material, read off the atlas in one walk.
fn occurrences(atlas: &ExactSuffixEcology, word: &[String]) -> u64 {
    let Ok(germs) = token_germs_public(word) else {
        return 0;
    };
    let Ok(current) = atlas.receive_path(&germs) else {
        return 0;
    };
    // A walk that arced lost context, so the whole word does not occur.
    if current.matched_length() as usize != word.len() {
        return 0;
    }
    atlas.standing_at(current.state()).unwrap_or(0)
}

/// Rank over `F_p` by Gaussian elimination on a flat row-major block. Exact throughout.
fn rank_mod(block: &[u64], height: usize, width: usize, prime: u64) -> usize {
    let mut matrix: Vec<u64> = block.iter().map(|entry| entry % prime).collect();
    let mut rank = 0usize;
    let mut column = 0usize;
    while rank < height && column < width {
        let Some(pivot) = (rank..height).find(|row| matrix[row * width + column] != 0) else {
            column += 1;
            continue;
        };
        if pivot != rank {
            for at in column..width {
                matrix.swap(rank * width + at, pivot * width + at);
            }
        }
        let inverse = mod_inverse(matrix[rank * width + column], prime);
        for at in column..width {
            let cell = matrix[rank * width + at];
            matrix[rank * width + at] =
                (u128::from(cell) * u128::from(inverse) % u128::from(prime)) as u64;
        }
        for row in 0..height {
            if row == rank {
                continue;
            }
            let factor = matrix[row * width + column];
            if factor == 0 {
                continue;
            }
            for at in column..width {
                let take =
                    u128::from(factor) * u128::from(matrix[rank * width + at]) % u128::from(prime);
                let held = u128::from(matrix[row * width + at]);
                matrix[row * width + at] =
                    ((held + u128::from(prime) - take) % u128::from(prime)) as u64;
            }
        }
        rank += 1;
        column += 1;
    }
    rank
}

fn mod_inverse(value: u64, prime: u64) -> u64 {
    let mut result: u128 = 1;
    let mut base = u128::from(value % prime);
    let mut exponent = prime - 2;
    let modulus = u128::from(prime);
    while exponent > 0 {
        if exponent & 1 == 1 {
            result = result * base % modulus;
        }
        base = base * base % modulus;
        exponent >>= 1;
    }
    result as u64
}

fn run() -> Result<(), String> {
    let mut passages = Vec::new();
    let mut stream: Vec<String> = Vec::new();
    for (path, receiver) in MATERIAL {
        let text = std::fs::read_to_string(path).map_err(|error| format!("{path}: {error}"))?;
        stream.extend(lexical_tokens(&text));
        passages.push(CausalLanguagePassage::new(*path, *receiver, text));
    }
    let ecology = CausalLanguageEcology::condition(&passages, current()?, 8)
        .map_err(|error| format!("conditioning refused: {error:?}"))?;
    let atlas = ecology.global_suffix();

    // Words that occur: every unigram, and every bigram the stream actually carries. Both sides of
    // the Hankel range over words, so a one-symbol block would be a bigram table rather than a
    // Hankel and its rank would answer a different question.
    let unigrams: BTreeSet<Vec<String>> = stream.iter().map(|token| vec![token.clone()]).collect();
    let bigrams: BTreeSet<Vec<String>> = stream.windows(2).map(|pair| pair.to_vec()).collect();
    let mut words: Vec<Vec<String>> = unigrams.iter().cloned().collect();
    words.extend(bigrams.iter().cloned());

    println!("THE MATERIAL");
    println!("  classes                {}", atlas.state_count());
    println!(
        "  germ transitions       {}",
        atlas.material_transition_count()
    );
    println!(
        "  occurrences            {}",
        atlas.material_occurrence_count()
    );
    println!("  distinct unigrams      {}", unigrams.len());
    println!("  distinct bigrams       {}", bigrams.len());
    println!("  Hankel word population {}", words.len());
    println!();

    // TWO FRAMES on the aperture itself. Canonical order is the corpus's own ordering and carries
    // no ranking; standing order takes the most-supported words first. If the rank differs between
    // them, the aperture is choosing the answer and the sweep says so.
    let mut canonical = words.clone();
    canonical.sort();
    let mut by_standing = words.clone();
    by_standing.sort_by_key(|word| (std::cmp::Reverse(occurrences(atlas, word)), word.clone()));

    for (frame, ordered) in [("canonical", &canonical), ("by standing", &by_standing)] {
        println!("APERTURE SWEEP — {frame} order");
        println!(
            "  {:>7} {:>9} {:>9} {:>9} {:>9}  {}",
            "block", "entries", "nonzero", "rank", "deficit", "frames"
        );
        let mut previous: Option<usize> = None;
        for aperture in APERTURES {
            if aperture > ordered.len() {
                println!(
                    "  {aperture:>7}  excluded: the word population is only {}",
                    ordered.len()
                );
                break;
            }
            let contexts = &ordered[..aperture];
            let continuations = &ordered[..aperture];
            let mut block = vec![0u64; aperture * aperture];
            let mut nonzero = 0usize;
            for (row, context) in contexts.iter().enumerate() {
                for (column, continuation) in continuations.iter().enumerate() {
                    let mut word = context.clone();
                    word.extend(continuation.iter().cloned());
                    let count = occurrences(atlas, &word);
                    if count != 0 {
                        nonzero += 1;
                    }
                    block[row * aperture + column] = count;
                }
            }
            let ranks: Vec<usize> = PRIMES
                .iter()
                .map(|prime| rank_mod(&block, aperture, aperture, *prime))
                .collect();
            let rank = ranks.iter().copied().max().unwrap_or(0);
            let agree = ranks.iter().all(|held| *held == rank);
            println!(
                "  {aperture:>7} {:>9} {nonzero:>9} {rank:>9} {:>9}  {}",
                aperture * aperture,
                aperture - rank,
                if agree { "agree" } else { "DISAGREE" }
            );
            if previous == Some(rank) {
                println!("           the rank did not move with the aperture — it has SATURATED");
            }
            previous = Some(rank);
        }
        println!();
    }

    println!("HOW TO READ THIS");
    println!("  The rank is the minimal exact dimension of a linear representation, by");
    println!("  Fliess-Kalman. If it tracks the aperture, the block is measuring the aperture and");
    println!("  the material's own rank is above what was swept. If it SATURATES, that value is");
    println!("  the width an Athena container can have and the file size follows from it.");
    println!(
        "  A rank near the class count ({}) refutes the linear-representation route",
        atlas.state_count()
    );
    println!("  for the transport half, and that is a real negative rather than a tuning failure.");
    Ok(())
}
