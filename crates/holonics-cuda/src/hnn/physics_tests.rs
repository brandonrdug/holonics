//! **Campaign 2's resident physics fixtures and the normal law's deposit on the card**: the
//! loaded constitution the port tests declare (`port_tests`; unpumped, since the certified step
//! refuses a linear deposit through a pumped resonator, whose growth is not certified), and the
//! prox deposit's parity with the host. The loaded resonator itself runs only inside the word kernels
//! (`hnn_word_forward`, `hnn_word_reverse`), whose parity tests cover its law; the standalone
//! resonator kernel was retired with its last consumer. The parity tests are `#[ignore]` and need
//! the card; run them alone:
//!
//! ```text
//! flock .local/gpu.lock cargo test --release -p holonics-cuda -- --include-ignored --test-threads=1
//! ```

use std::time::Instant;

use holonics::hnn::constitution::Constitution;
use holonics::hnn::field::Field;
use holonics::hnn::ring::ResonatorMaterial;
use holonics::ratio::{Rat, rat};

use super::tests::{Draw, card};

/// Campaign 1's field at the standing cut's population, each ring carrying its parametron's
/// resonator (unit weights, `d = 1/4`) unpumped: passive loaded material (`C, K, D ⪰ 0`), whose
/// growth the certified step reads as one.
pub(super) fn loaded(field: &Field) -> Constitution {
    let mut theta = Constitution::initial(field, 1 << 40).unwrap();
    for ring in 0..field.rings().len() {
        let material =
            ResonatorMaterial::of_parametron(field.ring(ring).parametron(), &rat(1, 4), None)
                .unwrap();
        theta = theta.with_ring_resonator(field, ring, material).unwrap();
    }
    theta
}

// -------------------------------------------------------------------------------------------
// the normal law's deposit on the card

use holonics::hnn::Lattice;
use holonics::hnn::constitution::{BudgetedCarry, ChartRule, NormalLaw, Sample, gamma_length};
use holonics::ratio::linear::ExactRatMatrix;
use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::lattice::{LatticeCoordinates, OuterSamples, ResidentLattice, SplitRecord};

/// A dyadic value `p / 2^e`, `p ∈ [−range, range]`.
fn dyadic(draw: &mut Draw, range: i64, exponent: u32) -> Rat {
    let p = (draw.next() % (2 * range as u64 + 1)) as i64 - range;
    Rat::new(BigInt::from(p), BigInt::one() << exponent as usize)
}

/// The coordinates of an array at a lattice (every entry on it), and of its remainders at the fine
/// lattice.
fn coordinates(values: &[Rat], exponent: u32) -> Vec<i64> {
    values
        .iter()
        .map(|v| {
            let scaled = v * Rat::from_integer(BigInt::one() << exponent as usize);
            assert!(scaled.is_integer(), "{v} off 2^-{exponent}");
            i64::try_from(scaled.to_integer()).unwrap()
        })
        .collect()
}

fn wide_coordinates(values: &[Rat], exponent: u32) -> Vec<i128> {
    values
        .iter()
        .map(|v| {
            let scaled = v * Rat::from_integer(BigInt::one() << exponent as usize);
            assert!(scaled.is_integer(), "{v} off 2^-{exponent}");
            i128::try_from(scaled.to_integer()).unwrap()
        })
        .collect()
}

/// The split's entries and remainders as exact values.
fn split_values(split: &SplitRecord, lattice: u32, fine: u32) -> (Vec<Rat>, Vec<Rat>) {
    assert!(split.status.iter().all(|&s| s == 0), "a refused entry");
    (
        split
            .entries
            .iter()
            .map(|&x| Rat::new(BigInt::from(x), BigInt::one() << lattice as usize))
            .collect(),
        split
            .remainders
            .iter()
            .map(|&r| Rat::new(BigInt::from(r), BigInt::one() << fine as usize))
            .collect(),
    )
}

/// **The normal law's prox step on the card equals the host's** (campaign 2, the hardware-surfaces rule: the deposit
/// phase on the card where its arithmetic is dyadic). A window of dyadic samples `(w, f, g)` is
/// deposited on a normal law by the host (`NormalLaw::deposited`: `ΔH = Σ w f fᵀ` carried onto `H`,
/// the chart of `H'`, `ΔW = γ Σ w g (X̂f)ᵀ` carried onto `W`, each by the budgeted carry at the deposit
/// clock's precision) and on the card (`hnn_outer_update` for both sums, `hnn_budgeted_split` for both
/// carries; the chart is the host's successor chart, and the reaches `X̂f` its exact products): the
/// successor's `H'`, `W'` and both carried remainders are equal, and the times are reported. The
/// third window deposits on a receiving map's scaled prior `H_0 = 2I`
/// (`NormalLaw::with_scaled_prior`) with features that reach only the first half of the
/// coordinates, so the Gram is `2` and the host's chart `½` on the diagonal off the support, read
/// on the card as they stand.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_prox_deposit_on_the_card_equals_the_host_and_is_measured() {
    let card = card();
    for (m, n, samples, scale, reached) in [
        (10usize, 64usize, 32usize, 0u32, 64usize),
        (10, 256, 64, 0, 256),
        (10, 64, 8, 1, 32),
    ] {
        let mut draw = Draw(9 + n as u64);
        let exponent = 9;
        let lattice = Lattice::new(exponent);
        let prior = ExactRatMatrix::shaped(
            m,
            n,
            (0..m)
                .map(|_| (0..n).map(|_| dyadic(&mut draw, 2, 1)).collect())
                .collect(),
        )
        .unwrap();
        let law = NormalLaw::with_scaled_prior(prior, scale);
        let window: Vec<Sample> = (0..samples)
            .map(|_| Sample {
                weight: Rat::one(),
                feature: (0..n)
                    .map(|j| {
                        if j < reached {
                            dyadic(&mut draw, 3, 6)
                        } else {
                            Rat::zero()
                        }
                    })
                    .collect(),
                covector: (0..m).map(|_| dyadic(&mut draw, 5, 8)).collect(),
                masses: None,
            })
            .collect();
        let proxy = Rat::one();
        let rule = ChartRule::new(lattice, 16);
        let clock = 1u64;
        let precision = gamma_length(clock);
        let fine = exponent + precision;

        let started = Instant::now();
        let mut at = BudgetedCarry::new(lattice, clock);
        let (next, _) = law.deposited(&window, &proxy, &rule, &mut at).unwrap();
        let host_us = started.elapsed().as_micros();

        // The card: ΔH and its carry. The samples' and arrays' coordinates are formed on the host
        // (timed apart), the card's part is its uploads, launches and reads.
        let started = Instant::now();
        let weights: Vec<Rat> = window.iter().map(|s| s.weight.clone()).collect();
        let features: Vec<Vec<Rat>> = window.iter().map(|s| s.feature.clone()).collect();
        let gram_samples = OuterSamples::of(&weights, &features, &features, n, n, fine).unwrap();
        let (gram_words, gram_rest) = (
            coordinates(law.gram().entries(), exponent),
            wide_coordinates(law.gram_remainder().entries(), fine),
        );
        let mut convert_us = started.elapsed().as_micros();
        let started = Instant::now();
        let gram_update = card.outer_update(&gram_samples).unwrap();
        let gram_split = card
            .budgeted_split(&gram_update, lattice, precision, &gram_words, &gram_rest)
            .unwrap();
        let card_gram_us = started.elapsed().as_micros();
        let (gram, gram_remainder) = split_values(&gram_split, exponent, fine);
        assert_eq!(
            gram,
            next.gram().entries().to_vec(),
            "H' ({m} × {n}, {samples})"
        );
        assert_eq!(gram_remainder, next.gram_remainder().entries().to_vec());

        // The reaches X̂f at the host's successor chart, read on the card (`hnn_lattice_read`: the
        // chart as the locus on `2^(−L_s)ℤ`, the features as its operand), and ΔW with its carry.
        let chart = next.solved();
        let off = Rat::new(BigInt::one(), BigInt::one() << scale as usize);
        for i in reached..n {
            assert_eq!(chart.get(i, i).unwrap(), &off, "the chart off the support at {i}");
        }
        let chart_lattice = Lattice::new(next.chart().exponent());
        let feature_lattice = Lattice::new(6);
        let started = Instant::now();
        let chart_locus = ResidentLattice::mount(
            &card,
            &LatticeCoordinates::of_matrix(&chart, chart_lattice).unwrap(),
        )
        .unwrap();
        let feature_operand = ResidentLattice::mount(
            &card,
            &LatticeCoordinates::of_vectors(&features, feature_lattice).unwrap(),
        )
        .unwrap();
        let read = card
            .read(&chart_locus, feature_operand.operand(), None)
            .unwrap()
            .fetch()
            .unwrap();
        let reaches: Vec<Vec<Rat>> = (0..samples).map(|t| read.vector(t)).collect();
        let reach_us = started.elapsed().as_micros();
        for (reach, feature) in reaches.iter().zip(&features).take(2) {
            assert_eq!(reach, &chart.apply(feature).unwrap());
        }
        let started = Instant::now();
        let covectors: Vec<Vec<Rat>> = window.iter().map(|s| s.covector.clone()).collect();
        let scaled: Vec<Rat> = weights.iter().map(|w| w * &proxy).collect();
        let map_samples = OuterSamples::of(&scaled, &covectors, &reaches, m, n, fine).unwrap();
        let (map_words, map_rest) = (
            coordinates(law.map().entries(), exponent),
            wide_coordinates(law.map_remainder().entries(), fine),
        );
        convert_us += started.elapsed().as_micros();
        let started = Instant::now();
        let map_update = card.outer_update(&map_samples).unwrap();
        let map_split = card
            .budgeted_split(&map_update, lattice, precision, &map_words, &map_rest)
            .unwrap();
        let card_map_us = started.elapsed().as_micros();
        let (map, map_remainder) = split_values(&map_split, exponent, fine);
        assert_eq!(
            map,
            next.map().entries().to_vec(),
            "W' ({m} × {n}, {samples})"
        );
        assert_eq!(map_remainder, next.map_remainder().entries().to_vec());
        // The released residuals: e·2^(−S), the host's staged at the same entries.
        let released = at.released();
        let released_count = gram_split.released.iter().filter(|e| **e != 0).count()
            + map_split.released.iter().filter(|e| **e != 0).count();
        assert_eq!(released.len(), released_count);
        eprintln!(
            "prox deposit {m} × {n}, {samples} samples (update scales 2^-{} and 2^-{}): host \
             NormalLaw::deposited {host_us} µs (chart refinement included); card ΔH + carry \
             {card_gram_us} µs, ΔW + carry {card_map_us} µs (uploads, launches, reads); host \
             coordinates {convert_us} µs; card reaches X̂f {reach_us} µs (mount, read, fetch)",
            gram_samples.exponent(),
            map_samples.exponent()
        );
    }
}
