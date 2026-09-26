//! **Campaign 2's resident ring physics** (`holonics::hnn::ring`, kernel `hnn_resonator_word`): the
//! word's resonators on the card equal the host's executed resonator ticks coordinate for
//! coordinate, and each phase is timed on the host and the card. The parity tests are `#[ignore]`
//! and need the card; run them alone:
//!
//! ```text
//! flock .local/gpu.lock cargo test --release -p holonics-cuda -- --include-ignored --test-threads=1
//! ```

use std::time::Instant;

use holonics::hnn::constitution::{Constitution, Steps};
use holonics::hnn::field::{Current, Field, FieldDeclaration};
use holonics::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial, ResonatorOperands};
use holonics::hnn::{ReceivingPhases, SourceMoment, Word};
use holonics::holon::parametron::Carrier;
use holonics::ratio::{Rat, rat};
use num_traits::Zero;

use super::card::{Realization, resonator_layout};
use super::tests::{Draw, card, census, entry};
use super::word::{RESONATOR_ENTRY, ResonatorPlan};

/// Campaign 1's field at the standing cut's population, each ring carrying its parametron's
/// resonator (unit weights, `d = 1/4`) with a half-turn pump of strength `1/8` on the axis `1`: dyadic
/// material, certified at both pump phases (`2C + D + ½K_j ⪰ 0` since `d ≥ p`).
fn resonant(field: &Field) -> Constitution {
    let mut theta = Constitution::initial(field, Steps::campaign_one(), 1 << 40).unwrap();
    for ring in 0..field.rings().len() {
        let pump = PumpDeclaration::new(
            rat(1, 8),
            Carrier::new(Rat::from_integer(1.into()), Rat::zero()).unwrap(),
            PumpStep::Half,
        )
        .unwrap();
        let material =
            ResonatorMaterial::of_parametron(field.ring(ring).parametron(), &rat(1, 4), Some(pump))
                .unwrap();
        theta = theta.with_ring_resonator(field, ring, material).unwrap();
    }
    theta
}

/// The resonators' layout: one block per resonator, one thread per row, the ticks serial.
#[test]
fn the_resonator_layout_is_one_block_per_ring_and_one_thread_per_row() {
    let census = census();
    let layout = resonator_layout(&census, &entry(RESONATOR_ENTRY, 1024, 0), 4, 26).unwrap();
    assert_eq!(layout.grid.x, 4);
    assert_eq!(layout.block.x, 32);
    assert_eq!(
        layout.realization,
        Realization::RingPerBlock {
            rings: 4,
            threads: 32,
            columns: 26
        }
    );
    assert!(resonator_layout(&census, &entry(RESONATOR_ENTRY, 16, 0), 4, 26).is_err());
}

/// **The resident resonators equal the host's word, tick for tick** (campaign 2, Decision 25): on
/// campaign 1's field with a resonator on every ring, the card's `(u, w, ω)` at every tick and the
/// carried solve remainders at the word's end equal the host word's executed resonator ticks
/// (`holonics::hnn::ring::ResonatorOperands::step` inside `Word::tick`), driven by the storage waves
/// the host word's junctions sent. The host's and the card's times are reported.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn resident_resonators_equal_the_host_word_and_are_measured() {
    let card = card();
    let field = Field::declare(FieldDeclaration::campaign_one(6148)).unwrap();
    let theta = resonant(&field);
    let mut draw = Draw(1_077);
    let cells: Vec<usize> = (0..2_048).map(|_| draw.below(256)).collect();
    let mut current = Current::at_rest(&field);
    let mut moment = SourceMoment::open(&field, &current);
    moment.ingest(&field, &mut current, &cells).unwrap();
    let phases = ReceivingPhases::declare(&field, &theta, &current, &field.receivers()[0]).unwrap();

    let clock = Instant::now();
    let mut word = Word::open(&field, &theta, &current, &moment).unwrap();
    word.forward(&phases).unwrap();
    let host_word_us = clock.elapsed().as_micros();
    let ticks = word.balances().len();
    assert!(word.field_balances().iter().all(|balance| balance.closes()));

    let resonators: Vec<&ResonatorOperands> =
        word.operands().resonators().iter().flatten().collect();
    let rings: Vec<usize> = resonators.iter().map(|r| r.ring()).collect();
    let drives: Vec<Vec<Vec<Rat>>> = (0..ticks)
        .map(|t| {
            let waves = word.storage_waves(t).unwrap();
            rings.iter().map(|&ring| waves[ring].clone()).collect()
        })
        .collect();
    let transient = field.word_lattice().unwrap().transient().exponent();
    let plan = ResonatorPlan::form(&resonators, transient).unwrap();

    // The host's resonator ticks alone, from the same drives.
    let lattice = field.word_lattice().unwrap().transient();
    let clock = Instant::now();
    for (k, resonator) in resonators.iter().enumerate() {
        let n = resonator.width();
        let mut state = [vec![Rat::zero(); n], vec![Rat::zero(); n]];
        let mut remainders = Default::default();
        for (t, tick) in drives.iter().enumerate() {
            let step = resonator
                .step(
                    t,
                    &tick[k],
                    [&state[0], &state[1]],
                    &remainders,
                    Some(&lattice),
                )
                .unwrap();
            state = step.state.clone();
            remainders = step.remainders().clone();
        }
    }
    let host_resonator_us = clock.elapsed().as_micros();

    // The card: a first word (its buffers allocated), then repeated words.
    let clock = Instant::now();
    let record = card.resonator_word(&plan, &drives).unwrap();
    let first_us = clock.elapsed().as_micros();
    const REPEATS: u32 = 16;
    let clock = Instant::now();
    for _ in 0..REPEATS {
        card.resonator_word(&plan, &drives).unwrap();
    }
    let card_us = clock.elapsed().as_micros() / u128::from(REPEATS);

    for (k, &ring) in rings.iter().enumerate() {
        let resonance = word.resonances()[ring].as_ref().unwrap();
        assert_eq!(resonance.steps.len(), ticks);
        for (t, step) in resonance.steps.iter().enumerate() {
            let (state, omega) = record.state(&plan, k, t).unwrap();
            assert_eq!(state, step.state, "ring {ring}, tick {t}");
            assert_eq!(omega, step.rate, "ring {ring}, tick {t}");
        }
        assert_eq!(
            record.remainders(&plan, k),
            resonance.remainders.rate,
            "ring {ring}'s carried solve remainders"
        );
    }
    let layout = resonator_layout(
        card.census(),
        &card.entry(RESONATOR_ENTRY).unwrap(),
        plan.widths().len(),
        plan.widths().iter().copied().max().unwrap(),
    )
    .unwrap();
    eprintln!("resonator layout: {:?}", layout.realization);
    eprintln!(
        "resonators {:?} widths {:?}, {} ticks, exponents (e_h, L_m, L_c, L_w) {:?}",
        plan.rings(),
        plan.widths(),
        ticks,
        plan.exponents()
    );
    eprintln!(
        "times (µs): host word with resonators {host_word_us}; host resonator ticks \
         {host_resonator_us}; card resonator word first {first_us}, then {card_us} a word \
         (upload, one launch, one read)"
    );
}

// -------------------------------------------------------------------------------------------
// the normal law's deposit on the card

use holonics::hnn::Lattice;
use holonics::hnn::constitution::{BudgetedCarry, ChartRule, NormalLaw, Sample, gamma_length};
use holonics::ratio::linear::ExactRatMatrix;
use num_bigint::BigInt;
use num_traits::One;

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

/// **The normal law's prox step on the card equals the host's** (campaign 2, Decision 25: the deposit
/// phase on the card where its arithmetic is dyadic). A window of dyadic samples `(w, f, g)` is
/// deposited on a normal law by the host (`NormalLaw::deposited`: `ΔH = Σ w f fᵀ` carried onto `H`,
/// the chart of `H'`, `ΔW = γ Σ w g (X̂f)ᵀ` carried onto `W`, each by the budgeted carry at the deposit
/// clock's precision) and on the card (`hnn_outer_update` for both sums, `hnn_budgeted_split` for both
/// carries; the chart is the host's successor chart, and the reaches `X̂f` its exact products): the
/// successor's `H'`, `W'` and both carried remainders are equal, and the times are reported.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn the_prox_deposit_on_the_card_equals_the_host_and_is_measured() {
    let card = card();
    for (m, n, samples) in [(10usize, 64usize, 32usize), (10, 256, 64)] {
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
        let law = NormalLaw::with_prior(prior);
        let window: Vec<Sample> = (0..samples)
            .map(|_| Sample {
                weight: Rat::one(),
                feature: (0..n).map(|_| dyadic(&mut draw, 3, 6)).collect(),
                covector: (0..m).map(|_| dyadic(&mut draw, 5, 8)).collect(),
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
