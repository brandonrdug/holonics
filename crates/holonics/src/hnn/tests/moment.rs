//! The source moment: the capacity by counting, the phase-binned counts against their clocked
//! closed form, the encoder contract and its tape-free covector, the window, and the carry-out.

use num_bigint::{BigInt, BigUint};
use num_traits::Zero;

use super::learning::chain;
use super::support::{Draw, Medium, Parts, contact, small_field};
use crate::hnn::field::{ConstitutionRead, Current, Field};
use crate::hnn::moment::{SourceMoment, capacity};
use crate::ratio::Rat;
use crate::ratio::linear::vector::{add, dot};

/// Lean `HNN/Moment.moment_capacity` on the three-ring control (periods 3, 4, 5, `|A| = 2`, every
/// ring a source, no offsets): `n* = 137`, and `log₂N(n)` per source bit is at least 1 below it and
/// below 1 past it, at every `n` from 2 to 4,096 (R3 H1).
#[test]
fn the_capacity_is_the_least_lossy_population_by_counting() {
    let control = capacity(&[3, 4, 5], &[0, 1, 2], 2, &[]).unwrap();
    assert_eq!(control.n_star(), 137);
    for n in 2..=4096u64 {
        let bound = BigUint::from(2u32).pow(n as u32);
        assert_eq!(control.states(n) < bound, n >= 137, "n = {n}");
    }
}

/// Campaign 1's declared source state (periods 5, 7, 11, 13; source ring 0; bytes; `Δ = {1}`),
/// counted without declaring the field: `n* = 6,148`, certified by exact integers at `n* − 1` and
/// `n*`.
#[test]
fn campaign_one_capacity_is_certified_at_its_crossover() {
    let capacity = capacity(&[5, 7, 11, 13], &[0], 256, &[1]).unwrap();
    assert_eq!(capacity.n_star(), 6_148);
    assert!(!capacity.lossy_at(6_147));
    assert!(capacity.lossy_at(6_148));
}

/// The clocked closed form of selective stepping, computed independently: ring `g`'s lift after
/// cell `k` is its opening lift plus its lock steps plus its predecessor's wraps on cells `0 … k`.
fn closed_form_lifts(field: &Field, opening: &[BigInt], cells: &[usize]) -> Vec<Vec<BigInt>> {
    let rings = field.rings().len();
    let mut per_ring: Vec<Vec<BigInt>> = Vec::with_capacity(rings);
    for g in 0..rings {
        let ring = field.ring(g);
        let d = BigInt::from(ring.period());
        let mut lifts = Vec::with_capacity(cells.len());
        let mut lock_steps = 0i64;
        let mut carries = 0i64;
        for (k, &code) in cells.iter().enumerate() {
            lock_steps += i64::from(ring.fits(ring.port(code)));
            if g > 0 {
                let before: &BigInt = if k == 0 {
                    &opening[g - 1]
                } else {
                    &per_ring[g - 1][k - 1]
                };
                let after = &per_ring[g - 1][k];
                let wraps = after / BigInt::from(field.ring(g - 1).period())
                    - before / BigInt::from(field.ring(g - 1).period());
                carries += i64::try_from(wraps).unwrap();
            }
            let _ = &d;
            lifts.push(&opening[g] + lock_steps + carries);
        }
        per_ring.push(lifts);
    }
    (0..cells.len())
        .map(|k| (0..rings).map(|g| per_ring[g][k].clone()).collect())
        .collect()
}

/// Lean `HNN/Moment.{closingRing_moment_is_phaseBinned, selective_position}`: per-cell ingest
/// equals the clocked closed form, bin by bin, and the lift point it reaches.
#[test]
fn per_cell_ingest_equals_the_clocked_closed_form() {
    let field = &chain();
    let (a, d) = (field.alphabet(), field.ring(0).period() as usize);
    let mut draw = Draw::new(21);
    let cells: Vec<usize> = (0..400).map(|_| draw.below(a)).collect();
    let opening = Current::at(field, vec![1.into(), 2.into(), 1.into()]).unwrap();
    let mut current = opening.clone();
    let mut moment = SourceMoment::open(field, &current);
    // The moment keeps counting across the joint clock's carry-outs.
    let mut fed = 0;
    while fed < cells.len() {
        fed += moment
            .ingest(field, &mut current, &cells[fed..])
            .unwrap()
            .cells;
    }
    let lifts = closed_form_lifts(field, opening.lift(), &cells);
    assert_eq!(current.lift(), &lifts[399][..]);
    let mut expected = vec![vec![0u64; a]; d];
    let mut offset = vec![vec![0u64; a * a]; d];
    for (k, &code) in cells.iter().enumerate() {
        let phase = (&lifts[k][0] % BigInt::from(d))
            .to_string()
            .parse::<usize>()
            .unwrap();
        expected[phase][code] += 1;
        if k > 0 {
            offset[phase][code * a + cells[k - 1]] += 1;
        }
    }
    for phase in 0..d {
        assert_eq!(moment.phase_counts(0, phase).unwrap(), &expected[phase][..]);
        assert_eq!(
            moment.offset_counts(0, 1, phase).unwrap(),
            &offset[phase][..]
        );
    }
    assert_eq!(moment.cells(), 400);
    assert_eq!(moment.opening(), opening.lift());
}

/// Lean `HNN/Moment.encoderMoment_contract`: for any rational encoder and pair port, the open
/// storage from the counts equals the streamed sum `Σ_k P^(τ_cut − τ_k)(E x_k + E^(1)(x_k, x_(k−1)))`.
#[test]
fn the_moment_contracts_to_the_streamed_encoder_sum() {
    let field = small_field(&[3, 2], vec![contact(0, 1, 1, 0)], 1);
    let medium = Medium::generic(&field, 5, Parts::default());
    let mut draw = Draw::new(8);
    let cells: Vec<usize> = (0..60).map(|_| draw.below(2)).collect();
    let mut current = Current::at_rest(&field);
    let mut moment = SourceMoment::open(&field, &current);
    // Stop only at a carry-out; feed the rest after.
    let mut fed = 0;
    let mut phases = Vec::new();
    let mut probe = current.clone();
    for &code in &cells {
        probe.step(&field, code).unwrap();
        phases.push(probe.lift()[0].clone());
    }
    while fed < cells.len() {
        fed += moment
            .ingest(&field, &mut current, &cells[fed..])
            .unwrap()
            .cells;
    }
    let ring = field.ring(0);
    let port = medium.source_port(0).unwrap();
    let pair = medium.pair_port(0, 1).unwrap();
    let mut streamed = vec![Rat::zero(); ring.width()];
    for (k, &code) in cells.iter().enumerate() {
        let mut x = vec![Rat::zero(); 2];
        x[code] = Rat::from_integer(1.into());
        let mut driven = port.apply(&x).unwrap();
        if k > 0 {
            let mut counts = vec![0u64; 4];
            counts[code * 2 + cells[k - 1]] = 1;
            driven = add(&driven, &pair.apply(&counts, 2, ring.width()));
        }
        let shift = &current.lift()[0] - &phases[k];
        streamed = add(&streamed, &ring.rotate(&driven, &shift));
    }
    let open = moment.open_storage(&field, &medium, &current).unwrap();
    assert_eq!(open[0], streamed);
    assert!(open[1].iter().all(Zero::is_zero));
}

/// Lean `HNN/Moment.encoder_covector_tape_free`: the encoder covector, read from the counts and the
/// covector alone, equals the exact directional derivative of `⟨g, s(0)⟩` in `E`.
#[test]
fn the_encoder_covector_is_the_exact_directional_derivative() {
    let field = &chain();
    let mut medium = Medium::generic(field, 9, Parts::default());
    let mut draw = Draw::new(10);
    let cells: Vec<usize> = (0..10).map(|_| draw.below(4)).collect();
    let mut current = Current::at_rest(field);
    let mut moment = SourceMoment::open(field, &current);
    moment.ingest(field, &mut current, &cells).unwrap();
    let covector = draw.vector(4);
    let base = dot(
        &covector,
        &moment.open_storage(field, &medium, &current).unwrap()[0],
    );
    let gradient = moment
        .encoder_covector(field, &current, 0, &covector)
        .unwrap();
    let direction = draw.matrix(4, 4);
    let pairing: Rat = gradient
        .entries()
        .iter()
        .zip(direction.entries())
        .map(|(g, e)| g * e)
        .sum();
    medium.source[0] = Some(medium.source[0].as_ref().unwrap().add(&direction).unwrap());
    let moved = dot(
        &covector,
        &moment.open_storage(field, &medium, &current).unwrap()[0],
    );
    assert_eq!(moved - base, pairing);
}

/// The window is a shift register of raw cells, overwritten; its bits are counted in the moment's
/// dense code, which is sized once.
#[test]
fn the_window_overwrites_and_its_bits_are_counted() {
    let field = &chain();
    let mut current = Current::at_rest(field);
    let mut moment = SourceMoment::open(field, &current);
    assert_eq!(moment.window(), vec![None]);
    let empty = moment.dense_bits();
    moment.ingest(field, &mut current, &[3, 1, 2]).unwrap();
    assert_eq!(moment.window(), vec![Some(2)]);
    // Slots are fixed: only their widths change. The window's 3 bits are in the empty code too
    // (`d = 2`, `|A| = 4`).
    assert!(moment.dense_bits() >= empty);
    assert_eq!(empty, 2 * (2 * 4 + 2 * 4 * 4) + 3);
}

/// Ingest stops at the joint clock's carry-out: the aeon boundary belongs to the winding.
#[test]
fn ingest_stops_at_the_carry_out() {
    let field = small_field(&[2, 2], vec![contact(0, 1, 1, 0)], 1);
    let mut current = Current::at_rest(&field);
    let mut moment = SourceMoment::open(&field, &current);
    // Code 0 steps both rings: ring 1 wraps at the second cell (1 + 1 + carry).
    let ingested = moment.ingest(&field, &mut current, &[0, 0, 0, 0]).unwrap();
    assert!(ingested.carry_out);
    assert_eq!(ingested.cells, 2);
    assert_eq!(moment.cells(), 2);
    let rest = moment.ingest(&field, &mut current, &[1, 1]).unwrap();
    assert!(!rest.carry_out);
    assert_eq!(rest.cells, 2);
}
