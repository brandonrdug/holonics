//! The word's tests (Decision 24). [`oracle`] states the contract of `word.rs`'s header directly
//! on unbounded integers, independent of the device code: the split is Lean's `round`
//! (`⌊s/2^L + 1/2⌋`, ties upward) taken on exact rationals, the refinement is `X(2 − AX)` formed
//! whole, and each refusal is decided from the exact terms. The fast tests prove the host-side laws
//! (the layouts, the ceilings, the split, the tick's accounting and the executed adjoint's pairing)
//! without a card; the parity tests are `#[ignore]` and require exact equality with the oracle on
//! the card, refusals included. Run them alone on the card:
//!
//! ```text
//! flock .local/gpu.lock cargo test -p holonics-cuda -- --include-ignored --test-threads=1
//! ```

use std::time::Instant;

use holonics::ratio::Rat;
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};

use super::card::{CERTIFICATE_SHARED_PER_THREAD, READ_SHARED_PER_THREAD};
use super::tests::{Draw, card, census, entry};
use super::word::{
    CERTIFICATE_ENTRY, INVERSE_EXPONENT_CEILING, RESIDUAL_ENTRY, TICK_ENTRY, TICK_EXPONENT_CEILING,
};
use super::*;
use crate::cuda::Dim3;

// -------------------------------------------------------------------------------------------
// the oracle

/// The contract on unbounded integers (see the module header).
mod oracle {
    use super::*;

    /// `2^127`, the least magnitude outside the carrier.
    pub fn carrier() -> BigInt {
        BigInt::one() << 127usize
    }

    /// Lean `LatticeDeposit.quot`/`rem`: `q = round(s/2^L) = ⌊s/2^L + 1/2⌋`, `r = s − q·2^L`.
    pub fn split(s: &BigInt, shift: u32) -> (BigInt, BigInt) {
        let unit = BigInt::one() << shift as usize;
        let lifted = Rat::new(s.clone(), unit.clone()) + Rat::new(BigInt::one(), BigInt::from(2));
        let q = lifted.floor().to_integer();
        let r = s - &q * &unit;
        (q, r)
    }

    /// A carried vector: every row's state word, remainder and refusal, region by region.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Carried {
        pub state: Vec<i64>,
        pub remainder: Vec<i64>,
        pub status: Vec<Option<Refusal>>,
    }

    impl Carried {
        pub fn open(state: Vec<i64>, remainder: Vec<i64>) -> Self {
            let status = vec![None; state.len()];
            Self {
                state,
                remainder,
                status,
            }
        }
    }

    /// One tick (or adjoint tick) of every region: `(ξ', r') = split_(L_c)(qξ + r)`.
    pub fn tick(charts: &[WordChart], carried: &Carried, orientation: Orientation) -> Carried {
        let mut next = Carried {
            state: Vec::new(),
            remainder: Vec::new(),
            status: Vec::new(),
        };
        let mut base = 0;
        for chart in charts {
            let n = chart.width();
            let refused = carried.status[base..base + n].iter().any(Option::is_some);
            for i in 0..n {
                let (state, remainder, status) = if refused {
                    (0, 0, Some(Refusal::Operand))
                } else {
                    let mut s = BigInt::from(carried.remainder[base + i]);
                    let mut bound = s.abs();
                    for j in 0..n {
                        let q = match orientation {
                            Orientation::Forward => chart.word(i, j),
                            Orientation::Adjoint => chart.word(j, i),
                        };
                        let p = BigInt::from(q) * BigInt::from(carried.state[base + j]);
                        bound += p.abs();
                        s += p;
                    }
                    if bound >= carrier() {
                        (0, 0, Some(Refusal::Carrier))
                    } else {
                        let (q, r) = split(&s, chart.chart_exponent());
                        match q.to_i64() {
                            Some(q) => (q, r.to_i64().expect("L_c ≤ 64 keeps r a word"), None),
                            None => (0, 0, Some(Refusal::Word)),
                        }
                    }
                };
                next.state.push(state);
                next.remainder.push(remainder);
                next.status.push(status);
            }
            base += n;
        }
        next
    }

    /// One pair's chart with its statuses, row-major.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Chart {
        pub words: Vec<i64>,
        pub status: Vec<Option<Refusal>>,
    }

    impl Chart {
        pub fn of(pair: &InversePair) -> Self {
            Self {
                words: pair.chart().to_vec(),
                status: vec![None; pair.chart().len()],
            }
        }
    }

    /// The exact product `a ξ` of one pair.
    fn product(pair: &InversePair, chart: &Chart) -> Vec<BigInt> {
        let n = pair.width();
        let mut out = vec![BigInt::zero(); n * n];
        for i in 0..n {
            for j in 0..n {
                for k in 0..n {
                    out[i * n + j] += BigInt::from(pair.operator()[i * n + k])
                        * BigInt::from(chart.words[k * n + j]);
                }
            }
        }
        out
    }

    /// The residual `ρ = 2^S·1 − aξ` with its refusals.
    pub fn residual(pair: &InversePair, chart: &Chart) -> Vec<(BigInt, Option<Refusal>)> {
        let n = pair.width();
        let unit = BigInt::one() << pair.shift() as usize;
        let mut out = Vec::with_capacity(n * n);
        for i in 0..n {
            for j in 0..n {
                if (0..n).any(|k| chart.status[k * n + j].is_some()) {
                    out.push((BigInt::zero(), Some(Refusal::Operand)));
                    continue;
                }
                let diagonal = if i == j { unit.clone() } else { BigInt::zero() };
                let (mut sum, mut bound) = (BigInt::zero(), diagonal.clone());
                for k in 0..n {
                    let p = BigInt::from(pair.operator()[i * n + k])
                        * BigInt::from(chart.words[k * n + j]);
                    bound += p.abs();
                    sum += p;
                }
                out.push(if bound >= carrier() {
                    (BigInt::zero(), Some(Refusal::Carrier))
                } else {
                    (diagonal - sum, None)
                });
            }
        }
        out
    }

    /// One refinement: `X(2 − AX)` formed whole on `2^(−(S + L_c))ℤ`, split at `2^S`; returns the
    /// refined chart and the largest discarded remainder's magnitude.
    pub fn refine(pair: &InversePair, chart: &Chart) -> (Chart, BigInt) {
        let n = pair.width();
        let shift = pair.shift();
        let rho = residual(pair, chart);
        let twice = BigInt::one() << (shift as usize + 1);
        let ax = product(pair, chart);
        let (mut words, mut status) = (Vec::new(), Vec::new());
        let mut discarded = BigInt::zero();
        for i in 0..n {
            for j in 0..n {
                let refused =
                    (0..n).any(|k| chart.status[i * n + k].is_some() || rho[k * n + j].1.is_some());
                if refused {
                    words.push(0);
                    status.push(Some(Refusal::Operand));
                    continue;
                }
                let bound: BigInt = (0..n)
                    .map(|k| BigInt::from(chart.words[i * n + k]).abs() * rho[k * n + j].0.abs())
                    .sum();
                if bound >= carrier() {
                    words.push(0);
                    status.push(Some(Refusal::Carrier));
                    continue;
                }
                let z: BigInt = (0..n)
                    .map(|k| {
                        let two = if k == j {
                            twice.clone()
                        } else {
                            BigInt::zero()
                        };
                        BigInt::from(chart.words[i * n + k]) * (two - &ax[k * n + j])
                    })
                    .sum();
                let (q, e) = split(&z, shift);
                if e.abs() > discarded {
                    discarded = e.abs();
                }
                match q.to_i64() {
                    Some(q) => {
                        words.push(q);
                        status.push(None);
                    }
                    None => {
                        words.push(0);
                        status.push(Some(Refusal::Word));
                    }
                }
            }
        }
        (Chart { words, status }, discarded)
    }

    /// The certificate's numerator `max_i Σ_j |ρ_ij|`, or its refusal.
    pub fn certificate(pair: &InversePair, chart: &Chart) -> Result<BigInt, Refusal> {
        let n = pair.width();
        let rho = residual(pair, chart);
        if rho.iter().any(|(_, status)| status.is_some()) {
            return Err(Refusal::Operand);
        }
        let largest = (0..n)
            .map(|i| (0..n).map(|j| rho[i * n + j].0.abs()).sum::<BigInt>())
            .max()
            .unwrap_or_default();
        if largest >= carrier() {
            Err(Refusal::Carrier)
        } else {
            Ok(largest)
        }
    }

    /// `‖A‖∞`, exact.
    pub fn operator_norm(pair: &InversePair) -> Rat {
        let n = pair.width();
        let largest = (0..n)
            .map(|i| {
                (0..n)
                    .map(|k| BigInt::from(pair.operator()[i * n + k]).abs())
                    .sum::<BigInt>()
            })
            .max()
            .unwrap_or_default();
        Rat::new(largest, BigInt::one() << pair.operator_exponent() as usize)
    }
}

use oracle::{Carried, Chart};

// -------------------------------------------------------------------------------------------
// fixtures

/// Campaign 1's rings, realified: `2 d_g` for the periods 5, 7, 11, 13.
const RINGS: [usize; 4] = [10, 14, 22, 26];
/// Campaign 1's contacts' channels, realified: `2 min(d_from, d_to)` over the chain of four.
const CONTACTS: [usize; 4] = [10, 14, 22, 10];
/// The widest region campaign 1 admits, `n ≤ 64`, with three narrow ones.
const WIDEST: [usize; 4] = [64, 1, 2, 3];

/// An exponent in campaign 1's range `16..=40`.
fn exponent(draw: &mut Draw) -> u32 {
    16 + draw.below(25) as u32
}

/// A region at drawn exponents: chart words below `2^(L_c − chart_slack)`, state words below
/// `2^(L_w + 2)`, remainders inside the cell.
struct Drawn {
    charts: Vec<WordChart>,
    carried: Carried,
}

fn drawn(draw: &mut Draw, widths: &[usize], chart_slack: u32) -> Drawn {
    let mut charts = Vec::new();
    let (mut state, mut remainder) = (Vec::new(), Vec::new());
    for &n in widths {
        let (lc, lw) = (exponent(draw), exponent(draw));
        let words = (0..n * n).map(|_| draw.signed(lc - chart_slack)).collect();
        charts.push(WordChart::new(n, lc, lw, words).unwrap());
        for _ in 0..n {
            state.push(draw.signed(lw + 2));
            remainder.push(draw.signed(lc - 1));
        }
    }
    Drawn {
        charts,
        carried: Carried::open(state, remainder),
    }
}

/// Regions whose words reach the carrier: the widest region's chart and state words take 62 and 63
/// bits (a row sum of `n ≥ 22` such products has mean magnitude about `n·2^123 ≥ 2^127`, so its rows
/// straddle the carrier's edge), the others 30 to 62 and 30 to 63 bits, so that some regions are
/// exact, some refuse the word, and their refusals travel to the next tick.
fn drawn_wide(draw: &mut Draw, widths: &[usize]) -> Drawn {
    let widest = widths.iter().copied().max().unwrap_or(0);
    let mut charts = Vec::new();
    let (mut state, mut remainder) = (Vec::new(), Vec::new());
    for &n in widths {
        let lc = exponent(draw);
        let (chart_bits, state_bits) = if n == widest {
            (62, 63)
        } else {
            (30 + draw.below(33) as u32, 30 + draw.below(34) as u32)
        };
        let words = (0..n * n).map(|_| draw.signed(chart_bits)).collect();
        charts.push(WordChart::new(n, lc, exponent(draw), words).unwrap());
        for _ in 0..n {
            state.push(draw.signed(state_bits));
            remainder.push(draw.signed(lc - 1));
        }
    }
    Drawn {
        charts,
        carried: Carried::open(state, remainder),
    }
}

/// The oracle's reading of a released word.
fn carried(release: &CarryRelease) -> Carried {
    Carried {
        state: release.state().to_vec(),
        remainder: release.remainder().to_vec(),
        status: release
            .status()
            .iter()
            .map(|status| Refusal::of_status(*status).unwrap())
            .collect(),
    }
}

fn oracle_word(charts: &[WordChart], opening: &Carried, ticks: usize, o: Orientation) -> Carried {
    (0..ticks).fold(opening.clone(), |carried, _| {
        oracle::tick(charts, &carried, o)
    })
}

/// The exact image `qξ + r − r = ξ'·2^(L_c) + r' − r` a tick executed, recovered from its split.
fn executed_image(charts: &[WordChart], before: &Carried, after: &Carried) -> Vec<BigInt> {
    let mut image = Vec::new();
    let mut base = 0;
    for chart in charts {
        for i in 0..chart.width() {
            let at = base + i;
            image.push(
                (BigInt::from(after.state[at]) << chart.chart_exponent() as usize)
                    + BigInt::from(after.remainder[at])
                    - BigInt::from(before.remainder[at]),
            );
        }
        base += chart.width();
    }
    image
}

/// `qξ` (or `qᵀξ`) exactly, per region.
fn exact_image(charts: &[WordChart], state: &[i64], orientation: Orientation) -> Vec<BigInt> {
    let mut image = Vec::new();
    let mut base = 0;
    for chart in charts {
        let n = chart.width();
        for i in 0..n {
            image.push(
                (0..n)
                    .map(|j| {
                        let q = match orientation {
                            Orientation::Forward => chart.word(i, j),
                            Orientation::Adjoint => chart.word(j, i),
                        };
                        BigInt::from(q) * BigInt::from(state[base + j])
                    })
                    .sum(),
            );
        }
        base += n;
    }
    image
}

/// Every remainder lies in its cell `[−2^(L_c−1), 2^(L_c−1))`.
fn in_cells(charts: &[WordChart], remainder: &[i64]) -> bool {
    let mut base = 0;
    charts.iter().all(|chart| {
        let lc = chart.chart_exponent();
        let inside = remainder[base..base + chart.width()].iter().all(|r| {
            let r = i128::from(*r);
            if lc == 0 {
                r == 0
            } else {
                let half = 1i128 << (lc - 1);
                -half <= r && r < half
            }
        });
        base += chart.width();
        inside
    })
}

/// `A = I − K` with `K` skew on `2^(−L_A)ℤ`, `|k_ij| < 2^(L_A − 7)` (so `‖K‖∞ < n/128 ≤ 1/2`),
/// and the chart of `I + K` (the Neumann series' first two terms) split onto `2^(−L_c)ℤ`: the
/// Cayley denominator `1 − E/2` of a ring element and a warm chart of its inverse.
fn cayley_pair(draw: &mut Draw, n: usize, la: u32, lc: u32) -> InversePair {
    let mut k = vec![0i64; n * n];
    for i in 0..n {
        for j in i + 1..n {
            let v = draw.signed(la - 7);
            k[i * n + j] = v;
            k[j * n + i] = -v;
        }
    }
    let unit = 1i64 << la;
    let diagonal = |at: usize| if at / n == at % n { unit } else { 0 };
    let operator = (0..n * n).map(|at| diagonal(at) - k[at]).collect();
    let chart = (0..n * n)
        .map(|at| {
            let v = BigInt::from(diagonal(at) + k[at]);
            let moved = if lc >= la {
                v << (lc - la) as usize
            } else {
                oracle::split(&v, la - lc).0
            };
            moved.to_i64().unwrap()
        })
        .collect();
    InversePair::new(n, la, lc, operator, chart).unwrap()
}

/// A pair of drawn words: operator and chart words below `2^bits`.
fn drawn_pair(draw: &mut Draw, n: usize, bits: u32) -> InversePair {
    let (la, lc) = (exponent(draw), exponent(draw));
    let operator = (0..n * n).map(|_| draw.signed(bits)).collect();
    let chart = (0..n * n).map(|_| draw.signed(bits)).collect();
    InversePair::new(n, la, lc, operator, chart).unwrap()
}

// -------------------------------------------------------------------------------------------
// fast tests: the host-side laws

/// The tick's layout is the read's over the flattened rows (one block per output entry, one warp
/// covering a campaign region's row); the inverse's is the read's over rows × columns; the
/// certificate's is one block per chart, its threads covering the rows.
#[test]
fn word_layouts_are_derived_from_the_census() {
    let census = census();
    let tick = entry(TICK_ENTRY, 1024, 4);
    // Campaign 1's four rings and four contacts: 128 rows, the widest 26.
    let rows: usize = RINGS.iter().chain(&CONTACTS).sum();
    let layout = read_layout(&census, &tick, rows, 26, 1).unwrap();
    assert_eq!(
        (layout.grid, layout.block, layout.shared),
        (
            Dim3 { x: 128, y: 1, z: 1 },
            Dim3::x(32),
            32 * READ_SHARED_PER_THREAD
        )
    );
    assert_eq!(
        layout.realization,
        Realization::EntryPerBlock {
            entries: 128,
            threads: 32,
            per_thread: 1
        }
    );
    // The widest region, 64, takes two warps.
    assert_eq!(
        read_layout(&census, &tick, 70, 64, 1).unwrap().block,
        Dim3::x(64)
    );
    // The inverse over the rings: 72 rows × 26 columns, one block per entry.
    let residual = entry(RESIDUAL_ENTRY, 1024, 4);
    let layout = read_layout(&census, &residual, 72, 26, 26).unwrap();
    assert_eq!(
        (layout.grid, layout.block),
        (Dim3 { x: 72, y: 26, z: 1 }, Dim3::x(32))
    );
    // The certificate: one block per chart.
    let certificate = entry(CERTIFICATE_ENTRY, 1024, 4);
    let layout = certificate_layout(&census, &certificate, 4, 26).unwrap();
    assert_eq!(
        (layout.grid, layout.block, layout.shared),
        (Dim3::x(4), Dim3::x(32), 32 * CERTIFICATE_SHARED_PER_THREAD)
    );
    assert_eq!(
        layout.realization,
        Realization::ChartPerBlock {
            charts: 4,
            threads: 32,
            rows_per_thread: 1
        }
    );
    // More rows than the block carries loop: (49,152 − 4)/16 = 3,071 threads by shared, 1,024 by
    // the ceiling.
    assert_eq!(
        certificate_layout(&census, &certificate, 1, 3000)
            .unwrap()
            .realization,
        Realization::ChartPerBlock {
            charts: 1,
            threads: 1024,
            rows_per_thread: 3
        }
    );
    assert!(matches!(
        certificate_layout(&census, &certificate, 0, 4),
        Err(DeviceError::Launch { .. })
    ));
}

/// The ceilings are the words': a tick's `L_c ≤ 64` keeps the remainder a signed 64-bit word, an
/// inverse's `S ≤ 126` keeps `2^S` a carrier word; shapes are checked.
#[test]
fn word_charts_and_pairs_refuse_past_their_ceilings() {
    assert_eq!(TICK_EXPONENT_CEILING, 64);
    assert_eq!(INVERSE_EXPONENT_CEILING, 126);
    assert!(WordChart::new(1, 64, 0, vec![1]).is_ok());
    assert!(matches!(
        WordChart::new(1, 65, 0, vec![1]),
        Err(DeviceError::Exponent { exponent: 65, .. })
    ));
    assert!(matches!(
        WordChart::new(2, 3, 0, vec![1, 2, 3]),
        Err(DeviceError::Shape { .. })
    ));
    assert!(InversePair::new(1, 63, 63, vec![1], vec![1]).is_ok());
    assert!(matches!(
        InversePair::new(1, 64, 63, vec![1], vec![1]),
        Err(DeviceError::Exponent { exponent: 127, .. })
    ));
    assert!(matches!(
        InversePair::new(2, 1, 1, vec![1; 4], vec![1; 3]),
        Err(DeviceError::Shape { .. })
    ));
    let rectangle = LatticeCoordinates::of_vectors(
        &[vec![Rat::one(), Rat::zero()]],
        holonics::hnn::Lattice::new(0),
    )
    .unwrap();
    assert!(matches!(
        WordChart::of_coordinates(&rectangle, 0),
        Err(DeviceError::Shape { .. })
    ));
}

/// The oracle's split is Lean's nearest-point division: `s = q·2^L + r`, `r` in its half-open cell,
/// ties upward on both signs, and every integer a lattice point at `L = 0`.
#[test]
fn the_split_is_the_nearest_point_ties_upward() {
    let mut draw = Draw(3);
    for shift in [0u32, 1, 2, 5, 16, 40, 64, 126] {
        let unit = BigInt::one() << shift as usize;
        for _ in 0..200 {
            let s = BigInt::from(draw.signed(63)) * BigInt::from(draw.signed(63));
            let (q, r) = oracle::split(&s, shift);
            assert_eq!(&q * &unit + &r, s);
            assert!(
                r.clone() * 2 >= -unit.clone() && r.clone() * 2 < unit,
                "{shift}"
            );
        }
        if shift > 0 {
            let half = BigInt::one() << (shift as usize - 1);
            for q in [-3i64, -1, 0, 2] {
                let tie = BigInt::from(q) * &unit + &half;
                assert_eq!(
                    oracle::split(&tie, shift),
                    (BigInt::from(q + 1), -half.clone())
                );
            }
        } else {
            assert_eq!(
                oracle::split(&BigInt::from(-7), 0),
                (BigInt::from(-7), BigInt::zero())
            );
        }
    }
}

/// **The tick's accounting** (Lean `feedback_tick`, `feedback_accounting`): at campaign 1's
/// shapes, every oracle tick has `ξ'·2^(L_c) + r' = qξ + r` exactly with `r'` in its cell, a word
/// of `k` ticks telescopes to `Σ_t ξ_(t+1)·2^(L_c) + r_k = Σ_t qξ_t + r_0`, and the executed
/// adjoint pairs exactly with the executed chart, `⟨λ, qξ⟩ = ⟨qᵀλ, ξ⟩`
/// (`executed_adjoint_pairing`), each read from the splits alone.
#[test]
fn the_tick_accounts_exactly() {
    let mut draw = Draw(11);
    for widths in [&RINGS[..], &CONTACTS[..]] {
        let Drawn { charts, carried } = drawn(&mut draw, widths, 3);
        let rows = carried.state.len();
        let mut states = vec![carried.clone()];
        for _ in 0..5 {
            let next = oracle::tick(&charts, states.last().unwrap(), Orientation::Forward);
            let before = states.last().unwrap();
            assert!(next.status.iter().all(Option::is_none));
            assert_eq!(
                executed_image(&charts, before, &next),
                exact_image(&charts, &before.state, Orientation::Forward)
            );
            assert!(in_cells(&charts, &next.remainder));
            states.push(next);
        }
        // The telescoping over the word, row by row.
        let mut base = 0;
        for chart in &charts {
            for i in 0..chart.width() {
                let row = base + i;
                let carried: BigInt = states[1..]
                    .iter()
                    .map(|s| BigInt::from(s.state[row]) << chart.chart_exponent() as usize)
                    .sum::<BigInt>()
                    + BigInt::from(states[5].remainder[row]);
                let exact: BigInt = states[..5]
                    .iter()
                    .map(|s| exact_image(&charts, &s.state, Orientation::Forward)[row].clone())
                    .sum::<BigInt>()
                    + BigInt::from(states[0].remainder[row]);
                assert_eq!(carried, exact, "row {row}");
            }
            base += chart.width();
        }
        // The executed adjoint's pairing, from the two splits.
        let covector = Carried::open((0..rows).map(|_| draw.signed(40)).collect(), vec![0; rows]);
        let forward = oracle::tick(&charts, &carried, Orientation::Forward);
        let adjoint = oracle::tick(&charts, &covector, Orientation::Adjoint);
        let q_x = executed_image(&charts, &carried, &forward);
        let qt_l = executed_image(&charts, &covector, &adjoint);
        let pair = |a: &[BigInt], b: &[i64]| -> BigInt {
            a.iter().zip(b).map(|(a, b)| a * BigInt::from(*b)).sum()
        };
        assert_eq!(pair(&q_x, &covector.state), pair(&qt_l, &carried.state));
    }
}

// -------------------------------------------------------------------------------------------
// parity on the card

/// The tick and the adjoint tick equal the oracle on hand fixtures: dyadic words at `L_c` of 4, 0
/// and 64; ties upward on both signs; the word's edge (`2^63 − 1` and `−2^63` admitted, one past
/// refused); the carrier's edge (`2^127 − 1` admitted with the remainder's share, `2^127` refused
/// whatever the value); an opening remainder off its cell refused by position; and a second tick,
/// where a region with a refused entry is refused throughout and the others go on.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn word_tick_matches_the_oracle_on_small_fixtures() {
    let card = card();
    let m = i64::MAX;
    let charts = vec![
        // 0: dyadic, L_c = 4.
        WordChart::new(3, 4, 6, vec![16, -8, 3, 5, 0, -7, -1, 2, 33]).unwrap(),
        // 1: L_c = 0, the split is the identity.
        WordChart::new(2, 0, 0, vec![2, -3, 1, 1]).unwrap(),
        // 2: L_c = 64, the widest remainder.
        WordChart::new(1, 64, 0, vec![m]).unwrap(),
        // 3: ties at L_c = 3: 8k + 4 and −8k − 4.
        WordChart::new(2, 3, 0, vec![8, 4, -8, -4]).unwrap(),
        // 4: the word's upper edge at L_c = 2.
        WordChart::new(2, 2, 0, vec![4, 2, 4, 2]).unwrap(),
        // 5: the word's lower edge at L_c = 2.
        WordChart::new(2, 2, 0, vec![4, 2, 4, 2]).unwrap(),
        // 6: the carrier's edge at L_c = 16.
        WordChart::new(
            4,
            16,
            0,
            [[m, m, (1 << 33) - 1, (1 << 32) - 8]; 3]
                .concat()
                .into_iter()
                .chain([0, 0, 0, 1])
                .collect(),
        )
        .unwrap(),
    ];
    let state = vec![
        5,
        -9,
        2, // 0
        7,
        -4, // 1
        m,  // 2
        11,
        1, // 3
        m,
        1, // 4
        i64::MIN,
        -1, // 5
        m,
        -m,
        1 << 32,
        1, // 6
    ];
    let remainder = vec![
        3,
        -8,
        0, // 0 (cells of 2^3)
        0,
        0,        // 1 (L_c = 0: only zero)
        i64::MIN, // 2 (the cell's least point)
        0,
        0, // 3
        -1,
        0, // 4: 4(2^63 − 1) + 1 admitted; 4(2^63 − 1) + 2 ties to 2^63, refused
        0,
        -1, // 5: −2^65 − 2 ties up to −2^63; −2^65 − 3 is −2^63 − 1, refused
        5,
        6,
        -6,
        -6, // 6: bound 2^127 − 6 + |r|
    ];
    let opening = Carried::open(state.clone(), remainder.clone());
    let expected = oracle::tick(&charts, &opening, Orientation::Forward);
    // The hand expectations the oracle must meet (rows: region 3 is 6..8, 4 is 8..10, 5 is
    // 10..12, 6 is 12..16).
    assert_eq!(expected.state[6..8], [12, -11]);
    assert_eq!(expected.remainder[6..8], [-4, -4]);
    assert_eq!(
        (expected.state[8], expected.remainder[8], expected.status[8]),
        (m, 1, None)
    );
    assert_eq!(expected.status[9], Some(Refusal::Word));
    assert_eq!(
        (
            expected.state[10],
            expected.remainder[10],
            expected.status[10]
        ),
        (i64::MIN, -2, None)
    );
    assert_eq!(expected.status[11], Some(Refusal::Word));
    assert_eq!(
        expected.status[12..16],
        [None, Some(Refusal::Carrier), Some(Refusal::Carrier), None]
    );
    assert_eq!((expected.state[12], expected.remainder[12]), (1 << 49, -3));
    assert_eq!((expected.state[15], expected.remainder[15]), (0, -5));

    let mounted = ResidentCharts::mount(&card, &charts).unwrap();
    eprintln!("tick: {:?}", mounted.layout());
    for orientation in [Orientation::Forward, Orientation::Adjoint] {
        let mut carry = ResidentCarry::open(&mounted, &state, Some(&remainder)).unwrap();
        card.stage(&mounted, &mut carry, orientation).unwrap();
        let first = carry.release().unwrap();
        let expected = oracle::tick(&charts, &opening, orientation);
        assert_eq!(carried(&first), expected, "{orientation:?}");
        card.stage(&mounted, &mut carry, orientation).unwrap();
        let second = carry.release().unwrap();
        let expected = oracle::tick(&charts, &expected, orientation);
        assert_eq!(carried(&second), expected, "{orientation:?}, second tick");
        assert_eq!(second.ticks(), 2);
        if orientation == Orientation::Forward {
            // Regions 4, 5 and 6 carried a refusal; each is refused throughout at the second tick.
            let refused = second.refusals().unwrap();
            assert!(refused.iter().all(|(region, _, _)| *region >= 4));
            assert_eq!(refused.len(), 8);
            assert!(matches!(second.exact(), Err(DeviceError::Refused { .. })));
        }
    }
    // An opening remainder off its cell is refused by position.
    let mut off = remainder.clone();
    off[1] = 8; // region 0, entry 1: 2^3 is outside [−8, 8)
    assert!(matches!(
        ResidentCarry::open(&mounted, &state, Some(&off)),
        Err(DeviceError::OffCell {
            region: 0,
            entry: 1,
            exponent: 4
        })
    ));
    let mut off = remainder;
    off[3] = 1; // region 1 at L_c = 0 admits only zero
    assert!(matches!(
        ResidentCarry::open(&mounted, &state, Some(&off)),
        Err(DeviceError::OffCell {
            region: 1,
            entry: 0,
            exponent: 0
        })
    ));
}

/// The tick's accounting on the card's own outputs: at campaign 1's shapes, read back tick by
/// tick, every device tick satisfies `ξ'·2^(L_c) + r' = qξ + r` with `r'` in its cell, the word
/// telescopes, and the device's adjoint pairs exactly with its forward chart.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn word_tick_accounting_holds_on_the_card() {
    let card = card();
    let mut draw = Draw(29);
    let Drawn {
        charts,
        carried: opening,
    } = drawn(&mut draw, &RINGS, 3);
    let mounted = ResidentCharts::mount(&card, &charts).unwrap();
    let mut carry =
        ResidentCarry::open(&mounted, &opening.state, Some(&opening.remainder)).unwrap();
    let mut states = vec![opening.clone()];
    for _ in 0..4 {
        card.tick(&mounted, &mut carry).unwrap();
        let next = carried(&carry.release().unwrap().exact().unwrap());
        let before = states.last().unwrap();
        assert_eq!(
            executed_image(&charts, before, &next),
            exact_image(&charts, &before.state, Orientation::Forward)
        );
        assert!(in_cells(&charts, &next.remainder));
        states.push(next);
    }
    let rows = opening.state.len();
    let mut base = 0;
    for chart in &charts {
        for i in 0..chart.width() {
            let row = base + i;
            let carried: BigInt = states[1..]
                .iter()
                .map(|s| BigInt::from(s.state[row]) << chart.chart_exponent() as usize)
                .sum::<BigInt>()
                + BigInt::from(states[4].remainder[row]);
            let exact: BigInt = states[..4]
                .iter()
                .map(|s| exact_image(&charts, &s.state, Orientation::Forward)[row].clone())
                .sum::<BigInt>()
                + BigInt::from(opening.remainder[row]);
            assert_eq!(carried, exact, "row {row}");
        }
        base += chart.width();
    }
    // The executed adjoint on the card pairs exactly with the executed chart.
    let covector = Carried::open((0..rows).map(|_| draw.signed(40)).collect(), vec![0; rows]);
    let mut adjoint = ResidentCarry::open(&mounted, &covector.state, None).unwrap();
    card.adjoint_tick(&mounted, &mut adjoint).unwrap();
    let adjoint = carried(&adjoint.release().unwrap().exact().unwrap());
    let q_x = executed_image(&charts, &opening, &states[1]);
    let qt_l = executed_image(&charts, &covector, &adjoint);
    let pair = |a: &[BigInt], b: &[i64]| -> BigInt {
        a.iter().zip(b).map(|(a, b)| a * BigInt::from(*b)).sum()
    };
    assert_eq!(pair(&q_x, &covector.state), pair(&qt_l, &opening.state));
}

/// Random fixtures at campaign 1's shapes (the rings 10, 14, 22, 26; the contacts' channels 10,
/// 14, 22, 10; the widest region 64 with three narrow ones; `L_c`, `L_w` drawn in `16..=40`): `k`
/// resident ticks, forward and adjoint, equal `k` oracle ticks exactly; and on words that reach
/// the carrier, the refused entries are the oracle's, entry by entry.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn word_ticks_match_the_oracle_at_campaign_one_shapes() {
    let card = card();
    let mut draw = Draw(1_077);
    let (mut fixtures, mut refused, mut exact) = (0usize, [0usize; 3], 0usize);
    for seed in 0..12 {
        for widths in [&RINGS[..], &CONTACTS[..], &WIDEST[..]] {
            for (reach, o) in [
                (false, Orientation::Forward),
                (false, Orientation::Adjoint),
                (true, Orientation::Forward),
                (true, Orientation::Adjoint),
            ] {
                let Drawn {
                    charts,
                    carried: opening,
                } = if reach {
                    drawn_wide(&mut draw, widths)
                } else {
                    drawn(&mut draw, widths, 3)
                };
                let ticks = 1 + (seed % 5);
                let mounted = ResidentCharts::mount(&card, &charts).unwrap();
                let mut carry =
                    ResidentCarry::open(&mounted, &opening.state, Some(&opening.remainder))
                        .unwrap();
                for _ in 0..ticks {
                    card.stage(&mounted, &mut carry, o).unwrap();
                }
                let found = carried(&carry.release().unwrap());
                let expected = oracle_word(&charts, &opening, ticks, o);
                assert_eq!(
                    found, expected,
                    "seed {seed}, {widths:?}, {o:?}, reach {reach}"
                );
                if !reach {
                    assert!(expected.status.iter().all(Option::is_none));
                }
                for status in &expected.status {
                    match status {
                        None => exact += 1,
                        Some(Refusal::Carrier) => refused[0] += 1,
                        Some(Refusal::Word) => refused[1] += 1,
                        Some(Refusal::Operand) => refused[2] += 1,
                    }
                }
                fixtures += 1;
            }
        }
    }
    eprintln!(
        "{fixtures} fixtures: {exact} exact entries; refused carrier {}, word {}, operand {}",
        refused[0], refused[1], refused[2]
    );
    assert!(
        refused.iter().all(|count| *count > 0),
        "every refusal is crossed"
    );
}

/// Nanoseconds read as microseconds with three decimals, for a person (integer arithmetic).
fn micros(nanos: u128) -> String {
    format!("{}.{:03} us", nanos / 1_000, nanos % 1_000)
}

/// **The resident word.** Campaign 1's four rings, three ticks: the word runs resident (the
/// states, statuses and remainders stay on the card; only the opening state goes in and the final
/// state, the released remainders and the statuses come out, one transfer each way) and equals
/// three oracle ticks, launched tick by tick, reloaded in place, and as one captured graph; the
/// adjoint word likewise. Measured end to end on the card after a warm-up, as latency (one
/// synchronization per word) and back to back (one synchronization per run), with the bus octets.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn resident_word_equals_the_oracle_word_and_is_measured() {
    const TICKS: usize = 3;
    const REPEATS: u32 = 2_000;
    const WARM: u32 = 30_000;
    let card = card();
    let mut draw = Draw(6_148);
    let Drawn {
        charts,
        carried: opening,
    } = drawn(&mut draw, &RINGS, 3);
    eprintln!(
        "exponents (L_c, L_w): {:?}",
        charts
            .iter()
            .map(|c| (c.chart_exponent(), c.state_exponent()))
            .collect::<Vec<_>>()
    );
    let rows: usize = RINGS.iter().sum();
    let fresh = Carried::open(opening.state.clone(), vec![0; rows]);
    let expected = oracle_word(&charts, &fresh, TICKS, Orientation::Forward);
    let expected_adjoint = oracle_word(&charts, &fresh, TICKS, Orientation::Adjoint);
    let per = |total: u128, count: u32| total / u128::from(count);

    // The mount (once per window's charts) and a first word with its allocation.
    let clock = Instant::now();
    let mounted = ResidentCharts::mount(&card, &charts).unwrap();
    let mounted_ns = clock.elapsed().as_nanos();
    let clock = Instant::now();
    let mut carry = ResidentCarry::open(&mounted, &opening.state, None).unwrap();
    for _ in 0..TICKS {
        card.tick(&mounted, &mut carry).unwrap();
    }
    let release = carry.release().unwrap();
    let first_ns = clock.elapsed().as_nanos();
    assert_eq!(carried(&release), expected);
    assert_eq!(release.ticks(), TICKS as u64);
    eprintln!("tick layout: {:?}", mounted.layout());
    eprintln!(
        "bus octets: mount {} (charts {} + region tables), once; per word in {} (the opening \
         state; statuses and remainders zeroed on the card), out {} (state, remainders, statuses, \
         one transfer); between ticks 0",
        mounted.mounted_octets(),
        8 * RINGS.iter().map(|n| n * n).sum::<usize>(),
        carry.loaded_octets(false),
        carry.released_octets()
    );

    // The adjoint word.
    let mut adjoint = ResidentCarry::open(&mounted, &opening.state, None).unwrap();
    for _ in 0..TICKS {
        card.adjoint_tick(&mounted, &mut adjoint).unwrap();
    }
    assert_eq!(carried(&adjoint.release().unwrap()), expected_adjoint);

    // Warm the card to its working clocks.
    for _ in 0..WARM {
        card.tick(&mounted, &mut adjoint).unwrap();
    }
    card.synchronize().unwrap();

    // A window's word in place: load, three ticks, release; no allocation.
    let clock = Instant::now();
    for _ in 0..REPEATS {
        carry.load(&opening.state, None).unwrap();
        for _ in 0..TICKS {
            card.tick(&mounted, &mut carry).unwrap();
        }
        carry.release().unwrap();
    }
    let window_ns = per(clock.elapsed().as_nanos(), REPEATS);
    assert_eq!(carried(&carry.release().unwrap()), expected);
    // Its parts, each closed by the host's wait (the context blocks on a synchronization).
    let (mut loading, mut ticking, mut releasing) = (0u128, 0u128, 0u128);
    for _ in 0..REPEATS {
        let clock = Instant::now();
        carry.load(&opening.state, None).unwrap();
        card.synchronize().unwrap();
        loading += clock.elapsed().as_nanos();
        let clock = Instant::now();
        for _ in 0..TICKS {
            card.tick(&mounted, &mut carry).unwrap();
        }
        card.synchronize().unwrap();
        ticking += clock.elapsed().as_nanos();
        let clock = Instant::now();
        carry.release().unwrap();
        releasing += clock.elapsed().as_nanos();
    }
    let clock = Instant::now();
    for _ in 0..REPEATS {
        card.synchronize().unwrap();
    }
    let idle_ns = per(clock.elapsed().as_nanos(), REPEATS);

    // The ticks alone, launched tick by tick: one synchronization per word (latency), then one
    // per run (back to back).
    let clock = Instant::now();
    for _ in 0..REPEATS {
        for _ in 0..TICKS {
            card.tick(&mounted, &mut carry).unwrap();
        }
        card.synchronize().unwrap();
    }
    let launched_ns = per(clock.elapsed().as_nanos(), REPEATS);
    let clock = Instant::now();
    for _ in 0..REPEATS {
        for _ in 0..TICKS {
            card.tick(&mounted, &mut carry).unwrap();
        }
    }
    card.synchronize().unwrap();
    let streamed_ns = per(clock.elapsed().as_nanos(), REPEATS);

    // One captured graph per word, at each parity (a word of three ticks flips it).
    carry.load(&opening.state, None).unwrap();
    let even = card
        .capture_word(&mounted, &mut carry, TICKS, Orientation::Forward)
        .unwrap();
    eprintln!("word graph: {:?}", even.census());
    even.launch(&mut carry).unwrap();
    assert_eq!(carried(&carry.release().unwrap()), expected);
    assert!(matches!(even.launch(&mut carry), Err(DeviceError::Graph)));
    let odd = card
        .capture_word(&mounted, &mut carry, TICKS, Orientation::Forward)
        .unwrap();
    odd.launch(&mut carry).unwrap();
    assert_eq!(
        carried(&carry.release().unwrap()),
        oracle_word(&charts, &expected, TICKS, Orientation::Forward)
    );
    let graphs = [&even, &odd];
    let clock = Instant::now();
    for repeat in 0..REPEATS {
        graphs[repeat as usize % 2].launch(&mut carry).unwrap();
        card.synchronize().unwrap();
    }
    let graphed_ns = per(clock.elapsed().as_nanos(), REPEATS);
    let clock = Instant::now();
    for repeat in 0..REPEATS {
        graphs[repeat as usize % 2].launch(&mut carry).unwrap();
    }
    card.synchronize().unwrap();
    let graph_streamed_ns = per(clock.elapsed().as_nanos(), REPEATS);

    // A whole window's word as one graph: the load, the ticks and the release, one launch and one
    // wait per word; each window opens at the same state and releases the oracle's word.
    let window = card
        .capture_window(&mounted, &mut carry, TICKS, Orientation::Forward)
        .unwrap();
    eprintln!("window graph: {:?}", window.census());
    assert!(matches!(window.launch(&mut carry), Err(DeviceError::Graph)));
    assert!(matches!(
        carry.run_window(&even, &opening.state),
        Err(DeviceError::Graph)
    ));
    assert_eq!(
        carried(&carry.run_window(&window, &opening.state).unwrap()),
        expected
    );
    let clock = Instant::now();
    for _ in 0..REPEATS {
        carry.run_window(&window, &opening.state).unwrap();
    }
    let windowed_ns = per(clock.elapsed().as_nanos(), REPEATS);
    assert_eq!(
        carried(&carry.run_window(&window, &opening.state).unwrap()),
        expected
    );

    let tick = |word: u128| micros(word / TICKS as u128);
    eprintln!(
        "window word as one graph (load + {TICKS} ticks + release, one launch, one wait): {} per \
         word, {} per tick",
        micros(windowed_ns),
        tick(windowed_ns)
    );
    eprintln!("mount of the four charts: {}", micros(mounted_ns));
    eprintln!(
        "first word with its allocation (open + {TICKS} ticks + release): {}",
        micros(first_ns)
    );
    eprintln!(
        "window word in place (load + {TICKS} ticks + release, {REPEATS} words): {} per word",
        micros(window_ns)
    );
    eprintln!(
        "its parts, each with its own wait: load {}, {TICKS} ticks {}, release {}; a wait on an \
         idle stream {}",
        micros(per(loading, REPEATS)),
        micros(per(ticking, REPEATS)),
        micros(per(releasing, REPEATS)),
        micros(idle_ns)
    );
    eprintln!(
        "ticks launched one by one: {} per word, {} per tick (synchronized per word); {} per \
         word, {} per tick (back to back)",
        micros(launched_ns),
        tick(launched_ns),
        micros(streamed_ns),
        tick(streamed_ns)
    );
    eprintln!(
        "one graph per word: {} per word, {} per tick (synchronized per word); {} per word, {} \
         per tick (back to back)",
        micros(graphed_ns),
        tick(graphed_ns),
        micros(graph_streamed_ns),
        tick(graph_streamed_ns)
    );
}

/// The Newton–Schulz refinement and the certificate equal the oracle on hand fixtures: ties upward
/// on both signs; the word's edge (`2^63 − 2` admitted, `2^63` refused); the residual's carrier at
/// the declared exponent (`S = 64` admitted, `S = 65` refused, the same words); the bounded
/// product's edge at `S = 126` (`2^127 − 4` admitted, `2^127` refused); and the refusals carried
/// into a second refinement and the certificates.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn newton_schulz_matches_the_oracle_on_small_fixtures() {
    let card = card();
    let m = i64::MAX;
    let pairs = vec![
        // 0, 1: ties. S = 8: A = 2^7, X = ±1: X(2 − AX) is 3/2 or −5/2 units.
        InversePair::new(1, 3, 5, vec![1 << 7], vec![1]).unwrap(),
        InversePair::new(1, 3, 5, vec![1 << 7], vec![-1]).unwrap(),
        // 2, 3: the word's edge: A = 0 doubles the chart.
        InversePair::new(1, 4, 4, vec![0], vec![1 << 62]).unwrap(),
        InversePair::new(1, 4, 4, vec![0], vec![(1 << 62) - 1]).unwrap(),
        // 4, 5: the residual's carrier: bound 2m² + 2^S at the entry (0, 0).
        InversePair::new(2, 32, 32, vec![m, m, 0, 1], vec![m, 0, -m, 1]).unwrap(),
        InversePair::new(2, 33, 32, vec![m, m, 0, 1], vec![m, 0, -m, 1]).unwrap(),
        // 6, 7, 8: the bounded product at S = 126: ρ = 2^126 − AX, ξρ against 2^127.
        InversePair::new(1, 63, 63, vec![0], vec![2]).unwrap(),
        InversePair::new(1, 63, 63, vec![1], vec![2]).unwrap(),
        InversePair::new(1, 63, 63, vec![-1], vec![-2]).unwrap(),
    ];
    let mut expected: Vec<Chart> = pairs.iter().map(Chart::of).collect();
    let mut inverses = ResidentInverses::mount(&card, &pairs).unwrap();
    eprintln!("inverse layouts: {:?}", inverses.layouts());
    for refinement in 0..2 {
        // The certificates of the current charts.
        let certificates = inverses.certificates().unwrap();
        for (g, (pair, chart)) in pairs.iter().zip(&expected).enumerate() {
            let want = oracle::certificate(pair, chart);
            match (&certificates[g], want) {
                (Ok(found), Ok(numerator)) => {
                    assert_eq!(BigInt::from(found.numerator()), numerator, "pair {g}");
                    assert_eq!(found.exponent(), pair.shift());
                }
                (Err(found), Err(refusal)) => assert_eq!(*found, refusal, "pair {g}"),
                (found, want) => panic!("pair {g}: {found:?} against {want:?}"),
            }
        }
        // The residual itself.
        let (residual, status) = inverses.residual_words().unwrap();
        let mut at = 0;
        for (pair, chart) in pairs.iter().zip(&expected) {
            for (value, refusal) in oracle::residual(pair, chart) {
                assert_eq!(
                    (
                        BigInt::from(residual[at]),
                        Refusal::of_status(status[at]).unwrap()
                    ),
                    (value, refusal),
                    "residual entry {at}, refinement {refinement}"
                );
                at += 1;
            }
        }
        inverses.refine().unwrap();
        let charts = inverses.charts().unwrap();
        for (g, pair) in pairs.iter().enumerate() {
            let (next, discarded) = oracle::refine(pair, &expected[g]);
            assert!(discarded * 2 <= BigInt::one() << pair.shift() as usize);
            let found = Chart {
                words: charts.chart(g).to_vec(),
                status: charts
                    .status(g)
                    .iter()
                    .map(|s| Refusal::of_status(*s).unwrap())
                    .collect(),
            };
            assert_eq!(found, next, "pair {g}, refinement {refinement}");
            expected[g] = next;
        }
        if refinement == 0 {
            // The hand expectations of the first refinement.
            let first: Vec<(i64, Option<Refusal>)> = (0..pairs.len())
                .map(|g| (expected[g].words[0], expected[g].status[0]))
                .collect();
            assert_eq!(first[0], (2, None));
            assert_eq!(first[1], (-2, None));
            assert_eq!(first[2], (0, Some(Refusal::Word)));
            assert_eq!(first[3], (i64::MAX - 1, None));
            assert_eq!(first[5].1, Some(Refusal::Operand));
            assert_eq!(first[6], (0, Some(Refusal::Carrier)));
            assert_eq!(first[7], (4, None));
            assert_eq!(first[8], (-4, None));
            assert_eq!(expected[5].status[1], None);
            eprintln!(
                "refused after the first refinement: {:?}",
                charts.refusals().unwrap()
            );
        }
    }
    assert_eq!(inverses.refinements(), 2);
}

/// Campaign 1's inverse charts (the Cayley denominators `1 − E/2` of the rings 10, 14, 22, 26 and
/// the widest 64, `L_A`, `L_c` drawn in `16..=40`, warm-started at `1 + K`): three resident
/// refinements equal the oracle's exactly, charts and certificates; each certificate obeys Lean's
/// `rounded_refinement_certificate`, `‖1 − AX''‖∞ ≤ ‖1 − AX‖∞² + ‖A‖∞·n·2^(−L_c)/2`, and the
/// refinements contract. Drawn words (arithmetic coverage, refusals included) equal the oracle's
/// for one refinement. Measured.
#[test]
#[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
fn newton_schulz_matches_the_oracle_at_campaign_one_shapes() {
    let card = card();
    let mut draw = Draw(1_190);
    for seed in 0..4 {
        let pairs: Vec<InversePair> = RINGS
            .iter()
            .chain(if seed == 0 { &[64usize][..] } else { &[][..] })
            .map(|&n| {
                let (la, lc) = (exponent(&mut draw), exponent(&mut draw));
                cayley_pair(&mut draw, n, la, lc)
            })
            .collect();
        let mut expected: Vec<Chart> = pairs.iter().map(Chart::of).collect();
        let mut inverses = ResidentInverses::mount(&card, &pairs).unwrap();
        let mut before: Vec<Rat> = inverses
            .certificates()
            .unwrap()
            .into_iter()
            .map(|c| c.unwrap().value())
            .collect();
        let opening = before.clone();
        for refinement in 0..3 {
            inverses.refine().unwrap();
            let charts = inverses.charts().unwrap();
            let certificates = inverses.certificates().unwrap();
            for (g, pair) in pairs.iter().enumerate() {
                let (next, _) = oracle::refine(pair, &expected[g]);
                assert_eq!(charts.chart(g), &next.words[..], "seed {seed}, pair {g}");
                assert!(charts.status(g).iter().all(|s| *s == 0));
                expected[g] = next;
                let certificate = certificates[g].unwrap();
                assert_eq!(
                    BigInt::from(certificate.numerator()),
                    oracle::certificate(pair, &expected[g]).unwrap()
                );
                let rounding = oracle::operator_norm(pair)
                    * Rat::new(
                        BigInt::from(pair.width()),
                        BigInt::one() << (pair.chart_exponent() as usize + 1),
                    );
                let bound = &before[g] * &before[g] + rounding;
                assert!(
                    certificate.value() <= bound,
                    "seed {seed}, pair {g}, refinement {refinement}"
                );
                before[g] = certificate.value();
            }
        }
        for (g, (last, first)) in before.iter().zip(&opening).enumerate() {
            assert!(
                last < first,
                "seed {seed}, pair {g}: {last} against {first}"
            );
        }
        if seed == 0 {
            eprintln!(
                "certificates, opening and after three refinements: {:?}",
                opening
                    .iter()
                    .zip(&before)
                    .map(|(a, b)| format!("{a} -> {b}"))
                    .collect::<Vec<_>>()
            );
        }
    }
    // Drawn words: every refusal kind against the oracle, one refinement.
    let mut kinds = [0usize; 4];
    for bits in [20u32, 40, 56, 62] {
        let pairs: Vec<InversePair> = RINGS
            .iter()
            .map(|&n| drawn_pair(&mut draw, n, bits))
            .collect();
        let mut inverses = ResidentInverses::mount(&card, &pairs).unwrap();
        let certificates = inverses.certificates().unwrap();
        inverses.refine().unwrap();
        let charts = inverses.charts().unwrap();
        for (g, pair) in pairs.iter().enumerate() {
            let chart = Chart::of(pair);
            match (&certificates[g], oracle::certificate(pair, &chart)) {
                (Ok(found), Ok(numerator)) => {
                    assert_eq!(BigInt::from(found.numerator()), numerator)
                }
                (Err(found), Err(refusal)) => assert_eq!(*found, refusal),
                (found, want) => panic!("bits {bits}, pair {g}: {found:?} against {want:?}"),
            }
            let (next, _) = oracle::refine(pair, &chart);
            let status: Vec<Option<Refusal>> = charts
                .status(g)
                .iter()
                .map(|s| Refusal::of_status(*s).unwrap())
                .collect();
            assert_eq!(
                (charts.chart(g), &status),
                (&next.words[..], &next.status),
                "bits {bits}, pair {g}"
            );
            for s in &status {
                kinds[match s {
                    None => 0,
                    Some(Refusal::Carrier) => 1,
                    Some(Refusal::Word) => 2,
                    Some(Refusal::Operand) => 3,
                }] += 1;
            }
        }
    }
    eprintln!(
        "drawn refinements: exact {}, carrier {}, word {}, operand {}",
        kinds[0], kinds[1], kinds[2], kinds[3]
    );
    assert!(kinds[0] > 0 && kinds[1] > 0 && kinds[2] > 0 && kinds[3] > 0);

    // The warm start: a deposit moves each operator by a skew D (`A → A + D`), the chart is kept,
    // and its certificate obeys Lean's `warm_start_certificate`, `‖1 − (A + D)X̂‖∞ ≤ ‖1 − AX̂‖∞ +
    // ‖D‖∞‖X̂‖∞`; the next refinement equals the oracle's.
    let mut pairs: Vec<InversePair> = RINGS
        .iter()
        .map(|&n| {
            let (la, lc) = (exponent(&mut draw), exponent(&mut draw));
            cayley_pair(&mut draw, n, la, lc)
        })
        .collect();
    let mut inverses = ResidentInverses::mount(&card, &pairs).unwrap();
    inverses.refine().unwrap();
    inverses.refine().unwrap();
    let settled = inverses.charts().unwrap();
    let before = inverses.certificates().unwrap();
    for (g, pair) in pairs.iter_mut().enumerate() {
        let n = pair.width();
        let mut moved = pair.operator().to_vec();
        let mut deposit = vec![0i64; n * n];
        for i in 0..n {
            for j in i + 1..n {
                let d = draw.signed(pair.operator_exponent() - 12);
                deposit[i * n + j] = d;
                deposit[j * n + i] = -d;
            }
        }
        for (a, d) in moved.iter_mut().zip(&deposit) {
            *a += d;
        }
        inverses.replace_operator(g, &moved).unwrap();
        let chart = settled.chart(g).to_vec();
        let warm = InversePair::new(
            n,
            pair.operator_exponent(),
            pair.chart_exponent(),
            moved,
            chart.clone(),
        )
        .unwrap();
        let norm = |words: &[i64], exponent: u32| -> Rat {
            let largest = (0..n)
                .map(|i| {
                    (0..n)
                        .map(|k| BigInt::from(words[i * n + k]).abs())
                        .sum::<BigInt>()
                })
                .max()
                .unwrap_or_default();
            Rat::new(largest, BigInt::one() << exponent as usize)
        };
        let warm_bound = before[g].unwrap().value()
            + norm(&deposit, pair.operator_exponent()) * norm(&chart, pair.chart_exponent());
        let warm_certificate = oracle::certificate(&warm, &Chart::of(&warm)).unwrap();
        assert!(
            Rat::new(warm_certificate, BigInt::one() << warm.shift() as usize) <= warm_bound,
            "pair {g}"
        );
        *pair = warm;
    }
    let certificates = inverses.certificates().unwrap();
    inverses.refine().unwrap();
    let refined = inverses.charts().unwrap();
    for (g, pair) in pairs.iter().enumerate() {
        assert_eq!(
            BigInt::from(certificates[g].unwrap().numerator()),
            oracle::certificate(pair, &Chart::of(pair)).unwrap()
        );
        let (next, _) = oracle::refine(pair, &Chart::of(pair));
        assert_eq!(refined.chart(g), &next.words[..], "warm pair {g}");
    }

    // Measured after a warm-up: one refinement (residual and refinement) of the four rings'
    // charts, resident, synchronized per refinement and back to back; the certificates with their
    // one transfer.
    const REPEATS: u32 = 1_000;
    for _ in 0..10 * REPEATS {
        inverses.refine().unwrap();
    }
    card.synchronize().unwrap();
    let clock = Instant::now();
    for _ in 0..REPEATS {
        inverses.refine().unwrap();
        card.synchronize().unwrap();
    }
    let refined = clock.elapsed().as_nanos() / u128::from(REPEATS);
    let clock = Instant::now();
    for _ in 0..REPEATS {
        inverses.refine().unwrap();
    }
    card.synchronize().unwrap();
    let streamed = clock.elapsed().as_nanos() / u128::from(REPEATS);
    let clock = Instant::now();
    for _ in 0..REPEATS {
        inverses.refine().unwrap();
        inverses.certificates().unwrap();
    }
    let certified = clock.elapsed().as_nanos() / u128::from(REPEATS);
    eprintln!(
        "inverse charts of the four rings: {} per refinement (residual + refine, synchronized), \
         {} back to back; {} per refinement with its certificate read (one transfer of {} \
         octets); layouts {:?}",
        micros(refined),
        micros(streamed),
        micros(certified),
        2 * 16 * RINGS.len(),
        inverses.layouts()
    );
}
