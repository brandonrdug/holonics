//! The executed growth's covector (`hnn::ring`, "The executed growth's covector"; Lean
//! `HNN/ExecutedComparison`): the executed monodromy's variation through the executed tick and its
//! solve, the certified dominant multiplier and its typed refusals, and the eigen-derivative against
//! the exact variation. The release's own comparison and its committed move are tested beside the
//! bank's generation (`hnn::tests::prediction`). One test per stated law and per refusal.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use crate::hnn::HnnError;
use crate::hnn::ring::{
    CovectorRefusal, MemberCovector, PumpDeclaration, PumpStep, ReceivingBank, ResonatorMaterial,
    dominant_multiplier, growth_of,
};
use crate::holon::parametron::Carrier;
use crate::ratio::algebraic::log2_enclosure;
use crate::ratio::gaussian::GaussianRat;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer, rat};

fn quarter(k: usize) -> Carrier {
    let (cos, sin) = match k % 4 {
        0 => (1, 0),
        1 => (0, 1),
        2 => (-1, 0),
        _ => (0, -1),
    };
    Carrier::new(integer(cos), integer(sin)).unwrap()
}

/// The declared bank: one node `C = I`, `K = I`, `Y = 16`, `h = 1`, four members at `p = 5/8`.
fn declared_bank() -> ReceivingBank {
    let identity = ExactRatMatrix::identity(2).unwrap();
    let material = ResonatorMaterial::new(
        identity.clone(),
        identity,
        ExactRatMatrix::zero(2, 2).unwrap(),
        None,
    )
    .unwrap();
    let members = [
        PumpStep::Stand,
        PumpStep::Quarter,
        PumpStep::Half,
        PumpStep::ThreeQuarters,
    ]
    .into_iter()
    .map(|step| PumpDeclaration::new(rat(5, 8), quarter(0), step).unwrap())
    .collect();
    ReceivingBank::new(material, members, integer(16), Rat::one(), 6).unwrap()
}

/// A drawn turn on the dyadic lattice `2^(−bits − 1)`, within `[−scale/2, scale/2]` a coordinate.
fn drawn(seed: u64, ticks: usize, bits: u32, scale: i64) -> Vec<GaussianRat> {
    let mut draw = crate::holarchy::terrain::Draw::new(seed);
    let unit = BigInt::one() << (bits + 1);
    let mut coordinate = || {
        let n = draw.below(1 << bits) as i64 - (1 << (bits - 1));
        Rat::new(BigInt::from(n * scale), unit.clone())
    };
    (0..ticks)
        .map(|_| GaussianRat::new(coordinate(), coordinate()))
        .collect()
}

fn shifted(turn: &[GaussianRat], direction: &[GaussianRat], by: &Rat) -> Vec<GaussianRat> {
    turn.iter()
        .zip(direction)
        .map(|(z, d)| z.add(&d.scale(by)))
        .collect()
}

fn largest(matrix: &ExactRatMatrix) -> Rat {
    matrix
        .entries()
        .iter()
        .map(|x| x.abs())
        .max()
        .unwrap_or_else(Rat::zero)
}

/// **The monodromy's variation, forward and in reverse, is the executed monodromy's derivative**
/// (`ReceivingBank::turn_variation`): the dual product and the prefix–suffix sum
/// `Σ_t T_(>t) ΔT_t T_(<t)` are equal exactly, and against the executed monodromy read at
/// `z ± ηδ` (an independent exact route through the executed solve) the central difference's
/// residual `M(z + ηδ) − M(z − ηδ) − 2ηΔM` is of third order: halving `η` divides it by at least
/// four.
#[test]
fn the_monodromys_variation_is_its_derivative_forward_and_in_reverse() {
    let bank = declared_bank();
    for seed in [3u64, 11] {
        let turn = drawn(seed, 8, 6, 2);
        let direction = drawn(seed + 100, 8, 6, 1);
        for member in 0..4 {
            let variation = bank.turn_variation(member, &turn, &direction).unwrap();
            assert_eq!(variation.forward, variation.reverse);
            let residual = |eta: &Rat| -> Rat {
                let up = bank
                    .turn_variation(member, &shifted(&turn, &direction, eta), &direction)
                    .unwrap()
                    .monodromy;
                let down = bank
                    .turn_variation(member, &shifted(&turn, &direction, &-eta.clone()), &direction)
                    .unwrap()
                    .monodromy;
                largest(
                    &up.subtract(&down)
                        .unwrap()
                        .subtract(&variation.forward.scaled(&(integer(2) * eta)))
                        .unwrap(),
                )
            };
            let (coarse, fine) = (residual(&rat(1, 1 << 10)), residual(&rat(1, 1 << 11)));
            assert!(fine.is_positive() && fine * integer(4) <= coarse);
        }
    }
}

/// **The dominant multiplier is certified, or refused by type** (`hnn::ring::dominant_multiplier`),
/// on characteristic polynomials of known roots: a simple real root (`5`), a simple conjugate pair
/// (`1 ± 5i`, the disk off the axis and disjoint from its conjugate), a tie in modulus (`±5`), and
/// a double root (`5, 5`).
#[test]
fn the_dominant_multiplier_is_certified_or_refused_by_type() {
    let expand = |roots: &[i64], quadratic: Option<(i64, i64)>| -> Vec<BigInt> {
        let mut coefficients = vec![BigInt::one()];
        let mut multiply = |factor: &[i64]| {
            let mut next = vec![BigInt::from(0); coefficients.len() + factor.len() - 1];
            for (i, a) in coefficients.iter().enumerate() {
                for (j, b) in factor.iter().enumerate() {
                    next[i + j] += a * BigInt::from(*b);
                }
            }
            coefficients = next;
        };
        for root in roots {
            multiply(&[-root, 1]);
        }
        if let Some((b, c)) = quadratic {
            multiply(&[c, b, 1]);
        }
        coefficients
    };
    let scale = BigInt::one();
    let read = |c: &[BigInt]| {
        let growth = growth_of(c, &scale, 24);
        dominant_multiplier(c, &scale, &growth).unwrap()
    };
    let real = read(&expand(&[5, 2, -1, 3], None)).unwrap();
    assert!(!real.pair);
    assert!(real.disk.center.is_real());
    let distance = real.disk.center.sub(&GaussianRat::real(integer(5))).norm_sq();
    assert!(distance <= &real.disk.radius * &real.disk.radius);
    assert!(real.inner > integer(3) && real.inner < integer(5));
    let pair = read(&expand(&[1, -2], Some((-2, 26)))).unwrap();
    assert!(pair.pair);
    let distance = pair.disk.center.sub(&GaussianRat::from_i64(1, 5)).norm_sq();
    assert!(distance <= &pair.disk.radius * &pair.disk.radius);
    assert_eq!(read(&expand(&[5, -5, 1, 2], None)), Err(CovectorRefusal::Tie));
    assert_eq!(read(&expand(&[5, 5, 1, -2], None)), Err(CovectorRefusal::Collision));
}

/// **A reading has the lattice's floor** (Lean `HNN/Floquet.integer_monodromy_floor`): on `M = N/Δ`
/// with `Δ = 4`, the nilpotent `N = [[0, 1], [0, 0]]` (`det(ν − N) = ν²`) reads the floor's cell
/// `[0, 1/4)` without bisecting toward zero, and `N = [[1, 0], [0, 0]]` (`ν² − ν`, `ρ(M) = 1/4`)
/// reads a cell whose lower end is within the grain of `1/4`.
#[test]
fn a_reading_is_zero_or_past_the_lattices_floor() {
    let scale = BigInt::from(4);
    let nilpotent = growth_of(&[BigInt::zero(), BigInt::zero(), BigInt::one()], &scale, 24);
    assert_eq!(nilpotent.lower, Rat::zero());
    assert_eq!(nilpotent.upper, rat(1, 4));
    let floor = growth_of(&[BigInt::zero(), -BigInt::one(), BigInt::one()], &scale, 24);
    assert!(floor.lower <= rat(1, 4) && rat(1, 4) < floor.upper);
    assert!(floor.lower >= rat(1, 4) * (Rat::one() - rat(1, 1 << 24)));
}

/// **The covector pairs with the exact variation, three ways** (`ReceivingBank::directional_routes`):
/// on drawn turns below and past the bifurcation (8 crossings, and 60 crossings, the order-2
/// ring's period, with amplitudes on `2^(−22)`) and drawn moves, every resolved member's covector
/// paired with the move, the eigen-pairing `Re(ℓᵀΔMr/(μℓᵀr))` on the exact forward variation, and
/// the trace `Re(tr(adj(μ − M)ΔM)/(μχ′(μ)))` share a point, and each enclosure is narrower than
/// `2^(−32)`: the passage keeps the covector tight, not merely overlapping.
#[test]
fn the_covector_pairs_with_the_exact_variation_three_ways() {
    let bank = declared_bank();
    let tight = rat(1, 1 << 32);
    let mut resolved = 0;
    for (seed, ticks, bits, scale) in [(5u64, 8, 6, 1i64), (7, 8, 6, 4), (13, 8, 6, 6), (41, 60, 21, 2)] {
        let turn = drawn(seed, ticks, bits, scale);
        let direction = drawn(seed + 1000, ticks, bits, 1);
        for member in 0..4 {
            if let Some(routes) = bank.directional_routes(member, &turn, &direction, 16).unwrap() {
                assert!(routes.agree(), "{routes:?}");
                for route in [&routes.covector, &routes.eigen, &routes.trace] {
                    assert!(&route.upper - &route.lower < tight, "{routes:?}");
                }
                resolved += 1;
            }
        }
    }
    assert!(resolved >= 8);
}

/// **The covector predicts the executed growth's change** (the finite difference, an independent
/// exact route): at a drawn turn past the bifurcation, the active member's `log₂ ρ` read by its
/// exact enclosure at `z ± ηδ` (grain `2^(−40)`) moves by `2η·D/ln 2` to within an eighth, `D` the
/// covector paired with `δ`.
#[test]
fn the_covector_predicts_the_executed_growths_change() {
    let bank = declared_bank();
    let turn = drawn(21, 8, 6, 6);
    let direction = drawn(22, 8, 6, 1);
    let covector = bank.read_turn_covector(&turn, 16).unwrap();
    let MemberCovector::Resolved {
        member, covector, ..
    } = covector.active[0].clone()
    else {
        panic!("a resolved member");
    };
    // The covector's own pairing with the move, at its enclosures' lower ends.
    let derivative: Rat = covector
        .iter()
        .zip(&direction)
        .map(|([re, im], delta)| &re.lower * &delta.re + &im.lower * &delta.im)
        .sum();
    let eta = rat(1, 1 << 14);
    let growth = |z: &[GaussianRat]| bank.read_turn(z, 40).unwrap().members[member].clone();
    let up = growth(&shifted(&turn, &direction, &eta));
    let down = growth(&shifted(&turn, &direction, &-eta.clone()));
    let lower = log2_enclosure(&(&up.lower / &down.upper)).unwrap().lower;
    let upper = log2_enclosure(&(&up.upper / &down.lower)).unwrap().upper;
    // ln 2 ∈ (693/1000, 694/1000): the predicted log₂ move 2ηD/ln 2.
    let ln2 = (rat(693, 1000), rat(694, 1000));
    let predicted = integer(2) * &eta * &derivative;
    let (low, high) = if predicted.is_positive() {
        (&predicted / &ln2.1, &predicted / &ln2.0)
    } else {
        (&predicted / &ln2.0, &predicted / &ln2.1)
    };
    let slack = predicted.abs() / integer(8);
    assert!(upper >= low - &slack && lower <= high + slack, "{lower} {upper} {predicted}");
}

/// **A station's predicates are read exactly, or left undecided** (`hnn::executed`, "The
/// comparison"): on enclosures of the target and its rivals, the class holds when the target's lower
/// end exceeds every rival's upper, fails when a rival's lower end reaches the target's upper, and is
/// undecided on an overlap; the threshold holds past one, fails at or below it, and is undecided on
/// an enclosure straddling one; the term `f = max(max ln(a_x/a_t), −ln a_t)` is negative exactly when
/// both hold.
#[test]
fn a_stations_predicates_are_read_exactly_or_left_undecided() {
    use crate::hnn::executed::{Predicate, station_predicates};
    use crate::hnn::ring::Growth;
    let g = |lower: Rat, upper: Rat| Growth { lower, upper };
    let read = |joints: &[Growth]| station_predicates(joints, 0).unwrap();
    let (value, class, threshold) = read(&[g(integer(3), integer(4)), g(integer(1), integer(2))]);
    assert_eq!((class, threshold), (Predicate::Holds, Predicate::Holds));
    assert!(value.upper.is_negative());
    let (value, class, threshold) = read(&[g(rat(1, 2), rat(3, 4)), g(rat(1, 8), rat(1, 4))]);
    assert_eq!((class, threshold), (Predicate::Holds, Predicate::Fails));
    assert!(value.lower.is_positive());
    let (_, _, threshold) = read(&[g(rat(7, 8), rat(9, 8)), g(rat(1, 8), rat(1, 4))]);
    assert_eq!(threshold, Predicate::Undecided);
    let (_, class, _) = read(&[g(integer(4), integer(6)), g(integer(3), integer(5))]);
    assert_eq!(class, Predicate::Undecided);
    let (value, class, _) = read(&[g(integer(4), integer(6)), g(integer(7), integer(8))]);
    assert_eq!(class, Predicate::Fails);
    assert!(value.lower.is_positive());
}

/// **Two members tied in growth are both active branches** (the max comparison's active set): on the
/// spectral line of 8 unit cells, the two quarter-turn neighbours read `[1061/16, 531/8]` each, so
/// both reach the joint's lower end and both return a covector.
#[test]
fn two_members_tied_in_growth_are_both_active() {
    let bank = declared_bank();
    let line: Vec<GaussianRat> = (0..8).map(|t| quarter(4 * 8 - t % 4).as_gaussian()).collect();
    let covector = bank.read_turn_covector(&line, 10).unwrap();
    let members: Vec<usize> = covector.active.iter().map(MemberCovector::member).collect();
    assert_eq!(members.len(), 2);
    assert_eq!(
        covector.reading.members[members[0]],
        covector.reading.members[members[1]]
    );
    assert!(covector
        .active
        .iter()
        .all(|member| matches!(member, MemberCovector::Resolved { .. })));
}

/// The released code length's excursion (`HNN/ExecutedComparison` §12, `checkpoint_one_iff`,
/// `excursion_enclosure`): strict descent is the decrease by disjoint enclosures; a held opening
/// state with a height admits a rise below its lower end plus the height and refuses one at or
/// above it; an interval closes only strictly below its opening state less the certified decrease.
#[test]
fn the_monotone_excursion_is_the_strict_decrease_and_a_height_admits_a_bounded_rise() {
    use crate::hnn::executed::ReleaseExcursion;
    use crate::ratio::algebraic::ExactInterval;
    let interval = |lower: i64, upper: i64| ExactInterval {
        lower: integer(lower),
        upper: integer(upper),
    };
    let before = interval(10, 11);
    let monotone = ReleaseExcursion::monotone();
    for upper in 7..14 {
        let own = interval(upper - 1, upper);
        assert_eq!(monotone.admits(&before, &own), own.upper < before.lower);
    }
    let excursion = ReleaseExcursion {
        checkpoint: Some(interval(9, 10)),
        height: Some(integer(3)),
    };
    assert!(excursion.admits(&before, &interval(10, 11)));
    assert!(!excursion.admits(&before, &interval(11, 12)));
    assert!(
        ReleaseExcursion::from_checkpoint(interval(9, 10)).admits(&before, &interval(99, 100))
    );
    let checkpoint = interval(9, 10);
    assert_eq!(ReleaseExcursion::closes(&checkpoint, &interval(5, 6), &integer(2)), Ok(true));
    assert_eq!(ReleaseExcursion::closes(&checkpoint, &interval(6, 7), &integer(2)), Ok(false));
    // A negative decrease would close an interval above its opening state, and a negative height
    // states no `CheckpointGuard` (the opening state itself would breach its excursion): both are
    // refused.
    assert_eq!(
        ReleaseExcursion::closes(&checkpoint, &interval(9, 10), &integer(-2)),
        Err(HnnError::WindowDecrease {
            decrease: integer(-2)
        })
    );
    assert!(monotone.checked().is_ok() && excursion.checked().is_ok());
    assert!(ReleaseExcursion::from_checkpoint(checkpoint.clone()).checked().is_ok());
    let sunk = ReleaseExcursion {
        checkpoint: None,
        height: Some(integer(-1)),
    };
    assert_eq!(
        sunk.checked(),
        Err(HnnError::ExcursionHeight {
            height: integer(-1)
        })
    );
    // One grain of `1/16` bit over 64 decisions is `4 ln 2` nats, read above `ln 2`.
    let grain = ReleaseExcursion::grain(64, &rat(1, 16)).unwrap();
    assert!(grain > rat(2772, 1000) && grain < rat(2773, 1000));
}
