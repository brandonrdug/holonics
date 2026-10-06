//! The executed growth's covector (`hnn::ring`, "The executed growth's covector"; Lean
//! `HNN/ExecutedComparison`): the executed monodromy's variation through the executed tick and its
//! solve, the certified dominant multiplier and its typed refusals, and the eigen-derivative against
//! the exact variation; the located pair's deposit (`hnn::executed`, S2) and the complete continuing
//! state of a deposited constitution, restored and continued exactly. One test per stated law and
//! per refusal.

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
pub(super) fn declared_bank() -> ReceivingBank {
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

// -------------------------------------------------------------------------------------------
// the located pair's deposit (lane B, October 5)

/// A field of one closing ring of period 16, its lock every port, over an exterior chart of
/// `alphabet` classes (one class a port when `alphabet ≤ 16`).
pub(super) fn pair_field(alphabet: usize) -> crate::hnn::field::Field {
    use crate::hnn::field::{CribDeclaration, Field, FieldDeclaration, ReceiverDeclaration};
    Field::declare(
        FieldDeclaration {
            rings: vec![super::support::ring(16, (0..16).collect())],
            contacts: Vec::new(),
            loops: Vec::new(),
            sources: vec![0],
            offsets: Vec::new(),
            alphabet,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: 0,
                aperture: 1,
                tolerance: rat(1, 16),
                depth: 1,
                prior: crate::compression::landmark::context::StopPrior::half(),
                mass: 1,
                base: crate::compression::landmark::context::BaseMeasure::Even,
                receiving_prior: 0,
            }],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 24,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap()
}

/// The order-2 pair the menu locates: distance 2, `y ↦ y + 1` on four symbols, turns of order 4.
pub(super) fn order_two_pair() -> crate::hnn::keys::LocatedPair {
    crate::hnn::keys::LocatedPair {
        offset: 2,
        map: vec![(0, 1), (1, 2), (2, 3), (3, 0)],
        cycle: 4,
        turns: vec![4, 12],
    }
}

/// [implemented-exact] **The located pair's deposit closes its slip, and its consumer holds**: on
/// the declared opening the slip `Δ_y = U B e_y − (E − B) e_(f(y))` is the carried prior, the
/// normal law's unit step closes half of it (the one-hot Gram `I + e eᵀ`), the library's certified
/// step on the quadratic slip is `η = 2` with its certified decrease the whole slip, and after the deposit `(E − B) T = U B` holds exactly on the menu's classes:
/// each consequence's column is its own prior plus its antecedent's prior carried two ticks. The
/// classes the key does not reach keep their prior. A second deposit of the same pair finds no slip
/// and is refused (the key is retained once, never counted).
#[test]
fn the_located_pairs_deposit_closes_its_slip_and_its_consumer_holds() {
    use crate::hnn::constitution::{CAMPAIGN_ONE_BUDGET, Constitution};
    use crate::hnn::executed::pair_deposit;
    use crate::hnn::field::ConstitutionRead;
    let field = pair_field(6);
    let opening = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
    let prior = opening.source_port(0).unwrap().clone();
    let (theta, deposit) = pair_deposit(&field, &opening, &prior, 0, &order_two_pair()).unwrap();
    // The slip's certified step: a = 2⟨Δ, D⟩ = 2·16, C = 2|D|² = 2·8, c = ½: η = 2 = a/C exactly,
    // and the certified decrease ½ η a = 32 is the whole slip.
    assert_eq!(deposit.certificate.step, integer(2));
    assert!(deposit.certificate.holds());
    assert_eq!(deposit.certificate.decrease(), integer(32));
    assert!(deposit.consumer);
    assert!(deposit.slip_after.is_zero());
    // Four classes of 32 entries ±½: the carried prior's squared norm.
    assert_eq!(deposit.slip_before, integer(32));
    let port = theta.source_port(0).unwrap();
    let ring = field.ring(0);
    for (y, x) in [(0usize, 1usize), (1, 2), (2, 3), (3, 0)] {
        let column = |m: &ExactRatMatrix, c: usize| -> Vec<Rat> {
            (0..m.rows()).map(|r| m.get(r, c).unwrap().clone()).collect()
        };
        let carried = ring.rotate(&column(&prior, y), &BigInt::from(2));
        let expected: Vec<Rat> = column(&prior, x).iter().zip(&carried).map(|(b, u)| b + u).collect();
        assert_eq!(column(port, x), expected);
    }
    for unreached in [4usize, 5] {
        for row in 0..port.rows() {
            assert_eq!(port.get(row, unreached).unwrap(), prior.get(row, unreached).unwrap());
        }
    }
    assert!(matches!(
        pair_deposit(&field, &theta, &prior, 0, &order_two_pair()),
        Err(HnnError::Shape { .. })
    ));
}

/// [implemented-exact] **A located port must hold one class of the encoding**: each class is its
/// own port (THE_MACHINE guard 9; the residue chart that put classes 0 and 16 at one port of a
/// period-16 ring is deleted), so a port holds at most one; on two classes over a ring of period 16
/// the order-2 pair's ports 2 and 3 hold none, the located map on ports is not a map of classes and
/// the deposit is refused.
#[test]
fn a_port_holding_no_class_refuses_the_pair_deposit() {
    use crate::hnn::constitution::{CAMPAIGN_ONE_BUDGET, Constitution};
    use crate::hnn::executed::pair_deposit;
    use crate::hnn::field::ConstitutionRead;
    let field = pair_field(2);
    let opening = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
    let prior = opening.source_port(0).unwrap().clone();
    assert!(matches!(
        pair_deposit(&field, &opening, &prior, 0, &order_two_pair()),
        Err(HnnError::Shape { expected: 1, found: 0, .. })
    ));
}

// -------------------------------------------------------------------------------------------
// the continuing state of a deposited constitution

/// A located pair on the joint field's ring 0 at distance `offset`, its map on ports (each of the
/// three classes at its own port).
fn joint_pair(offset: usize, map: &[(usize, usize)]) -> crate::hnn::keys::LocatedPair {
    crate::hnn::keys::LocatedPair {
        offset,
        map: map.to_vec(),
        cycle: map.len() as u64,
        turns: Vec::new(),
    }
}

/// The successive receptions' located pairs: a 3-cycle at distance 1, the swap of two classes at
/// distance 2, and the inverse 3-cycle at distance 3.
fn joint_pairs() -> [crate::hnn::keys::LocatedPair; 3] {
    [
        joint_pair(1, &[(0, 1), (1, 2), (2, 0)]),
        joint_pair(2, &[(0, 1), (1, 0)]),
        joint_pair(3, &[(0, 2), (1, 0), (2, 1)]),
    ]
}

/// The joint field's opening at the modulus `3/4` and its source port, the deposits' declared prior.
fn joint_opening(
    field: &crate::hnn::field::Field,
    seed: u64,
) -> (crate::hnn::constitution::Constitution, ExactRatMatrix) {
    use crate::hnn::field::ConstitutionRead;
    let opening = super::learning::generic(field, seed).with_transport(0, rat(3, 4)).unwrap();
    let prior = opening.source_port(0).unwrap().clone();
    (opening, prior)
}

/// [implemented-exact] **A restored checkpoint continues exactly, over successive deposits**: after
/// one located pair's deposit, the complete continuing state written as text and restored onto the
/// declared opening is the continued constitution exactly (the port, the carried Gram, the chart,
/// the remainders, the modulus, the clock, the commit and the storage product); then over two
/// further located pairs the restored and the continued constitutions read the same slips and make
/// the same deposits (each certified step and carried source step), the same clock and the same
/// subsequent state. A remount of `E` and `ρ` alone is partial: its text has no state and is refused
/// as a continuing state, its constitution loses the Gram, and its next deposit reads the same slip
/// and deposits otherwise.
#[test]
fn a_restored_checkpoint_continues_exactly_over_successive_deposits() {
    use crate::hnn::constitution::{ContinuingState, Locus};
    use crate::hnn::executed::pair_deposit;
    use crate::hnn::field::ConstitutionRead;
    let field = super::prediction::joint();
    let (opening, prior) = joint_opening(&field, 94);
    let pairs = joint_pairs();
    let (continued, first) = pair_deposit(&field, &opening, &prior, 0, &pairs[0]).unwrap();
    assert!(first.certificate.holds() && first.slip_after < first.slip_before);
    let locus = Locus::SourcePort(0);
    assert!(continued.clock(locus) >= 1);
    let text = continued.continuing_state(0).unwrap().to_text();
    let state = ContinuingState::from_text(&text).unwrap();
    assert_eq!(state, continued.continuing_state(0).unwrap());
    let restored = opening.clone().continued(&state).unwrap();
    assert_eq!(restored, continued);
    let (mut a, mut b) = (continued.clone(), restored);
    for pair in &pairs[1..] {
        let (sa, da) = pair_deposit(&field, &a, &prior, 0, pair).unwrap();
        let (sb, db) = pair_deposit(&field, &b, &prior, 0, pair).unwrap();
        assert_eq!(da, db);
        assert_eq!(sa.clock(locus), sb.clock(locus));
        assert_eq!(sa, sb);
        a = sa;
        b = sb;
        let state = a.continuing_state(0).unwrap();
        assert_eq!(ContinuingState::from_text(&state.to_text()).unwrap(), state);
    }
    // The partial remount: E and ρ alone.
    let rows = continued.source_port(0).unwrap().rows();
    let partial_text: String = text
        .lines()
        .take(rows + 2)
        .map(|line| format!("{line}\n"))
        .collect();
    assert!(matches!(
        ContinuingState::from_text(&partial_text),
        Err(HnnError::ContinuingState { .. })
    ));
    let partial = opening
        .clone()
        .with_ports(0, None, Some(continued.source_port(0).unwrap().clone()), None)
        .unwrap()
        .with_transport(0, continued.transport(0))
        .unwrap();
    assert_ne!(partial, continued);
    assert_ne!(
        partial.source_law(0).unwrap().gram(),
        continued.source_law(0).unwrap().gram()
    );
    let (p, dp) = pair_deposit(&field, &partial, &prior, 0, &pairs[1]).unwrap();
    let (c, dc) = pair_deposit(&field, &continued, &prior, 0, &pairs[1]).unwrap();
    assert_eq!(dp.slip_before, dc.slip_before);
    assert_ne!(dp.source, dc.source);
    assert_ne!(p, c);
    // A checkpoint is refused onto a constitution that is not the declared opening.
    assert!(matches!(
        continued.clone().continued(&continued.continuing_state(0).unwrap()),
        Err(HnnError::ContinuingState { .. })
    ));
}

/// [implemented-exact] **A restored checkpoint authenticates the declared material it continues and
/// refuses damage**: a state carries the identity of its opening's declared material
/// ([`crate::hnn::constitution::Constitution::material_identity`]) and a check over its text. The
/// state carries every learned value whole, so an opening founded from another seed (the same
/// declared material, other learned founding values) restores it to the same constitution, while an
/// opening of another declared material (here another budget) is refused, and a text damaged in
/// one byte is refused before it mounts.
#[test]
fn a_checkpoint_is_refused_onto_foreign_material_and_when_damaged() {
    use super::learning::{OPEN_BUDGET, generic_within};
    use crate::hnn::constitution::ContinuingState;
    use crate::hnn::executed::pair_deposit;
    let field = super::prediction::joint();
    let (opening, prior) = joint_opening(&field, 94);
    let (reseeded, _) = joint_opening(&field, 95);
    let foreign = generic_within(&field, 94, OPEN_BUDGET - 1)
        .with_transport(0, rat(3, 4))
        .unwrap();
    assert_ne!(opening, reseeded);
    assert_eq!(opening.material_identity(), reseeded.material_identity());
    assert_ne!(opening.material_identity(), foreign.material_identity());
    let (continued, _) = pair_deposit(&field, &opening, &prior, 0, &joint_pairs()[0]).unwrap();
    // No deposit changes the declared material.
    assert_eq!(continued.material_identity(), opening.material_identity());
    let text = continued.continuing_state(0).unwrap().to_text();
    let state = ContinuingState::from_text(&text).unwrap();
    assert_eq!(opening.clone().continued(&state).unwrap(), continued);
    assert_eq!(reseeded.clone().continued(&state).unwrap(), continued);
    assert!(matches!(
        foreign.clone().continued(&state),
        Err(HnnError::ContinuingState { what }) if what.contains("another opening")
    ));
    // One byte of the port's first row changed, still a well-formed rational: refused by the check.
    let row = text.lines().nth(1).expect("the port's first row");
    let at = text.find(row).expect("the row") + row.find(|c: char| c.is_ascii_digit()).expect("a digit");
    let mut damaged = text.clone().into_bytes();
    damaged[at] = if damaged[at] == b'7' { b'8' } else { b'7' };
    let damaged = String::from_utf8(damaged).unwrap();
    assert_ne!(damaged, text);
    assert!(matches!(
        ContinuingState::from_text(&damaged),
        Err(HnnError::ContinuingState { what }) if what.contains("damaged")
    ));
    // A changed material line is caught by the check as well.
    let material = format!("material {}", opening.material_identity());
    let relabelled = text.replace(&material, &format!("material {}", foreign.material_identity()));
    assert_ne!(relabelled, text);
    assert!(ContinuingState::from_text(&relabelled).is_err());
}

/// [implemented-exact; the reception carry §2.4] **A continuing state carries the reception's end
/// inside its check**: a state written with a carried end reads back whole (every storage wave,
/// arriving pair and contact state, and the elapsed ticks), a state at rest writes no carry and
/// reads back at rest (every state written before the carry), the carry is resident motion that
/// [`crate::hnn::constitution::Constitution::continued`] does not read, the stamp still replaces
/// only what follows the storage product, and one byte changed inside the carry is refused as
/// damage. Under the default reception a saved state mounts through one owner
/// (`Reference::mount_continued`, the reception carry §8).
#[test]
fn a_continuing_state_carries_the_receptions_end_inside_its_check() {
    use super::learning::{OPEN_BUDGET, generic_within};
    use crate::hnn::constitution::ContinuingState;
    use crate::hnn::executed::pair_deposit;
    use crate::hnn::field::Current;
    use crate::hnn::reference::{Reception, Reference};
    use crate::hnn::word::{EndChange, ReceptionCarry};
    let field = super::prediction::joint();
    let (opening, prior) = joint_opening(&field, 94);
    let (continued, _) = pair_deposit(&field, &opening, &prior, 0, &joint_pairs()[0]).unwrap();
    let at_rest = continued.continuing_state(0).unwrap();
    assert!(at_rest.carry().is_none());
    assert!(!at_rest.to_text().contains("\ncarry "));
    // A carried end of the field's shape, every value a distinct exact rational.
    let mut k = 0i64;
    let mut wave = |n: usize| -> Vec<Rat> {
        (0..n)
            .map(|_| {
                k += 1;
                rat(if k % 2 == 0 { -k } else { k }, 2 * k + 1)
            })
            .collect()
    };
    let widths: Vec<usize> = field.rings().iter().map(|ring| ring.width()).collect();
    let storage = widths.iter().map(|n| wave(*n)).collect();
    let arrivals = field
        .contacts()
        .iter()
        .map(|contact| {
            let (a, b) = contact.ends();
            [wave(widths[a]), wave(widths[b])]
        })
        .collect();
    let states = field
        .contacts()
        .iter()
        .map(|contact| [wave(contact.width()), wave(contact.width())])
        .collect();
    let momenta = field.contacts().iter().map(|contact| wave(contact.width())).collect();
    let conductances = (0..field.contacts().len())
        .map(|a| rat(2 * a as i64 + 3, 4))
        .collect();
    let carry = ReceptionCarry {
        change: EndChange {
            storage,
            arrivals,
            states,
            resonators: vec![None, Some([wave(2), wave(2)])],
            resonator_phases: vec![None, Some(3)],
        },
        ticks: 27,
        conductances,
        momenta,
        resonator_momenta: vec![None, Some(wave(2))],
    };
    assert!(carry.fits(&field));
    let carried = at_rest.clone().with_carry(Some(carry.clone()));
    let text = carried.to_text();
    let read = ContinuingState::from_text(&text).unwrap();
    assert_eq!(read, carried);
    assert_eq!(read.carry(), Some(&carry));
    assert_eq!(opening.clone().continued(&read).unwrap(), continued);
    // The stamp replaces only what follows the storage product, so the carry stays inside it.
    let stamped = ContinuingState::stamped(&text, &opening).unwrap();
    assert_eq!(stamped, text);
    // One byte inside the carry changed: refused by the check.
    let at = text.find("\ncarry ").unwrap() + "\ncarry ".len();
    let mut damaged = text.clone().into_bytes();
    damaged[at] = if damaged[at] == b'7' { b'8' } else { b'7' };
    let damaged = String::from_utf8(damaged).unwrap();
    assert!(matches!(
        ContinuingState::from_text(&damaged),
        Err(HnnError::ContinuingState { what }) if what.contains("damaged")
    ));
    // A state at rest mounts with no carry, so its next reception opens with zero carry; a carried
    // state mounts its end beside the continued constitution; another declared material is
    // refused; a carried state is refused by a reference declared at rest.
    let current = Current::at_rest(&field);
    let reference = Reference::campaign_one();
    assert_eq!(reference.reception(), Reception::Carry(crate::hnn::Absorption::Nothing));
    let rested = reference
        .mount_continued(&field, &current, opening.clone(), &at_rest)
        .unwrap();
    assert!(rested.carried().is_none());
    assert_eq!(rested.constitution(), &continued);
    let resumed = reference
        .mount_continued(&field, &current, opening.clone(), &read)
        .unwrap();
    assert_eq!(resumed.carried(), Some(&carry));
    assert_eq!(resumed.constitution(), &continued);
    assert!(matches!(
        reference.mount_continued(&field, &current, generic_within(&field, 94, OPEN_BUDGET - 1), &at_rest),
        Err(HnnError::ContinuingState { .. })
    ));
    assert!(matches!(
        reference
            .with_reception(Reception::Rest)
            .mount_continued(&field, &current, opening.clone(), &read),
        Err(HnnError::ContinuingState { .. })
    ));
}
