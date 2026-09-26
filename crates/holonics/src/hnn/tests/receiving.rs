//! The receiving phases: the grain derived from the receiver, the observability refusal, the exact
//! grain reading, the read through `R P_R^(τ_R)`, and the standing read of the bound harmonic
//! coordinate (Decision 26).

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::learning::chain;
use super::support::{Draw, Medium, Parts, lift, small_field};
use crate::hnn::HnnError;
use crate::hnn::constitution::{CAMPAIGN_ONE_BUDGET, Constitution, Steps};
use crate::hnn::field::{ConstitutionRead, Current, Field, FieldDeclaration, ReceiverDeclaration};
use crate::hnn::receiving::{GrainCell, ReceivingPhases, standing_energy, standing_return};
use crate::ratio::{Rat, integer, rat};

/// `L_R = ⌈1/ε_bits⌉` (R2 M2): the chain control's tolerance of 1/16 bit (campaign 1's) gives 16,
/// and 3/40 gives 14; the first epoch is the front's hop distance, and the observability rank is
/// reported and covers `A`.
#[test]
fn the_grain_is_derived_from_the_receivers_code_tolerance() {
    let field = &chain();
    let medium = Medium::initial(field, 4);
    let current = Current::at_rest(field);
    let phases = ReceivingPhases::declare(field, &medium, &current, &field.receivers()[0]).unwrap();
    assert_eq!(phases.grain(), 16);
    assert_eq!(phases.first_epoch(), 2);
    assert_eq!(phases.epochs(), 2..4);
    assert!(phases.rank() >= phases.aperture());
    let coarse = ReceiverDeclaration {
        ring: 2,
        aperture: 2,
        tolerance: rat(3, 40),
    };
    assert_eq!(
        ReceivingPhases::declare(field, &medium, &current, &coarse)
            .unwrap()
            .grain(),
        14
    );
    let none = ReceiverDeclaration {
        tolerance: Rat::zero(),
        ..coarse
    };
    assert!(matches!(
        ReceivingPhases::declare(field, &medium, &current, &none),
        Err(HnnError::Tolerance { .. })
    ));
}

/// Review C7: an aperture beyond the receiving ring's observability rank over the word is refused,
/// and the rank is reported. A period-2 source ring injects at most 4 directions.
#[test]
fn an_aperture_beyond_the_observability_rank_is_refused() {
    let field = small_field(&[2, 3], vec![super::support::contact(0, 1, 1, 0)], 1);
    let medium = Medium::generic(&field, 7, Parts::default());
    let current = Current::at_rest(&field);
    let wide = ReceiverDeclaration {
        ring: 1,
        aperture: 5,
        tolerance: rat(1, 16),
    };
    match ReceivingPhases::declare(&field, &medium, &current, &wide) {
        Err(HnnError::Observability { aperture, rank }) => {
            assert_eq!(aperture, 5);
            assert!(rank <= 4);
        }
        other => panic!("expected an observability refusal, found {other:?}"),
    }
}

/// Guard 15, and Lean `HNN/Ratio.face_constant_on_fibre`: an exponent read at a grain is its carry,
/// its phase class and its fibre, exactly, with `0 ≤ ε < 1/L`; reading it down to its cell's
/// representative moves it by less than `1/L`, and every value of a cell has one representative.
#[test]
fn the_grain_reading_is_a_carry_a_phase_class_and_a_fibre() {
    let values = [
        rat(-37, 7),
        rat(5, 3),
        integer(-2),
        rat(1, 16),
        rat(-1, 1000),
        Rat::zero(),
    ];
    for value in &values {
        for grain in [1u64, 2, 16, 7] {
            let cell = GrainCell::of(value, grain);
            let grain_rat = Rat::from_integer(BigInt::from(grain));
            assert!(cell.phase < grain);
            assert!(cell.fibre >= Rat::zero() && cell.fibre < grain_rat.recip());
            assert_eq!(cell.representative(grain) + &cell.fibre, *value);
            assert!(value - cell.representative(grain) < grain_rat.recip());
            let inside = cell.representative(grain) + &cell.fibre / integer(2);
            assert_eq!(
                GrainCell::of(&inside, grain).representative(grain),
                cell.representative(grain)
            );
        }
    }
    let cell = GrainCell::of(&rat(-37, 7), 16);
    assert_eq!(cell.carry, BigInt::from(-6));
    assert_eq!(cell.phase, 11);
}

/// The read is `f = R · P_R^(τ_R) v_R`: each class's real logit read at the grain and its imaginary
/// logit halved into turns, at the receiving ring's phase.
#[test]
fn the_read_rotates_the_anchor_to_the_receivers_phase() {
    let field = &chain();
    let medium = Medium::encoding(field, 12);
    // The phases are declared at rest; the read rotates by the receiving ring's phase at its cut.
    let phases = ReceivingPhases::declare(
        field,
        &medium,
        &Current::at_rest(field),
        &field.receivers()[0],
    )
    .unwrap();
    let current = Current::at(field, lift(&[0, 0, 3])).unwrap();
    let anchor = Draw::new(13).vector(4);
    let read = phases.read(field, &medium, &current, &anchor).unwrap();
    let map = medium.receiving_map(2).unwrap();
    let rotated = field.ring(2).rotate(&anchor, &BigInt::from(3));
    assert_eq!(read.logits, map.apply(&rotated).unwrap());
    assert_eq!(read.logits.len(), 2 * field.alphabet());
    for (class, cell) in read.cells.iter().enumerate() {
        assert_eq!(
            cell.representative(16) + &cell.fibre,
            read.logits[2 * class]
        );
        assert_eq!(read.phases[class], &read.logits[2 * class + 1] / integer(2));
    }
    assert!(phases.read(field, &medium, &current, &anchor[..2]).is_err());
}

/// Decision 26 (`harmonic_read_rotation_invariant`): the harmonic projection `Π`, read off the
/// ring's own rotation, is the orthogonal projection onto the fixed space of `P_g`: idempotent,
/// symmetric, fixed by every rotation and blind to it (`Π P^k = Π`); on each of campaign 1's closing
/// rotors the fixed space is the constant vector in each part (one orbit, every node), and a vector
/// is harmonic exactly when `Π` leaves it.
#[test]
fn the_harmonic_projection_is_the_fixed_space_of_the_rotation() {
    let field = Field::declare(FieldDeclaration::campaign_one(6_148)).unwrap();
    let mut draw = Draw::new(29);
    for ring in field.rings() {
        let (n, d) = (ring.width(), ring.period() as usize);
        assert_eq!(ring.orbits(), vec![(0..d).collect::<Vec<_>>()]);
        let (a, b) = (draw.vector(n), draw.vector(n));
        let projected = ring.harmonic(&a);
        assert_eq!(ring.harmonic(&projected), projected);
        assert!(ring.is_harmonic(&projected));
        assert_eq!(dot(&projected, &b), dot(&a, &ring.harmonic(&b)));
        assert!(projected.chunks(2).all(|node| node == &projected[..2]));
        for k in 0..=d as i64 {
            let k = BigInt::from(k);
            assert_eq!(ring.rotate(&projected, &k), projected);
            assert_eq!(ring.harmonic(&ring.rotate(&a, &k)), projected);
        }
        assert_eq!(ring.is_harmonic(&a), a == projected);
        let mut unit = vec![Rat::zero(); n];
        unit[0] = Rat::one();
        assert!(!ring.is_harmonic(&unit));
    }
}

/// Decision 26, the standing read (`standing_read_at_zero_change`, `standing_read_pullback`): the
/// face reads `f = R P^τ(v + h_R)`, which is `R P^τ v + R h_R` at every phase class and `R h_R` at
/// zero change; the coordinate is refused off the fixed space; its return `Π Rᵀ Σ_j ∇_j` is harmonic
/// and pairs with every harmonic variation as the face does, `Σ_j ⟨∇_j, R δ⟩ = ⟨Π Rᵀ Σ_j ∇_j, δ⟩`;
/// and the face's curvature along the fixed space is `Σ_j tr(Π Rᵀ 𝒥_j R Π)`.
#[test]
fn the_standing_read_is_rotation_invariant_and_its_return_pairs() {
    let field = chain();
    let ring = field.ring(2);
    let n = ring.width();
    let mut draw = Draw::new(31);
    let plain = Constitution::initial(&field, Steps::campaign_one(), CAMPAIGN_ONE_BUDGET).unwrap();
    let mut unit = vec![Rat::zero(); n];
    unit[0] = Rat::one();
    assert!(plain.clone().with_harmonic(&field, 2, unit).is_err());
    assert!(
        plain
            .clone()
            .with_harmonic(&field, 1, vec![Rat::zero(); field.ring(1).width()])
            .is_err()
    );
    let standing = ring.harmonic(&draw.vector(n));
    let theta = plain
        .clone()
        .with_harmonic(&field, 2, standing.clone())
        .unwrap();
    assert_eq!(theta.harmonic(2), Some(standing.as_slice()));
    let phases = ReceivingPhases::declare(
        &field,
        &theta,
        &Current::at_rest(&field),
        &field.receivers()[0],
    )
    .unwrap();
    let map = theta.receiving_map(2).unwrap();
    let bound = map.apply(&standing).unwrap();
    let anchor = draw.vector(n);
    for tau in 0..4 {
        let current = Current::at(&field, lift(&[0, 0, tau])).unwrap();
        let with = phases.read(&field, &theta, &current, &anchor).unwrap();
        let without = phases.read(&field, &plain, &current, &anchor).unwrap();
        let sum: Vec<Rat> = without
            .logits
            .iter()
            .zip(&bound)
            .map(|(a, b)| a + b)
            .collect();
        assert_eq!(with.logits, sum);
        let rest = phases
            .read(&field, &theta, &current, &vec![Rat::zero(); n])
            .unwrap();
        assert_eq!(rest.logits, bound);
    }
    let gradients: Vec<Vec<Rat>> = (0..2).map(|_| draw.vector(2 * field.alphabet())).collect();
    let views: Vec<&[Rat]> = gradients.iter().map(Vec::as_slice).collect();
    let returned = standing_return(ring, map, &views).unwrap();
    assert!(ring.is_harmonic(&returned));
    let transposed = map.transpose().unwrap();
    let mut pulled = vec![Rat::zero(); n];
    for gradient in &gradients {
        for (sum, value) in pulled.iter_mut().zip(transposed.apply(gradient).unwrap()) {
            *sum += value;
        }
    }
    assert_eq!(returned, ring.harmonic(&pulled));
    for _ in 0..3 {
        let variation = ring.harmonic(&draw.vector(n));
        let moved = map.apply(&variation).unwrap();
        let face: Rat = gradients.iter().map(|gradient| dot(gradient, &moved)).sum();
        assert_eq!(face, dot(&returned, &variation));
    }
    // The face's curvature along the fixed space, `Σ_j tr(Π Rᵀ 𝒥_j R Π)`, against its dense form:
    // `diag(p̃) − p̃p̃ᵀ` on the real rows (`p̃ = ∇_re + q`) and `¼` at the target's imaginary row.
    let targets = [1usize, 3];
    let classes = field.alphabet();
    let mut energy = Rat::zero();
    for (gradient, &target) in gradients.iter().zip(&targets) {
        let masses: Vec<Rat> = (0..classes)
            .map(|c| &gradient[2 * c] + if c == target { Rat::one() } else { Rat::zero() })
            .collect();
        let curvature = |a: &[Rat], b: &[Rat]| -> Rat {
            let mut sum = &a[2 * target + 1] * &b[2 * target + 1] / integer(4);
            for c in 0..classes {
                sum += &masses[c] * &a[2 * c] * &b[2 * c];
            }
            let (left, right): (Rat, Rat) = (
                (0..classes).map(|c| &masses[c] * &a[2 * c]).sum(),
                (0..classes).map(|c| &masses[c] * &b[2 * c]).sum(),
            );
            sum - left * right
        };
        for i in 0..n {
            let mut unit = vec![Rat::zero(); n];
            unit[i] = Rat::one();
            let column = map.apply(&ring.harmonic(&unit)).unwrap();
            energy += curvature(&column, &column);
        }
    }
    let reads: Vec<(&[Rat], usize)> = views.iter().copied().zip(targets).collect();
    assert_eq!(standing_energy(ring, map, &reads).unwrap(), energy);
    assert!(standing_energy(ring, map, &[(views[0], classes)]).is_err());
}

fn dot(a: &[Rat], b: &[Rat]) -> Rat {
    a.iter().zip(b).map(|(x, y)| x * y).sum()
}
