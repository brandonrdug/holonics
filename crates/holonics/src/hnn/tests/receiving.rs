//! The receiving phases: the grain derived from the receiver, the observability refusal, the exact
//! grain reading and the read through `R P_R^(τ_R)`.

use num_bigint::BigInt;
use num_traits::Zero;

use super::learning::chain;
use super::support::{Draw, Medium, Parts, lift, small_field};
use crate::hnn::HnnError;
use crate::hnn::field::{ConstitutionRead, Current, ReceiverDeclaration};
use crate::hnn::receiving::{GrainCell, ReceivingPhases};
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
