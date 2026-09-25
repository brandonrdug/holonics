//! The word: it opens at zero change whatever preceded it, runs its receiving window, and releases
//! the change at its end.

use num_traits::Zero;

use super::learning::chain;
use super::support::Medium;
use crate::hnn::HnnError;
use crate::hnn::field::{Current, Field};
use crate::hnn::moment::SourceMoment;
use crate::hnn::receiving::ReceivingPhases;
use crate::hnn::word::Word;
use crate::ratio::Rat;

/// A cut of the chain control (rings of periods 2, 3, 2, source ring 0, receiving ring 2 with
/// aperture 2): a constitution with a nonzero encoder, and a moment of 40 cells that fit no lock
/// (code 1: odd and not divisible by 3), so every ring stays dormant at rest and every contact's
/// exponent is zero: the word's laws, not the exponent's bits.
fn cut(field: &Field) -> (Medium, Current, SourceMoment) {
    let medium = Medium::encoding(field, 41);
    let cells = vec![1usize; 40];
    let mut current = Current::at_rest(field);
    let mut moment = SourceMoment::open(field, &current);
    moment.ingest(field, &mut current, &cells).unwrap();
    (medium, current, moment)
}

/// Lean `HNN/Retention.word_opens_at_zero`: a word opens with every wave and contact state zero
/// and storage only on the source rings, and a word opened after another word's full window reads
/// exactly what the first read: nothing of the earlier change persists.
#[test]
fn a_word_opens_at_zero_change_whatever_preceded_it() {
    let field = &chain();
    let (medium, current, moment) = cut(field);
    assert_eq!(
        current,
        Current::at_rest(field),
        "the cut's rings stay dormant"
    );
    let phases = ReceivingPhases::declare(field, &medium, &current, &field.receivers()[0]).unwrap();
    let mut first = Word::open(field, &medium, &current, &moment).unwrap();
    assert_eq!(first.support(), vec![true, false, false]);
    assert!(first.contact_support().iter().all(|carried| !carried));
    let opening = first.power().unwrap();
    let reads = first.forward(&phases).unwrap();
    first.release().unwrap();
    let mut second = Word::open(field, &medium, &current, &moment).unwrap();
    assert_eq!(second.power().unwrap(), opening);
    assert_eq!(second.forward(&phases).unwrap(), reads);
}

/// The forward word runs `e_max = e_0 + A` junction steps on its own hop clock, reads the receiving
/// ring at `e_0 … e_last` (the front reaches it no earlier than `e_0`), every full tick's balance
/// closes, and its end releases the change with the power it carried after the last junction.
#[test]
fn the_forward_word_reads_its_epochs_and_releases_its_change() {
    let field = &chain();
    let (medium, current, moment) = cut(field);
    let phases = ReceivingPhases::declare(field, &medium, &current, &field.receivers()[0]).unwrap();
    assert_eq!(
        (
            phases.first_epoch(),
            phases.last_epoch(),
            phases.junction_steps()
        ),
        (2, 3, 4)
    );
    let mut word = Word::open(field, &medium, &current, &moment).unwrap();
    let reads = word.forward(&phases).unwrap();
    assert_eq!(reads.len(), 2);
    assert!(reads.iter().all(|read| read.iter().any(|x| !x.is_zero())));
    for early in 0..2 {
        assert!(word.anchor(early, 2).unwrap().iter().all(Zero::is_zero));
    }
    assert_eq!(word.ticks(), 4);
    assert_eq!(word.clock().ticks(), 4u32.into());
    assert_eq!(word.balances().len(), 3);
    assert!(word.balances().iter().all(|balance| balance.closes()));
    let before_last = word.balances()[2].after.clone();
    assert!(matches!(word.tick(), Err(HnnError::WordEnded { ticks: 4 })));
    let released = word.release().unwrap();
    assert_eq!(
        released.power, before_last,
        "the last junction is a W-isometry"
    );
    assert_eq!(released.ticks, 4);
    assert!(released.peak_bits > 0);
}

/// The declared initial constitution has `E = 0`, so its first word carries no change and every
/// logit is zero: the first faces are uniform.
#[test]
fn the_initial_constitution_opens_an_empty_word() {
    let field = &chain();
    let medium = Medium::initial(field, 3);
    let (_, current, moment) = cut(field);
    let phases = ReceivingPhases::declare(field, &medium, &current, &field.receivers()[0]);
    // With `E = 0` the observability over the source storage is still the medium's own; the read
    // of this moment is zero.
    let phases = phases.unwrap();
    let mut word = Word::open(field, &medium, &current, &moment).unwrap();
    assert_eq!(word.power().unwrap(), Rat::zero());
    for anchor in word.forward(&phases).unwrap() {
        let read = phases.read(field, &medium, &current, &anchor).unwrap();
        assert!(read.logits.iter().all(Zero::is_zero));
        assert!(
            read.cells
                .iter()
                .all(|cell| cell.carry.is_zero() && cell.phase == 0)
        );
    }
}
