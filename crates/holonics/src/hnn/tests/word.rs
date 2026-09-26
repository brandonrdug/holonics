//! The word: it opens at zero change whatever preceded it, runs its receiving window, and releases
//! the change at its end.

use num_bigint::BigInt;
use num_traits::Zero;

use super::learning::chain;
use super::support::Medium;
use crate::hnn::HnnError;
use crate::hnn::field::{Current, Field};
use crate::hnn::moment::SourceMoment;
use crate::hnn::receiving::{ActiveAddress, ReceivingPhases, ReceivingRead, grain_logits};
use crate::hnn::word::Word;
use crate::ratio::{Rat, integer};

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
/// closes up to its residual within its certified bound, and its end releases the change with the
/// power it carried after the last junction: the last junction is a `W`-isometry about the
/// participation mean, so its power moves only by the executed anchor's residual, zero under the
/// exact law. On the word's lattices every carried remainder it releases lies in its half-open
/// cell (Lean `HNN/LatticeWord.feedback_rem_bounds`); under the exact law it releases none.
#[test]
fn the_forward_word_reads_its_epochs_and_releases_its_change() {
    for field in [chain(), chain().with_exact_word()] {
        let field = &field;
        let (medium, current, moment) = cut(field);
        let phases =
            ReceivingPhases::declare(field, &medium, &current, &field.receivers()[0]).unwrap();
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
            released.power,
            &before_last + &released.last,
            "the last junction moves the power only by its executed anchor's residual"
        );
        assert_eq!(released.ticks, 4);
        assert!(released.peak_bits > 0);
        match field.word_lattice() {
            Some(lattice) => {
                assert!(released.remainders.entries > 0);
                assert!(released.remainders.largest <= lattice.transient().unit() / integer(2));
                assert_eq!(released.charts.len(), 5, "three rings and two contacts");
                assert!(
                    released
                        .charts
                        .iter()
                        .all(|chart| chart.certificate <= lattice.target())
                );
            }
            None => {
                assert!(released.last.is_zero());
                assert_eq!(released.remainders.entries, 0);
                assert!(released.charts.is_empty());
            }
        }
    }
}

/// A medium with `E = 0` opens an empty word: its first word carries no change and every wave
/// logit is zero; the receiving parametron's tree is empty, so its face is uniform at every
/// address (Decision 28): every real logit of the combined read is `log₂(1/|A|) = −2` on the
/// chain's `|A| = 4`, carry `−2` and phase class `0`, every imaginary logit zero. The first faces
/// are uniform.
#[test]
fn the_initial_constitution_opens_an_empty_word() {
    let field = &chain();
    let medium = Medium::initial(field, 3);
    let (_, current, moment) = cut(field);
    let phases = ReceivingPhases::declare(field, &medium, &current, &field.receivers()[0]);
    // With `E = 0` the observability over the source storage is still the medium's own; the wave
    // of this moment is zero.
    let phases = phases.unwrap();
    let tree = phases
        .tree_faces(&medium, &ActiveAddress::boundary(phases.depth()), &[1, 3])
        .unwrap();
    let mut word = Word::open(field, &medium, &current, &moment).unwrap();
    assert_eq!(word.power().unwrap(), Rat::zero());
    for (anchor, tree) in word.forward(&phases).unwrap().into_iter().zip(&tree) {
        let wave = phases.read(field, &medium, &current, &anchor).unwrap();
        assert!(wave.logits.iter().all(Zero::is_zero));
        let read = ReceivingRead::combined(wave.logits, tree, phases.grain()).unwrap();
        assert_eq!(read.logits, grain_logits(tree));
        assert!(read.logits.iter().skip(1).step_by(2).all(Zero::is_zero));
        assert!(
            read.cells
                .iter()
                .all(|cell| cell.carry == BigInt::from(-2) && cell.phase == 0)
        );
    }
}
