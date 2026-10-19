//! Grouped tube bounds enclose actual independently opened words. No word's
//! entries are joined to another word's stations, and no forward is replayed.

use super::*;
use crate::hnn::chart::Charts;
use crate::hnn::field::Current;
use crate::hnn::propagation::Operands;
use crate::hnn::ring::TubeCentre;
use crate::hnn::word::{EndChange, Word};

fn fixture() -> (Field, Constitution, usize) {
    let field = crate::hnn::tests::learning::chain();
    let ring = field.receivers()[0].ring;
    let material = Constitution::initial(&field, 1 << 40)
        .unwrap()
        .with_locking_pump(&field, ring)
        .unwrap();
    (field, material, ring)
}

/// Execute a word on an actual standing sheet, under its own opening clock.
/// Its reach uses elapsed ticks from that opening, as the actual return does.
fn actual_reach(
    field: &Field,
    material: &Constitution,
    ring: usize,
    sign: i8,
    ticks: usize,
    opening_tick: usize,
) -> Reach {
    let operands = Operands::at_cut_charted(
        field,
        material,
        &Current::at_rest(field),
        &mut Charts::new(),
    )
    .unwrap();
    let centre = operands.resonators()[ring]
        .as_ref()
        .unwrap()
        .tube_centres()
        .unwrap()
        .into_iter()
        .find(|(centre, _)| *centre == TubeCentre::Sheet(sign))
        .unwrap()
        .1;
    let mut change = EndChange::rest(field, &operands);
    change.resonators[ring] = Some([centre, vec![Rat::zero(); field.ring(ring).width()]]);
    let injection: Vec<_> = field
        .rings()
        .iter()
        .map(|declared| vec![Rat::zero(); declared.width()])
        .collect();
    let mut word = Word::continuing(field, operands, &change, &injection, opening_tick).unwrap();
    for _ in 0..ticks {
        assert!(word.tick().unwrap().closes());
    }
    let passages = word.tube_passages().unwrap();
    assert_eq!(passages.len(), 1);
    assert_eq!(passages[0].ring, ring);
    assert_eq!(passages[0].nearest().0, TubeCentre::Sheet(sign));
    // Keeping the actual producing word changes no summary and executes no tick.
    assert_eq!(word.keep().tube_passages().unwrap(), passages);
    Reach {
        receiver: ring,
        stations: vec![ticks as u64],
        entries: vec![0],
        phases: 1,
        loci: [Locus::Element(ring)].into_iter().collect(),
        passages,
    }
}

/// The real epoch envelope has a union medium and a longest LOCAL span. Its
/// entries are deliberately empty: only the original words own their entries.
fn envelope(readings: &[Reach]) -> Reach {
    Reach {
        receiver: readings[0].receiver,
        stations: vec![
            readings
                .iter()
                .flat_map(|reach| reach.stations.iter().copied())
                .max()
                .unwrap(),
        ],
        entries: Vec::new(),
        phases: readings.iter().map(|reach| reach.phases).max().unwrap(),
        loci: readings
            .iter()
            .flat_map(|reach| reach.loci.iter().copied())
            .collect(),
        passages: Vec::new(),
    }
}

#[test]
fn grouped_actual_word_passages_take_each_centre_maximum_before_selecting_the_centre() {
    let (field, material, ring) = fixture();
    let local = vec![
        actual_reach(&field, &material, ring, 1, 2, 7),
        actual_reach(&field, &material, ring, -1, 3, 29),
    ];
    let before = local.clone();
    let joined = envelope(&local);
    let read = material.tube_metrics(Some(&joined), Some(&local)).unwrap();
    assert_eq!(read.len(), 1);
    let (passage, metric) = &read[0];
    for (centre, distance) in &passage.distances {
        let expected = local
            .iter()
            .map(|reach| reach.passages[0].distance(*centre).unwrap())
            .max()
            .unwrap();
        assert_eq!(distance, expected);
    }
    // Individually the words are nearest opposite sheets; their common tube
    // is nearest the saddle. Choosing a local centre first misses this fact.
    assert_eq!(metric.centre, TubeCentre::Origin);
    assert_eq!(passage.nearest().0, TubeCentre::Origin);
    assert_eq!(local, before);
    assert!(joined.entries.is_empty());
    assert_eq!(joined.stations, vec![3]);
    assert_eq!(local[0].entries, vec![0]);
    assert_eq!(local[1].entries, vec![0]);
}

#[test]
fn one_actual_word_has_the_same_tube_metric_through_the_grouped_interface() {
    let (field, material, ring) = fixture();
    let actual = actual_reach(&field, &material, ring, 1, 2, 11);
    let local = std::slice::from_ref(&actual);
    assert_eq!(
        material.tube_metrics(Some(&actual), None).unwrap(),
        material
            .tube_metrics(Some(&envelope(local)), Some(local))
            .unwrap()
    );
}

#[test]
fn another_actual_word_cannot_hide_a_missing_local_tube_passage() {
    let (field, material, ring) = fixture();
    let first = actual_reach(&field, &material, ring, 1, 2, 7);
    let mut missing = actual_reach(&field, &material, ring, -1, 3, 29);
    missing.passages.clear();
    let local = vec![first, missing];
    let before = local.clone();
    assert!(matches!(
        material.tube_metrics(Some(&envelope(&local)), Some(&local)),
        Err(HnnError::Resonator { ring: failed, what })
            if failed == ring
                && what == "every word reaching a saturated ring carries its actual tube passage"
    ));
    assert_eq!(local, before);
}

#[test]
fn grouped_actual_summaries_refuse_a_different_producing_rest_point_family() {
    let (field, material, ring) = fixture();
    let first = actual_reach(&field, &material, ring, 1, 2, 7);
    let mut mismatched = actual_reach(&field, &material, ring, -1, 3, 29);
    // Damage only the summary's declared rest-point family after the actual
    // word has run. Its distance values cannot authorize a different period.
    assert!(mismatched.passages[0].distances.pop().is_some());
    let local = vec![first, mismatched];
    assert!(matches!(
        material.tube_metrics(Some(&envelope(&local)), Some(&local)),
        Err(HnnError::Resonator { ring: failed, what })
            if failed == ring
                && what == "an epoch's tube passages share their producing period's rest points"
    ));
}

#[test]
fn a_word_outside_the_ring_diamond_contributes_no_tube_distance() {
    let (field, material, ring) = fixture();
    let first = actual_reach(&field, &material, ring, 1, 2, 7);
    let mut outside = actual_reach(&field, &material, ring, -1, 3, 29);
    outside.loci.clear();
    let expected = material.tube_metrics(Some(&first), None).unwrap();
    let local = vec![first, outside];
    assert_eq!(
        material
            .tube_metrics(Some(&envelope(&local)), Some(&local))
            .unwrap(),
        expected
    );
}
