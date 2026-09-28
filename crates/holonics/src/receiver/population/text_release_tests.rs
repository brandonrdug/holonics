use super::tests::Fixed;
use super::text_release::{
    ResponseLaw, ResponseRefusal, TextAppend, TextRelease, TextReleaseError, TextSeparator,
    verify_scored_text_path,
};
use super::{Population, PopulationRelease};
use crate::compression::landmark::context::SectionChart;
use crate::ratio::Rat;
use crate::receiver::release::ReleaseReturn;

fn path(bytes: &[u8], section_class: usize, chart: SectionChart) -> Vec<PopulationRelease> {
    let face = vec![Rat::new(1.into(), chart.alphabet().into()); chart.alphabet()];
    let population = Population::new(vec![Box::new(Fixed::new(face, 0))]).unwrap();
    bytes
        .iter()
        .map(|&byte| PopulationRelease::from_scored_face(&population, usize::from(byte)).unwrap())
        .chain(std::iter::once(
            PopulationRelease::from_scored_face(&population, section_class).unwrap(),
        ))
        .collect()
}

#[test]
fn multibyte_response_includes_stop_and_append_square_holds() {
    let response = "café✓";
    let bytes = response.as_bytes().to_vec();
    let chart = SectionChart::curated();
    let section_class = chart
        .letter(crate::compression::landmark::context::sections::Section {
            kind: 3,
            channel: 2,
        })
        .unwrap();
    assert!(section_class >= 256);
    let views = path(&bytes, section_class, chart);
    let release = TextRelease::checked(bytes.clone(), chart, section_class, &views).unwrap();
    assert_eq!(release.text(), response);
    assert_eq!(release.bytes(), bytes);
    assert_eq!(release.section_class(), section_class);
    assert_eq!(release.append(TextAppend('界')).unwrap(), "café✓界");
    assert_eq!(release.face_trace(), views.as_slice());
    assert_eq!(
        release.face_trace().last().unwrap().selected_class(),
        section_class
    );
}

#[test]
fn invalid_utf8_returns_operands_in_separator() {
    let chart = SectionChart::curated();
    let error = TextRelease::checked(vec![0xf0, 0x9f, 0x92], chart, 256, &[]).unwrap_err();
    assert!(matches!(
        error,
        TextReleaseError::Separator(TextSeparator::InvalidUtf8 { valid_up_to: 0, .. })
    ));
}

#[test]
fn byte_class_cannot_be_used_as_a_stop_section() {
    let chart = SectionChart::curated();
    let error = TextRelease::checked(b"done".to_vec(), chart, 255, &[]).unwrap_err();
    assert!(matches!(
        error,
        TextReleaseError::Separator(TextSeparator::InvalidSection {
            section_class: 255,
            ..
        })
    ));
}

#[test]
fn one_next_face_cannot_certify_a_complete_response() {
    let chart = SectionChart::curated();
    let one = path(b"", 256, chart);
    let error = TextRelease::checked(b"answer".to_vec(), chart, 256, &one).unwrap_err();
    assert_eq!(
        error,
        TextReleaseError::Separator(TextSeparator::PathLength {
            expected: 7,
            actual: 1,
        })
    );
}

#[test]
fn verifier_captures_each_contemporary_face_through_the_stop() {
    let chart = SectionChart::curated();
    let mut first = vec![Rat::from_integer(0.into()); chart.alphabet()];
    let mut second = first.clone();
    first[usize::from(b'a')] = Rat::new(1.into(), 2.into());
    first[256] = Rat::new(1.into(), 2.into());
    second[usize::from(b'a')] = Rat::new(1.into(), 4.into());
    second[256] = Rat::new(3.into(), 4.into());
    let mut population = Population::new(vec![
        Box::new(Fixed::new(first, 1)),
        Box::new(Fixed::new(second, 1)),
    ])
    .unwrap();

    let release =
        super::text_release::verify_scored_text_path(&mut population, b"a", 256, chart).unwrap();
    assert_eq!(release.text(), "a");
    assert_eq!(release.face_trace().len(), 2);
    assert_eq!(release.face_trace()[0].selected_class(), usize::from(b'a'));
    assert_eq!(release.face_trace()[1].selected_class(), 256);
    assert_ne!(
        release.face_trace()[0].face(),
        release.face_trace()[1].face()
    );
}

#[test]
fn verifier_rejects_invalid_stop_before_mutating_branch() {
    let chart = SectionChart::curated();
    let face = vec![Rat::new(1.into(), chart.alphabet().into()); chart.alphabet()];
    let mut population = Population::new(vec![Box::new(Fixed::new(face, 0))]).unwrap();
    let error = super::text_release::verify_scored_text_path(&mut population, b"a", 255, chart)
        .unwrap_err();
    assert!(matches!(
        error,
        TextReleaseError::Separator(TextSeparator::InvalidSection {
            section_class: 255,
            ..
        })
    ));
    assert_eq!(population.cells(), 0);
}

#[test]
fn verifier_reports_impossible_cell_and_its_tick() {
    let chart = SectionChart::curated();
    let mut face = vec![Rat::from_integer(0.into()); chart.alphabet()];
    face[256] = Rat::from_integer(1.into());
    let mut population = Population::new(vec![Box::new(Fixed::new(face, 0))]).unwrap();
    let error = super::text_release::verify_scored_text_path(&mut population, b"a", 256, chart)
        .unwrap_err();
    assert!(matches!(
        error,
        TextReleaseError::Separator(TextSeparator::Receive { tick: 0, .. })
    ));
}

// -------------------------------------------------------------------------------------------
// the response through the one decision law

fn chart_face(entries: &[(usize, Rat)]) -> Vec<Rat> {
    let mut face = vec![Rat::from_integer(0.into()); SectionChart::curated().alphabet()];
    for (class, mass) in entries {
        face[*class] = mass.clone();
    }
    face
}

fn keys(values: Vec<Rat>) -> impl FnMut() -> Rat {
    let mut values = values.into_iter();
    move || values.next().expect("a declared key")
}

fn q(numerator: i64, denominator: i64) -> Rat {
    Rat::new(numerator.into(), denominator.into())
}

/// **The scored law's response is the verifier's path.** Each cell is a certified draw from the
/// population's scored face; the stop law ends it at the drawn section, which is emitted and
/// received; the drawn path's faces are exactly the faces the verifier captures for the same bytes
/// on a fresh branch of the same standing (`P_release = P_scored`), and the codec square holds.
#[test]
fn a_scored_response_is_drawn_through_the_one_law_and_verifies() {
    let chart = SectionChart::curated();
    let a = usize::from(b'a');
    let population = || {
        Population::new(vec![
            Box::new(Fixed::new(chart_face(&[(a, q(1, 2)), (256, q(1, 2))]), 1)),
            Box::new(Fixed::new(chart_face(&[(a, q(1, 4)), (256, q(3, 4))]), 1)),
        ])
        .unwrap()
    };
    let mut released = population();
    // Face 1: `a` 3/8, stop 5/8, the key 0 draws `a`; face 2 (weights 2/3, 1/3): `a` 5/12,
    // stop 7/12, the key 1/2 draws the stop.
    let response = released.release_response(
        chart,
        1 << 10,
        ResponseLaw::Scored,
        &mut keys(vec![q(0, 1), q(1, 2)]),
    );
    assert_eq!(response.refusal, None);
    assert_eq!(response.bytes, b"a".to_vec());
    assert_eq!(response.stop, Some(256));
    assert_eq!(response.emitted(), 2);
    assert_eq!(
        response
            .decisions
            .iter()
            .map(ReleaseReturn::drawn_class)
            .collect::<Vec<_>>(),
        vec![Some(a), Some(256)]
    );
    let ReleaseReturn::Drawn(stop) = &response.decisions[1] else {
        panic!("the stop is a certified draw")
    };
    assert_eq!(stop.key, q(1, 2));
    assert!(stop.prior_upper <= stop.key && stop.key < stop.through_lower);
    assert_eq!(response.provenance.len(), 2);
    assert_eq!(response.provenance[0].len(), 2);
    assert_eq!(released.cells(), 2);

    let checked = response
        .text(chart)
        .expect("stopped")
        .expect("the codec square");
    assert_eq!(checked.text(), "a");
    let verified = verify_scored_text_path(&mut population(), b"a", 256, chart).unwrap();
    assert_eq!(verified.face_trace(), response.trace.as_slice());
}

/// **The stop law's refusal**: a byte drawn when the aperture keeps no room for the stop is not
/// emitted, and the return is `NoContinuationBridges`.
#[test]
fn a_byte_with_no_room_for_the_stop_is_not_emitted() {
    let chart = SectionChart::curated();
    let a = usize::from(b'a');
    let mut population =
        Population::new(vec![Box::new(Fixed::new(chart_face(&[(a, q(1, 1))]), 0))]).unwrap();
    let response = population.release_response(
        chart,
        3,
        ResponseLaw::Scored,
        &mut keys(vec![q(1, 2); 3]),
    );
    assert_eq!(response.bytes, b"aa".to_vec());
    assert_eq!(response.stop, None);
    assert_eq!(response.emitted(), 2);
    assert!(matches!(
        response.last(),
        Some(ReleaseReturn::NoContinuationBridges { .. })
    ));
    assert_eq!(population.cells(), 2);
    assert!(response.text(chart).is_none());
}

/// **The ancestral law**: one family is drawn from the posterior enclosure, then its exact face is
/// followed through the stop; a key the posterior leaves plural holds the family draw and nothing
/// is drawn; an aperture with no room for the stop is refused.
#[test]
fn the_ancestral_law_draws_a_family_then_follows_it_to_the_stop() {
    let chart = SectionChart::curated();
    let a = usize::from(b'a');
    let population = || {
        Population::new(vec![
            Box::new(Fixed::new(chart_face(&[(a, q(1, 2)), (256, q(1, 2))]), 1)),
            Box::new(Fixed::new(chart_face(&[(256, q(1, 1))]), 2)),
        ])
        .unwrap()
    };
    let response = population().release_response(
        chart,
        1 << 10,
        ResponseLaw::Ancestral,
        &mut keys(vec![q(1, 4), q(1, 4), q(3, 4)]),
    );
    assert_eq!(response.drawn_family(), Some(0));
    let posterior = response.posterior.as_ref().expect("the posterior was read");
    assert!(posterior[0].lower <= q(2, 3) && q(2, 3) <= posterior[0].upper);
    assert_eq!(response.bytes, b"a".to_vec());
    assert_eq!(response.stop, Some(256));
    assert_eq!(response.emitted(), 2);
    assert!(response.trace.is_empty() && response.provenance.is_empty());

    let held = population().release_response(
        chart,
        1 << 10,
        ResponseLaw::Ancestral,
        &mut keys(vec![q(2, 3)]),
    );
    assert!(matches!(
        held.family,
        Some(Ok(ReleaseReturn::Unresolved(ref unresolved))) if unresolved.crossings.len() == 2
    ));
    assert!(held.decisions.is_empty() && held.bytes.is_empty() && held.refusal.is_none());

    let cramped =
        population().release_response(chart, 0, ResponseLaw::Ancestral, &mut keys(vec![q(1, 4)]));
    assert_eq!(
        cramped.refusal,
        Some(ResponseRefusal::NoRoomForStop {
            capacity: 0,
            cells: 0
        })
    );
}
