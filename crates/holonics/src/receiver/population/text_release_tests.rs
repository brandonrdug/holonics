use super::tests::Fixed;
use super::text_release::{TextAppend, TextRelease, TextReleaseError, TextSeparator};
use super::{Population, PopulationRelease};
use crate::compression::landmark::context::SectionChart;
use crate::ratio::Rat;

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
