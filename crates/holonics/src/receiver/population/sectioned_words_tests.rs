//! Exact fixtures for the curated-chart word family.

use super::sectioned_words::SectionedWordFamily;
use crate::compression::landmark::context::{
    Capacity, LandmarkDeclaration, Section, SectionChart, SectionSlots, Sections, StopPrior,
};
use crate::ratio::Rat;
use crate::receiver::population::{
    BoundaryEgg, Family, Likelihood, Readout, TreeFamily, WORD_END, WordDictionary,
};
use num_bigint::BigInt;
use num_traits::Zero;

const POPULATION: u64 = 1 << 10;
const GRAIN: u64 = 16;

fn chart() -> SectionChart {
    SectionChart::curated()
}

fn boundary() -> BoundaryEgg {
    let chart = chart();
    let sections = Sections::new(chart, SectionSlots::Channel).expect("channel section slots");
    let byte_tree = TreeFamily::sectioned(
        LandmarkDeclaration {
            alphabet: chart.alphabet(),
            depth: 2,
            forced: 0,
            population: POPULATION,
            grain: GRAIN,
            family: sections.family().clone(),
            prior: StopPrior::half(),
            capacity: Capacity::Unbounded,
        },
        1,
        sections,
    )
    .expect("typed byte tree");
    let letters = LandmarkDeclaration {
        alphabet: chart.letters(),
        depth: 2,
        forced: 0,
        population: POPULATION,
        grain: GRAIN,
        family: BoundaryEgg::letter_family(POPULATION).expect("letter family"),
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
    };
    BoundaryEgg::new("boundary fixture".to_string(), 1, byte_tree, chart, letters)
        .expect("boundary egg")
}

fn dictionary() -> (WordDictionary, usize) {
    let mut words: Vec<Vec<u8>> = (0u16..=255).map(|byte| vec![byte as u8]).collect();
    let phrase = words.len();
    words.push(b"ab".to_vec());
    let weight = Rat::new(BigInt::from(1), BigInt::from(words.len()));
    let token_face = vec![weight; words.len()];
    (
        WordDictionary::new(
            words,
            token_face,
            Rat::new(BigInt::from(1), BigInt::from(3)),
        )
        .expect("positive token and stop faces"),
        phrase,
    )
}

#[test]
fn sectioned_word_face_routes_stop_mass_and_resets_after_a_letter() {
    let (dictionary, phrase) = dictionary();
    assert!(!dictionary.is_uniquely_decodable());
    assert_eq!(
        dictionary.decode(&[phrase]).expect("phrase decoding"),
        b"ab"
    );

    let mut family = SectionedWordFamily::new(
        "sectioned words".to_string(),
        8,
        dictionary.clone(),
        boundary(),
    )
    .expect("sectioned word family");
    let mut product = Rat::from_integer(1.into());

    let opening = chart()
        .letter(Section {
            kind: 0,
            channel: 0,
        })
        .expect("opening section letter");
    let initial = family.face().expect("opening face");
    assert_eq!(
        initial.iter().cloned().sum::<Rat>(),
        Rat::from_integer(1.into())
    );
    assert!(initial[..chart().bytes()].iter().all(Rat::is_zero));
    assert_eq!(
        initial[chart().bytes()..].iter().cloned().sum::<Rat>(),
        Rat::from_integer(1.into())
    );
    product *= family.receive(opening).expect("opening letter");

    let a = usize::from(b'a');
    let b = usize::from(b'b');
    let first = family.face().expect("first within-part face");
    assert_eq!(
        first.iter().cloned().sum::<Rat>(),
        Rat::from_integer(1.into())
    );
    assert_eq!(
        first[..chart().bytes()].iter().cloned().sum::<Rat>(),
        Rat::new(2.into(), 3.into())
    );
    assert_eq!(
        first[chart().bytes()..].iter().cloned().sum::<Rat>(),
        Rat::new(1.into(), 3.into())
    );
    let first_a = family.receive(a).expect("first byte");
    product *= &first_a;
    let after_a = family.face().expect("face after first byte");
    let second_b = family.receive(b).expect("second byte");
    assert_eq!(second_b, after_a[b]);
    product *= &second_b;

    let before_end = family.face().expect("word-end face");
    let stop = before_end[chart().bytes()..].iter().cloned().sum::<Rat>();
    assert_eq!(stop, Rat::new(1.into(), 3.into()));
    let conditional: Vec<Rat> = before_end[chart().bytes()..]
        .iter()
        .map(|mass| mass / &stop)
        .collect();
    assert_eq!(
        conditional.iter().cloned().sum::<Rat>(),
        Rat::from_integer(1.into())
    );
    let closing = chart()
        .letter(Section {
            kind: 2,
            channel: 1,
        })
        .expect("closing section letter");
    let part_mass = dictionary.parse_mass(b"ab");
    let closing_probability = family.receive(closing).expect("close and reset the word");
    assert_eq!(
        closing_probability,
        &stop * &conditional[closing - chart().bytes()]
    );
    product *= closing_probability;
    assert_eq!(part_mass, first_a * second_b * stop);

    let next = family.face().expect("fresh word at the next part");
    assert_eq!(
        next.iter().cloned().sum::<Rat>(),
        Rat::from_integer(1.into())
    );
    assert_eq!(
        next[..chart().bytes()].iter().cloned().sum::<Rat>(),
        Rat::new(2.into(), 3.into())
    );
    assert_eq!(
        next[chart().bytes()..].iter().cloned().sum::<Rat>(),
        Rat::new(1.into(), 3.into())
    );
    assert_eq!(
        family.likelihood(),
        Likelihood::Exact(product),
        "the online product of prequential faces is the family's exact score"
    );
    match family.readout() {
        Readout::Words(readout) => {
            assert_eq!(readout.received, 0);
            assert_eq!(readout.boundary_mass, Rat::from_integer(1.into()));
            assert!(!readout.terminated);
        }
        other => panic!("word decoder readout, got {other:?}"),
    }
}

#[test]
fn sectioned_word_stop_face_is_distributed_in_the_boundary_egg_ratio() {
    let (dictionary, _) = dictionary();
    let mut family =
        SectionedWordFamily::new("sectioned words".to_string(), 8, dictionary, boundary())
            .expect("sectioned word family");
    let opening = chart()
        .letter(Section {
            kind: 0,
            channel: 0,
        })
        .expect("opening section letter");
    family.receive(opening).expect("open part");
    let word_face = family.face().expect("word face with section conditioner");
    let boundary_face = family
        .boundary
        .face()
        .expect("underlying boundary egg's exact face");
    let boundary_letters = &boundary_face[chart().bytes()..];
    let boundary_total: Rat = boundary_letters.iter().cloned().sum();
    let stop = family.word.face().expect("word receiver face")[WORD_END].clone();
    for offset in 0..chart().letters() {
        assert_eq!(
            word_face[chart().bytes() + offset],
            &stop * (&boundary_letters[offset] / &boundary_total)
        );
    }
}
