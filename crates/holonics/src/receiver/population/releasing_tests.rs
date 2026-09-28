use super::tests::Fixed;
use super::{
    MissingTextReleaseTerm, Population, PopulationRelease, Relation, RelationKind, ReleaseRefusal,
    TextReleaseRefusal,
};
use crate::ratio::rat;

#[test]
fn release_is_the_scored_face_and_includes_the_declared_stopping_class() {
    let family = Fixed::new(vec![rat(1, 2), rat(1, 3), rat(1, 6)], 0);
    let population = Population::new(vec![Box::new(family)]).expect("population");
    let scored = population.face().expect("scored face");

    let release = PopulationRelease::from_scored_face(&population, 2).expect("release");
    assert_eq!(release.face(), scored.as_slice());
    assert_eq!(release.stopping_class(), 2);
    assert!(release.face()[2].lower <= rat(1, 6));
    assert!(release.face()[2].upper >= rat(1, 6));
}

#[test]
fn release_refuses_a_stopping_class_outside_the_scored_alphabet() {
    let family = Fixed::new(vec![rat(1, 2), rat(1, 2)], 0);
    let population = Population::new(vec![Box::new(family)]).expect("population");
    assert_eq!(
        PopulationRelease::from_scored_face(&population, 2).unwrap_err(),
        ReleaseRefusal::StopOutsideAlphabet {
            class: 2,
            alphabet: 2,
        }
    );
}

#[test]
fn a_relation_without_a_living_receiver_owner_is_refused() {
    let family = Fixed::new(vec![rat(1, 2), rat(1, 2)], 0);
    let mut population = Population::new(vec![Box::new(family)]).expect("population");
    assert!(
        population
            .plan_relation(Relation {
                target: 0,
                letter: 1,
                kind: RelationKind::Request,
            })
            .is_err(),
        "a keyless family cannot claim to condition a response on a request"
    );
}

#[test]
fn text_release_names_missing_terms_and_does_not_mutate_the_population() {
    let family = Fixed::new(vec![rat(1, 2), rat(1, 3), rat(1, 6)], 0);
    let population = Population::new(vec![Box::new(family)]).expect("population");
    let before = population.face().expect("face before attempt");

    assert_eq!(
        population.attempt_text_release(2),
        Err(TextReleaseRefusal {
            missing: vec![
                MissingTextReleaseTerm::Decoder,
                MissingTextReleaseTerm::ProducingFamilyAndKeyProvenance,
                MissingTextReleaseTerm::GrainAndFibreWitness,
                MissingTextReleaseTerm::ReleaseSquare,
            ],
        })
    );
    assert_eq!(population.face().expect("face after attempt"), before);
}
