use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::ExactRatMatrix;

use super::*;

#[test]
fn one_participant_lineage_survives_i_you_and_name_charts() {
    let participant = EmanationParticipant {
        occurrence: "participant-occurrence/brandon".to_owned(),
        identity: "participant/brandon".to_owned(),
        proper_name: "Brandon".to_owned(),
    };
    let speaker =
        PerspectiveChart::found("chart/speaker", Some(participant.identity.clone()), None)
            .unwrap()
            .face(&participant);
    let addressee =
        PerspectiveChart::found("chart/addressee", None, Some(participant.identity.clone()))
            .unwrap()
            .face(&participant);
    let referent = PerspectiveChart::found("chart/referent", None, None)
        .unwrap()
        .face(&participant);
    assert_eq!(speaker.participant_identity, participant.identity);
    assert_eq!(addressee.participant_identity, participant.identity);
    assert_eq!(referent.participant_identity, participant.identity);
    assert_eq!(speaker.exterior_surface, "I");
    assert_eq!(addressee.exterior_surface, "you");
    assert_eq!(referent.exterior_surface, "Brandon");
}

#[test]
fn the_causal_adjoint_basis_is_exactly_the_changed_support() {
    let candidate = BTreeMap::from([("shared".to_owned(), 1), ("departed".to_owned(), 1)]);
    let returned = BTreeMap::from([("shared".to_owned(), 1), ("arrived".to_owned(), 1)]);
    let (basis, left, right, difference, zero_fibre) =
        sparse_difference(&candidate, &returned).unwrap();
    assert_eq!(basis, vec!["arrived".to_owned(), "departed".to_owned()]);
    assert_eq!(left, vec![0, 1]);
    assert_eq!(right, vec![1, 0]);
    assert_eq!(difference, vec![1, -1]);
    assert_eq!(zero_fibre, BTreeSet::from(["shared".to_owned()]));
    let metric = exact_morphology_metric(&left, &right).unwrap();
    let adjoint = CausalAdjointWord::found(
        vec![CausalAdjointStepInput {
            name: "returned-world-boundary".to_owned(),
            forward: ExactRatMatrix::identity(basis.len()).unwrap(),
            domain_metric: metric.clone(),
            codomain_metric: metric,
        }],
        difference.iter().copied().map(rat).collect(),
    )
    .unwrap();
    assert_eq!(adjoint.returned_source_covector, vec![rat(1), rat(-1)]);
}
