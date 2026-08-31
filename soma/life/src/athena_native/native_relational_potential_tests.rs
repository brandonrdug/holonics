use super::*;
use crate::relational_language::RelationalEntity;
use std::collections::BTreeSet;

#[test]
fn source_passages_descend_to_triangular_native_incidence() {
    let mut builder =
        NativeRelationalPotentialBuilder::new(vec!["a".repeat(64), "b".repeat(64)]).unwrap();
    builder
        .receive(
            0,
            NativeDeliveryPhase::Ingress,
            "message/0",
            "Brandon founds Athena.",
        )
        .unwrap();
    builder
        .receive(
            0,
            NativeDeliveryPhase::Emanation,
            "message/1",
            "Athena carries exact holonic transport.",
        )
        .unwrap();
    builder
        .receive(
            1,
            NativeDeliveryPhase::Emanation,
            "message/2",
            "Brandon cultivates the holonic laboratory.",
        )
        .unwrap();
    let (codec, potential, receipt) = builder.finish().unwrap();
    assert_eq!(receipt.triangular_boundary_defect_population, 0);
    assert!(!potential.cells.is_empty());
    let contact = codec.contact(&potential, "Describe Brandon.").unwrap();
    assert!(!contact.faces.is_empty());
    assert_eq!(contact.factor_support, vec![0, 1]);
    let wire = potential.canonical_bytes().unwrap();
    assert!(!String::from_utf8_lossy(&wire).contains("Brandon founds Athena"));
    assert_eq!(
        NativeRelationalPotentialComplex::read(&wire).unwrap(),
        potential
    );
}

#[test]
fn identical_reading_does_not_replace_the_exact_causal_signature() {
    let mut builder =
        NativeRelationalPotentialBuilder::new(vec!["a".repeat(64), "b".repeat(64)]).unwrap();
    builder
        .receive(
            0,
            NativeDeliveryPhase::Emanation,
            "message/a",
            "Alpha carries beta.",
        )
        .unwrap();
    builder
        .receive(
            1,
            NativeDeliveryPhase::Emanation,
            "message/b",
            "Alpha carries beta.",
        )
        .unwrap();
    let (codec, potential, _) = builder.finish().unwrap();
    let alpha = codec.contact(&potential, "Describe alpha.").unwrap();
    assert_eq!(alpha.factor_support, vec![0, 1]);
    assert!(potential
        .faces
        .iter()
        .any(|face| face.factor_support == vec![0, 1] && face.occurrences.len() == 2));
}

#[test]
fn addressed_dialogue_lineage_glues_deictic_faces_without_naming_native_state() {
    let mut builder = NativeRelationalPotentialBuilder::new(vec!["a".repeat(64)]).unwrap();
    builder
        .receive(
            0,
            NativeDeliveryPhase::Ingress,
            "message/0",
            "I cultivate Athena.",
        )
        .unwrap();
    builder
        .receive(
            0,
            NativeDeliveryPhase::Emanation,
            "message/1",
            "Brandon is the user. You require exact holonic transport.",
        )
        .unwrap();
    let (codec, potential, _) = builder.finish().unwrap();
    let contact = codec.contact(&potential, "Describe Brandon.").unwrap();
    let (participant, alias) = contact.participant_alias.unwrap();
    assert!(contact.faces.contains(&participant));
    assert!(contact.faces.contains(&alias));
    assert_eq!(
        potential.faces[participant as usize].kind,
        NativeRelationalFaceKind::Participant
    );
    assert!(codec
        .canonical_bytes(&potential)
        .map(|wire| !String::from_utf8_lossy(&wire).contains("native-brandon"))
        .unwrap());
}

#[test]
fn participant_subject_is_exact_and_existential_copulas_remain_outside_its_chart() {
    let mut builder = NativeRelationalPotentialBuilder::new(vec!["a".repeat(64)]).unwrap();
    builder
        .receive(
            0,
            NativeDeliveryPhase::Ingress,
            "message/existential",
            "There are elliptic curves.",
        )
        .unwrap();
    builder
        .receive(
            0,
            NativeDeliveryPhase::Emanation,
            "message/copular",
            "You are right.",
        )
        .unwrap();
    builder
        .receive(
            0,
            NativeDeliveryPhase::Emanation,
            "message/modal",
            "You can carry exact current.",
        )
        .unwrap();
    builder
        .receive(
            0,
            NativeDeliveryPhase::Return,
            "message/return",
            "I carry returned current.",
        )
        .unwrap();
    let (codec, potential, _) = builder.finish().unwrap();
    let participant_faces = potential.addressed_participant_subject_faces().unwrap();
    assert_eq!(participant_faces.len(), 1);
    assert!(participant_faces.iter().all(|face| {
        potential.faces[*face as usize].kind == NativeRelationalFaceKind::Participant
    }));

    let clauses = potential
        .cells
        .iter()
        .map(|cell| {
            (
                cell,
                codec.clause(&potential, cell, None).unwrap(),
                participant_faces.contains(&cell.subject),
            )
        })
        .collect::<Vec<_>>();
    let existential = clauses
        .iter()
        .find(|(_, clause, _)| clause.subject.identity.contains("there"))
        .expect("the existential cell remains in the complete potential");
    assert!(!existential.2);
    assert_eq!(
        potential.faces[existential.0.subject as usize].kind,
        NativeRelationalFaceKind::Entity
    );

    let direct = clauses
        .iter()
        .filter(|(_, _, participant)| *participant)
        .collect::<Vec<_>>();
    assert!(direct
        .iter()
        .any(|(cell, clause, _)| { cell.copular && clause.object.identity.contains("right") }));
    assert!(direct
        .iter()
        .any(|(_, clause, _)| clause.modality.as_deref() == Some("can")));
    assert!(direct.iter().any(|(cell, _, _)| {
        cell.occurrences
            .iter()
            .any(|occurrence| occurrence.phase == NativeDeliveryPhase::Return)
    }));

    for (_, clause, _) in direct {
        let mut clause = clause.clone();
        clause.subject = RelationalEntity {
            surface: vec!["Brandon".to_owned()],
            identity: BTreeSet::from(["brandon".to_owned()]),
        };
        let surface = crate::relational_language::realize_relational_clauses(&[clause], &[], false)
            .unwrap()
            .text;
        assert!(surface.starts_with("Brandon "));
        assert!(!surface.contains("Brandon is elliptic curves"));
    }
}
