use super::*;
use holonic_engine::operation_correspondence::{
    NativeGraphIdentity, OpenRemainder, OperationCorrespondence, OperationResolution,
    SourceOperationOccurrence,
};
use holonic_engine::ported_operation::OperationSpecies;
use holonic_engine::{causal::EventId, evolution::EvolutionLawId};

fn seal(ids: &[&str]) -> OperationCorrespondenceSeal {
    let graph = NativeGraphIdentity::derived_with_topology(
        1,
        1,
        "fixture",
        vec!["r".to_owned()],
        vec!["c".to_owned()],
        vec!["t".to_owned()],
    );
    let sources = ids
        .iter()
        .enumerate()
        .map(|(at, id)| SourceOperationOccurrence {
            id: (*id).to_owned(),
            source_identity: (*id).to_owned(),
            deed: "fixture".to_owned(),
            family: "fixture-family".to_owned(),
            parameters: BTreeMap::new(),
            event: EventId(at as u64),
            law: EvolutionLawId(at as u64),
            operation: (*id).to_owned(),
            species: OperationSpecies::Transport,
            inputs: Vec::new(),
            outputs: Vec::new(),
            carrier: None,
        })
        .collect::<Vec<_>>();
    let operations = ids
        .iter()
        .map(|id| OperationCorrespondence {
            source_id: (*id).to_owned(),
            resolution: OperationResolution::Native(NativeOperationBinding {
                source_id: (*id).to_owned(),
                resident_law: format!("law-{id}"),
                species: OperationSpecies::Transport,
                native_population: None,
                inputs: Vec::new(),
                outputs: Vec::new(),
                graph_key: graph.key.clone(),
            }),
        })
        .collect();
    OperationCorrespondenceSeal::new(sources, operations, Vec::new(), Vec::new(), vec![graph])
        .seal()
        .unwrap()
}

fn input<'a>(
    s: &'a OperationCorrespondenceSeal,
    observations: &[(u64, u64, u64)],
    split: bool,
) -> CondensationInput<'a> {
    let ids = ["a", "b", "c"];
    let states = ids
        .iter()
        .map(|id| CondensationState {
            id: (*id).to_owned(),
            source_members: vec![(*id).to_owned()],
        })
        .collect();
    let mut values = BTreeMap::new();
    let row = observations[0];
    for (id, value) in ids.iter().zip([row.0, row.1, row.2]) {
        values.insert((*id).to_owned(), value);
    }
    let receiver = ReceiverSignature {
        name: "future".to_owned(),
        values,
    };
    let mut next = BTreeMap::new();
    next.insert("a".to_owned(), "c".to_owned());
    next.insert(
        "b".to_owned(),
        if split {
            "a".to_owned()
        } else {
            "c".to_owned()
        },
    );
    next.insert("c".to_owned(), "c".to_owned());
    CondensationInput {
        seal: s,
        states,
        receivers: vec![receiver],
        successors: vec![SuccessorSignature {
            input: "step".to_owned(),
            next,
        }],
        sharing: Vec::new(),
    }
}

#[test]
fn adversarial_successor_separates_equal_one_shot_pair_and_retains_fibre() {
    let s = seal(&["a", "b", "c"]);
    let result = condense(input(&s, &[(1, 1, 2)], true)).unwrap();
    assert_eq!(result.reconstruction.len(), 1);
    assert_eq!(result.no_factor.len(), 1);
    assert_eq!(result.no_factor[0].witnesses[0].word, vec!["step"]);
    assert!(!result.candidates[0].factorization.holds);
}

#[test]
fn equal_future_successor_is_a_lawful_candidate_not_a_byte_factor() {
    let s = seal(&["a", "b", "c"]);
    let result = condense(input(&s, &[(1, 1, 2)], false)).unwrap();
    assert!(result.no_factor.is_empty());
    assert!(
        result
            .candidates
            .iter()
            .all(|candidate| matches!(candidate.status, CandidateStatus::Exact))
    );
}

#[test]
fn open_native_binding_is_retained_and_not_called_preserved() {
    let mut s = seal(&["a", "b", "c"]);
    s.operations[1].resolution = OperationResolution::Open(OpenRemainder {
        name: "b".to_owned(),
        reason: "unbound fixture law".to_owned(),
        reopening: "supply resident law".to_owned(),
    });
    let mut value = input(&s, &[(1, 1, 2)], false);
    value.sharing.push(SharingDeclaration {
        family: "kv".to_owned(),
        kind: StructureKind::Kv,
        states: vec!["a".to_owned(), "b".to_owned()],
        source_members: vec!["a".to_owned(), "b".to_owned()],
    });
    let result = condense(value).unwrap();
    assert_eq!(result.open_source_operations, vec!["b"]);
    assert!(matches!(
        result.structures[0].status,
        SharingStatus::Open { .. }
    ));
}

#[test]
fn foreign_structure_member_refuses_instead_of_fabricating_a_binding() {
    let s = seal(&["a", "b", "c"]);
    let mut value = input(&s, &[(1, 1, 2)], false);
    value.sharing.push(SharingDeclaration {
        family: "qk".to_owned(),
        kind: StructureKind::Qk,
        states: vec!["a".to_owned(), "not-w1".to_owned()],
        source_members: vec!["a".to_owned()],
    });
    assert!(matches!(
        condense(value),
        Err(CondensationRefusal::ForeignStructureMember { .. })
    ));
}

#[test]
fn a_grouped_state_must_cover_each_source_operation_exactly_once() {
    let s = seal(&["a", "b", "c"]);
    let mut value = input(&s, &[(1, 1, 2)], false);
    value.states = vec![
        CondensationState {
            id: "layer-0".to_owned(),
            source_members: vec!["a".to_owned(), "b".to_owned()],
        },
        CondensationState {
            id: "layer-1".to_owned(),
            source_members: vec!["c".to_owned()],
        },
    ];
    for receiver in &mut value.receivers {
        receiver.values = BTreeMap::from([("layer-0".to_owned(), 1), ("layer-1".to_owned(), 2)]);
    }
    value.successors[0].next = BTreeMap::from([
        ("layer-0".to_owned(), "layer-1".to_owned()),
        ("layer-1".to_owned(), "layer-1".to_owned()),
    ]);
    value.sharing.push(SharingDeclaration {
        family: "grouped-qk".to_owned(),
        kind: StructureKind::Qk,
        states: vec!["layer-0".to_owned()],
        source_members: vec!["a".to_owned(), "b".to_owned()],
    });
    let result = condense(value).unwrap();
    assert_eq!(result.source_operations, 3);
    assert_eq!(result.structures[0].state_members, vec!["layer-0"]);
    assert_eq!(result.structures[0].source_members, vec!["a", "b"]);
    assert_eq!(result.structures[0].bindings.len(), 2);
}

#[test]
fn a_source_operation_cannot_be_claimed_by_two_states() {
    let s = seal(&["a", "b", "c"]);
    let mut value = input(&s, &[(1, 1, 2)], false);
    value.states[1].source_members = vec!["a".to_owned(), "c".to_owned()];
    assert!(matches!(
        condense(value),
        Err(CondensationRefusal::DuplicateSourceMember(member)) if member == "a"
    ));
}

#[test]
fn complete_conduct_reopens_a_pair_after_a_locally_factored_target_splits() {
    let s = seal(&["a", "b", "c", "d", "e", "f"]);
    let ids = ["a", "b", "c", "d", "e", "f"];
    let states = ids
        .iter()
        .map(|id| CondensationState {
            id: (*id).to_owned(),
            source_members: vec![(*id).to_owned()],
        })
        .collect();
    let receiver = ReceiverSignature {
        name: "future".to_owned(),
        values: BTreeMap::from([
            ("a".to_owned(), 0),
            ("b".to_owned(), 0),
            ("c".to_owned(), 1),
            ("d".to_owned(), 1),
            ("e".to_owned(), 2),
            ("f".to_owned(), 3),
        ]),
    };
    // A and B have the same immediate target block (C/D), so the one-step test holds. The
    // second step reaches E/F, where the complete Moore/Nerode conduct separates them.
    let successor = SuccessorSignature {
        input: "step".to_owned(),
        next: BTreeMap::from([
            ("a".to_owned(), "c".to_owned()),
            ("b".to_owned(), "d".to_owned()),
            ("c".to_owned(), "e".to_owned()),
            ("d".to_owned(), "f".to_owned()),
            ("e".to_owned(), "e".to_owned()),
            ("f".to_owned(), "f".to_owned()),
        ]),
    };
    let result = condense(CondensationInput {
        seal: &s,
        states,
        receivers: vec![receiver],
        successors: vec![successor],
        sharing: Vec::new(),
    })
    .unwrap();
    let candidate = result
        .candidates
        .iter()
        .find(|candidate| candidate.members == ["a", "b"])
        .expect("delayed candidate");
    assert!(candidate.factorization.holds);
    assert!(matches!(
        candidate.status,
        CandidateStatus::RequiresRefinement
    ));
    assert!(
        result
            .no_factor
            .iter()
            .any(|remainder| remainder.candidate == ["a", "b"])
    );
}
