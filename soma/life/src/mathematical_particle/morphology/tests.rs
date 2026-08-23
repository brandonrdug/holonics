use holonic_engine::cuda_refine::DeviceDynamicMorphology;

use super::super::DerivationRecurrenceRest;
use super::{
    ConstraintReceiver, DynamicMorphologyCandidate, MorphologyDecision,
    ReturnedConstraintOccurrence,
};

fn predecessor() -> DerivationRecurrenceRest {
    DerivationRecurrenceRest::read(br#"{"schema":"holonics.r2.derivation-recurrence-rest.v1","predecessor_product_sha256":"0000000000000000000000000000000000000000000000000000000000000000","native_action":[0,0],"native_starts":[1,1],"generator_member_population":2,"open_exterior":["open"]}"#).expect("predecessor")
}

fn returns(last_orientation: i32) -> Vec<ReturnedConstraintOccurrence> {
    ConstraintReceiver::FAMILY
        .into_iter()
        .enumerate()
        .map(|(at, receiver)| ReturnedConstraintOccurrence {
            receiver,
            emission_occurrence: format!("emission-{at}"),
            world_occurrence: format!("world-{at}"),
            return_occurrence: format!("return-{at}"),
            consequence_sha256: format!("{at:064x}"),
            primitive_orientation: if at + 1 == ConstraintReceiver::FAMILY.len() {
                last_orientation
            } else {
                1
            },
            support_native_states: vec![0],
        })
        .collect()
}

#[test]
fn a_declined_card_return_gives_the_same_predecessor_back() {
    let candidate = DynamicMorphologyCandidate::found(
        predecessor(),
        "predecessor",
        returns(0),
        vec![2, 4],
        "development",
        "held-out",
        "disjoint-control",
    )
    .expect("candidate");
    assert_eq!(candidate.recurrence_starts(), [0, 1]);
    let device = DeviceDynamicMorphology {
        returned_adjoint: vec![4, 0],
        predecessor_action: vec![0, 0, 2],
        successor_action: vec![0, 0, 2],
        withdrawn_action: vec![0, 0, 2],
        predecessor_trace: vec![],
        successor_trace: vec![],
        withdrawn_trace: vec![],
        predecessor_lengths: vec![],
        successor_lengths: vec![],
        withdrawn_lengths: vec![],
        trace_stride: 4,
        committed: false,
        supported_state: Some(0),
        launches: 1,
        synchronizations: 1,
        block_threads: 32,
        active_lanes: 2,
        host_ingress_octets: 0,
        host_egress_octets: 0,
        resident_octets: 0,
    };
    let decision = candidate.finish(&device).expect("decline");
    let MorphologyDecision::Declined { predecessor, .. } = decision else {
        panic!("a zero returned face cannot commit")
    };
    assert_eq!(predecessor.native_action, vec![0, 0]);
}
