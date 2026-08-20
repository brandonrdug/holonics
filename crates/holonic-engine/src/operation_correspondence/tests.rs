use std::collections::BTreeMap;

use super::*;
use crate::causal::EventId;
use crate::evolution::EvolutionLawId;
use crate::ported_operation::{OperationSpecies, PortedOperationComplex, SourceTestimony};

fn source(id: &str) -> SourceOperationOccurrence {
    SourceOperationOccurrence {
        id: id.to_owned(),
        source_identity: "fixture-topology".to_owned(),
        deed: "layer-0".to_owned(),
        family: "fixture-family".to_owned(),
        parameters: BTreeMap::new(),
        event: EventId(1),
        law: EvolutionLawId(1),
        operation: "contract".to_owned(),
        species: OperationSpecies::Transport,
        inputs: vec!["residual".to_owned()],
        outputs: vec!["projected".to_owned()],
        carrier: Some("weights.q".to_owned()),
    }
}

fn native(id: &str) -> OperationCorrespondence {
    let graph = graph();
    OperationCorrespondence {
        source_id: id.to_owned(),
        resolution: OperationResolution::Native(NativeOperationBinding {
            source_id: id.to_owned(),
            resident_law: "contract".to_owned(),
            species: OperationSpecies::Transport,
            native_population: Some("native.weights.q".to_owned()),
            inputs: vec![PortCorrespondence {
                ordinal: 0,
                source: "residual".to_owned(),
                native: "resident.residual".to_owned(),
            }],
            outputs: vec![PortCorrespondence {
                ordinal: 0,
                source: "projected".to_owned(),
                native: "resident.projected".to_owned(),
            }],
            graph_key: graph.key,
        }),
    }
}

fn graph() -> NativeGraphIdentity {
    NativeGraphIdentity::derived_with_topology(
        3,
        2,
        "cooperative",
        vec!["k-reduction".to_owned()],
        vec!["contract".to_owned()],
        vec!["residual->projected".to_owned()],
    )
}

fn population(name: &str) -> PopulationCorrespondence {
    PopulationCorrespondence {
        source_population: name.to_owned(),
        resolution: PopulationResolution::Native {
            native_population: format!("native.{name}"),
        },
    }
}

fn complete() -> OperationCorrespondenceSeal {
    OperationCorrespondenceSeal::new(
        vec![source("layer-0::fixture-topology::event-1")],
        vec![native("layer-0::fixture-topology::event-1")],
        vec!["weights.q".to_owned()],
        vec![population("weights.q")],
        vec![graph()],
    )
}

#[test]
fn missing_occurrence_refuses_before_seal() {
    let mut seal = complete();
    seal.operations.clear();
    assert!(matches!(
        seal.validate(),
        Err(CorrespondenceRefusal::MissingOccurrence { .. })
    ));
}

#[test]
fn duplicate_occurrence_refuses_before_seal() {
    let mut seal = complete();
    seal.operations
        .push(native("layer-0::fixture-topology::event-1"));
    assert!(matches!(
        seal.validate(),
        Err(CorrespondenceRefusal::DuplicateOccurrence { .. })
    ));
}

#[test]
fn unbound_occurrence_is_not_silently_open() {
    let mut seal = complete();
    seal.operations[0].resolution = OperationResolution::Open(OpenRemainder {
        name: String::new(),
        reason: "not yet".to_owned(),
        reopening: "later".to_owned(),
    });
    assert!(matches!(
        seal.validate(),
        Err(CorrespondenceRefusal::InvalidRemainder { .. })
    ));
}

#[test]
fn named_open_remainder_is_allowed_and_serialization_is_stable() {
    let mut seal = complete();
    seal.operations[0].resolution = OperationResolution::Open(OpenRemainder {
        name: "unfounded-law".to_owned(),
        reason: "no resident law founded".to_owned(),
        reopening: "return with a typed resident law and graph identity".to_owned(),
    });
    let sealed = seal
        .seal()
        .expect("explicit remainder closes the coverage question");
    assert_eq!(sealed.validate().expect("valid").open_occurrences, 1);
    assert!(
        sealed
            .stable_json()
            .expect("json")
            .contains("unfounded-law")
    );
    let json = sealed.stable_json().expect("json");
    let remounted = OperationCorrespondenceSeal::from_stable_json(&json).expect("round trip");
    assert_eq!(remounted.stable_json().expect("stable json"), json);
    let mut wrong: serde_json::Value = serde_json::from_str(&json).expect("object");
    wrong["schema"] = serde_json::Value::String("foreign.schema.v0".to_owned());
    let refused = OperationCorrespondenceSeal::from_stable_json(
        &serde_json::to_string(&wrong).expect("object json"),
    );
    assert!(matches!(
        refused,
        Err(CorrespondenceRefusal::WrongSchema { .. })
    ));
}

#[test]
fn arbitrary_graph_key_cannot_authenticate_a_native_binding() {
    let mut seal = complete();
    if let OperationResolution::Native(binding) = &mut seal.operations[0].resolution {
        binding.graph_key = "caller-asserted-graph".to_owned();
    }
    assert!(matches!(
        seal.validate(),
        Err(CorrespondenceRefusal::GraphIdentityMissing { .. })
    ));
}

#[test]
fn complete_native_seal_validates_and_round_trips() {
    let sealed = complete().seal().expect("complete native binding");
    assert_eq!(sealed.validate().expect("valid seal").native_occurrences, 1);
    let json = sealed.stable_json().expect("stable json");
    let remounted = OperationCorrespondenceSeal::from_stable_json(&json).expect("round trip");
    assert_eq!(remounted.stable_json().expect("stable json"), json);
}

fn assert_graph_tamper_refused(seal: OperationCorrespondenceSeal) {
    assert!(matches!(
        seal.validate(),
        Err(CorrespondenceRefusal::GraphIdentityNotDerived { .. })
    ));
}

#[test]
fn graph_topology_tamper_is_refused() {
    let mut seal = complete();
    seal.graphs[0].topology[0] = "different-edge".to_owned();
    assert_graph_tamper_refused(seal);
}

#[test]
fn graph_chronology_tamper_is_refused() {
    let mut seal = complete();
    seal.graphs[0].chronology[0] = "different-law".to_owned();
    assert_graph_tamper_refused(seal);
}

#[test]
fn graph_count_tamper_is_refused() {
    let mut seal = complete();
    seal.graphs[0].nodes += 1;
    assert_graph_tamper_refused(seal);
}

#[test]
fn graph_tiling_tamper_is_refused() {
    let mut seal = complete();
    seal.graphs[0].tiling = "different-tiling".to_owned();
    assert_graph_tamper_refused(seal);
}

#[test]
fn source_enumeration_refuses_missing_operation_or_law_instead_of_dropping_event() {
    let mut complex = PortedOperationComplex::new("fixture deed");
    let output = complex.port("output");
    let law = complex
        .bind_operation(
            "walk",
            OperationSpecies::Construction,
            vec![],
            vec![output],
            None,
            Vec::new(),
        )
        .expect("law");
    complex.occur(law).expect("event");
    complex.operations.clear();
    assert!(matches!(
        SourceOperationOccurrence::from_complex("fixture", &complex),
        Err(CorrespondenceRefusal::MissingOperation { .. })
    ));

    let mut complex = PortedOperationComplex::new("fixture deed");
    let output = complex.port("output");
    let law = complex
        .bind_operation(
            "walk",
            OperationSpecies::Construction,
            vec![],
            vec![output],
            None,
            Vec::new(),
        )
        .expect("law");
    complex.occur(law).expect("event");
    complex.shape.laws.clear();
    assert!(matches!(
        SourceOperationOccurrence::from_complex("fixture", &complex),
        Err(CorrespondenceRefusal::MissingLaw { .. })
    ));
}

#[test]
fn source_enumeration_refuses_a_missing_boundary_port() {
    let missing = crate::category::BoundaryId(999);
    let mut complex = PortedOperationComplex::new("fixture deed");
    let output = complex.port("output");
    let law = complex
        .bind_operation(
            "walk",
            OperationSpecies::Transport,
            vec![],
            vec![output],
            None,
            Vec::new(),
        )
        .expect("law");
    complex.occur(law).expect("event");
    complex
        .shape
        .laws
        .get_mut(&law)
        .expect("law")
        .outputs
        .push(missing);
    assert!(matches!(
        SourceOperationOccurrence::from_complex("fixture", &complex),
        Err(CorrespondenceRefusal::MissingBoundary { boundary: 999, .. })
    ));
}

#[test]
fn graph_identity_keeps_same_counts_with_different_topology_apart() {
    let left = NativeGraphIdentity::derived_with_topology(
        3,
        2,
        "cooperative",
        vec!["reduce".to_owned()],
        vec!["law-a".to_owned()],
        vec!["a->b".to_owned()],
    );
    let right = NativeGraphIdentity::derived_with_topology(
        3,
        2,
        "cooperative",
        vec!["reduce".to_owned()],
        vec!["law-b".to_owned()],
        vec!["a->b".to_owned()],
    );
    assert_ne!(left.key, right.key);
}

#[test]
fn topology_identity_keeps_same_shape_with_different_operation_body_apart() {
    let mut left = PortedOperationComplex::new("fixture deed");
    let output = left.port("output");
    let law = left
        .bind_operation(
            "walk",
            OperationSpecies::Construction,
            vec![],
            vec![output],
            Some("weights.a".to_owned()),
            Vec::new(),
        )
        .expect("law");
    left.occur(law).expect("event");
    let mut right = left.clone();
    right.operations.get_mut(&law).expect("operation").species = OperationSpecies::Transport;
    assert_ne!(topology_identity(&left), topology_identity(&right));
}

#[test]
fn topology_identity_ignores_relocation_but_keeps_implementation_symbol() {
    let mut left = PortedOperationComplex::new("fixture deed");
    let output = left.port("output");
    let law = left
        .bind_operation(
            "walk",
            OperationSpecies::Construction,
            vec![],
            vec![output],
            None,
            vec![SourceTestimony::Implementation {
                locator: "/original/modeling.py".to_owned(),
                symbol: "Walk.forward".to_owned(),
            }],
        )
        .expect("law");
    left.occur(law).expect("event");

    let mut relocated = left.clone();
    if let SourceTestimony::Implementation { locator, .. } = &mut relocated
        .operations
        .get_mut(&law)
        .expect("operation")
        .testimony[0]
    {
        *locator = "/mounted/modeling.py".to_owned();
    }
    assert_eq!(topology_identity(&left), topology_identity(&relocated));

    let mut changed = relocated.clone();
    if let SourceTestimony::Implementation { symbol, .. } = &mut changed
        .operations
        .get_mut(&law)
        .expect("operation")
        .testimony[0]
    {
        *symbol = "Walk.backward".to_owned();
    }
    assert_ne!(topology_identity(&left), topology_identity(&changed));
}

#[test]
fn parametric_family_identity_is_distinct_from_a_fixed_graph_instance() {
    let mut complex = PortedOperationComplex::new("fixture deed");
    let output = complex.port("output");
    let law = complex
        .bind_operation(
            "walk",
            OperationSpecies::Construction,
            vec![],
            vec![output],
            None,
            Vec::new(),
        )
        .expect("law");
    complex.occur(law).expect("event");
    let mut sliding = BTreeMap::new();
    sliding.insert("head_width".to_owned(), "256".to_owned());
    let mut full = BTreeMap::new();
    full.insert("head_width".to_owned(), "512".to_owned());
    let left =
        SourceOperationOccurrence::from_complex_family("fixture", "attention", sliding, &complex)
            .expect("sliding");
    let right =
        SourceOperationOccurrence::from_complex_family("fixture", "attention", full, &complex)
            .expect("full");
    assert_ne!(left[0].id, right[0].id);
    assert_ne!(left[0].parameters, right[0].parameters);
}
