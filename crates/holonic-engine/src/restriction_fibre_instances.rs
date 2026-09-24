//! Plan phase 10 equality evidence: every engine reconstruction fibre and separator that became an
//! instance of the core restriction fibre (`holonics::restriction::fibre`) keeps its wire,
//! its `Debug` face and its reading.
//!
//! Each `Old*` struct below is the exact derive the alias replaced; the tests compare serialized
//! bytes, remount in both directions, and compare the `Debug` text and the unknown-field policy.

use std::collections::BTreeSet;
use std::fmt::Debug;

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

use crate::EventId;
use crate::native_ecology::recurrent::BoundaryFibre;
use crate::native_ecology::recurrent_condensation::{
    CondensedFibre, CondensedFibreMember, CondensedSeparator,
};
use crate::native_spool::{NativeCollapsedFibre, NativeShortestSeparator};
use crate::receiver_exact_compression::{InputId, ItemId, Observation, ReceiverId};
use crate::receiver_history_compression::{NativeStateId, ReconstructionFibre};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct NativeCollapsedFibreOld {
    native: NativeStateId,
    occurrences: BTreeSet<EventId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct BoundaryFibreOld {
    native: NativeStateId,
    source_sections: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct CondensedFibreOld {
    native: u32,
    members: Vec<CondensedFibreMember>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ReconstructionFibreOld {
    native: NativeStateId,
    sources: BTreeSet<ItemId>,
}

/// `new` and `old` carry the same content: equal wire, mutual remount, equal `Debug` once the old
/// derive's `*Old` name is read as the replaced struct's name, and the same verdict on an unknown
/// field.
fn same_wire_named<New, Old>(new: &New, old: &Old, old_name: &str, name: &str)
where
    New: Serialize + DeserializeOwned + PartialEq + Debug,
    Old: Serialize + DeserializeOwned + PartialEq + Debug,
{
    let wire = serde_json::to_string(new).expect("serializes");
    assert_eq!(wire, serde_json::to_string(old).expect("serializes"));
    assert_eq!(&serde_json::from_str::<New>(&wire).expect("remounts"), new);
    assert_eq!(&serde_json::from_str::<Old>(&wire).expect("remounts"), old);
    assert_eq!(
        format!("{new:?}"),
        format!("{old:?}").replacen(old_name, name, 1)
    );
    assert_eq!(
        format!("{new:#?}"),
        format!("{old:#?}").replacen(old_name, name, 1)
    );
    let mut value = serde_json::to_value(new).expect("a value");
    value
        .as_object_mut()
        .expect("a struct")
        .insert("unlisted".to_owned(), serde_json::Value::Bool(true));
    assert_eq!(
        serde_json::from_value::<New>(value.clone()).is_ok(),
        serde_json::from_value::<Old>(value).is_ok()
    );
}

#[test]
fn the_class_fibres_are_core_preimage_fibres_with_their_wires_unchanged() {
    let collapsed =
        NativeCollapsedFibre::new(NativeStateId(4), BTreeSet::from([EventId(9), EventId(2)]));
    same_wire_named(
        &collapsed,
        &NativeCollapsedFibreOld {
            native: NativeStateId(4),
            occurrences: BTreeSet::from([EventId(9), EventId(2)]),
        },
        "NativeCollapsedFibreOld",
        "NativeCollapsedFibre",
    );
    // The spool fixture's retained fibres remount through the old wire unchanged.
    for fibre in crate::native_spool::fixture::spool().reconstruction_fibres {
        let old = NativeCollapsedFibreOld {
            native: fibre.native,
            occurrences: fibre.members.clone(),
        };
        same_wire_named(
            &fibre,
            &old,
            "NativeCollapsedFibreOld",
            "NativeCollapsedFibre",
        );
    }

    same_wire_named(
        &BoundaryFibre::new(NativeStateId(1), vec!["b".to_owned(), "a".to_owned()]),
        &BoundaryFibreOld {
            native: NativeStateId(1),
            source_sections: vec!["b".to_owned(), "a".to_owned()],
        },
        "BoundaryFibreOld",
        "BoundaryFibre",
    );

    let members = vec![
        CondensedFibreMember {
            occurrence: "left".to_owned(),
            terminal_potential_sha256: Some("aa".to_owned()),
        },
        CondensedFibreMember {
            occurrence: "right".to_owned(),
            terminal_potential_sha256: None,
        },
    ];
    same_wire_named(
        &CondensedFibre::new(3, members.clone()),
        &CondensedFibreOld { native: 3, members },
        "CondensedFibreOld",
        "CondensedFibre",
    );

    // The observable fibre's wire ignores unknown fields; the alias keeps that policy.
    same_wire_named(
        &ReconstructionFibre::new(NativeStateId(0), BTreeSet::from([ItemId(5), ItemId(1)])),
        &ReconstructionFibreOld {
            native: NativeStateId(0),
            sources: BTreeSet::from([ItemId(5), ItemId(1)]),
        },
        "ReconstructionFibreOld",
        "ReconstructionFibre",
    );
}

#[test]
fn the_native_shortest_separator_reads_as_the_core_separator() {
    let wire = NativeShortestSeparator {
        left: EventId(1),
        right: EventId(2),
        word: vec![InputId(3), InputId(0)],
        receiver: ReceiverId(7),
        left_observation: Observation(10),
        right_observation: Observation(11),
    };
    let core = wire.shortest_separator();
    assert_eq!((core.left, core.right), (wire.left, wire.right));
    assert_eq!(core.distinguishing_word, wire.word);
    assert_eq!(core.receiver(), Some(&wire.receiver));
    assert_eq!(core.left_observation(), Some(&wire.left_observation));
    assert_eq!(core.right_observation(), Some(&wire.right_observation));
    assert!(!core.separated_by_terminus);
    let separation = core.separation();
    assert_eq!(
        separation.readings(),
        &(Some(wire.left_observation), Some(wire.right_observation))
    );
}

#[test]
fn the_condensed_separator_reads_as_a_core_separation() {
    let wire = CondensedSeparator {
        native: 2,
        left_occurrence: "a".to_owned(),
        right_occurrence: "b".to_owned(),
        left_potential_sha256: "11".to_owned(),
        right_potential_sha256: "22".to_owned(),
        shortest_history: vec![0, 1],
    };
    let separation = wire.separation();
    assert_eq!(separation.pair(), ("a".to_owned(), "b".to_owned()));
    assert_eq!(separation.witness(), &(2, vec![0, 1]));
    assert_eq!(separation.readings(), &("11".to_owned(), "22".to_owned()));
}
