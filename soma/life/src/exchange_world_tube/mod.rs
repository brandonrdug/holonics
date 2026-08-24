//! The exact exchange world-tube mounted as provider-neutral record incidence.
//!
//! A JSONL file, dialogue role, tool name, provider and path are exterior faces. The native atlas
//! retains occurrence identity, ordered JSON incidence, exact scalar-content contact classes,
//! unresolved fibres and chronology receivers. Equal content founds a contact class; it never
//! identifies the situated occurrences which inhabit that class.

mod continuation;
mod json_record;
mod mount;
mod receiver;
mod rest;
mod source;

use std::{collections::BTreeMap, ops::Range, path::PathBuf};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

pub use continuation::{
    derive_continuation_aperture, ContinuationAperture, ContinuationExclusion,
    ContinuationFamily, ContinuationPartition, ContinuationWorldWindow, MessageAddress,
    ShortestHistorySeparator,
};
pub use mount::{mount_exchange_world_tube_on_device, ExchangeContainerSpec, ExchangeMountError};
pub use receiver::{
    BranchPermutationReceipt, ExactJoinPopulation, LineageAblationReceipt, ScalarJoinWitness,
};
pub use rest::{
    exchange_world_tube_rest_digest, remount_exchange_world_tube, write_exchange_world_tube_rest,
    EXCHANGE_REST_PREFIX,
};
pub use source::{
    attach_visible_exchange_faces, discover_complete_exchange_aperture,
    CompleteExchangeSource, VisibleProjectionReceipt,
};

/// One exact SHA-256 content address. It is not an occurrence identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Digest32([u8; 32]);

impl Digest32 {
    pub const ZERO: Self = Self([0; 32]);

    pub fn of(octets: &[u8]) -> Self {
        Self::from_sha(Sha256::digest(octets))
    }

    pub(crate) fn from_sha(digest: impl AsRef<[u8]>) -> Self {
        let mut out = [0u8; 32];
        out.copy_from_slice(digest.as_ref());
        Self(out)
    }

    pub const fn octets(self) -> [u8; 32] {
        self.0
    }

    pub fn render(self) -> String {
        const HEX: &[u8; 16] = b"0123456789abcdef";
        let mut out = String::with_capacity(64);
        for octet in self.0 {
            out.push(HEX[(octet >> 4) as usize] as char);
            out.push(HEX[(octet & 15) as usize] as char);
        }
        out
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum NodeKind {
    Object,
    Array,
    Key,
    String,
    Atom,
}

impl NodeKind {
    pub(crate) const fn wire(self) -> u8 {
        match self {
            Self::Object => 1,
            Self::Array => 2,
            Self::Key => 3,
            Self::String => 4,
            Self::Atom => 5,
        }
    }

    pub(crate) fn from_wire(wire: u8) -> Result<Self, String> {
        match wire {
            1 => Ok(Self::Object),
            2 => Ok(Self::Array),
            3 => Ok(Self::Key),
            4 => Ok(Self::String),
            5 => Ok(Self::Atom),
            _ => Err(format!("unknown exchange-node kind {wire}")),
        }
    }
}

/// One node local to one JSON record. The record occurrence supplies the rest of its identity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RecordNode {
    pub parent: Option<u32>,
    pub position: u32,
    pub kind: NodeKind,
    pub content: Digest32,
}

/// An object key and the value occurrence it faces. The decoded key remains an exterior codec
/// coordinate and is never consulted by the scalar-contact law.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct FieldFace {
    pub key_node: u32,
    pub value_node: u32,
    pub key: String,
    pub raw_key_sha256: Digest32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExchangeRecord {
    pub container: u32,
    pub ordinal: u64,
    pub raw_range: Range<u64>,
    pub raw_sha256: Digest32,
    pub root_sha256: Digest32,
    pub node_from: u64,
    pub node_extent: u32,
    pub field_from: u64,
    pub field_extent: u32,
}

/// Exterior lineage attached to a content-addressed container occurrence. None of these faces
/// enters the content-law digest or scalar quotient.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ContainerLineageFaces {
    pub locator: PathBuf,
    pub provider: String,
    pub material_kind: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExchangeContainer {
    pub ordinal: u32,
    pub captured_extent: u64,
    pub prefix_sha256: Digest32,
    pub record_from: u64,
    pub record_extent: u64,
    pub incomplete_tail: Option<Range<u64>>,
    pub blank_records: Vec<Range<u64>>,
    pub lineage: ContainerLineageFaces,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GlobalNode {
    pub record: u64,
    pub local: RecordNode,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GlobalFieldFace {
    pub record: u64,
    pub local: FieldFace,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ScalarContactSite {
    pub node: u64,
    pub content: Digest32,
    pub class: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeviceContactReceipt {
    pub schema: String,
    pub device: String,
    pub scalar_sites: usize,
    pub contact_classes: usize,
    pub launches: u64,
    pub block_threads: u32,
    pub warp_size: u32,
    pub cpu_semantic_replay: bool,
}

/// One visible-language codec face attached to the richer record occurrence which carried it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct VisibleMessageFace {
    pub container: u32,
    pub record: u64,
    pub raw_range: Range<u64>,
    pub occurrence: String,
    pub text_sha256: Digest32,
    pub text: String,
    pub provider_face: String,
    pub speaker_face: String,
    pub phase_face: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExcludedPopulation {
    pub blank_records: u64,
    pub incomplete_tails: u64,
    pub visible_membrane_controls: u64,
    pub unavailable_private_reasoning_required: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CorrespondenceFibres {
    pub singleton_classes: u64,
    pub repeated_classes: u64,
    pub repeated_sites: u64,
    /// The complete member population by class. A receiver may open any class later; no pairwise
    /// cross-product is materialized or silently dropped.
    pub class_members: BTreeMap<u32, Vec<u64>>,
}

/// The one continuing mounted atlas. It intentionally has no `Clone`: rest/remount and branch
/// receivers receive exact testimony, never a duplicate ecology.
#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct ExchangeWorldTube {
    pub schema: String,
    pub source_occurrence_sha256: Digest32,
    pub content_law_sha256: Digest32,
    pub containers: Vec<ExchangeContainer>,
    pub records: Vec<ExchangeRecord>,
    pub nodes: Vec<GlobalNode>,
    pub fields: Vec<GlobalFieldFace>,
    pub scalar_sites: Vec<ScalarContactSite>,
    pub visible_messages: Vec<VisibleMessageFace>,
    pub fibres: CorrespondenceFibres,
    pub excluded: ExcludedPopulation,
    pub device: DeviceContactReceipt,
}

impl ExchangeWorldTube {
    pub fn record_occurrence(&self, record: u64) -> Digest32 {
        let occurrence = &self.records[record as usize];
        let mut digest = Sha256::new();
        digest.update(b"exchange-record-occurrence/v1");
        digest.update(self.source_occurrence_sha256.octets());
        digest.update(occurrence.container.to_le_bytes());
        digest.update(occurrence.ordinal.to_le_bytes());
        digest.update(occurrence.raw_range.start.to_le_bytes());
        digest.update(occurrence.raw_range.end.to_le_bytes());
        digest.update(occurrence.raw_sha256.octets());
        Digest32::from_sha(digest.finalize())
    }

    pub fn node_occurrence(&self, node: u64) -> Digest32 {
        let situated = &self.nodes[node as usize];
        let mut digest = Sha256::new();
        digest.update(b"exchange-node-occurrence/v1");
        digest.update(self.record_occurrence(situated.record).octets());
        digest.update((node - self.records[situated.record as usize].node_from).to_le_bytes());
        digest.update(situated.local.content.octets());
        Digest32::from_sha(digest.finalize())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temporary_root() -> PathBuf {
        let serial = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("time advances")
            .as_nanos();
        std::env::temp_dir().join(format!(
            "soma-exchange-world-tube-{}-{serial}",
            std::process::id()
        ))
    }

    #[test]
    #[ignore = "requires the resident CUDA exact-quotient entry"]
    fn one_atlas_keeps_occurrences_contacts_permutation_and_detached_rest() {
        let root = temporary_root();
        std::fs::create_dir_all(&root).unwrap();
        let main = root.join("main.jsonl");
        let branch = root.join("branch.jsonl");
        let main_text = concat!(
            "{\"uuid\":\"root\",\"sessionId\":\"session\",\"message\":\"same\"}\n",
            "{\"uuid\":\"call\",\"parentUuid\":\"root\",\"call_id\":\"contact\",\"message\":\"work\"}\n",
            "{\"uuid\":\"return\",\"parentUuid\":\"call\",\"call_id\":\"contact\",\"message\":\"same\"}\n"
        );
        let branch_text = concat!(
            "{\"uuid\":\"branch\",\"parentUuid\":\"root\",\"sessionId\":\"session\",\"tool_use_id\":\"tool\"}\n",
            "{\"uuid\":\"result\",\"parentUuid\":\"branch\",\"sessionId\":\"session\",\"id\":\"tool\"}\n"
        );
        std::fs::write(&main, main_text).unwrap();
        std::fs::write(&branch, branch_text).unwrap();
        let mut world = mount_exchange_world_tube_on_device(&[
            ExchangeContainerSpec {
                locator: main,
                provider_face: "first".to_owned(),
                material_kind_face: "main".to_owned(),
            },
            ExchangeContainerSpec {
                locator: branch,
                provider_face: "second".to_owned(),
                material_kind_face: "branch".to_owned(),
            },
        ])
        .unwrap();
        world
            .attach_visible_messages(
                vec![
                    VisibleMessageFace {
                        container: 0,
                        record: 0,
                        raw_range: world.records[0].raw_range.clone(),
                        occurrence: "visible/0".to_owned(),
                        text_sha256: Digest32::of(b"same"),
                        text: "same".to_owned(),
                        provider_face: "first".to_owned(),
                        speaker_face: "face-a".to_owned(),
                        phase_face: "face-a".to_owned(),
                    },
                    VisibleMessageFace {
                        container: 0,
                        record: 2,
                        raw_range: world.records[2].raw_range.clone(),
                        occurrence: "visible/2".to_owned(),
                        text_sha256: Digest32::of(b"same"),
                        text: "same".to_owned(),
                        provider_face: "first".to_owned(),
                        speaker_face: "face-b".to_owned(),
                        phase_face: "face-b".to_owned(),
                    },
                ],
                0,
            )
            .unwrap();
        let parent = world.joins_between_key_faces("parentUuid", "uuid", true);
        let tool = world.joins_between_key_faces("tool_use_id", "id", false);
        let call = world.joins_between_key_faces("call_id", "call_id", false);
        assert!(parent.pair_population > 0 && tool.pair_population > 0 && call.pair_population > 0);
        assert_eq!(world.repeated_visible_content_population().len(), 1);
        let permutation = world.branch_permutation_receipt(0, 3);
        assert!(permutation.chronology_changed && permutation.certificate_ordered);
        assert!(world.lineage_ablation(true, true).content_law_preserved);
        let rest = root.join("rest.ewtb");
        write_exchange_world_tube_rest(&world, &rest).unwrap();
        assert_eq!(remount_exchange_world_tube(&rest).unwrap(), world);
        std::fs::remove_dir_all(root).unwrap();
    }
}
