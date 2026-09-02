//! Exact exterior admission of the complete Gemma 4 excitation receipt.
//!
//! Paths, source identities, modality names, and BF16 codewords remain cold testimony. This
//! reader verifies the actual returned files and yields typed excitation families; only the
//! separate scaffold lift may found source-neutral native current from them.

use std::{
    collections::BTreeSet,
    fs,
    path::{Component, Path},
};

use serde::Deserialize;
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::{BoundaryId, EventId};

use super::{ExteriorModality, ForeignBf16Excitation};

pub const COMPLETE_GEMMA4_EXCITATION_SCHEMA: &str = "holonics.scf2.complete-gemma4-excitation.v2";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Gemma4ExcitationFamily {
    pub modality: ExteriorModality,
    pub excitations: Vec<ForeignBf16Excitation>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompleteGemma4ExcitationReceipt {
    pub families: Vec<Gemma4ExcitationFamily>,
    pub open_exterior: Vec<String>,
}

impl CompleteGemma4ExcitationReceipt {
    pub fn interleaved(&self) -> Vec<ForeignBf16Excitation> {
        let mut families = self
            .families
            .iter()
            .map(|family| family.excitations.iter())
            .collect::<Vec<_>>();
        let mut returned = Vec::new();
        loop {
            let mut advanced = false;
            for family in &mut families {
                if let Some(excitation) = family.next() {
                    returned.push(excitation.clone());
                    advanced = true;
                }
            }
            if !advanced {
                break;
            }
        }
        returned
    }
}

#[derive(Debug, Error)]
pub enum CompleteExcitationReceiptError {
    #[error("the complete excitation receipt could not be read: {0}")]
    Io(#[from] std::io::Error),
    #[error("the complete excitation receipt is malformed: {0}")]
    Json(#[from] serde_json::Error),
    #[error("the complete excitation receipt uses an unknown schema")]
    Schema,
    #[error("one foreign return lost its complete layer frontier or BF16 identity")]
    ForeignReturn,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireReceipt {
    schema: String,
    text: WireOrgan,
    vision: WireOrgan,
    audio: WireOrgan,
    video: WireVideoOrgan,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireOrgan {
    returns: Vec<WireReturn>,
}

#[derive(Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct WireReturn {
    occurrence: String,
    source_sha256: String,
    entering_bf16: String,
    entering_sha256: String,
    returned_bf16: String,
    returned_sha256: String,
    complete_layer_count: usize,
    #[serde(default)]
    frame_ordinal: Option<u64>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct WireVideoOrgan {
    temporal_frame_lineage: bool,
    frame_returns: Vec<WireReturn>,
}

pub fn read_complete_gemma4_excitation_receipt(
    root: &Path,
) -> Result<CompleteGemma4ExcitationReceipt, CompleteExcitationReceiptError> {
    let receipt: WireReceipt = serde_json::from_slice(&fs::read(root.join("receipt.json"))?)?;
    if receipt.schema != COMPLETE_GEMMA4_EXCITATION_SCHEMA {
        return Err(CompleteExcitationReceiptError::Schema);
    }
    let mut event = 1u64;
    let mut wire_families = vec![
        (ExteriorModality::Text, receipt.text.returns),
        (ExteriorModality::Image, receipt.vision.returns),
        (ExteriorModality::Audio, receipt.audio.returns),
    ];
    let mut open_exterior = Vec::new();
    if receipt.video.temporal_frame_lineage {
        wire_families.push((ExteriorModality::Video, receipt.video.frame_returns));
    } else {
        open_exterior.push(
            "sampled-video remains open until distinct temporally ordered frame occurrences return"
                .to_owned(),
        );
    }
    let families = wire_families
        .into_iter()
        .map(|(modality, returns)| {
            let excitations = returns
                .into_iter()
                .enumerate()
                .map(|(family_ordinal, returned)| {
                    let current_event = EventId(event);
                    event = event
                        .checked_add(1)
                        .ok_or(CompleteExcitationReceiptError::ForeignReturn)?;
                    if modality == ExteriorModality::Video
                        && returned.frame_ordinal
                            != Some(
                                u64::try_from(family_ordinal)
                                    .map_err(|_| CompleteExcitationReceiptError::ForeignReturn)?,
                            )
                    {
                        return Err(CompleteExcitationReceiptError::ForeignReturn);
                    }
                    let entering_boundary = BoundaryId(
                        current_event
                            .0
                            .checked_mul(2)
                            .ok_or(CompleteExcitationReceiptError::ForeignReturn)?,
                    );
                    let emitting_boundary = BoundaryId(
                        entering_boundary
                            .0
                            .checked_add(1)
                            .ok_or(CompleteExcitationReceiptError::ForeignReturn)?,
                    );
                    let entering_bytes = read_contained(root, Path::new(&returned.entering_bf16))?;
                    let returned_bytes = read_contained(root, Path::new(&returned.returned_bf16))?;
                    if returned.complete_layer_count == 0
                        || digest(&entering_bytes) != returned.entering_sha256
                        || digest(&returned_bytes) != returned.returned_sha256
                    {
                        return Err(CompleteExcitationReceiptError::ForeignReturn);
                    }
                    Ok(ForeignBf16Excitation {
                        event: current_event,
                        predecessor: None,
                        entering_boundary,
                        emitting_boundary,
                        source_occurrence: returned.occurrence,
                        exterior_modality: modality,
                        entering_codewords: words(&entering_bytes)?,
                        returned_codewords: words(&returned_bytes)?,
                        interventions: BTreeSet::from([
                            format!("withdraw-excitation/{}", current_event.0),
                            format!("source-sha256/{}", returned.source_sha256),
                        ]),
                        receiver_consequences: BTreeSet::from([returned.returned_sha256]),
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            if excitations.is_empty() {
                return Err(CompleteExcitationReceiptError::ForeignReturn);
            }
            Ok(Gemma4ExcitationFamily {
                modality,
                excitations,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(CompleteGemma4ExcitationReceipt {
        families,
        open_exterior,
    })
}

fn read_contained(root: &Path, relative: &Path) -> Result<Vec<u8>, std::io::Error> {
    if relative.is_absolute()
        || relative
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "the excitation artifact path leaves its receipt root",
        ));
    }
    fs::read(root.join(relative))
}

fn words(bytes: &[u8]) -> Result<Vec<u16>, CompleteExcitationReceiptError> {
    if bytes.is_empty() || bytes.len() % 2 != 0 {
        return Err(CompleteExcitationReceiptError::ForeignReturn);
    }
    Ok(bytes
        .chunks_exact(2)
        .map(|word| u16::from_le_bytes([word[0], word[1]]))
        .collect())
}

fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn returned(name: &str, identity: &str) -> serde_json::Value {
        json!({
            "occurrence": name,
            "source_sha256": identity,
            "entering_bf16": format!("{name}-in.bf16"),
            "entering_sha256": identity,
            "returned_bf16": format!("{name}-out.bf16"),
            "returned_sha256": identity,
            "complete_layer_count": 1
        })
    }

    #[test]
    fn boundaries_follow_occurrences_and_non_temporal_video_remains_open() {
        let root = std::env::temp_dir().join(format!(
            "complete-gemma4-receipt-{}-{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("receipt")
        ));
        std::fs::create_dir_all(&root).expect("root");
        let bytes = 0x3f80u16.to_le_bytes();
        let identity = digest(&bytes);
        for name in ["text", "vision", "audio"] {
            std::fs::write(root.join(format!("{name}-in.bf16")), bytes).expect("entering");
            std::fs::write(root.join(format!("{name}-out.bf16")), bytes).expect("returned");
        }
        let receipt = json!({
            "schema": COMPLETE_GEMMA4_EXCITATION_SCHEMA,
            "text": {"returns": [returned("text", &identity)]},
            "vision": {"returns": [returned("vision", &identity)]},
            "audio": {"returns": [returned("audio", &identity)]},
            "video": {"temporal_frame_lineage": false, "frame_returns": []}
        });
        std::fs::write(
            root.join("receipt.json"),
            serde_json::to_vec(&receipt).expect("receipt bytes"),
        )
        .expect("receipt");
        let admitted = read_complete_gemma4_excitation_receipt(&root).expect("admitted");
        assert_eq!(admitted.families.len(), 3);
        let boundaries = admitted
            .families
            .iter()
            .flat_map(|family| &family.excitations)
            .map(|excitation| {
                (
                    excitation.entering_boundary.0,
                    excitation.emitting_boundary.0,
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(boundaries, vec![(2, 3), (4, 5), (6, 7)]);
        assert!(
            admitted
                .families
                .iter()
                .all(|family| family.modality != ExteriorModality::Video)
        );
        assert_eq!(admitted.open_exterior.len(), 1);
        std::fs::remove_dir_all(root).expect("cleanup");
    }

    #[test]
    fn unknown_fields_and_paths_outside_the_receipt_root_refuse() {
        let root = std::env::temp_dir().join(format!(
            "complete-gemma4-receipt-refusal-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&root).expect("root");
        let bytes = 0x3f80u16.to_le_bytes();
        let identity = digest(&bytes);
        for name in ["text", "vision", "audio"] {
            std::fs::write(root.join(format!("{name}-in.bf16")), bytes).expect("entering");
            std::fs::write(root.join(format!("{name}-out.bf16")), bytes).expect("returned");
        }
        let mut receipt = json!({
            "schema": COMPLETE_GEMMA4_EXCITATION_SCHEMA,
            "text": {"returns": [returned("text", &identity)]},
            "vision": {"returns": [returned("vision", &identity)]},
            "audio": {"returns": [returned("audio", &identity)]},
            "video": {"temporal_frame_lineage": false, "frame_returns": []},
            "unknown": true
        });
        std::fs::write(
            root.join("receipt.json"),
            serde_json::to_vec(&receipt).expect("wire"),
        )
        .expect("receipt");
        assert!(read_complete_gemma4_excitation_receipt(&root).is_err());
        receipt.as_object_mut().expect("object").remove("unknown");
        receipt["text"]["returns"][0]["entering_bf16"] = json!("../outside.bf16");
        std::fs::write(
            root.join("receipt.json"),
            serde_json::to_vec(&receipt).expect("wire"),
        )
        .expect("receipt");
        assert!(read_complete_gemma4_excitation_receipt(&root).is_err());
        std::fs::remove_dir_all(root).expect("cleanup");
    }
}
