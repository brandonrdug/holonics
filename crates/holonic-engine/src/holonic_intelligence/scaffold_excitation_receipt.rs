//! Exact exterior admission of the complete Gemma 4 excitation receipt.
//!
//! Paths, source identities, modality names, and BF16 codewords remain cold testimony. This
//! reader verifies the actual returned files and yields typed excitation families; only the
//! separate scaffold lift may found source-neutral native current from them.

use std::{collections::BTreeSet, fs, path::Path};

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
struct WireReceipt {
    schema: String,
    text: WireOrgan,
    vision: WireOrgan,
    audio: WireOrgan,
    video: WireVideoOrgan,
}

#[derive(Deserialize)]
struct WireOrgan {
    returns: Vec<WireReturn>,
}

#[derive(Clone, Deserialize)]
struct WireReturn {
    occurrence: String,
    source_sha256: String,
    entering_bf16: String,
    entering_sha256: String,
    returned_bf16: String,
    returned_sha256: String,
    complete_layer_count: usize,
}

#[derive(Deserialize)]
struct WireVideoOrgan {
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
    let families = [
        (
            ExteriorModality::Text,
            BoundaryId(10),
            BoundaryId(11),
            receipt.text.returns,
        ),
        (
            ExteriorModality::Image,
            BoundaryId(20),
            BoundaryId(21),
            receipt.vision.returns,
        ),
        (
            ExteriorModality::Audio,
            BoundaryId(30),
            BoundaryId(31),
            receipt.audio.returns,
        ),
        (
            ExteriorModality::Video,
            BoundaryId(40),
            BoundaryId(41),
            receipt.video.frame_returns,
        ),
    ]
    .into_iter()
    .map(|(modality, entering, emitting, returns)| {
        let excitations = returns
            .into_iter()
            .map(|returned| {
                let current_event = EventId(event);
                event = event
                    .checked_add(1)
                    .ok_or(CompleteExcitationReceiptError::ForeignReturn)?;
                let entering_bytes = fs::read(root.join(&returned.entering_bf16))?;
                let returned_bytes = fs::read(root.join(&returned.returned_bf16))?;
                if returned.complete_layer_count == 0
                    || digest(&entering_bytes) != returned.entering_sha256
                    || digest(&returned_bytes) != returned.returned_sha256
                {
                    return Err(CompleteExcitationReceiptError::ForeignReturn);
                }
                Ok(ForeignBf16Excitation {
                    event: current_event,
                    predecessor: None,
                    entering_boundary: entering,
                    emitting_boundary: emitting,
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
    Ok(CompleteGemma4ExcitationReceipt { families })
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
