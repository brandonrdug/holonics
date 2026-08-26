use std::collections::BTreeMap;

use sha2::{Digest, Sha256};

use super::types::{
    ContiguousTokenWindow, CultivationMaterialManifest, IncidenceChange, MaterialArm,
    MaterialIdentity, MaterialInput,
};

pub fn material_identity(
    input: &MaterialInput<'_>,
    token_ids: &[u32],
    codec_variant: &str,
) -> String {
    let mut hasher = Sha256::new();
    frame(&mut hasher, input.lineage.as_bytes());
    frame(&mut hasher, input.subject.as_bytes());
    hasher.update([input.arm as u8]);
    match input.related_to {
        Some(value) => {
            hasher.update([1]);
            frame(&mut hasher, value.as_bytes());
        }
        None => hasher.update([0]),
    }
    frame(&mut hasher, input.text.as_bytes());
    match input.surface_rebase_identity {
        Some(value) => {
            hasher.update([1]);
            frame(&mut hasher, value.as_bytes());
        }
        None => hasher.update([0]),
    }
    frame(&mut hasher, codec_variant.as_bytes());
    hasher.update((token_ids.len() as u64).to_le_bytes());
    for token in token_ids {
        hasher.update(token.to_le_bytes());
    }
    format!("{:x}", hasher.finalize())
}

pub fn surface_rebase_identity(
    related_to: &str,
    development_text_sha256: &str,
    variant_text_sha256: &str,
) -> String {
    let mut hasher = Sha256::new();
    frame(&mut hasher, b"holonic-engine.phoenix.surface-rebase.v1");
    frame(&mut hasher, related_to.as_bytes());
    frame(&mut hasher, development_text_sha256.as_bytes());
    frame(&mut hasher, variant_text_sha256.as_bytes());
    format!("{:x}", hasher.finalize())
}

#[cfg(test)]
pub(super) fn identity_preview(input: &MaterialInput<'_>) -> String {
    let mut hasher = Sha256::new();
    frame(&mut hasher, input.lineage.as_bytes());
    frame(&mut hasher, input.subject.as_bytes());
    format!("{:x}", hasher.finalize())
}

impl CultivationMaterialManifest {
    pub(super) fn digest_without_manifest(&self) -> String {
        let mut hasher = Sha256::new();
        frame(&mut hasher, super::types::MANIFEST_SCHEMA.as_bytes());
        frame(&mut hasher, self.w1_codebook_sha256.as_bytes());
        frame(&mut hasher, self.tokenizer_sha256.as_bytes());
        match &self.tokenizer_config_sha256 {
            Some(value) => {
                hasher.update([1]);
                frame(&mut hasher, value.as_bytes());
            }
            None => hasher.update([0]),
        }
        for entry in &self.entries {
            hash_entry(&mut hasher, entry);
        }
        format!("{:x}", hasher.finalize())
    }
}

fn hash_entry(hasher: &mut Sha256, entry: &MaterialIdentity) {
    frame(hasher, entry.identity.as_bytes());
    frame(hasher, entry.lineage.as_bytes());
    frame(hasher, entry.subject.as_bytes());
    hasher.update([entry.arm as u8]);
    match &entry.related_to {
        Some(value) => {
            hasher.update([1]);
            frame(hasher, value.as_bytes());
        }
        None => hasher.update([0]),
    }
    match &entry.surface_rebase_identity {
        Some(value) => {
            hasher.update([1]);
            frame(hasher, value.as_bytes());
        }
        None => hasher.update([0]),
    }
    frame(hasher, entry.text_sha256.as_bytes());
    hasher.update(entry.text_octets.to_le_bytes());
    frame(hasher, entry.codec_variant.as_bytes());
    hasher.update((entry.token_ids.len() as u64).to_le_bytes());
    for token in &entry.token_ids {
        hasher.update(token.to_le_bytes());
    }
    match &entry.structural_overlap {
        Some(overlap) => {
            hasher.update([1]);
            hasher.update(overlap.development_start.to_le_bytes());
            hasher.update(overlap.held_out_start.to_le_bytes());
            hasher.update(overlap.length.to_le_bytes());
            hasher.update((overlap.token_ids.len() as u64).to_le_bytes());
            for token in &overlap.token_ids {
                hasher.update(token.to_le_bytes());
            }
        }
        None => hasher.update([0]),
    }
    match &entry.incidence_change {
        Some(change) => {
            hasher.update([1]);
            hasher.update(change.extent.to_le_bytes());
            hasher.update((change.changed_positions.len() as u64).to_le_bytes());
            for position in &change.changed_positions {
                hasher.update(position.to_le_bytes());
            }
        }
        None => hasher.update([0]),
    }
}

pub(super) fn attach_cohort_evidence(entries: &mut [MaterialIdentity]) {
    for index in 0..entries.len() {
        if entries[index].arm != MaterialArm::StructuralHeldOut {
            continue;
        }
        let Some(related) = entries[index].related_to.as_deref() else {
            continue;
        };
        let Ok(source_index) =
            entries.binary_search_by(|entry| entry.identity.as_str().cmp(related))
        else {
            continue;
        };
        entries[index].structural_overlap = Some(longest_common_window(
            &entries[source_index].token_ids,
            &entries[index].token_ids,
        ));
    }
    for index in 0..entries.len() {
        if entries[index].arm != MaterialArm::MatchedFoil {
            continue;
        }
        let Some(related) = entries[index].related_to.as_deref() else {
            continue;
        };
        let Ok(source_index) =
            entries.binary_search_by(|entry| entry.identity.as_str().cmp(related))
        else {
            continue;
        };
        entries[index].incidence_change = Some(incidence_change(
            &entries[source_index].token_ids,
            &entries[index].token_ids,
        ));
    }
}

pub(super) fn longest_common_window(
    development: &[u32],
    held_out: &[u32],
) -> ContiguousTokenWindow {
    let mut best = ContiguousTokenWindow {
        development_start: 0,
        held_out_start: 0,
        length: 0,
        token_ids: Vec::new(),
    };
    for development_start in 0..development.len() {
        for held_out_start in 0..held_out.len() {
            let mut length = 0usize;
            while development_start + length < development.len()
                && held_out_start + length < held_out.len()
                && development[development_start + length] == held_out[held_out_start + length]
            {
                length += 1;
            }
            let earlier = (development_start, held_out_start)
                < (
                    best.development_start as usize,
                    best.held_out_start as usize,
                );
            if length > best.length as usize
                || (length == best.length as usize && length > 0 && earlier)
            {
                best = ContiguousTokenWindow {
                    development_start: development_start as u64,
                    held_out_start: held_out_start as u64,
                    length: length as u64,
                    token_ids: held_out[held_out_start..held_out_start + length].to_vec(),
                };
            }
        }
    }
    best
}

pub(super) fn token_multiset(tokens: &[u32]) -> BTreeMap<u32, u64> {
    let mut counts = BTreeMap::new();
    for token in tokens {
        *counts.entry(*token).or_insert(0) += 1;
    }
    counts
}

pub(super) fn incidence_change(development: &[u32], foil: &[u32]) -> IncidenceChange {
    IncidenceChange {
        extent: development.len() as u64,
        changed_positions: development
            .iter()
            .zip(foil)
            .enumerate()
            .filter_map(|(position, (left, right))| (left != right).then_some(position as u64))
            .collect(),
    }
}

pub(super) fn is_digest(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

pub(super) fn digest_bytes(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn frame(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}
