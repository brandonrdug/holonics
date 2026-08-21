use std::collections::BTreeMap;

use holonic_engine::foreign_codec_rest::{ExteriorCodebookRest, ExteriorCodecArtifact};

#[cfg(test)]
use super::hashing::identity_preview;
use super::hashing::{
    attach_cohort_evidence, digest_bytes, incidence_change, is_digest, longest_common_window,
    material_identity, surface_rebase_identity, token_multiset,
};
#[cfg(test)]
use super::types::ExteriorTextCodec;
use super::types::MANIFEST_SCHEMA;
use super::types::{
    CultivationMaterialManifest, MaterialArm, MaterialIdentity, MaterialInput,
    MaterialLineageRefusal,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TokenizedMaterial<'a> {
    pub input: MaterialInput<'a>,
    pub token_ids: Vec<u32>,
    pub codec_variant: String,
}

impl CultivationMaterialManifest {
    pub fn validate(&self) -> Result<(), MaterialLineageRefusal> {
        if self.schema != MANIFEST_SCHEMA {
            return Err(MaterialLineageRefusal::W1Boundary(format!(
                "wrong W3 schema {}",
                self.schema
            )));
        }
        let mut identities = std::collections::BTreeSet::new();
        for entry in &self.entries {
            if !identities.insert(entry.identity.clone()) {
                return Err(MaterialLineageRefusal::DuplicateIdentity(
                    entry.identity.clone(),
                ));
            }
        }
        for arm in [
            MaterialArm::Development,
            MaterialArm::StructuralHeldOut,
            MaterialArm::CodecVariant,
            MaterialArm::SubjectDisjointControl,
            MaterialArm::NoOp,
            MaterialArm::MatchedFoil,
        ] {
            if !self.entries.iter().any(|entry| entry.arm == arm) {
                return Err(MaterialLineageRefusal::MissingArm(arm));
            }
        }
        let by_identity: BTreeMap<&str, &MaterialIdentity> = self
            .entries
            .iter()
            .map(|entry| (entry.identity.as_str(), entry))
            .collect();
        for entry in &self.entries {
            if let Some(surface_rebase_identity) = &entry.surface_rebase_identity {
                if !is_digest(surface_rebase_identity) {
                    return Err(MaterialLineageRefusal::InvalidSurfaceRebaseIdentity {
                        identity: entry.identity.clone(),
                    });
                }
            }
            match entry.arm {
                MaterialArm::Development => {
                    if entry.structural_overlap.is_some() {
                        return Err(MaterialLineageRefusal::UnexpectedOverlapEvidence {
                            identity: entry.identity.clone(),
                        });
                    }
                    if entry.incidence_change.is_some() {
                        return Err(MaterialLineageRefusal::UnexpectedIncidenceEvidence {
                            identity: entry.identity.clone(),
                        });
                    }
                }
                MaterialArm::StructuralHeldOut | MaterialArm::CodecVariant => {
                    let related = entry.related_to.as_deref().ok_or(
                        MaterialLineageRefusal::MissingRelation {
                            identity: entry.identity.clone(),
                            arm: entry.arm,
                        },
                    )?;
                    let source = by_identity.get(related).ok_or_else(|| {
                        MaterialLineageRefusal::UnknownRelation {
                            identity: entry.identity.clone(),
                            related_to: related.to_owned(),
                        }
                    })?;
                    if source.arm != MaterialArm::Development || source.lineage == entry.lineage {
                        return Err(MaterialLineageRefusal::LineageNotSeparated {
                            identity: entry.identity.clone(),
                            related_to: related.to_owned(),
                        });
                    }
                    if entry.arm == MaterialArm::StructuralHeldOut {
                        if entry.incidence_change.is_some() {
                            return Err(MaterialLineageRefusal::UnexpectedIncidenceEvidence {
                                identity: entry.identity.clone(),
                            });
                        }
                        if source.token_ids == entry.token_ids {
                            return Err(MaterialLineageRefusal::UnchangedRelatedMaterial {
                                identity: entry.identity.clone(),
                                related_to: related.to_owned(),
                            });
                        }
                        if entry.structural_overlap.as_ref()
                            != Some(&longest_common_window(&source.token_ids, &entry.token_ids))
                        {
                            return Err(MaterialLineageRefusal::StructuralOverlapMismatch {
                                identity: entry.identity.clone(),
                            });
                        }
                    } else {
                        if entry.structural_overlap.is_some() {
                            return Err(MaterialLineageRefusal::UnexpectedOverlapEvidence {
                                identity: entry.identity.clone(),
                            });
                        }
                        if entry.incidence_change.is_some() {
                            return Err(MaterialLineageRefusal::UnexpectedIncidenceEvidence {
                                identity: entry.identity.clone(),
                            });
                        }
                        if source.codec_variant == entry.codec_variant {
                            return Err(MaterialLineageRefusal::UnchangedRelatedMaterial {
                                identity: entry.identity.clone(),
                                related_to: related.to_owned(),
                            });
                        }
                        if source.text_sha256 != entry.text_sha256 {
                            let Some(declared) = entry.surface_rebase_identity.as_deref() else {
                                return Err(MaterialLineageRefusal::CodecVariantNeedsRebase {
                                    identity: entry.identity.clone(),
                                    related_to: related.to_owned(),
                                });
                            };
                            if declared
                                != surface_rebase_identity(
                                    related,
                                    &source.text_sha256,
                                    &entry.text_sha256,
                                )
                            {
                                return Err(MaterialLineageRefusal::InvalidSurfaceRebaseIdentity {
                                    identity: entry.identity.clone(),
                                });
                            }
                        }
                    }
                }
                MaterialArm::SubjectDisjointControl => {
                    if entry.structural_overlap.is_some() {
                        return Err(MaterialLineageRefusal::UnexpectedOverlapEvidence {
                            identity: entry.identity.clone(),
                        });
                    }
                    if entry.incidence_change.is_some() {
                        return Err(MaterialLineageRefusal::UnexpectedIncidenceEvidence {
                            identity: entry.identity.clone(),
                        });
                    }
                    if self.entries.iter().any(|other| {
                        other.identity != entry.identity
                            && other.arm != MaterialArm::SubjectDisjointControl
                            && other.arm != MaterialArm::NoOp
                            && other.subject == entry.subject
                    }) {
                        return Err(MaterialLineageRefusal::SubjectNotDisjoint {
                            identity: entry.identity.clone(),
                            subject: entry.subject.clone(),
                        });
                    }
                }
                MaterialArm::NoOp => {
                    let related = entry.related_to.as_deref().ok_or_else(|| {
                        MaterialLineageRefusal::NoOpRequiresDevelopment {
                            identity: entry.identity.clone(),
                        }
                    })?;
                    let source = by_identity.get(related).ok_or_else(|| {
                        MaterialLineageRefusal::UnknownRelation {
                            identity: entry.identity.clone(),
                            related_to: related.to_owned(),
                        }
                    })?;
                    if source.arm != MaterialArm::Development || source.lineage == entry.lineage {
                        return Err(MaterialLineageRefusal::NoOpRequiresDevelopment {
                            identity: entry.identity.clone(),
                        });
                    }
                    if entry.structural_overlap.is_some() {
                        return Err(MaterialLineageRefusal::UnexpectedOverlapEvidence {
                            identity: entry.identity.clone(),
                        });
                    }
                    if entry.incidence_change.is_some() {
                        return Err(MaterialLineageRefusal::UnexpectedIncidenceEvidence {
                            identity: entry.identity.clone(),
                        });
                    }
                    if entry.surface_rebase_identity.is_some()
                        || entry.text_sha256.is_empty()
                        || entry.token_ids.is_empty()
                    {
                        return Err(MaterialLineageRefusal::NoOpCarriesMaterial {
                            identity: entry.identity.clone(),
                        });
                    }
                    if source.text_sha256 != entry.text_sha256
                        || source.text_octets != entry.text_octets
                        || source.token_ids != entry.token_ids
                        || source.codec_variant != entry.codec_variant
                    {
                        return Err(MaterialLineageRefusal::NoOpMaterialMismatch {
                            identity: entry.identity.clone(),
                            related_to: related.to_owned(),
                        });
                    }
                }
                MaterialArm::MatchedFoil => {
                    let related = entry.related_to.as_deref().ok_or(
                        MaterialLineageRefusal::MissingRelation {
                            identity: entry.identity.clone(),
                            arm: entry.arm,
                        },
                    )?;
                    let source = by_identity.get(related).ok_or_else(|| {
                        MaterialLineageRefusal::UnknownRelation {
                            identity: entry.identity.clone(),
                            related_to: related.to_owned(),
                        }
                    })?;
                    if source.arm != MaterialArm::Development || source.subject != entry.subject {
                        return Err(MaterialLineageRefusal::FoilSubjectMismatch {
                            identity: entry.identity.clone(),
                            related_to: related.to_owned(),
                        });
                    }
                    if entry.structural_overlap.is_some() {
                        return Err(MaterialLineageRefusal::UnexpectedOverlapEvidence {
                            identity: entry.identity.clone(),
                        });
                    }
                    if source.token_ids.len() != entry.token_ids.len()
                        || token_multiset(&source.token_ids) != token_multiset(&entry.token_ids)
                    {
                        return Err(MaterialLineageRefusal::FoilPopulationMismatch {
                            identity: entry.identity.clone(),
                            related_to: related.to_owned(),
                        });
                    }
                    if source.token_ids == entry.token_ids {
                        return Err(MaterialLineageRefusal::FoilIncidenceUnchanged {
                            identity: entry.identity.clone(),
                            related_to: related.to_owned(),
                        });
                    }
                    if entry.incidence_change.as_ref()
                        != Some(&incidence_change(&source.token_ids, &entry.token_ids))
                    {
                        return Err(MaterialLineageRefusal::IncidenceEvidenceMismatch {
                            identity: entry.identity.clone(),
                        });
                    }
                }
            }
        }
        let expected = self.digest_without_manifest();
        if expected != self.manifest_sha256 {
            return Err(MaterialLineageRefusal::W1Boundary(format!(
                "manifest digest {actual} does not match {expected}",
                actual = self.manifest_sha256
            )));
        }
        Ok(())
    }

    #[cfg(test)]
    pub fn identities(&self, arm: MaterialArm) -> impl Iterator<Item = &MaterialIdentity> {
        self.entries.iter().filter(move |entry| entry.arm == arm)
    }
}

#[cfg(test)]
pub fn admit_text<C: ExteriorTextCodec>(
    codebook: &ExteriorCodebookRest,
    codec_artifact: &ExteriorCodecArtifact,
    codec: &C,
    inputs: &[MaterialInput<'_>],
) -> Result<CultivationMaterialManifest, MaterialLineageRefusal> {
    codebook
        .validate_with_codec(codec_artifact)
        .map_err(|error| MaterialLineageRefusal::W1Boundary(error.to_string()))?;
    let mut passages = Vec::with_capacity(inputs.len());
    for input in inputs {
        let tokens = codec
            .encode(input.text)
            .map_err(|reason| MaterialLineageRefusal::Codec {
                identity: identity_preview(input),
                reason,
            })?;
        passages.push(TokenizedMaterial {
            input: input.clone(),
            token_ids: tokens,
            codec_variant: codec.variant_identity().to_owned(),
        });
    }
    admit_tokenized(codebook, codec_artifact, passages)
}

pub fn admit_tokenized<'a>(
    codebook: &ExteriorCodebookRest,
    codec_artifact: &ExteriorCodecArtifact,
    passages: impl IntoIterator<Item = TokenizedMaterial<'a>>,
) -> Result<CultivationMaterialManifest, MaterialLineageRefusal> {
    codebook
        .validate_with_codec(codec_artifact)
        .map_err(|error| MaterialLineageRefusal::W1Boundary(error.to_string()))?;
    let descriptor = codebook.codec.as_ref().ok_or_else(|| {
        MaterialLineageRefusal::W1Boundary("W1 codebook has no tokenizer descriptor".to_owned())
    })?;
    let mut entries = Vec::new();
    for passage in passages {
        let input = passage.input;
        validate_input(&input)?;
        let identity = material_identity(&input, &passage.token_ids, &passage.codec_variant);
        if let Some(surface_rebase_identity) = input.surface_rebase_identity {
            if !is_digest(surface_rebase_identity) {
                return Err(MaterialLineageRefusal::InvalidSurfaceRebaseIdentity {
                    identity: identity.clone(),
                });
            }
        }
        if input.text.is_empty() {
            return Err(MaterialLineageRefusal::EmptyText { identity });
        }
        for &token in &passage.token_ids {
            if token >= codebook.vocabulary_extent {
                return Err(MaterialLineageRefusal::TokenOutOfRange {
                    identity: identity.clone(),
                    token,
                    extent: codebook.vocabulary_extent,
                });
            }
            if codebook.source_id(token).is_none() {
                return Err(MaterialLineageRefusal::OpenToken { identity, token });
            }
        }
        entries.push(MaterialIdentity {
            identity,
            lineage: input.lineage.to_owned(),
            subject: input.subject.to_owned(),
            arm: input.arm,
            related_to: input.related_to.map(str::to_owned),
            surface_rebase_identity: input.surface_rebase_identity.map(str::to_owned),
            text_sha256: if input.text.is_empty() {
                String::new()
            } else {
                digest_bytes(input.text.as_bytes())
            },
            text_octets: input.text.len() as u64,
            token_ids: passage.token_ids,
            codec_variant: passage.codec_variant,
            structural_overlap: None,
            incidence_change: None,
        });
    }
    entries.sort_by(|left, right| left.identity.cmp(&right.identity));
    attach_cohort_evidence(&mut entries);
    let mut manifest = CultivationMaterialManifest {
        schema: MANIFEST_SCHEMA.to_owned(),
        w1_codebook_sha256: codebook.codebook_sha256.clone(),
        tokenizer_sha256: descriptor.tokenizer_json_sha256.clone(),
        tokenizer_config_sha256: descriptor.tokenizer_config_sha256.clone(),
        entries,
        manifest_sha256: String::new(),
    };
    manifest.manifest_sha256 = manifest.digest_without_manifest();
    manifest.validate()?;
    Ok(manifest)
}

fn validate_input(input: &MaterialInput<'_>) -> Result<(), MaterialLineageRefusal> {
    if input.lineage.is_empty() {
        return Err(MaterialLineageRefusal::EmptyField { field: "lineage" });
    }
    if input.subject.is_empty() {
        return Err(MaterialLineageRefusal::EmptyField { field: "subject" });
    }
    if input.lineage.starts_with('/')
        || input.lineage.starts_with('~')
        || input.lineage.contains('\\')
        || input.lineage.contains("/home/")
    {
        return Err(MaterialLineageRefusal::AbsoluteLineage(
            input.lineage.to_owned(),
        ));
    }
    Ok(())
}
