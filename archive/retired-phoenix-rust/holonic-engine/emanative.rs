//! Emanative recurrence over the authenticated Phoenix full-tower boundary.
//!
//! [`ProductSession`] already owns one mounted inherited body and returns the complete plural
//! terminal potential. This module joins that return to the next entry while retaining occurrence
//! identity, the unresolved fibre and a detachable continuation rest. It owns no sampler,
//! language, conversation, cache, scheduler or second inference body.

use std::collections::BTreeSet;
use std::path::Path;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::exact_work::ExactWork;
use crate::phoenix::continuation::{ContinuationRuntimeIdentity, CultivatedBodyIdentity};
use crate::phoenix::runtime::{ProductSession, RuntimeReturn};
use crate::phoenix::session_factor_complex::SessionFactorComplexIdentity;
use crate::phoenix::streamed::{InterventionSite, ReceiverOption};
use crate::phoenix::tower::Intervention;

pub const EMANATIVE_REST_SCHEMA: &str = "holonic-engine.phoenix.emanative-continuation.v1";

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EmanativeOccurrence {
    pub address_sha256: String,
    pub predecessor_address_sha256: Option<String>,
    pub native_ids: Vec<u32>,
    pub native_ids_sha256: String,
    pub text: String,
    pub text_sha256: String,
    pub text_octets: u64,
}

impl EmanativeOccurrence {
    pub fn found(
        predecessor_address_sha256: Option<String>,
        native_ids: Vec<u32>,
        text: String,
    ) -> Result<Self, String> {
        if native_ids.is_empty() || text.is_empty() {
            return Err(
                "an emanative occurrence requires native incidence and a codec face".into(),
            );
        }
        let native_ids_sha256 = digest_native_ids(&native_ids);
        let text_sha256 = sha256(text.as_bytes());
        let address_sha256 = occurrence_address(
            predecessor_address_sha256.as_deref(),
            &native_ids_sha256,
            &text_sha256,
        );
        Ok(Self {
            address_sha256,
            predecessor_address_sha256,
            native_ids,
            native_ids_sha256,
            text_octets: text.len() as u64,
            text,
            text_sha256,
        })
    }

    fn validate(&self, expected_predecessor: Option<&str>) -> Result<(), String> {
        require_digest("occurrence address", &self.address_sha256)?;
        require_digest("native word", &self.native_ids_sha256)?;
        require_digest("text face", &self.text_sha256)?;
        if self.native_ids.is_empty()
            || self.text.is_empty()
            || self.text_octets != self.text.len() as u64
            || self.predecessor_address_sha256.as_deref() != expected_predecessor
            || self.native_ids_sha256 != digest_native_ids(&self.native_ids)
            || self.text_sha256 != sha256(self.text.as_bytes())
            || self.address_sha256
                != occurrence_address(
                    expected_predecessor,
                    &self.native_ids_sha256,
                    &self.text_sha256,
                )
        {
            return Err("emanative occurrence identity does not reconstruct".into());
        }
        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EmanativeCandidate {
    pub native_id: u32,
    pub surface: String,
    pub lower: i64,
    pub upper: i64,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EmanativePotential {
    pub vocabulary_extent: usize,
    pub grain: u32,
    pub top_lower: i64,
    pub plural: Vec<EmanativeCandidate>,
    pub separated: usize,
    pub complete_plural_sha256: String,
}

impl EmanativePotential {
    pub fn found(
        vocabulary_extent: usize,
        grain: u32,
        top_lower: i64,
        plural: Vec<EmanativeCandidate>,
        separated: usize,
    ) -> Result<Self, String> {
        let complete_plural_sha256 =
            potential_digest(vocabulary_extent, grain, top_lower, &plural, separated)?;
        let potential = Self {
            vocabulary_extent,
            grain,
            top_lower,
            plural,
            separated,
            complete_plural_sha256,
        };
        potential.validate()?;
        Ok(potential)
    }

    fn from_runtime(returned: &RuntimeReturn) -> Result<Self, String> {
        let generated = &returned.receipt.generated;
        let plural = generated
            .plural
            .iter()
            .map(|candidate| EmanativeCandidate {
                native_id: candidate.native_id,
                surface: candidate.surface.clone(),
                lower: candidate.lower,
                upper: candidate.upper,
            })
            .collect::<Vec<_>>();
        Self::found(
            generated.vocabulary_extent,
            generated.grain,
            generated.top_lower,
            plural,
            generated.separated,
        )
    }

    fn validate(&self) -> Result<(), String> {
        require_digest("complete plural future", &self.complete_plural_sha256)?;
        let ids = self
            .plural
            .iter()
            .map(|candidate| candidate.native_id)
            .collect::<BTreeSet<_>>();
        if self.vocabulary_extent == 0
            || self.grain == 0
            || self.plural.is_empty()
            || ids.len() != self.plural.len()
            || self.separated + self.plural.len() != self.vocabulary_extent
            || self.plural.iter().any(|candidate| {
                candidate.surface.is_empty()
                    || candidate.lower > candidate.upper
                    || candidate.upper < self.top_lower
            })
            || self.complete_plural_sha256
                != potential_digest(
                    self.vocabulary_extent,
                    self.grain,
                    self.top_lower,
                    &self.plural,
                    self.separated,
                )?
        {
            return Err("the complete plural potential does not reconstruct".into());
        }
        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExactBoundarySelection {
    pub law: String,
    pub selected_native_id: u32,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EmanativeFront {
    pub index: usize,
    pub before_address_sha256: String,
    pub after: Option<EmanativeOccurrence>,
    pub potential: EmanativePotential,
    pub selection: Option<ExactBoundarySelection>,
    pub semantic_receipt_sha256: String,
    pub exact_work: ExactWork,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub enum EmanativeStatus {
    Open,
    FrontierAperture {
        conducted_fronts: usize,
    },
    UnresolvedPlural {
        at_front: usize,
        complete_plural_sha256: String,
    },
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EmanativeContinuationRest {
    pub schema: String,
    pub body: CultivatedBodyIdentity,
    pub cultivation_continuation: Option<ContinuationRuntimeIdentity>,
    pub factor_complex: Option<SessionFactorComplexIdentity>,
    pub predecessor_rest_sha256: Option<String>,
    pub entering: EmanativeOccurrence,
    pub fronts: Vec<EmanativeFront>,
    pub codec_identity: String,
    pub status: EmanativeStatus,
    pub open_exterior: Vec<String>,
}

impl EmanativeContinuationRest {
    pub fn read(bytes: &[u8]) -> Result<Self, String> {
        let rest: Self = serde_json::from_slice(bytes).map_err(|error| error.to_string())?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, String> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| error.to_string())
    }

    pub fn current(&self) -> &EmanativeOccurrence {
        self.fronts
            .iter()
            .rev()
            .find_map(|front| front.after.as_ref())
            .unwrap_or(&self.entering)
    }

    pub fn emitted_native_ids(&self) -> Vec<u32> {
        self.fronts
            .iter()
            .filter_map(|front| {
                front
                    .selection
                    .as_ref()
                    .map(|selection| selection.selected_native_id)
            })
            .collect()
    }

    pub fn validate(&self) -> Result<(), String> {
        if self.schema != EMANATIVE_REST_SCHEMA || self.codec_identity.is_empty() {
            return Err("emanative continuation schema or codec identity is absent".into());
        }
        validate_body(&self.body)?;
        if let Some(predecessor) = &self.predecessor_rest_sha256 {
            require_digest("predecessor continuation rest", predecessor)?;
        }
        self.entering.validate(None)?;
        let mut cursor = &self.entering;
        let mut unresolved = None;
        for (index, front) in self.fronts.iter().enumerate() {
            front.potential.validate()?;
            require_digest("semantic tower receipt", &front.semantic_receipt_sha256)?;
            if front.index != index || front.before_address_sha256 != cursor.address_sha256 {
                return Err("emanative front chronology moved away from its predecessor".into());
            }
            match (&front.selection, &front.after) {
                (Some(selection), Some(after)) => {
                    if selection.law != "exact-singleton-maximizer-fibre"
                        || front.potential.plural.len() != 1
                        || selection.selected_native_id != front.potential.plural[0].native_id
                    {
                        return Err(
                            "a non-singleton future was presented as exact selection".into()
                        );
                    }
                    after.validate(Some(&cursor.address_sha256))?;
                    if after.native_ids.len() != cursor.native_ids.len() + 1
                        || !after.native_ids.starts_with(&cursor.native_ids)
                        || after.native_ids.last() != Some(&selection.selected_native_id)
                    {
                        return Err(
                            "the emitted face did not found the next native occurrence".into()
                        );
                    }
                    cursor = after;
                }
                (None, None)
                    if front.potential.plural.len() > 1 && index + 1 == self.fronts.len() =>
                {
                    unresolved = Some((index, front.potential.complete_plural_sha256.clone()));
                }
                _ => return Err("emanative front selection and successor do not commute".into()),
            }
        }
        match (&self.status, unresolved) {
            (EmanativeStatus::Open, None) => {}
            (EmanativeStatus::FrontierAperture { conducted_fronts }, None)
                if *conducted_fronts == self.fronts.len() => {}
            (
                EmanativeStatus::UnresolvedPlural {
                    at_front,
                    complete_plural_sha256,
                },
                Some((expected_at, expected_digest)),
            ) if *at_front == expected_at && *complete_plural_sha256 == expected_digest => {}
            _ => return Err("emanative status does not describe its terminal frontier".into()),
        }
        Ok(())
    }
}

/// One mounted owner of the inherited body and its continuing addressed occurrence.
pub struct EmanativeSession {
    product: ProductSession,
    rest: EmanativeContinuationRest,
}

impl EmanativeSession {
    pub fn begin(
        product_directory: impl AsRef<Path>,
        continuation_directory: Option<&Path>,
        entering_text: &str,
    ) -> Result<Self, String> {
        let product = open_product(product_directory, continuation_directory)?;
        let native_ids = product.encode(entering_text)?;
        let decoded = product.decode_native_ids(&native_ids)?;
        if product.encode(&decoded)? != native_ids {
            return Err(
                "the entering occurrence is not stable under its authenticated codec".into(),
            );
        }
        let entering = EmanativeOccurrence::found(None, native_ids, decoded)?;
        let rest = EmanativeContinuationRest {
            schema: EMANATIVE_REST_SCHEMA.to_owned(),
            body: product.body_identity()?,
            cultivation_continuation: product.continuation_identity()?,
            factor_complex: product.factor_complex_identity()?,
            predecessor_rest_sha256: None,
            entering,
            fronts: Vec::new(),
            codec_identity: product.source_codec_identity().to_owned(),
            status: EmanativeStatus::Open,
            open_exterior: vec![
                "world return has not crossed this continuation".to_owned(),
                "plural maximizer fibres require a declared exterior quotient".to_owned(),
                "the inherited prefix trajectory is not yet receiver-exactly condensed".to_owned(),
            ],
        };
        rest.validate()?;
        Ok(Self { product, rest })
    }

    pub fn resume(
        product_directory: impl AsRef<Path>,
        continuation_directory: Option<&Path>,
        rested_bytes: &[u8],
    ) -> Result<Self, String> {
        let product = open_product(product_directory, continuation_directory)?;
        Self::resume_mounted(product, rested_bytes)
    }

    /// Begin emanation from an already mounted product owner. This is the factor-complex seam:
    /// callers may remount the canonical cultivated rest into `ProductSession`, then move that
    /// same non-cloned owner here without opening another inference body.
    pub fn begin_mounted(product: ProductSession, entering_text: &str) -> Result<Self, String> {
        let native_ids = product.encode(entering_text)?;
        let decoded = product.decode_native_ids(&native_ids)?;
        if product.encode(&decoded)? != native_ids {
            return Err(
                "the entering occurrence is not stable under its authenticated codec".into(),
            );
        }
        let entering = EmanativeOccurrence::found(None, native_ids, decoded)?;
        let rest = EmanativeContinuationRest {
            schema: EMANATIVE_REST_SCHEMA.to_owned(),
            body: product.body_identity()?,
            cultivation_continuation: product.continuation_identity()?,
            factor_complex: product.factor_complex_identity()?,
            predecessor_rest_sha256: None,
            entering,
            fronts: Vec::new(),
            codec_identity: product.source_codec_identity().to_owned(),
            status: EmanativeStatus::Open,
            open_exterior: vec![
                "world return has not crossed this continuation".to_owned(),
                "plural maximizer fibres require a declared exterior quotient".to_owned(),
                "the inherited prefix trajectory is not yet receiver-exactly condensed".to_owned(),
            ],
        };
        rest.validate()?;
        Ok(Self { product, rest })
    }

    /// Resume one addressed emanative continuation through the exact already-mounted morphology.
    pub fn resume_mounted(product: ProductSession, rested_bytes: &[u8]) -> Result<Self, String> {
        let mut rest = EmanativeContinuationRest::read(rested_bytes)?;
        if rest.body != product.body_identity()?
            || rest.cultivation_continuation != product.continuation_identity()?
            || rest.factor_complex != product.factor_complex_identity()?
            || rest.codec_identity != product.source_codec_identity()
            || product.encode(&rest.current().text)? != rest.current().native_ids
        {
            return Err("the detached continuation does not address this mounted body".into());
        }
        rest.predecessor_rest_sha256 = Some(sha256(rested_bytes));
        rest.status = EmanativeStatus::Open;
        rest.validate()?;
        Ok(Self { product, rest })
    }

    pub fn rest(&self) -> &EmanativeContinuationRest {
        &self.rest
    }

    /// Return the same mounted product owner after the addressed emanative passage closes. This
    /// is an ownership transfer, not a clone or rollback, and permits later ablation/withdrawal to
    /// act on the exact body which emitted the inspected surface.
    pub fn into_product(self) -> ProductSession {
        self.product
    }

    /// Conduct one full tower and emit only when the returned maximizer fibre is exact.
    pub fn advance_exact(&mut self) -> Result<RuntimeReturn, String> {
        if self.rest.status != EmanativeStatus::Open {
            return Err("the continuation must be open before another frontier conducts".into());
        }
        let before_address_sha256 = self.rest.current().address_sha256.clone();
        let before_native_ids = self.rest.current().native_ids.clone();
        let runtime = self.product.infer_native_with_intervention(
            &before_native_ids,
            InterventionSite::Nowhere,
            &Intervention::None,
            ReceiverOption::Terminal,
        )?;
        if runtime.receipt.input.native_ids != before_native_ids {
            return Err("the tower moved the addressed predecessor occurrence".into());
        }
        let potential = EmanativePotential::from_runtime(&runtime)?;
        let semantic_receipt_sha256 = semantic_receipt_digest(&runtime)?;
        let index = self.rest.fronts.len();
        let (selection, after) = if potential.plural.len() == 1 {
            let selected_native_id = potential.plural[0].native_id;
            let mut native_ids = before_native_ids;
            native_ids.push(selected_native_id);
            let text = self.product.decode_native_ids(&native_ids)?;
            if self.product.encode(&text)? != native_ids {
                return Err(
                    "the emitted successor is not stable under the authenticated codec".into(),
                );
            }
            let after =
                EmanativeOccurrence::found(Some(before_address_sha256.clone()), native_ids, text)?;
            (
                Some(ExactBoundarySelection {
                    law: "exact-singleton-maximizer-fibre".to_owned(),
                    selected_native_id,
                }),
                Some(after),
            )
        } else {
            self.rest.status = EmanativeStatus::UnresolvedPlural {
                at_front: index,
                complete_plural_sha256: potential.complete_plural_sha256.clone(),
            };
            (None, None)
        };
        let front = EmanativeFront {
            index,
            before_address_sha256,
            after,
            potential,
            selection,
            semantic_receipt_sha256,
            exact_work: runtime.receipt.total_work.clone(),
        };
        self.rest.fronts.push(front);
        self.rest.validate()?;
        Ok(runtime)
    }

    pub fn seal_frontier_aperture(&mut self) -> Result<(), String> {
        if self.rest.status != EmanativeStatus::Open || self.rest.fronts.is_empty() {
            return Err("only a nonempty open continuation can meet a frontier aperture".into());
        }
        self.rest.status = EmanativeStatus::FrontierAperture {
            conducted_fronts: self.rest.fronts.len(),
        };
        self.rest.validate()
    }
}

fn open_product(
    product_directory: impl AsRef<Path>,
    continuation_directory: Option<&Path>,
) -> Result<ProductSession, String> {
    match continuation_directory {
        Some(continuation) => {
            ProductSession::open_with_continuation(product_directory, continuation)
        }
        None => ProductSession::open(product_directory),
    }
}

fn validate_body(body: &CultivatedBodyIdentity) -> Result<(), String> {
    for (name, digest) in [
        ("product", &body.product.sha256),
        ("predecessor", &body.predecessor.sha256),
        ("morphology", &body.morphology.sha256),
        ("runtime law", &body.runtime_law_sha256),
        ("complete body", &body.complete_sha256),
    ] {
        require_digest(name, digest)?;
    }
    let expected = digest_json(&(
        &body.product,
        &body.predecessor,
        &body.morphology,
        &body.codec_companions,
        &body.runtime_law_sha256,
    ))?;
    if expected != body.complete_sha256 {
        return Err("the cultivated body identity does not reconstruct".into());
    }
    Ok(())
}

fn occurrence_address(
    predecessor: Option<&str>,
    native_ids_sha256: &str,
    text_sha256: &str,
) -> String {
    let mut hasher = Sha256::new();
    frame(
        &mut hasher,
        b"holonic-engine.phoenix.emanative-occurrence.v1",
    );
    frame(&mut hasher, predecessor.unwrap_or("").as_bytes());
    frame(&mut hasher, native_ids_sha256.as_bytes());
    frame(&mut hasher, text_sha256.as_bytes());
    format!("{:x}", hasher.finalize())
}

fn potential_digest(
    vocabulary_extent: usize,
    grain: u32,
    top_lower: i64,
    plural: &[EmanativeCandidate],
    separated: usize,
) -> Result<String, String> {
    digest_json(&(
        "holonic-engine.phoenix.emanative-potential.v1",
        vocabulary_extent,
        grain,
        top_lower,
        plural,
        separated,
    ))
}

fn semantic_receipt_digest(returned: &RuntimeReturn) -> Result<String, String> {
    let receipt = &returned.receipt;
    digest_json(&(
        "holonic-engine.phoenix.emanative-semantic-receipt.v1",
        (
            &receipt.product_identity,
            &receipt.predecessor_identity,
            &receipt.morphology_identity,
            &receipt.codec_companion_identities,
            &receipt.continuation_identity,
            &receipt.runtime_law,
            receipt.frozen_members_verified,
            &receipt.input,
            &receipt.generated,
            &receipt.reconstruction_identity,
            &receipt.codec_identity,
            &receipt.total_work,
            &receipt.overlay_work,
            &receipt.admission,
            &receipt.tower_admission,
            &receipt.overlay_execution,
        ),
    ))
}

fn digest_json(value: &impl Serialize) -> Result<String, String> {
    serde_json::to_vec(value)
        .map(|bytes| sha256(&bytes))
        .map_err(|error| error.to_string())
}

fn digest_native_ids(ids: &[u32]) -> String {
    let mut hasher = Sha256::new();
    frame(&mut hasher, b"holonic-engine.phoenix.native-word.v1");
    hasher.update((ids.len() as u64).to_le_bytes());
    for id in ids {
        hasher.update(id.to_le_bytes());
    }
    format!("{:x}", hasher.finalize())
}

fn frame(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn require_digest(name: &str, digest: &str) -> Result<(), String> {
    if digest.len() != 64 || !digest.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(format!("{name} is not a SHA-256 identity"));
    }
    Ok(())
}
