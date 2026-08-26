//! Canonical source-detached standing for the receiver-history cultivated Phoenix transition.
//!
//! This owner composes three already-founded objects: the authenticated Phoenix body, the exact
//! receiver/history quotient, and the rested factor complex. It stores no inherited tensor twice
//! and no source exchange material. Remount consumes the standing into one [`ProductSession`]; the
//! exterior product and continuation directories are apparatus organs authenticated by the body
//! identity, not semantic lookup tables.

use std::path::Path;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::receiver_history_compression::ReceiverHistoryCompression;

use super::{
    continuation::{ContinuationRuntimeIdentity, CultivatedBodyIdentity},
    runtime::ProductSession,
    session_factor_complex::{SessionFactorComplexIdentity, SessionFactorComplexRest},
};

pub const PHOENIX_TRANSITION_REST_SCHEMA: &str = "holonic-engine.phoenix.transition-rest.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PhoenixTransitionDecoderReceipt {
    pub codec_identity_sha256: String,
    pub native_codebook_sha256: String,
    pub source_extent: u32,
    pub native_extent: u32,
    pub unresolved_source_ids: Vec<u32>,
}

/// One rested product. Deliberately not `Clone`: branches remount the immutable wire and own only
/// their later local continuation differences.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PhoenixTransitionRest {
    pub schema: String,
    pub body: CultivatedBodyIdentity,
    pub cultivation_continuation: Option<ContinuationRuntimeIdentity>,
    pub receiver_history: ReceiverHistoryCompression,
    pub factor_complex: SessionFactorComplexRest,
    pub decoder: PhoenixTransitionDecoderReceipt,
    pub product_identity_sha256: String,
    pub open_exterior: Vec<String>,
}

/// The source-detached rest consumed into one non-cloned productive owner.
pub struct MountedPhoenixTransition {
    session: ProductSession,
    receiver_history: ReceiverHistoryCompression,
    product_identity_sha256: String,
}

impl PhoenixTransitionRest {
    pub fn seal(
        session: &ProductSession,
        receiver_history: ReceiverHistoryCompression,
        open_exterior: Vec<String>,
    ) -> Result<Self, PhoenixTransitionRestRefusal> {
        receiver_history
            .validate()
            .map_err(|error| PhoenixTransitionRestRefusal::ReceiverHistory(error.to_string()))?;
        let body = session
            .body_identity()
            .map_err(PhoenixTransitionRestRefusal::Product)?;
        let cultivation_continuation = session
            .continuation_identity()
            .map_err(PhoenixTransitionRestRefusal::Product)?;
        let factor_complex = session
            .factor_complex_rest()
            .map_err(PhoenixTransitionRestRefusal::Product)?;
        let decoder = PhoenixTransitionDecoderReceipt {
            codec_identity_sha256: session.source_codec_identity().to_owned(),
            native_codebook_sha256: session.codebook_digest().to_owned(),
            source_extent: session.source_extent(),
            native_extent: session.native_extent(),
            unresolved_source_ids: session.unresolved_source_ids(),
        };
        let product_identity_sha256 = product_identity(
            &body,
            cultivation_continuation.as_ref(),
            &receiver_history,
            factor_complex.identity(),
            &decoder,
        )?;
        let rest = Self {
            schema: PHOENIX_TRANSITION_REST_SCHEMA.to_owned(),
            body,
            cultivation_continuation,
            receiver_history,
            factor_complex,
            decoder,
            product_identity_sha256,
            open_exterior,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, PhoenixTransitionRestRefusal> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| PhoenixTransitionRestRefusal::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, PhoenixTransitionRestRefusal> {
        self.validate()?;
        serde_json::to_vec(self)
            .map_err(|error| PhoenixTransitionRestRefusal::Wire(error.to_string()))
    }

    pub fn validate(&self) -> Result<(), PhoenixTransitionRestRefusal> {
        if self.schema != PHOENIX_TRANSITION_REST_SCHEMA
            || self.open_exterior.is_empty()
            || self.decoder.source_extent == 0
            || self.decoder.native_extent == 0
            || self.decoder.codec_identity_sha256.len() != 64
            || self.decoder.native_codebook_sha256.len() != 64
        {
            return Err(PhoenixTransitionRestRefusal::Identity);
        }
        self.receiver_history
            .validate()
            .map_err(|error| PhoenixTransitionRestRefusal::ReceiverHistory(error.to_string()))?;
        let expected = product_identity(
            &self.body,
            self.cultivation_continuation.as_ref(),
            &self.receiver_history,
            self.factor_complex.identity(),
            &self.decoder,
        )?;
        if expected != self.product_identity_sha256 {
            return Err(PhoenixTransitionRestRefusal::Identity);
        }
        Ok(())
    }

    pub fn mount(
        self,
        product_directory: impl AsRef<Path>,
        continuation_directory: impl AsRef<Path>,
    ) -> Result<MountedPhoenixTransition, PhoenixTransitionRestRefusal> {
        self.validate()?;
        let expected_factor_identity = self.factor_complex.identity().clone();
        let mut session =
            ProductSession::open_with_continuation(product_directory, continuation_directory)
                .map_err(PhoenixTransitionRestRefusal::Product)?;
        if session
            .body_identity()
            .map_err(PhoenixTransitionRestRefusal::Product)?
            != self.body
            || session
                .continuation_identity()
                .map_err(PhoenixTransitionRestRefusal::Product)?
                != self.cultivation_continuation
            || session.source_codec_identity() != self.decoder.codec_identity_sha256
            || session.codebook_digest() != self.decoder.native_codebook_sha256
            || session.source_extent() != self.decoder.source_extent
            || session.native_extent() != self.decoder.native_extent
            || session.unresolved_source_ids() != self.decoder.unresolved_source_ids
        {
            return Err(PhoenixTransitionRestRefusal::Identity);
        }
        session
            .mount_factor_complex_standing(self.factor_complex)
            .map_err(PhoenixTransitionRestRefusal::Product)?;
        if session
            .factor_complex_identity()
            .map_err(PhoenixTransitionRestRefusal::Product)?
            .as_ref()
            != Some(&expected_factor_identity)
        {
            return Err(PhoenixTransitionRestRefusal::Identity);
        }
        Ok(MountedPhoenixTransition {
            session,
            receiver_history: self.receiver_history,
            product_identity_sha256: self.product_identity_sha256,
        })
    }
}

impl MountedPhoenixTransition {
    pub fn product_identity(&self) -> &str {
        &self.product_identity_sha256
    }

    pub fn receiver_history(&self) -> &ReceiverHistoryCompression {
        &self.receiver_history
    }

    pub fn into_session(self) -> ProductSession {
        self.session
    }
}

fn product_identity(
    body: &CultivatedBodyIdentity,
    continuation: Option<&ContinuationRuntimeIdentity>,
    receiver_history: &ReceiverHistoryCompression,
    factor: &SessionFactorComplexIdentity,
    decoder: &PhoenixTransitionDecoderReceipt,
) -> Result<String, PhoenixTransitionRestRefusal> {
    let bytes = serde_json::to_vec(&(
        PHOENIX_TRANSITION_REST_SCHEMA,
        body,
        continuation,
        receiver_history,
        factor,
        decoder,
    ))
    .map_err(|error| PhoenixTransitionRestRefusal::Wire(error.to_string()))?;
    Ok(format!("{:x}", Sha256::digest(bytes)))
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum PhoenixTransitionRestRefusal {
    #[error("the Phoenix-transition rest wire refused: {0}")]
    Wire(String),
    #[error("the receiver-history rest refused: {0}")]
    ReceiverHistory(String),
    #[error("the mounted Phoenix product refused: {0}")]
    Product(String),
    #[error("the Phoenix-transition rest identity does not reconstruct")]
    Identity,
}
