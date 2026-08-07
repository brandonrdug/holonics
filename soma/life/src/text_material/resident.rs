//! Ownership-coupled CUDA residency, exact admission, bounded restriction, and native rest.

use holonic_structure::LocalSequence;
use serde::Serialize;
use soma_abi::text_restrict_cuda as text_cuda;

use crate::{
    laboratory_language::{
        LaboratoryInformantPort, LaboratoryResearchLeader, LaboratoryWorldContactAttempt,
        LaboratoryWorldContactOutcome, LaboratoryWorldContactRequest, LaboratoryWorldContactReturn,
        LaboratoryWorldReturn,
    },
    text_material_cuda::{
        CudaTextMaterialResidentExecutor, TextMaterialCudaError, TextMaterialCudaLaunchReceipt,
        TextMaterialCudaRestrictionOutput, TextMaterialCudaSyncReceipt,
    },
};

use super::{
    ExactTextMaterialAtlas, ExactTextMaterialCorpus, TextMaterialAtlasReceipt, TextMaterialError,
    TextMaterialSet,
};

#[derive(Clone, Debug)]
pub enum TextMaterialRestrictionError {
    Cuda(TextMaterialCudaError),
    Text(TextMaterialError),
    CarrierExtent,
}

/// Recoverable refusal of the initial host-to-card ownership crossing.
///
/// The exact host predecessor remains inside this value, so unavailable hardware or an ABI
/// refusal cannot destroy the only conditioned text body merely because mounting consumes
/// ownership on success.
#[derive(Debug)]
pub struct TextMaterialCudaMountRefusal {
    atlas: ExactTextMaterialAtlas,
    error: TextMaterialRestrictionError,
}

impl TextMaterialCudaMountRefusal {
    pub const fn atlas(&self) -> &ExactTextMaterialAtlas {
        &self.atlas
    }

    pub const fn error(&self) -> &TextMaterialRestrictionError {
        &self.error
    }

    pub fn into_parts(self) -> (ExactTextMaterialAtlas, TextMaterialRestrictionError) {
        (self.atlas, self.error)
    }
}

impl From<TextMaterialCudaError> for TextMaterialRestrictionError {
    fn from(error: TextMaterialCudaError) -> Self {
        Self::Cuda(error)
    }
}

impl From<TextMaterialError> for TextMaterialRestrictionError {
    fn from(error: TextMaterialError) -> Self {
        Self::Text(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct TextMaterialCudaRestrictionReceipt {
    pub atlas_shape: [u64; 4],
    pub returned_handle_population: usize,
    pub leader_feature_population: usize,
    pub query_transport_population: usize,
    pub host_query_preparation_nanoseconds: u128,
    pub host_return_formation_nanoseconds: u128,
    pub total_elapsed_nanoseconds: u128,
    pub bounded_delta_equal: bool,
    pub resident_sync: Option<TextMaterialCudaSyncReceipt>,
    pub launch: Option<TextMaterialCudaLaunchReceipt>,
}

/// Apparatus testimony for one resident-card contact. The semantic return crosses through the
/// laboratory contact attempt; timing and device realization remain in this separate observer
/// membrane and cannot affect deterministic world-return equality.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct TextMaterialCudaContactReceipt {
    pub contact: String,
    pub restriction: TextMaterialCudaRestrictionReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TextMaterialCudaContactAttempt {
    pub semantic: LaboratoryWorldContactAttempt,
    pub apparatus: LocalSequence<TextMaterialCudaContactReceipt>,
}

/// One ownership-coupled text ecology and its admitted resident CUDA realization.  Mounting
/// consumes the host atlas so an exterior caller cannot silently bind the same card executor to
/// another semantic world.  The host remains exact causal authority; the card is its retained
/// physical chart and may only advance through append deltas derived from this body.
pub struct CudaResidentTextMaterialAtlas {
    host: ExactTextMaterialAtlas,
    card: Option<CudaTextMaterialResidentExecutor>,
    device_ordinal: i32,
    resident_equality_certified: bool,
}

#[derive(Debug)]
pub struct CudaResidentTextMaterialNativeRest {
    host_bytes: Box<[u8]>,
    device_ordinal: i32,
}

#[derive(Debug)]
pub struct CudaResidentTextMaterialRestRefusal {
    pub error: TextMaterialRestrictionError,
    rest: CudaResidentTextMaterialNativeRest,
}

impl CudaResidentTextMaterialRestRefusal {
    pub fn recover(self) -> CudaResidentTextMaterialNativeRest {
        self.rest
    }
}

impl CudaResidentTextMaterialNativeRest {
    /// Found a fresh host owner from native contemporary standing, then transfer it across a new
    /// device mount. No corpus or developmental source is consulted.
    pub fn remount(
        self,
    ) -> Result<CudaResidentTextMaterialAtlas, CudaResidentTextMaterialRestRefusal> {
        let atlas = match ExactTextMaterialAtlas::from_native_bytes(&self.host_bytes) {
            Ok(atlas) => atlas,
            Err(error) => {
                return Err(CudaResidentTextMaterialRestRefusal {
                    error: error.into(),
                    rest: self,
                });
            }
        };
        match atlas.mount_cuda(self.device_ordinal) {
            Ok(resident) => Ok(resident),
            Err(refusal) => {
                let (_atlas, error) = refusal.into_parts();
                Err(CudaResidentTextMaterialRestRefusal { error, rest: self })
            }
        }
    }
}

impl std::fmt::Debug for CudaResidentTextMaterialAtlas {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CudaResidentTextMaterialAtlas")
            .field("receipt", self.host.receipt())
            .field("card", &self.card)
            .field(
                "resident_equality_certified",
                &self.resident_equality_certified,
            )
            .finish()
    }
}

impl ExactTextMaterialAtlas {
    /// Consume this exact text ecology into one ownership-coupled resident CUDA realization.
    pub fn mount_cuda(
        self,
        device_ordinal: i32,
    ) -> Result<CudaResidentTextMaterialAtlas, TextMaterialCudaMountRefusal> {
        let image = match self.resident_image() {
            Ok(image) => image,
            Err(error) => return Err(TextMaterialCudaMountRefusal { atlas: self, error }),
        };
        let card = match CudaTextMaterialResidentExecutor::mount(device_ordinal, image) {
            Ok(card) => card,
            Err(error) => {
                return Err(TextMaterialCudaMountRefusal {
                    atlas: self,
                    error: error.into(),
                });
            }
        };
        Ok(CudaResidentTextMaterialAtlas {
            host: self,
            card: Some(card),
            device_ordinal,
            resident_equality_certified: true,
        })
    }
}

impl CudaResidentTextMaterialAtlas {
    pub const fn corpus(&self) -> &ExactTextMaterialCorpus {
        self.host.corpus()
    }

    pub const fn receipt(&self) -> &TextMaterialAtlasReceipt {
        self.host.receipt()
    }

    pub fn device_name(&self) -> &str {
        match self.card.as_ref() {
            Some(card) => card.device_name(),
            None => "unmounted-cuda-realization",
        }
    }

    pub fn launches(&self) -> u64 {
        match self.card.as_ref() {
            Some(card) => card.launches(),
            None => 0,
        }
    }

    /// Suspend by ownership transfer. Device storage is destroyed; only the exact native host
    /// body and apparatus address survive for a later fresh remount.
    pub fn into_native_rest(
        self,
    ) -> Result<CudaResidentTextMaterialNativeRest, TextMaterialRestrictionError> {
        let host_bytes = self.host.encode_native_bytes()?.into_boxed_slice();
        let Self {
            host: _,
            card,
            device_ordinal,
            resident_equality_certified: _,
        } = self;
        drop(card);
        Ok(CudaResidentTextMaterialNativeRest {
            host_bytes,
            device_ordinal,
        })
    }

    /// Grade the continuing host authority through its native rest membrane without detaching
    /// or replacing the resident card realization. This is an observation of the current body;
    /// the remounted image never becomes the authority merely because it compares equal.
    pub fn grade_host_rest(&self) -> Result<bool, TextMaterialRestrictionError> {
        let bytes = self.host.encode_native_bytes()?;
        Ok(ExactTextMaterialAtlas::from_native_bytes(&bytes)? == self.host)
    }

    /// Restrict the continuing ecology through its resident card chart.  A poisoned realization
    /// is discarded before recovery; no question may traverse a partially updated card body.
    pub fn enact(
        &mut self,
        leader: &LaboratoryResearchLeader,
    ) -> Result<
        (LaboratoryWorldReturn, TextMaterialCudaRestrictionReceipt),
        TextMaterialRestrictionError,
    > {
        let total_started = std::time::Instant::now();
        self.synchronize_card()?;
        let atlas_shape = self.atlas_shape()?;
        let query_started = std::time::Instant::now();
        let (leader_features, query_transports) = self.host.restriction_coordinates(leader);
        let feature_mask_words = text_cuda::mask_words(leader_features.len());
        let transport_mask_words = text_cuda::mask_words(query_transports.len());
        let aperture = leader.aperture.max(1).min(self.host.sections.len());
        if leader_features.is_empty() || aperture == 0 {
            let resident_sync = self
                .card
                .as_mut()
                .ok_or(TextMaterialRestrictionError::CarrierExtent)?
                .take_pending_sync();
            return Ok((
                LaboratoryWorldReturn {
                    leader: leader.identity.to_owned(),
                    sections: Default::default(),
                    complete_population: 0,
                    omitted_population: 0,
                },
                TextMaterialCudaRestrictionReceipt {
                    atlas_shape,
                    returned_handle_population: 0,
                    leader_feature_population: leader_features.len(),
                    query_transport_population: query_transports.len(),
                    host_query_preparation_nanoseconds: query_started.elapsed().as_nanos(),
                    host_return_formation_nanoseconds: 0,
                    total_elapsed_nanoseconds: total_started.elapsed().as_nanos(),
                    bounded_delta_equal: self.resident_equality_certified,
                    resident_sync,
                    launch: None,
                },
            ));
        }
        let transport_words = query_transports
            .len()
            .checked_mul(text_cuda::TRANSPORT_WORDS)
            .ok_or(TextMaterialRestrictionError::CarrierExtent)?;
        let query_words = text_cuda::HEADER_WORDS
            .checked_add(leader_features.len())
            .and_then(|words| words.checked_add(transport_words))
            .and_then(|words| words.checked_add(leader_features.len()))
            .ok_or(TextMaterialRestrictionError::CarrierExtent)?;
        let mut query = LocalSequence::with_capacity(query_words);
        query.resize_with(text_cuda::HEADER_WORDS, || 0);
        let leader_features_at = query.len();
        query.extend_from_slice(&leader_features);
        let query_transports_at = query.len();
        for (source, target) in &query_transports {
            query.extend_from_slice(&[*source, *target]);
        }
        let feature_cursors_at = query.len();
        query.resize_with(query_words, || text_cuda::OPEN_LINK);
        query[text_cuda::VERSION] = text_cuda::LAYOUT_VERSION;
        query[text_cuda::EPOCH] = 0;
        query[text_cuda::APERTURE] = extent_u32(aperture)?;
        query[text_cuda::LEADER_FEATURES] = extent_u32(leader_features.len())?;
        query[text_cuda::QUERY_TRANSPORTS] = extent_u32(query_transports.len())?;
        query[text_cuda::FEATURE_MASK_WORDS] = extent_u32(feature_mask_words)?;
        query[text_cuda::TRANSPORT_MASK_WORDS] = extent_u32(transport_mask_words)?;
        query[text_cuda::LEADER_FEATURES_AT] = extent_u32(leader_features_at)?;
        query[text_cuda::QUERY_TRANSPORTS_AT] = extent_u32(query_transports_at)?;
        query[text_cuda::FEATURE_CURSORS_AT] = extent_u32(feature_cursors_at)?;
        query[text_cuda::TOTAL_WORDS] = extent_u32(query.len())?;
        let host_query_preparation_nanoseconds = query_started.elapsed().as_nanos();
        let TextMaterialCudaRestrictionOutput {
            restriction_words,
            returned_handles,
            launch,
        } = self
            .card
            .as_mut()
            .ok_or(TextMaterialRestrictionError::CarrierExtent)?
            .restrict(&mut query)?;

        let return_started = std::time::Instant::now();
        let returned = self.host.finish_restriction(
            leader,
            &leader_features,
            feature_mask_words,
            transport_mask_words,
            &restriction_words,
        );
        let host_return_formation_nanoseconds = return_started.elapsed().as_nanos();
        let resident_sync = self
            .card
            .as_mut()
            .ok_or(TextMaterialRestrictionError::CarrierExtent)?
            .take_pending_sync();
        Ok((
            returned,
            TextMaterialCudaRestrictionReceipt {
                atlas_shape,
                returned_handle_population: returned_handles,
                leader_feature_population: leader_features.len(),
                query_transport_population: query_transports.len(),
                host_query_preparation_nanoseconds,
                host_return_formation_nanoseconds,
                total_elapsed_nanoseconds: total_started.elapsed().as_nanos(),
                bounded_delta_equal: self.resident_equality_certified,
                resident_sync,
                launch: Some(launch),
            },
        ))
    }

    /// Enact exactly the resident-card members exposed by one research-owned unresolved front.
    /// Each semantic success or obstruction remains bound to its original contact identity;
    /// CUDA telemetry is returned beside, never inside, that caused semantic population.
    pub fn enact_contact_front(
        &mut self,
        requests: &[LaboratoryWorldContactRequest],
    ) -> TextMaterialCudaContactAttempt {
        let mut outcomes = LocalSequence::with_capacity(requests.len());
        let mut apparatus = LocalSequence::with_capacity(requests.len());
        for request in requests {
            if request.port != LaboratoryInformantPort::ResidentTextCard {
                outcomes.push(LaboratoryWorldContactOutcome::Obstructed {
                    identity: request.identity.to_owned(),
                    obstruction: format!("resident text card cannot enact {:?}", request.port),
                });
                continue;
            }
            match self.enact(&request.leader) {
                Ok((returned, restriction)) => {
                    apparatus.push(TextMaterialCudaContactReceipt {
                        contact: request.identity.to_owned(),
                        restriction,
                    });
                    outcomes.push(LaboratoryWorldContactOutcome::Returned(
                        LaboratoryWorldContactReturn {
                            identity: request.identity.to_owned(),
                            leader: request.leader.identity.to_owned(),
                            port: request.port,
                            returned,
                        },
                    ));
                }
                Err(error) => outcomes.push(LaboratoryWorldContactOutcome::Obstructed {
                    identity: request.identity.to_owned(),
                    obstruction: format!("{error:?}"),
                }),
            }
        }
        TextMaterialCudaContactAttempt {
            semantic: LaboratoryWorldContactAttempt {
                outcomes,
                execution: None,
            },
            apparatus,
        }
    }

    pub fn receive_emanated(
        &mut self,
        identity: impl Into<String>,
        text: impl Into<String>,
    ) -> Result<(), TextMaterialRestrictionError> {
        self.receive_emanated_caused(identity, text, Default::default())
    }

    /// Return one generated deed to the same ecology, then carry only its appended morphology to
    /// the resident chart.  If physical synchronization fails the host deed remains caused and
    /// the card is barred until a clean remount from that authority succeeds.
    pub fn receive_emanated_caused(
        &mut self,
        identity: impl Into<String>,
        text: impl Into<String>,
        caused_by: TextMaterialSet<String>,
    ) -> Result<(), TextMaterialRestrictionError> {
        let before = self.atlas_shape()?;
        self.host
            .receive_emanated_caused(identity, text, caused_by)?;
        let after = self.atlas_shape()?;
        if before != after {
            self.synchronize_card()?;
        }
        Ok(())
    }

    fn atlas_shape(&self) -> Result<[u64; 4], TextMaterialRestrictionError> {
        Ok([
            extent_u64(self.host.corpus.occurrences.len())?,
            extent_u64(self.host.sections.len())?,
            extent_u64(self.host.feature_catalogue.len())?,
            extent_u64(self.host.token_catalogue.len())?,
        ])
    }

    fn synchronize_card(&mut self) -> Result<(), TextMaterialRestrictionError> {
        let needs_remount = match self.card.as_ref() {
            Some(card) => card.is_poisoned(),
            None => true,
        };
        if needs_remount {
            let stale = self.card.take();
            drop(stale);
            let image = self.host.resident_image()?;
            self.card = Some(CudaTextMaterialResidentExecutor::mount(
                self.device_ordinal,
                image,
            )?);
            self.resident_equality_certified = true;
            return Ok(());
        }

        let synchronized = {
            let card = self
                .card
                .as_ref()
                .ok_or(TextMaterialRestrictionError::CarrierExtent)?;
            let shape = card.active_shape();
            shape.occurrences == self.host.corpus.occurrences.len()
                && shape.sections == self.host.sections.len()
                && shape.features == self.host.feature_catalogue.len()
                && shape.tokens == self.host.token_catalogue.len()
        };
        if synchronized {
            return Ok(());
        }
        let card = self
            .card
            .as_mut()
            .ok_or(TextMaterialRestrictionError::CarrierExtent)?;
        if card.device_ordinal() != self.device_ordinal {
            return Err(TextMaterialRestrictionError::CarrierExtent);
        }
        let delta = self
            .host
            .resident_delta(card.active_shape(), card.head_shadow())?;
        card.synchronize(delta)?;
        self.resident_equality_certified = true;
        Ok(())
    }
}
pub(super) fn extent_u32(value: usize) -> Result<u32, TextMaterialRestrictionError> {
    u32::try_from(value).map_err(|_| TextMaterialRestrictionError::CarrierExtent)
}

pub(super) fn extent_u64(value: usize) -> Result<u64, TextMaterialRestrictionError> {
    u64::try_from(value).map_err(|_| TextMaterialRestrictionError::CarrierExtent)
}
