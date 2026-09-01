use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::native_spool::{
    NativeAddressedSection, NativeCollapsedFibre, NativeShortestSeparator,
    NativeSpoolConductReturn, NativeSpoolRefusal, NativeTransportScaffold,
};
use crate::receiver_exact_compression::{InputId, Observation, ReceiverId};
use crate::receiver_history_compression::NativeStateId;
use crate::{EventId, OccurrencePort};

use super::{InferenceCirculation, OpenObligation, OpenScope};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct NativeInferenceAddress {
    pub spool: String,
    pub thread: String,
    pub occurrence: EventId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeInferenceRequest {
    pub address: NativeInferenceAddress,
    pub receiver: ReceiverId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeFutureFace {
    pub from: NativeStateId,
    pub to: NativeStateId,
    pub observation: Observation,
}

/// The complete plural future section with one addressed emission face selected by actual ingress.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeEmissionSection {
    pub entering_occurrence: EventId,
    pub receiver: ReceiverId,
    pub ordered_word: Vec<InputId>,
    pub plural_futures: Vec<NativeFutureFace>,
    pub emitted_future: usize,
}

impl NativeEmissionSection {
    pub fn emitted(&self) -> Option<NativeFutureFace> {
        self.plural_futures.get(self.emitted_future).copied()
    }

    pub fn validate(&self) -> Result<(), NativeInferenceError> {
        let starts = self
            .plural_futures
            .iter()
            .map(|future| future.from)
            .collect::<BTreeSet<_>>();
        if self.ordered_word.is_empty()
            || self.plural_futures.is_empty()
            || self.emitted().is_none()
            || starts.len() != self.plural_futures.len()
        {
            return Err(NativeInferenceError::MalformedEmission);
        }
        Ok(())
    }
}

/// Structural emission address. No digest or codec surface participates in it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeEmissionAddress {
    pub entering_occurrence: EventId,
    pub receiver: ReceiverId,
    pub ordered_word: Vec<InputId>,
    pub emitted: NativeFutureFace,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeInferenceLineage {
    pub entering_occurrence: EventId,
    pub predecessor: Option<EventId>,
    pub entering_port: OccurrencePort,
    pub emitting_port: OccurrencePort,
    pub ordered_word: Vec<InputId>,
    pub native_start: Vec<NativeStateId>,
    pub native_end: Vec<NativeStateId>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct NativeFutureReconstruction<'a> {
    pub fibres: Vec<&'a NativeCollapsedFibre>,
    pub shortest_separators: &'a [NativeShortestSeparator],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExteriorReturnAperture {
    pub emitted: NativeEmissionAddress,
    pub reconstruction_fibre_population: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExteriorReturnOccurrence<Returned> {
    pub emitted: NativeEmissionAddress,
    pub returned: Returned,
    pub reconstruction_fibre_population: usize,
}

impl ExteriorReturnAperture {
    /// Admit a genuinely exterior value beside its emission. HIF4 supplies later chronology and
    /// the morphology-changing returned difference; this function performs neither operation.
    pub fn admit<Returned>(self, returned: Returned) -> ExteriorReturnOccurrence<Returned> {
        ExteriorReturnOccurrence {
            emitted: self.emitted,
            returned,
            reconstruction_fibre_population: self.reconstruction_fibre_population,
        }
    }
}

/// One borrowed-rest inference circulation with one terminal resident return.
#[derive(Debug)]
pub struct NativeInferenceCirculation<'a> {
    morphology: &'a NativeTransportScaffold,
    entering: NativeAddressedSection<'a>,
    conducted: NativeSpoolConductReturn,
    face: NativeEmissionSection,
    emitted: NativeEmissionAddress,
    lineage: NativeInferenceLineage,
    reconstruction: NativeFutureReconstruction<'a>,
    return_aperture: ExteriorReturnAperture,
    successor_requests: Vec<NativeInferenceRequest>,
    open_obligations: Vec<OpenObligation<'a>>,
}

impl NativeInferenceCirculation<'_> {
    pub fn return_aperture(&self) -> &ExteriorReturnAperture {
        &self.return_aperture
    }

    /// Every actually caused later occurrence; no collection member is selected as native policy.
    pub fn successor_requests(&self) -> &[NativeInferenceRequest] {
        &self.successor_requests
    }
}

impl<'a> InferenceCirculation for NativeInferenceCirculation<'a> {
    type Morphology = NativeTransportScaffold;
    type EnteringOccurrence = crate::native_spool::NativeThreadOccurrence;
    type ActiveSection = NativeAddressedSection<'a>;
    type ConductedSection = NativeSpoolConductReturn;
    type Receiver = ReceiverId;
    type Face = NativeEmissionSection;
    type EmittedOccurrence = NativeEmissionAddress;
    type Lineage = NativeInferenceLineage;
    type Reconstruction = NativeFutureReconstruction<'a>;
    type OpenObligation = OpenObligation<'a>;

    fn predecessor_morphology(&self) -> &Self::Morphology {
        self.morphology
    }

    fn entering_occurrence(&self) -> &Self::EnteringOccurrence {
        self.entering.occurrence()
    }

    fn active_section(&self) -> &Self::ActiveSection {
        &self.entering
    }

    fn conducted_section(&self) -> &Self::ConductedSection {
        &self.conducted
    }

    fn receiver(&self) -> &Self::Receiver {
        &self.face.receiver
    }

    fn face(&self) -> &Self::Face {
        &self.face
    }

    fn emitted_occurrence(&self) -> &Self::EmittedOccurrence {
        &self.emitted
    }

    fn lineage(&self) -> &Self::Lineage {
        &self.lineage
    }

    fn reconstruction(&self) -> &Self::Reconstruction {
        &self.reconstruction
    }

    fn successor_morphology(&self) -> &Self::Morphology {
        self.morphology
    }

    fn open_obligations(&self) -> &[Self::OpenObligation] {
        &self.open_obligations
    }
}

pub fn conduct_native_inference(
    morphology: &NativeTransportScaffold,
    request: NativeInferenceRequest,
) -> Result<NativeInferenceCirculation<'_>, NativeInferenceError> {
    morphology.validate()?;
    let entering = morphology.addressed_section(
        &request.address.spool,
        &request.address.thread,
        request.address.occurrence,
    )?;
    if !entering.spool().receiver_family.contains(&request.receiver) {
        return Err(NativeInferenceError::ReceiverOutsideFamily(
            request.receiver,
        ));
    }
    let ordered_word = entering.ordered_generator_word().to_vec();
    let native_start = entering
        .spool()
        .native_population
        .iter()
        .copied()
        .filter(|native| {
            ordered_word.iter().all(|generator| {
                entering
                    .spool()
                    .generator_descents
                    .iter()
                    .find(|descent| descent.generator == *generator)
                    .is_some_and(|descent| !descent.open_domain.contains(native))
            })
        })
        .collect::<Vec<_>>();
    if native_start.is_empty() || !native_start.contains(&entering.occurrence().entering_native) {
        return Err(NativeInferenceError::EnteringOccurrenceOutsideActiveDomain);
    }
    let mut resident = morphology.mount_word(&request.address.spool, &ordered_word)?;
    let conducted = resident.conduct(&native_start, request.receiver)?;
    if conducted.native_start != native_start
        || conducted.native_end.len() != native_start.len()
        || conducted.observations.len() != native_start.len()
        || conducted.apparatus.invariant_transport_reuploaded
    {
        return Err(NativeInferenceError::MalformedConduct);
    }
    let plural_futures = native_start
        .iter()
        .zip(&conducted.native_end)
        .zip(&conducted.observations)
        .map(|((from, to), observation)| NativeFutureFace {
            from: *from,
            to: *to,
            observation: *observation,
        })
        .collect::<Vec<_>>();
    let emitted_future = plural_futures
        .iter()
        .position(|future| future.from == entering.occurrence().entering_native)
        .ok_or(NativeInferenceError::MalformedEmission)?;
    let face = NativeEmissionSection {
        entering_occurrence: request.address.occurrence,
        receiver: request.receiver,
        ordered_word: ordered_word.clone(),
        plural_futures,
        emitted_future,
    };
    face.validate()?;
    let emitted = NativeEmissionAddress {
        entering_occurrence: request.address.occurrence,
        receiver: request.receiver,
        ordered_word: ordered_word.clone(),
        emitted: face
            .emitted()
            .ok_or(NativeInferenceError::MalformedEmission)?,
    };
    let mut fibres = Vec::new();
    for future in &face.plural_futures {
        let before = fibres.len();
        fibres.extend(
            entering
                .spool()
                .reconstruction_fibres
                .iter()
                .filter(|fibre| fibre.native == future.to),
        );
        if fibres.len() == before {
            return Err(NativeInferenceError::MissingReconstructionFibre(future.to));
        }
    }
    let lineage = NativeInferenceLineage {
        entering_occurrence: request.address.occurrence,
        predecessor: entering.occurrence().predecessor,
        entering_port: entering.occurrence().entering_port,
        emitting_port: entering.occurrence().emitting_port,
        ordered_word,
        native_start: conducted.native_start.clone(),
        native_end: conducted.native_end.clone(),
    };
    let reconstruction = NativeFutureReconstruction {
        fibres,
        shortest_separators: &entering.spool().shortest_separators,
    };
    let return_aperture = ExteriorReturnAperture {
        emitted: emitted.clone(),
        reconstruction_fibre_population: reconstruction.fibres.len(),
    };
    // A bare `EventId` predecessor is meaningful only inside its owning spool. Cross-spool
    // continuation additionally owes a declared scaffold composition, so equal event numbers in
    // two winding families can never manufacture a successor here.
    let successor_requests = morphology
        .spools
        .iter()
        .find(|spool| spool.address == request.address.spool)
        .into_iter()
        .flat_map(|spool| {
            spool.threads.iter().flat_map(|thread| {
                thread.occurrences.iter().filter_map(|occurrence| {
                    (occurrence.predecessor == Some(request.address.occurrence)).then(|| {
                        NativeInferenceRequest {
                            address: NativeInferenceAddress {
                                spool: spool.address.clone(),
                                thread: thread.address.clone(),
                                occurrence: occurrence.occurrence,
                            },
                            receiver: request.receiver,
                        }
                    })
                })
            })
        })
        .collect::<Vec<_>>();
    let mut open_obligations = entering
        .thread()
        .open_exterior
        .iter()
        .map(|testimony| OpenObligation {
            scope: OpenScope::Thread,
            testimony,
        })
        .collect::<Vec<_>>();
    open_obligations.extend(entering.spool().open_exterior.iter().map(|testimony| {
        OpenObligation {
            scope: OpenScope::Spool,
            testimony,
        }
    }));
    open_obligations.extend(
        morphology
            .open_exterior
            .iter()
            .map(|testimony| OpenObligation {
                scope: OpenScope::Scaffold,
                testimony,
            }),
    );
    Ok(NativeInferenceCirculation {
        morphology,
        entering,
        conducted,
        face,
        emitted,
        lineage,
        reconstruction,
        return_aperture,
        successor_requests,
        open_obligations,
    })
}

pub trait ExteriorEmissionCodec {
    type Surface;
    type Error;

    fn render(&self, emission: &NativeEmissionSection) -> Result<Self::Surface, Self::Error>;
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Utf8InspectionCodec;

impl ExteriorEmissionCodec for Utf8InspectionCodec {
    type Surface = String;
    type Error = NativeInferenceError;

    fn render(&self, emission: &NativeEmissionSection) -> Result<Self::Surface, Self::Error> {
        emission.validate()?;
        serde_json::to_string(emission)
            .map_err(|error| NativeInferenceError::Codec(error.to_string()))
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct BinaryEmissionCodec;

impl ExteriorEmissionCodec for BinaryEmissionCodec {
    type Surface = Vec<u8>;
    type Error = NativeInferenceError;

    fn render(&self, emission: &NativeEmissionSection) -> Result<Self::Surface, Self::Error> {
        emission.validate()?;
        let count = u64::try_from(emission.plural_futures.len())
            .map_err(|_| NativeInferenceError::Codec("future population overflow".to_owned()))?;
        let word = u64::try_from(emission.ordered_word.len())
            .map_err(|_| NativeInferenceError::Codec("word population overflow".to_owned()))?;
        let selected = u64::try_from(emission.emitted_future)
            .map_err(|_| NativeInferenceError::Codec("selected address overflow".to_owned()))?;
        let mut bytes = Vec::with_capacity(
            45 + emission.ordered_word.len() * 8 + emission.plural_futures.len() * 24,
        );
        bytes.extend_from_slice(b"HIFE1");
        push_u64(&mut bytes, emission.entering_occurrence.0);
        push_u64(&mut bytes, emission.receiver.0);
        push_u64(&mut bytes, word);
        for generator in &emission.ordered_word {
            push_u64(&mut bytes, generator.0);
        }
        push_u64(&mut bytes, count);
        push_u64(&mut bytes, selected);
        for future in &emission.plural_futures {
            push_u64(&mut bytes, future.from.0);
            push_u64(&mut bytes, future.to.0);
            push_u64(&mut bytes, future.observation.0);
        }
        Ok(bytes)
    }
}

impl BinaryEmissionCodec {
    pub fn read(bytes: &[u8]) -> Result<NativeEmissionSection, NativeInferenceError> {
        if bytes.get(..5) != Some(b"HIFE1") {
            return Err(NativeInferenceError::Codec(
                "unknown binary emission schema".to_owned(),
            ));
        }
        let mut at = 5usize;
        let entering_occurrence = EventId(take_u64(bytes, &mut at)?);
        let receiver = ReceiverId(take_u64(bytes, &mut at)?);
        let word = usize::try_from(take_u64(bytes, &mut at)?)
            .map_err(|_| NativeInferenceError::Codec("word extent overflow".to_owned()))?;
        let mut ordered_word = Vec::with_capacity(word);
        for _ in 0..word {
            ordered_word.push(InputId(take_u64(bytes, &mut at)?));
        }
        let count = usize::try_from(take_u64(bytes, &mut at)?)
            .map_err(|_| NativeInferenceError::Codec("future extent overflow".to_owned()))?;
        let emitted_future = usize::try_from(take_u64(bytes, &mut at)?)
            .map_err(|_| NativeInferenceError::Codec("selected address overflow".to_owned()))?;
        let mut plural_futures = Vec::with_capacity(count);
        for _ in 0..count {
            plural_futures.push(NativeFutureFace {
                from: NativeStateId(take_u64(bytes, &mut at)?),
                to: NativeStateId(take_u64(bytes, &mut at)?),
                observation: Observation(take_u64(bytes, &mut at)?),
            });
        }
        if at != bytes.len() {
            return Err(NativeInferenceError::Codec(
                "trailing binary emission octets".to_owned(),
            ));
        }
        let emission = NativeEmissionSection {
            entering_occurrence,
            receiver,
            ordered_word,
            plural_futures,
            emitted_future,
        };
        emission.validate()?;
        Ok(emission)
    }
}

#[derive(Debug, Error, PartialEq, Eq)]
pub enum NativeInferenceError {
    #[error("native ecology refused inference: {0}")]
    Native(#[from] NativeSpoolRefusal),
    #[error("receiver {0:?} lies outside the addressed native family")]
    ReceiverOutsideFamily(ReceiverId),
    #[error("resident conduct did not return the complete mounted future population")]
    MalformedConduct,
    #[error("the plural emission section is malformed")]
    MalformedEmission,
    #[error("future state {0:?} has no complete reconstruction fibre")]
    MissingReconstructionFibre(NativeStateId),
    #[error("the entering occurrence lies outside the active generator domain")]
    EnteringOccurrenceOutsideActiveDomain,
    #[error("exterior emission codec refused: {0}")]
    Codec(String),
}

fn push_u64(bytes: &mut Vec<u8>, value: u64) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

fn take_u64(bytes: &[u8], at: &mut usize) -> Result<u64, NativeInferenceError> {
    let end = at
        .checked_add(8)
        .ok_or_else(|| NativeInferenceError::Codec("binary address overflow".to_owned()))?;
    let word = bytes
        .get(*at..end)
        .ok_or_else(|| NativeInferenceError::Codec("truncated binary emission".to_owned()))?;
    *at = end;
    Ok(u64::from_le_bytes(word.try_into().expect("eight octets")))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> NativeEmissionSection {
        NativeEmissionSection {
            entering_occurrence: EventId(7),
            receiver: ReceiverId(11),
            ordered_word: vec![InputId(3), InputId(5)],
            plural_futures: vec![
                NativeFutureFace {
                    from: NativeStateId(0),
                    to: NativeStateId(2),
                    observation: Observation(13),
                },
                NativeFutureFace {
                    from: NativeStateId(1),
                    to: NativeStateId(4),
                    observation: Observation(17),
                },
            ],
            emitted_future: 1,
        }
    }

    #[test]
    fn text_and_binary_codecs_render_one_unchanged_complete_emission() {
        let emission = fixture();
        let text = Utf8InspectionCodec.render(&emission).expect("text");
        let binary = BinaryEmissionCodec.render(&emission).expect("binary");
        assert!(text.contains("plural_futures"));
        assert_eq!(BinaryEmissionCodec::read(&binary).expect("read"), emission);
    }

    #[test]
    fn binary_codec_refuses_truncation_trailing_octets_and_repeated_starting_states() {
        let emission = fixture();
        let mut binary = BinaryEmissionCodec.render(&emission).expect("binary");
        assert!(BinaryEmissionCodec::read(&binary[..binary.len() - 1]).is_err());
        binary.push(0);
        assert!(BinaryEmissionCodec::read(&binary).is_err());
        let mut duplicate = emission;
        duplicate.plural_futures[1].from = duplicate.plural_futures[0].from;
        assert_eq!(
            duplicate.validate(),
            Err(NativeInferenceError::MalformedEmission)
        );
    }
}
