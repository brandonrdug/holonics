//! Modality-neutral world faces and constituted scaffold returns.
//!
//! An application may report only what happened to an issued emission grain. The continuing
//! circulation owner validates the complete face family and derives current, storage, and local
//! native support. Diagnostics are retained testimony and never route the return.

use std::collections::BTreeSet;

use holonic_engine::{
    native_ecology::holonic_intelligence::NativeEmissionAddress,
    receiver_history_compression::NativeStateId, EventId, ExactComplexWaveCurrent,
};
use holonic_structure::CountedCrossing;
use num_bigint::{BigInt, BigUint};
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};

use super::{
    NativeCirculationBoundary, NativeCirculationSession, NativeCultivationCandidate,
    NativeSessionError, NATIVE_CULTIVATION_CANDIDATE_SCHEMA,
};
use super::scaffold_cultivation::ReturnedScaffoldInteraction;

pub const NATIVE_WORLD_FACE_SCHEMA: &str = "soma-life.native-world-face.v2";

/// One member of the complete face family issued by a conducted boundary.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeIssuedWorldFace {
    schema: String,
    generation: u64,
    emission: NativeEmissionAddress,
    grain: usize,
    support: BTreeSet<EventId>,
}

impl NativeIssuedWorldFace {
    pub fn generation(&self) -> u64 {
        self.generation
    }

    pub fn emission(&self) -> &NativeEmissionAddress {
        &self.emission
    }

    pub fn grain(&self) -> usize {
        self.grain
    }

    pub fn support(&self) -> &BTreeSet<EventId> {
        &self.support
    }
}

/// An exterior world's report about exactly one issued emission grain.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeWorldFace {
    issued: NativeIssuedWorldFace,
    admitted: bool,
    carried: BTreeSet<EventId>,
    diagnostic: Vec<u8>,
}

impl NativeWorldFace {
    /// Report one world face. This cannot mint support: every carried occurrence must belong to
    /// the issued grain. The session later revalidates the issued member against its own boundary.
    pub fn report(
        issued: NativeIssuedWorldFace,
        admitted: bool,
        carried: BTreeSet<EventId>,
        diagnostic: Vec<u8>,
    ) -> Result<Self, NativeSessionError> {
        if issued.schema != NATIVE_WORLD_FACE_SCHEMA
            || issued.support.is_empty()
            || carried.is_empty()
            || !carried.is_subset(&issued.support)
        {
            return Err(NativeSessionError::WorldFace);
        }
        Ok(Self {
            issued,
            admitted,
            carried,
            diagnostic,
        })
    }

    pub fn issued(&self) -> &NativeIssuedWorldFace {
        &self.issued
    }

    pub fn admitted(&self) -> bool {
        self.admitted
    }

    pub fn carried(&self) -> &BTreeSet<EventId> {
        &self.carried
    }

    pub fn diagnostic(&self) -> &[u8] {
        &self.diagnostic
    }
}

/// Exact counted crossing attached to one valid world-face family.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeWorldJunction {
    pub incident: u64,
    pub transmitted: u64,
    pub reflection: Rat,
    pub transmission: Rat,
    pub service_rounds: BigUint,
}

impl NativeWorldJunction {
    fn from_crossing(crossing: CountedCrossing) -> Self {
        Self {
            incident: crossing.incident(),
            transmitted: crossing.transmitted(),
            reflection: Rat::new(
                BigInt::from(crossing.reflection_pair().0),
                BigInt::from(crossing.reflection_pair().1),
            ),
            transmission: Rat::new(
                BigInt::from(crossing.power_transmission_pair().0),
                BigInt::from(crossing.power_transmission_pair().1),
            ),
            service_rounds: BigUint::from(crossing.service_rounds()),
        }
    }

    pub fn matched(&self) -> bool {
        self.incident == self.transmitted
    }

    fn reflection_current(&self) -> Rat {
        self.reflection.clone()
    }

    fn transmission_current(&self) -> Rat {
        self.transmission.clone()
    }

    fn storage(&self) -> Rat {
        Rat::new(
            BigInt::from(1),
            BigInt::from(self.service_rounds.clone()),
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeWorldObstructionKind {
    NoAdmission,
    EmittedGrainReflected,
}

/// A complete valid face family which cannot lawfully found a local returned interaction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeWorldObstruction {
    pub generation: u64,
    pub emission: NativeEmissionAddress,
    pub returned_occurrence: EventId,
    pub incident: u64,
    pub transmitted: u64,
    pub kind: NativeWorldObstructionKind,
    pub diagnostics: Vec<Vec<u8>>,
}

/// Result of constituting an actual world report at one circulation boundary.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "world_return", rename_all = "kebab-case")]
pub enum NativeWorldStage {
    Candidate {
        candidate: NativeCultivationCandidate,
        junction: NativeWorldJunction,
    },
    Obstructed(NativeWorldObstruction),
}

pub(super) struct ConstitutedWorldInteraction {
    pub interaction: ReturnedScaffoldInteraction,
    pub junction: NativeWorldJunction,
}

impl NativeCirculationBoundary {
    /// Issue the complete face family for this exact boundary. Applications may copy these
    /// members into reports but cannot change their generation, emission, grain, or support.
    pub fn issued_world_faces(&self) -> Vec<NativeIssuedWorldFace> {
        self.emission
            .grains
            .iter()
            .enumerate()
            .map(|(grain, emitted)| NativeIssuedWorldFace {
                schema: NATIVE_WORLD_FACE_SCHEMA.to_owned(),
                generation: self.generation,
                emission: self.emission.address.clone(),
                grain,
                support: emitted.occurrences.clone(),
            })
            .collect()
    }
}

impl NativeCirculationSession {
    /// Validate one complete exterior face family and either stage its privately derived local
    /// interaction or return the exact obstruction. The junction is not a terminal law.
    pub fn stage_world_return(
        &self,
        boundary: &NativeCirculationBoundary,
        faces: Vec<NativeWorldFace>,
        returned_occurrence: EventId,
    ) -> Result<NativeWorldStage, NativeSessionError> {
        boundary.validate_for(self)?;
        match constitute_world_interaction(boundary, &faces, returned_occurrence)? {
            Ok(constituted) => Ok(NativeWorldStage::Candidate {
                candidate: NativeCultivationCandidate {
                    schema: NATIVE_CULTIVATION_CANDIDATE_SCHEMA.to_owned(),
                    boundary: boundary.clone(),
                    faces,
                    returned_occurrence,
                },
                junction: constituted.junction,
            }),
            Err(obstruction) => Ok(NativeWorldStage::Obstructed(obstruction)),
        }
    }
}

pub(super) fn constitute_world_interaction(
    boundary: &NativeCirculationBoundary,
    faces: &[NativeWorldFace],
    returned_occurrence: EventId,
) -> Result<Result<ConstitutedWorldInteraction, NativeWorldObstruction>, NativeSessionError> {
    if returned_occurrence <= boundary.request.address.occurrence {
        return Err(NativeSessionError::Return);
    }
    let issued = boundary.issued_world_faces();
    if issued.is_empty() || faces.len() != issued.len() {
        return Err(NativeSessionError::WorldFace);
    }
    let mut seen = BTreeSet::new();
    for face in faces {
        if face.issued.schema != NATIVE_WORLD_FACE_SCHEMA
            || !seen.insert(face.issued.grain)
            || face.issued.grain >= issued.len()
            || face.issued != issued[face.issued.grain]
            || face.carried.is_empty()
            || !face.carried.is_subset(&face.issued.support)
        {
            return Err(NativeSessionError::WorldFace);
        }
    }
    if seen != (0..issued.len()).collect::<BTreeSet<_>>() {
        return Err(NativeSessionError::WorldFace);
    }

    let incident = u64::try_from(faces.len()).map_err(|_| NativeSessionError::WorldFace)?;
    let transmitted = u64::try_from(faces.iter().filter(|face| face.admitted).count())
        .map_err(|_| NativeSessionError::WorldFace)?;
    let diagnostics = faces
        .iter()
        .map(|face| face.diagnostic.clone())
        .collect::<Vec<_>>();
    let selected = boundary.emission.selected_grain;
    let selected_admitted = faces
        .iter()
        .find(|face| face.issued.grain == selected)
        .is_some_and(|face| face.admitted);
    let Some(crossing) = CountedCrossing::meet(incident, transmitted) else {
        return Ok(Err(NativeWorldObstruction {
            generation: boundary.generation,
            emission: boundary.emission.address.clone(),
            returned_occurrence,
            incident,
            transmitted,
            kind: NativeWorldObstructionKind::NoAdmission,
            diagnostics,
        }));
    };
    let junction = NativeWorldJunction::from_crossing(crossing);
    if !selected_admitted {
        return Ok(Err(NativeWorldObstruction {
            generation: boundary.generation,
            emission: boundary.emission.address.clone(),
            returned_occurrence,
            incident,
            transmitted,
            kind: NativeWorldObstructionKind::EmittedGrainReflected,
            diagnostics,
        }));
    }

    let mut native_support = BTreeSet::<NativeStateId>::new();
    for face in faces.iter().filter(|face| face.admitted) {
        let grain = boundary
            .emission
            .grains
            .get(face.issued.grain)
            .ok_or(NativeSessionError::WorldFace)?;
        native_support.insert(grain.future.from);
        native_support.insert(grain.future.to);
    }
    let (current, storage) = if junction.matched() {
        (ExactComplexWaveCurrent::one(), Rat::from_integer(BigInt::from(1)))
    } else {
        (
            ExactComplexWaveCurrent::new(
                junction.transmission_current(),
                junction.reflection_current(),
            ),
            junction.storage(),
        )
    };
    let interaction = ReturnedScaffoldInteraction::constituted(
        boundary.emission.address.clone(),
        returned_occurrence,
        boundary.emitting_boundary,
        current,
        storage,
        native_support,
    )
    .map_err(|error| NativeSessionError::Commit(error.to_string()))?;
    Ok(Ok(ConstitutedWorldInteraction {
        interaction,
        junction,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonic_engine::{
        native_ecology::holonic_intelligence::{
            Bf16ExcitationDismantling, ExteriorModality, ForeignBf16Excitation,
            NativeInferenceAddress, NativeInferenceRequest,
        },
        receiver_exact_compression::ReceiverId,
        native_spool::NativeGeneratorStep,
        soulkiller::dismantle,
        BoundaryId,
    };

    use crate::native_intelligence::{
        consume_dismantling_return, InferenceConfigurationAddress, MorphologyLineage,
        NativeCirculationConfiguration, NativeMorphologyArtifact,
    };

    fn excitation(event: u64) -> ForeignBf16Excitation {
        ForeignBf16Excitation {
            event: EventId(event),
            predecessor: None,
            entering_boundary: BoundaryId(event * 2),
            emitting_boundary: BoundaryId(event * 2 + 1),
            source_occurrence: format!("cold/{event}"),
            exterior_modality: ExteriorModality::Text,
            entering_codewords: vec![
                0x3f80 + event as u16,
                0x4000 + event as u16,
                0x4040 + event as u16,
            ],
            returned_codewords: vec![
                0x4080 + event as u16,
                0x40a0 + event as u16,
                0x40c0 + event as u16,
            ],
            interventions: BTreeSet::from([format!("intervention/{event}")]),
            receiver_consequences: BTreeSet::from([format!("consequence/{event}")]),
        }
    }

    fn session_and_boundary() -> (NativeCirculationSession, NativeCirculationBoundary) {
        let mut returned = dismantle(Bf16ExcitationDismantling {
            receiver: ReceiverId(7),
            excitations: vec![excitation(1), excitation(2), excitation(3)],
        })
        .expect("dismantle");
        let spool = &mut returned.native.spools[0];
        let steps = spool
            .threads
            .iter()
            .map(|thread| {
                let occurrence = &thread.occurrences[0];
                NativeGeneratorStep {
                    from: occurrence.entering_native,
                    to: occurrence.emitting_native,
                    thread: thread.address.clone(),
                }
            })
            .collect::<Vec<_>>();
        let domain = steps.iter().map(|step| step.from).collect::<BTreeSet<_>>();
        spool.generator_descents[0].steps = steps;
        spool.generator_descents[0].open_domain =
            &spool.native_population - &domain;
        let (hot, _) = consume_dismantling_return(returned).expect("hot");
        let package = NativeMorphologyArtifact::found(
            hot,
            MorphologyLineage::origin(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
        .expect("package");
        let session = NativeCirculationSession::mount(
            package,
            NativeCirculationConfiguration::found(InferenceConfigurationAddress {
                ingress_aperture: "native-addressed-occurrence".to_owned(),
                occurrence: EventId(1),
                receiver: ReceiverId(7),
                continuation_receiver: "exterior-world-face".to_owned(),
                world_return_law: "issued-complete-face-family".to_owned(),
                emission_codec: "owned-native-grain".to_owned(),
                apparatus: "resident-native-word".to_owned(),
                stochastic_current: None,
            })
            .expect("configuration"),
        )
        .expect("session");
        let native = session.package().hot().native();
        let boundary = session
            .conduct(NativeInferenceRequest {
                address: NativeInferenceAddress {
                    spool: native.spools[0].address.clone(),
                    thread: native.spools[0].threads[0].address.clone(),
                    occurrence: EventId(1),
                },
                receiver: ReceiverId(7),
            })
            .expect("boundary");
        assert!(boundary.emission.grains.len() >= 3);
        (session, boundary)
    }

    fn report(
        boundary: &NativeCirculationBoundary,
        admitted: impl Fn(usize) -> bool,
        diagnostic: &[u8],
    ) -> Vec<NativeWorldFace> {
        boundary
            .issued_world_faces()
            .into_iter()
            .map(|issued| {
                NativeWorldFace::report(
                    issued.clone(),
                    admitted(issued.grain()),
                    issued.support().clone(),
                    diagnostic.to_vec(),
                )
                .expect("face")
            })
            .collect()
    }

    #[test]
    fn matched_partial_and_no_admission_are_distinct_without_a_terminal_claim() {
        let (session, boundary) = session_and_boundary();
        let matched = session
            .stage_world_return(&boundary, report(&boundary, |_| true, b"left"), EventId(100))
            .expect("matched");
        let NativeWorldStage::Candidate {
            junction: matched, ..
        } = matched
        else {
            panic!("matched family must stage")
        };
        assert!(matched.matched());

        let selected = boundary.emission.selected_grain;
        let partial = session
            .stage_world_return(
                &boundary,
                report(&boundary, |grain| grain == selected, b"right"),
                EventId(101),
            )
            .expect("partial");
        let NativeWorldStage::Candidate {
            junction: partial, ..
        } = partial
        else {
            panic!("selected partial family must stage")
        };
        assert!(!partial.matched());
        assert_eq!(partial.transmitted, 1);

        let none = session
            .stage_world_return(&boundary, report(&boundary, |_| false, b"none"), EventId(102))
            .expect("no admission");
        assert!(matches!(
            none,
            NativeWorldStage::Obstructed(NativeWorldObstruction {
                kind: NativeWorldObstructionKind::NoAdmission,
                transmitted: 0,
                ..
            })
        ));
    }

    #[test]
    fn diagnostics_cannot_change_the_derived_current_storage_or_support() {
        let (session, boundary) = session_and_boundary();
        let left = session
            .stage_world_return(&boundary, report(&boundary, |_| true, b"left"), EventId(100))
            .expect("left");
        let right = session
            .stage_world_return(
                &boundary,
                report(&boundary, |_| true, b"entirely different diagnostics"),
                EventId(100),
            )
            .expect("right");
        let (
            NativeWorldStage::Candidate {
                candidate: left,
                junction: left_junction,
            },
            NativeWorldStage::Candidate {
                candidate: right,
                junction: right_junction,
            },
        ) = (left, right)
        else {
            panic!("both complete families must stage")
        };
        let left_return = constitute_world_interaction(
            &left.boundary,
            &left.faces,
            left.returned_occurrence,
        )
        .expect("left valid")
        .expect("left interaction");
        let right_return = constitute_world_interaction(
            &right.boundary,
            &right.faces,
            right.returned_occurrence,
        )
        .expect("right valid")
        .expect("right interaction");
        assert_eq!(left_junction, right_junction);
        assert_eq!(left_return.interaction, right_return.interaction);
    }

    #[test]
    fn incomplete_duplicate_stale_foreign_and_nonlater_faces_refuse_without_mutation() {
        let (session, boundary) = session_and_boundary();
        let before = session.package().canonical_bytes().expect("before");

        let mut missing = report(&boundary, |_| true, b"");
        missing.pop();
        assert!(matches!(
            session.stage_world_return(&boundary, missing, EventId(100)),
            Err(NativeSessionError::WorldFace)
        ));

        let mut duplicate = report(&boundary, |_| true, b"");
        duplicate[1] = duplicate[0].clone();
        assert!(matches!(
            session.stage_world_return(&boundary, duplicate, EventId(100)),
            Err(NativeSessionError::WorldFace)
        ));

        let mut wrong_emission = report(&boundary, |_| true, b"");
        wrong_emission[0].issued.emission.entering_occurrence = EventId(99);
        assert!(matches!(
            session.stage_world_return(&boundary, wrong_emission, EventId(100)),
            Err(NativeSessionError::WorldFace)
        ));

        let mut wrong_grain = report(&boundary, |_| true, b"");
        wrong_grain[0].issued.grain = boundary.emission.grains.len();
        assert!(matches!(
            session.stage_world_return(&boundary, wrong_grain, EventId(100)),
            Err(NativeSessionError::WorldFace)
        ));

        let mut out_of_support = report(&boundary, |_| true, b"");
        out_of_support[0].carried.insert(EventId(999));
        assert!(matches!(
            session.stage_world_return(&boundary, out_of_support, EventId(100)),
            Err(NativeSessionError::WorldFace)
        ));

        let mut stale = boundary.clone();
        stale.generation += 1;
        assert!(matches!(
            session.stage_world_return(
                &stale,
                report(&stale, |_| true, b""),
                EventId(100)
            ),
            Err(NativeSessionError::Boundary)
        ));
        assert!(matches!(
            session.stage_world_return(
                &boundary,
                report(&boundary, |_| true, b""),
                boundary.request.address.occurrence
            ),
            Err(NativeSessionError::Return)
        ));
        assert_eq!(session.package().canonical_bytes().expect("after"), before);
    }

    #[test]
    fn reflection_of_the_selected_emission_returns_an_obstruction() {
        let (session, boundary) = session_and_boundary();
        let selected = boundary.emission.selected_grain;
        let stage = session
            .stage_world_return(
                &boundary,
                report(&boundary, |grain| grain != selected, b"reflected"),
                EventId(100),
            )
            .expect("valid reflected family");
        assert!(matches!(
            stage,
            NativeWorldStage::Obstructed(NativeWorldObstruction {
                kind: NativeWorldObstructionKind::EmittedGrainReflected,
                ..
            })
        ));
    }
}
