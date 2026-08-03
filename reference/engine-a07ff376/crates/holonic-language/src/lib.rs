//! Exact reflective runtime beneath learnable surface codecs.
//!
//! This crate deliberately defines no universal syntax and no semantic token. A visible language,
//! file format, theorem prover, machine instruction set, or sensor representation is a codec body
//! supplied as `Program`; its material is a receiver face supplied as `Face`; and its live local
//! bindings are an `Environment`. The runtime owns only their causal relationship:
//!
//! 1. a continuation receives one caused face through one codec version;
//! 2. the codec may advance, rest, or request a reflective lift;
//! 3. reflection reifies the codec, environment-bearing continuation, and instruction horizon;
//! 4. a returned replacement becomes a lineaged codec version and governs resumed conduct.
//!
//! Bytecode is therefore one possible terminal `Program`, not the ontology of every preceding
//! face. CPU and card executors may realize the same typed crossing without becoming its law.

#![no_std]

extern crate alloc;

use alloc::borrow::ToOwned;
use core::fmt;

use holonic_structure::{
    GrowingKeyAtlas, KeyAtlasError, LocalSet, LocalStructureError, OrdinalAtlasError,
    SparseOrdinalAtlas,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FaceId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CodecId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ContinuationId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ReflectionId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ReceiverId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ContinuationState {
    Running,
    Reflected(ReflectionId),
    Rested,
    Obstructed,
}

#[derive(Debug, PartialEq, Eq)]
pub struct CodecVersion<Program, Contact = ()> {
    pub id: CodecId,
    pub parents: LocalSet<CodecId>,
    pub caused_by: FaceId,
    pub program: Program,
    contacts: LocalSet<Contact>,
}

impl<Program, Contact> CodecVersion<Program, Contact> {
    pub fn contacts(&self) -> &LocalSet<Contact> {
        &self.contacts
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct ReflectiveContinuation<Environment> {
    pub id: ContinuationId,
    pub codec: CodecId,
    pub next_instruction: u64,
    pub state: ContinuationState,
    environment: Option<Environment>,
}

impl<Environment> ReflectiveContinuation<Environment> {
    pub fn environment(&self) -> Option<&Environment> {
        self.environment.as_ref()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReflectionState {
    Open,
    Revised(CodecId),
    ResumedUnchanged,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReflectionFrame {
    pub id: ReflectionId,
    pub receiver: ReceiverId,
    pub continuation: ContinuationId,
    pub codec: CodecId,
    pub instruction: u64,
    pub state: ReflectionState,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReflectiveRuntimeError {
    CarrierExtent,
    UnknownFace(FaceId),
    UnknownCodec(CodecId),
    UnknownContinuation(ContinuationId),
    UnknownReflection(ReflectionId),
    ContinuationNotRunning(ContinuationId),
    ContinuationNotReflected(ContinuationId),
    ReflectionAlreadyReturned(ReflectionId),
    ReflectionDoesNotOwnContinuation(ReflectionId),
    InstructionExtent,
    MalformedStanding,
}

impl fmt::Display for ReflectiveRuntimeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl core::error::Error for ReflectiveRuntimeError {}

impl From<OrdinalAtlasError> for ReflectiveRuntimeError {
    fn from(_: OrdinalAtlasError) -> Self {
        Self::CarrierExtent
    }
}

/// A codec step returns ownership of the environment it received. The interpreter cannot retain
/// a hidden second environment, and the runtime need not clone standing to recover from refusal.
#[derive(Debug, PartialEq, Eq)]
pub enum CodecStep<Environment, Emission> {
    Advance {
        environment: Environment,
        emission: Emission,
    },
    Rest {
        environment: Environment,
        emission: Emission,
    },
    Reflect {
        environment: Environment,
        receiver: ReceiverId,
        emission: Emission,
    },
}

/// A refused crossing returns the exact environment to the continuation that supplied it.
#[derive(Debug, PartialEq, Eq)]
pub struct CodecObstruction<Environment, Obstruction> {
    pub environment: Environment,
    pub obstruction: Obstruction,
}

pub trait ReflectiveCodecExecutor<Program, Environment, Face> {
    type Emission;
    type Obstruction;

    fn receive(
        &mut self,
        program: &Program,
        instruction: u64,
        environment: Environment,
        face: &Face,
    ) -> Result<
        CodecStep<Environment, Self::Emission>,
        CodecObstruction<Environment, Self::Obstruction>,
    >;
}

#[derive(Debug, PartialEq, Eq)]
pub struct CodecEmission<Emission> {
    pub emission: Emission,
    pub reflection: Option<ReflectionId>,
    pub next_instruction: u64,
    pub state: ContinuationState,
}

#[derive(Debug, PartialEq, Eq)]
pub enum CodecCrossingError<Obstruction, Emission> {
    Runtime(ReflectiveRuntimeError),
    Executor(Obstruction),
    ReturnCouldNotCommit {
        error: ReflectiveRuntimeError,
        emission: Emission,
    },
}

#[derive(Debug, PartialEq, Eq)]
pub struct CodecRevisionRefusal<Program> {
    pub error: ReflectiveRuntimeError,
    pub program: Program,
}

#[derive(Debug, PartialEq, Eq)]
pub struct CodecLineageRefusal<Program, Contact> {
    pub error: ReflectiveRuntimeError,
    pub program: Program,
    pub parents: LocalSet<CodecId>,
    pub contacts: LocalSet<Contact>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReflectiveRuntimeRestReceipt {
    pub faces: usize,
    pub codecs: usize,
    pub continuations: usize,
    pub reflections: usize,
    pub recruited_contacts: usize,
}

/// Native structural rest of the continuing reflective body. Remount transfers these owners
/// directly; it does not replay the faces which developed them.
#[derive(Debug, PartialEq, Eq)]
pub struct ReflectiveRuntimeRest<Program, Environment, Face, Contact = ()> {
    faces: SparseOrdinalAtlas<Face>,
    codecs: SparseOrdinalAtlas<CodecVersion<Program, Contact>>,
    continuations: SparseOrdinalAtlas<ReflectiveContinuation<Environment>>,
    reflections: SparseOrdinalAtlas<ReflectionFrame>,
    recruitment: GrowingKeyAtlas<Contact, LocalSet<CodecId>>,
}

impl<Program, Environment, Face, Contact>
    ReflectiveRuntimeRest<Program, Environment, Face, Contact>
{
    pub fn receipt(&self) -> ReflectiveRuntimeRestReceipt {
        ReflectiveRuntimeRestReceipt {
            faces: self.faces.len(),
            codecs: self.codecs.len(),
            continuations: self.continuations.len(),
            reflections: self.reflections.len(),
            recruited_contacts: self.recruitment.len(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct ReflectiveRemountRefusal<Program, Environment, Face, Contact = ()> {
    pub error: ReflectiveRuntimeError,
    pub rest: ReflectiveRuntimeRest<Program, Environment, Face, Contact>,
}

/// One continuing reflective body. It is intentionally not `Clone`: plurality must be expressed
/// through explicit continuations and reflections, not by copying the complete world.
#[derive(Debug, PartialEq, Eq)]
pub struct ReflectiveRuntime<Program, Environment, Face, Contact = ()> {
    faces: SparseOrdinalAtlas<Face>,
    codecs: SparseOrdinalAtlas<CodecVersion<Program, Contact>>,
    continuations: SparseOrdinalAtlas<ReflectiveContinuation<Environment>>,
    reflections: SparseOrdinalAtlas<ReflectionFrame>,
    recruitment: GrowingKeyAtlas<Contact, LocalSet<CodecId>>,
}

impl<Program, Environment, Face, Contact> Default
    for ReflectiveRuntime<Program, Environment, Face, Contact>
{
    fn default() -> Self {
        Self::new_with_contacts()
    }
}

impl<Program, Environment, Face, Contact> ReflectiveRuntime<Program, Environment, Face, Contact> {
    pub const fn new_with_contacts() -> Self {
        Self {
            faces: SparseOrdinalAtlas::new(),
            codecs: SparseOrdinalAtlas::new(),
            continuations: SparseOrdinalAtlas::new(),
            reflections: SparseOrdinalAtlas::new(),
            recruitment: GrowingKeyAtlas::new(),
        }
    }

    pub fn found_face(&mut self, face: Face) -> Result<FaceId, (ReflectiveRuntimeError, Face)> {
        self.faces
            .try_push_recover(face)
            .map(FaceId)
            .map_err(|(_, face)| (ReflectiveRuntimeError::CarrierExtent, face))
    }

    pub fn mount_codec(
        &mut self,
        program: Program,
        caused_by: FaceId,
    ) -> Result<CodecId, CodecRevisionRefusal<Program>> {
        if !self.faces.contains(caused_by.0) {
            return Err(CodecRevisionRefusal {
                error: ReflectiveRuntimeError::UnknownFace(caused_by),
                program,
            });
        }
        let id = CodecId(self.codecs.extent());
        let version = CodecVersion {
            id,
            parents: LocalSet::new(),
            caused_by,
            program,
            contacts: LocalSet::new(),
        };
        self.codecs
            .try_push_recover(version)
            .map(|_| id)
            .map_err(|(_, version)| CodecRevisionRefusal {
                error: ReflectiveRuntimeError::CarrierExtent,
                program: version.program,
            })
    }

    pub fn open_continuation(
        &mut self,
        codec: CodecId,
        environment: Environment,
    ) -> Result<ContinuationId, (ReflectiveRuntimeError, Environment)> {
        if !self.codecs.contains(codec.0) {
            return Err((ReflectiveRuntimeError::UnknownCodec(codec), environment));
        }
        let id = ContinuationId(self.continuations.extent());
        let continuation = ReflectiveContinuation {
            id,
            codec,
            next_instruction: 0,
            state: ContinuationState::Running,
            environment: Some(environment),
        };
        self.continuations
            .try_push_recover(continuation)
            .map(|_| id)
            .map_err(|(_, mut continuation)| {
                (
                    ReflectiveRuntimeError::CarrierExtent,
                    continuation
                        .environment
                        .take()
                        .expect("a proposed continuation owns its environment"),
                )
            })
    }

    pub fn face(&self, id: FaceId) -> Option<&Face> {
        self.faces.get(id.0)
    }

    pub fn codec(&self, id: CodecId) -> Option<&CodecVersion<Program, Contact>> {
        self.codecs.get(id.0)
    }

    pub fn codecs(&self) -> impl Iterator<Item = &CodecVersion<Program, Contact>> {
        self.codecs.values()
    }

    pub fn continuation(&self, id: ContinuationId) -> Option<&ReflectiveContinuation<Environment>> {
        self.continuations.get(id.0)
    }

    pub fn reflection(&self, id: ReflectionId) -> Option<&ReflectionFrame> {
        self.reflections.get(id.0)
    }

    pub fn receive_with<Executor>(
        &mut self,
        continuation_id: ContinuationId,
        face_id: FaceId,
        executor: &mut Executor,
    ) -> Result<
        CodecEmission<Executor::Emission>,
        CodecCrossingError<Executor::Obstruction, Executor::Emission>,
    >
    where
        Executor: ReflectiveCodecExecutor<Program, Environment, Face>,
    {
        if !self.faces.contains(face_id.0) {
            return Err(CodecCrossingError::Runtime(
                ReflectiveRuntimeError::UnknownFace(face_id),
            ));
        }
        let (codec_id, instruction) = {
            let continuation =
                self.continuations
                    .get(continuation_id.0)
                    .ok_or(CodecCrossingError::Runtime(
                        ReflectiveRuntimeError::UnknownContinuation(continuation_id),
                    ))?;
            if continuation.state != ContinuationState::Running {
                return Err(CodecCrossingError::Runtime(
                    ReflectiveRuntimeError::ContinuationNotRunning(continuation_id),
                ));
            }
            if continuation.environment.is_none() {
                return Err(CodecCrossingError::Runtime(
                    ReflectiveRuntimeError::MalformedStanding,
                ));
            }
            (continuation.codec, continuation.next_instruction)
        };
        if !self.codecs.contains(codec_id.0) {
            return Err(CodecCrossingError::Runtime(
                ReflectiveRuntimeError::UnknownCodec(codec_id),
            ));
        }
        let environment = {
            let continuation = self
                .continuations
                .get_mut(continuation_id.0)
                .expect("validated continuation remains standing");
            continuation
                .environment
                .take()
                .expect("validated continuation owns its environment")
        };
        let crossing = {
            let program = &self
                .codecs
                .get(codec_id.0)
                .expect("validated codec remains standing")
                .program;
            let face = self
                .faces
                .get(face_id.0)
                .expect("validated face remains standing");
            executor.receive(program, instruction, environment, face)
        };
        let step = match crossing {
            Ok(step) => step,
            Err(obstruction) => {
                self.restore_environment(continuation_id, obstruction.environment)
                    .map_err(CodecCrossingError::Runtime)?;
                return Err(CodecCrossingError::Executor(obstruction.obstruction));
            }
        };
        match step {
            CodecStep::Advance {
                environment,
                emission,
            } => {
                let Some(next_instruction) = instruction.checked_add(1) else {
                    self.restore_environment(continuation_id, environment)
                        .map_err(CodecCrossingError::Runtime)?;
                    return Err(CodecCrossingError::ReturnCouldNotCommit {
                        error: ReflectiveRuntimeError::InstructionExtent,
                        emission,
                    });
                };
                self.commit_continuation_step(
                    continuation_id,
                    environment,
                    next_instruction,
                    ContinuationState::Running,
                )
                .map_err(CodecCrossingError::Runtime)?;
                Ok(CodecEmission {
                    emission,
                    reflection: None,
                    next_instruction,
                    state: ContinuationState::Running,
                })
            }
            CodecStep::Rest {
                environment,
                emission,
            } => {
                self.commit_continuation_step(
                    continuation_id,
                    environment,
                    instruction,
                    ContinuationState::Rested,
                )
                .map_err(CodecCrossingError::Runtime)?;
                Ok(CodecEmission {
                    emission,
                    reflection: None,
                    next_instruction: instruction,
                    state: ContinuationState::Rested,
                })
            }
            CodecStep::Reflect {
                environment,
                receiver,
                emission,
            } => {
                let id = ReflectionId(self.reflections.extent());
                let frame = ReflectionFrame {
                    id,
                    receiver,
                    continuation: continuation_id,
                    codec: codec_id,
                    instruction,
                    state: ReflectionState::Open,
                };
                if self.reflections.try_push_recover(frame).is_err() {
                    self.restore_environment(continuation_id, environment)
                        .map_err(CodecCrossingError::Runtime)?;
                    return Err(CodecCrossingError::ReturnCouldNotCommit {
                        error: ReflectiveRuntimeError::CarrierExtent,
                        emission,
                    });
                }
                self.commit_continuation_step(
                    continuation_id,
                    environment,
                    instruction,
                    ContinuationState::Reflected(id),
                )
                .map_err(CodecCrossingError::Runtime)?;
                Ok(CodecEmission {
                    emission,
                    reflection: Some(id),
                    next_instruction: instruction,
                    state: ContinuationState::Reflected(id),
                })
            }
        }
    }

    pub fn revise_and_resume(
        &mut self,
        reflection_id: ReflectionId,
        caused_by: FaceId,
        program: Program,
    ) -> Result<CodecId, CodecRevisionRefusal<Program>> {
        let Some(frame) = self.reflections.get(reflection_id.0) else {
            return Err(CodecRevisionRefusal {
                error: ReflectiveRuntimeError::UnknownReflection(reflection_id),
                program,
            });
        };
        if frame.state != ReflectionState::Open {
            return Err(CodecRevisionRefusal {
                error: ReflectiveRuntimeError::ReflectionAlreadyReturned(reflection_id),
                program,
            });
        }
        if !self.faces.contains(caused_by.0) {
            return Err(CodecRevisionRefusal {
                error: ReflectiveRuntimeError::UnknownFace(caused_by),
                program,
            });
        }
        let continuation_id = frame.continuation;
        let parent = frame.codec;
        let Some(continuation) = self.continuations.get(continuation_id.0) else {
            return Err(CodecRevisionRefusal {
                error: ReflectiveRuntimeError::UnknownContinuation(continuation_id),
                program,
            });
        };
        if continuation.state != ContinuationState::Reflected(reflection_id) {
            return Err(CodecRevisionRefusal {
                error: ReflectiveRuntimeError::ReflectionDoesNotOwnContinuation(reflection_id),
                program,
            });
        }
        let codec_id = CodecId(self.codecs.extent());
        let version = CodecVersion {
            id: codec_id,
            parents: LocalSet::from([parent]),
            caused_by,
            program,
            contacts: LocalSet::new(),
        };
        if let Err((_, version)) = self.codecs.try_push_recover(version) {
            return Err(CodecRevisionRefusal {
                error: ReflectiveRuntimeError::CarrierExtent,
                program: version.program,
            });
        }
        let continuation = self
            .continuations
            .get_mut(continuation_id.0)
            .expect("validated continuation remains standing");
        continuation.codec = codec_id;
        continuation.state = ContinuationState::Running;
        self.reflections
            .get_mut(reflection_id.0)
            .expect("validated reflection remains standing")
            .state = ReflectionState::Revised(codec_id);
        Ok(codec_id)
    }

    pub fn into_rest(self) -> ReflectiveRuntimeRest<Program, Environment, Face, Contact> {
        ReflectiveRuntimeRest {
            faces: self.faces,
            codecs: self.codecs,
            continuations: self.continuations,
            reflections: self.reflections,
            recruitment: self.recruitment,
        }
    }

    pub fn from_rest(
        rest: ReflectiveRuntimeRest<Program, Environment, Face, Contact>,
    ) -> Result<Self, ReflectiveRemountRefusal<Program, Environment, Face, Contact>>
    where
        Contact: Ord,
    {
        let runtime = Self {
            faces: rest.faces,
            codecs: rest.codecs,
            continuations: rest.continuations,
            reflections: rest.reflections,
            recruitment: rest.recruitment,
        };
        if let Err(error) = runtime.validate_standing() {
            return Err(ReflectiveRemountRefusal {
                error,
                rest: runtime.into_rest(),
            });
        }
        Ok(runtime)
    }

    pub fn resume_unchanged(
        &mut self,
        reflection_id: ReflectionId,
    ) -> Result<(), ReflectiveRuntimeError> {
        let frame = self
            .reflections
            .get(reflection_id.0)
            .copied()
            .ok_or(ReflectiveRuntimeError::UnknownReflection(reflection_id))?;
        if frame.state != ReflectionState::Open {
            return Err(ReflectiveRuntimeError::ReflectionAlreadyReturned(
                reflection_id,
            ));
        }
        let continuation = self.continuations.get_mut(frame.continuation.0).ok_or(
            ReflectiveRuntimeError::UnknownContinuation(frame.continuation),
        )?;
        if continuation.state != ContinuationState::Reflected(reflection_id) {
            return Err(ReflectiveRuntimeError::ReflectionDoesNotOwnContinuation(
                reflection_id,
            ));
        }
        continuation.state = ContinuationState::Running;
        self.reflections
            .get_mut(reflection_id.0)
            .expect("validated reflection remains standing")
            .state = ReflectionState::ResumedUnchanged;
        Ok(())
    }

    fn restore_environment(
        &mut self,
        continuation_id: ContinuationId,
        environment: Environment,
    ) -> Result<(), ReflectiveRuntimeError> {
        let continuation = self
            .continuations
            .get_mut(continuation_id.0)
            .ok_or(ReflectiveRuntimeError::UnknownContinuation(continuation_id))?;
        if continuation.environment.replace(environment).is_some() {
            return Err(ReflectiveRuntimeError::MalformedStanding);
        }
        Ok(())
    }

    fn commit_continuation_step(
        &mut self,
        continuation_id: ContinuationId,
        environment: Environment,
        next_instruction: u64,
        state: ContinuationState,
    ) -> Result<(), ReflectiveRuntimeError> {
        let continuation = self
            .continuations
            .get_mut(continuation_id.0)
            .ok_or(ReflectiveRuntimeError::UnknownContinuation(continuation_id))?;
        if continuation.environment.replace(environment).is_some() {
            return Err(ReflectiveRuntimeError::MalformedStanding);
        }
        continuation.next_instruction = next_instruction;
        continuation.state = state;
        Ok(())
    }

    fn validate_standing(&self) -> Result<(), ReflectiveRuntimeError>
    where
        Contact: Ord,
    {
        for (ordinal, version) in self.codecs.iter() {
            if version.id.0 != ordinal || !self.faces.contains(version.caused_by.0) {
                return Err(ReflectiveRuntimeError::MalformedStanding);
            }
            for parent in &version.parents {
                if !self.codecs.contains(parent.0) {
                    return Err(ReflectiveRuntimeError::MalformedStanding);
                }
            }
            for contact in &version.contacts {
                if !self
                    .recruitment
                    .get(contact)
                    .is_some_and(|versions| versions.contains(&version.id))
                {
                    return Err(ReflectiveRuntimeError::MalformedStanding);
                }
            }
        }
        for (ordinal, continuation) in self.continuations.iter() {
            if continuation.id.0 != ordinal
                || !self.codecs.contains(continuation.codec.0)
                || continuation.environment.is_none()
            {
                return Err(ReflectiveRuntimeError::MalformedStanding);
            }
            if let ContinuationState::Reflected(reflection) = continuation.state {
                let frame = self
                    .reflections
                    .get(reflection.0)
                    .ok_or(ReflectiveRuntimeError::MalformedStanding)?;
                if frame.continuation != continuation.id || frame.state != ReflectionState::Open {
                    return Err(ReflectiveRuntimeError::MalformedStanding);
                }
            }
        }
        for (ordinal, frame) in self.reflections.iter() {
            if frame.id.0 != ordinal
                || !self.continuations.contains(frame.continuation.0)
                || !self.codecs.contains(frame.codec.0)
            {
                return Err(ReflectiveRuntimeError::MalformedStanding);
            }
        }
        Ok(())
    }
}

impl<Program, Environment, Face> ReflectiveRuntime<Program, Environment, Face, ()> {
    pub const fn new() -> Self {
        Self::new_with_contacts()
    }
}

impl<Program, Environment, Face, Contact: Ord + Clone>
    ReflectiveRuntime<Program, Environment, Face, Contact>
{
    /// Mount a codec with every co-present parent and receiver contact retained exactly.
    pub fn mount_codec_with_lineage(
        &mut self,
        program: Program,
        caused_by: FaceId,
        parents: LocalSet<CodecId>,
        contacts: LocalSet<Contact>,
    ) -> Result<CodecId, CodecLineageRefusal<Program, Contact>> {
        if !self.faces.contains(caused_by.0) {
            return Err(CodecLineageRefusal {
                error: ReflectiveRuntimeError::UnknownFace(caused_by),
                program,
                parents,
                contacts,
            });
        }
        for parent in &parents {
            if !self.codecs.contains(parent.0) {
                return Err(CodecLineageRefusal {
                    error: ReflectiveRuntimeError::UnknownCodec(*parent),
                    program,
                    parents,
                    contacts,
                });
            }
        }
        self.commit_lineaged_codec(program, caused_by, parents, contacts)
    }

    /// Return a revised plural codec to the same reflected continuation.
    pub fn revise_and_resume_with_lineage(
        &mut self,
        reflection_id: ReflectionId,
        caused_by: FaceId,
        program: Program,
        mut parents: LocalSet<CodecId>,
        contacts: LocalSet<Contact>,
    ) -> Result<CodecId, CodecLineageRefusal<Program, Contact>> {
        let Some(frame) = self.reflections.get(reflection_id.0) else {
            return Err(CodecLineageRefusal {
                error: ReflectiveRuntimeError::UnknownReflection(reflection_id),
                program,
                parents,
                contacts,
            });
        };
        if frame.state != ReflectionState::Open {
            return Err(CodecLineageRefusal {
                error: ReflectiveRuntimeError::ReflectionAlreadyReturned(reflection_id),
                program,
                parents,
                contacts,
            });
        }
        let continuation_id = frame.continuation;
        let current_parent = frame.codec;
        if !self.faces.contains(caused_by.0) {
            return Err(CodecLineageRefusal {
                error: ReflectiveRuntimeError::UnknownFace(caused_by),
                program,
                parents,
                contacts,
            });
        }
        if parents.try_insert(current_parent).is_err() {
            return Err(CodecLineageRefusal {
                error: ReflectiveRuntimeError::CarrierExtent,
                program,
                parents,
                contacts,
            });
        }
        for parent in &parents {
            if !self.codecs.contains(parent.0) {
                return Err(CodecLineageRefusal {
                    error: ReflectiveRuntimeError::UnknownCodec(*parent),
                    program,
                    parents,
                    contacts,
                });
            }
        }
        let Some(continuation) = self.continuations.get(continuation_id.0) else {
            return Err(CodecLineageRefusal {
                error: ReflectiveRuntimeError::UnknownContinuation(continuation_id),
                program,
                parents,
                contacts,
            });
        };
        if continuation.state != ContinuationState::Reflected(reflection_id) {
            return Err(CodecLineageRefusal {
                error: ReflectiveRuntimeError::ReflectionDoesNotOwnContinuation(reflection_id),
                program,
                parents,
                contacts,
            });
        }
        let codec_id = self.commit_lineaged_codec(program, caused_by, parents, contacts)?;
        let continuation = self
            .continuations
            .get_mut(continuation_id.0)
            .expect("validated continuation remains standing");
        continuation.codec = codec_id;
        continuation.state = ContinuationState::Running;
        self.reflections
            .get_mut(reflection_id.0)
            .expect("validated reflection remains standing")
            .state = ReflectionState::Revised(codec_id);
        Ok(codec_id)
    }

    pub fn recruited_codecs(&self, contact: &Contact) -> Option<&LocalSet<CodecId>> {
        self.recruitment.get(contact)
    }

    fn commit_lineaged_codec(
        &mut self,
        program: Program,
        caused_by: FaceId,
        parents: LocalSet<CodecId>,
        contacts: LocalSet<Contact>,
    ) -> Result<CodecId, CodecLineageRefusal<Program, Contact>> {
        let id = CodecId(self.codecs.extent());
        let version = CodecVersion {
            id,
            parents,
            caused_by,
            program,
            contacts,
        };
        if let Err((_, version)) = self.codecs.try_push_recover(version) {
            return Err(CodecLineageRefusal {
                error: ReflectiveRuntimeError::CarrierExtent,
                program: version.program,
                parents: version.parents,
                contacts: version.contacts,
            });
        }
        let contact_count = self
            .codecs
            .get(id.0)
            .expect("new codec remains standing")
            .contacts
            .len();
        for contact_at in 0..contact_count {
            let contact = self
                .codecs
                .get(id.0)
                .and_then(|version| version.contacts.get(contact_at))
                .expect("codec contact remains standing")
                .to_owned();
            let indexed = if let Some(versions) = self.recruitment.get_mut(&contact) {
                versions
                    .try_insert(id)
                    .map_err(|_| KeyAtlasError::CarrierExtent)
            } else {
                let mut versions = LocalSet::new();
                match versions.try_insert(id) {
                    Ok(_) => self.recruitment.try_insert(contact, versions).map(|_| true),
                    Err(_) => Err(KeyAtlasError::CarrierExtent),
                }
            };
            if indexed.is_err() {
                self.rollback_contact_index(id, contact_at);
                let version = self
                    .codecs
                    .remove(id.0)
                    .expect("refused codec remains recoverable");
                return Err(CodecLineageRefusal {
                    error: ReflectiveRuntimeError::CarrierExtent,
                    program: version.program,
                    parents: version.parents,
                    contacts: version.contacts,
                });
            }
        }
        Ok(id)
    }

    fn rollback_contact_index(&mut self, id: CodecId, indexed_contacts: usize) {
        for contact_at in 0..indexed_contacts {
            let contact = self
                .codecs
                .get(id.0)
                .and_then(|version| version.contacts.get(contact_at))
                .expect("indexed codec contact remains standing")
                .to_owned();
            if let Some(versions) = self.recruitment.get_mut(&contact) {
                versions.remove(&id);
            }
        }
    }
}

impl From<LocalStructureError> for ReflectiveRuntimeError {
    fn from(_: LocalStructureError) -> Self {
        Self::CarrierExtent
    }
}
