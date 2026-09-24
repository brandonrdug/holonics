//! **The reflective continuation: a navigator whose codec can be revised mid-passage.**
//!
//! [established-bounded; source-inspected] The source-neutral continuation contract is a chart of
//! Navigator and Receiver operations, not a new elementary object
//! ([objects §3](../../../../docs/ELEMENTARY_OBJECTS.md#3-navigator)). No universal syntax is
//! defined here: a language, file format, instruction set or sensor representation is a codec body
//! supplied as `Program`; its material is a receiver face supplied as `Face`; its live bindings
//! are an `Environment`. The runtime owns only their causal relationship:
//!
//! 1. a continuation receives one caused face through one codec version;
//! 2. the codec may advance, rest, or request a reflection;
//! 3. a reflection records the codec and the instruction at which it was requested;
//! 4. a returned revision is a new codec version naming the reflected codec as a parent, and it
//!    governs the same continuation from the same instruction; an unchanged resumption keeps the
//!    codec and the instruction.
//!
//! The environment returned by the executor stays with the continuation throughout, including
//! when the executor refuses a crossing.
//!
//! | Lean `Transport/ReflectiveContinuation` | Rust |
//! |---|---|
//! | `ContinuationState`, `ReflectionState`, `Continuation`, `Frame` | [`ContinuationState`], [`ReflectionState`], [`ReflectiveContinuation`], [`ReflectionFrame`] |
//! | `requestReflection`, `requestReflection_success` | [`ReflectiveRuntime::receive_with`] returning [`CodecStep::Reflect`] |
//! | `reviseAndResume`, `reviseAndResume_success`, `revision_resumes_the_requested_boundary` | [`ReflectiveRuntime::revise_and_resume`] |
//! | `resumeUnchanged`, `resumeUnchanged_success` | [`ReflectiveRuntime::resume_unchanged`] |

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

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
}

/// One codec version: the program, the face that caused its mounting, its parent versions and the
/// receiver contacts that recruit it.
#[derive(Debug, PartialEq, Eq)]
pub struct CodecVersion<Program, Contact = ()> {
    pub id: CodecId,
    pub parents: BTreeSet<CodecId>,
    pub caused_by: FaceId,
    pub program: Program,
    pub contacts: BTreeSet<Contact>,
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

/// A requested reflection: the receiver asked, the continuation, and the codec and instruction at
/// which it was requested.
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
    UnknownFace(FaceId),
    UnknownCodec(CodecId),
    UnknownContinuation(ContinuationId),
    UnknownReflection(ReflectionId),
    ContinuationNotRunning(ContinuationId),
    ReflectionAlreadyReturned(ReflectionId),
    ReflectionDoesNotOwnContinuation(ReflectionId),
    InstructionExtent,
    /// A continuation was found without the environment it owns, or holding two.
    MalformedStanding,
}

impl fmt::Display for ReflectiveRuntimeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for ReflectiveRuntimeError {}

/// A codec step returns ownership of the environment it received, so the executor cannot retain a
/// hidden second environment.
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

/// A refused mount or revision returns the program it was handed.
#[derive(Debug, PartialEq, Eq)]
pub struct CodecRevisionRefusal<Program, Contact = ()> {
    pub error: ReflectiveRuntimeError,
    pub program: Program,
    pub parents: BTreeSet<CodecId>,
    pub contacts: BTreeSet<Contact>,
}

/// One continuing reflective body. It is not `Clone`: plurality is expressed through explicit
/// continuations and reflections, not by copying the whole.
#[derive(Debug, PartialEq, Eq)]
pub struct ReflectiveRuntime<Program, Environment, Face, Contact = ()> {
    faces: Vec<Face>,
    codecs: Vec<CodecVersion<Program, Contact>>,
    continuations: Vec<ReflectiveContinuation<Environment>>,
    reflections: Vec<ReflectionFrame>,
    recruitment: BTreeMap<Contact, BTreeSet<CodecId>>,
}

impl<Program, Environment, Face, Contact> Default
    for ReflectiveRuntime<Program, Environment, Face, Contact>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<Program, Environment, Face, Contact> ReflectiveRuntime<Program, Environment, Face, Contact> {
    pub const fn new() -> Self {
        Self {
            faces: Vec::new(),
            codecs: Vec::new(),
            continuations: Vec::new(),
            reflections: Vec::new(),
            recruitment: BTreeMap::new(),
        }
    }

    pub fn found_face(&mut self, face: Face) -> FaceId {
        self.faces.push(face);
        FaceId(self.faces.len() as u64 - 1)
    }

    pub fn face(&self, id: FaceId) -> Option<&Face> {
        self.faces.get(id.0 as usize)
    }

    pub fn codec(&self, id: CodecId) -> Option<&CodecVersion<Program, Contact>> {
        self.codecs.get(id.0 as usize)
    }

    pub fn codecs(&self) -> impl Iterator<Item = &CodecVersion<Program, Contact>> {
        self.codecs.iter()
    }

    pub fn continuation(&self, id: ContinuationId) -> Option<&ReflectiveContinuation<Environment>> {
        self.continuations.get(id.0 as usize)
    }

    pub fn reflection(&self, id: ReflectionId) -> Option<&ReflectionFrame> {
        self.reflections.get(id.0 as usize)
    }

    fn has_face(&self, id: FaceId) -> bool {
        (id.0 as usize) < self.faces.len()
    }

    fn has_codec(&self, id: CodecId) -> bool {
        (id.0 as usize) < self.codecs.len()
    }

    pub fn open_continuation(
        &mut self,
        codec: CodecId,
        environment: Environment,
    ) -> Result<ContinuationId, (ReflectiveRuntimeError, Environment)> {
        if !self.has_codec(codec) {
            return Err((ReflectiveRuntimeError::UnknownCodec(codec), environment));
        }
        let id = ContinuationId(self.continuations.len() as u64);
        self.continuations.push(ReflectiveContinuation {
            id,
            codec,
            next_instruction: 0,
            state: ContinuationState::Running,
            environment: Some(environment),
        });
        Ok(id)
    }

    /// **One crossing**: the continuation's codec receives the face at its next instruction. An
    /// advance moves the instruction on; a rest stops the continuation; a reflection records a
    /// frame at the current instruction (Lean `requestReflection_success`). A refused crossing
    /// restores the environment unchanged.
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
        let runtime = CodecCrossingError::Runtime;
        let face = self
            .faces
            .get(face_id.0 as usize)
            .ok_or(runtime(ReflectiveRuntimeError::UnknownFace(face_id)))?;
        let continuation = self
            .continuations
            .get_mut(continuation_id.0 as usize)
            .ok_or(runtime(ReflectiveRuntimeError::UnknownContinuation(
                continuation_id,
            )))?;
        if continuation.state != ContinuationState::Running {
            return Err(runtime(ReflectiveRuntimeError::ContinuationNotRunning(
                continuation_id,
            )));
        }
        let codec_id = continuation.codec;
        let instruction = continuation.next_instruction;
        let program = &self
            .codecs
            .get(codec_id.0 as usize)
            .ok_or(runtime(ReflectiveRuntimeError::UnknownCodec(codec_id)))?
            .program;
        let environment = continuation
            .environment
            .take()
            .ok_or(runtime(ReflectiveRuntimeError::MalformedStanding))?;
        let step = match executor.receive(program, instruction, environment, face) {
            Ok(step) => step,
            Err(obstruction) => {
                continuation.environment = Some(obstruction.environment);
                return Err(CodecCrossingError::Executor(obstruction.obstruction));
            }
        };
        let (environment, emission, next_instruction, state, reflection) = match step {
            CodecStep::Advance {
                environment,
                emission,
            } => {
                let Some(next) = instruction.checked_add(1) else {
                    continuation.environment = Some(environment);
                    return Err(CodecCrossingError::ReturnCouldNotCommit {
                        error: ReflectiveRuntimeError::InstructionExtent,
                        emission,
                    });
                };
                (
                    environment,
                    emission,
                    next,
                    ContinuationState::Running,
                    None,
                )
            }
            CodecStep::Rest {
                environment,
                emission,
            } => (
                environment,
                emission,
                instruction,
                ContinuationState::Rested,
                None,
            ),
            CodecStep::Reflect {
                environment,
                receiver,
                emission,
            } => {
                let id = ReflectionId(self.reflections.len() as u64);
                self.reflections.push(ReflectionFrame {
                    id,
                    receiver,
                    continuation: continuation_id,
                    codec: codec_id,
                    instruction,
                    state: ReflectionState::Open,
                });
                (
                    environment,
                    emission,
                    instruction,
                    ContinuationState::Reflected(id),
                    Some(id),
                )
            }
        };
        continuation.environment = Some(environment);
        continuation.next_instruction = next_instruction;
        continuation.state = state;
        Ok(CodecEmission {
            emission,
            reflection,
            next_instruction,
            state,
        })
    }

    /// **Unchanged resumption** (Lean `resumeUnchanged_success`): the reflected continuation runs
    /// again under the same codec at the same instruction.
    pub fn resume_unchanged(
        &mut self,
        reflection_id: ReflectionId,
    ) -> Result<(), ReflectiveRuntimeError> {
        let continuation_id = self.open_frame(reflection_id)?.continuation;
        let continuation = &mut self.continuations[continuation_id.0 as usize];
        continuation.state = ContinuationState::Running;
        self.reflections[reflection_id.0 as usize].state = ReflectionState::ResumedUnchanged;
        Ok(())
    }

    /// The open frame of a reflection whose continuation still waits on it.
    fn open_frame(
        &self,
        reflection_id: ReflectionId,
    ) -> Result<ReflectionFrame, ReflectiveRuntimeError> {
        let frame = *self
            .reflection(reflection_id)
            .ok_or(ReflectiveRuntimeError::UnknownReflection(reflection_id))?;
        if frame.state != ReflectionState::Open {
            return Err(ReflectiveRuntimeError::ReflectionAlreadyReturned(
                reflection_id,
            ));
        }
        let continuation = self.continuation(frame.continuation).ok_or(
            ReflectiveRuntimeError::UnknownContinuation(frame.continuation),
        )?;
        if continuation.state != ContinuationState::Reflected(reflection_id) {
            return Err(ReflectiveRuntimeError::ReflectionDoesNotOwnContinuation(
                reflection_id,
            ));
        }
        Ok(frame)
    }
}

impl<Program, Environment, Face, Contact: Ord + Clone>
    ReflectiveRuntime<Program, Environment, Face, Contact>
{
    /// Mount a codec caused by a face, with no parents and no contacts.
    pub fn mount_codec(
        &mut self,
        program: Program,
        caused_by: FaceId,
    ) -> Result<CodecId, CodecRevisionRefusal<Program, Contact>> {
        self.mount_codec_with_lineage(program, caused_by, BTreeSet::new(), BTreeSet::new())
    }

    /// Mount a codec with every co-present parent and receiver contact retained exactly.
    pub fn mount_codec_with_lineage(
        &mut self,
        program: Program,
        caused_by: FaceId,
        parents: BTreeSet<CodecId>,
        contacts: BTreeSet<Contact>,
    ) -> Result<CodecId, CodecRevisionRefusal<Program, Contact>> {
        let error = if !self.has_face(caused_by) {
            Some(ReflectiveRuntimeError::UnknownFace(caused_by))
        } else {
            parents
                .iter()
                .find(|parent| !self.has_codec(**parent))
                .map(|parent| ReflectiveRuntimeError::UnknownCodec(*parent))
        };
        if let Some(error) = error {
            return Err(CodecRevisionRefusal {
                error,
                program,
                parents,
                contacts,
            });
        }
        let id = CodecId(self.codecs.len() as u64);
        for contact in &contacts {
            self.recruitment
                .entry(contact.clone())
                .or_default()
                .insert(id);
        }
        self.codecs.push(CodecVersion {
            id,
            parents,
            caused_by,
            program,
            contacts,
        });
        Ok(id)
    }

    /// **Revise and resume** (Lean `reviseAndResume_success`,
    /// `revision_resumes_the_requested_boundary`): the revision is a new codec version whose
    /// parents include the reflected codec, and the same continuation runs under it from the
    /// instruction at which the reflection was requested.
    pub fn revise_and_resume(
        &mut self,
        reflection_id: ReflectionId,
        caused_by: FaceId,
        program: Program,
    ) -> Result<CodecId, CodecRevisionRefusal<Program, Contact>> {
        self.revise_and_resume_with_lineage(
            reflection_id,
            caused_by,
            program,
            BTreeSet::new(),
            BTreeSet::new(),
        )
    }

    /// [`Self::revise_and_resume`] with further co-present parents and receiver contacts.
    pub fn revise_and_resume_with_lineage(
        &mut self,
        reflection_id: ReflectionId,
        caused_by: FaceId,
        program: Program,
        mut parents: BTreeSet<CodecId>,
        contacts: BTreeSet<Contact>,
    ) -> Result<CodecId, CodecRevisionRefusal<Program, Contact>> {
        let frame = match self.open_frame(reflection_id) {
            Ok(frame) => frame,
            Err(error) => {
                return Err(CodecRevisionRefusal {
                    error,
                    program,
                    parents,
                    contacts,
                });
            }
        };
        parents.insert(frame.codec);
        let codec_id = self.mount_codec_with_lineage(program, caused_by, parents, contacts)?;
        let continuation = &mut self.continuations[frame.continuation.0 as usize];
        continuation.codec = codec_id;
        continuation.next_instruction = frame.instruction;
        continuation.state = ContinuationState::Running;
        self.reflections[reflection_id.0 as usize].state = ReflectionState::Revised(codec_id);
        Ok(codec_id)
    }

    /// The codec versions a receiver contact recruits.
    pub fn recruited_codecs(&self, contact: &Contact) -> Option<&BTreeSet<CodecId>> {
        self.recruitment.get(contact)
    }
}

#[cfg(test)]
mod tests;
