use super::*;

#[derive(Debug, PartialEq, Eq)]
enum Instruction {
    Add(i64),
    AskReflection,
    Rest,
}

#[derive(Debug, PartialEq, Eq)]
struct Program(Vec<Instruction>);

struct ExactExecutor;

impl ReflectiveCodecExecutor<Program, i64, i64> for ExactExecutor {
    type Emission = i64;
    type Obstruction = &'static str;

    fn receive(
        &mut self,
        program: &Program,
        instruction: u64,
        mut environment: i64,
        face: &i64,
    ) -> Result<CodecStep<i64, i64>, CodecObstruction<i64, Self::Obstruction>> {
        let Some(operation) = usize::try_from(instruction)
            .ok()
            .and_then(|at| program.0.get(at))
        else {
            return Err(CodecObstruction {
                environment,
                obstruction: "instruction horizon",
            });
        };
        match operation {
            Instruction::Add(offset) => {
                environment += face + offset;
                Ok(CodecStep::Advance {
                    environment,
                    emission: environment,
                })
            }
            Instruction::AskReflection => Ok(CodecStep::Reflect {
                environment,
                receiver: ReceiverId(7),
                emission: environment,
            }),
            Instruction::Rest => Ok(CodecStep::Rest {
                environment,
                emission: environment,
            }),
        }
    }
}

/// Lean `reviseAndResume_success`, `revision_resumes_the_requested_boundary`: the revision names
/// the reflected codec as a parent and governs the same continuation from the requested
/// instruction, keeping its environment.
#[test]
fn a_returned_revision_governs_the_same_continuation_from_the_requested_instruction() {
    let mut runtime: ReflectiveRuntime<Program, i64, i64> = ReflectiveRuntime::new();
    let origin = runtime.found_face(2);
    let correction = runtime.found_face(5);
    let codec = runtime
        .mount_codec(
            Program(vec![Instruction::Add(1), Instruction::AskReflection]),
            origin,
        )
        .unwrap();
    let continuation = runtime.open_continuation(codec, 0).unwrap();
    let mut executor = ExactExecutor;

    assert_eq!(
        runtime
            .receive_with(continuation, origin, &mut executor)
            .unwrap()
            .emission,
        3
    );
    let reflected = runtime
        .receive_with(continuation, origin, &mut executor)
        .unwrap();
    let reflection = reflected.reflection.unwrap();
    assert_eq!(runtime.reflection(reflection).unwrap().instruction, 1);
    assert_eq!(
        runtime.continuation(continuation).unwrap().state,
        ContinuationState::Reflected(reflection)
    );

    let revised = runtime
        .revise_and_resume(
            reflection,
            correction,
            Program(vec![
                Instruction::Add(1),
                Instruction::Add(10),
                Instruction::Rest,
            ]),
        )
        .unwrap();
    assert!(runtime.codec(revised).unwrap().parents.contains(&codec));
    let resumed = runtime.continuation(continuation).unwrap();
    assert_eq!((resumed.codec, resumed.next_instruction), (revised, 1));

    assert_eq!(
        runtime
            .receive_with(continuation, correction, &mut executor)
            .unwrap()
            .emission,
        18
    );
    let rested = runtime
        .receive_with(continuation, correction, &mut executor)
        .unwrap();
    assert_eq!(rested.state, ContinuationState::Rested);
    assert_eq!(
        runtime.continuation(continuation).unwrap().environment(),
        Some(&18)
    );
    assert_eq!(
        runtime
            .revise_and_resume(reflection, correction, Program(vec![]))
            .map_err(|r| r.error),
        Err(ReflectiveRuntimeError::ReflectionAlreadyReturned(
            reflection
        ))
    );
}

/// Lean `resumeUnchanged_success`: the continuation keeps its codec and instruction.
#[test]
fn an_unchanged_resumption_keeps_the_codec_and_the_instruction() {
    let mut runtime: ReflectiveRuntime<Program, i64, i64> = ReflectiveRuntime::new();
    let origin = runtime.found_face(2);
    let codec = runtime
        .mount_codec(
            Program(vec![Instruction::AskReflection, Instruction::Rest]),
            origin,
        )
        .unwrap();
    let continuation = runtime.open_continuation(codec, 4).unwrap();
    let reflection = runtime
        .receive_with(continuation, origin, &mut ExactExecutor)
        .unwrap()
        .reflection
        .unwrap();
    runtime.resume_unchanged(reflection).unwrap();
    let resumed = runtime.continuation(continuation).unwrap();
    assert_eq!(
        (resumed.codec, resumed.next_instruction, resumed.state),
        (codec, 0, ContinuationState::Running)
    );
    assert_eq!(resumed.environment(), Some(&4));
}

/// A plural revision keeps every co-present parent, and each receiver contact recruits it.
#[test]
fn plural_lineage_is_recruited_by_receiver_contact() {
    let mut runtime: ReflectiveRuntime<Program, i64, i64, String> = ReflectiveRuntime::new();
    let origin = runtime.found_face(2);
    let correction = runtime.found_face(5);
    let first = runtime
        .mount_codec_with_lineage(
            Program(vec![Instruction::Add(1), Instruction::AskReflection]),
            origin,
            BTreeSet::new(),
            BTreeSet::from(["arithmetic".to_owned()]),
        )
        .unwrap();
    let copresent = runtime
        .mount_codec(Program(vec![Instruction::Rest]), origin)
        .unwrap();
    let continuation = runtime.open_continuation(first, 0).unwrap();
    let mut executor = ExactExecutor;
    runtime
        .receive_with(continuation, origin, &mut executor)
        .unwrap();
    let reflection = runtime
        .receive_with(continuation, origin, &mut executor)
        .unwrap()
        .reflection
        .unwrap();
    let revised = runtime
        .revise_and_resume_with_lineage(
            reflection,
            correction,
            Program(vec![
                Instruction::Add(1),
                Instruction::Add(10),
                Instruction::Rest,
            ]),
            BTreeSet::from([copresent]),
            BTreeSet::from(["arithmetic".to_owned(), "corrected".to_owned()]),
        )
        .unwrap();
    let version = runtime.codec(revised).unwrap();
    assert_eq!(version.parents, BTreeSet::from([first, copresent]));
    assert_eq!(
        runtime.recruited_codecs(&"arithmetic".to_owned()),
        Some(&BTreeSet::from([first, revised]))
    );
    assert_eq!(
        runtime
            .receive_with(continuation, correction, &mut executor)
            .unwrap()
            .emission,
        18
    );
}
