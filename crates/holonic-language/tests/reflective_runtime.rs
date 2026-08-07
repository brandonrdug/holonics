use holonic_language::{
    CodecObstruction, CodecStep, ContinuationState, ReceiverId, ReflectiveCodecExecutor,
    ReflectiveRuntime,
};
use holonic_structure::LocalSet;

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

#[test]
fn returned_codec_revision_governs_the_same_resumed_continuation() {
    let mut runtime = ReflectiveRuntime::new();
    let origin = runtime.found_face(2).unwrap();
    let correction = runtime.found_face(5).unwrap();
    let codec = runtime
        .mount_codec(
            Program(vec![Instruction::Add(1), Instruction::AskReflection]),
            origin,
        )
        .unwrap();
    let continuation = runtime.open_continuation(codec, 0).unwrap();
    let mut executor = ExactExecutor;

    let first = runtime
        .receive_with(continuation, origin, &mut executor)
        .unwrap();
    assert_eq!(first.emission, 3);
    let reflected = runtime
        .receive_with(continuation, origin, &mut executor)
        .unwrap();
    let reflection = reflected.reflection.unwrap();
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
    assert_eq!(runtime.continuation(continuation).unwrap().codec, revised);

    let after_revision = runtime
        .receive_with(continuation, correction, &mut executor)
        .unwrap();
    assert_eq!(after_revision.emission, 18);
    let rested = runtime
        .receive_with(continuation, correction, &mut executor)
        .unwrap();
    assert_eq!(rested.state, ContinuationState::Rested);
    assert_eq!(
        runtime.continuation(continuation).unwrap().environment(),
        Some(&18)
    );
}

#[test]
fn plural_lineage_recruits_by_receiver_contact_and_remounts_without_replay() {
    let mut runtime: ReflectiveRuntime<Program, i64, i64, String> =
        ReflectiveRuntime::new_with_contacts();
    let origin = runtime.found_face(2).unwrap();
    let correction = runtime.found_face(5).unwrap();
    let first = runtime
        .mount_codec_with_lineage(
            Program(vec![Instruction::Add(1), Instruction::AskReflection]),
            origin,
            LocalSet::new(),
            LocalSet::from(["arithmetic".to_owned()]),
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
            LocalSet::from([copresent]),
            LocalSet::from(["arithmetic".to_owned(), "corrected".to_owned()]),
        )
        .unwrap();
    let version = runtime.codec(revised).unwrap();
    assert!(version.parents.contains(&first));
    assert!(version.parents.contains(&copresent));
    assert!(
        runtime
            .recruited_codecs(&"corrected".to_owned())
            .unwrap()
            .contains(&revised)
    );

    let rest = runtime.into_rest();
    assert_eq!(rest.receipt().codecs, 3);
    let mut remounted = ReflectiveRuntime::from_rest(rest).unwrap();
    assert_eq!(
        remounted
            .receive_with(continuation, correction, &mut executor)
            .unwrap()
            .emission,
        18
    );
}
