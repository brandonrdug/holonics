//! The agentic answer path conducts through a caller-mounted carrier.
//!
//! `AgenticLanguageEcology::condition_with_executor` has existed since the seam was first extended:
//! a caller mounting a card could condition the language body through it. **The answer path could
//! not.** Every materialization of a selected answer current ran `into_materialized_return`, which
//! builds a private `ParallelHostLiveCurrentExecutor` out of a worker count, so a caller holding a
//! mounted carrier had no expressible way to hand it to generation. The carrier was not declined;
//! past conditioning it was unreachable.
//!
//! This driver measures the seam after the join. It is built so that a *fake* twin — one which
//! takes the executor argument and quietly builds its own host pool anyway — fails it.
//!
//! Both agentic answer paths are exercised, because they are different edges of the loop:
//!
//! - **the world-return path** — an ungrounded question emits a deed, the world returns sections,
//!   and the answer is materialized inside `receive_world_return_with_executor`;
//! - **the locally-grounded path** — a later question reaches the founded episode and answers
//!   without a deed, materialized inside `receive_question_with_executor`.
//!
//! Three frames, in order of how hard they are to fake:
//!
//! 1. **The counting frame.** One `CountingHostExecutor` forwards every request to exactly the host
//!    carrier the private path would have built, and counts. Equality of the whole returned
//!    `AgenticLanguageAnswer` proves the twin computes the same thing; the count proves the
//!    supplied executor is the one that computed it. A fake twin returns the same answer with a
//!    count of zero.
//!
//! 2. **The refusal frame.** One `RefusingExecutor` refuses every enactment. If an answer path
//!    genuinely crosses the supplied executor, that answer *must* fail. A fake twin never consults
//!    the argument, so it answers happily and this control fails. This is the control that cannot
//!    pass by accident: no arrangement of counters or receipts makes a refused carrier produce an
//!    answer.
//!
//! 3. **The phase split.** The counter is read between occurrences, so the driver states *where on
//!    the loop* the carrier is crossed rather than only that it was.
//!
//! What this driver does NOT claim: any speedup, any card, or that the generation front is enacted
//! wide. The executor here is a host pool wearing a counter, and the returned answer is required to
//! be bit-identical to the private path's. This is a precondition being made expressible, not a
//! performance change.

use body::num::Cog;
use holonic_structure::CausalMembrane;
use life::agentic_language::{
    AgenticLanguageAnswer, AgenticLanguageCapability, AgenticLanguageConsequence,
    AgenticLanguageEcology, AgenticLanguageError, AgenticLanguageOccurrence,
    AgenticLanguageQuestion, AgenticLanguageSpec, AgenticLanguageTrajectory,
    AgenticLanguageWorldReturn,
};
use life::morphological_language::MorphologicalLanguagePassage;
use soma_abi::active::ActionCurrent;
use soma_membrane::{
    CurrentExecutionRequest, DirectedExecutionRequest, ExecutedContemporaryEvent, LiveCurrentError,
    LiveCurrentExecutor, ParallelHostLiveCurrentExecutor, RegionalExecutionRequest,
    SparseStandingSurface,
};

/// One caller-retained executor which counts the events it was asked to realize and changes no
/// result: every request is forwarded to the same host carrier the private path would have built.
struct CountingHostExecutor {
    host: ParallelHostLiveCurrentExecutor,
    enactments: usize,
    currents: usize,
}

impl CountingHostExecutor {
    const fn new(worker_threads: usize) -> Self {
        Self {
            host: ParallelHostLiveCurrentExecutor::new(worker_threads),
            enactments: 0,
            currents: 0,
        }
    }
}

impl LiveCurrentExecutor for CountingHostExecutor {
    fn enact(
        &mut self,
        physical_revision: u64,
        standing: &SparseStandingSurface,
        currents: &[CurrentExecutionRequest<'_>],
        relations: &[DirectedExecutionRequest],
        regional: &[RegionalExecutionRequest<'_>],
    ) -> Result<ExecutedContemporaryEvent, LiveCurrentError> {
        self.enactments += 1;
        self.currents += currents.len();
        self.host
            .enact(physical_revision, standing, currents, relations, regional)
    }
}

/// One caller-retained executor which refuses every enactment. Nothing downstream can produce an
/// answer through it, so an answer returned while it is mounted was produced by a carrier the
/// caller did not supply.
struct RefusingExecutor {
    consulted: usize,
}

impl LiveCurrentExecutor for RefusingExecutor {
    fn enact(
        &mut self,
        _physical_revision: u64,
        _standing: &SparseStandingSurface,
        _currents: &[CurrentExecutionRequest<'_>],
        _relations: &[DirectedExecutionRequest],
        _regional: &[RegionalExecutionRequest<'_>],
    ) -> Result<ExecutedContemporaryEvent, LiveCurrentError> {
        self.consulted += 1;
        Err(LiveCurrentError::PhysicalSettlement)
    }
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).unwrap()
}

const WORKER_THREADS: usize = 2;

const DEED_QUESTION: &str = "What did the reflection correction establish?";
const GROUNDED_QUESTION: &str = "What does the returned current change in the next passage?";
const OBSERVATION: &str = "The reflection correction makes the returned current change the local morphology used by the next passage.";

fn agent() -> AgenticLanguageEcology {
    let capabilities = vec![AgenticLanguageCapability::new("repository-search", 70)];
    let trajectories = vec![
        AgenticLanguageTrajectory::new(
            "suffix",
            1,
            "What did the suffix correction establish?",
            "repository-search",
            vec![MorphologicalLanguagePassage::new(
                "suffix-observation",
                "suffix-record",
                11,
                "The suffix current advances through returned events.",
            )],
            "The correction made the returned event advance the suffix current used by the next emanation.",
        ),
        AgenticLanguageTrajectory::new(
            "phase",
            2,
            "What did the phase correction establish?",
            "repository-search",
            vec![MorphologicalLanguagePassage::new(
                "phase-observation",
                "phase-record",
                12,
                "The phase receiver retains quotient and causal carry.",
            )],
            "The correction retained phase quotient and carry instead of one scalar cell.",
        ),
    ];
    AgenticLanguageEcology::condition(
        &[MorphologicalLanguagePassage::new(
            "language-form",
            "language-form",
            3,
            "A correction changes the current used by a later passage.",
        )],
        &capabilities,
        &trajectories,
        AgenticLanguageSpec::default(),
        action(),
        WORKER_THREADS,
    )
    .unwrap()
}

fn world_return(deed: String) -> AgenticLanguageWorldReturn {
    AgenticLanguageWorldReturn::new(
        deed,
        vec![MorphologicalLanguagePassage::new(
            "reflection-observation",
            "reflection-record",
            91,
            OBSERVATION,
        )],
    )
}

/// The whole cycle through the fixed `CausalMembrane` mouth: question -> deed -> world return ->
/// answer, then one grounded later question. This is the pre-join path every caller had.
fn cycle_through_private_pool(
    ecology: &mut AgenticLanguageEcology,
) -> (AgenticLanguageAnswer, AgenticLanguageAnswer) {
    let question = AgenticLanguageQuestion::new("reflection-question", 90, DEED_QUESTION);
    let deed = match ecology
        .receive_occurrence(AgenticLanguageOccurrence::Question(&question))
        .unwrap()
    {
        AgenticLanguageConsequence::Deed(deed) => deed,
        other => panic!("the unseen question must emit a deed, received {other:?}"),
    };
    let returned = match ecology
        .receive_occurrence(AgenticLanguageOccurrence::WorldReturn(&world_return(
            deed.identity,
        )))
        .unwrap()
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        other => panic!("the world return must answer, received {other:?}"),
    };
    let later = AgenticLanguageQuestion::new("later-question", 90, GROUNDED_QUESTION);
    let grounded = match ecology
        .receive_occurrence(AgenticLanguageOccurrence::Question(&later))
        .unwrap()
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        other => panic!("the grounded follow-up must answer, received {other:?}"),
    };
    (returned, grounded)
}

fn main() {
    println!("THE ANSWER CROSSES THE MOUNTED CARRIER");
    println!("======================================");
    println!();

    // -------------------------------------------------------------------------------------------
    // FRAME 0 - the private host pool. What every caller had before the join.
    // -------------------------------------------------------------------------------------------
    let mut private_body = agent();
    let (private_world_answer, private_grounded_answer) =
        cycle_through_private_pool(&mut private_body);

    println!("FRAME 0 - private host pool (the pre-join path)");
    println!("  world-return answer   {:?}", private_world_answer.text);
    println!("  grounded answer       {:?}", private_grounded_answer.text);
    println!(
        "  episode origin census {:?}",
        private_body.episode_origin_census()
    );
    println!();

    // -------------------------------------------------------------------------------------------
    // FRAME 1 - one supplied executor, counted, read between occurrences.
    // -------------------------------------------------------------------------------------------
    let mut counted_body = agent();
    let mut counting = CountingHostExecutor::new(WORKER_THREADS);
    let after_conditioning = counting.enactments;

    let question = AgenticLanguageQuestion::new("reflection-question", 90, DEED_QUESTION);
    let counted_deed = match counted_body
        .receive_occurrence_with_executor(
            AgenticLanguageOccurrence::Question(&question),
            &mut counting,
        )
        .unwrap()
    {
        AgenticLanguageConsequence::Deed(deed) => deed,
        other => panic!("the unseen question must emit a deed, received {other:?}"),
    };
    let after_deed = counting.enactments;

    let counted_world_answer = match counted_body
        .receive_occurrence_with_executor(
            AgenticLanguageOccurrence::WorldReturn(&world_return(counted_deed.identity)),
            &mut counting,
        )
        .unwrap()
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        other => panic!("the world return must answer, received {other:?}"),
    };
    let after_world_return = counting.enactments;

    let later = AgenticLanguageQuestion::new("later-question", 90, GROUNDED_QUESTION);
    let counted_grounded_answer = match counted_body
        .receive_occurrence_with_executor(
            AgenticLanguageOccurrence::Question(&later),
            &mut counting,
        )
        .unwrap()
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        other => panic!("the grounded follow-up must answer, received {other:?}"),
    };
    let after_grounded = counting.enactments;

    println!("FRAME 1 - one supplied executor, counted");
    println!("  world-return answer   {:?}", counted_world_answer.text);
    println!("  grounded answer       {:?}", counted_grounded_answer.text);
    println!(
        "  episode origin census {:?}",
        counted_body.episode_origin_census()
    );
    println!(
        "  currents presented to the supplied carrier  {}",
        counting.currents
    );
    println!();

    println!("THE PHASE SPLIT - where on the loop the carrier is crossed");
    println!("  occurrence                       enactments on the supplied carrier");
    println!("  ------------------------------   -----------------------------------");
    println!(
        "  (conditioning, before any ask)   {after_conditioning}",
        after_conditioning = after_conditioning
    );
    println!(
        "  question -> deed                 {}",
        after_deed - after_conditioning
    );
    println!(
        "  world return -> answer           {}",
        after_world_return - after_deed
    );
    println!(
        "  grounded question -> answer      {}",
        after_grounded - after_world_return
    );
    println!("  total                            {after_grounded}");
    println!();

    // -------------------------------------------------------------------------------------------
    // FRAME 2 - the refusal, on BOTH answer paths. The control that cannot pass by accident.
    // -------------------------------------------------------------------------------------------
    let mut refused_world_body = agent();
    let mut refusing_world = RefusingExecutor { consulted: 0 };
    let question = AgenticLanguageQuestion::new("reflection-question", 90, DEED_QUESTION);
    let refused_deed = match refused_world_body
        .receive_occurrence_with_executor(
            AgenticLanguageOccurrence::Question(&question),
            &mut refusing_world,
        )
        .unwrap()
    {
        AgenticLanguageConsequence::Deed(deed) => deed,
        other => panic!("the unseen question must emit a deed, received {other:?}"),
    };
    let refused_world = refused_world_body.receive_occurrence_with_executor(
        AgenticLanguageOccurrence::WorldReturn(&world_return(refused_deed.identity)),
        &mut refusing_world,
    );

    // The grounded path needs a body which already received the world return, so that body is
    // driven to that point on a working carrier and only the final question is refused.
    let mut refused_grounded_body = agent();
    let mut working = CountingHostExecutor::new(WORKER_THREADS);
    let question = AgenticLanguageQuestion::new("reflection-question", 90, DEED_QUESTION);
    let grounded_deed = match refused_grounded_body
        .receive_occurrence_with_executor(
            AgenticLanguageOccurrence::Question(&question),
            &mut working,
        )
        .unwrap()
    {
        AgenticLanguageConsequence::Deed(deed) => deed,
        other => panic!("the unseen question must emit a deed, received {other:?}"),
    };
    refused_grounded_body
        .receive_occurrence_with_executor(
            AgenticLanguageOccurrence::WorldReturn(&world_return(grounded_deed.identity)),
            &mut working,
        )
        .unwrap();
    let mut refusing_grounded = RefusingExecutor { consulted: 0 };
    let later = AgenticLanguageQuestion::new("later-question", 90, GROUNDED_QUESTION);
    let refused_grounded = refused_grounded_body.receive_occurrence_with_executor(
        AgenticLanguageOccurrence::Question(&later),
        &mut refusing_grounded,
    );

    println!("FRAME 2 - the refusing carrier");
    println!("  world-return path returned  {refused_world:?}");
    println!("    refusal consulted         {}", refusing_world.consulted);
    println!("  grounded path returned      {refused_grounded:?}");
    println!(
        "    refusal consulted         {}",
        refusing_grounded.consulted
    );
    println!();

    // -------------------------------------------------------------------------------------------
    // CONTROLS
    // -------------------------------------------------------------------------------------------
    println!("CONTROLS");
    println!();

    let same_world = private_world_answer == counted_world_answer;
    report(
        same_world,
        "the supplied-executor world-return answer equals the private-host answer",
        "the twin computed a different answer -- threading the carrier changed semantics, not only\n       the carrier. This compares the WHOLE AgenticLanguageAnswer: question, generated body,\n       tokens, retained alternatives, reflection receipt, codec versions and relational thoughts.",
    );

    let same_grounded = private_grounded_answer == counted_grounded_answer;
    report(
        same_grounded,
        "the supplied-executor grounded answer equals the private-host answer",
        "the locally-grounded answer path diverged under a supplied carrier.",
    );

    let world_crossing = after_world_return - after_deed;
    report(
        world_crossing > 0,
        &format!("the world-return answer crossed the supplied carrier ({world_crossing} enactments)"),
        "receive_world_return_with_executor built a private host pool and ignored its argument.\n       A FAKE TWIN RETURNS THE SAME ANSWER WITH THIS COUNT AT ZERO -- which is exactly why the\n       equality controls above are not sufficient on their own.",
    );

    let grounded_crossing = after_grounded - after_world_return;
    report(
        grounded_crossing > 0,
        &format!(
            "the grounded answer crossed the supplied carrier ({grounded_crossing} enactments)"
        ),
        "receive_question_with_executor's local answer path built its own pool.",
    );

    let deed_crossing = after_deed - after_conditioning;
    report(
        deed_crossing == 0,
        &format!("a question which emits a deed crosses NO Swing event ({deed_crossing} enactments)"),
        "the deed path reached a physical current. This is a claim about the machine, not about the\n       join: if it ever becomes nonzero, deed emission acquired a Swing event and this driver is\n       the thing that would notice.",
    );

    let world_refused = matches!(refused_world, Err(AgenticLanguageError::Morphology(_)));
    report(
        world_refused,
        "a refusing carrier makes the world-return answer path FAIL",
        "the answer was produced by some carrier other than the one supplied. THIS CONTROL CANNOT\n       PASS BY ACCIDENT: a refused carrier that still yields an answer proves the argument is\n       decorative.",
    );

    let grounded_refused = matches!(refused_grounded, Err(AgenticLanguageError::Morphology(_)));
    report(
        grounded_refused,
        "a refusing carrier makes the grounded answer path FAIL",
        "the locally-grounded answer was produced by a carrier the caller did not supply.",
    );

    report(
        refusing_world.consulted > 0 && refusing_grounded.consulted > 0,
        &format!(
            "both refusals were actually consulted ({} and {})",
            refusing_world.consulted, refusing_grounded.consulted
        ),
        "a path errored before ever reaching the carrier, which would make the two refusal controls\n       above VACUOUS -- they would pass on an error that has nothing to do with the carrier.",
    );

    let all = same_world
        && same_grounded
        && world_crossing > 0
        && grounded_crossing > 0
        && deed_crossing == 0
        && world_refused
        && grounded_refused
        && refusing_world.consulted > 0
        && refusing_grounded.consulted > 0;
    println!("ALL CONTROLS HELD: {all}");

    assert!(
        same_world,
        "the world-return twin must return what the private path did"
    );
    assert!(
        same_grounded,
        "the grounded twin must return what the private path did"
    );
    assert!(
        world_crossing > 0,
        "the world-return answer must cross the supplied carrier"
    );
    assert!(
        grounded_crossing > 0,
        "the grounded answer must cross the supplied carrier"
    );
    assert!(
        deed_crossing == 0,
        "deed emission must cross no Swing event"
    );
    assert!(
        world_refused,
        "a refusing carrier must refuse the world-return answer"
    );
    assert!(
        grounded_refused,
        "a refusing carrier must refuse the grounded answer"
    );
    assert!(
        refusing_world.consulted > 0 && refusing_grounded.consulted > 0,
        "the refusal controls are vacuous unless the carrier was reached"
    );
}

fn report(held: bool, claim: &str, would_fail_if: &str) {
    println!("  [{}] {claim}", if held { "HELD" } else { "FAILED" });
    println!("       would fail if: {would_fail_if}");
    println!();
}
