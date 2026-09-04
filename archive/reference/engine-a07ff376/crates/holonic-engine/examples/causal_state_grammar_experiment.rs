use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs;
use std::path::PathBuf;

use holonic_engine::{
    CausalActionId, CausalActionSpec, CausalActionWord, CausalContinuationTestimony,
    CausalContinuationTrace, CausalObservableId, CausalObservableSpec, CausalStateGrammarEvent,
    CausalStateGrammarHistoryEntry, CausalStateGrammarLaw, CausalStateGrammarQuery,
    CausalStateGrammarSpec, CausalStateGrammarStanding, CausalStateObservation, CausalWorld,
    DynamicSeparationKind, EventId, OrganizationalConstraintId, OrganizationalConstraintSpec,
    OrganizationalEcologySpec, OrganizationalLineageId, OrganizationalQuery, OrganizationalSiteId,
    OrganizationalSiteSpec, OrganizationalValue, OrganizationalVariantId,
    OrganizationalVariantSpec, StateOrganizationalTestimony,
};
use num_bigint::BigInt;
use num_rational::BigRational;

const SCAFFOLD: CausalActionId = CausalActionId(1);
const RELEASE: CausalActionId = CausalActionId(2);
const DROP_DECOY: CausalActionId = CausalActionId(3);
const PULSE: CausalObservableId = CausalObservableId(1);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ChargePhase {
    Rest,
    Charged,
    Released,
    Emitted,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct HiddenChargeWorld {
    phase: ChargePhase,
    sparse: bool,
}

impl Default for HiddenChargeWorld {
    fn default() -> Self {
        Self {
            phase: ChargePhase::Rest,
            sparse: false,
        }
    }
}

impl HiddenChargeWorld {
    fn enact(&mut self, action: CausalActionId) {
        match action {
            SCAFFOLD => self.phase = ChargePhase::Charged,
            RELEASE => {
                self.phase = match self.phase {
                    ChargePhase::Rest => ChargePhase::Rest,
                    ChargePhase::Charged => ChargePhase::Released,
                    ChargePhase::Released => ChargePhase::Emitted,
                    ChargePhase::Emitted => ChargePhase::Rest,
                };
            }
            DROP_DECOY => self.sparse = true,
            _ => panic!("the bounded membrane received an undeclared action"),
        }
    }

    fn observation(&self) -> CausalStateObservation {
        let pulse = i64::from(self.phase == ChargePhase::Emitted);
        let mut population = (1..=6).map(OrganizationalSiteId).collect::<BTreeSet<_>>();
        if self.sparse {
            population.remove(&OrganizationalSiteId(4));
        }
        CausalStateObservation::new(BTreeMap::from([(PULSE, value(pulse))]), population)
    }

    fn trace(word: &CausalActionWord) -> CausalContinuationTrace {
        let mut world = Self::default();
        let mut observations = vec![world.observation()];
        for action in &word.actions {
            world.enact(*action);
            observations.push(world.observation());
        }
        CausalContinuationTrace::new(observations)
    }

    fn after(word: &CausalActionWord) -> Self {
        let mut world = Self::default();
        for action in &word.actions {
            world.enact(*action);
        }
        world
    }
}

fn value(integer: i64) -> OrganizationalValue {
    BigRational::from_integer(BigInt::from(integer))
}

fn variant(id: u64, name: &str, lineage: u64) -> OrganizationalVariantSpec {
    OrganizationalVariantSpec {
        id: OrganizationalVariantId(id),
        name: name.to_owned(),
        lineage: OrganizationalLineageId(lineage),
    }
}

fn site(
    id: u64,
    name: &str,
    variants: Vec<OrganizationalVariantSpec>,
    reference_variant: Option<u64>,
) -> OrganizationalSiteSpec {
    OrganizationalSiteSpec {
        id: OrganizationalSiteId(id),
        name: name.to_owned(),
        variants,
        reference_variant: reference_variant.map(OrganizationalVariantId),
    }
}

fn constraint(id: u64, name: &str, receiver: u64) -> OrganizationalConstraintSpec {
    OrganizationalConstraintSpec {
        id: OrganizationalConstraintId(id),
        name: name.to_owned(),
        receiver: OrganizationalSiteId(receiver),
    }
}

fn experiment_spec() -> CausalStateGrammarSpec {
    let organizational_ecology = OrganizationalEcologySpec::new(
        vec![
            site(
                1,
                "left resource relay",
                vec![variant(11, "left", 101)],
                Some(11),
            ),
            site(
                2,
                "right resource relay",
                vec![
                    variant(21, "right lineage", 201),
                    variant(22, "homologous repair", 202),
                ],
                Some(21),
            ),
            site(
                3,
                "exterior control",
                vec![variant(31, "control", 301)],
                Some(31),
            ),
            site(
                4,
                "co-occurring decoy",
                vec![variant(41, "decoy", 401)],
                Some(41),
            ),
            site(
                5,
                "downstream consumer",
                vec![variant(51, "consumer", 501)],
                Some(51),
            ),
            site(
                6,
                "dormant scaffold",
                vec![variant(61, "scaffold", 601)],
                None,
            ),
        ],
        vec![
            constraint(1, "left stored resource", 1),
            constraint(2, "right stored resource", 2),
            constraint(3, "control standing", 3),
            constraint(4, "decoy standing", 4),
            constraint(5, "consumer standing", 5),
            constraint(6, "scaffold standing", 6),
        ],
    )
    .expect("the bounded organizational ecology is valid");

    CausalStateGrammarSpec::new(
        vec![
            CausalActionSpec {
                id: SCAFFOLD,
                name: "transient scaffold charge".to_owned(),
            },
            CausalActionSpec {
                id: RELEASE,
                name: "release stored charge".to_owned(),
            },
            CausalActionSpec {
                id: DROP_DECOY,
                name: "remove decoy population".to_owned(),
            },
        ],
        vec![CausalObservableSpec {
            id: PULSE,
            name: "visible release pulse".to_owned(),
        }],
        4,
        4,
        4,
        organizational_ecology,
    )
    .expect("the bounded causal-state grammar specification is valid")
}

fn organizational_return(
    world: HiddenChargeWorld,
    query: &OrganizationalQuery,
) -> BTreeMap<OrganizationalConstraintId, OrganizationalValue> {
    let active = |site| {
        i64::from(
            query
                .configuration
                .selected_variant(OrganizationalSiteId(site))
                .is_some(),
        )
    };
    let a = active(1);
    let b = active(2);
    let control = active(3);
    let decoy = active(4);
    let consumer = active(5);
    let scaffold = active(6);
    let coefficient = if world.phase == ChargePhase::Released {
        3
    } else {
        2
    };
    let transfer = coefficient * a * b * control;
    BTreeMap::from([
        (
            OrganizationalConstraintId(1),
            value(a + transfer + 5 * a * scaffold),
        ),
        (OrganizationalConstraintId(2), value(b - transfer)),
        (OrganizationalConstraintId(3), value(control)),
        (
            OrganizationalConstraintId(4),
            value(if world.sparse { 0 } else { 7 * decoy }),
        ),
        (
            OrganizationalConstraintId(5),
            value(consumer + 3 * a * consumer),
        ),
        (OrganizationalConstraintId(6), value(scaffold)),
    ])
}

fn word_text(word: &CausalActionWord) -> String {
    if word.actions.is_empty() {
        return "epsilon".to_owned();
    }
    word.actions
        .iter()
        .map(|action| action.0.to_string())
        .collect::<Vec<_>>()
        .join(",")
}

fn trace_text(trace: &CausalContinuationTrace) -> String {
    trace
        .observations
        .iter()
        .map(|observation| {
            let pulse = observation
                .values
                .get(&PULSE)
                .expect("the pulse receiver is complete");
            format!("{pulse}@{}", observation.population.len())
        })
        .collect::<Vec<_>>()
        .join(">")
}

fn main() {
    let standing = CausalStateGrammarStanding::new(experiment_spec()).expect("standing forms");
    let mut machine = CausalWorld::new(CausalStateGrammarLaw, standing);
    let mut next_event = 1_u64;
    let mut guard = 0_usize;
    while let Some(query) = machine.standing().next_query().cloned() {
        let event = match query {
            CausalStateGrammarQuery::Continuation(query) => {
                CausalStateGrammarEvent::ReturnContinuation(CausalContinuationTestimony {
                    event: EventId(next_event),
                    receiver: OrganizationalLineageId(900),
                    trace: HiddenChargeWorld::trace(&query.word),
                    query,
                })
            }
            CausalStateGrammarQuery::StateOrganization(query) => {
                let hidden = HiddenChargeWorld::after(&query.access_word);
                CausalStateGrammarEvent::ReturnStateOrganization(StateOrganizationalTestimony {
                    event: EventId(next_event),
                    receiver: OrganizationalLineageId(900),
                    access_trace: HiddenChargeWorld::trace(&query.access_word),
                    values: organizational_return(hidden, &query.organizational_query),
                    query,
                })
            }
        };
        machine
            .receive(&event)
            .expect("the exact return is admitted");
        next_event += 1;
        guard += 1;
        assert!(guard < 5_000, "the bounded experiment must reach rest");
    }

    let certificate = machine
        .standing()
        .certificate()
        .expect("the dynamic grammar certifies");
    let mut separation_counts = BTreeMap::<DynamicSeparationKind, u64>::new();
    for separation in &certificate.separations {
        for kind in &separation.kinds {
            *separation_counts.entry(*kind).or_default() += 1;
        }
    }

    let mut tsv = String::from("kind\tevent_or_state\tword_or_action\treceipt\n");
    for entry in machine.standing().history() {
        match entry {
            CausalStateGrammarHistoryEntry::SourceContinuation(testimony) => {
                writeln!(
                    tsv,
                    "continuation\t{}\t{}\t{}",
                    testimony.event.0,
                    word_text(&testimony.query.word),
                    trace_text(&testimony.trace)
                )
                .expect("TSV write");
            }
            CausalStateGrammarHistoryEntry::EmanatedPrediction(prediction) => {
                writeln!(
                    tsv,
                    "prediction\t{}\t{}\t{}",
                    prediction.query.word.len(),
                    word_text(&prediction.query.word),
                    trace_text(&prediction.predicted_trace)
                )
                .expect("TSV write");
            }
            CausalStateGrammarHistoryEntry::SourceStateOrganization(testimony) => {
                let values = testimony
                    .values
                    .iter()
                    .map(|(constraint, value)| format!("{}={value}", constraint.0))
                    .collect::<Vec<_>>()
                    .join(",");
                writeln!(
                    tsv,
                    "organization\t{}\t{}\t{}",
                    testimony.event.0, testimony.query.state.0, values
                )
                .expect("TSV write");
            }
        }
    }

    let output_directory = PathBuf::from("target/holonic-engine");
    fs::create_dir_all(&output_directory).expect("trace directory forms");
    let trace_path = output_directory.join("causal_state_grammar_trace.tsv");
    fs::write(&trace_path, tsv).expect("exact trace writes");

    println!("events={}", next_event - 1);
    println!("states={}", certificate.causal_model.states.len());
    println!("transitions={}", certificate.causal_model.transitions.len());
    println!("bounded_words={}", certificate.graded_words);
    println!("predictions={}", certificate.predictions_graded);
    println!(
        "prediction_obstructions={}",
        certificate.prediction_obstructions.len()
    );
    println!(
        "organizational_fibers={}",
        certificate.organizational_fibers.len()
    );
    println!("transports={}", certificate.transports.len());
    println!("cycles={}", certificate.cycles.len());
    for (kind, count) in separation_counts {
        println!("separation_{kind:?}={count}");
    }
    for state in &certificate.causal_model.states {
        println!(
            "state_{}=access:{} pulse:{} population:{}",
            state.id.0,
            word_text(&state.representative),
            state.observation.values.get(&PULSE).expect("pulse exists"),
            state.observation.population.len()
        );
    }
    println!("trace={}", trace_path.display());
}
