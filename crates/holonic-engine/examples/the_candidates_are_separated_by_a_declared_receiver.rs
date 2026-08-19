//! **Phoenix station five, its dissection half: the open candidate compositions are separated by a
//! declared receiver family, not by anyone reading the output.**
//!
//! Plan: `blueprint/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md`.
//! Derivation:
//! `research/records/2026-08-18_THE_HOLON_IS_THE_OPERATION_COMPLEX_THE_FOREIGN_MAP_IS_A_PORTED_WORD_AND_THE_CARD_CARRIES_ITS_FRONTS.md`
//! §§7, 12.5.
//!
//! # What this settles and what it cannot
//!
//! Station one returned four bindings the admitted testimony does not decide. The plan forbids
//! settling them by inspecting a plausible surface, and it is right to: a reading that looks like
//! language is a receiver's coarse face and cannot adjudicate a transport.
//!
//! What *can* be settled here is which of those questions are **real**. Two candidates that no
//! declared receiver separates are one composition for that family, and the question between them
//! is moot at this aperture. Two that separate are genuinely different transports, and the
//! **shortest history that separates them** is what a later station must acquire source evidence
//! about. `receiver_exact_compression` returns exactly that, and nothing here chooses.
//!
//! # Matched siblings
//!
//! Each sibling differs from the base in **exactly one relation**, so a separation is attributable.
//!
//! # The anti-vacuity control, and the obvious reading of it is wrong
//!
//! Withdrawing one receiver and finding the partition unmoved does **not** show that receiver is
//! decorative — it shows it is **redundant with the others**. Measured here: all thirty-two are
//! individually redundant, and the family still does work. The two honest controls are withdrawing
//! the whole family, which must coarsen the partition, and finding a **minimal subfamily** that
//! returns the same one. Both run below.
//!
//! ```text
//! cargo run --release -q -p holonic-engine \
//!   --example the_candidates_are_separated_by_a_declared_receiver -- /home/b/models/gemma-4-E4B-it
//! ```

use std::collections::BTreeMap;
use std::fs::File;

use holonic_engine::category::BoundaryId;
use holonic_engine::causal::EventId;
use holonic_engine::embedding_fiber::{align_bfloat16, ResidentReadout};
use holonic_engine::exact_value::ieee754::{decode_bfloat16_bits, round_into_bfloat16};
use holonic_engine::exact_value::{AlgebraicRoot, CertifiedSeries, ExactInterval};
use holonic_engine::foreign_map::{manifest_safetensors, ForeignContainer};
use holonic_engine::interaction::OccurrencePort;
use holonic_engine::ported_operation::{
    realize, OperationSpecies, PortedCarrier, PortedOperationComplex, PortedOperationKind,
    PortedProgram, SourceTestimony,
};
use holonic_engine::receiver_exact_compression::{
    compress, AblatedSystem, InputId, ItemId, Observation, ObservedSystem, ReceiverId,
};
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use relational_geometry::Rat;

const SITE: usize = 0;
const SYMBOLS: &str = "model.language_model.embed_tokens.weight";
const CAUSED: [usize; 3] = [818, 18_740, 563];

fn named(suffix: &str) -> String {
    format!("model.language_model.layers.{SITE}.{suffix}")
}

/// One member of the open candidate populations. A sibling moves **one** relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Candidate {
    name: &'static str,
    question: &'static str,
    gain_carries_unit: bool,
    pairs_halves: bool,
    scale_contact: bool,
}

const BASE: Candidate = Candidate {
    name: "base",
    question: "-",
    gain_carries_unit: false,
    pairs_halves: true,
    scale_contact: true,
};

const SIBLINGS: [Candidate; 3] = [
    Candidate {
        name: "the gain carries a unit",
        question: "how is a stored rebase gain read?",
        gain_carries_unit: true,
        ..BASE
    },
    Candidate {
        name: "the chronology pairs adjacent coordinates",
        question: "which two coordinates does the chronology pair?",
        pairs_halves: false,
        ..BASE
    },
    Candidate {
        name: "the contact carries no scale",
        question: "does the contact carry a scale?",
        scale_contact: false,
        ..BASE
    },
];

// ---------------------------------------------------------------------------------------------

struct ResidentSourceCarrier<'chart> {
    chart: &'chart ResidentReadout,
    container: ForeignContainer,
    file: File,
    below_the_frame: usize,
}

/// Read off the carrier and the diagram: a signed word holds sixty-three magnitude octaves, a
/// `BF16` significand eight of them, and the widest contraction here is `2560` wide, so
/// `2(reach + 8) + 12 + 1 <= 128` gives `reach <= 49`.
const CARRIER_REACH: i32 = 46;

impl PortedCarrier for ResidentSourceCarrier<'_> {
    fn contract(&mut self, population: &str, standing: &[Rat]) -> Result<Vec<Rat>, String> {
        let tensor = self
            .container
            .tensor(population)
            .map_err(|error| error.to_string())?
            .clone();
        let mut words = Vec::with_capacity(standing.len());
        for value in standing {
            let (word, residual) = round_into_bfloat16(value).map_err(|e| format!("{e:?}"))?;
            if !residual.is_zero() {
                return Err("a contraction was handed an ungrained standing".to_owned());
            }
            words.push(word);
        }
        let query = align_bfloat16(&words).map_err(|e| format!("{e:?}"))?;
        let stored = self
            .container
            .read_bf16_whole(&mut self.file, population)
            .map_err(|error| error.to_string())?;
        let mounted = self
            .chart
            .mount_bfloat16(&stored, tensor.shape[1])
            .map_err(|e| format!("{e:?}"))?;
        let scored = mounted.score_many(&[&query]).map_err(|e| format!("{e:?}"))?;
        let unit = two_to(scored[0].readout_exponent as i64 + scored[0].query_exponent as i64);
        Ok((0..tensor.shape[0])
            .map(|row| Rat::from_integer(scored[0].exact(row).unwrap_or_else(BigInt::zero)) * &unit)
            .collect())
    }

    fn stored(&mut self, population: &str) -> Result<Vec<Rat>, String> {
        Ok(self
            .container
            .read_bf16_whole(&mut self.file, population)
            .map_err(|error| error.to_string())?
            .iter()
            .map(|word| decode_bfloat16_bits(*word).expect("finite").value())
            .collect())
    }

    fn stored_row(&mut self, population: &str, row: usize) -> Result<Vec<Rat>, String> {
        Ok(self
            .container
            .read_rows_bf16(&mut self.file, population, row, 1)
            .map_err(|error| error.to_string())?
            .0
            .iter()
            .map(|word| decode_bfloat16_bits(*word).expect("finite").value())
            .collect())
    }

    fn grain(&mut self, standing: &[Rat]) -> Result<(Vec<Rat>, Vec<Rat>), String> {
        let mut rounded = Vec::with_capacity(standing.len());
        let mut residual = Vec::with_capacity(standing.len());
        for value in standing {
            let (word, remainder) = round_into_bfloat16(value).map_err(|e| format!("{e:?}"))?;
            let datum = decode_bfloat16_bits(word).map_err(|e| format!("{e:?}"))?;
            rounded.push((datum.value(), datum.ulp_exponent, datum.significand.bits() == 0));
            residual.push(remainder);
        }
        let top = rounded
            .iter()
            .filter(|(_, _, zero)| !zero)
            .map(|(_, exponent, _)| *exponent)
            .max()
            .unwrap_or(0);
        let mut carried = Vec::with_capacity(standing.len());
        for (at, (value, exponent, zero)) in rounded.into_iter().enumerate() {
            if !zero && (top - exponent) > CARRIER_REACH {
                residual[at] = standing[at].clone();
                self.below_the_frame += 1;
                carried.push(Rat::from_integer(BigInt::from(0)));
            } else {
                carried.push(value);
            }
        }
        Ok((carried, residual))
    }
}

fn two_to(exponent: i64) -> Rat {
    if exponent >= 0 {
        Rat::from_integer(BigInt::from(num_bigint::BigUint::from(1u8) << exponent as usize))
    } else {
        Rat::new(
            BigInt::from(1),
            BigInt::from(num_bigint::BigUint::from(1u8) << (-exponent) as usize),
        )
    }
}

// ---------------------------------------------------------------------------------------------

/// Found the contact half of the site under one candidate, and conduct it.
///
/// **The aperture is declared**: this is the receiver/presented/carried front, its chronology and
/// its contact. The constitutive passage is excluded, and every candidate flag is exercised here.
fn conduct(
    root: &str,
    chart: &ResidentReadout,
    candidate: Candidate,
    terms: usize,
) -> Result<Vec<Vec<Rat>>, String> {
    let (file, container) = manifest_safetensors(&format!("{root}/model.safetensors"))
        .map_err(|error| error.to_string())?;
    let chart_width = container
        .tensor(&named("self_attn.q_norm.weight"))
        .map_err(|e| e.to_string())?
        .shape[0];
    let receivers = container
        .tensor(&named("self_attn.q_proj.weight"))
        .map_err(|e| e.to_string())?
        .shape[0]
        / chart_width;

    // The band ladder and the band group elements: standing material of the site, founded once.
    let bands = chart_width / 2;
    let ratio = AlgebraicRoot::nth_root(&Rat::from_integer(BigInt::from(10_000)), bands as u32, 44)
        .map_err(|e| format!("{e:?}"))?
        .enclosure()
        .reciprocal()
        .map_err(|e| format!("{e:?}"))?;
    let two = Rat::from_integer(BigInt::from(2));
    let mut current = ExactInterval::point(Rat::from_integer(BigInt::from(1)));
    let mut rotations = Vec::with_capacity(bands);
    for _ in 0..bands {
        let angle = (&current.lower + &current.upper) / &two;
        let (cosine, sine) =
            CertifiedSeries::circular_series(&angle, terms).map_err(|e| format!("{e:?}"))?;
        rotations.push((
            cosine.enclosure().round_out(40).map_err(|e| format!("{e:?}"))?,
            sine.enclosure().round_out(40).map_err(|e| format!("{e:?}"))?,
        ));
        current = current
            .times(&ratio)
            .map_err(|e| format!("{e:?}"))?
            .round_out(40)
            .map_err(|e| format!("{e:?}"))?;
    }

    let mut complex = PortedOperationComplex::new(format!("site {SITE} contact, {}", candidate.name));
    let standing = complex.port("continuing standing");
    let grained = complex.port("grained standing");
    let receiver_wide = complex.port("receiver chart, all heads");
    let presented_wide = complex.port("presented chart, all families");
    let carried_wide = complex.port("carried chart, all families");
    let receiver_head = complex.port("one receiver chart");
    let presented_head = complex.port("one presented chart");
    let carried_head = complex.port("one carried chart");

    let mut program = PortedProgram::default();
    let mut turned_presented: Vec<EventId> = Vec::new();
    let mut carried_heads: Vec<EventId> = Vec::new();
    let mut assembled: Vec<EventId> = Vec::new();
    let floor = Rat::new(BigInt::from(1), BigInt::from(1_000_000));

    for (position, symbol) in CAUSED.iter().enumerate() {
        let tag = |what: &str| format!("position {position} {what}");
        let lookup = law(&mut complex, tag("entering"), OperationSpecies::Construction, vec![], vec![standing]);
        let lookup_event = complex.occur(lookup).map_err(|e| e.to_string())?;
        program.bind(
            lookup_event,
            PortedOperationKind::Lookup { population: SYMBOLS.to_owned(), row: *symbol },
        );
        let entering = grain_after(&mut complex, &mut program, tag("entering grain"), standing, grained, lookup_event)?;

        let rebase = law(&mut complex, tag("entering rebase"), OperationSpecies::Transport, vec![grained], vec![standing]);
        let rebase_event = complex.occur(rebase).map_err(|e| e.to_string())?;
        program.bind(
            rebase_event,
            PortedOperationKind::RebaseByGain {
                population: named("input_layernorm.weight"),
                floor: floor.clone(),
                gain_carries_unit: candidate.gain_carries_unit,
            },
        );
        join(&mut complex, tag("rebase admits"), grained, entering, rebase_event, 0)?;
        let front = grain_after(&mut complex, &mut program, tag("front grain"), standing, grained, rebase_event)?;

        let mut branches = Vec::new();
        for (what, suffix, port) in [
            ("receiver", "self_attn.q_proj.weight", receiver_wide),
            ("presented", "self_attn.k_proj.weight", presented_wide),
            ("carried", "self_attn.v_proj.weight", carried_wide),
        ] {
            let l = law(&mut complex, tag(what), OperationSpecies::Transport, vec![grained], vec![port]);
            let event = complex.occur(l).map_err(|e| e.to_string())?;
            program.bind(event, PortedOperationKind::Contract { population: named(suffix) });
            join(&mut complex, tag(what), grained, front, event, 0)?;
            branches.push(event);
        }

        // One presented and one carried family, and one receiver chart per family.
        let l = law(&mut complex, tag("presented head"), OperationSpecies::Quotient, vec![presented_wide], vec![presented_head]);
        let presented_projected = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(presented_projected, PortedOperationKind::Project { from: 0, count: chart_width });
        join(&mut complex, tag("presented head"), presented_wide, branches[1], presented_projected, 0)?;

        let l = law(&mut complex, tag("presented rebase"), OperationSpecies::Transport, vec![presented_head], vec![presented_head]);
        let presented_rebased = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(
            presented_rebased,
            PortedOperationKind::RebaseByGain {
                population: named("self_attn.k_norm.weight"),
                floor: floor.clone(),
                gain_carries_unit: candidate.gain_carries_unit,
            },
        );
        join(&mut complex, tag("presented rebase"), presented_head, presented_projected, presented_rebased, 0)?;

        let l = law(&mut complex, tag("presented chronology"), OperationSpecies::Transport, vec![presented_head], vec![presented_head]);
        let presented_turned = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(
            presented_turned,
            PortedOperationKind::Chronology {
                rotations: rotations.clone(),
                position: position as u64,
                pairs_halves: candidate.pairs_halves,
            },
        );
        join(&mut complex, tag("presented turns"), presented_head, presented_rebased, presented_turned, 0)?;
        turned_presented.push(presented_turned);

        let l = law(&mut complex, tag("carried head"), OperationSpecies::Quotient, vec![carried_wide], vec![carried_head]);
        let carried_projected = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(carried_projected, PortedOperationKind::Project { from: 0, count: chart_width });
        join(&mut complex, tag("carried head"), carried_wide, branches[2], carried_projected, 0)?;
        carried_heads.push(carried_projected);

        let mut parts = Vec::new();
        for head in 0..receivers {
            let what = format!("receiver chart {head}");
            let l = law(&mut complex, tag(&what), OperationSpecies::Quotient, vec![receiver_wide], vec![receiver_head]);
            let projected = complex.occur(l).map_err(|e| e.to_string())?;
            program.bind(projected, PortedOperationKind::Project { from: head * chart_width, count: chart_width });
            join(&mut complex, tag(&what), receiver_wide, branches[0], projected, 0)?;

            let l = law(&mut complex, tag(&format!("{what} rebase")), OperationSpecies::Transport, vec![receiver_head], vec![receiver_head]);
            let rebased = complex.occur(l).map_err(|e| e.to_string())?;
            program.bind(
                rebased,
                PortedOperationKind::RebaseByGain {
                    population: named("self_attn.q_norm.weight"),
                    floor: floor.clone(),
                    gain_carries_unit: candidate.gain_carries_unit,
                },
            );
            join(&mut complex, tag(&format!("{what} rebase")), receiver_head, projected, rebased, 0)?;

            let l = law(&mut complex, tag(&format!("{what} chronology")), OperationSpecies::Transport, vec![receiver_head], vec![receiver_head]);
            let turned = complex.occur(l).map_err(|e| e.to_string())?;
            program.bind(
                turned,
                PortedOperationKind::Chronology {
                    rotations: rotations.clone(),
                    position: position as u64,
                    pairs_halves: candidate.pairs_halves,
                },
            );
            join(&mut complex, tag(&format!("{what} turns")), receiver_head, rebased, turned, 0)?;

            let reach = position + 1;
            let mut inputs = vec![receiver_head];
            inputs.extend(std::iter::repeat_n(presented_head, reach));
            inputs.extend(std::iter::repeat_n(carried_head, reach));
            let l = law(&mut complex, tag(&format!("{what} contact")), OperationSpecies::Construction, inputs, vec![carried_head]);
            let contact = complex.occur(l).map_err(|e| e.to_string())?;
            program.bind(
                contact,
                PortedOperationKind::ContactAndCarry {
                    terms,
                    scale_width: if candidate.scale_contact { chart_width } else { 1 },
                },
            );
            join(&mut complex, tag(&format!("{what} contact receiver")), receiver_head, turned, contact, 0)?;
            for at in 0..reach {
                join(&mut complex, tag(&format!("{what} presented {at}")), presented_head, turned_presented[at], contact, 1 + at)?;
                join(&mut complex, tag(&format!("{what} carried {at}")), carried_head, carried_heads[at], contact, 1 + reach + at)?;
            }
            parts.push(contact);
        }

        let l = law(&mut complex, tag("carried reconvergence"), OperationSpecies::Construction, vec![carried_head; receivers], vec![carried_wide]);
        let joined = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(joined, PortedOperationKind::Concatenate);
        for (at, part) in parts.iter().enumerate() {
            join(&mut complex, tag(&format!("reconvergence {at}")), carried_head, *part, joined, at)?;
        }
        assembled.push(joined);
    }

    program.validate(&complex).map_err(|e| e.to_string())?;
    let mut carrier = ResidentSourceCarrier {
        chart,
        container,
        file,
        below_the_frame: 0,
    };
    let receipt = realize(&complex, &program, &mut carrier, &BTreeMap::new())
        .map_err(|error| error.to_string())?;
    Ok(assembled
        .iter()
        .map(|event| receipt.carried[&OccurrencePort::output(*event, 0)].clone())
        .collect())
}

fn law(
    complex: &mut PortedOperationComplex,
    name: String,
    species: OperationSpecies,
    inputs: Vec<BoundaryId>,
    outputs: Vec<BoundaryId>,
) -> holonic_engine::evolution::EvolutionLawId {
    complex
        .bind_operation(
            name.clone(),
            species,
            inputs,
            outputs,
            None,
            vec![SourceTestimony::AuthoritativeDescription { statement: name }],
        )
        .expect("bound")
}

fn join(
    complex: &mut PortedOperationComplex,
    name: String,
    boundary: BoundaryId,
    source: EventId,
    target: EventId,
    input: usize,
) -> Result<(), String> {
    complex
        .carries_precedence(name, boundary, OccurrencePort::output(source, 0), OccurrencePort::input(target, input))
        .map_err(|error| error.to_string())
}

fn grain_after(
    complex: &mut PortedOperationComplex,
    program: &mut PortedProgram,
    name: String,
    from: BoundaryId,
    to: BoundaryId,
    source: EventId,
) -> Result<EventId, String> {
    let l = law(complex, name.clone(), OperationSpecies::Quotient, vec![from], vec![to]);
    let event = complex.occur(l).map_err(|e| e.to_string())?;
    program.bind(event, PortedOperationKind::GrainBoundary);
    join(complex, name, from, source, event, 0)?;
    Ok(event)
}

// ---------------------------------------------------------------------------------------------
// THE DECLARED RECEIVER FAMILY
// ---------------------------------------------------------------------------------------------

/// The candidates and what a declared family of receivers reads of each, at each caused position.
///
/// **The receivers are faces, not magnitudes.** A hand is the phase a magnitude reading deletes, and
/// an ordering is what survives a rebase; both cross a frame where a value does not.
struct CandidateSystem {
    /// `returns[item][position]` — the carried standing under one candidate at one position.
    returns: Vec<Vec<Vec<Rat>>>,
    /// `state[item]` is `(candidate, position)`, flattened.
    states: Vec<(usize, usize)>,
    coordinates: Vec<usize>,
}

impl CandidateSystem {
    fn item_of(&self, candidate: usize, position: usize) -> ItemId {
        ItemId(
            self.states
                .iter()
                .position(|held| *held == (candidate, position))
                .expect("declared") as u64,
        )
    }
}

impl ObservedSystem for CandidateSystem {
    fn items(&self) -> Vec<ItemId> {
        (0..self.states.len() as u64).map(ItemId).collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        // One hand receiver and one order receiver per declared coordinate.
        (0..(self.coordinates.len() * 2) as u64)
            .map(ReceiverId)
            .collect()
    }

    fn inputs(&self) -> Vec<InputId> {
        vec![InputId(0)]
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let (candidate, position) = self.states[item.0 as usize];
        let section = &self.returns[candidate][position];
        let which = receiver.0 as usize / 2;
        let coordinate = self.coordinates[which];
        let value = section.get(coordinate).cloned().unwrap_or_else(Rat::zero);
        if receiver.0 % 2 == 0 {
            // THE HAND: the phase a magnitude reading deletes.
            Observation(if value.is_positive() {
                1
            } else if value.is_negative() {
                2
            } else {
                0
            })
        } else {
            // AN ORDER: this coordinate against the next declared one. A relation, not a value.
            let other = self
                .coordinates
                .get(which + 1)
                .and_then(|at| section.get(*at))
                .cloned()
                .unwrap_or_else(Rat::zero);
            Observation(match value.cmp(&other) {
                std::cmp::Ordering::Less => 1,
                std::cmp::Ordering::Equal => 2,
                std::cmp::Ordering::Greater => 3,
            })
        }
    }

    fn successor(&self, item: ItemId, _input: InputId) -> Option<ItemId> {
        let (candidate, position) = self.states[item.0 as usize];
        if position + 1 < self.returns[candidate].len() {
            Some(self.item_of(candidate, position + 1))
        } else {
            None
        }
    }
}

/// A declared subfamily of receivers. `AblatedSystem` withdraws one; this keeps a stated set, which
/// is what a MINIMAL separating family needs.
struct RestrictedSystem<'a> {
    inner: &'a dyn ObservedSystem,
    kept: Vec<ReceiverId>,
}

impl ObservedSystem for RestrictedSystem<'_> {
    fn items(&self) -> Vec<ItemId> {
        self.inner.items()
    }
    fn receivers(&self) -> Vec<ReceiverId> {
        self.kept.clone()
    }
    fn inputs(&self) -> Vec<InputId> {
        self.inner.inputs()
    }
    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        self.inner.observation(item, receiver)
    }
    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.inner.successor(item, input)
    }
}

// ---------------------------------------------------------------------------------------------

fn main() {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let terms: usize = std::env::var("TERMS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(20);

    let chart = match ResidentReadout::new() {
        Ok(chart) => chart,
        Err(error) => {
            println!("the resident chart refused: {error:?}");
            println!("The admitted hot deed returns a typed refusal. No CPU answer appears.");
            std::process::exit(1);
        }
    };

    println!("PHOENIX STATION FIVE (DISSECTION) — THE CANDIDATES ARE SEPARATED");
    println!();
    println!("  resident chart                    {}", chart.device_name());
    println!("  caused positions                  {}", CAUSED.len());
    println!("  declared aperture                 the receiver/presented/carried front, its");
    println!("                                    chronology and its contact. The constitutive");
    println!("                                    passage is EXCLUDED and reported as excluded.");
    println!();

    let mut population = vec![BASE];
    population.extend(SIBLINGS);
    let mut returns = Vec::with_capacity(population.len());
    for candidate in &population {
        let clock = std::time::Instant::now();
        match conduct(&root, &chart, *candidate, terms) {
            Ok(carried) => {
                println!(
                    "  conducted  {:<44} {:?}",
                    candidate.name,
                    clock.elapsed()
                );
                returns.push(carried);
            }
            Err(error) => {
                println!("  REFUSED    {:<44} {error}", candidate.name);
                println!("  A refusal is the return. Nothing is substituted for it.");
                std::process::exit(1);
            }
        }
    }

    // The declared coordinate family: a spread across the carried chart, stated rather than sought.
    let width = returns[0][0].len();
    let coordinates: Vec<usize> = (0..16).map(|k| k * width / 16).collect();
    let mut states = Vec::new();
    for candidate in 0..population.len() {
        for position in 0..CAUSED.len() {
            states.push((candidate, position));
        }
    }
    let system = CandidateSystem {
        returns,
        states,
        coordinates: coordinates.clone(),
    };

    println!();
    println!("  THE DECLARED RECEIVER FAMILY");
    println!("    coordinates declared            {}", coordinates.len());
    println!("    receivers                       {} — a HAND and an ORDER at each", coordinates.len() * 2);
    println!("    items                           {} — one per candidate per position", system.states.len());
    println!("    (a hand is the phase a magnitude reading deletes; an order is a relation. Both");
    println!("     cross a frame where a value does not.)");

    let reading = compress(&system);
    println!();
    println!("  THE RECEIVER-EXACT QUOTIENT");
    println!("    one-shot blocks                 {}", reading.one_shot.len());
    println!("    blocks under successor conduct  {}", reading.conduct.len());
    println!("    refinement rounds               {}", reading.rounds);
    println!("    one-shot reading is exact       {}", reading.is_exact());
    println!("    collapsed pairs later conduct separates  {}", reading.collapsed.len());

    println!();
    println!("  WHAT THIS SETTLES, QUESTION BY QUESTION");
    println!();
    let base_item = system.item_of(0, 0);
    for (at, candidate) in population.iter().enumerate().skip(1) {
        let sibling = system.item_of(at, 0);
        let together = reading.conduct.block_of(base_item) == reading.conduct.block_of(sibling);
        println!("    {}", candidate.question);
        println!("        sibling                 {}", candidate.name);
        if together {
            println!("        SEPARATED               no — no declared receiver tells them apart");
            println!("        so the question is      MOOT at this aperture; both are one transport");
            println!("                                for this family, and a richer receiver may reopen it");
        } else {
            println!("        SEPARATED               YES — the family tells them apart");
            println!("        so the question is      REAL, and settling it needs SOURCE conduct,");
            println!("                                which this machine does not hold");
        }
        println!();
    }

    for pair in reading.collapsed.iter().take(4) {
        println!(
            "    a one-shot collapse later conduct separates: {:?} against {:?} after {} input(s)",
            pair.left,
            pair.right,
            pair.distinguishing_word.len()
        );
        if let Some((receiver, left, right)) = &pair.witness {
            println!("        the receiver that finally saw it: {receiver:?} returning {left:?} against {right:?}");
        }
    }

    println!();
    println!("  THE ANTI-VACUITY CONTROL — and the first reading of it was wrong");
    println!();
    let mut individually_redundant = 0usize;
    for receiver in system.receivers() {
        let ablated = AblatedSystem {
            inner: &system,
            without: receiver,
        };
        if compress(&ablated).conduct.len() == reading.conduct.len() {
            individually_redundant += 1;
        }
    }
    println!("    receivers withdrawn one at a time          {}", system.receivers().len());
    println!("    whose single withdrawal changed nothing    {individually_redundant}");
    println!();
    println!("    **That is redundancy, not decoration**, and reading it as decoration would be");
    println!("    the error. Many receivers witness the same separation, so no SINGLE one is");
    println!("    necessary. The honest controls are the two below.");
    println!();

    // Control one: withdraw the whole family. The partition must collapse.
    let empty = RestrictedSystem {
        inner: &system,
        kept: Vec::new(),
    };
    let without_any = compress(&empty);
    println!("    with NO receiver at all, blocks            {}", without_any.conduct.len());
    println!("    with the whole family, blocks              {}", reading.conduct.len());
    println!(
        "    the family does work                       {}",
        without_any.conduct.len() < reading.conduct.len()
    );
    println!();

    // Control two: a MINIMAL subfamily that still returns the same partition.
    let mut kept: Vec<ReceiverId> = system.receivers();
    for receiver in system.receivers() {
        let trial: Vec<ReceiverId> = kept.iter().copied().filter(|held| *held != receiver).collect();
        let restricted = RestrictedSystem {
            inner: &system,
            kept: trial.clone(),
        };
        if compress(&restricted).conduct == reading.conduct {
            kept = trial;
        }
    }
    println!("    a MINIMAL subfamily returning the same partition: {} of {}", kept.len(), system.receivers().len());
    for receiver in &kept {
        let which = receiver.0 as usize / 2;
        println!(
            "        {receiver:?}  the {} at declared coordinate {}",
            if receiver.0 % 2 == 0 { "HAND" } else { "ORDER" },
            coordinates[which]
        );
    }
    println!("    every receiver outside it is redundant WITH these, not idle.");

    println!();
    println!("THE STATION'S VERDICT");
    println!();
    println!("  The candidates were separated by a declared receiver family and by nothing else.");
    println!("  No plausible surface was read and no composition was selected.");
    println!("  A question whose siblings collapse is MOOT at this aperture and is recorded so.");
    println!("  A question whose siblings separate is REAL, and the evidence that would settle it");
    println!("  is source conduct, which is absent on this machine and named as absent.");
    println!();
    println!("  The constitutive passage is excluded from this aperture. CONSTRUCTION_STATE is");
    println!("  untouched.");
}
