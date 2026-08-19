//! **The Phoenix site: one founding of the bound diagram, shared by every station that conducts it.**
//!
//! Plan: `blueprint/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md`.
//!
//! Two stations conduct this same site — the dissection separates candidate compositions, the
//! condensation asks which axes are load-bearing — and they must conduct the SAME diagram or
//! neither return means anything against the other. So the founding lives here once.
//!
//! It is not a library owner: it binds a source instance, and `CLAUDE.md`'s rule is that a source
//! instance never becomes internal anatomy. It is also not a scheduler — it declares ports, laws,
//! occurrences and bonds, binds each occurrence to an exact operation, and hands over to
//! `ported_operation::realize`, which is where the chronology decides the order.

#![allow(dead_code)]

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
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use relational_geometry::Rat;

const SITE: usize = 0;
const SYMBOLS: &str = "model.language_model.embed_tokens.weight";
/// The name the chronology's band elements are sealed and looked up under.
pub const BAND_POPULATION: &str = "site.chronology.band-elements";

pub const CAUSED: [usize; 3] = [818, 18_740, 563];

fn named(suffix: &str) -> String {
    format!("model.language_model.layers.{SITE}.{suffix}")
}

/// One member of the open candidate populations. A sibling moves **one** relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Candidate {
    pub name: &'static str,
    pub question: &'static str,
    pub gain_carries_unit: bool,
    pub pairs_halves: bool,
    pub scale_contact: bool,
}

pub const BASE: Candidate = Candidate {
    name: "base",
    question: "-",
    gain_carries_unit: false,
    pairs_halves: true,
    scale_contact: true,
};

pub const SIBLINGS: [Candidate; 3] = [
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

pub struct ResidentSourceCarrier<'chart> {
    chart: &'chart ResidentReadout,
    container: ForeignContainer,
    file: File,
    below_the_frame: usize,
    /// The band group elements, founded once and supplied by name. **Material, not program text.**
    rotations: BTreeMap<String, Vec<(ExactInterval, ExactInterval)>>,
}

/// Read off the carrier and the diagram: a signed word holds sixty-three magnitude octaves, a
/// `BF16` significand eight of them, and the widest contraction here is `2560` wide, so
/// `2(reach + 8) + 12 + 1 <= 128` gives `reach <= 49`.
pub const CARRIER_REACH: i32 = 46;

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

    fn rotations(
        &mut self,
        population: &str,
    ) -> Result<Vec<(ExactInterval, ExactInterval)>, String> {
        self.rotations
            .get(population)
            .cloned()
            .ok_or_else(|| format!("no band population named {population}"))
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
/// A declared ablation of the entering construction: a span of coordinates withdrawn and retained.
///
/// `None` is the base. A span is a **matched sibling** differing in exactly one relation, which is
/// what makes an attribution possible at all.
pub type DeclaredAblation = Option<(usize, usize)>;

/// **The founding: the diagram, its program, and the material they name.**
///
/// Separated from the conduct so a native rest can seal exactly this and nothing else. What a
/// program NAMES is what a rest must carry; anything else in the source is outside the seal and is
/// reported as outside it.
pub struct FoundedSite {
    pub complex: PortedOperationComplex,
    pub program: PortedProgram,
    pub band_elements: Vec<(ExactInterval, ExactInterval)>,
    /// Every stored population the program names, and nothing else.
    pub populations: Vec<String>,
    /// The occurrences whose output is the site's return, in position order.
    pub returns: Vec<EventId>,
}

pub fn found(
    root: &str,
    candidate: Candidate,
    terms: usize,
    ablation: DeclaredAblation,
) -> Result<(FoundedSite, ForeignContainer, File), String> {
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
        let mut entering =
            grain_after(&mut complex, &mut program, tag("entering grain"), standing, grained, lookup_event)?;
        if let Some((from, count)) = ablation {
            // **A targeted ablation, as an occurrence in the diagram.** What it withdraws is its
            // retained fibre, so the predecessor stays reconstructible from the return and the
            // fibre together.
            let l = law(&mut complex, tag("declared ablation"), OperationSpecies::Quotient, vec![grained], vec![grained]);
            let event = complex.occur(l).map_err(|e| e.to_string())?;
            program.bind(event, PortedOperationKind::Ablate { from, count });
            join(&mut complex, tag("ablation admits"), grained, entering, event, 0)?;
            entering = event;
        }

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
                rotations: BAND_POPULATION.to_owned(),
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
                    rotations: BAND_POPULATION.to_owned(),
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
    let mut populations: Vec<String> = Vec::new();
    for operation in program.operations.values() {
        let named = match operation {
            PortedOperationKind::Lookup { population, .. }
            | PortedOperationKind::Contract { population }
            | PortedOperationKind::RebaseByGain { population, .. } => Some(population.clone()),
            _ => None,
        };
        if let Some(name) = named
            && !populations.contains(&name)
        {
            populations.push(name);
        }
    }
    populations.sort();
    Ok((
        FoundedSite {
            complex,
            program,
            band_elements: rotations,
            populations,
            returns: assembled,
        },
        container,
        file,
    ))
}

pub fn conduct(
    root: &str,
    chart: &ResidentReadout,
    candidate: Candidate,
    terms: usize,
    ablation: DeclaredAblation,
) -> Result<Vec<Vec<Rat>>, String> {
    let (site, container, file) = found(root, candidate, terms, ablation)?;
    let mut carrier = ResidentSourceCarrier {
        chart,
        container,
        file,
        below_the_frame: 0,
        rotations: BTreeMap::from([(BAND_POPULATION.to_owned(), site.band_elements.clone())]),
    };
    let receipt = realize(&site.complex, &site.program, &mut carrier, &BTreeMap::new())
        .map_err(|error| error.to_string())?;
    Ok(site
        .returns
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

