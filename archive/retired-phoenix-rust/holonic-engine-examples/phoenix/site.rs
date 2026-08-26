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
//! `ported_reference::realize`, which is where the chronology decides the order.

#![allow(dead_code)]

use std::collections::BTreeMap;
use std::fs::File;
use std::io::Write;

use holonic_engine::category::BoundaryId;
use holonic_engine::causal::EventId;
use holonic_engine::embedding_fiber::{MountedReadout, ResidentReadout, align_bfloat16};
use holonic_engine::exact_value::ieee754::{
    decode_bfloat16_bits, decode_binary64_bits, round_into_bfloat16,
};
use holonic_engine::exact_value::{AlgebraicRoot, CertifiedSeries, ExactInterval};
use holonic_engine::foreign_map::{ForeignContainer, manifest_safetensors};
use holonic_engine::interaction::OccurrencePort;
use holonic_engine::ported_operation::{OperationSpecies, PortedOperationComplex, SourceTestimony};
use holonic_engine::ported_reference::{
    PortedCarrier, PortedOperationKind, PortedProgram, realize,
};
use num_bigint::BigInt;
use num_traits::Zero;
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
    pub chart: &'chart ResidentReadout,
    pub container: ForeignContainer,
    pub file: File,
    pub below_the_frame: usize,
    /// The band group elements, founded once and supplied by name. **Material, not program text.**
    pub rotations: BTreeMap<String, Vec<(ExactInterval, ExactInterval)>>,
    /// **Residency.** A population mounted on the card stays there and is scored again.
    ///
    /// Without this the carrier re-read and re-mounted an INVARIANT operand at every occurrence —
    /// three times per projection for three positions, and it would have been four gigabytes of
    /// re-upload for a tied emission head. `CLAUDE.md` names that failure directly: *a device call
    /// with no residency that spends its time re-uploading an invariant operand*. Keyed by
    /// population, so nothing about the diagram decides what is resident; the material does.
    pub resident: BTreeMap<String, MountedReadout<'chart>>,
    /// How many mounts were served from residency rather than re-uploaded. A measurement, so the
    /// claim above is checkable rather than asserted.
    pub reused: usize,
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
        if self.resident.contains_key(population) {
            self.reused += 1;
        } else {
            let stored = self
                .container
                .read_bf16_whole(&mut self.file, population)
                .map_err(|error| error.to_string())?;
            let mounted = self
                .chart
                .mount_bfloat16(&stored, tensor.shape[1])
                .map_err(|e| format!("{e:?}"))?;
            self.resident.insert(population.to_owned(), mounted);
        }
        let scored = self.resident[population]
            .score_many(&[&query])
            .map_err(|e| format!("{e:?}"))?;
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
            rounded.push((
                datum.value(),
                datum.ulp_exponent,
                datum.significand.bits() == 0,
            ));
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

pub fn two_to(exponent: i64) -> Rat {
    if exponent >= 0 {
        Rat::from_integer(BigInt::from(
            num_bigint::BigUint::from(1u8) << exponent as usize,
        ))
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

/// **How far into the layer the diagram reaches.**
///
/// A parameter rather than an edit, because the stations that returned already measured the contact
/// half and a figure re-taken against a different diagram is a different figure.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum Reach {
    /// Through the contact and its reconvergence. What stations three through eleven measured.
    #[default]
    ContactHalf,
    /// The whole layer: the contact's return projected back, both re-entries, and the gated
    /// passage. **Not the whole layer's SOURCE** — the per-layer branch is an open candidate and is
    /// named as one by `WHOLE_LAYER_OPEN` rather than guessed at.
    WholeLayer,
    /// The layer, then the body's final rebase and the **tied** emission head.
    ///
    /// `tie_word_embeddings` is `true` and there is no `lm_head` in the container, so the head IS
    /// `embed_tokens.weight` read the other way — the same 262144 x 2560 population the mouth reads
    /// rows of. The return is the illicial potential section, 262144 wide.
    ///
    /// The declared `final_logit_softcapping` is NOT an occurrence here, and that is a claim rather
    /// than an omission: `c*tanh(x/c)` is strictly monotone, so it cannot move any receiver that
    /// reads an ORDER, and an order is what crosses a frame where a magnitude does not. The station
    /// applies it as the receiver face it is and checks that the block does not move.
    ThroughEmission,
}

/// **What the whole-layer reach does NOT decide.** Four populations layer zero carries whose
/// composition the source's configuration and model card do not fix, retained as the question they
/// are rather than bound to a plausible reading. `CLAUDE.md`: human inspection of plausible language
/// cannot select a composition.
pub const WHOLE_LAYER_OPEN: [(&str, &str); 4] = [
    (
        "per_layer_input_gate.weight",
        "the per-layer embedding is 256 wide and this contracts 2560 to 256 — which side gates \
         which, and is the product taken before or after `post_per_layer_input_norm`?",
    ),
    (
        "per_layer_projection.weight",
        "it returns 256 to 2560, but whether its return re-enters the residual before or after the \
         gated passage is not stated anywhere in the configuration or the model card",
    ),
    (
        "post_per_layer_input_norm.weight",
        "a 2560 rebase gain on a branch whose own composition is undecided",
    ),
    (
        "layer_scalar",
        "a single stored value with no declared role — a gain on the layer's return, on its \
         re-entry, or on neither",
    ),
];

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
    found_reaching(root, candidate, terms, ablation, Reach::ContactHalf)
}

pub fn found_reaching(
    root: &str,
    candidate: Candidate,
    terms: usize,
    ablation: DeclaredAblation,
    reach: Reach,
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
            cosine
                .enclosure()
                .round_out(40)
                .map_err(|e| format!("{e:?}"))?,
            sine.enclosure()
                .round_out(40)
                .map_err(|e| format!("{e:?}"))?,
        ));
        current = current
            .times(&ratio)
            .map_err(|e| format!("{e:?}"))?
            .round_out(40)
            .map_err(|e| format!("{e:?}"))?;
    }

    let mut complex =
        PortedOperationComplex::new(format!("site {SITE} contact, {}", candidate.name));
    let standing = complex.port("continuing standing");
    let grained = complex.port("grained standing");
    let receiver_wide = complex.port("receiver chart, all heads");
    let presented_wide = complex.port("presented chart, all families");
    let carried_wide = complex.port("carried chart, all families");
    let receiver_head = complex.port("one receiver chart");
    let presented_head = complex.port("one presented chart");
    let carried_head = complex.port("one carried chart");
    let passage_wide = complex.port("the gated passage's chart");
    let potential = complex.port("the illicial potential section");

    let mut program = PortedProgram::default();
    let mut entering_standing: Vec<EventId> = Vec::new();
    let mut turned_presented: Vec<EventId> = Vec::new();
    let mut carried_heads: Vec<EventId> = Vec::new();
    let mut assembled: Vec<EventId> = Vec::new();
    let floor = Rat::new(BigInt::from(1), BigInt::from(1_000_000));

    for (position, symbol) in CAUSED.iter().enumerate() {
        let tag = |what: &str| format!("position {position} {what}");
        let lookup = law(
            &mut complex,
            tag("entering"),
            OperationSpecies::Construction,
            vec![],
            vec![standing],
        );
        let lookup_event = complex.occur(lookup).map_err(|e| e.to_string())?;
        program.bind(
            lookup_event,
            PortedOperationKind::Lookup {
                population: SYMBOLS.to_owned(),
                row: *symbol,
            },
        );
        let mut entering = grain_after(
            &mut complex,
            &mut program,
            tag("entering grain"),
            standing,
            grained,
            lookup_event,
        )?;
        if let Some((from, count)) = ablation {
            // **A targeted ablation, as an occurrence in the diagram.** What it withdraws is its
            // retained fibre, so the predecessor stays reconstructible from the return and the
            // fibre together.
            let l = law(
                &mut complex,
                tag("declared ablation"),
                OperationSpecies::Quotient,
                vec![grained],
                vec![grained],
            );
            let event = complex.occur(l).map_err(|e| e.to_string())?;
            program.bind(event, PortedOperationKind::Ablate { from, count });
            join(
                &mut complex,
                tag("ablation admits"),
                grained,
                entering,
                event,
                0,
            )?;
            entering = event;
        }

        // The residual stream is the value BEFORE the entering rebase, which is what both
        // re-entries below return to.
        entering_standing.push(entering);
        let rebase = law(
            &mut complex,
            tag("entering rebase"),
            OperationSpecies::Transport,
            vec![grained],
            vec![standing],
        );
        let rebase_event = complex.occur(rebase).map_err(|e| e.to_string())?;
        program.bind(
            rebase_event,
            PortedOperationKind::RebaseByGain {
                population: named("input_layernorm.weight"),
                floor: floor.clone(),
                gain_carries_unit: candidate.gain_carries_unit,
            },
        );
        join(
            &mut complex,
            tag("rebase admits"),
            grained,
            entering,
            rebase_event,
            0,
        )?;
        let front = grain_after(
            &mut complex,
            &mut program,
            tag("front grain"),
            standing,
            grained,
            rebase_event,
        )?;

        let mut branches = Vec::new();
        for (what, suffix, port) in [
            ("receiver", "self_attn.q_proj.weight", receiver_wide),
            ("presented", "self_attn.k_proj.weight", presented_wide),
            ("carried", "self_attn.v_proj.weight", carried_wide),
        ] {
            let l = law(
                &mut complex,
                tag(what),
                OperationSpecies::Transport,
                vec![grained],
                vec![port],
            );
            let event = complex.occur(l).map_err(|e| e.to_string())?;
            program.bind(
                event,
                PortedOperationKind::Contract {
                    population: named(suffix),
                },
            );
            join(&mut complex, tag(what), grained, front, event, 0)?;
            branches.push(event);
        }

        // One presented and one carried family, and one receiver chart per family.
        let l = law(
            &mut complex,
            tag("presented head"),
            OperationSpecies::Quotient,
            vec![presented_wide],
            vec![presented_head],
        );
        let presented_projected = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(
            presented_projected,
            PortedOperationKind::Project {
                from: 0,
                count: chart_width,
            },
        );
        join(
            &mut complex,
            tag("presented head"),
            presented_wide,
            branches[1],
            presented_projected,
            0,
        )?;

        let l = law(
            &mut complex,
            tag("presented rebase"),
            OperationSpecies::Transport,
            vec![presented_head],
            vec![presented_head],
        );
        let presented_rebased = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(
            presented_rebased,
            PortedOperationKind::RebaseByGain {
                population: named("self_attn.k_norm.weight"),
                floor: floor.clone(),
                gain_carries_unit: candidate.gain_carries_unit,
            },
        );
        join(
            &mut complex,
            tag("presented rebase"),
            presented_head,
            presented_projected,
            presented_rebased,
            0,
        )?;

        let l = law(
            &mut complex,
            tag("presented chronology"),
            OperationSpecies::Transport,
            vec![presented_head],
            vec![presented_head],
        );
        let presented_turned = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(
            presented_turned,
            PortedOperationKind::Chronology {
                rotations: BAND_POPULATION.to_owned(),
                position: position as u64,
                pairs_halves: candidate.pairs_halves,
            },
        );
        join(
            &mut complex,
            tag("presented turns"),
            presented_head,
            presented_rebased,
            presented_turned,
            0,
        )?;
        turned_presented.push(presented_turned);

        let l = law(
            &mut complex,
            tag("carried head"),
            OperationSpecies::Quotient,
            vec![carried_wide],
            vec![carried_head],
        );
        let carried_projected = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(
            carried_projected,
            PortedOperationKind::Project {
                from: 0,
                count: chart_width,
            },
        );
        join(
            &mut complex,
            tag("carried head"),
            carried_wide,
            branches[2],
            carried_projected,
            0,
        )?;
        carried_heads.push(carried_projected);

        let mut parts = Vec::new();
        for head in 0..receivers {
            let what = format!("receiver chart {head}");
            let l = law(
                &mut complex,
                tag(&what),
                OperationSpecies::Quotient,
                vec![receiver_wide],
                vec![receiver_head],
            );
            let projected = complex.occur(l).map_err(|e| e.to_string())?;
            program.bind(
                projected,
                PortedOperationKind::Project {
                    from: head * chart_width,
                    count: chart_width,
                },
            );
            join(
                &mut complex,
                tag(&what),
                receiver_wide,
                branches[0],
                projected,
                0,
            )?;

            let l = law(
                &mut complex,
                tag(&format!("{what} rebase")),
                OperationSpecies::Transport,
                vec![receiver_head],
                vec![receiver_head],
            );
            let rebased = complex.occur(l).map_err(|e| e.to_string())?;
            program.bind(
                rebased,
                PortedOperationKind::RebaseByGain {
                    population: named("self_attn.q_norm.weight"),
                    floor: floor.clone(),
                    gain_carries_unit: candidate.gain_carries_unit,
                },
            );
            join(
                &mut complex,
                tag(&format!("{what} rebase")),
                receiver_head,
                projected,
                rebased,
                0,
            )?;

            let l = law(
                &mut complex,
                tag(&format!("{what} chronology")),
                OperationSpecies::Transport,
                vec![receiver_head],
                vec![receiver_head],
            );
            let turned = complex.occur(l).map_err(|e| e.to_string())?;
            program.bind(
                turned,
                PortedOperationKind::Chronology {
                    rotations: BAND_POPULATION.to_owned(),
                    position: position as u64,
                    pairs_halves: candidate.pairs_halves,
                },
            );
            join(
                &mut complex,
                tag(&format!("{what} turns")),
                receiver_head,
                rebased,
                turned,
                0,
            )?;

            let reach = position + 1;
            let mut inputs = vec![receiver_head];
            inputs.extend(std::iter::repeat_n(presented_head, reach));
            inputs.extend(std::iter::repeat_n(carried_head, reach));
            let l = law(
                &mut complex,
                tag(&format!("{what} contact")),
                OperationSpecies::Construction,
                inputs,
                vec![carried_head],
            );
            let contact = complex.occur(l).map_err(|e| e.to_string())?;
            program.bind(
                contact,
                PortedOperationKind::ContactAndCarry {
                    terms,
                    scale_width: if candidate.scale_contact {
                        chart_width
                    } else {
                        1
                    },
                },
            );
            join(
                &mut complex,
                tag(&format!("{what} contact receiver")),
                receiver_head,
                turned,
                contact,
                0,
            )?;
            for at in 0..reach {
                join(
                    &mut complex,
                    tag(&format!("{what} presented {at}")),
                    presented_head,
                    turned_presented[at],
                    contact,
                    1 + at,
                )?;
                join(
                    &mut complex,
                    tag(&format!("{what} carried {at}")),
                    carried_head,
                    carried_heads[at],
                    contact,
                    1 + reach + at,
                )?;
            }
            parts.push(contact);
        }

        let l = law(
            &mut complex,
            tag("carried reconvergence"),
            OperationSpecies::Construction,
            vec![carried_head; receivers],
            vec![carried_wide],
        );
        let joined = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(joined, PortedOperationKind::Concatenate);
        for (at, part) in parts.iter().enumerate() {
            join(
                &mut complex,
                tag(&format!("reconvergence {at}")),
                carried_head,
                *part,
                joined,
                at,
            )?;
        }
        if reach == Reach::ContactHalf {
            assembled.push(joined);
            continue;
        }

        // -------------------------------------------------------------------------------------
        // THE GATED PASSAGE HALF. Every population below is named by the source; the four the
        // source does NOT decide are in `WHOLE_LAYER_OPEN` and appear nowhere in this diagram.
        // -------------------------------------------------------------------------------------
        let returned_grain = grain_after(
            &mut complex,
            &mut program,
            tag("contact return grain"),
            carried_wide,
            carried_wide,
            joined,
        )?;

        let l = law(
            &mut complex,
            tag("contact returns"),
            OperationSpecies::Transport,
            vec![carried_wide],
            vec![grained],
        );
        let projected_back = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(
            projected_back,
            PortedOperationKind::Contract {
                population: named("self_attn.o_proj.weight"),
            },
        );
        join(
            &mut complex,
            tag("contact returns"),
            carried_wide,
            returned_grain,
            projected_back,
            0,
        )?;

        let l = law(
            &mut complex,
            tag("contact return rebase"),
            OperationSpecies::Transport,
            vec![grained],
            vec![grained],
        );
        let returned_rebased = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(
            returned_rebased,
            PortedOperationKind::RebaseByGain {
                population: named("post_attention_layernorm.weight"),
                floor: floor.clone(),
                gain_carries_unit: candidate.gain_carries_unit,
            },
        );
        join(
            &mut complex,
            tag("contact return rebase"),
            grained,
            projected_back,
            returned_rebased,
            0,
        )?;

        // **THE FIRST RE-ENTRY.** The retained standing and the returned current, joined.
        let l = law(
            &mut complex,
            tag("contact re-entry"),
            OperationSpecies::Construction,
            vec![grained, grained],
            vec![grained],
        );
        let first_re_entry = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(first_re_entry, PortedOperationKind::ReEntry);
        join(
            &mut complex,
            tag("re-entry retains"),
            grained,
            entering_standing[position],
            first_re_entry,
            0,
        )?;
        join(
            &mut complex,
            tag("re-entry returns"),
            grained,
            returned_rebased,
            first_re_entry,
            1,
        )?;

        let l = law(
            &mut complex,
            tag("passage entering rebase"),
            OperationSpecies::Transport,
            vec![grained],
            vec![grained],
        );
        let passage_entering = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(
            passage_entering,
            PortedOperationKind::RebaseByGain {
                population: named("pre_feedforward_layernorm.weight"),
                floor: floor.clone(),
                gain_carries_unit: candidate.gain_carries_unit,
            },
        );
        join(
            &mut complex,
            tag("passage entering rebase"),
            grained,
            first_re_entry,
            passage_entering,
            0,
        )?;
        let passage_grain = grain_after(
            &mut complex,
            &mut program,
            tag("passage entering grain"),
            grained,
            grained,
            passage_entering,
        )?;

        // **THE FRONT.** The gate and the carried branch are CO-PRESENT — neither reads the other,
        // and `layers()` puts them in one front for exactly that reason.
        let mut passage_branches = Vec::new();
        for (what, suffix) in [
            ("gate", "mlp.gate_proj.weight"),
            ("up", "mlp.up_proj.weight"),
        ] {
            let l = law(
                &mut complex,
                tag(what),
                OperationSpecies::Transport,
                vec![grained],
                vec![passage_wide],
            );
            let event = complex.occur(l).map_err(|e| e.to_string())?;
            program.bind(
                event,
                PortedOperationKind::Contract {
                    population: named(suffix),
                },
            );
            join(&mut complex, tag(what), grained, passage_grain, event, 0)?;
            passage_branches.push(event);
        }

        let l = law(
            &mut complex,
            tag("the gate turns"),
            OperationSpecies::Transport,
            vec![passage_wide],
            vec![passage_wide],
        );
        let gated = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(
            gated,
            PortedOperationKind::GatedPassage {
                terms,
                inner: Some(gelu_inner()),
            },
        );
        join(
            &mut complex,
            tag("the gate turns"),
            passage_wide,
            passage_branches[0],
            gated,
            0,
        )?;

        let l = law(
            &mut complex,
            tag("the gate admits"),
            OperationSpecies::Construction,
            vec![passage_wide, passage_wide],
            vec![passage_wide],
        );
        let admitted = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(admitted, PortedOperationKind::Hadamard);
        join(
            &mut complex,
            tag("the gate admits gate"),
            passage_wide,
            gated,
            admitted,
            0,
        )?;
        join(
            &mut complex,
            tag("the gate admits up"),
            passage_wide,
            passage_branches[1],
            admitted,
            1,
        )?;
        let admitted_grain = grain_after(
            &mut complex,
            &mut program,
            tag("passage grain"),
            passage_wide,
            passage_wide,
            admitted,
        )?;

        let l = law(
            &mut complex,
            tag("the passage returns"),
            OperationSpecies::Transport,
            vec![passage_wide],
            vec![grained],
        );
        let passage_returned = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(
            passage_returned,
            PortedOperationKind::Contract {
                population: named("mlp.down_proj.weight"),
            },
        );
        join(
            &mut complex,
            tag("the passage returns"),
            passage_wide,
            admitted_grain,
            passage_returned,
            0,
        )?;

        let l = law(
            &mut complex,
            tag("passage return rebase"),
            OperationSpecies::Transport,
            vec![grained],
            vec![grained],
        );
        let passage_rebased = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(
            passage_rebased,
            PortedOperationKind::RebaseByGain {
                population: named("post_feedforward_layernorm.weight"),
                floor: floor.clone(),
                gain_carries_unit: candidate.gain_carries_unit,
            },
        );
        join(
            &mut complex,
            tag("passage return rebase"),
            grained,
            passage_returned,
            passage_rebased,
            0,
        )?;

        // **THE SECOND RE-ENTRY.** The layer's return.
        let l = law(
            &mut complex,
            tag("passage re-entry"),
            OperationSpecies::Construction,
            vec![grained, grained],
            vec![grained],
        );
        let second_re_entry = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(second_re_entry, PortedOperationKind::ReEntry);
        join(
            &mut complex,
            tag("passage re-entry retains"),
            grained,
            first_re_entry,
            second_re_entry,
            0,
        )?;
        join(
            &mut complex,
            tag("passage re-entry returns"),
            grained,
            passage_rebased,
            second_re_entry,
            1,
        )?;
        if reach == Reach::WholeLayer {
            assembled.push(second_re_entry);
            continue;
        }

        // -------------------------------------------------------------------------------------
        // THE EMISSION. The body's final rebase, then the TIED head.
        // -------------------------------------------------------------------------------------
        let l = law(
            &mut complex,
            tag("the body's rebase"),
            OperationSpecies::Transport,
            vec![grained],
            vec![grained],
        );
        let body_rebased = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(
            body_rebased,
            PortedOperationKind::RebaseByGain {
                population: "model.language_model.norm.weight".to_owned(),
                floor: floor.clone(),
                gain_carries_unit: candidate.gain_carries_unit,
            },
        );
        join(
            &mut complex,
            tag("the body's rebase"),
            grained,
            second_re_entry,
            body_rebased,
            0,
        )?;
        let emission_grain = grain_after(
            &mut complex,
            &mut program,
            tag("emission grain"),
            grained,
            grained,
            body_rebased,
        )?;

        let l = law(
            &mut complex,
            tag("the emission"),
            OperationSpecies::Transport,
            vec![grained],
            vec![potential],
        );
        let emitted = complex.occur(l).map_err(|e| e.to_string())?;
        program.bind(
            emitted,
            PortedOperationKind::Contract {
                population: SYMBOLS.to_owned(),
            },
        );
        join(
            &mut complex,
            tag("the emission"),
            grained,
            emission_grain,
            emitted,
            0,
        )?;
        assembled.push(emitted);
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
        resident: BTreeMap::new(),
        reused: 0,
    };
    let receipt = realize(&site.complex, &site.program, &mut carrier, &BTreeMap::new())
        .map_err(|error| error.to_string())?;
    Ok(site
        .returns
        .iter()
        .map(|event| receipt.carried[&OccurrencePort::output(*event, 0)].clone())
        .collect())
}

/// **The inner argument the source's `hidden_activation` declares**, read exactly.
///
/// `config.json` names `gelu_pytorch_tanh`, whose implementation computes
/// `½x(1 + tanh(s·(x + c·x³)))` with `s` and `c` as `binary64` words. The source does not compute
/// `sqrt(2/pi)` at conduct time; it computes with one particular stored word. That word is read here
/// through the standing IEEE-754 mouth — **from its bits, so no float arithmetic occurs anywhere** —
/// which makes this `SourceTestimony::Implementation` rather than an approximation of one.
pub fn gelu_inner() -> (Rat, Rat) {
    let read = |bits: u64| {
        decode_binary64_bits(bits)
            .expect("a finite stored word")
            .value()
    };
    (read(0x3FE9_8845_33D4_3651), read(0x3FA6_E4E2_6D48_01F7))
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
        .carries_precedence(
            name,
            boundary,
            OccurrencePort::output(source, 0),
            OccurrencePort::input(target, input),
        )
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
    let l = law(
        complex,
        name.clone(),
        OperationSpecies::Quotient,
        vec![from],
        vec![to],
    );
    let event = complex.occur(l).map_err(|e| e.to_string())?;
    program.bind(event, PortedOperationKind::GrainBoundary);
    join(complex, name, from, source, event, 0)?;
    Ok(event)
}

// ---------------------------------------------------------------------------------------------
// THE NATIVE SIDE: a carrier that holds NO source handle, and the container writer it reads back.
// ---------------------------------------------------------------------------------------------

// ---------------------------------------------------------------------------------------------
// THE NATIVE CARRIER. It holds no source path, so the code path to the source does not exist.
// ---------------------------------------------------------------------------------------------

pub struct NativeRestCarrier<'chart> {
    pub chart: &'chart ResidentReadout,
    pub container: holonic_engine::foreign_map::ForeignContainer,
    pub file: std::fs::File,
    pub bands: BTreeMap<String, Vec<(ExactInterval, ExactInterval)>>,
    pub below_the_frame: usize,
    /// **Residency**, for the same reason the source-fed carrier has it: an invariant operand is
    /// mounted once and scored again, never re-uploaded per occurrence.
    pub resident: BTreeMap<String, MountedReadout<'chart>>,
    pub reused: usize,
}

/// Read off the carrier and the diagram, exactly as the source-fed conduct reads it.

impl PortedCarrier for NativeRestCarrier<'_> {
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
        let query = holonic_engine::embedding_fiber::align_bfloat16(&words)
            .map_err(|e| format!("{e:?}"))?;
        if self.resident.contains_key(population) {
            self.reused += 1;
        } else {
            let stored = self
                .container
                .read_bf16_whole(&mut self.file, population)
                .map_err(|error| error.to_string())?;
            let mounted = self
                .chart
                .mount_bfloat16(&stored, tensor.shape[1])
                .map_err(|e| format!("{e:?}"))?;
            self.resident.insert(population.to_owned(), mounted);
        }
        let scored = self.resident[population]
            .score_many(&[&query])
            .map_err(|e| format!("{e:?}"))?;
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

    /// **The sealed rest carries only the rows the diagram named, not the whole table.**
    ///
    /// So a lookup's row index is relocated at the seal and read here against the sealed
    /// population's own extent. The rest is smaller than the source by exactly the rows no caused
    /// material excited — which are `unexcited`, not condensed, and no factor is quoted for them.
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
        self.bands
            .get(population)
            .cloned()
            .ok_or_else(|| format!("the rest carries no band population named {population}"))
    }

    fn grain(&mut self, standing: &[Rat]) -> Result<(Vec<Rat>, Vec<Rat>), String> {
        let mut rounded = Vec::with_capacity(standing.len());
        let mut residual = Vec::with_capacity(standing.len());
        for value in standing {
            let (word, remainder) = round_into_bfloat16(value).map_err(|e| format!("{e:?}"))?;
            let datum = decode_bfloat16_bits(word).map_err(|e| format!("{e:?}"))?;
            rounded.push((
                datum.value(),
                datum.ulp_exponent,
                datum.significand.bits() == 0,
            ));
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

/// Write a container in the species the source arrived in, so the standing mouth reads it back.
pub fn write_container(
    path: &str,
    header: &[(String, (String, Vec<usize>, u64, u64))],
    metadata: &BTreeMap<String, String>,
    payload: &[u8],
) {
    let mut map = serde_json::Map::new();
    map.insert(
        "__metadata__".to_owned(),
        serde_json::to_value(metadata).expect("metadata"),
    );
    for (name, (dtype, shape, start, end)) in header {
        let mut entry = serde_json::Map::new();
        entry.insert("dtype".to_owned(), serde_json::json!(dtype));
        entry.insert("shape".to_owned(), serde_json::json!(shape));
        entry.insert("data_offsets".to_owned(), serde_json::json!([start, end]));
        map.insert(name.clone(), serde_json::Value::Object(entry));
    }
    let text = serde_json::to_string(&serde_json::Value::Object(map)).expect("header");
    let mut file = std::fs::File::create(path).expect("create");
    file.write_all(&(text.len() as u64).to_le_bytes())
        .expect("length");
    file.write_all(text.as_bytes()).expect("header");
    file.write_all(payload).expect("payload");
}

/// A digest declares which byte occurrence was read. It is a frame declaration, never an identity.
pub fn digest_of(path: &str) -> String {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(std::fs::read(path).expect("read"));
    hasher
        .finalize()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
