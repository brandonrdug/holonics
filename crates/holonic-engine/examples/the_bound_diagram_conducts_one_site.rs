//! **Phoenix station three: the bound diagram conducts one site on caused material.**
//!
//! Plan: `blueprint/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md`.
//! Derivation:
//! `research/records/2026-08-18_THE_HOLON_IS_THE_OPERATION_COMPLEX_THE_FOREIGN_MAP_IS_A_PORTED_WORD_AND_THE_CARD_CARRIES_ITS_FRONTS.md`
//! §12.3 — *"Enact the real branch/join diagram … **No source-specific semantic scheduler.**"*
//!
//! # There is no scheduler here, and there is nowhere to put one
//!
//! This driver **binds** and hands over. It declares ports, laws, occurrences and bonds; it binds
//! each occurrence to an exact operation; it supplies a [`PortedCarrier`]. Then it calls
//! `ported_operation::realize` **once**.
//!
//! Every ordering question is answered by `CausalDiagram::layers` inside that call, and every
//! dataflow question by the diagram's own interaction bonds. This file contains no loop over
//! operations, no sequence of applications, and no knowledge of what runs before what — a previous
//! attempt hand-wrote that order in a driver and was withdrawn for it.
//!
//! # The apparatus seam
//!
//! The carrier below owns the card and the source mouth; the bridge owns neither. A contraction
//! goes to the strongest lawful resident surface and a stored population comes from the source's
//! own mouth, and a diagram knows about neither.
//!
//! ```text
//! cargo run --release -q -p holonic-engine \
//!   --example the_bound_diagram_conducts_one_site -- /home/b/models/gemma-4-E4B-it
//! ```

use std::collections::BTreeMap;
use std::fs::File;
use std::time::Instant;

use holonic_engine::category::BoundaryId;
use holonic_engine::causal::EventId;
use holonic_engine::embedding_fiber::{align_bfloat16, ResidentReadout};
use holonic_engine::exact_value::ieee754::{decode_bfloat16_bits, round_into_bfloat16};
use holonic_engine::foreign_map::{manifest_safetensors, ForeignContainer};
use holonic_engine::interaction::OccurrencePort;
use holonic_engine::ported_operation::{
    realize, OperationSpecies, PortedCarrier, PortedOperationComplex, PortedOperationKind,
    PortedProgram, SourceTestimony,
};
use num_bigint::BigInt;
use num_traits::Zero;
use relational_geometry::Rat;

const SITE: usize = 0;
const SYMBOLS: &str = "model.language_model.embed_tokens.weight";
/// Two caused symbols, delivered by the source's own codec: `The` and `receiver`.
const CAUSED: [usize; 2] = [818, 18_740];
/// **One member of the open candidate populations station one returned.**
///
/// A sibling differs from the base in exactly one relation, which is what makes a separation
/// attributable. Nothing here selects; the receiver separation below decides which questions are
/// real and which are moot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Candidate {
    name: &'static str,
    gain_carries_unit: bool,
    pairs_halves: bool,
    scale_contact: bool,
}

impl Candidate {
    const BASE: Self = Self {
        name: "base",
        gain_carries_unit: false,
        pairs_halves: true,
        scale_contact: true,
    };
    fn contact_scale_width(&self, chart_width: usize) -> usize {
        if self.scale_contact { chart_width } else { 1 }
    }
}

fn named(suffix: &str) -> String {
    format!("model.language_model.layers.{SITE}.{suffix}")
}

// ---------------------------------------------------------------------------------------------
// THE APPARATUS. The bridge owns none of this.
// ---------------------------------------------------------------------------------------------

struct ResidentSourceCarrier<'chart> {
    chart: &'chart ResidentReadout,
    container: ForeignContainer,
    file: File,
    contractions: usize,
    stored_octets: u64,
    grain_crossings: usize,
    below_the_frame: usize,
}

/// The octaves the exact aligned carrier admits between a section's top entry and its smallest.
///
/// **Read off the carrier and the stored grain together, not chosen.** A signed word holds
/// sixty-three magnitude octaves; a `BF16` significand occupies eight of them; alignment shifts an
/// entry up by its own distance from the common exponent. So the admissible spread is `63 - 8`, and
/// fifty-four would leave one octave of margin for the ALIGNMENT alone. Measured 2026-08-18, an
/// earlier reading of sixty-two was refused by name:
/// `AlignmentOverflows { octaves: 8, spread: 57, needed: 65, carrier: 63 }`.
///
/// But the binding contraction is wider than the alignment. An exact `d`-term contraction of
/// `b`-octave entries needs `2b + ceil(log2 d) + 1` octaves against a `128`-octave carrier, and the
/// widest contraction this diagram performs is `d = 10240`. So `2(reach + 8) + 14 + 1 <= 128` gives
/// `reach <= 48`, and forty-six leaves two octaves of margin. That was also refused by name before
/// it was read: `CarrierTooNarrow { dim: 10240, entry_octaves: 62, needed: 139, carrier: 128 }`.
///
/// **Both bounds are read off the carrier and the diagram, never chosen for a result.**
const CARRIER_REACH: i32 = 46;

impl ResidentSourceCarrier<'_> {
    fn exact(&self, words: &[u16]) -> Vec<Rat> {
        words
            .iter()
            .map(|word| decode_bfloat16_bits(*word).expect("finite").value())
            .collect()
    }
}

impl PortedCarrier for ResidentSourceCarrier<'_> {
    fn contract(&mut self, population: &str, standing: &[Rat]) -> Result<Vec<Rat>, String> {
        let tensor = self
            .container
            .tensor(population)
            .map_err(|error| error.to_string())?
            .clone();
        if tensor.shape.len() != 2 || tensor.shape[1] != standing.len() {
            return Err(format!(
                "{population} declares {:?} and the standing is {}",
                tensor.shape,
                standing.len()
            ));
        }
        // The standing arrives already grained, so this crossing is lossless and says so.
        let mut words = Vec::with_capacity(standing.len());
        for value in standing {
            let (word, residual) = round_into_bfloat16(value).map_err(|e| format!("{e:?}"))?;
            if !residual.is_zero() {
                return Err(
                    "a contraction was handed an ungrained standing; the diagram owes a grain \
                     boundary before it"
                        .to_owned(),
                );
            }
            words.push(word);
        }
        let query = align_bfloat16(&words).map_err(|e| format!("{e:?}"))?;
        let stored = self
            .container
            .read_bf16_whole(&mut self.file, population)
            .map_err(|error| error.to_string())?;
        self.stored_octets += (stored.len() * 2) as u64;
        let mounted = self
            .chart
            .mount_bfloat16(&stored, tensor.shape[1])
            .map_err(|e| format!("{e:?}"))?;
        let population_scores = mounted.score_many(&[&query]).map_err(|e| format!("{e:?}"))?;
        self.contractions += 1;
        let scores = &population_scores[0];
        let unit = two_to(scores.readout_exponent as i64 + scores.query_exponent as i64);
        Ok((0..tensor.shape[0])
            .map(|row| Rat::from_integer(scores.exact(row).unwrap_or_else(BigInt::zero)) * &unit)
            .collect())
    }

    fn stored(&mut self, population: &str) -> Result<Vec<Rat>, String> {
        let words = self
            .container
            .read_bf16_whole(&mut self.file, population)
            .map_err(|error| error.to_string())?;
        Ok(self.exact(&words))
    }

    fn stored_row(&mut self, population: &str, row: usize) -> Result<Vec<Rat>, String> {
        let (words, _) = self
            .container
            .read_rows_bf16(&mut self.file, population, row, 1)
            .map_err(|error| error.to_string())?;
        Ok(self.exact(&words))
    }

    /// **The declared quotient, with the frame it can cross stated.**
    ///
    /// Rounding onto the stored grain is only half of it. The exact carrier aligns a whole section
    /// onto ONE common exponent, so an entry more than sixty-three octaves below the section's own
    /// top cannot cross that frame at all — and this material really does span eighty-eight after a
    /// gated passage, measured 2026-08-18 by the refusal `AlignmentSpread { spread: 88 }`.
    ///
    /// So the aperture is declared here and what falls below it is **retained whole** rather than
    /// carried as something it is not. That is the horizon law: what cannot cross the frame is
    /// kept, not approximated across it.
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
                // Below the frame this carrier can cross: retained whole.
                residual[at] = standing[at].clone();
                self.below_the_frame += 1;
                carried.push(Rat::from_integer(BigInt::from(0)));
            } else {
                carried.push(value);
            }
        }
        self.grain_crossings += standing.len();
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

fn main() {
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/b/models/gemma-4-E4B-it".to_owned());
    let candidate = Candidate::BASE;
    let terms: usize = std::env::var("TERMS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(24);

    let (file, container) = match manifest_safetensors(&format!("{root}/model.safetensors")) {
        Ok(pair) => pair,
        Err(error) => {
            println!("the source refused: {error}");
            std::process::exit(1);
        }
    };
    let chart = match ResidentReadout::new() {
        Ok(chart) => chart,
        Err(error) => {
            println!("the resident chart refused: {error:?}");
            println!("The admitted hot deed returns a typed refusal. No CPU answer appears.");
            std::process::exit(1);
        }
    };

    println!("PHOENIX STATION THREE — THE BOUND DIAGRAM CONDUCTS");
    println!();
    println!("  resident chart                    {}", chart.device_name());

    let chart_width = container
        .tensor(&named("self_attn.q_norm.weight"))
        .expect("manifested")
        .shape[0];
    let receivers = container
        .tensor(&named("self_attn.q_proj.weight"))
        .expect("manifested")
        .shape[0]
        / chart_width;
    let families = container
        .tensor(&named("self_attn.k_proj.weight"))
        .expect("manifested")
        .shape[0]
        / chart_width;
    let construction_width = container.tensor(SYMBOLS).expect("manifested").shape[1];

    // -----------------------------------------------------------------------------------------
    // THE BINDING. Ports, laws, occurrences, bonds. No order is stated anywhere below.
    // -----------------------------------------------------------------------------------------
    let mut complex = PortedOperationComplex::new("gemma site zero, two caused positions");
    let standing = complex.port("continuing standing");
    let grained = complex.port("grained standing");
    let receiver_wide = complex.port("receiver chart, all heads");
    let presented_wide = complex.port("presented chart, all families");
    let carried_wide = complex.port("carried chart, all families");
    let receiver_head = complex.port("one receiver chart");
    let presented_head = complex.port("one presented chart");
    let carried_head = complex.port("one carried chart");
    let intermediate = complex.port("intermediate chart");

    let shape_of = |name: &str| -> Vec<SourceTestimony> {
        container
            .tensor(name)
            .map(|tensor| {
                vec![SourceTestimony::DeclaredShape {
                    population: name.to_owned(),
                    shape: tensor.shape.clone(),
                }]
            })
            .unwrap_or_default()
    };

    // **The band ladder is standing material of the site, founded ONCE.** One certified root of
    // degree `bands`, then a geometric progression. Re-founding it per occurrence put a Sturm
    // isolation of a degree-128 polynomial inside the hot path.
    let bands = chart_width / 2;
    let ladder: Vec<Rat> = {
        let ratio = holonic_engine::exact_value::AlgebraicRoot::nth_root(
            &Rat::from_integer(BigInt::from(10_000)),
            bands as u32,
            44,
        )
        .expect("isolated")
        .enclosure()
        .reciprocal()
        .expect("positive");
        let two = Rat::from_integer(BigInt::from(2));
        let mut angles: Vec<Rat> = Vec::with_capacity(bands);
        let mut current = holonic_engine::exact_value::ExactInterval::point(Rat::from_integer(BigInt::from(1)));
        for _ in 0..bands {
            angles.push((&current.lower + &current.upper) / &two);
            // Held outward on a dyadic grid at every step. Without it the ladder's denominators
            // reach five thousand six hundred bits and a series on each is the whole cost.
            current = current
                .times(&ratio)
                .expect("in the carrier")
                .round_out(40)
                .expect("held");
        }
        angles
    };
    // **The band group elements, founded ONCE.** `R(p a) = R(a)^p`, so the transcendental runs here
    // and a position spends only multiplication. Founding them per occurrence cost a quarter of a
    // second an occurrence for a value that does not change.
    let rotations: Vec<(
        holonic_engine::exact_value::ExactInterval,
        holonic_engine::exact_value::ExactInterval,
    )> = ladder
        .iter()
        .map(|angle| {
            let (cosine, sine) =
                holonic_engine::exact_value::CertifiedSeries::circular_series(angle, terms)
                    .expect("in the unit domain");
            (
                cosine.enclosure().round_out(40).expect("held"),
                sine.enclosure().round_out(40).expect("held"),
            )
        })
        .collect();

    let mut program = PortedProgram::default();
    let mut entering_events: Vec<EventId> = Vec::new();
    let mut turned_presented: Vec<Vec<EventId>> = Vec::new();
    let mut carried_heads: Vec<Vec<EventId>> = Vec::new();
    let mut successors: Vec<EventId> = Vec::new();

    for (position, symbol) in CAUSED.iter().enumerate() {
        let tag = |what: &str| format!("position {position} {what}");

        // The entering construction, then the declared grain.
        let lookup = bind(
            &mut complex,
            tag("entering construction"),
            OperationSpecies::Construction,
            vec![],
            vec![standing],
            Some(SYMBOLS.to_owned()),
            shape_of(SYMBOLS),
        );
        let lookup_event = complex.occur(lookup).expect("occurs");
        program.bind(
            lookup_event,
            PortedOperationKind::Lookup {
                population: SYMBOLS.to_owned(),
                row: *symbol,
            },
        );

        let entering_grain = grain_after(
            &mut complex,
            &mut program,
            tag("entering grain"),
            standing,
            grained,
            lookup_event,
        );
        entering_events.push(entering_grain);

        // The entering rebase, then a grain before the front.
        let rebase = bind(
            &mut complex,
            tag("entering rebase"),
            OperationSpecies::Transport,
            vec![grained],
            vec![standing],
            Some(named("input_layernorm.weight")),
            shape_of(&named("input_layernorm.weight")),
        );
        let rebase_event = complex.occur(rebase).expect("occurs");
        program.bind(
            rebase_event,
            PortedOperationKind::RebaseByGain {
                population: named("input_layernorm.weight"),
                floor: Rat::new(BigInt::from(1), BigInt::from(1_000_000)),
                gain_carries_unit: candidate.gain_carries_unit,
            },
        );
        join(&mut complex, tag("rebase admits"), grained, entering_grain, rebase_event, 0);
        let front_grain = grain_after(
            &mut complex,
            &mut program,
            tag("front grain"),
            standing,
            grained,
            rebase_event,
        );

        // THE FIRST FRONT: three co-present branches of one predecessor.
        let mut branches = Vec::new();
        for (what, suffix, port) in [
            ("receiver projection", "self_attn.q_proj.weight", receiver_wide),
            ("presented projection", "self_attn.k_proj.weight", presented_wide),
            ("carried projection", "self_attn.v_proj.weight", carried_wide),
        ] {
            let carrier = named(suffix);
            let law = bind(
                &mut complex,
                tag(what),
                OperationSpecies::Transport,
                vec![grained],
                vec![port],
                Some(carrier.clone()),
                shape_of(&carrier),
            );
            let event = complex.occur(law).expect("occurs");
            program.bind(event, PortedOperationKind::Contract { population: carrier });
            join(&mut complex, tag(what), grained, front_grain, event, 0);
            branches.push((event, port));
        }

        // EVERY receiver chart of the front, each by a projection whose retained fibre is exactly
        // what it dropped. The presented and carried families are projected once each and shared,
        // which is what "unified Keys and Values" means at this site.
        let mut presented_heads_here = Vec::new();
        let mut carried_heads_here = Vec::new();
        for family in 0..families {
            for (what, (source, wide), narrow, held) in [
                (
                    format!("presented head {family}"),
                    branches[1],
                    presented_head,
                    &mut presented_heads_here,
                ),
                (
                    format!("carried head {family}"),
                    branches[2],
                    carried_head,
                    &mut carried_heads_here,
                ),
            ] {
                let law = bind(
                    &mut complex,
                    tag(&what),
                    OperationSpecies::Quotient,
                    vec![wide],
                    vec![narrow],
                    None,
                    vec![SourceTestimony::Configuration {
                        field: "num_key_value_heads".to_owned(),
                        value: families.to_string(),
                    }],
                );
                let event = complex.occur(law).expect("occurs");
                program.bind(
                    event,
                    PortedOperationKind::Project {
                        from: family * chart_width,
                        count: chart_width,
                    },
                );
                join(&mut complex, tag(&what), wide, source, event, 0);
                held.push(event);
            }
        }
        // The presented charts turn; the carried do not, because a chronology acts on an
        // orientation and not on a construction.
        let mut turned_presented_here = Vec::new();
        for (family, source) in presented_heads_here.iter().enumerate() {
            let what = format!("presented chart {family}");
            let carrier = named("self_attn.k_norm.weight");
            let law = bind(
                &mut complex,
                tag(&format!("{what} rebase")),
                OperationSpecies::Transport,
                vec![presented_head],
                vec![presented_head],
                Some(carrier.clone()),
                shape_of(&carrier),
            );
            let event = complex.occur(law).expect("occurs");
            program.bind(
                event,
                PortedOperationKind::RebaseByGain {
                    population: carrier,
                    floor: Rat::new(BigInt::from(1), BigInt::from(1_000_000)),
                    gain_carries_unit: candidate.gain_carries_unit,
                },
            );
            join(&mut complex, tag(&what), presented_head, *source, event, 0);
            let chronology = bind(
                &mut complex,
                tag(&format!("{what} chronology")),
                OperationSpecies::Transport,
                vec![presented_head],
                vec![presented_head],
                None,
                vec![SourceTestimony::AuthoritativeDescription {
                    statement: "global layers feature unified Keys and Values, and apply \
                                Proportional RoPE (p-RoPE)"
                        .to_owned(),
                }],
            );
            let turn_event = complex.occur(chronology).expect("occurs");
            program.bind(
                turn_event,
                PortedOperationKind::Chronology {
                    rotations: rotations.clone(),
                    position: position as u64,
                    pairs_halves: candidate.pairs_halves,
                },
            );
            join(&mut complex, tag(&format!("{what} turns")), presented_head, event, turn_event, 0);
            turned_presented_here.push(turn_event);
        }
        turned_presented.push(turned_presented_here);
        carried_heads.push(carried_heads_here);

        // Every receiver chart: projected, rebased, turned, and contacted against its family.
        let mut carried_parts = Vec::with_capacity(receivers);
        for head in 0..receivers {
            let family = head / (receivers / families.max(1)).max(1);
            let what = format!("receiver chart {head}");
            let law = bind(
                &mut complex,
                tag(&what),
                OperationSpecies::Quotient,
                vec![receiver_wide],
                vec![receiver_head],
                None,
                vec![SourceTestimony::Configuration {
                    field: "num_attention_heads".to_owned(),
                    value: receivers.to_string(),
                }],
            );
            let projected = complex.occur(law).expect("occurs");
            program.bind(
                projected,
                PortedOperationKind::Project {
                    from: head * chart_width,
                    count: chart_width,
                },
            );
            join(&mut complex, tag(&what), receiver_wide, branches[0].0, projected, 0);

            let carrier = named("self_attn.q_norm.weight");
            let law = bind(
                &mut complex,
                tag(&format!("{what} rebase")),
                OperationSpecies::Transport,
                vec![receiver_head],
                vec![receiver_head],
                Some(carrier.clone()),
                shape_of(&carrier),
            );
            let rebased = complex.occur(law).expect("occurs");
            program.bind(
                rebased,
                PortedOperationKind::RebaseByGain {
                    population: carrier,
                    floor: Rat::new(BigInt::from(1), BigInt::from(1_000_000)),
                    gain_carries_unit: candidate.gain_carries_unit,
                },
            );
            join(&mut complex, tag(&format!("{what} rebase")), receiver_head, projected, rebased, 0);

            let law = bind(
                &mut complex,
                tag(&format!("{what} chronology")),
                OperationSpecies::Transport,
                vec![receiver_head],
                vec![receiver_head],
                None,
                vec![SourceTestimony::AuthoritativeDescription {
                    statement: "a position is an integer power of one group element".to_owned(),
                }],
            );
            let turned = complex.occur(law).expect("occurs");
            program.bind(
                turned,
                PortedOperationKind::Chronology {
                    rotations: rotations.clone(),
                    position: position as u64,
                    pairs_halves: candidate.pairs_halves,
                },
            );
            join(&mut complex, tag(&format!("{what} turns")), receiver_head, rebased, turned, 0);

            // THE CONTACT. Its reach is every retained position up to this one, and the DIAGRAM
            // declares it: the law's arity is 1 + 2n and the bonds carry each member.
            let reach = position + 1;
            let mut inputs = vec![receiver_head];
            inputs.extend(std::iter::repeat_n(presented_head, reach));
            inputs.extend(std::iter::repeat_n(carried_head, reach));
            let law = bind(
                &mut complex,
                tag(&format!("{what} contact and carry")),
                OperationSpecies::Construction,
                inputs,
                vec![carried_head],
                None,
                vec![SourceTestimony::AuthoritativeDescription {
                    statement: "a carried construction is a convex combination and lies inside its \
                                population's hull"
                        .to_owned(),
                }],
            );
            let contact = complex.occur(law).expect("occurs");
            program.bind(
                contact,
                PortedOperationKind::ContactAndCarry {
                    terms,
                    scale_width: candidate.contact_scale_width(chart_width),
                },
            );
            join(&mut complex, tag(&format!("{what} contact receiver")), receiver_head, turned, contact, 0);
            for at in 0..reach {
                join(
                    &mut complex,
                    tag(&format!("{what} contact presented {at}")),
                    presented_head,
                    turned_presented[at][family],
                    contact,
                    1 + at,
                );
                join(
                    &mut complex,
                    tag(&format!("{what} contact carried {at}")),
                    carried_head,
                    carried_heads[at][family],
                    contact,
                    1 + reach + at,
                );
            }
            carried_parts.push(contact);
        }

        // THE FRONT RECONVERGES: eight carried charts assemble into one standing.
        let law = bind(
            &mut complex,
            tag("carried reconvergence"),
            OperationSpecies::Construction,
            vec![carried_head; receivers],
            vec![carried_wide],
            None,
            vec![SourceTestimony::AuthoritativeDescription {
                statement: "the front's breadth is the diagram's, and its parts assemble in bond \
                            order"
                    .to_owned(),
            }],
        );
        let assembled = complex.occur(law).expect("occurs");
        program.bind(assembled, PortedOperationKind::Concatenate);
        for (at, part) in carried_parts.iter().enumerate() {
            join(
                &mut complex,
                tag(&format!("reconvergence admits part {at}")),
                carried_head,
                *part,
                assembled,
                at,
            );
        }

        // The return, its grain, and the reconvergence.
        let contact_grain = grain_after(
            &mut complex,
            &mut program,
            tag("contact grain"),
            carried_wide,
            carried_wide,
            assembled,
        );
        let carrier = named("self_attn.o_proj.weight");
        let law = bind(
            &mut complex,
            tag("contact return"),
            OperationSpecies::Transport,
            vec![carried_wide],
            vec![standing],
            Some(carrier.clone()),
            shape_of(&carrier),
        );
        let returning_event = complex.occur(law).expect("occurs");
        program.bind(returning_event, PortedOperationKind::Contract { population: carrier });
        join(&mut complex, tag("return admits"), carried_wide, contact_grain, returning_event, 0);

        let law = bind(
            &mut complex,
            tag("contact return rebase"),
            OperationSpecies::Transport,
            vec![standing],
            vec![standing],
            Some(named("post_attention_layernorm.weight")),
            shape_of(&named("post_attention_layernorm.weight")),
        );
        let return_rebase = complex.occur(law).expect("occurs");
        program.bind(
            return_rebase,
            PortedOperationKind::RebaseByGain {
                population: named("post_attention_layernorm.weight"),
                floor: Rat::new(BigInt::from(1), BigInt::from(1_000_000)),
                gain_carries_unit: candidate.gain_carries_unit,
            },
        );
        join(&mut complex, tag("return rebase admits"), standing, returning_event, return_rebase, 0);

        let reentry = bind(
            &mut complex,
            tag("contact re-entry"),
            OperationSpecies::Construction,
            vec![grained, standing],
            vec![standing],
            None,
            vec![SourceTestimony::AuthoritativeDescription {
                statement: "a residual re-entry admits two paths: the retained standing and the \
                            returned delta"
                    .to_owned(),
            }],
        );
        let reentry_event = complex.occur(reentry).expect("occurs");
        program.bind(reentry_event, PortedOperationKind::ReEntry);
        join(&mut complex, tag("re-entry retains"), grained, entering_grain, reentry_event, 0);
        join(&mut complex, tag("re-entry admits"), standing, return_rebase, reentry_event, 1);

        // THE SECOND FRONT and the constitutive passage.
        let constitutive_grain = grain_after(
            &mut complex,
            &mut program,
            tag("constitutive grain"),
            standing,
            grained,
            reentry_event,
        );
        let mut second = Vec::new();
        for (what, suffix) in [
            ("gate projection", "mlp.gate_proj.weight"),
            ("raise projection", "mlp.up_proj.weight"),
        ] {
            let carrier = named(suffix);
            let law = bind(
                &mut complex,
                tag(what),
                OperationSpecies::Transport,
                vec![grained],
                vec![intermediate],
                Some(carrier.clone()),
                shape_of(&carrier),
            );
            let event = complex.occur(law).expect("occurs");
            program.bind(event, PortedOperationKind::Contract { population: carrier });
            join(&mut complex, tag(what), grained, constitutive_grain, event, 0);
            second.push(event);
        }
        let passage = bind(
            &mut complex,
            tag("gated passage"),
            OperationSpecies::Transport,
            vec![intermediate],
            vec![intermediate],
            None,
            vec![SourceTestimony::Configuration {
                field: "hidden_activation".to_owned(),
                value: "gelu_pytorch_tanh".to_owned(),
            }],
        );
        let passage_event = complex.occur(passage).expect("occurs");
        program.bind(passage_event, PortedOperationKind::GatedPassage { terms });
        join(&mut complex, tag("passage admits"), intermediate, second[0], passage_event, 0);

        let mixed = bind(
            &mut complex,
            tag("gated product"),
            OperationSpecies::Construction,
            vec![intermediate, intermediate],
            vec![intermediate],
            None,
            vec![SourceTestimony::AuthoritativeDescription {
                statement: "the two co-present branches meet pointwise".to_owned(),
            }],
        );
        let mixed_event = complex.occur(mixed).expect("occurs");
        program.bind(mixed_event, PortedOperationKind::Hadamard);
        join(&mut complex, tag("product admits gate"), intermediate, passage_event, mixed_event, 0);
        join(&mut complex, tag("product admits raise"), intermediate, second[1], mixed_event, 1);

        let lowering_grain = grain_after(
            &mut complex,
            &mut program,
            tag("lowering grain"),
            intermediate,
            intermediate,
            mixed_event,
        );
        let lowering = bind(
            &mut complex,
            tag("constitutive return"),
            OperationSpecies::Transport,
            vec![intermediate],
            vec![standing],
            Some(named("mlp.down_proj.weight")),
            shape_of(&named("mlp.down_proj.weight")),
        );
        let lowering_event = complex.occur(lowering).expect("occurs");
        program.bind(
            lowering_event,
            PortedOperationKind::Contract {
                population: named("mlp.down_proj.weight"),
            },
        );
        join(&mut complex, tag("lowering admits"), intermediate, lowering_grain, lowering_event, 0);

        let constitutive_reentry = bind(
            &mut complex,
            tag("constitutive re-entry"),
            OperationSpecies::Construction,
            vec![standing, standing],
            vec![standing],
            None,
            vec![SourceTestimony::AuthoritativeDescription {
                statement: "the second reconvergence of this site".to_owned(),
            }],
        );
        let successor = complex.occur(constitutive_reentry).expect("occurs");
        program.bind(successor, PortedOperationKind::ReEntry);
        join(&mut complex, tag("successor retains"), standing, reentry_event, successor, 0);
        join(&mut complex, tag("successor admits"), standing, lowering_event, successor, 1);
        successors.push(successor);
    }

    let closure = complex.closure().expect("validated");
    println!();
    println!("  THE BINDING");
    println!("    typed ports                     {}", closure.ports);
    println!("    bound operations                {}", closure.operations);
    println!("    occurrences                     {}", closure.occurrences);
    println!("    CO-PRESENT FRONTS               {}", closure.fronts);
    println!("    species census:");
    for (species, count) in complex.species_census() {
        println!("        {:<14} {count}", species.name());
    }
    match program.validate(&complex) {
        Ok(()) => println!("    the program VALIDATES against the diagram"),
        Err(error) => {
            println!("    the program REFUSED: {error}");
            std::process::exit(1);
        }
    }
    println!("    construction width              {construction_width}");
    println!("    one chart's width               {chart_width}");
    println!("    receiver charts / families      {receivers} / {families}");
    println!("    chronology bands, founded once  {bands}");

    // -----------------------------------------------------------------------------------------
    // THE HANDOVER. One call. The chronology decides everything after this line.
    // -----------------------------------------------------------------------------------------
    let mut carrier = ResidentSourceCarrier {
        chart: &chart,
        container,
        file,
        contractions: 0,
        stored_octets: 0,
        grain_crossings: 0,
        below_the_frame: 0,
    };
    println!();
    println!("  THE HANDOVER — one call to `realize`; no order is stated in this driver");
    let clock = Instant::now();
    let receipt = match realize(&complex, &program, &mut carrier, &BTreeMap::new()) {
        Ok(receipt) => receipt,
        Err(error) => {
            println!("    the realization REFUSED: {error}");
            println!("    A refusal is the return. Nothing is substituted for it.");
            std::process::exit(1);
        }
    };
    let spent = clock.elapsed();

    println!();
    println!("THE SITE'S RETURN");
    println!();
    println!("  fronts conducted, in the chronology's order  {}", receipt.fronts.len());
    println!("  occurrence ports written                     {}", receipt.ports_written());
    println!("  resident contractions                        {}", carrier.contractions);
    println!("  stored codewords across the bus              {} octets", carrier.stored_octets);
    println!("  declared grain crossings                     {}", carrier.grain_crossings);
    println!("  entries BELOW THE FRAME, retained whole      {}", carrier.below_the_frame);
    println!("  conducted in                                 {spent:?}");
    println!();
    println!("  EXACT WORK, counted rather than timed:");
    for (name, count) in receipt.work.coordinates() {
        println!("      {name:<28} {count}");
    }
    println!();
    println!("  THE RETAINED FIBRE — exhibited per occurrence, never propagated");
    println!("    occurrences that retained something        {}", receipt.retained.len());
    let (retained_entries, retained_nonzero, widest) = receipt.retained_population();
    println!("    entries retained                           {retained_entries}");
    println!("    of those, genuinely nonzero                {retained_nonzero}");
    if let Some((occurrence, value)) = widest {
        println!(
            "    the widest single residual, at {occurrence:?}   {}",
            shorten(&value.to_string(), 40)
        );
    }
    println!();
    for (position, successor) in successors.iter().enumerate() {
        let section = &receipt.carried[&OccurrencePort::output(*successor, 0)];
        println!(
            "  position {position} successor, width {}, first three coordinates exactly:",
            section.len()
        );
        for value in section.iter().take(3) {
            println!("      {}", shorten(&value.to_string(), 60));
        }
    }

    println!();
    println!("THE STATION'S VERDICT");
    println!();
    println!("  The diagram conducted. Its chronology ordered every occurrence and its bonds");
    println!("  carried every standing; this driver stated no order and could not have.");
    println!("  The card carried every contraction and refused nothing to a serial fallback.");
    println!("  Every projection, grain boundary, rebase, chronology and contact retained what it");
    println!("  could not carry, at its own occurrence.");
    println!();
    println!("  This is ONE site of forty-two on ONE receiver chart of eight. No candidate");
    println!("  composition is selected and CONSTRUCTION_STATE is untouched.");
}

// ---------------------------------------------------------------------------------------------

fn bind(
    complex: &mut PortedOperationComplex,
    name: String,
    species: OperationSpecies,
    inputs: Vec<BoundaryId>,
    outputs: Vec<BoundaryId>,
    carrier: Option<String>,
    testimony: Vec<SourceTestimony>,
) -> holonic_engine::evolution::EvolutionLawId {
    complex
        .bind_operation(name, species, inputs, outputs, carrier, testimony)
        .expect("bound")
}

fn join(
    complex: &mut PortedOperationComplex,
    name: String,
    boundary: BoundaryId,
    source: EventId,
    target: EventId,
    input: usize,
) {
    complex
        .carries_precedence(
            name,
            boundary,
            OccurrencePort::output(source, 0),
            OccurrencePort::input(target, input),
        )
        .expect("joined");
}

/// A declared grain boundary after one occurrence. **The quotient is an occurrence in the diagram**,
/// not something a driver does between operations.
fn grain_after(
    complex: &mut PortedOperationComplex,
    program: &mut PortedProgram,
    name: String,
    from: BoundaryId,
    to: BoundaryId,
    source: EventId,
) -> EventId {
    let law = complex
        .bind_operation(
            name.clone(),
            OperationSpecies::Quotient,
            vec![from],
            vec![to],
            None,
            vec![SourceTestimony::AuthoritativeDescription {
                statement: "a declared quotient onto the stored grain, whose residual is exact"
                    .to_owned(),
            }],
        )
        .expect("bound");
    let event = complex.occur(law).expect("occurs");
    program.bind(event, PortedOperationKind::GrainBoundary);
    join(complex, name, from, source, event, 0);
    event
}

fn shorten(text: &str, extent: usize) -> String {
    if text.len() <= extent {
        return text.to_owned();
    }
    format!("{}…", &text[..extent])
}
