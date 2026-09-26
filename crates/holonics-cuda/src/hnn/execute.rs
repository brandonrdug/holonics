//! **One word executed on the card: its plan, its resident buffers, its launches and its record**
//! (kernels `hnn_pair_weights`, `hnn_word_forward`, `hnn_word_reverse`, `hnn_copy_words`;
//! `kernels/hnn_word.cuh`).
//!
//! [definition] A word's **plan** ([`WordPlan::form`]) is the host's declaration of every scale
//! and table the kernels read (the plan's layout is the kernels' `WP_*`, `WR_*`, `WC_*`, `WI_*`,
//! `WA_*`, `WS_*`, `WQ_*` words), formed from the field, the lift point at the word's cut, the
//! published loci ([`crate::hnn::publication`]) and the word's declared precisions: the junctions'
//! executed weights (`holonics::hnn::propagation::junction_weights` on `2^(−L_c)ℤ`), each contact's
//! conductance from its exponent's carry at the cut, and the rotations of the source and receiving
//! rings as gathers read off the host's own rotation (`Ring::rotate` of the index vector). It
//! refuses what the card's dyadic words cannot carry: a hop that is not a power of two (its
//! `ζ/h` would leave the dyadics), a non-dyadic admittance.
//!
//! [definition] A [`ResidentWord`] is one word's buffers on the card: its plan, its operands (the
//! junctions' weights and its own copies of its charts, gathered from the chart store's workspace in
//! one launch), and one buffer of its arrays (the carried change, the carried remainders, the
//! per-step record its balance and its return read, the logits, and its return's own arrays). Its
//! forward word is one launch and one read of its record ([`ForwardRecord`]); its return is one
//! write of the carried reads, one launch and one read ([`ReverseRecord`]). The word keeps its
//! record on the card between its refine and its compare (the kept read), and it holds the
//! publication it read, so its return reads the operators its forward executed.

use std::rc::Rc;

use core::ffi::c_void;

use holonics::hnn::propagation::{contact_exponent, junction_weights};
use holonics::hnn::{Current, Field, HnnError, ReceivingPhases, WordLattice};
use holonics::ratio::Rat;
use holonics::ratio::exponentiated::power_of_two as rat_power_of_two;
use num_bigint::BigInt;
use num_traits::ToPrimitive;

use crate::hnn::DeviceError;
use crate::hnn::card::{Card, CardBuffer, Layout, read_layout, word_layout};
use crate::hnn::dyadic::{power_of_two, reduced_word, refused, word};
use crate::hnn::moment::MomentSnapshot;
use crate::hnn::publication::Publication;
use crate::hnn::store::{ChartStore, Refined, copy_words};

pub const FORWARD_ENTRY: &str = "hnn_word_forward";
pub const REVERSE_ENTRY: &str = "hnn_word_reverse";
pub const PAIR_ENTRY: &str = "hnn_pair_weights";

fn device(error: DeviceError) -> HnnError {
    error.into_hnn()
}

// -------------------------------------------------------------------------------------------
// the plan's layout (the kernels' `WP_*` … words)

const WP_HEADER: usize = 31;
const WP_RINGS: usize = 0;
const WP_CONTACTS: usize = 1;
const WP_STEPS: usize = 2;
const WP_LC: usize = 3;
const WP_LW: usize = 4;
const WP_RING_ROWS: usize = 5;
const WP_ARRIVALS: usize = 6;
const WP_CONTACT_ROWS: usize = 7;
const WP_H_MUL: usize = 8;
const WP_H_SHIFT: usize = 9;
const WP_X_MUL: usize = 10;
const WP_X_SHIFT: usize = 11;
const WP_RING_TABLE: usize = 12;
const WP_CONTACT_TABLE: usize = 13;
const WP_INCIDENCE: usize = 14;
const WP_ROW_RING: usize = 15;
const WP_ROW_CONTACT: usize = 16;
const WP_ARRIVAL_TABLE: usize = 17;
const WP_RECEIVER: usize = 18;
const WP_EPOCH: usize = 19;
const WP_APERTURE: usize = 20;
const WP_MAP_ROWS: usize = 21;
const WP_GATHER: usize = 22;
const WP_SOURCES: usize = 23;
const WP_SOURCE_TABLE: usize = 24;
const WP_ALPHABET: usize = 25;
const WP_PAIR_TABLE: usize = 26;
const WP_INCIDENCES: usize = 27;
const WP_MAP: usize = 28;
const WP_HARMONIC: usize = 29;
const WP_HARMONIC_SHIFT: usize = 30;

const WR_STRIDE: usize = 12;
const WR_WIDTH: usize = 0;
const WR_ROWS: usize = 1;
const WR_CHART: usize = 2;
const WR_WC: usize = 3;
const WR_WC_EXP: usize = 4;
const WR_STORAGE_EXP: usize = 5;
const WR_DEGREE: usize = 6;
const WR_INCIDENCE: usize = 7;
const WR_WEIGHTS: usize = 8;
const WR_ANCHOR_EXP: usize = 9;

const WC_STRIDE: usize = 20;
const WC_WIDTH: usize = 0;
const WC_FROM: usize = 1;
const WC_TO: usize = 2;
const WC_ROWS: usize = 3;
const WC_ARRIVAL_FROM: usize = 4;
const WC_ARRIVAL_TO: usize = 5;
const WC_SELECTION: usize = 6;
const WC_CHART: usize = 7;
const WC_C: usize = 8;
const WC_C_EXP: usize = 9;
const WC_K: usize = 10;
const WC_K_EXP: usize = 11;
const WC_GAIN: usize = 12;
const WC_GAIN_EXP: usize = 13;
const WC_RIGHT_EXP: usize = 14;
const WC_RATE_GAIN: usize = 15;
const WC_RATE_GAIN_EXP: usize = 16;
const WC_SHIFT_GAIN: usize = 17;
const WC_SHIFT_GAIN_EXP: usize = 18;
const WC_ZETA_EXP: usize = 19;

const WS_STRIDE: usize = 9;
const WQ_STRIDE: usize = 8;

/// The word buffer's arrays, in the kernels' `WL_*` order.
const WL_ENTRIES: usize = 51;

// -------------------------------------------------------------------------------------------
// the scales the host decodes with

/// [definition] **One ring's plan, as the host reads its record**: its width and rows, its
/// incidence (contact, slot, arrival base) in the host's order, its junction weights' certificate
/// `‖ŵ − w‖₁`, its admittance and admittance sum, and its scales (the contrast port's `σ_Wc` when
/// live, the storage remainder's `ρ_s`, the return's anchor `σ_A`).
#[derive(Clone, Debug)]
pub(crate) struct RingPlan {
    pub(crate) width: usize,
    pub(crate) rows: usize,
    pub(crate) incident: Vec<(usize, usize, usize)>,
    pub(crate) certificate: Rat,
    pub(crate) admittance: Rat,
    pub(crate) total: Rat,
    pub(crate) contrast: Option<u32>,
    pub(crate) storage_exp: u32,
    pub(crate) anchor_exp: u32,
}

/// [definition] **One contact's plan, as the host reads its record**: its ends, width, rows,
/// arrival bases and selections, its conductance at the cut (with its carry, the chart's key),
/// its gain `G/2h` as `(numerator, e_g)`, and its scales (`σ_R`, `σ_Z`).
#[derive(Clone, Debug)]
pub(crate) struct ContactPlan {
    pub(crate) ends: (usize, usize),
    pub(crate) width: usize,
    pub(crate) rows: usize,
    pub(crate) arrival: [usize; 2],
    pub(crate) selection: [Vec<usize>; 2],
    pub(crate) carry: BigInt,
    pub(crate) conductance: Rat,
    pub(crate) gain_exp: u32,
    pub(crate) right_exp: u32,
    pub(crate) zeta_exp: u32,
    /// The storage and stiffness forms' scales when live (the host reads a zero form as no term).
    pub(crate) storage_exp: Option<u32>,
    pub(crate) stiffness_exp: Option<u32>,
}

/// [definition] **A word's plan**: the plan's words, the operands' weights (every ring's, first;
/// only they cross the bus), the charts' offsets after them (gathered in on the card), and what the
/// host reads the record with.
pub(crate) struct WordPlan {
    pub(crate) plan: Vec<i64>,
    pub(crate) operands: Vec<i64>,
    /// The operands' extent: the weights, then every chart.
    pub(crate) operand_words: usize,
    /// Each chart's offset in the operands, rings then contacts.
    pub(crate) charts: Vec<usize>,
    pub(crate) rings: Vec<RingPlan>,
    pub(crate) contacts: Vec<ContactPlan>,
    pub(crate) lc: u32,
    pub(crate) lw: u32,
    pub(crate) step: Rat,
    pub(crate) steps: usize,
    pub(crate) n: usize,
    pub(crate) na: usize,
    pub(crate) k: usize,
    pub(crate) incidences: usize,
    pub(crate) receiver: usize,
    pub(crate) first_epoch: usize,
    pub(crate) aperture: usize,
    pub(crate) map_rows: usize,
    pub(crate) logit_exp: u32,
    pub(crate) grain: u64,
    /// Per pair port entry `(source ring index, offset index, phases, rank, weights offset)`.
    pub(crate) pairs: Vec<(usize, usize, usize, usize, usize)>,
    pub(crate) pair_weights: usize,
}

/// The executed junction weights, their certificate and the admittance sum of one ring at the
/// cut's conductances.
fn weights(
    field: &Field,
    ring: usize,
    conductances: &[Rat],
    lattice: &WordLattice,
) -> Result<(Vec<Rat>, Rat, Rat), HnnError> {
    let incident: Vec<&Rat> = field
        .incident(ring)
        .iter()
        .map(|&a| &conductances[a])
        .collect();
    let admittance = field.ring(ring).admittance();
    let (executed, _, certificate) =
        junction_weights(admittance, &incident, Some(&lattice.chart()))?;
    let total = incident.iter().fold(admittance.clone(), |sum, g| sum + *g);
    Ok((executed, certificate, total))
}

/// The gather realizing `P^k` on a ring's realified coordinates, read off the host's own rotation.
fn gather(field: &Field, ring: usize, k: &BigInt) -> Vec<i64> {
    let width = field.ring(ring).width();
    let indices: Vec<Rat> = (0..width)
        .map(|index| Rat::from_integer(BigInt::from(index)))
        .collect();
    field
        .ring(ring)
        .rotate(&indices, k)
        .iter()
        .map(|index| index.to_integer().to_i64().expect("a coordinate index"))
        .collect()
}

impl WordPlan {
    /// **Form a word's plan** at a lift point on a publication, for a receiving window (module
    /// header), with the moment's count layout (its phase rows' and offset blocks' bases).
    pub(crate) fn form(
        field: &Field,
        current: &Current,
        publication: &Publication<'_>,
        phases: &ReceivingPhases,
        moment: &MomentSnapshot<'_>,
    ) -> Result<Self, HnnError> {
        let lattice = *field
            .word_lattice()
            .ok_or_else(|| refused("a field whose word runs on no declared lattice"))?;
        let (lc, lw) = (lattice.chart_exponent(), lattice.transient_exponent());
        let step = field.step().clone();
        let eta = power_of_two(&step)
            .ok_or_else(|| refused("a hop that is not a power of two (ζ/h leaves the dyadics)"))?;
        let (h_mul, h_shift) = if eta >= 0 {
            (1i64 << eta, 0u32)
        } else {
            (1, (-eta) as u32)
        };
        let (x_mul, x_shift) = if eta <= 0 {
            (1i64 << (-eta), 0u32)
        } else {
            (1, eta as u32)
        };
        let loci = &publication.loci;
        let lift = current.lift();
        // The contacts' conductances at the cut.
        let mut conductances = Vec::with_capacity(field.contacts().len());
        let mut carries = Vec::with_capacity(field.contacts().len());
        for a in 0..field.contacts().len() {
            let exponent = contact_exponent(field, a, lift)?;
            if exponent.phase != 0 {
                return Err(HnnError::ExponentPhase {
                    contact: a,
                    phase: exponent.phase,
                    grain: field.exponent_grain(),
                });
            }
            conductances.push(rat_power_of_two(&exponent.carry)? * field.contact(a).admittance());
            carries.push(exponent.carry);
        }
        let mut plan = vec![0i64; WP_HEADER];
        let mut operands: Vec<i64> = Vec::new();
        let mut charts = Vec::new();
        // The weights come first (one per port of every junction); the charts follow them.
        let mut chart_cursor: usize = (0..field.rings().len())
            .map(|g| 1 + field.incident(g).len())
            .sum();
        // Ring rows, arrival coordinates and contact rows.
        let widths: Vec<usize> = field.rings().iter().map(|ring| ring.width()).collect();
        let mut ring_rows = Vec::with_capacity(widths.len());
        let mut n = 0;
        for width in &widths {
            ring_rows.push(n);
            n += width;
        }
        let mut arrival_bases = Vec::with_capacity(field.contacts().len());
        let mut contact_rows = Vec::with_capacity(field.contacts().len());
        let (mut na, mut k) = (0usize, 0usize);
        for contact in field.contacts() {
            let (from, to) = contact.ends();
            if from == to {
                return Err(refused("a contact joining a ring to itself"));
            }
            arrival_bases.push([na, na + widths[from]]);
            na += widths[from] + widths[to];
            contact_rows.push(k);
            k += contact.width();
        }
        // The rings' table.
        let ring_table = plan.len();
        plan.resize(ring_table + WR_STRIDE * widths.len(), 0);
        let mut incidence: Vec<i64> = Vec::new();
        let mut rings = Vec::with_capacity(widths.len());
        let mut incidences = 0usize;
        let sources: Vec<usize> = field.sources().to_vec();
        for (g, &width) in widths.iter().enumerate() {
            let (executed, certificate, total) = weights(field, g, &conductances, &lattice)?;
            let weights_at = operands.len();
            for weight in &executed {
                operands.push(word(
                    weight,
                    lc,
                    "a junction weight off the charts' lattice",
                )?);
            }
            let chart_at = chart_cursor;
            chart_cursor += width * width;
            charts.push(chart_at);
            let ringloci = &loci.rings[g];
            let contrast = ringloci
                .contrast_live
                .then_some(ringloci.contrast.matrix.exponent);
            let swc = contrast.unwrap_or(0);
            let open_exp = loci
                .sources
                .iter()
                .find(|source| source.ring == g)
                .map(open_exponent);
            let storage_exp = (lc + swc + lw).max(open_exp.unwrap_or(0));
            let anchor_exp = lw + swc.max(h_shift);
            let incident: Vec<(usize, usize, usize)> = field
                .incident(g)
                .iter()
                .map(|&a| {
                    let slot = usize::from(field.contact(a).ends().0 != g);
                    (a, slot, arrival_bases[a][slot])
                })
                .collect();
            let record = &mut plan[ring_table + g * WR_STRIDE..ring_table + (g + 1) * WR_STRIDE];
            record[WR_WIDTH] = width as i64;
            record[WR_ROWS] = ring_rows[g] as i64;
            record[WR_CHART] = chart_at as i64;
            record[WR_WC] = if contrast.is_some() {
                ringloci.contrast.offset as i64
            } else {
                -1
            };
            record[WR_WC_EXP] = i64::from(swc);
            record[WR_STORAGE_EXP] = i64::from(storage_exp);
            record[WR_DEGREE] = incident.len() as i64;
            record[WR_INCIDENCE] = incidences as i64;
            record[WR_WEIGHTS] = weights_at as i64;
            record[WR_ANCHOR_EXP] = i64::from(anchor_exp);
            for &(a, slot, base) in &incident {
                incidence.extend([a as i64, slot as i64, base as i64]);
            }
            incidences += incident.len();
            rings.push(RingPlan {
                width,
                rows: ring_rows[g],
                incident,
                certificate,
                admittance: field.ring(g).admittance().clone(),
                total,
                contrast,
                storage_exp,
                anchor_exp,
            });
        }
        // The contacts' table.
        let contact_table = plan.len();
        plan.resize(contact_table + WC_STRIDE * field.contacts().len(), 0);
        let mut selections: Vec<i64> = Vec::new();
        let selection_base = |plan_len: usize, extra: usize| plan_len + extra;
        let mut contacts = Vec::with_capacity(field.contacts().len());
        let mut selection_offsets = Vec::with_capacity(field.contacts().len());
        for (a, contact) in field.contacts().iter().enumerate() {
            let width = contact.width();
            let chart_at = chart_cursor;
            chart_cursor += width * width;
            charts.push(chart_at);
            let contactloci = &loci.contacts[a];
            let g = &conductances[a];
            let (gain, gain_exp) = reduced_word(
                &(g / (Rat::from_integer(BigInt::from(2)) * &step)),
                "a contact's gain G/2h off the dyadics or past the word",
            )?;
            let (rate_gain, rate_gain_exp) = reduced_word(
                &(g / &step),
                "a contact's gain G/h off the dyadics or past the word",
            )?;
            let (shift_gain, shift_gain_exp) = reduced_word(
                &(g / Rat::from_integer(BigInt::from(2))),
                "a contact's gain G/2 off the dyadics or past the word",
            )?;
            let sc = contactloci
                .storage_live
                .then_some(contactloci.storage.matrix.exponent);
            let sk = contactloci
                .stiffness_live
                .then_some(contactloci.stiffness.matrix.exponent);
            let right_exp = lw
                + h_shift
                    .max(sc.unwrap_or(0))
                    .max(sk.map_or(0, |sk| sk + h_shift));
            let zeta_exp = lw + rate_gain_exp.max(shift_gain_exp).max(x_shift);
            let (from, to) = contact.ends();
            let select = [
                contact.selection(holonics::hnn::field::End::From),
                contact.selection(holonics::hnn::field::End::To),
            ];
            selection_offsets.push(selections.len());
            selections.extend(select[0].iter().map(|x| *x as i64));
            selections.extend(select[1].iter().map(|x| *x as i64));
            let record =
                &mut plan[contact_table + a * WC_STRIDE..contact_table + (a + 1) * WC_STRIDE];
            record[WC_WIDTH] = width as i64;
            record[WC_FROM] = from as i64;
            record[WC_TO] = to as i64;
            record[WC_ROWS] = contact_rows[a] as i64;
            record[WC_ARRIVAL_FROM] = arrival_bases[a][0] as i64;
            record[WC_ARRIVAL_TO] = arrival_bases[a][1] as i64;
            record[WC_CHART] = chart_at as i64;
            record[WC_C] = if sc.is_some() {
                contactloci.storage.offset as i64
            } else {
                -1
            };
            record[WC_C_EXP] = i64::from(sc.unwrap_or(0));
            record[WC_K] = if sk.is_some() {
                contactloci.stiffness.offset as i64
            } else {
                -1
            };
            record[WC_K_EXP] = i64::from(sk.unwrap_or(0));
            record[WC_GAIN] = gain;
            record[WC_GAIN_EXP] = i64::from(gain_exp);
            record[WC_RIGHT_EXP] = i64::from(right_exp);
            record[WC_RATE_GAIN] = rate_gain;
            record[WC_RATE_GAIN_EXP] = i64::from(rate_gain_exp);
            record[WC_SHIFT_GAIN] = shift_gain;
            record[WC_SHIFT_GAIN_EXP] = i64::from(shift_gain_exp);
            record[WC_ZETA_EXP] = i64::from(zeta_exp);
            contacts.push(ContactPlan {
                ends: (from, to),
                width,
                rows: contact_rows[a],
                arrival: arrival_bases[a],
                selection: select,
                carry: carries[a].clone(),
                conductance: g.clone(),
                gain_exp,
                right_exp,
                zeta_exp,
                storage_exp: sc,
                stiffness_exp: sk,
            });
        }
        let _ = selection_base;
        // The incidence, the row tables, the arrival table and the selections.
        let incidence_at = plan.len();
        plan.extend_from_slice(&incidence);
        let row_ring_at = plan.len();
        for (g, width) in widths.iter().enumerate() {
            plan.extend(core::iter::repeat_n(g as i64, *width));
        }
        let row_contact_at = plan.len();
        for (a, contact) in field.contacts().iter().enumerate() {
            plan.extend(core::iter::repeat_n(a as i64, contact.width()));
        }
        let arrival_at = plan.len();
        for (a, contact) in contacts.iter().enumerate() {
            for (end, ring) in [contact.ends.0, contact.ends.1].into_iter().enumerate() {
                for coordinate in 0..widths[ring] {
                    let channel = contact.selection[end]
                        .iter()
                        .position(|x| *x == coordinate)
                        .map_or(-1, |kk| kk as i64);
                    plan.extend([
                        a as i64,
                        end as i64,
                        ring as i64,
                        coordinate as i64,
                        channel,
                    ]);
                }
            }
        }
        let selections_at = plan.len();
        plan.extend_from_slice(&selections);
        for (a, offset) in selection_offsets.iter().enumerate() {
            plan[contact_table + a * WC_STRIDE + WC_SELECTION] = (selections_at + offset) as i64;
        }
        // The receiving window and its gather.
        let receiver = phases.ring();
        let map = loci.maps[receiver]
            .as_ref()
            .ok_or(HnnError::MissingReceivingMap { ring: receiver })?;
        // The bound harmonic coordinate (Decision 26), added to the anchor before the map reads it:
        // its words at the receiving locus's lattice, lifted onto the transients' `2^(−L_w)ℤ`.
        let (harmonic_at, harmonic_shift) = match &loci.harmonics[receiver] {
            Some(placed) if placed.matrix.exponent > lw => {
                return Err(refused(
                    "a harmonic coordinate finer than the transients' lattice (the read adds it to \
                     the anchor on 2^(−L_w)ℤ)",
                ));
            }
            Some(placed) => (placed.offset as i64, i64::from(lw - placed.matrix.exponent)),
            None => (-1, 0),
        };
        let gather_at = plan.len();
        plan.extend(gather(field, receiver, &lift[receiver]));
        // The source rings: their ports, pair ports and phase gathers.
        let source_at = plan.len();
        plan.resize(source_at + WS_STRIDE * loci.sources.len(), 0);
        let mut pair_entries: Vec<[i64; WQ_STRIDE]> = Vec::new();
        let mut pairs = Vec::new();
        let mut pair_weights = 0usize;
        for (s, source) in loci.sources.iter().enumerate() {
            let g = source.ring;
            let phases_g = field.ring(g).period() as usize;
            let gathers_at = plan.len();
            for c in 0..phases_g {
                plan.extend(gather(field, g, &(&lift[g] - BigInt::from(c))));
            }
            let open_exp = open_exponent(source);
            let first_pair = pair_entries.len();
            for (o, pair) in source.pairs.iter().enumerate() {
                let rank = pair.rank;
                let sigma = pair.outputs.matrix.exponent;
                let counts = moment.paired_base(s, o) as i64;
                pair_entries.push([
                    rank as i64,
                    pair.outputs.offset as i64,
                    pair.current.offset as i64,
                    pair.earlier.offset as i64,
                    counts,
                    pair_weights as i64,
                    i64::from(open_exp) - 3 * i64::from(sigma),
                    phases_g as i64,
                ]);
                pairs.push((s, o, phases_g, rank, pair_weights));
                pair_weights += phases_g * rank;
            }
            let record = &mut plan[source_at + s * WS_STRIDE..source_at + (s + 1) * WS_STRIDE];
            record[0] = g as i64;
            record[1] = phases_g as i64;
            record[2] = source.port.offset as i64;
            record[3] = moment.first_base(s) as i64;
            record[4] = gathers_at as i64;
            record[5] = i64::from(open_exp);
            record[6] = i64::from(open_exp) - i64::from(source.port.matrix.exponent);
            record[7] = source.pairs.len() as i64;
            record[8] = first_pair as i64;
        }
        let pair_at = plan.len();
        for entry in &pair_entries {
            plan.extend_from_slice(entry);
        }
        let steps = phases.junction_steps();
        let header = [
            (WP_RINGS, widths.len() as i64),
            (WP_CONTACTS, field.contacts().len() as i64),
            (WP_STEPS, steps as i64),
            (WP_LC, i64::from(lc)),
            (WP_LW, i64::from(lw)),
            (WP_RING_ROWS, n as i64),
            (WP_ARRIVALS, na as i64),
            (WP_CONTACT_ROWS, k as i64),
            (WP_H_MUL, h_mul),
            (WP_H_SHIFT, i64::from(h_shift)),
            (WP_X_MUL, x_mul),
            (WP_X_SHIFT, i64::from(x_shift)),
            (WP_RING_TABLE, ring_table as i64),
            (WP_CONTACT_TABLE, contact_table as i64),
            (WP_INCIDENCE, incidence_at as i64),
            (WP_ROW_RING, row_ring_at as i64),
            (WP_ROW_CONTACT, row_contact_at as i64),
            (WP_ARRIVAL_TABLE, arrival_at as i64),
            (WP_RECEIVER, receiver as i64),
            (WP_EPOCH, phases.first_epoch() as i64),
            (WP_APERTURE, phases.aperture() as i64),
            (WP_MAP_ROWS, map.matrix.rows as i64),
            (WP_GATHER, gather_at as i64),
            (WP_SOURCES, loci.sources.len() as i64),
            (WP_SOURCE_TABLE, source_at as i64),
            (WP_ALPHABET, field.alphabet() as i64),
            (WP_PAIR_TABLE, pair_at as i64),
            (WP_INCIDENCES, incidences as i64),
            (WP_MAP, map.offset as i64),
            (WP_HARMONIC, harmonic_at),
            (WP_HARMONIC_SHIFT, harmonic_shift),
        ];
        for (at, value) in header {
            plan[at] = value;
        }
        if sources.len() != loci.sources.len() {
            return Err(refused("the published sources against the field's"));
        }
        Ok(Self {
            plan,
            operands,
            operand_words: chart_cursor,
            charts,
            rings,
            contacts,
            lc,
            lw,
            step,
            steps,
            n,
            na,
            k,
            incidences,
            receiver,
            first_epoch: phases.first_epoch(),
            aperture: phases.aperture(),
            map_rows: map.matrix.rows,
            logit_exp: map.matrix.exponent + lw,
            grain: phases.grain(),
            pairs,
            pair_weights,
        })
    }

    /// The widest stage's rows (the word's layout covers them).
    fn widest(&self) -> usize {
        self.n
            .max(self.na)
            .max(self.k)
            .max(self.incidences)
            .max(self.aperture * self.map_rows)
    }
}

/// A source ring's opening scale: its port's lattice, or three of it with a pair port (`e (a·x)(b·y)`).
fn open_exponent(source: &crate::hnn::publication::SourceLoci) -> u32 {
    let port = source.port.matrix.exponent;
    source
        .pairs
        .iter()
        .map(|pair| 3 * pair.outputs.matrix.exponent)
        .fold(port, u32::max)
}

// -------------------------------------------------------------------------------------------
// the word's buffer

/// [definition] **The word buffer's layout**: the octet offset of each array (16-octet aligned),
/// the forward region's end, and the whole buffer's extent.
#[derive(Clone, Debug)]
pub(crate) struct WordLayout {
    pub(crate) offsets: [u64; WL_ENTRIES],
    pub(crate) forward: usize,
    pub(crate) total: usize,
}

impl WordLayout {
    fn new(plan: &WordPlan, contacts: usize) -> Self {
        let (n, na, k, s) = (plan.n, plan.na, plan.k, plan.steps);
        let logits = plan.aperture * plan.map_rows;
        let reads = plan.aperture * plan.rings[plan.receiver].width;
        // (entry, octets) in the kernels' order.
        let sizes: [usize; WL_ENTRIES] = [
            8 * n,
            8 * na,
            8 * k,
            8 * k,
            16 * n,
            16 * n,
            16 * k,
            16 * na,
            16 * k,
            16 * k,
            8 * n,
            16 * n,
            16 * k,
            8 * k,
            8 * s * n,
            8 * s * na,
            8 * s * k,
            8 * s * k,
            8 * s * n,
            16 * s * n,
            16 * s * k,
            8 * s * k,
            16 * s * k,
            16 * logits,
            16,
            // the return's
            8 * n,
            8 * na,
            8 * k,
            8 * k,
            16 * n,
            16 * k,
            16 * k,
            16 * k,
            16 * k,
            16 * n,
            16 * na,
            8 * n,
            16 * n,
            16 * n,
            16 * na,
            16 * k,
            8 * k,
            8 * k,
            16 * n,
            8 * s * n,
            8 * s * k,
            16 * s * contacts,
            16 * s * contacts,
            16 * s * plan.incidences,
            8 * reads,
            16,
        ];
        let mut offsets = [0u64; WL_ENTRIES];
        let mut at = 0usize;
        let mut forward = 0usize;
        for (entry, size) in sizes.iter().enumerate() {
            offsets[entry] = at as u64;
            at += size.next_multiple_of(16).max(16);
            if entry == WL_STATUS {
                forward = at;
            }
        }
        Self {
            offsets,
            forward,
            total: at,
        }
    }

    fn at(&self, entry: usize) -> usize {
        self.offsets[entry] as usize
    }
}

const WL_STORAGE: usize = 0;
const WL_ARRIVALS: usize = 1;
const WL_U: usize = 2;
const WL_W: usize = 3;
const WL_REM_ANCHOR: usize = 4;
const WL_REM_STORAGE: usize = 5;
const WL_REM_SOLVE: usize = 6;
const WL_REM_ARRIVAL: usize = 7;
const WL_REM_DISP: usize = 8;
const WL_REM_RATE: usize = 9;
const WL_REC_STORAGE: usize = 14;
const WL_REC_ARRIVALS: usize = 15;
const WL_REC_U: usize = 16;
const WL_REC_W: usize = 17;
const WL_REC_ANCHOR: usize = 18;
const WL_REC_MID: usize = 19;
const WL_REC_RIGHT: usize = 20;
const WL_REC_ZETA: usize = 21;
const WL_REC_OMEGA: usize = 22;
const WL_LOGITS: usize = 23;
const WL_STATUS: usize = 24;
const WL_BAR_STORAGE: usize = 25;
const WL_REV_EL: usize = 29;
const WL_REV_ZETA: usize = 30;
const WL_REV_SOLVED: usize = 31;
const WL_REV_RATE: usize = 32;
const WL_REV_DISP: usize = 33;
const WL_REV_STORAGE: usize = 34;
const WL_REV_ARRIVAL: usize = 35;
const WL_REC_ADJ_U: usize = 44;
const WL_REC_SOLVED: usize = 45;
const WL_DOTS1: usize = 46;
const WL_DOTS2: usize = 47;
const WL_DOTS3: usize = 48;
const WL_READS: usize = 49;
const WL_REV_STATUS: usize = 50;

fn i64s(octets: &[u8], at: usize, count: usize) -> Vec<i64> {
    octets[at..at + 8 * count]
        .chunks_exact(8)
        .map(|chunk| i64::from_ne_bytes(chunk.try_into().expect("eight octets")))
        .collect()
}

fn i128s(octets: &[u8], at: usize, count: usize) -> Vec<i128> {
    octets[at..at + 16 * count]
        .chunks_exact(16)
        .map(|chunk| i128::from_ne_bytes(chunk.try_into().expect("sixteen octets")))
        .collect()
}

fn u32s(octets: &[u8], at: usize, count: usize) -> Vec<u32> {
    octets[at..at + 4 * count]
        .chunks_exact(4)
        .map(|chunk| u32::from_ne_bytes(chunk.try_into().expect("four octets")))
        .collect()
}

/// [definition] **The forward word's record as the host reads it**: per step the change at its
/// start (storage, arrivals, `u`, `w`) and its carried anchors; per full tick the elements'
/// midpoints `x̄` (at `L_c + σ_Wc + L_w + 1`), the transits' right sides (at `σ_R`), carried `ζ`
/// and `ω` (at `L_w + e_g`); the change after the last junction; every carried remainder at its
/// scale; the logits (at `L_R + L_w`); the status.
#[derive(Clone, Debug)]
pub(crate) struct ForwardRecord {
    pub(crate) storage: Vec<i64>,
    pub(crate) arrivals: Vec<i64>,
    pub(crate) u: Vec<i64>,
    pub(crate) w: Vec<i64>,
    pub(crate) anchors: Vec<i64>,
    pub(crate) mid: Vec<i128>,
    pub(crate) right: Vec<i128>,
    pub(crate) zeta: Vec<i64>,
    pub(crate) omega: Vec<i128>,
    pub(crate) final_storage: Vec<i64>,
    pub(crate) final_arrivals: Vec<i64>,
    pub(crate) final_u: Vec<i64>,
    pub(crate) final_w: Vec<i64>,
    pub(crate) rem_anchor: Vec<i128>,
    pub(crate) rem_storage: Vec<i128>,
    pub(crate) rem_solve: Vec<i128>,
    pub(crate) rem_arrival: Vec<i128>,
    pub(crate) rem_disp: Vec<i128>,
    pub(crate) rem_rate: Vec<i128>,
    pub(crate) logits: Vec<i128>,
}

/// [definition] **The return's record as the host reads it**: the opening covector, per step the
/// elements' adjoints `u` and the transits' solved adjoints, the conductance's dyadic parts, and
/// every carried remainder of the return at its scale.
#[derive(Clone, Debug)]
pub(crate) struct ReverseRecord {
    pub(crate) opening: Vec<i64>,
    pub(crate) adjoint: Vec<i64>,
    pub(crate) solved: Vec<i64>,
    pub(crate) dots1: Vec<i128>,
    pub(crate) dots2: Vec<i128>,
    pub(crate) dots3: Vec<i128>,
    pub(crate) rem_el: Vec<i128>,
    pub(crate) rem_zeta: Vec<i128>,
    pub(crate) rem_solved: Vec<i128>,
    pub(crate) rem_rate: Vec<i128>,
    pub(crate) rem_disp: Vec<i128>,
    pub(crate) rem_storage: Vec<i128>,
    pub(crate) rem_arrival: Vec<i128>,
}

/// The stages the kernels report a refusal at.
fn refusal(status: &[u32], forward: bool) -> Option<HnnError> {
    let bits = status[0];
    if bits == 0 {
        return None;
    }
    let what = match (forward, status[1]) {
        (true, 1) => "the word's open on the card (carrier, word or malformed plan)",
        (true, 2) => "a junction's carried anchor on the card",
        (true, 3) => "an element's operand on the card",
        (true, 4) => "a transit's right side on the card",
        (true, 5) => "an element's carried storage on the card",
        (true, 6) => "a transit's carried solve or state on the card",
        (true, 7) => "a carried arrival on the card",
        (true, 8) => "the last junction's change on the card",
        (true, 9) => "a receiving logit on the card",
        (false, 1) => "an element's carried adjoint on the card",
        (false, 2) => "a transit's carried covector on the card",
        (false, 3) => "an element's contrast covector on the card",
        (false, 4) => "a transit's solved adjoint on the card",
        (false, 5) => "a transit's state covector on the card",
        (false, 6) => "an outgoing covector on the card",
        (false, 7) => "a conductance part on the card",
        (false, 8) => "a junction's carried covector on the card",
        _ => "a word's entry on the card",
    };
    Some(HnnError::Carrier { what })
}

// -------------------------------------------------------------------------------------------
// the resident word

/// [definition] **One word's buffers on the card** (module header).
pub(crate) struct ResidentWord<'c> {
    card: &'c Card,
    pub(crate) plan: WordPlan,
    layout: WordLayout,
    plan_words: CardBuffer<'c, i64>,
    operands: CardBuffer<'c, i64>,
    buffer: CardBuffer<'c, u8>,
    offsets: CardBuffer<'c, u64>,
    /// The publication the word read: its return reads the same operators.
    pub(crate) publication: Rc<Publication<'c>>,
    pub(crate) record: ForwardRecord,
    /// The octets the word took across the bus.
    pub(crate) octets: usize,
}

/// The launches' layouts, derived once from the census for a word's shape.
pub(crate) struct Launches {
    forward: Layout,
    reverse: Layout,
}

impl Launches {
    /// The forward word's and the return's layouts (the hardware law's report of their
    /// realizations).
    pub(crate) fn layouts(&self) -> (Layout, Layout) {
        (self.forward, self.reverse)
    }

    fn derive(card: &Card, plan: &WordPlan) -> Result<Self, HnnError> {
        let census = card.census();
        Ok(Self {
            forward: word_layout(
                census,
                &card.entry(FORWARD_ENTRY).map_err(device)?,
                plan.widest(),
            )
            .map_err(device)?,
            reverse: word_layout(
                census,
                &card.entry(REVERSE_ENTRY).map_err(device)?,
                plan.widest(),
            )
            .map_err(device)?,
        })
    }
}

macro_rules! arguments {
    ($($value:ident),* $(,)?) => {
        [$(&mut $value as *mut _ as *mut c_void),*]
    };
}

impl<'c> ResidentWord<'c> {
    /// **Run a word's forward on the card** (module header): its plan and operands written, its
    /// charts gathered from the store's workspace, the pair ports' weights read against the moment,
    /// one launch of the word, and one read of its record.
    pub(crate) fn forward(
        card: &'c Card,
        plan: WordPlan,
        publication: Rc<Publication<'c>>,
        moment: &MomentSnapshot<'c>,
        store: &ChartStore<'c>,
        refined: &Refined,
    ) -> Result<(Self, Launches), HnnError> {
        let launches = Launches::derive(card, &plan)?;
        let layout = WordLayout::new(&plan, plan.contacts.len());
        let plan_words = card.upload(&plan.plan).map_err(device)?;
        let operands = card.alloc::<i64>(plan.operand_words).map_err(device)?;
        card.write(&operands, 0, &plan.operands).map_err(device)?;
        let offsets = card.upload(&layout.offsets).map_err(device)?;
        let buffer = card.alloc::<u8>(layout.total).map_err(device)?;
        let mut octets = 8 * (plan.plan.len() + plan.operands.len() + WL_ENTRIES);
        // The word's own charts, gathered from the workspace.
        let table: Vec<[u64; 3]> = refined
            .charts
            .iter()
            .zip(&plan.charts)
            .map(|(&(width, from), &to)| [from as u64, to as u64, (width * width) as u64])
            .collect();
        copy_words(card, store.workspace(), &operands, &table).map_err(device)?;
        // The pair ports' weights at the open.
        let weights = card
            .alloc::<i128>(plan.pair_weights.max(1))
            .map_err(device)?;
        let weight_status = card
            .alloc::<u32>(plan.pair_weights.max(1))
            .map_err(device)?;
        for &(s, o, phases, rank, at) in &plan.pairs {
            let pair = &publication.loci.sources[s].pairs[o];
            let entry = card.entry(PAIR_ENTRY).map_err(device)?;
            let alphabet = pair.current.matrix.columns;
            let layout =
                read_layout(card.census(), &entry, phases, alphabet, rank).map_err(device)?;
            let mut counts = moment.paired_pointer(s, o);
            let mut current = publication.words.device_ptr() + 8 * pair.current.offset as u64;
            let mut earlier = publication.words.device_ptr() + 8 * pair.earlier.offset as u64;
            let mut alphabet_wire = alphabet as u32;
            let mut rank_wire = rank as u32;
            let mut phases_wire = phases as u32;
            let mut out = weights.device_ptr() + 16 * at as u64;
            let mut status = weight_status.device_ptr() + 4 * at as u64;
            let mut params = arguments![
                counts,
                current,
                earlier,
                alphabet_wire,
                rank_wire,
                phases_wire,
                out,
                status
            ];
            card.launch(PAIR_ENTRY, &layout, &mut params)
                .map_err(device)?;
        }
        let mut plan_ptr = plan_words.device_ptr();
        let mut operands_ptr = operands.device_ptr();
        let mut published = publication.words.device_ptr();
        let mut moment_ptr = moment.first_pointer();
        let mut weights_ptr = weights.device_ptr();
        let mut word_ptr = buffer.device_ptr();
        let mut offsets_ptr = offsets.device_ptr();
        let mut params = arguments![
            plan_ptr,
            operands_ptr,
            published,
            moment_ptr,
            weights_ptr,
            word_ptr,
            offsets_ptr
        ];
        card.launch(FORWARD_ENTRY, &launches.forward, &mut params)
            .map_err(device)?;
        if plan.pair_weights > 0 {
            let statuses = card.fetch(&weight_status).map_err(device)?;
            if statuses.iter().take(plan.pair_weights).any(|s| *s != 0) {
                return Err(HnnError::Carrier {
                    what: "a pair port's weight at the open on the card",
                });
            }
        }
        let octets_read = card
            .fetch_range(&buffer, 0, layout.forward)
            .map_err(device)?;
        octets += layout.forward;
        let status = u32s(&octets_read, layout.at(WL_STATUS), 3);
        if let Some(refusal) = refusal(&status, true) {
            return Err(refusal);
        }
        let record = decode_forward(&plan, &layout, &octets_read);
        Ok((
            Self {
                card,
                plan,
                layout,
                plan_words,
                operands,
                buffer,
                offsets,
                publication,
                record,
                octets,
            },
            launches,
        ))
    }

    /// **Run the word's return on the card**: the carried reads written (per receiving epoch, the
    /// receiving ring's covector on `2^(−L_w)ℤ`), one launch, one read of its record.
    pub(crate) fn reverse(&mut self, reads: &[i64]) -> Result<ReverseRecord, HnnError> {
        let card = self.card;
        let plan = &self.plan;
        let expected = plan.aperture * plan.rings[plan.receiver].width;
        if reads.len() != expected {
            return Err(HnnError::Shape {
                what: "the carried reads of a word's return",
                expected,
                found: reads.len(),
            });
        }
        let octets: Vec<u8> = reads.iter().flat_map(|r| r.to_ne_bytes()).collect();
        card.write(&self.buffer, self.layout.at(WL_READS), &octets)
            .map_err(device)?;
        let launches = Launches::derive(card, plan)?;
        let mut plan_ptr = self.plan_words.device_ptr();
        let mut operands_ptr = self.operands.device_ptr();
        let mut published = self.publication.words.device_ptr();
        let mut word_ptr = self.buffer.device_ptr();
        let mut offsets_ptr = self.offsets.device_ptr();
        let mut params = arguments![plan_ptr, operands_ptr, published, word_ptr, offsets_ptr];
        card.launch(REVERSE_ENTRY, &launches.reverse, &mut params)
            .map_err(device)?;
        let from = self.layout.at(WL_BAR_STORAGE);
        let read = card
            .fetch_range(&self.buffer, from, self.layout.total - from)
            .map_err(device)?;
        self.octets += octets.len() + read.len();
        let at = |entry: usize| self.layout.at(entry) - from;
        let status = u32s(&read, at(WL_REV_STATUS), 3);
        if let Some(refusal) = refusal(&status, false) {
            return Err(refusal);
        }
        let (n, na, k, s) = (plan.n, plan.na, plan.k, plan.steps);
        let c = plan.contacts.len();
        Ok(ReverseRecord {
            opening: i64s(&read, at(WL_BAR_STORAGE), n),
            adjoint: i64s(&read, at(WL_REC_ADJ_U), s * n),
            solved: i64s(&read, at(WL_REC_SOLVED), s * k),
            dots1: i128s(&read, at(WL_DOTS1), s * c),
            dots2: i128s(&read, at(WL_DOTS2), s * c),
            dots3: i128s(&read, at(WL_DOTS3), s * plan.incidences),
            rem_el: i128s(&read, at(WL_REV_EL), n),
            rem_zeta: i128s(&read, at(WL_REV_ZETA), k),
            rem_solved: i128s(&read, at(WL_REV_SOLVED), k),
            rem_rate: i128s(&read, at(WL_REV_RATE), k),
            rem_disp: i128s(&read, at(WL_REV_DISP), k),
            rem_storage: i128s(&read, at(WL_REV_STORAGE), n),
            rem_arrival: i128s(&read, at(WL_REV_ARRIVAL), na),
        })
    }
}

fn decode_forward(plan: &WordPlan, layout: &WordLayout, octets: &[u8]) -> ForwardRecord {
    let (n, na, k, s) = (plan.n, plan.na, plan.k, plan.steps);
    let at = |entry: usize| layout.at(entry);
    ForwardRecord {
        storage: i64s(octets, at(WL_REC_STORAGE), s * n),
        arrivals: i64s(octets, at(WL_REC_ARRIVALS), s * na),
        u: i64s(octets, at(WL_REC_U), s * k),
        w: i64s(octets, at(WL_REC_W), s * k),
        anchors: i64s(octets, at(WL_REC_ANCHOR), s * n),
        mid: i128s(octets, at(WL_REC_MID), s * n),
        right: i128s(octets, at(WL_REC_RIGHT), s * k),
        zeta: i64s(octets, at(WL_REC_ZETA), s * k),
        omega: i128s(octets, at(WL_REC_OMEGA), s * k),
        final_storage: i64s(octets, at(WL_STORAGE), n),
        final_arrivals: i64s(octets, at(WL_ARRIVALS), na),
        final_u: i64s(octets, at(WL_U), k),
        final_w: i64s(octets, at(WL_W), k),
        rem_anchor: i128s(octets, at(WL_REM_ANCHOR), n),
        rem_storage: i128s(octets, at(WL_REM_STORAGE), n),
        rem_solve: i128s(octets, at(WL_REM_SOLVE), k),
        rem_arrival: i128s(octets, at(WL_REM_ARRIVAL), na),
        rem_disp: i128s(octets, at(WL_REM_DISP), k),
        rem_rate: i128s(octets, at(WL_REM_RATE), k),
        logits: i128s(octets, at(WL_LOGITS), plan.aperture * plan.map_rows),
    }
}

impl WordPlan {
    /// The contact's remainder scales `(solve, arrival, displacement, rate)` and its `ω` scale.
    pub(crate) fn contact_scales(&self, a: usize) -> (u32, u32, u32, u32, u32) {
        let contact = &self.contacts[a];
        let (lc, lw) = (self.lc, self.lw);
        let eta = power_of_two(&self.step).expect("checked at the plan");
        let h_shift = if eta < 0 { (-eta) as u32 } else { 0 };
        let x_shift = if eta > 0 { eta as u32 } else { 0 };
        (
            lc + contact.right_exp,
            lw + x_shift,
            lw + contact.gain_exp + h_shift,
            lw + contact.gain_exp,
            lw + contact.gain_exp,
        )
    }

    /// `h`'s multiplier and shift (`h = H_mul·2^(−H)`), and `1/h`'s.
    pub(crate) fn hop(&self) -> (i64, u32, i64, u32) {
        let eta = power_of_two(&self.step).expect("checked at the plan");
        let (h_mul, h_shift) = if eta >= 0 {
            (1i64 << eta, 0u32)
        } else {
            (1, (-eta) as u32)
        };
        let (x_mul, x_shift) = if eta <= 0 {
            (1i64 << (-eta), 0u32)
        } else {
            (1, eta as u32)
        };
        (h_mul, h_shift, x_mul, x_shift)
    }
}
