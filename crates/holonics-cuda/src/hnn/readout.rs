//! **The host's readings of a word executed on the card** (the port plan's host side): the faces,
//! each tick's balance, the word's release, and the word's return, each read exactly from the
//! card's integer record.
//!
//! [definition] The card executes the word's change; the host keeps the readings whose values are
//! exact rationals past the carrier or in `ℚ(θ)` (the port plan: "the faces in `ℚ(θ)`, every
//! enclosure, the Holon ratio"). Each is the host owner's formula read on the record's coordinates:
//!
//! - **the faces** (`holonics::hnn::receiving::ReceivingPhases::read`, `ratio::Faces::of_reads`):
//!   the wave's logits are the card's (`R · P_R^(τ_R) v_R(e_j)`, exact); the count face's grain
//!   logits (Decision 27, read on the host from the publication's class masses), their sum
//!   (`ReceivingRead::combined`, the host reference's own formula), the grain cells and the faces
//!   in `ℚ(θ)` are the host's;
//! - **each tick's balance** (`holonics::hnn::word::Word::tick`, `propagation::TickBalance`): the
//!   power before and after, the dissipation, the passive and contrast terms, and the executed
//!   word's residual with its certified bound, term by term as the host forms them. [agent-inferred]
//!   They are read on the host, from the record the return reads anyway, because their terms pass
//!   the card's 128-bit carrier (`⟨x̄, K x̄⟩` lies on `2^(−148)ℤ` at campaign 1's scales) and they are
//!   receipts, read once per tick;
//! - **the release** (`Word::released`): the unread change's power, the peak bits of the change,
//!   the last junction's residual, and every carried remainder, released and read;
//! - **the return** (`port::Word::pull_back`): the reads' covectors formed on the host (the
//!   covector `p̃ − q` lives on `(1/W)ℤ`, not on a lattice, so its pull through `Rᵀ` and its first
//!   split are the host's, and its remainder is released with the return's), the elements' and
//!   transits' ticks, the conductance covector (its junction parts divide by the admittance sum,
//!   which is not dyadic) and the return's remainders.

use holonics::hnn::chart::carry;
use holonics::hnn::port::{ElementTick, TransitTick, WordReturn};
use holonics::hnn::propagation::TickBalance;
use holonics::hnn::ratio::Faces;
use holonics::hnn::receiving::ReceivingRead;
use holonics::hnn::{
    ChartReading, CountFace, Field, HnnError, RatioCovector, Released, Remainders,
};
use holonics::ratio::Rat;

use num_bigint::BigInt;
use num_traits::{Signed, Zero};

use crate::hnn::dyadic::{DyadicMatrix, dot, integral, l1, lift, sup, value, wide, wider};
use crate::hnn::execute::{ForwardRecord, ReverseRecord, WordPlan};
use crate::hnn::publication::Loci;

fn rat(numerator: BigInt, exponent: u32) -> Rat {
    value(numerator, exponent)
}

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

/// A word's slice of `len` entries at `at`.
fn slice<T: Clone>(values: &[T], at: usize, len: usize) -> &[T] {
    &values[at..at + len]
}

/// The exact bits of a dyadic entry `X · 2^(−σ)` as a reduced ratio: its numerator's and its
/// denominator's bits (`ExactWork`'s and `Word::state_bits`'s reading).
fn entry_bits(coordinate: i64, exponent: u32) -> u64 {
    let value = rat(BigInt::from(coordinate), exponent);
    value.numer().bits() + value.denom().bits()
}

/// [definition] **One step's change as the host reads it**: per ring its storage and anchor, per
/// contact its arrivals at both ends and its state `(u, w)`, all on `2^(−L_w)ℤ`.
struct Change<'a> {
    storage: &'a [i64],
    arrivals: &'a [i64],
    u: &'a [i64],
    w: &'a [i64],
}

impl<'a> Change<'a> {
    fn at(plan: &WordPlan, record: &'a ForwardRecord, step: usize) -> Self {
        Self {
            storage: slice(&record.storage, step * plan.n, plan.n),
            arrivals: slice(&record.arrivals, step * plan.na, plan.na),
            u: slice(&record.u, step * plan.k, plan.k),
            w: slice(&record.w, step * plan.k, plan.k),
        }
    }

    fn after(plan: &WordPlan, record: &'a ForwardRecord) -> Self {
        let _ = plan;
        Self {
            storage: &record.final_storage,
            arrivals: &record.final_arrivals,
            u: &record.final_u,
            w: &record.final_w,
        }
    }
}

/// `⟨x, F x⟩` for a form at its scale and a coordinate vector at `σ_x`: the value, or zero for a
/// zero form (the host reads it as no term).
fn quadratic(form: &DyadicMatrix, vector: &[BigInt], exponent: u32) -> Rat {
    if form.is_zero() {
        return Rat::zero();
    }
    let image = form.apply(vector);
    rat(dot(vector, &image), 2 * exponent + form.exponent)
}

/// **The global power of a change** (`holonics::hnn::propagation::global_power`):
/// `(h/4)[Σ_r Y_r |s_r|² + Σ_a G_a (|a_from|² + |a_to|²)] + Σ_a ½(⟨w, C w⟩ + ⟨u, K u⟩)`.
fn power(plan: &WordPlan, loci: &Loci, change: &Change<'_>) -> Rat {
    let lw = plan.lw;
    let mut waves = Rat::zero();
    for ring in &plan.rings {
        let s = wide(slice(change.storage, ring.rows, ring.width));
        waves += &ring.admittance * rat(dot(&s, &s), 2 * lw);
    }
    let mut stored = Rat::zero();
    for (a, contact) in plan.contacts.iter().enumerate() {
        let widths = [
            plan.rings[contact.ends.0].width,
            plan.rings[contact.ends.1].width,
        ];
        let mut squares = BigInt::zero();
        for (base, width) in contact.arrival.iter().zip(widths) {
            let x = wide(slice(change.arrivals, *base, width));
            squares += dot(&x, &x);
        }
        waves += &contact.conductance * rat(squares, 2 * lw);
        let u = wide(slice(change.u, contact.rows, contact.width));
        let w = wide(slice(change.w, contact.rows, contact.width));
        let contactloci = &loci.contacts[a];
        stored += (quadratic(&contactloci.storage.matrix, &w, lw)
            + quadratic(&contactloci.stiffness.matrix, &u, lw))
            / integer(2);
    }
    &plan.step / integer(4) * waves + stored
}

/// **One ring's junction terms at a step**: the executed anchor's residual against the
/// participation mean, `h·total·⟨v, v − v*⟩`, and its bound `h·total·‖v‖₁(‖ŵ − w‖₁·largest + u)`
/// (`holonics::hnn::word::Word::junctions`).
fn junction(plan: &WordPlan, record: &ForwardRecord, step: usize, g: usize) -> (Rat, Rat) {
    let (n, lw) = (plan.n, plan.lw);
    let ring = &plan.rings[g];
    let v = wide(slice(&record.anchors, step * n + ring.rows, ring.width));
    let s = wide(slice(&record.storage, step * n + ring.rows, ring.width));
    let mut largest = sup(&s);
    // total·v* = Y s + Σ G a.
    let mut pulled = rat(dot(&v, &s), 2 * lw) * &ring.admittance;
    for &(a, _, base) in &ring.incident {
        let x = wide(slice(&record.arrivals, step * plan.na + base, ring.width));
        largest = largest.max(sup(&x));
        pulled += rat(dot(&v, &x), 2 * lw) * &plan.contacts[a].conductance;
    }
    let h = &plan.step;
    let residual = h * (&ring.total * rat(dot(&v, &v), 2 * lw) - pulled);
    let unit = rat(BigInt::from(1), lw);
    let bound = h * &ring.total * rat(l1(&v), lw) * (&ring.certificate * rat(largest, lw) + unit);
    (residual, bound)
}

/// The terms of one full tick's balance that a ring's element contributes: `(resist, drive,
/// residual, bound)`, each already scaled by `(h/2)Y` or `(h/4)Y` as the word adds them.
fn element(
    plan: &WordPlan,
    loci: &Loci,
    record: &ForwardRecord,
    step: usize,
    g: usize,
    certificate: &Rat,
) -> (Rat, Rat, Rat, Rat) {
    let (n, lc, lw) = (plan.n, plan.lc, plan.lw);
    let ring = &plan.rings[g];
    let ringloci = &loci.rings[g];
    let swc = ring.contrast.unwrap_or(0);
    let sx = lc + swc + lw + 1;
    let v = wide(slice(&record.anchors, step * n + ring.rows, ring.width));
    let s = wide(slice(&record.storage, step * n + ring.rows, ring.width));
    let next = wide(slice(
        &record.storage,
        (step + 1) * n + ring.rows,
        ring.width,
    ));
    let x = wider(slice(&record.mid, step * n + ring.rows, ring.width));
    let b: Vec<BigInt> = v.iter().zip(&s).map(|(v, s)| 2 * v - s).collect();
    let c: Vec<BigInt> = v.iter().zip(&s).map(|(v, s)| v - s).collect();
    // next_image = 2x̄ − b on σ_x.
    let b_at_x = lift(&b, sx - lw);
    let image: Vec<BigInt> = x.iter().zip(&b_at_x).map(|(x, b)| 2 * x - b).collect();
    // The contrast port's drive W_c c on σ_Wc + L_w, and the operand 2b + W_c c.
    let (drive, operand, operand_exp) = match ring.contrast {
        Some(exponent) => {
            let wcc = ringloci.contrast.matrix.apply(&c);
            let operand: Vec<BigInt> = lift(&b, exponent + 1)
                .iter()
                .zip(&wcc)
                .map(|(b, d)| b + d)
                .collect();
            (Some(wcc), operand, exponent + lw)
        }
        None => (None, lift(&b, 1), lw),
    };
    let resist = quadratic(&ringloci.passive, &x, sx);
    let drive_term = match &drive {
        Some(wcc) => rat(dot(&x, wcc), sx + swc + lw),
        None => Rat::zero(),
    };
    // e = next_image − b − K x̄ − W_c c on σ_e = σ_x + σ_K.
    let sk = ringloci.element.exponent;
    let se = sx + sk;
    let kx = ringloci.element.apply(&x);
    let mut e: Vec<BigInt> = lift(&image, sk)
        .iter()
        .zip(lift(&b, se - lw))
        .zip(&kx)
        .map(|((image, b), kx)| image - b - kx)
        .collect();
    if let Some(wcc) = &drive {
        for (entry, d) in e.iter_mut().zip(lift(wcc, se - swc - lw)) {
            *entry -= d;
        }
    }
    let defect = rat(dot(&x, &e), sx + se);
    let chart_bound = rat(l1(&x), sx) * certificate * rat(sup(&operand), operand_exp);
    // The storage's split: |s′|² − |ŝ′|² = ⟨s′ − ŝ′, s′ + ŝ′⟩ on σ_x.
    let next_at_x = lift(&next, sx - lw);
    let difference: Vec<BigInt> = next_at_x.iter().zip(&image).map(|(a, b)| a - b).collect();
    let sum: Vec<BigInt> = next_at_x.iter().zip(&image).map(|(a, b)| a + b).collect();
    let split_power = rat(dot(&difference, &sum), 2 * sx);
    let split_bound = rat(l1(&sum), sx + lw);
    let half = &plan.step / integer(2) * &ring.admittance;
    let quarter = &plan.step / integer(4) * &ring.admittance;
    (
        &half * resist,
        &half * drive_term,
        &half * defect + &quarter * split_power,
        &half * chart_bound + &quarter * split_bound,
    )
}

/// The terms of one full tick's balance that a contact's transit contributes: `(dissipation,
/// residual, bound)` (`holonics::hnn::propagation::transit_defect` and the word's split terms).
fn transit(
    plan: &WordPlan,
    loci: &Loci,
    record: &ForwardRecord,
    step: usize,
    a: usize,
    executed: &Executed<'_>,
) -> (Rat, Rat, Rat) {
    let (operator, norm) = executed.contacts[a];
    let certificate = &executed.readings[plan.rings.len() + a].certificate;
    let (k, na, lw) = (plan.k, plan.na, plan.lw);
    let contact = &plan.contacts[a];
    let contactloci = &loci.contacts[a];
    let (h_mul, h_shift, x_mul, x_shift) = plan.hop();
    let eg = contact.gain_exp;
    let so = lw + eg;
    let at = step * k + contact.rows;
    let zeta = wide(slice(&record.zeta, at, contact.width));
    let omega = wider(slice(&record.omega, at, contact.width));
    let right = wider(slice(&record.right, at, contact.width));
    // ⟨ω, m ζ − right⟩ on a common scale.
    let mz = operator.apply(&zeta);
    let smz = operator.exponent + lw;
    let common = smz.max(contact.right_exp);
    let residual: Vec<BigInt> = lift(&mz, common - smz)
        .iter()
        .zip(lift(&right, common - contact.right_exp))
        .map(|(m, r)| m - r)
        .collect();
    let chart_term = rat(dot(&omega, &residual), common + so);
    let unit = rat(BigInt::from(1), lw);
    let chart_bound =
        rat(l1(&omega), so) * (certificate * rat(sup(&right), contact.right_exp) + norm * &unit);
    let h = &plan.step;
    let dissipation = h * quadratic(&contactloci.dissipation, &omega, so);
    // The state's split: E(u′, w′) − E(û′, ŵ′), and its bound.
    let u = wide(slice(&record.u, at, contact.width));
    let w = wide(slice(&record.w, at, contact.width));
    let next_u = wide(slice(
        &record.u,
        (step + 1) * k + contact.rows,
        contact.width,
    ));
    let next_w = wide(slice(
        &record.w,
        (step + 1) * k + contact.rows,
        contact.width,
    ));
    // ŵ′ = 2ω − w on L_w + e_g; û′ = u + hω on L_w + e_g + H.
    let image_w: Vec<BigInt> = omega
        .iter()
        .zip(lift(&w, eg))
        .map(|(o, w)| 2 * o - w)
        .collect();
    let image_u: Vec<BigInt> = lift(&u, eg + h_shift)
        .iter()
        .zip(&omega)
        .map(|(u, o)| u + BigInt::from(h_mul) * o)
        .collect();
    let (sw, su) = (lw + eg, lw + eg + h_shift);
    let energy = |disp: &[BigInt], sd: u32, rate: &[BigInt], sr: u32| -> Rat {
        (quadratic(&contactloci.storage.matrix, rate, sr)
            + quadratic(&contactloci.stiffness.matrix, disp, sd))
            / integer(2)
    };
    let mut split_power = energy(&next_u, lw, &next_w, lw) - energy(&image_u, su, &image_w, sw);
    let w_sum: Vec<BigInt> = lift(&next_w, eg)
        .iter()
        .zip(&image_w)
        .map(|(a, b)| a + b)
        .collect();
    let u_sum: Vec<BigInt> = lift(&next_u, eg + h_shift)
        .iter()
        .zip(&image_u)
        .map(|(a, b)| a + b)
        .collect();
    let stored = contactloci.storage.matrix.apply(&w_sum);
    let stiffened = contactloci.stiffness.matrix.apply(&u_sum);
    let mut split_bound = &unit
        * (rat(l1(&stored), contactloci.storage.matrix.exponent + sw)
            + rat(l1(&stiffened), contactloci.stiffness.matrix.exponent + su))
        / integer(2);
    // The arrivals' split at both ends, each weighted (hG/4).
    let quarter = h / integer(4) * &contact.conductance;
    let (from, to) = contact.ends;
    for (end, ring) in [from, to].into_iter().enumerate() {
        let width = plan.rings[ring].width;
        let base = contact.arrival[end];
        let v = wide(slice(
            &record.anchors,
            step * plan.n + plan.rings[ring].rows,
            width,
        ));
        let a_in = wide(slice(&record.arrivals, step * na + base, width));
        let carried = wide(slice(&record.arrivals, (step + 1) * na + base, width));
        // image = o·2^X ∓ X_mul·ζ on the channel, o = 2v − a.
        let mut image: Vec<BigInt> = v
            .iter()
            .zip(&a_in)
            .map(|(v, a)| (2 * v - a) << x_shift as usize)
            .collect();
        for (kk, &coordinate) in contact.selection[end].iter().enumerate() {
            let exchange = BigInt::from(x_mul) * &zeta[kk];
            if end == 0 {
                image[coordinate] -= exchange;
            } else {
                image[coordinate] += exchange;
            }
        }
        let carried_at = lift(&carried, x_shift);
        let difference: Vec<BigInt> = carried_at.iter().zip(&image).map(|(a, b)| a - b).collect();
        let sum: Vec<BigInt> = carried_at.iter().zip(&image).map(|(a, b)| a + b).collect();
        let sa = lw + x_shift;
        split_power += &quarter * rat(dot(&difference, &sum), 2 * sa);
        split_bound += &quarter * (&unit * rat(l1(&sum), sa));
    }
    (
        dissipation,
        chart_term + split_power,
        chart_bound + split_bound,
    )
}

/// [definition] **The operators a word's balance reads beside the publication's loci**: each
/// contact's operator words and row norm at its carry, and every chart's certificate (rings then
/// contacts, the refinement's readings).
pub(crate) struct Executed<'a> {
    pub(crate) contacts: Vec<(&'a DyadicMatrix, &'a Rat)>,
    pub(crate) readings: &'a [ChartReading],
}

/// **The faces a word read** (module header).
pub(crate) fn faces(
    plan: &WordPlan,
    record: &ForwardRecord,
    count: &CountFace,
) -> Result<Faces, HnnError> {
    let reads: Vec<ReceivingRead> = (0..plan.aperture)
        .map(|j| {
            let wave: Vec<Rat> = slice(&record.logits, j * plan.map_rows, plan.map_rows)
                .iter()
                .map(|l| rat(BigInt::from(*l), plan.logit_exp))
                .collect();
            ReceivingRead::combined(wave, count, plan.grain)
        })
        .collect::<Result<_, _>>()?;
    Faces::of_reads(&reads, plan.grain)
}

/// **The receiving ring's carried anchors** `v_R(e_j)` at the window's epochs.
pub(crate) fn anchors(plan: &WordPlan, record: &ForwardRecord) -> Vec<Vec<Rat>> {
    let ring = &plan.rings[plan.receiver];
    (0..plan.aperture)
        .map(|j| {
            slice(
                &record.anchors,
                (plan.first_epoch + j) * plan.n + ring.rows,
                ring.width,
            )
            .iter()
            .map(|v| rat(BigInt::from(*v), plan.lw))
            .collect()
        })
        .collect()
}

/// **The word's release read at its end** (`Word::released`): its unread change's power, its
/// steps, the peak bits of its change, every full tick's balance, the last junction's residual,
/// its carried remainders and its charts' readings.
pub(crate) fn released(
    plan: &WordPlan,
    loci: &Loci,
    record: &ForwardRecord,
    executed: &Executed<'_>,
) -> Released {
    let (steps, lw) = (plan.steps, plan.lw);
    let rings = plan.rings.len();
    let certificate = |pair: usize| &executed.readings[pair].certificate;
    let mut balances = Vec::with_capacity(steps.saturating_sub(1));
    let mut before = power(plan, loci, &Change::at(plan, record, 0));
    for step in 0..steps.saturating_sub(1) {
        let (mut residual, mut bound) = (Rat::zero(), Rat::zero());
        for g in 0..rings {
            let (r, b) = junction(plan, record, step, g);
            residual += r;
            bound += b;
        }
        let (mut resist, mut contrast) = (Rat::zero(), Rat::zero());
        for g in 0..rings {
            let (r, d, res, b) = element(plan, loci, record, step, g, certificate(g));
            resist += r;
            contrast += d;
            residual += res;
            bound += b;
        }
        let mut dissipation = Rat::zero();
        for a in 0..plan.contacts.len() {
            let (d, res, b) = transit(plan, loci, record, step, a, executed);
            dissipation += d;
            residual += res;
            bound += b;
        }
        let after = power(plan, loci, &Change::at(plan, record, step + 1));
        balances.push(TickBalance {
            before: before.clone(),
            after: after.clone(),
            dissipation,
            resist,
            contrast,
            residual,
            bound,
        });
        before = after;
    }
    let last = (0..rings)
        .map(|g| junction(plan, record, steps - 1, g).0)
        .sum();
    // The peak bits of the change at the open and after each full tick.
    let mut peak = 0u64;
    for step in 0..steps {
        let change = Change::at(plan, record, step);
        for coordinate in change
            .storage
            .iter()
            .chain(change.arrivals)
            .chain(change.u)
            .chain(change.w)
        {
            peak = peak.max(entry_bits(*coordinate, lw));
        }
    }
    // Every carried remainder, released at the word's end.
    let mut remainders: Vec<Rat> = Vec::new();
    for ring in &plan.rings {
        for i in 0..ring.width {
            remainders.push(rat(
                BigInt::from(record.rem_anchor[ring.rows + i]),
                plan.lc + lw,
            ));
            remainders.push(rat(
                BigInt::from(record.rem_storage[ring.rows + i]),
                ring.storage_exp,
            ));
        }
    }
    for (a, contact) in plan.contacts.iter().enumerate() {
        let (solve, arrival, disp, rate, _) = plan.contact_scales(a);
        for i in 0..contact.width {
            let q = contact.rows + i;
            remainders.push(rat(BigInt::from(record.rem_solve[q]), solve));
            remainders.push(rat(BigInt::from(record.rem_disp[q]), disp));
            remainders.push(rat(BigInt::from(record.rem_rate[q]), rate));
        }
        let widths = [
            plan.rings[contact.ends.0].width,
            plan.rings[contact.ends.1].width,
        ];
        for (base, width) in contact.arrival.iter().zip(widths) {
            for i in 0..width {
                remainders.push(rat(BigInt::from(record.rem_arrival[base + i]), arrival));
            }
        }
    }
    Released {
        power: power(plan, loci, &Change::after(plan, record)),
        ticks: steps,
        peak_bits: peak,
        balances,
        last,
        remainders: Remainders::of(&remainders),
        charts: executed.readings.to_vec(),
    }
}

/// [definition] **The return's source on the host** (module header): per receiving epoch the
/// receiving anchor's covector `P_R^(−τ_R) Rᵀ g_j`, split onto `2^(−L_w)ℤ` in reverse epoch order
/// with its carried remainder; the carried reads (one row per epoch) for the card, the released
/// remainder, and the reads the return reports.
pub(crate) struct Source {
    pub(crate) carried: Vec<i64>,
    pub(crate) remainder: Vec<Rat>,
    pub(crate) reads: Vec<(Vec<Rat>, Vec<Rat>)>,
}

/// **Form the return's source** from the ratio's covector, the receiving map's words and the
/// receiving ring's lift at the cut.
pub(crate) fn source(
    field: &Field,
    plan: &WordPlan,
    record: &ForwardRecord,
    covector: &RatioCovector,
    map: &DyadicMatrix,
    lift: &BigInt,
) -> Result<Source, HnnError> {
    if covector.logits().len() != plan.aperture {
        return Err(HnnError::Shape {
            what: "covector phases against the aperture",
            expected: plan.aperture,
            found: covector.logits().len(),
        });
    }
    let ring = field.ring(plan.receiver);
    let width = ring.width();
    let lattice =
        field
            .word_lattice()
            .map(|word| word.transient())
            .ok_or(HnnError::Realization {
                what: "a field whose word runs on no declared lattice",
            })?;
    let anchors = anchors(plan, record);
    let mut images = Vec::with_capacity(plan.aperture);
    let mut reads = Vec::with_capacity(plan.aperture);
    for (j, gradient) in covector.logits().iter().enumerate() {
        // Rᵀ g: the gradient in its integral chart against the map's words.
        let (numerators, denominator) = integral(gradient);
        let scale: BigInt = &denominator * (BigInt::from(1) << map.exponent as usize);
        let pulled: Vec<Rat> = (0..width)
            .map(|column| {
                let sum: BigInt = (0..map.rows)
                    .filter(|&row| !numerators[row].is_zero())
                    .map(|row| {
                        BigInt::from(map.words[row * map.columns + column]) * &numerators[row]
                    })
                    .sum();
                Rat::new(sum, scale.clone())
            })
            .collect();
        images.push(ring.rotate(&pulled, &-lift));
        reads.push((ring.rotate(&anchors[j], lift), gradient.clone()));
    }
    let mut remainder = vec![Rat::zero(); width];
    let mut carried = vec![0i64; plan.aperture * width];
    for j in (0..plan.aperture).rev() {
        let split = carry(&lattice, &images[j], &mut remainder);
        for (i, value) in split.iter().enumerate() {
            let coordinate = value * Rat::from_integer(BigInt::from(1) << plan.lw as usize);
            carried[j * width + i] = num_traits::ToPrimitive::to_i64(&coordinate.to_integer())
                .ok_or(HnnError::Carrier {
                    what: "a receiving covector past the signed 64-bit word",
                })?;
        }
    }
    Ok(Source {
        carried,
        remainder,
        reads,
    })
}

/// **The word's return** (`port::WordReturn`) from the card's reverse record, the forward record
/// and the host's source.
pub(crate) fn word_return(
    plan: &WordPlan,
    loci: &Loci,
    record: &ForwardRecord,
    reverse: &ReverseRecord,
    source: Source,
) -> WordReturn {
    let _ = loci;
    let (n, k, lc, lw, steps) = (plan.n, plan.k, plan.lc, plan.lw, plan.steps);
    let full = steps.saturating_sub(1);
    let opening = plan
        .rings
        .iter()
        .map(|ring| {
            slice(&reverse.opening, ring.rows, ring.width)
                .iter()
                .map(|v| rat(BigInt::from(*v), lw))
                .collect()
        })
        .collect();
    let elements = plan
        .rings
        .iter()
        .map(|ring| {
            let sx = lc + ring.contrast.unwrap_or(0) + lw + 1;
            (0..full)
                .map(|t| {
                    let at = t * n + ring.rows;
                    ElementTick {
                        tick: t,
                        midpoint: slice(&record.mid, at, ring.width)
                            .iter()
                            .map(|x| rat(BigInt::from(*x), sx))
                            .collect(),
                        adjoint: slice(&reverse.adjoint, at, ring.width)
                            .iter()
                            .map(|u| rat(BigInt::from(*u), lw))
                            .collect(),
                        contrast: slice(&record.anchors, at, ring.width)
                            .iter()
                            .zip(slice(&record.storage, at, ring.width))
                            .map(|(v, s)| rat(BigInt::from(*v) - BigInt::from(*s), lw))
                            .collect(),
                    }
                })
                .collect()
        })
        .collect();
    let transits = plan
        .contacts
        .iter()
        .map(|contact| {
            let so = lw + contact.gain_exp;
            (0..full)
                .map(|t| {
                    let at = t * k + contact.rows;
                    let at_lw = |values: &[i64]| -> Vec<Rat> {
                        slice(values, at, contact.width)
                            .iter()
                            .map(|v| rat(BigInt::from(*v), lw))
                            .collect()
                    };
                    TransitTick {
                        tick: t,
                        solved: at_lw(&reverse.solved),
                        displacement: at_lw(&record.u),
                        rate: at_lw(&record.w),
                        midpoint: slice(&record.omega, at, contact.width)
                            .iter()
                            .map(|o| rat(BigInt::from(*o), so))
                            .collect(),
                    }
                })
                .collect()
        })
        .collect();
    // The conductance covector: the transits' parts, then the junctions' (each divided by its
    // ring's admittance sum).
    let contacts = plan.contacts.len();
    let mut conductance = vec![Rat::zero(); contacts];
    let h = &plan.step;
    for (a, contact) in plan.contacts.iter().enumerate() {
        let square = &contact.conductance * &contact.conductance;
        let sd = 2 * lw + contact.gain_exp;
        for t in 0..full {
            let d1 = rat(BigInt::from(reverse.dots1[t * contacts + a]), sd);
            let d2 = rat(BigInt::from(reverse.dots2[t * contacts + a]), sd);
            conductance[a] += integer(2) * h / &square * d1 - integer(2) / &square * d2;
        }
    }
    let mut x = 0usize;
    for ring in &plan.rings {
        for &(a, _, _) in &ring.incident {
            for t in 0..steps {
                let d3 = rat(
                    BigInt::from(reverse.dots3[t * plan.incidences + x]),
                    ring.anchor_exp + lw,
                );
                conductance[a] += d3 / &ring.total;
            }
            x += 1;
        }
    }
    // The return's remainders, released at the open.
    let mut remainders: Vec<Rat> = source.remainder.clone();
    for ring in &plan.rings {
        for i in 0..ring.width {
            let e = ring.rows + i;
            remainders.push(rat(BigInt::from(reverse.rem_el[e]), lc + lw));
            remainders.push(rat(
                BigInt::from(reverse.rem_storage[e]),
                lc + ring.anchor_exp,
            ));
        }
    }
    let (_, h_shift, _, _) = plan.hop();
    for contact in &plan.contacts {
        let sc = contact.storage_exp.unwrap_or(0);
        let sk = contact.stiffness_exp.unwrap_or(0);
        for i in 0..contact.width {
            let q = contact.rows + i;
            remainders.push(rat(BigInt::from(reverse.rem_zeta[q]), contact.zeta_exp));
            remainders.push(rat(BigInt::from(reverse.rem_solved[q]), lc + lw));
            remainders.push(rat(BigInt::from(reverse.rem_rate[q]), sc + lw));
            remainders.push(rat(BigInt::from(reverse.rem_disp[q]), sk + lw + h_shift));
        }
        for (end, ring) in [contact.ends.0, contact.ends.1].into_iter().enumerate() {
            let target = &plan.rings[ring];
            for i in 0..target.width {
                remainders.push(rat(
                    BigInt::from(reverse.rem_arrival[contact.arrival[end] + i]),
                    lc + target.anchor_exp,
                ));
            }
        }
    }
    WordReturn {
        opening,
        elements,
        transits,
        conductance,
        reads: source.reads,
        released: Remainders::of(&remainders),
    }
}

/// Zero test for a coordinate (a helper for readings that skip zero terms).
#[allow(dead_code)]
fn is_zero(value: &BigInt) -> bool {
    value.is_zero() || value.abs().is_zero()
}
