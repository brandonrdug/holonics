//! **A section: read, return, deposit.**
//!
//! a section's regions read on the card, their covector returned and deposited; the learner's state is its constitution, its
//! moments, its rates and the pass's place (`StorePass`)
//!
//! Kind: chain over the sections. Kernels: the realization's (above).
//! Lean: `Foundation/Standing`.
//! Atlas: `tower.field-completion-covector`, `tower.field-deposit`, `tower.field-own-states`, `tower.field-step-price`, `tower.store-stretch-cut`,
//! `tower.store-frontier-state`.
//! Records: `2026-11-01_THE_PROBLEM_IS_ONE_FIELD…`, `2026-11-15_THE_OWN_STATES…`. The derivations' history is in the records; the items below keep
//! their reasons.

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use rayon::prelude::*;

/// [measurement; theory, November 13, P58 item 4] **The deposit's parts on the host**, summed over every section a process realizes (ns; a
/// reading, no state changes), in the order [`Learner::section_realized`] runs them ([`SECTION_PART_NAMES`]).
pub static SECTION_PARTS: [std::sync::atomic::AtomicU64; 15] = [const { std::sync::atomic::AtomicU64::new(0) }; 15];

/// [measurement; P58 item 4] The names of [`SECTION_PARTS`], with the whole-layout passes each makes over the constitution's entries.
pub const SECTION_PART_NAMES: [&str; 15] = [
    "read_and_return",
    "compared_and_code",
    "covector_clone",
    "transfer_price",
    "entry_rates",
    "external_step",
    "external_price",
    "covector_grains",
    "deposit_pass",
    "step",
    "step_price",
    "reading_parts",
    "parts_price",
    "stepped",
    "rest",
];

/// A deposited step held for the next regions' read: the proposed step on each family's grain and
/// the halvings it stood at. The material before it is the material less nothing: the deposit
/// subtracted `release(step, halvings)` from each entry, so adding it back restores every bit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct HeldStep {
    pub(crate) step: Vec<i128>,
    pub(crate) halvings: u32,
}

/// Each unresolved site's face read at its class, the faces the section's code and the held read compare.
/// [definition; agent-inferred, November 3, §16.24] **A section's compared reading**: each open site's face at its
/// class before its region's port (`(mass, total)`), and the ports' coupling codes summed on `2^(−20)` bits.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Compared {
    pub(crate) pairs: Vec<(u128, u128)>,
    pub(crate) coupled: i64,
    pub(crate) ported: bool,
}

/// [realization; theory, November 13, P58 item 3] Each region's faces read at their classes, `(m_c, T)` where a site carries a face.
pub fn faces_at_class(faces: &[Vec<Option<TowerFace>>], regions: &[Region]) -> Vec<Vec<Option<(u128, u128)>>> {
    // [the lead, November 23] A passage read by two streams is read at its targets ([`Region::targets`]), none at a place not compared.
    faces.iter().zip(regions).map(|(f, r)| f.iter().zip(r.targets.unwrap_or(r.classes)).map(|(face, &c)| face.as_ref().filter(|_| c != UNCOMPARED).map(|face| (face.masses[c], face.total))).collect()).collect()
}

/// [`compared`] from the faces read at their classes ([`faces_at_class`]), where no region has a port: the same pairs.
pub(crate) fn compared_at_class(at_class: &[Vec<Option<(u128, u128)>>], regions: &[Region]) -> Result<Compared> {
    if at_class.len() != regions.len() || regions.iter().any(|r| r.port.is_some()) {
        return refuse("faces at their classes are compared one row a region, with no port");
    }
    // A place read and not compared ([`UNCOMPARED`]) counts in no code.
    let compared_at = |r: &Region, t: usize| r.targets.is_none_or(|tg| tg[t] != UNCOMPARED);
    Ok(Compared { pairs: at_class.iter().zip(regions).flat_map(|(f, r)| f.iter().take(r.classes.len()).enumerate().filter(move |&(t, _)| compared_at(r, t)).filter_map(|(_, p)| *p)).collect(), coupled: 0, ported: false })
}

pub(crate) fn compared(faces: &[Vec<Option<TowerFace>>], regions: &[Region]) -> Result<Compared> {
    let mut out = Compared { pairs: Vec::new(), coupled: 0, ported: false };
    for (f, r) in faces.iter().zip(regions) {
        let end = r.port.map_or(r.classes.len(), |p| p.start);
        out.pairs.extend(f.iter().zip(r.targets.unwrap_or(r.classes)).take(end).filter(|(_, c)| **c != UNCOMPARED).filter_map(|(face, &c)| face.as_ref().map(|face| (face.masses[c], face.total))));
        if let Some(port) = r.port {
            out.coupled += port_code(f, &port)?;
            out.ported = true;
        }
    }
    Ok(out)
}

/// Each region's run of compared sites before its port and its weight in the joint code, `(K, m, K)`
/// ([`Region::weight`], §16.23), in the order [`compared`] reads them.
/// [the lead, November 18] A passage read by two streams ([`Region::strand`]) compares every place past its first at weight one: its
/// compared places are its domain.
pub(crate) fn spans_of(regions: &[Region]) -> Vec<(usize, u64, u64)> {
    regions
        .iter()
        .map(|r| {
            if r.strand {
                // [the lead, November 23] Its places past the first that are compared ([`UNCOMPARED`]).
                let places = (1..r.classes.len()).filter(|&t| r.targets.is_none_or(|tg| tg[t] != UNCOMPARED)).count();
                return (places, places as u64, places as u64);
            }
            let (m, k) = r.weight();
            (r.unresolved[..r.port.map_or(r.unresolved.len(), |p| p.start)].iter().filter(|&&u| u).count(), m, k)
        })
        .collect()
}

/// Whether `new` codes strictly fewer bits than `old`. Where a port is read, its coupling code has no product form, so
/// the decision is the codes' on their grain (`2^(−20)` bits, §16.24); otherwise it is the held read's weighed comparison.
pub(crate) fn fewer(old: &Compared, new: &Compared, spans: &[(usize, u64, u64)]) -> bool {
    if old.ported || new.ported {
        code_of(new, spans) < code_of(old, spans)
    } else {
        fewer_bits_weighed(&old.pairs, &new.pairs, spans)
    }
}

/// [measurement; agent-inferred, November 4, §16.41] **A step's first-order change of the code it was fit on**: `Σ_i g_i Δθ_i`
/// with `Δθ = −step` at its full size and `g` the section's covector as its return gives it, on the codes' `2^(−20)` bits, a
/// unit of `g Δθ` standing at `2^(−(40 + grain − 20))` bits on the material's families and `2^(−(24 + grain − 20))` on the
/// faces' (the covector's grains, as `covector_matches_the_codes_difference` reads them); `None` where a product or the sum
/// passes its carrier. At the full step it is the first coefficient `a` of the section's own parabola `e(μ) = aμ + bμ²`; no
/// reread reads the second since the step fluxes (November 5), so `b` is unread on the section itself. With the next
/// section's covector and the step at the halvings it stood at, it is the step's transfer ([`Receipt::transfer`]).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn predicted_change(field: &Constitution, g: &[i128], step: &[i128], halvings: u32) -> Option<i64> {
    let mut total = 0i128;
    for &(start, len, grain) in &field.families_all() {
        let shift = if grain == MATERIAL_BITS { 40 + grain - 20 } else { 24 + grain - 20 };
        let mut family = 0i128;
        for i in start..start + len {
            family = family.checked_add(g[i].checked_mul(-release(step[i], halvings))?)?;
        }
        total = total.checked_add(family >> shift)?;
    }
    i64::try_from(total).ok()
}

/// [measurement; theory, November 12, G96's third branch] **A step's first-order change by founded part**: [`predicted_change`]'s
/// sum with each family's terms gathered by the part each entry belongs to (`parts`, [`Constitution::founded_parts`]; index [`PARTS`] the
/// old entries, which no part holds), each gathered family sum released onto the codes' `2^(−20)` bits as the total releases it.
/// So the parts sum to the total less the releases' floors, at most one unit a family and part, which a reader keeps as the
/// total's rest. `None` where a product or a sum passes its carrier. A reading: the step is not changed. Why: a section's
/// predicted price is a total over every part, and a reading names its partition beside its total (the guide's rule of November
/// 11); on tp5 that price burst a hundredfold before the card refused a sum, and which part's covector burst is the question
/// G96's rule asks before eight times returns.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn predicted_parts(field: &Constitution, g: &[i128], step: &[i128], halvings: u32, parts: &[u8]) -> Option<[i64; PARTS + 1]> {
    let mut by = [0i128; PARTS + 1];
    for &(start, len, grain) in &field.families_all() {
        let shift = if grain == MATERIAL_BITS { 40 + grain - 20 } else { 24 + grain - 20 };
        let mut family = [0i128; PARTS + 1];
        for i in start..start + len {
            let p = parts.get(i).map_or(PARTS, |&p| if p == OLD_PART { PARTS } else { usize::from(p) });
            family[p] = family[p].checked_add(g[i].checked_mul(-release(step[i], halvings))?)?;
        }
        for (b, f) in by.iter_mut().zip(family) {
            *b = b.checked_add(f >> shift)?;
        }
    }
    let mut out = [0i64; PARTS + 1];
    for (o, b) in out.iter_mut().zip(by) {
        *o = i64::try_from(b).ok()?;
    }
    Some(out)
}

/// What one section's deposit pass returns ([`deposit_pass`]): the step, and the four first-order prices a section's receipt carries
/// ([`Receipt`]: the transfer of the step before, the external price, the step's own and its parts').
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DepositPass {
    pub(crate) step: Vec<i128>,
    pub(crate) transfer: Option<i64>,
    pub(crate) external: Option<i64>,
    pub(crate) predicted: Option<i64>,
    pub(crate) parts: Option<[i64; PARTS + 1]>,
}

/// A chunk's sums of the four prices on their families' grains, each `None` once a product or a sum passed its carrier.
#[derive(Clone, Copy)]
struct PriceSums {
    transfer: Option<i128>,
    external: Option<i128>,
    predicted: Option<i128>,
    parts: Option<[i128; PARTS + 1]>,
}

impl PriceSums {
    fn zero(transfer: bool) -> Self {
        Self { transfer: transfer.then_some(0), external: Some(0), predicted: Some(0), parts: Some([0; PARTS + 1]) }
    }

    fn join(self, o: Self) -> Self {
        let add = |a: Option<i128>, b: Option<i128>| a.zip(b).and_then(|(a, b)| a.checked_add(b));
        let parts = self.parts.zip(o.parts).and_then(|(a, b)| {
            let mut out = [0i128; PARTS + 1];
            for k in 0..=PARTS {
                out[k] = a[k].checked_add(b[k])?;
            }
            Some(out)
        });
        Self { transfer: add(self.transfer, o.transfer), external: add(self.external, o.external), predicted: add(self.predicted, o.predicted), parts }
    }
}

/// `g · (−s)` added to a price's sum, `None` once the product or the sum passes its carrier.
fn price_term(sum: &mut Option<i128>, g: i128, s: i128) {
    *sum = sum.and_then(|a| g.checked_mul(-s).and_then(|p| a.checked_add(p)));
}

/// [realization; the lead, November 20, the engineering report's host deposit (A4 and the phases read)] **A section's deposit in one pass
/// a family**: for each entry, its external step from the moments before (`deposit_step` at its rate), its covector on the step's grain
/// ([`on_step_grain`]), its moments moved ([`toward`], or opened at its first nonzero covector), its step from the moments after (with its
/// carried remainder where the learner carries one), and its terms of the four prices: [`predicted_change`]'s sum for the transfer of the
/// step before (`last`, at its halvings), the external price and the step's own, and [`predicted_parts`]'s by founded part (`parts`).
/// Every entry reads only its own moments, rate, remainder and covector, so the entries are split across the host's cores in chunks; each
/// price's terms meet on their family's grain and are released once a family (`≫ shift`), as [`predicted_change`] releases them, so the
/// chunks' sums give the same bits in any bracketing (integer sums, the guide's precision law). A product or a sum past its 128-bit carrier
/// reads `None` for that price as it did; the only reading that can differ from the serial order's is a `None` at partial sums past
/// `2^127` in one bracketing and not another, where the line's largest price stands near `2^40` (`agent-inferred`). A covector's square
/// past its carrier refuses the section, as it did. Entries no family holds keep the serial law's treatment: moments moved by the raw
/// covector, no step and no price. Why: on the store line at 1,859,961 entries the section's deposit took about 58 ms on the host, eight
/// whole-layout passes four of them serial, while the card stood idle (`STORE_DEPOSIT_PARTS`, the phases read of November 20); every bit
/// of the step, the moments, the remainders and the prices stands as the serial passes formed them (the test
/// `the_deposit_in_one_pass_is_the_serial_passes_bit_for_bit`).
#[allow(clippy::too_many_arguments)]
pub(crate) fn deposit_pass(families: &[(usize, usize, u32)], g: &[i128], first: &mut [i128], second: &mut [i128], rates: &[u32], mut remainder: Option<&mut [i64]>, mut carried: Option<(&mut [i32], &mut [i32])>, last: Option<&HeldStep>, parts: &[u8]) -> Result<DepositPass> {
    // A chunk of entries a core takes at once; seven under test, so the tiny fields' families are cut in many places.
    #[cfg(not(test))]
    const CHUNK: usize = 1 << 13;
    #[cfg(test)]
    const CHUNK: usize = 7;
    let n = first.len().min(second.len()).min(g.len());
    let last = last.filter(|l| l.step.len() >= n);
    let mut step = vec![0i128; n];
    // The families as a partition: sorted by start, disjoint (the serial passes would have grained an entry once a family it lies in).
    let mut sorted: Vec<(usize, usize, u32)> = families.iter().copied().filter(|&(start, len, _)| len > 0 && start < n).collect();
    sorted.sort_unstable_by_key(|f| f.0);
    if sorted.windows(2).any(|w| w[0].0 + w[0].1 > w[1].0) || sorted.iter().any(|&(start, len, _)| start + len > n) {
        return refuse("a deposit over families that overlap or pass the material");
    }
    let refused = || TowerError::Refused("a covector's square outgrew its 128-bit carrier");
    let (mut transfer, mut external, mut predicted) = (last.map(|_| 0i128), Some(0i128), Some(0i128));
    let mut by = Some([0i128; PARTS + 1]);
    let mut at = 0usize;
    for &(start, len, grain) in &sorted {
        // Entries before this family that no family holds: moments moved by the raw covector, no step.
        for k in at..start {
            let square = g[k].checked_mul(g[k]).ok_or_else(refused)?;
            if first[k] == 0 && second[k] == 0 {
                (first[k], second[k]) = (g[k], square);
            } else if let Some((cf, cs)) = carried.as_mut() {
                first[k] = toward_carried(first[k], &mut cf[k], g[k], FIRST_RATE)?;
                second[k] = toward_carried(second[k], &mut cs[k], square, SECOND_RATE)?;
            } else {
                first[k] = toward(first[k], g[k], FIRST_RATE);
                second[k] = toward(second[k], square, SECOND_RATE);
            }
        }
        at = start + len;
        let shift = if grain == MATERIAL_BITS { 40 + grain - 20 } else { 24 + grain - 20 };
        let chunks = len.div_ceil(CHUNK);
        let rems: Vec<Option<&mut [i64]>> = match remainder.as_deref_mut() {
            Some(r) => r[start..start + len].chunks_mut(CHUNK).map(Some).collect(),
            None => (0..chunks).map(|_| None).collect(),
        };
        // [the lead, November 21, E4 of #1088] The moments' carried remainders, chunked as the moments are.
        let cars: Vec<Option<(&mut [i32], &mut [i32])>> = match carried.as_mut() {
            Some((cf, cs)) => cf[start..start + len].chunks_mut(CHUNK).zip(cs[start..start + len].chunks_mut(CHUNK)).map(Some).collect(),
            None => (0..chunks).map(|_| None).collect(),
        };
        let chunk = |c: usize, m: &mut [i128], v: &mut [i128], s: &mut [i128], mut r: Option<&mut [i64]>, mut car: Option<(&mut [i32], &mut [i32])>| -> Result<PriceSums> {
            let mut sums = PriceSums::zero(last.is_some());
            let mut parts_ok = true;
            for j in 0..m.len() {
                let k = start + c * CHUNK + j;
                let raw = g[k];
                if let Some(l) = last {
                    price_term(&mut sums.transfer, raw, release(l.step[k], l.halvings));
                }
                price_term(&mut sums.external, raw, deposit_step(m[j], v[j], grain, rates[k]));
                let gk = on_step_grain(grain, raw);
                let square = gk.checked_mul(gk).ok_or_else(refused)?;
                if m[j] == 0 && v[j] == 0 {
                    (m[j], v[j]) = (gk, square);
                } else if let Some((cf, cs)) = car.as_mut() {
                    m[j] = toward_carried(m[j], &mut cf[j], gk, FIRST_RATE)?;
                    v[j] = toward_carried(v[j], &mut cs[j], square, SECOND_RATE)?;
                } else {
                    m[j] = toward(m[j], gk, FIRST_RATE);
                    v[j] = toward(v[j], square, SECOND_RATE);
                }
                s[j] = match r.as_deref_mut() {
                    None => deposit_step(m[j], v[j], grain, rates[k]),
                    Some(carried) => {
                        let fine = deposit_step(m[j], v[j], grain + REMAINDER_BITS, rates[k]);
                        let sum = i128::from(carried[j]) + fine;
                        let whole = sum >> REMAINDER_BITS;
                        carried[j] = (sum - (whole << REMAINDER_BITS)) as i64;
                        whole
                    }
                };
                price_term(&mut sums.predicted, raw, s[j]);
                if parts_ok && let Some(p) = sums.parts.as_mut() {
                    let at = parts.get(k).map_or(PARTS, |&p| if p == OLD_PART { PARTS } else { usize::from(p) });
                    match raw.checked_mul(-s[j]).and_then(|x| p[at].checked_add(x)) {
                        Some(x) => p[at] = x,
                        None => parts_ok = false,
                    }
                }
            }
            if !parts_ok {
                sums.parts = None;
            }
            Ok(sums)
        };
        let fam = first[start..start + len]
            .par_chunks_mut(CHUNK)
            .zip(second[start..start + len].par_chunks_mut(CHUNK))
            .zip(step[start..start + len].par_chunks_mut(CHUNK))
            .zip(rems.into_par_iter())
            .zip(cars.into_par_iter())
            .enumerate()
            .map(|(c, ((((m, v), s), r), car))| chunk(c, m, v, s, r, car))
            .try_reduce(|| PriceSums::zero(last.is_some()), |a, b| Ok(a.join(b)))?;
        let close = |total: Option<i128>, family: Option<i128>| total.zip(family).and_then(|(t, f)| t.checked_add(f >> shift));
        transfer = close(transfer, fam.transfer);
        external = close(external, fam.external);
        predicted = close(predicted, fam.predicted);
        by = by.zip(fam.parts).and_then(|(mut b, f)| {
            for k in 0..=PARTS {
                b[k] = b[k].checked_add(f[k] >> shift)?;
            }
            Some(b)
        });
    }
    for k in at..n {
        let square = g[k].checked_mul(g[k]).ok_or_else(refused)?;
        if first[k] == 0 && second[k] == 0 {
            (first[k], second[k]) = (g[k], square);
        } else if let Some((cf, cs)) = carried.as_mut() {
            first[k] = toward_carried(first[k], &mut cf[k], g[k], FIRST_RATE)?;
            second[k] = toward_carried(second[k], &mut cs[k], square, SECOND_RATE)?;
        } else {
            first[k] = toward(first[k], g[k], FIRST_RATE);
            second[k] = toward(second[k], square, SECOND_RATE);
        }
    }
    let narrow = |v: Option<i128>| v.and_then(|v| i64::try_from(v).ok());
    let parts = by.and_then(|b| {
        let mut out = [0i64; PARTS + 1];
        for (o, v) in out.iter_mut().zip(b) {
            *o = i64::try_from(v).ok()?;
        }
        Some(out)
    });
    Ok(DepositPass { step, transfer: narrow(transfer), external: narrow(external), predicted: narrow(predicted), parts })
}

/// [definition; agent-inferred, November 1] **The field's learner**: the field, the covector's two
/// moments and the step's rate `2^(−k)`. The deposit is the tower's ([`super::TowerLearner`]),
/// with one difference: a coordinate's moments open at its own first nonzero covector (`m = g`,
/// `v = g²`), not at the section the learner first read. The returns and the readout open at zero,
/// so the charts' covectors first arrive sections later; moments opened from zero would step them
/// two to four times the declared rate until the second moment caught up (the review of
/// November 1).
///
/// **The step deposits at its size** (Brandon, November 5: the step fluxes): `m/(⌊√v⌋ + 1)` at
/// `2^(−rate)`, at most about 4.2 times its rate by Cauchy–Schwarz over the moments' rates
/// (agent-inferred), and no reread decides it. What it does is priced as the learner passes:
/// predicted on its own section, transferred onto the next section's covector, and external before
/// the covector moves the moments ([`Receipt`]); the moments carry every covector, a
/// contraction's and an expansion's alike.
///
/// History, kept as history. *November 1*: **a step was held and read on the next regions** (the
/// tower's acceptance 77, [`super::TowerLearner::next_section`]): a step certified on its own
/// section was held, and the next section's regions were read under the material before it and its
/// size read on them by the one bounded law of a step's size ([`scaled`]): it stood at its size, at
/// half, or at the parabola's halving where it coded them no higher, or was refused (the material
/// before it stood). The moments stayed as they moved. Why (the first reading on the card,
/// November 1): the certificate read only its own section, and the held-out answer code rose at the
/// second lap and the third (5.38, 5.49, 6.18 bits a class) while the passage's own code fell every
/// section; the tower had recorded this failure and its repair, and the field had been built without
/// it. *November 3*: the held read was set aside ([`Learner::read_held`], `false`, with its
/// reason there) and stands since as a declared comparison only. *November 5*: the certificate
/// itself was retired, because it kept a step only where its own section reread lower, a selection
/// on the code that discarded what an expansion measures ([`Learner::section_realized`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Learner {
    pub field: Constitution,
    pub(crate) first: Vec<i128>,
    pub(crate) second: Vec<i128>,
    pub rate_bits: u32,
    /// The founding key bytes read so far: the founding's, then each growth's.
    pub drawn: usize,
    /// The laps the learner has read (an exterior walk's count, so a continued run keeps its
    /// keyed masks and order moving rather than replaying the first lap's).
    pub laps: u64,
    pub(crate) held: Option<HeldStep>,
    /// [definition; agent-inferred, November 3, §16.30] Whether a deposited step is held and read on the next regions
    /// before it stands (the tower's acceptance 77). The field's law is `false`: a step stands at its size (certified
    /// on its own section, strictly fewer bits there, [`scaled`], until November 5; since then the step fluxes), and the
    /// next regions are read under it as they come. The reason below is the November 3 reading, when the certificate
    /// still stood.
    /// Why: from the same trained state, two laps read the held answers' joint code at 3.200 and 3.160 bits a byte with
    /// the steps standing unread against 3.204 and 3.174 with the next-section read, in 171 s a lap against 280 s (the
    /// read refused 30% of the steps and halved 55%: a step that lowers its own section's code raises another
    /// section's about as often as gradient noise says, so the read mostly threw away and shrank good steps). `true`
    /// keeps the read as a declared comparison. Not carried in the learner's text.
    pub read_held: bool,
    /// [definition; theory, November 10 19:05] The founded parts' deposit rates ([`RateParts`]), carried in the learner's text; none
    /// (every entry at `rate_bits`) in a state without them.
    pub rate_parts: Option<RateParts>,
    /// [definition; theory, November 12 00:20, the Einstein record's U2] **Each entry's own deposit rate**, in bits (the entry steps at
    /// `2^(−rate)`), set between laps by the host law (`tools/part_rates.py blocks`: every block of the material a part of its own, its
    /// rate following its polarization, under the base word where that stands under the floor's) and carried in the learner's text as a
    /// trailing `rates` line, one count an entry. Where it stands it is every entry's rate ([`Learner::entry_rates`]); the parts'
    /// line is kept beside it for its contacts count. None in a state without the line, and after every growth (the law sets it again) but the
    /// triads' ([`Learner::with_triads`]), which keeps each old entry's own rate and opens the triads' entries at the base rate.
    pub own_rates: Option<Vec<u32>>,
    /// [definition; the lead, November 17, the step back's record §11] **The store's leak**, in bits: after a section's step every material
    /// entry relaxes toward rest by `2^(−leak)` of itself, `θ ← θ − release(θ, leak)` (to the nearest grain, a half away from zero, so an
    /// entry under `2^(leak − 1)` grains stands where it is). An entry held by its own rate (past [`HELD_RATE`] bits) is outside the
    /// deposit and does not leak. Why: no store is at rest (CLAUDE.md, November 11): a store holds by upkeep and relaxes through its one
    /// coupling, and the deposit had none, so an entry moved once stood for ever and a structure the passage keeps driving had no advantage
    /// over what one section left behind. With the leak an entry's steady state is `2^(leak − rate)` times the mean of its own step's
    /// ratio `m / (⌊√v⌋ + 1)`: what its flux keeps up. Carried in the learner's text as a trailing `leak K` line after the rates' and only
    /// where set, so every state without one reads and writes byte for byte as before; none on a state without the line. Kept by every
    /// growth. Its value is a trial's bracket until a law gives it (`agent-inferred`, November 17: the deposit's own rate was the first
    /// candidate, the balance of a store's noise against its dissipation). Read on November 22 (`agent-inferred`; that day's record on a
    /// release, §3.3 and §5.4): a part the code reads as a ratio to its own power rests under the leak at a root mean square of
    /// `2^(−rate) √(c 2^(leak − 1))`, `c` its growth of power an entry a section over `2^(−2 rate)`, and turns there by the leak alone.
    /// So at the rate itself such a part shrinks to a sixteenth of the store line's sizes and turns fifteen times as far a section;
    /// the leak that keeps a part where it stands is `1 + 2 log₂(rms · 2^rate) − log₂ c` bits, 16 to 23 by block on the floor line of
    /// November 11, and one value rests no two parts alike.
    pub leak: Option<u32>,
    /// [definition; the lead, November 18, the audit of that day §1.8; the precision law (a term is released only by partition, its
    /// remainder accounted)] **The step's carried remainder**, one an entry, on [`REMAINDER_BITS`] bits under the entry's own grain. Where
    /// it is carried, a section's step is formed at that finer grain, `((m ≪ (grain + REMAINDER_BITS)) ≫ rate) / (⌊√v⌋ + 1)`, added to the
    /// entry's remainder, and released to the entry's grain by its whole part (the floor), the rest staying in the remainder for the next
    /// section. Without it the step is the truncated quotient, so an entry whose ratio `m / (⌊√v⌋ + 1)` times `2^(grain − rate)` stands
    /// under one takes no step at all: on the line 38 to 47% of the encodings' entries a section at rate 12, and every one of them at a
    /// rate of 16, which is what bars a cooler deposit from being read. Carried in the learner's text as a trailing `remainder` line after
    /// the leak's and only where present; a state without the line has the truncating step.
    pub remainder: Option<Vec<i64>>,
    /// [definition; the lead, November 21, E4 of #1088 (the precision record §4.4; Lean `HNN/LatticeDeposit`, `release_tracks`)] **The moments'
    /// carried remainders**, one a moment an entry, each on the grain `2^(−rate)` of its moment's own grain. Where carried, a moment moves
    /// toward its input as `t = (g − m) + r`, `m ← m + release(t, rate)`, `r ← t − release(t, rate) 2^rate`: what a section's move drops under
    /// the moment's grain waits in `r` and moves the moment when it carries, so the moment stays within a grain of its true mean at any size.
    /// Without them a move that releases to zero is forced to one grain toward its input ([`toward`]), a step that stands where a carried
    /// remainder belongs. Carried in the learner's text as two trailing lines (`carried_first`, `carried_second`) after the remainder's,
    /// and only where present; a state without them has the forced grain.
    pub carried: Option<(Vec<i32>, Vec<i32>)>,
    /// [definition; the lead, November 21, E5 of #1088 (the October lattice deposit; Lean `HNN/LatticeDeposit`, `lattice_deposit_accounting`;
    /// atlas `hnn.lattice-deposit`)] **The forward reads each family's read part, and the deposit integrates under it**: each entry is its
    /// read part on its family's lattice plus a carried rest under half of that lattice's unit, and the material every forward and every
    /// reader reads is the read part. A section's step adds to the read part and its rest, and the read part moves only where their sum
    /// crosses a lattice point, so `read + rest + Σ released = start + Σ steps`.
    /// [definition; the lead, November 22, the second precision pass (the record of November 21, "a grain is a relation between grains",
    /// §4 and §7; atlas `radix.grain-is-a-relation`)] **A family's lattice is a relation to its own spread**: its unit is the power of two one
    /// place under its whole words' standing spread (the rms of a save's end less the mean of the states since the save before), read from
    /// the machine at a save and carried in this line, never a tolerance handed in by number ([`Lattice`]). Carried in the learner's text as
    /// two trailing lines (`lattice`, `lattice_rest`) after the moments' carried lines, and only where present.
    pub lattice: Option<Lattice>,
    /// [measurement; §16.41] The step the last section stood at, the operand of the next section's
    /// [`Receipt::transfer`]; a reading's operand, not carried in the learner's text, cleared by every growth, and not
    /// kept under the held read (whose next section moves the step before pricing it).
    pub(crate) last: Option<HeldStep>,
    /// [definition; theory, November 12 (the record of the opening's room, §4 item 5)] **The pass's place** over a store of documents
    /// ([`StorePass`]), carried as the learner's text's last line and only where present, so every state of the code line reads and
    /// writes byte for byte as before; none on a learner that has not crossed to a store. Kept by every growth.
    pub pass: Option<StorePass>,
}

/// [definition; theory, November 12 (the record of the opening's room, §4 items 1, 3 and 5)] **A pass's place over a store of
/// documents**: the store's role read (its prefix, its training store) and the SHA-256 of its `STORE.tsv`, the stretches taken, the law
/// of a stretch's two draws (contexts and runs each on an octave uniform over `least·[2^0, 2^1)` to `least·[2^(octaves−1), 2^octaves)`),
/// the section's two declared bounds (its regions' pairs of sites and its sites), and each slice's place, in the store's order: its piece,
/// its cursor in the piece and the places taken from it. The cut itself (the trainer's, `train-store`) reads only this line and the store.
/// Why in the learner's state (the record §4 items 3 and 5): a section is the unit a deposit consumes, so its extent is law and is carried
/// in the state, never read from the device or a run's argument; the pass's place is what a continued run reads on from.
///
/// [definition; agent-inferred, November 15, the record of the states a field trains on, §3 and §5] `own`: **the states are the field's
/// own**, each stretch's one state the release's own at a crossing of its octaves ([`crate::passage::own_state_of`]) in place of a keyed
/// draw ([`crate::passage::state_of`]). Written as the word `own` after the bounds and only where set, so every state of the line reads and
/// writes byte for byte as before. Why in the state: which states a field trains on is law (it sets the temperature the field holds, the
/// record §1), and a law is carried in the learner's state, never in a run's switch (CLAUDE.md, November 8).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StorePass {
    pub role: String,
    pub store: String,
    pub stretches: u64,
    pub least: u64,
    pub octaves: u64,
    pub pairs: u64,
    pub sites: u64,
    pub own: bool,
    pub slices: Vec<PassSlice>,
    /// [definition; agent-inferred, November 16, the theory thread's Build B of 18:58 UTC] The world that answers the field's act, where one
    /// is joined ([`PassWorld`]).
    pub world: Option<PassWorld>,
    /// [definition; agent-inferred, the lead, November 18, the audit of that day §1.4 and the night's text run] **The frontier's share**: of
    /// every eight stretches, keyed by the stretch's count, this many are read at the frontier ([`crate::passage::frontier_cut_of`],
    /// [`crate::passage::frontier_state_of`]): the context known and the next place alone open, the region ending there, which is the
    /// state a writer in place order meets at every place it writes. Zero where the pass has none. Written as the line's last two words,
    /// `frontier E`, and only where set, so every state of the line reads and writes byte for byte as before. Why in the state: which
    /// states a field trains on is law (CLAUDE.md, November 8). Why the share: from lap 1 to lap 94 the line compared a place at the
    /// writer's frontier only among a writer state's open places, about 92% of which lie past it (the audit's count from the law, §1.4);
    /// fifteen passes compared there alone took the panel written one place a read from 38% to 76% of its words in the lexicon (the
    /// level's design record of November 17, §12).
    pub frontier: u64,
    /// [definition; the lead, November 18, the frontier record §6; `agent-inferred`] **The frontier's stretches are read as known streams**
    /// ([`crate::field::Region::before`]): each known place of a stretch at the frontier hears only what stands before it, which is the row a
    /// passage read by two streams gives its open place ([`crate::field::Constitution::strand_pass`]), so a state trained on it stands in
    /// the regime that read is in. Written as the word `before` after the frontier's share (`frontier E before`), only where set; a pass
    /// with no frontier share has none.
    pub before: bool,
    /// [definition; the lead, November 18, the frontier record §6; `agent-inferred`] **The frontier's stretches are read by two streams**
    /// ([`crate::field::Region::strand`]): the stretch is its known stream and an open place at every place, so every place of it is
    /// compared at its own frontier in one forward, where a stretch read at the frontier compares its last place alone. Written as the
    /// word `strand` after the frontier's share (`frontier E strand`), only where set, and never beside `before`.
    pub strand: bool,
    /// [the lead, November 18] **Their odd strand contacts face the past** ([`crate::field::Region::past`]): the word `past` after
    /// `before` or `strand` (`frontier E strand past`), only where set.
    pub past: bool,
    /// [the lead, November 18, the record of the two streams §15] **Their row of the site after reads the second site before**
    /// ([`crate::field::Region::second`]): the word `second` last, after `before` or `strand` and after `past` where that stands
    /// (`frontier E strand past second`), only where set.
    pub second: bool,
    /// [definition; the lead, November 21, Brandon's 04:54Z] The terrain whose own records the pass meets beside its slices, held by its
    /// tension ([`PassTerrain`]); written as its own line after the pass line, only where set.
    pub terrain: Option<PassTerrain>,
    /// [definition; the lead, November 24, Brandon's 21:57Z ("ultimately I'd prefer simultaneous"); `agent-inferred`, a guess at the law
    /// fixed before its arm] **The slices held by their tension**: each slice's field code at its open places in the last section that read
    /// it (millionths of a bit a place, the opening's code the section's receipt reads), in the store's order. Where set, the cut takes the
    /// slice whose own clock stands furthest behind ([`StorePass::slice_clock`], [`crate::passage::Cut::next`]), so a slice is read at its octets' share weighed by how
    /// much news it still holds for the field: the terrain's law of November 21 ([`PassTerrain`]), read between the passage's slices. Every
    /// piece is still read once a pass and in order; only the interleave moves. A slice with no reading yet weighs as the mean of those
    /// with one (as its quota alone where none has). Written as its own line `tension T₀ … T_(k−1)` after the pass's (and its terrain's),
    /// only where set.
    pub slice_tension: Option<Vec<u64>>,
    /// [definition; the lead, November 25, W113s's reading and Brandon's 03:03Z] **Each slice's own clock under its tension**:
    /// `c_s = Σ places / p_s` over the stretches it gave since its tension was set, `p_s = quota_s T_s / Σ_r quota_r T_r` its share of her
    /// news when it was read ([`crate::passage::clock_step`]), so the clock counts the passage's own places and a slice is due again a gap of
    /// `1/p_s` of them after its last read. Where the tensions are set the cut takes the slice whose clock stands furthest behind
    /// ([`crate::passage::Cut::next`]), so a change of tension moves the rate a slice is read at from then on and carries no debt from
    /// before it. Why: the first form compared `taken_s / (quota_s · T_s)` over the whole pass, so a slice read at its quota for most of a
    /// pass and then given a low tension owed every place read before it: on W113s (from W112's state, 108 million places into its pass) her
    /// conversations and her tool turns, at the two lowest tensions, were read in its first section and in none of the 2,999 after it,
    /// against 2,253 and 94,646 regions on its control. Written as a line `clock C₀ … C_(k−1)` after the tension line, only where the
    /// tensions are set; a tension line with no clock line reads every clock at zero.
    pub slice_clock: Option<Vec<u128>>,
    /// [definition; the lead, November 25, Gemini Neon's audit relayed by Brandon (a coprime-stride walk); W113s's reading] **Each slice's
    /// pieces walked on a golden stride**: where set, slice `s`'s pieces from `W_s` on (the count it had finished when the walk was set) are
    /// read in the order `W_s + (k g) mod M`, `M` the pieces left and `g` the stride nearest `M (√5 − 1)/2` coprime to `M`
    /// ([`crate::passage::golden_stride`]), so every piece is still read once a pass and the slice's stretches are spread over the whole
    /// slice instead of walked down its order. Why: a slice is stored in its documents' order, and a slice read faster in order moves her
    /// toward the stretch she is in: on W113s wikidata, read at nearly three times its control's regions, coded its held stretches 0.048
    /// nats a place dearer. Written as a line `walk W₀ … W_(k−1)` after the clock line (or the tension line, or the pass's), only where set.
    pub slice_walk: Option<Vec<u64>>,
    /// [definition; the lead, November 25, Brandon's 05:32Z and 06:14Z: power at her ports, foveated, read by a flock] **Each slice's trail
    /// and its looks**: `(trail, looks)` a slice, the trail a store of the out-of-sample work a deposit did on the slice's stretches (millionths
    /// of a bit a place, `STORE_TRANSFER`), charged at each reading by `(x − trail)/R` with `R` the readings in a mean's window (its fade,
    /// the line's own clock), and the looks the stretches the slice has given since the trail was set. Where set, the cut takes the slice
    /// with fewest looks for its quota times its trail's weight ([`crate::passage::Cut::trail_weights`]: the trail held between the strongest
    /// and that over twice the count of slices), every look at the pass's octaves: the fovea looked at often, the periphery rarely and never
    /// in a shorter look (W115t: looks shortened to the least octave cost their slices 0.03 to 0.05 nats a place).
    /// Written as a line `trail T₀ … T_(k−1) looks L₀ … L_(k−1)` after the walk line, only where set.
    pub slice_trail: Option<(Vec<i64>, Vec<u64>)>,
    /// [definition; the lead, November 25, Fable's construction (the cut ruler's record of that day)] **The pass reads a slice's
    /// consecutive stretches as one passage**: a section's stretches of one slice that follow each other in its text (none ending its
    /// piece before the next begins) are read as one region up to the field's reach, each stretch's first place a cut at the joined
    /// mask (`Region::stretches`). Written as a line `joined` after the trail's, only where set.
    pub joined: bool,
    /// [definition; the lead, November 26, the formal thread's lever after the class hairs (the cut record's §8.3 and §11)] **A joined
    /// passage heard whole**: with [`StorePass::joined`], its stretches are one region with no cut between them, so every open place hears
    /// every definite site of the stretches before its own, sharply, by the law; the same bound on its length and its pairs. Written as
    /// the line `joined whole` in place of `joined`, only where set.
    pub joined_whole: bool,
}

/// [definition; the lead, November 21; `agent-inferred` (a guess at the law, fixed before its arm): Brandon, 04:52Z and 04:54Z, "do not
/// expect arithmetic or code success without tension reinforcement"; the deterministic panel's openings stood at 4 to 5 of 168 at L17,
/// L71 and L75] **A terrain held by its tension.** A world writes its own records, each `EXPRESSION = ANSWER` on one line
/// (`athena::world::record`), `records` of one kind a region, every answer and its line feed open and every expression known: the condition
/// under which the plain engine founded sums on November 17 (about 160 to 200 thousand records of the law, in any arrangement tried). The
/// share of a section's sites the terrain takes is its tension against the passage's, `T_w / (T_w + T_p)`, where `T_w` is the field's code
/// at the terrain's open places in the last section and `T_p` its code at the passage's open places there (millionths of a bit a place,
/// the opening's code the section's receipt reads): the pass stays on the world while the field's misses on its answers stand above its
/// misses on the passage, and leaves as they are absorbed, never to nothing. Why the share and not a count by hand: on the old line the
/// sums were about a hundredth of a section's places and stood at 2.33 nats over 1.6 million records; met alone or a quarter of a section
/// they were founded inside 200 thousand. `met` counts the records written, the key of the next draw. Written `terrain RECORDS MET T_W
/// T_P` after the pass line, only where set; a terrain with no reading yet (`T_w + T_p = 0`) takes half.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassTerrain {
    pub records: u64,
    pub met: u64,
    pub tension_world: u64,
    pub tension_passage: u64,
    /// [definition; the lead, November 21, W77's read at section 2000; `agent-inferred`] **The writer's state**: each region's records but its
    /// last stand known whole, and the last record's answer is open from a keyed place to its line feed, where the region ends: the state a
    /// write in place order meets at that place (every earlier place known, nothing to its right). Where unset, every record's answer is
    /// open at once with the next record known to its right. Why: at W77's section 2000 (1.36 million records met, every answer open at
    /// once) the held panel's writes took the arithmetic answers' form and no value, and wrote no bracket, copy or reversal in the world's
    /// form, while the November 17 dwell that founded sums compared a keyed part of a record's answer with the region ending there. Written
    /// as the word `suffix` after the four counts, only where set.
    pub suffix: bool,
    /// [definition; the lead, November 21, the dwells of that morning] **Read by two streams**: each region is read as the pass reads its
    /// frontier where the pass's word is `strand` ([`crate::region::OwnedRegion::strand`], with the pass's `past` and `second`), every place
    /// compared at its own frontier, the expressions' places with the answers'. Why: a dwell on sums from L76's end founded the held digit
    /// in two-sided regions (0.0005 nats) and wrote 0 of 95 held sums free, and the same dwell read by two streams wrote 67 of 96: the
    /// writer writes in the pass's regime, and a law founded in another regime does not reach it. The terrain's tension is then read over
    /// every place of its regions, the expressions' irreducible news included (`agent-inferred`: its share falls only as far as the
    /// answers' news does). Written as the word `strand` after the four counts, only where set, never beside `suffix`.
    pub strand: bool,
}

impl PassTerrain {
    pub fn to_line(&self) -> String {
        format!("terrain {} {} {} {}{}", self.records, self.met, self.tension_world, self.tension_passage, if self.suffix { " suffix" } else if self.strand { " strand" } else { "" })
    }

    pub fn from_line(line: &str) -> Result<Self> {
        let w: Vec<&str> = line.split(' ').collect();
        let n = |w: &str| w.parse::<u64>().map_err(|_| TowerError::Refused("a terrain's count that is not a count"));
        if !(w.len() == 5 || (w.len() == 6 && (w[5] == "suffix" || w[5] == "strand"))) || w[0] != "terrain" {
            return refuse("a terrain line that is not `terrain RECORDS MET T_W T_P [suffix|strand]`");
        }
        let t = Self { records: n(w[1])?, met: n(w[2])?, tension_world: n(w[3])?, tension_passage: n(w[4])?, suffix: w.get(5) == Some(&"suffix"), strand: w.get(5) == Some(&"strand") };
        if t.records == 0 {
            return refuse("a terrain of no records a region");
        }
        Ok(t)
    }

    /// The sites of a section of `sites` the terrain takes: `sites · T_w / (T_w + T_p)`, floored, or half where it has no reading.
    pub fn share(&self, sites: u64) -> u64 {
        let (w, p) = (u128::from(self.tension_world), u128::from(self.tension_passage));
        if w + p == 0 { sites / 2 } else { u64::try_from(u128::from(sites) * w / (w + p)).unwrap_or(sites) }
    }
}

/// [definition; the lead, November 23, an act answered in kind] **The terrain's world**: a world whose slice is this name answers her acts
/// on the terrain's records ([`PassTerrain`]) in place of a slice's stretches (`athena`'s `set-world ... terrain EVERY RECORDS RUN`); no
/// slice of a store bears it. Its records count is one or more: it is a world of records, never a draft world.
pub const TERRAIN_WORLD: &str = "terrain";

/// [definition; agent-inferred, November 16, the theory thread's Build B of 18:58 UTC, the friction record §3 and §5] **A world joined at the
/// pass's boundary**: a receiver outside the machine that answers the field's own act. One stretch in `every` of the slice `slice` (keyed by
/// the stretch's count) becomes an act: its last `records` whole lines are the prompt, the field releases `run` places after them (its
/// draft), and the world appends its reaction to the draft, which is the only part of the region compared; the prompt and the draft are
/// known context, never a target. The world's law (what it answers) is terrain at the exterior, never the machine's: the machine meets
/// only the bytes it returns. Written after the slices as `world SLICE EVERY RECORDS RUN`, only where set, so every state without one reads
/// and writes byte for byte as before. Why in the state: which acts the world answers is law, carried in the learner's state (CLAUDE.md,
/// November 8).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassWorld {
    pub slice: String,
    pub every: u64,
    /// [definition; the lead, November 23; `agent-inferred`] Zero: **a draft world**. Its act is
    /// the stretch itself: the field drafts the stretch's last `run` places from the places before them, and the stretch is read by two
    /// streams with the draft in its known stream and the passage's own symbols what every place is compared with
    /// ([`crate::field::Region::targets`]). The passage's symbol at a drafted place is no function of the draft, so the draft carries no
    /// news of what it is compared with and that comparison's least code is reached by ignoring the draft (atlas
    /// `receipt.unanswered-act-is-discounted`, Lean `HNN/AnsweredAct`; the formal thread, November 23): the draft world is no answered
    /// act, which is the path of `records` of one or more above. The release draws at the field's own temperature. With `refine` unset
    /// the draft is the writer's, one place a read; set, it is drawn whole from one read of the field and reopened `refine` times, the
    /// release's runs ([`Constitution::sample_runs`]; the record of November 23 on her drafts, §4: a place a read priced a draft at `run` reads; Brandon, 19:49Z: grading her drafts
    /// against the passage is not play, which has no right answer and is answered in kind).
    pub records: u64,
    pub run: u64,
    /// [definition; theory, November 16 20:39Z] Whether each act's draft is redrawn once after its predicted reaction is drawn
    /// ([`Constitution::refine_drafts`]): one where it is, written as a fifth word of the clause only where set, so a clause without it reads
    /// and writes as before.
    pub refine: u64,
}

/// A slice's place in a pass ([`StorePass`]): its name, the piece it stands in, its cursor in that piece and its places taken.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassSlice {
    pub name: String,
    pub piece: u64,
    pub cursor: u64,
    pub taken: u64,
}

impl StorePass {
    /// The pass as its line: `pass ROLE STORE_SHA256 STRETCHES LEAST OCTAVES PAIRS SITES`, the word `own` where the states are the field's
    /// own, and, for each slice in order, `NAME PIECE CURSOR TAKEN`.
    pub fn to_line(&self) -> String {
        let slices: String = self.slices.iter().map(|s| format!(" {} {} {} {}", s.name, s.piece, s.cursor, s.taken)).collect();
        let own = if self.own { " own" } else { "" };
        let world = self.world.as_ref().map_or(String::new(), |w| {
            let refine = if w.refine > 0 { format!(" {}", w.refine) } else { String::new() };
            format!(" world {} {} {} {}{refine}", w.slice, w.every, w.records, w.run)
        });
        let frontier = if self.frontier > 0 { format!(" frontier {}{}", self.frontier, if self.strand { " strand" } else if self.before { " before" } else { "" }) + if self.past { " past" } else { "" } + if self.second { " second" } else { "" } } else { String::new() };
        format!("pass {} {} {} {} {} {} {}{own}{slices}{world}{frontier}", self.role, self.store, self.stretches, self.least, self.octaves, self.pairs, self.sites)
    }

    /// The pass read from its line ([`StorePass::to_line`]).
    pub fn from_line(line: &str) -> Result<Self> {
        let mut all: Vec<&str> = line.split(' ').collect();
        // The known streams' word, where set, is the line's last, after the frontier's clause (a line's last word is otherwise a count).
        // The word `second`, where set, stands last; the word `past`, where set, last before it, after the frontier's reading.
        let second = all.len() >= 12 && all[all.len() - 1] == "second" && (all[all.len() - 4] == "frontier" || (all.len() >= 13 && all[all.len() - 2] == "past" && all[all.len() - 5] == "frontier"));
        if second {
            all.truncate(all.len() - 1);
        }
        let past = all.len() >= 12 && all[all.len() - 1] == "past" && all[all.len() - 4] == "frontier";
        if past {
            all.truncate(all.len() - 1);
        }
        let reading = |word: &str| all.len() >= 11 && all[all.len() - 1] == word && all[all.len() - 3] == "frontier";
        let (before, strand) = (reading("before"), reading("strand"));
        if before || strand {
            all.truncate(all.len() - 1);
        }
        if (past || second) && !before && !strand {
            return refuse("a pass whose word `past` or `second` follows no one-sided reading of the frontier");
        }
        // The frontier's clause, where set, is the line's last two words, opened by the word `frontier` (no slice is named `frontier`, and
        // the word before a line's last is otherwise a count).
        let frontier = if all.len() >= 10 && all[all.len() - 2] == "frontier" {
            let share = all[all.len() - 1].parse::<u64>().map_err(|_| TowerError::Refused("a frontier's share that is not a count"))?;
            if share == 0 || share > 8 {
                return refuse("a frontier's share that is not one to eight of every eight stretches");
            }
            all.truncate(all.len() - 2);
            share
        } else {
            0
        };
        // The world's clause, where set, is the line's last five words, opened by the word `world` (no slice is named `world`).
        let (words, world_words) = if all.len() >= 13 && all[all.len() - 5] == "world" {
            (&all[..all.len() - 5], Some(&all[all.len() - 4..]))
        } else if all.len() >= 14 && all[all.len() - 6] == "world" {
            (&all[..all.len() - 6], Some(&all[all.len() - 5..]))
        } else {
            (&all[..], None)
        };
        // The word `own` stands ninth with four words a slice after it; with it absent the slices begin ninth. The two counts differ by one
        // modulo four, so no slice's name is read as the word.
        let own = words.len() >= 9 && words[8] == "own" && (words.len() - 9) % 4 == 0;
        let from = if own { 9 } else { 8 };
        if words.len() < 8 || words[0] != "pass" || (words.len() - from) % 4 != 0 {
            return refuse("a pass line that is not `pass ROLE STORE STRETCHES LEAST OCTAVES PAIRS SITES [own]` and four words a slice");
        }
        let n = |w: &str| w.parse::<u64>().map_err(|_| TowerError::Refused("a pass's count that is not a count"));
        let word = |w: &str| if !w.is_empty() && w.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_') { Ok(w.to_string()) } else { refuse("a pass's name that is not a word") };
        if words[2].len() != 64 || !words[2].bytes().all(|b| b.is_ascii_hexdigit()) {
            return refuse("a pass's store that is not a SHA-256");
        }
        let slices = words[from..].chunks(4).map(|c| Ok(PassSlice { name: word(c[0])?, piece: n(c[1])?, cursor: n(c[2])?, taken: n(c[3])? })).collect::<Result<Vec<_>>>()?;
        if slices.iter().any(|s| s.name == "world" || s.name == "frontier" || s.name == "before" || s.name == "strand" || s.name == "past" || s.name == "second") {
            return refuse("a pass with a slice named `world`, `frontier`, `before`, `strand`, `past` or `second`, the words of the pass's clauses");
        }
        let world = match world_words {
            Some(w) => Some(PassWorld { slice: word(w[0])?, every: n(w[1])?, records: n(w[2])?, run: n(w[3])?, refine: w.get(4).map(|r| n(r)).transpose()?.unwrap_or(0) }),
            None => None,
        };
        if let Some(w) = &world {
            if w.every == 0 || w.run == 0 || (w.records > 0 && w.refine > 1) || world_words.is_some_and(|ww| ww.len() == 5 && w.refine == 0) || !(slices.iter().any(|s| s.name == w.slice) || (w.slice == TERRAIN_WORLD && w.records > 0)) {
                return refuse("a world whose share or run is zero, a world of records that refines past once, or a world whose slice is not the pass's");
            }
        }
        let pass = Self { role: word(words[1])?, store: words[2].to_string(), stretches: n(words[3])?, least: n(words[4])?, octaves: n(words[5])?, pairs: n(words[6])?, sites: n(words[7])?, own, slices, world, frontier, before, strand, past, second, terrain: None, slice_tension: None, slice_clock: None, slice_walk: None, slice_trail: None, joined: false, joined_whole: false };
        if pass.least == 0 || pass.octaves == 0 || pass.pairs == 0 || pass.sites == 0 {
            return refuse("a pass whose least context, octaves or bounds are zero");
        }
        Ok(pass)
    }
}

/// [definition; the lead, November 21, E5 of #1088; re-founded November 22] A learner's lattice ([`Learner::lattice`]): each family's unit,
/// the standing spread of its whole words (read part plus rest), the root mean square of a save's end less the mean of the states since the
/// save before, on `2^(−MATERIAL_BITS)` whatever the family's grain (zero for a family that did not move), one a family of
/// [`Constitution::families_all`]; and each entry's rest under its read part, on its family's grain.
/// A family of spread `σ` reads its entries on the power of two one place under `σ`'s own ([`Lattice::places`]): the static rent of a place
/// is `R (u/σ)² / 12` (the record's §3) and a store that jitters by `σ ≥ u` is read without bias (its frozen error, §6, under `10^(−9)` of a
/// grain), so one place under is under a 48th of the store's own heat; a family that did not move is read whole.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lattice {
    pub spread: Vec<u64>,
    pub rest: Vec<i32>,
}

/// [definition; the lead, November 22] **Each family's standing spread**: the root mean square of `end − mean` over its entries, each
/// difference on `2^(−MATERIAL_BITS)` (a family on a coarser grain shifted up), rounded down; one a family of `families`.
pub fn family_spreads(families: &[(usize, usize, u32)], end: &[i64], mean: &[i64]) -> Vec<u64> {
    families
        .iter()
        .map(|&(start, n, grain)| {
            if n == 0 {
                return 0;
            }
            let up = MATERIAL_BITS.saturating_sub(grain);
            let sq: u128 = (start..start + n).map(|i| { let d = (i128::from(end[i]) - i128::from(mean[i])).unsigned_abs() << up; d * d }).sum();
            u64::try_from((sq / n as u128).isqrt()).unwrap_or(u64::MAX)
        })
        .collect()
}

impl Lattice {
    /// Each family's places below the point, one place under its spread's own power of two (`MATERIAL_BITS − ⌊log₂ σ⌋ + 1`, `σ` on
    /// `2^(−MATERIAL_BITS)`), and `None` for a family with no spread, read whole.
    pub fn places(&self) -> Vec<Option<u32>> {
        self.spread.iter().map(|&s| (s > 0).then(|| (MATERIAL_BITS + 1).saturating_sub(s.ilog2()))).collect()
    }

    /// Each entry's places dropped below its family's grain: `grain − L` where the lattice is coarser than the grain, else zero.
    pub(crate) fn drops(&self, families: &[(usize, usize, u32)], len: usize) -> Vec<u32> {
        let mut drop = vec![0u32; len];
        for (&(start, n, grain), places) in families.iter().zip(self.places()) {
            drop[start..start + n].fill(places.map_or(0, |p| grain.saturating_sub(p)));
        }
        drop
    }

    /// The deposit under the lattice: every entry's read part and rest summed, the read part set to the nearest lattice point, the rest kept.
    fn settle(&mut self, families: &[(usize, usize, u32)], material: &mut dyn Iterator<Item = &mut i32>, len: usize) -> Result<()> {
        let drops = self.drops(families, len);
        for ((v, r), &q) in material.zip(self.rest.iter_mut()).zip(&drops) {
            if q == 0 {
                // A family read whole holds no rest: what it held joins the read part.
                *v = i32::try_from(i128::from(*v) + i128::from(*r)).map_err(|_| TowerError::Refused("a read part past its 32-bit word"))?;
                *r = 0;
                continue;
            }
            let full = i128::from(*v) + i128::from(*r);
            let read = release(full, q) << q;
            *v = i32::try_from(read).map_err(|_| TowerError::Refused("a read part past its 32-bit word"))?;
            *r = i32::try_from(full - read).map_err(|_| TowerError::Refused("a lattice's rest past its word"))?;
        }
        Ok(())
    }
}

impl Learner {
    /// [definition; the lead, November 22, the second precision pass] **The learner's whole words**: each entry's read part plus its rest
    /// ([`Learner::lattice`]), or its material where no lattice is set.
    pub fn whole_material(&self) -> Vec<i64> {
        match &self.lattice {
            Some(l) => self.field.material().zip(&l.rest).map(|(&v, &r)| i64::from(v) + i64::from(r)).collect(),
            None => self.field.material().map(|&v| i64::from(v)).collect(),
        }
    }

    /// [definition; the lead, November 24] **The learner with its lattice folded back into its material**: every entry its whole word (read
    /// part and rest summed), no lattice set, every other line kept, so a growth that refuses a lattice can found its parts and the lattice
    /// be founded again after it ([`Learner::with_lattice_from`]). Refused where a whole word passes the material's 32-bit carrier.
    pub fn unlatticed(&self) -> Result<Self> {
        let mut out = self.clone();
        if self.lattice.is_none() {
            return Ok(out);
        }
        let whole = self.whole_material();
        for (slot, &v) in out.field.material_mut().zip(&whole) {
            *slot = i32::try_from(v).map_err(|_| TowerError::Refused("a whole word past the material's 32-bit carrier"))?;
        }
        out.lattice = None;
        out.last = None;
        Ok(out)
    }

    /// [definition; the lead, November 22, the second precision pass (G-R5)] **The learner whose forward reads each family's read part on a
    /// lattice one place under its own spread** ([`Lattice`]), the spread read from this state as a save's end and `mean`'s whole words as the
    /// mean of the states before it: every entry split into its read part and its rest, so the whole word is this state's and every face
    /// reads the read part. Every other line is kept. Refused where a lattice is set or on a mean of another material.
    pub fn with_lattice_from(&self, mean: &Learner) -> Result<Self> {
        if self.lattice.is_some() {
            return refuse("a learner whose forward already reads a lattice");
        }
        let len = self.field.material_len();
        if mean.field.material_len() != len {
            return refuse("a lattice founded from a mean of another material");
        }
        let mut out = self.clone();
        let families = out.field.families_all();
        let mut lattice = Lattice { spread: family_spreads(&families, &self.whole_material(), &mean.whole_material()), rest: vec![0; len] };
        lattice.settle(&families, &mut out.field.material_mut(), len)?;
        out.lattice = Some(lattice);
        out.last = None;
        Ok(out)
    }

    /// [definition; the lead, November 22, the second precision pass (the record's §7: "the lattice is re-founded at a save where the spread
    /// has moved a place, and `settle` conserves across it")] **The lattice re-founded at a save**: each family's spread read from this
    /// state's whole words against `mean_whole` (the whole words' mean of the states since the save before); a family whose spread's power
    /// of two moved (or which began or ceased to move) takes the new spread, and its entries are settled on the new lattice, each read part
    /// and rest summed and split again, so every whole word is kept. Returns the families re-founded; none where no lattice is set.
    pub fn refound_lattice(&mut self, mean_whole: &[i64]) -> Result<usize> {
        let whole = self.whole_material();
        let families = self.field.families_all();
        let len = self.field.material_len();
        let Some(lattice) = self.lattice.as_mut() else { return Ok(0) };
        if mean_whole.len() != len {
            return refuse("a lattice re-founded from a mean of another material");
        }
        let fresh = family_spreads(&families, &whole, mean_whole);
        let place = |s: u64| (s > 0).then(|| s.ilog2());
        let moved: Vec<usize> = (0..families.len()).filter(|&k| place(fresh[k]) != place(lattice.spread[k])).collect();
        if moved.is_empty() {
            return Ok(0);
        }
        for &k in &moved {
            lattice.spread[k] = fresh[k];
        }
        let drops = lattice.drops(&families, len);
        let mut chosen = vec![false; len];
        for &k in &moved {
            let (start, n, _) = families[k];
            chosen[start..start + n].fill(true);
        }
        for (((v, r), &q), _) in self.field.material_mut().zip(lattice.rest.iter_mut()).zip(&drops).zip(&chosen).filter(|(_, c)| **c) {
            let full = i128::from(*v) + i128::from(*r);
            let read = if q == 0 { full } else { release(full, q) << q };
            *v = i32::try_from(read).map_err(|_| TowerError::Refused("a read part past its 32-bit word"))?;
            *r = i32::try_from(full - read).map_err(|_| TowerError::Refused("a lattice's rest past its word"))?;
        }
        self.last = None;
        Ok(moved.len())
    }

    /// [measurement; the lead, November 21, the precision pass's G-W4] The deposit's two moments, one entry each for the material: a reading.
    pub fn moments(&self) -> (&[i128], &[i128]) {
        (&self.first, &self.second)
    }

    /// The learner of a field founded on its declared key stream (the founding read
    /// [`Declaration::founding_draws`] draws).
    pub fn new(field: Constitution, rate_bits: u32) -> Self {
        let len = field.material_len();
        let drawn = 4 * field.declaration.founding_draws();
        Self { field, first: vec![0; len], second: vec![0; len], rate_bits, drawn, laps: 0, held: None, read_held: false, rate_parts: None, own_rates: None, leak: None, last: None, pass: None, remainder: None, carried: None, lattice: None }
    }

    /// Whether a deposited step is held for the next regions' read.
    pub fn holds_step(&self) -> bool {
        self.held.is_some()
    }

    /// The held step read on `regions` without a deposit: the faces of `regions` under the
    /// material that stands after the read, and the read (`None` when no step was held).
    pub fn read_step_on(&mut self, regions: &[Region], realization: &mut dyn Realization) -> Result<(Vec<Vec<Option<TowerFace>>>, Option<Next>)> {
        let (faces, _, next) = self.open(regions, realization, false)?;
        Ok((faces, next))
    }

    /// The opening read of `regions` (with the covector when `returning`), after the held step,
    /// if any, is read on them ([`Learner::next_scale`]): the material before it and the
    /// stepped material read first, the material that stands decided, and the opening read read
    /// on it (a read already made is not made again).
    pub(crate) fn open(&mut self, regions: &[Region], realization: &mut dyn Realization, returning: bool) -> Result<(Vec<Vec<Option<TowerFace>>>, Option<Vec<i128>>, Option<Next>)> {
        let Some(held) = self.held.take() else {
            return if returning {
                let (faces, g) = realization.read_and_return(&self.field, regions)?;
                Ok((faces, Some(g), None))
            } else {
                Ok((realization.read_faces(&self.field, regions)?, None, None))
            };
        };
        let mut before = self.field.clone();
        for (slot, &q) in before.material_mut().zip(&held.step) {
            *slot = fit32(*slot as i128 + release(q, held.halvings), "a held step's material outgrew its 32-bit carrier")?;
        }
        let (standing, faces, next) = Self::next_scale(&before, &held, regions, realization)?;
        self.field = standing;
        if returning {
            let (faces, g) = realization.read_and_return(&self.field, regions)?;
            return Ok((faces, Some(g), Some(next)));
        }
        Ok((faces, None, Some(next)))
    }

    /// [definition; agent-inferred, November 1] **The held step read on regions it was not fit
    /// on** (the tower's acceptance 77, `TowerLearner::next_section`): the regions are read under
    /// the material before the step (`old`), and the step's size is read on them by [`scaled`]
    /// against `old`, standing where it codes them no higher. A refused step leaves the material
    /// before it, so the material that stands never codes the regions higher than `old`. At most
    /// four reads of the regions are made before the opening read.
    ///
    /// Returns the material that stands, its faces, and the read.
    #[allow(clippy::type_complexity)]
    pub(crate) fn next_scale(before: &Constitution, held: &HeldStep, regions: &[Region], realization: &mut dyn Realization) -> Result<(Constitution, Vec<Vec<Option<TowerFace>>>, Next)> {
        let before_faces = realization.read_faces(before, regions)?;
        let old = compared(&before_faces, regions)?;
        let scale = scaled(before, &held.step, held.halvings, &old, false, regions, realization)?;
        let next = Next { change: scale.change, halvings: scale.halvings, refused: scale.standing.is_none() };
        Ok(match scale.standing {
            Some((field, faces)) => (field, faces, next),
            None => (before.clone(), before_faces, next),
        })
    }

    /// One section: the step the section before deposited read on its regions (only under
    /// [`Learner::read_held`]), then its regions read and returned on the material that stands,
    /// the moments moved, and the step deposited at its size (the step fluxes, November 5; a step that
    /// moves no entry deposits nothing), priced by its prediction, transfer and external price
    /// ([`Receipt`]) and kept for the next section's transfer.
    pub fn section(&mut self, regions: &[Region]) -> Result<Receipt> {
        self.section_realized(regions, &mut Host)
    }

    /// [`Learner::section`] on a declared realization of the field's read and return; the step
    /// is deposited at its size, and the moments and the step stay on the host.
    pub fn section_realized(&mut self, regions: &[Region], realization: &mut dyn Realization) -> Result<Receipt> {
        // [the lead, November 24] The rings' skins formed from the fades the material holds now ([`Declaration::fade`]).
        self.field.refresh_fade()?;
        let mut part = std::time::Instant::now();
        let mut mark = |k: usize| {
            SECTION_PARTS[k].fetch_add(part.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
            part = std::time::Instant::now();
        };
        // [realization; theory, November 13, P58 item 3] With no held step and no port the comparison reads each open site's face at its
        // class alone, so the realization is asked for those words ([`Realization::read_and_return_at_class`]); the same pairs.
        // [theory, November 13, P60 item 1d] Where the field has the opening's lift the call returns its codes beside the faces and the covector.
        let (faces_old, g, next, codes) = if self.held.is_none() && regions.iter().all(|r| r.port.is_none()) {
            let (at_class, g, codes) = realization.read_and_return_opening(&self.field, regions)?;
            mark(0);
            (compared_at_class(&at_class, regions)?, Some(g), None, codes)
        } else {
            let (faces, g, next) = self.open(regions, realization, true)?;
            let codes = if self.field.declaration.opening { regions.iter().map(|r| self.field.opening_codes(r)).collect::<Result<_>>()? } else { Vec::new() };
            mark(0);
            (compared(&faces, regions)?, g, next, codes)
        };
        let opening: Vec<(i64, usize)> = codes.iter().map(|c| (c.iter().flatten().sum(), c.iter().flatten().count())).collect();
        let mut g = g.ok_or(TowerError::Refused("a section's opening read returned no covector"))?;
        // [definition; the lead, November 24] The level's own lane holds its other writers and the prolongation's other rows at zero: their
        // covector is none ([`Constitution::level_lane_held`]).
        if let Some(held) = self.field.level_lane_held()? {
            for i in held {
                g[i] = 0;
            }
        }
        let spans = spans_of(regions);
        let code_before = code_of(&faces_old, &spans);
        if faces_old.pairs.is_empty() && !faces_old.ported {
            return refuse("a section with no unresolved site");
        }
        // The sites the weighed code is a code of (§16.23): each region's domain where it reads an open site.
        let sites = spans.iter().filter(|s| s.0 > 0).map(|s| s.1 as usize).sum::<usize>()
            + regions.iter().filter_map(|r| r.port.map(|p| (p.start..p.stop.unwrap_or(r.classes.len()).min(r.classes.len())).filter(|&t| r.unresolved[t] && p.heard.is_none_or(|h| h[t])).count())).sum::<usize>();
        mark(1);
        // [the unified-theory reading of November 6, 08:54] The external price is the step the moments would deposit before this section
        // moves them, priced on this section: a step this section never shaped. [realization; the lead, November 20] The transfer, the
        // external step and its price, the covector's grains, the moments, the step and its prices are one pass a family ([`deposit_pass`]),
        // every bit as the serial passes formed them; the parts `2`, `3`, `5`, `6`, `7`, `9`, `10` and `12` of [`SECTION_PART_NAMES`] read zero.
        let rates = self.entry_rates();
        mark(4);
        let families = self.field.families_all();
        let parts = self.reading_parts();
        mark(11);
        let last = self.last.take();
        let carried = self.carried.as_mut().map(|(cf, cs)| (&mut cf[..], &mut cs[..]));
        let pass = deposit_pass(&families, &g, &mut self.first, &mut self.second, &rates, self.remainder.as_deref_mut(), carried, last.as_ref(), &parts)?;
        drop(g);
        let DepositPass { step, transfer, external, predicted, parts: predicted_parts } = pass;
        mark(8);
        // [definition; Brandon, November 5 17:29 and 17:32] **The step fluxes**: it deposits at its size, and no reread of the
        // section certifies it. The reread kept a step only where the regions reread under it coded strictly fewer bits, a
        // selection on the code (a maximum in effect) that discarded what an expansion measures ("you can't discard failure
        // or mistakes, knowing what causes contraction in contrast to expansion is equally important") and cost a full read
        // of the section (27% of path75's second segment). What the step does is read by the passes the field makes anyway:
        // the next section's own covector prices it at first order ([`Receipt::transfer`]), contraction and expansion
        // alike, and the moments carry every covector.
        let (mut candidate, moved) = stepped(&self.field, &step, 0)?;
        // [definition; the lead, November 21, E5 of #1088] Under a lattice the step lands on the read part and its rest, and the read part moves
        // only where their sum crosses a lattice point ([`Learner::lattice`]).
        if moved && let Some(lattice) = self.lattice.as_mut() {
            let (families, len) = (candidate.families_all(), candidate.material_len());
            lattice.settle(&families, &mut candidate.material_mut(), len)?;
        }
        mark(13);
        if !moved {
            self.relax(&rates);
            return Ok(Receipt { sites, code_before, code_after: None, halvings: 0, deposited: false, next, predicted, change: None, transfer, external, predicted_parts, opening });
        }
        self.field = candidate;
        self.relax(&rates);
        if self.read_held {
            self.held = Some(HeldStep { step, halvings: 0 });
        } else {
            self.last = Some(HeldStep { step, halvings: 0 });
        }
        mark(14);
        Ok(Receipt { sites, code_before, code_after: None, halvings: 0, deposited: true, next, predicted, change: None, transfer, external, predicted_parts, opening })
    }

    /// [definition; the lead, November 17] **The leak's relaxation** ([`Learner::leak`]): every material entry whose rate is under
    /// [`HELD_RATE`] bits moves toward rest by `release(θ, leak)`; nothing where the learner carries no leak. Each entry reads only itself,
    /// so the order is free.
    pub(crate) fn relax(&mut self, rates: &[u32]) {
        let Some(k) = self.leak else { return };
        for (slot, &rate) in self.field.material_mut().zip(rates) {
            if rate < HELD_RATE {
                *slot -= release(i128::from(*slot), k) as i32;
            }
        }
    }

    /// The learner as text: its head line (the held step's halvings, or `-`), the field, each
    /// moment on one line, then the held step on one line when one is held.
    pub fn to_text(&self) -> String {
        let join = |v: &[i128]| v.iter().map(i128::to_string).collect::<Vec<_>>().join(" ");
        let (held, step) = match &self.held {
            Some(h) => (h.halvings.to_string(), format!("{}\n", join(&h.step))),
            None => ("-".to_string(), String::new()),
        };
        {
            // [definition; theory, November 10 19:05] The founded parts' rates, a trailing line a binary without them never reads.
            // The parts the field has, in the line's order ([`written_parts`]): nineteen without carry circles, twenty-two with them, and the
            // triad's one more where the field has triads.
            let d = &self.field.declaration;
            let parts = self.rate_parts.map_or(String::new(), |rp| format!("parts {} {}\n", rp.contacts_before, written_parts(d.carry, d.triads, d.opening, d.junction, d.mark, d.loud, d.lane_leak).iter().chain(d.friction.then_some(&FRICTION_PART)).chain(d.fade.then_some(&FADE_PART)).chain(d.fade_rate.then_some(&FADE_RATE_PART)).chain(d.twin.then_some(&TWIN_PART)).map(|&p| rp.octaves[p].to_string()).collect::<Vec<_>>().join(" ")));
            // [definition; theory, November 12 00:20] Each entry's own rate, a trailing line after the parts' (`rates r₀ … r_(n−1)`).
            let own = self.own_rates.as_ref().map_or(String::new(), |r| format!("rates {}\n", r.iter().map(u32::to_string).collect::<Vec<_>>().join(" ")));
            // [definition; theory, November 12] The pass's place over a store, the text's last line and only where present ([`StorePass`]).
            let pass = self.pass.as_ref().map_or(String::new(), |p| {
                let tension = p.slice_tension.as_ref().map_or(String::new(), |t| format!("tension {}\n", t.iter().map(u64::to_string).collect::<Vec<_>>().join(" ")));
                let clock = p.slice_clock.as_ref().map_or(String::new(), |c| format!("clock {}\n", c.iter().map(u128::to_string).collect::<Vec<_>>().join(" ")));
                let walk = p.slice_walk.as_ref().map_or(String::new(), |w| format!("walk {}\n", w.iter().map(u64::to_string).collect::<Vec<_>>().join(" ")));
                let trail = p.slice_trail.as_ref().map_or(String::new(), |(t, l)| format!("trail {} looks {}\n", t.iter().map(i64::to_string).collect::<Vec<_>>().join(" "), l.iter().map(u64::to_string).collect::<Vec<_>>().join(" ")));
                let joined = match (p.joined, p.joined_whole) {
                    (true, true) => "joined whole\n",
                    (true, false) => "joined\n",
                    _ => "",
                };
                let tension = format!("{tension}{clock}{walk}{trail}{joined}");
                format!("{}\n{}{tension}", p.to_line(), p.terrain.as_ref().map_or(String::new(), |t| format!("{}\n", t.to_line())))
            });
            // [definition; the lead, November 17] The store's leak, a trailing line after the rates' and only where set (`leak K`).
            let leak = self.leak.map_or(String::new(), |k| format!("leak {k}\n"));
            // [definition; the lead, November 18] The step's carried remainders, a trailing line after the leak's and only where carried.
            let remainder = self.remainder.as_ref().map_or(String::new(), |r| format!("remainder {}\n", r.iter().map(i64::to_string).collect::<Vec<_>>().join(" ")));
            // [the lead, November 21, E4 of #1088] The moments' carried remainders, two trailing lines after the remainder's, only where carried.
            let carried = self.carried.as_ref().map_or(String::new(), |(cf, cs)| format!("carried_first {}\ncarried_second {}\n", cf.iter().map(i32::to_string).collect::<Vec<_>>().join(" "), cs.iter().map(i32::to_string).collect::<Vec<_>>().join(" ")));
            // [the lead, November 21, E5 of #1088] The lattice, two trailing lines after the moments' carried lines, only where set.
            let lattice = self.lattice.as_ref().map_or(String::new(), |l| format!("lattice {}\nlattice_rest {}\n", l.spread.iter().map(u64::to_string).collect::<Vec<_>>().join(" "), l.rest.iter().map(i32::to_string).collect::<Vec<_>>().join(" ")));
            format!("hnn-field-learner-v3 {} {} {} {held}\n{}{}\n{}\n{step}{parts}{own}{leak}{remainder}{carried}{lattice}{pass}", self.rate_bits, self.drawn, self.laps, self.field.to_text(), join(&self.first), join(&self.second))
        }
    }

    pub fn from_text(text: &str) -> Result<Self> {
        let mut lines = text.lines();
        let head: Vec<&str> = lines.next().unwrap_or("").split(' ').collect();
        if head.len() != 5 || head[0] != "hnn-field-learner-v3" {
            return refuse("a learner's head line that is not hnn-field-learner-v3");
        }
        let rate_bits = head[1].parse::<u32>().map_err(|_| TowerError::Refused("a learner's rate that is not a count"))?;
        let drawn = head[2].parse::<usize>().map_err(|_| TowerError::Refused("a learner's drawn keys that are not a count"))?;
        let laps = head[3].parse::<u64>().map_err(|_| TowerError::Refused("a learner's laps that are not a count"))?;
        let mut lines = lines.peekable();
        let field = Constitution::from_lines(&mut lines)?;
        let first = read_numbers::<i128>(lines.next())?;
        let second = read_numbers::<i128>(lines.next())?;
        if first.len() != field.material_len() || second.len() != field.material_len() {
            return refuse("a learner's moments that are not its field's length");
        }
        let held = match head[4] {
            "-" => None,
            h => {
                let halvings = h.parse::<u32>().map_err(|_| TowerError::Refused("a learner's held halvings that are not a count"))?;
                let step = read_numbers::<i128>(lines.next())?;
                if step.len() != field.material_len() {
                    return refuse("a learner's held step that is not its field's length");
                }
                Some(HeldStep { step, halvings })
            }
        };
        // [definition; theory, November 10 19:05] The founded parts' rates, a trailing line (`parts CONTACTS_BEFORE k₀ … k₁₄`).
        let rate_parts = match lines.peek() {
            Some(l) if l.starts_with("parts ") => {
                let v = read_numbers::<usize>(lines.next().and_then(|l| l.strip_prefix("parts ")))?;
                // The line's parts in its order ([`written_parts`]); an older line (fifteen or sixteen parts, or nineteen with carry
                // circles, or a triad field's line without the triad's octave: the line before its growth) reads its parts in order with the
                // ones it lacks at the old rate.
                // [theory, November 13, P60 item 1f] An opening field's line without the opening's octave (the line before its founding) reads with
                // it at the old rate, as a triad field's line without the triad's.
                // [theory, November 13, the junction record §7] So does a field with the return whose line lacks the junction's octave.
                // [agent-inferred, November 14, the ring record §4] So does a field that reads twice whose line lacks the mark's octave.
                // [Brandon, November 15 02:06Z] So does a field whose face reads its sites' loudness and whose line lacks the loudness's octave.
                let (carry, triads, opening, junction, mark, loud, lane_leak) = (field.declaration.carry, field.declaration.triads, field.declaration.opening, field.declaration.junction, field.declaration.mark, field.declaration.loud, field.declaration.lane_leak);
                // [the lead, November 21] A field with the friction of distance appends its part; its line without it (the line before its
                // founding) reads with it at the old rate.
                let friction = field.declaration.friction;
                let unfrictioned = written_parts(carry, triads, opening, junction, mark, loud, lane_leak);
                // [the lead, November 24] A field whose rings hold their fades appends their part; its line without it reads with it at the
                // old rate.
                let fade = field.declaration.fade;
                let unfaded: Vec<usize> = unfrictioned.iter().copied().chain(friction.then_some(FRICTION_PART)).collect();
                // [the lead, November 25] A field whose classes fade at their own rates appends their part; its line without it reads with it
                // at the old rate.
                let fade_rate = field.declaration.fade_rate;
                let unrated: Vec<usize> = unfaded.iter().copied().chain(fade.then_some(FADE_PART)).collect();
                let untwinned: Vec<usize> = unrated.iter().copied().chain(fade_rate.then_some(FADE_RATE_PART)).collect();
                // [the lead, November 25] A field whose rings hold a second fade appends its part; its line without it reads with it at the old rate.
                let twin = field.declaration.twin;
                let order: Vec<usize> = untwinned.iter().copied().chain(twin.then_some(TWIN_PART)).collect();
                let unleaked = written_parts(carry, triads, opening, junction, mark, loud, false);
                let unloud = written_parts(carry, triads, opening, junction, mark, false, false);
                let unmarked = written_parts(carry, triads, opening, junction, false, false, false);
                let unjoined = written_parts(carry, triads, opening, false, false, false, false);
                let unopened = written_parts(carry, triads, false, false, false, false, false);
                let before = written_parts(carry, 0, false, false, false, false, false);
                let older: Vec<usize> = if carry > 0 { (0..PLAIN_PARTS).chain(CIRCLE_PARTS).collect() } else { (0..PLAIN_PARTS).collect() };
                let n = v.len().saturating_sub(1);
                let slots: Vec<usize> = if n == order.len() {
                    order
                } else if twin && n == untwinned.len() {
                    untwinned
                } else if fade_rate && n == unrated.len() {
                    unrated
                } else if fade && n == unfaded.len() {
                    unfaded
                } else if friction && n == unfrictioned.len() {
                    unfrictioned
                } else if lane_leak && n == unleaked.len() {
                    unleaked
                } else if loud && n == unloud.len() {
                    unloud
                } else if mark && n == unmarked.len() {
                    unmarked
                } else if junction && n == unjoined.len() {
                    unjoined
                } else if opening && n == unopened.len() {
                    unopened
                } else if triads > 0 && n == before.len() {
                    before
                } else if n == older.len() || n == PLAIN_PARTS || n == PLAIN_PARTS - 1 {
                    older[..n].to_vec()
                } else {
                    return refuse("a learner's founded parts' rates that are not one a part");
                };
                let mut octaves = [0u32; PARTS];
                for (&slot, &k) in slots.iter().zip(&v[1..]) {
                    octaves[slot] = u32::try_from(k).map_err(|_| TowerError::Refused("a part's octaves past a count"))?;
                }
                Some(RateParts { contacts_before: v[0], octaves })
            }
            _ => None,
        };
        // [definition; theory, November 12 00:20] Each entry's own rate, a trailing line after the parts' (`rates r₀ … r_(n−1)`): one count
        // an entry, each at least one bit and under the step's carrier (the deposit shifts an `i128`, [`deposit_step`]).
        let own_rates = match lines.peek() {
            Some(l) if l.starts_with("rates ") => {
                let v = read_numbers::<u32>(lines.next().and_then(|l| l.strip_prefix("rates ")))?;
                if v.len() != field.material_len() {
                    return refuse("a learner's own rates that are not one an entry");
                }
                if v.iter().any(|&r| r == 0 || r >= i128::BITS) {
                    return refuse("an entry's own rate under one bit or past the step's carrier");
                }
                Some(v)
            }
            _ => None,
        };
        // [definition; the lead, November 17] The store's leak, a trailing line after the rates' (`leak K`): at least one bit and under the
        // material's 32-bit carrier.
        let leak = match lines.peek() {
            Some(l) if l.starts_with("leak ") => {
                let k = lines.next().and_then(|l| l.strip_prefix("leak ")).and_then(|w| w.parse::<u32>().ok()).ok_or(TowerError::Refused("a learner's leak that is not a count"))?;
                if k == 0 || k >= 32 {
                    return refuse("a leak under one bit or past the material's carrier");
                }
                Some(k)
            }
            _ => None,
        };
        // [definition; the lead, November 18] The step's carried remainders, a trailing line after the leak's (`remainder r₀ … r_(n−1)`):
        // one an entry, each inside one grain.
        let remainder = match lines.peek() {
            Some(l) if l.starts_with("remainder ") => {
                let v = read_numbers::<i64>(lines.next().and_then(|l| l.strip_prefix("remainder ")))?;
                if v.len() != field.material_len() {
                    return refuse("a learner's remainders that are not one an entry");
                }
                if v.iter().any(|&r| !(0..1i64 << REMAINDER_BITS).contains(&r)) {
                    return refuse("a carried remainder outside one grain");
                }
                Some(v)
            }
            _ => None,
        };
        // [definition; the lead, November 21, E4 of #1088] The moments' carried remainders, two trailing lines after the remainder's: one a
        // moment an entry, each inside half of its rate's grain.
        let carried = match lines.peek() {
            Some(l) if l.starts_with("carried_first ") => {
                let cf = read_numbers::<i32>(lines.next().and_then(|l| l.strip_prefix("carried_first ")))?;
                let cs = read_numbers::<i32>(lines.next().and_then(|l| l.strip_prefix("carried_second ")))?;
                if cf.len() != field.material_len() || cs.len() != field.material_len() {
                    return refuse("a learner's carried moments that are not one a moment an entry");
                }
                let inside = |v: &[i32], rate: u32| v.iter().all(|&r| (-(1i32 << (rate - 1))..=(1i32 << (rate - 1))).contains(&r));
                if !inside(&cf, FIRST_RATE) || !inside(&cs, SECOND_RATE) {
                    return refuse("a moment's carried remainder outside half its rate's grain");
                }
                Some((cf, cs))
            }
            _ => None,
        };
        // [definition; the lead, November 21, E5 of #1088; re-founded November 22] The lattice, two trailing lines after the moments' carried
        // lines: one spread a family, then one rest an entry, each under half its lattice's unit.
        let lattice = match lines.peek() {
            Some(l) if l.starts_with("lattice ") => {
                let spread = read_numbers::<u64>(lines.next().and_then(|l| l.strip_prefix("lattice ")))?;
                let rest = read_numbers::<i32>(lines.next().and_then(|l| l.strip_prefix("lattice_rest ")))?;
                let families = field.families_all();
                if spread.len() != families.len() || rest.len() != field.material_len() {
                    return refuse("a learner's lattice that is not one spread a family and one rest an entry");
                }
                let lattice = Lattice { spread, rest };
                let drops = lattice.drops(&families, field.material_len());
                if lattice.rest.iter().zip(&drops).any(|(&r, &q)| if q == 0 { r != 0 } else { i128::from(r).abs() > 1i128 << (q - 1) }) {
                    return refuse("a lattice's rest outside half its lattice's unit");
                }
                Some(lattice)
            }
            _ => None,
        };
        // [definition; theory, November 12] The pass's place over a store, the text's last line where present ([`StorePass`]).
        let pass = match lines.peek() {
            Some(l) if l.starts_with("pass ") => Some(StorePass::from_line(lines.next().unwrap_or(""))?),
            _ => None,
        };
        // [definition; the lead, November 21] The pass's terrain, a line after the pass line and only where set ([`PassTerrain`]).
        let pass = match (pass, lines.peek()) {
            (Some(p), Some(l)) if l.starts_with("terrain ") => Some(StorePass { terrain: Some(PassTerrain::from_line(lines.next().unwrap_or(""))?), ..p }),
            (p, _) => p,
        };
        // [definition; the lead, November 24] The slices' tensions, a line after the pass's (and its terrain's), only where set.
        let pass = match (pass, lines.peek()) {
            (Some(p), Some(l)) if l.starts_with("tension ") => {
                let t: Vec<u64> = lines.next().unwrap_or("").split_whitespace().skip(1).map(str::parse).collect::<std::result::Result<_, _>>().map_err(|_| TowerError::Refused("a tension line that is not `tension T₀ … T_(k−1)`"))?;
                if t.len() != p.slices.len() {
                    return refuse("a tension line that is not one reading a slice of the pass");
                }
                Some(StorePass { slice_tension: Some(t), ..p })
            }
            (p, _) => p,
        };
        // [definition; the lead, November 25] The slices' clocks under their tensions, a line after the tension line, only where set.
        let pass = match (pass, lines.peek()) {
            (Some(p), Some(l)) if l.starts_with("clock ") && p.slice_tension.is_some() => {
                let c: Vec<u128> = lines.next().unwrap_or("").split_whitespace().skip(1).map(str::parse).collect::<std::result::Result<_, _>>().map_err(|_| TowerError::Refused("a clock line that is not `clock C₀ … C_(k−1)`"))?;
                if c.len() != p.slices.len() {
                    return refuse("a clock line that is not one clock a slice of the pass");
                }
                Some(StorePass { slice_clock: Some(c), ..p })
            }
            (p, _) => p,
        };
        // [definition; the lead, November 25] The slices' walks, a line after the pass's (and its terrain, tension and clock lines), only where set.
        let pass = match (pass, lines.peek()) {
            (Some(p), Some(l)) if l.starts_with("walk ") => {
                let w: Vec<u64> = lines.next().unwrap_or("").split_whitespace().skip(1).map(str::parse).collect::<std::result::Result<_, _>>().map_err(|_| TowerError::Refused("a walk line that is not `walk W₀ … W_(k−1)`"))?;
                if w.len() != p.slices.len() {
                    return refuse("a walk line that is not one place a slice of the pass");
                }
                Some(StorePass { slice_walk: Some(w), ..p })
            }
            (p, _) => p,
        };
        // [definition; the lead, November 25] The slices' trails and looks, a line after the walk's, only where set.
        let pass = match (pass, lines.peek()) {
            (Some(p), Some(l)) if l.starts_with("trail ") => {
                let words: Vec<&str> = lines.next().unwrap_or("").split_whitespace().collect();
                let k = p.slices.len();
                if words.len() != 2 * k + 2 || words[k + 1] != "looks" {
                    return refuse("a trail line that is not `trail T₀ … T_(k−1) looks L₀ … L_(k−1)`");
                }
                let t: Vec<i64> = words[1..=k].iter().map(|w| w.parse()).collect::<std::result::Result<_, _>>().map_err(|_| TowerError::Refused("a trail that is not a count"))?;
                let l: Vec<u64> = words[k + 2..].iter().map(|w| w.parse()).collect::<std::result::Result<_, _>>().map_err(|_| TowerError::Refused("a look that is not a count"))?;
                Some(StorePass { slice_trail: Some((t, l)), ..p })
            }
            (p, _) => p,
        };
        // [definition; the lead, November 25] The pass reads a slice's consecutive stretches as one passage, a line after the trail's.
        let pass = match (pass, lines.peek()) {
            (Some(p), Some(&"joined")) => {
                lines.next();
                Some(StorePass { joined: true, ..p })
            }
            (Some(p), Some(&"joined whole")) => {
                lines.next();
                Some(StorePass { joined: true, joined_whole: true, ..p })
            }
            (p, _) => p,
        };
        Ok(Self { field, first, second, rate_bits, read_held: held.is_some(), drawn, laps, held, rate_parts, own_rates, leak, remainder, carried, lattice, last: None, pass })
    }
}
