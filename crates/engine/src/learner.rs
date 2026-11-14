//! The engine's learner (C5 of #603: cut from `field.rs` by object, each item's text as it stood but for its visibility).

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use crate::inherited::tower::{affine, covector, deposit_step, div_nearest, exp_series, face_code, fewer_bits_weighed, fit32, fit64, half_turn, on_step_grain, outer_sum, ratio_adjoint, ratio_to_power, reach, refuse, release, toward, transposed, weighed_code, Result, TowerError, TowerFace, FACE_BITS, FIRST_RATE, MATERIAL_BITS, MOVE_BITS, SECOND_RATE};
#[allow(unused_imports)]
use crate::inherited::keyed_modes::{ln2_face, log2_face, Exponential};
#[allow(unused_imports)]
use rayon::prelude::*;

/// [measurement; theory, November 13, P58 item 4] **The deposit's parts on the host**, summed over every section a process realizes (ns; a
/// reading, no state changes), in the order [`FieldLearner::section_realized`] runs them ([`SECTION_PART_NAMES`]).
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
    "moments",
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
    faces.iter().zip(regions).map(|(f, r)| f.iter().zip(r.classes).map(|(face, &c)| face.as_ref().map(|face| (face.masses[c], face.total))).collect()).collect()
}

/// [`compared`] from the faces read at their classes ([`faces_at_class`]), where no region has a port: the same pairs.
pub(crate) fn compared_at_class(at_class: &[Vec<Option<(u128, u128)>>], regions: &[Region]) -> Result<Compared> {
    if at_class.len() != regions.len() || regions.iter().any(|r| r.port.is_some()) {
        return refuse("faces at their classes are compared one row a region, with no port");
    }
    Ok(Compared { pairs: at_class.iter().zip(regions).flat_map(|(f, r)| f.iter().take(r.classes.len()).filter_map(|p| *p)).collect(), coupled: 0, ported: false })
}

pub(crate) fn compared(faces: &[Vec<Option<TowerFace>>], regions: &[Region]) -> Result<Compared> {
    let mut out = Compared { pairs: Vec::new(), coupled: 0, ported: false };
    for (f, r) in faces.iter().zip(regions) {
        let end = r.port.map_or(r.classes.len(), |p| p.start);
        out.pairs.extend(f.iter().zip(r.classes).take(end).filter_map(|(face, &c)| face.as_ref().map(|face| (face.masses[c], face.total))));
        if let Some(port) = r.port {
            out.coupled += port_code(f, &port)?;
            out.ported = true;
        }
    }
    Ok(out)
}

/// Each region's run of compared sites before its port and its weight in the joint code, `(K, m, K)`
/// ([`Region::weight`], §16.23), in the order [`compared`] reads them.
pub(crate) fn spans_of(regions: &[Region]) -> Vec<(usize, u64, u64)> {
    regions.iter().map(|r| { let (m, k) = r.weight(); (r.unresolved[..r.port.map_or(r.unresolved.len(), |p| p.start)].iter().filter(|&&u| u).count(), m, k) }).collect()
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
/// section's covector and the step at the halvings it stood at, it is the step's transfer ([`FieldReceipt::transfer`]).
pub(crate) fn predicted_change(field: &Field, g: &[i128], step: &[i128], halvings: u32) -> Option<i64> {
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
/// sum with each family's terms gathered by the part each entry belongs to (`parts`, [`Field::founded_parts`]; index [`PARTS`] the
/// old entries, which no part holds), each gathered family sum released onto the codes' `2^(−20)` bits as the total releases it.
/// So the parts sum to the total less the releases' floors, at most one unit a family and part, which a reader keeps as the
/// total's rest. `None` where a product or a sum passes its carrier. A reading: the step is not changed. Why: a section's
/// predicted price is a total over every part, and a reading names its partition beside its total (the guide's rule of November
/// 11); on tp5 that price burst a hundredfold before the card refused a sum, and which part's covector burst is the question
/// G96's rule asks before eight times returns.
pub(crate) fn predicted_parts(field: &Field, g: &[i128], step: &[i128], halvings: u32, parts: &[u8]) -> Option<[i64; PARTS + 1]> {
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
/// the covector moves the moments ([`FieldReceipt`]); the moments carry every covector, a
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
/// it. *November 3*: the held read was set aside ([`FieldLearner::read_held`], `false`, with its
/// reason there) and stands since as a declared comparison only. *November 5*: the certificate
/// itself was retired, because it kept a step only where its own section reread lower, a selection
/// on the code that discarded what an expansion measures ([`FieldLearner::section_realized`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldLearner {
    pub field: Field,
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
    /// trailing `rates` line, one count an entry. Where it stands it is every entry's rate ([`FieldLearner::entry_rates`]); the parts'
    /// line is kept beside it for its contacts count. None in a state without the line, and after every growth (the law sets it again) but the
    /// triads' ([`FieldLearner::with_triads`]), which keeps each old entry's own rate and opens the triads' entries at the base rate.
    pub own_rates: Option<Vec<u32>>,
    /// [measurement; §16.41] The step the last section stood at, the operand of the next section's
    /// [`FieldReceipt::transfer`]; a reading's operand, not carried in the learner's text, cleared by every growth, and not
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StorePass {
    pub role: String,
    pub store: String,
    pub stretches: u64,
    pub least: u64,
    pub octaves: u64,
    pub pairs: u64,
    pub sites: u64,
    pub slices: Vec<PassSlice>,
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
    /// The pass as its line: `pass ROLE STORE_SHA256 STRETCHES LEAST OCTAVES PAIRS SITES` and, for each slice in order, `NAME PIECE CURSOR
    /// TAKEN`.
    pub fn to_line(&self) -> String {
        let slices: String = self.slices.iter().map(|s| format!(" {} {} {} {}", s.name, s.piece, s.cursor, s.taken)).collect();
        format!("pass {} {} {} {} {} {} {}{slices}", self.role, self.store, self.stretches, self.least, self.octaves, self.pairs, self.sites)
    }

    /// The pass read from its line ([`StorePass::to_line`]).
    pub fn from_line(line: &str) -> Result<Self> {
        let words: Vec<&str> = line.split(' ').collect();
        if words.len() < 8 || words[0] != "pass" || (words.len() - 8) % 4 != 0 {
            return refuse("a pass line that is not `pass ROLE STORE STRETCHES LEAST OCTAVES PAIRS SITES` and four words a slice");
        }
        let n = |w: &str| w.parse::<u64>().map_err(|_| TowerError::Refused("a pass's count that is not a count"));
        let word = |w: &str| if !w.is_empty() && w.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_') { Ok(w.to_string()) } else { refuse("a pass's name that is not a word") };
        if words[2].len() != 64 || !words[2].bytes().all(|b| b.is_ascii_hexdigit()) {
            return refuse("a pass's store that is not a SHA-256");
        }
        let slices = words[8..].chunks(4).map(|c| Ok(PassSlice { name: word(c[0])?, piece: n(c[1])?, cursor: n(c[2])?, taken: n(c[3])? })).collect::<Result<Vec<_>>>()?;
        let pass = Self { role: word(words[1])?, store: words[2].to_string(), stretches: n(words[3])?, least: n(words[4])?, octaves: n(words[5])?, pairs: n(words[6])?, sites: n(words[7])?, slices };
        if pass.least == 0 || pass.octaves == 0 || pass.pairs == 0 || pass.sites == 0 {
            return refuse("a pass whose least context, octaves or bounds are zero");
        }
        Ok(pass)
    }
}

impl FieldLearner {
    /// The learner of a field founded on its declared key stream (the founding read
    /// [`FieldDeclaration::founding_draws`] draws).
    pub fn new(field: Field, rate_bits: u32) -> Self {
        let len = field.material_len();
        let drawn = 4 * field.declaration.founding_draws();
        Self { field, first: vec![0; len], second: vec![0; len], rate_bits, drawn, laps: 0, held: None, read_held: false, rate_parts: None, own_rates: None, last: None, pass: None }
    }

    /// Whether a deposited step is held for the next regions' read.
    pub fn holds_step(&self) -> bool {
        self.held.is_some()
    }

    /// The held step read on `regions` without a deposit: the faces of `regions` under the
    /// material that stands after the read, and the read (`None` when no step was held).
    pub fn read_step_on(&mut self, regions: &[Region], realization: &mut dyn FieldRealization) -> Result<(Vec<Vec<Option<TowerFace>>>, Option<FieldNext>)> {
        let (faces, _, next) = self.open(regions, realization, false)?;
        Ok((faces, next))
    }

    /// The opening read of `regions` (with the covector when `returning`), after the held step,
    /// if any, is read on them ([`FieldLearner::next_scale`]): the material before it and the
    /// stepped material read first, the material that stands decided, and the opening read read
    /// on it (a read already made is not made again).
    pub(crate) fn open(&mut self, regions: &[Region], realization: &mut dyn FieldRealization, returning: bool) -> Result<(Vec<Vec<Option<TowerFace>>>, Option<Vec<i128>>, Option<FieldNext>)> {
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
    pub(crate) fn next_scale(before: &Field, held: &HeldStep, regions: &[Region], realization: &mut dyn FieldRealization) -> Result<(Field, Vec<Vec<Option<TowerFace>>>, FieldNext)> {
        let before_faces = realization.read_faces(before, regions)?;
        let old = compared(&before_faces, regions)?;
        let scale = scaled(before, &held.step, held.halvings, &old, false, regions, realization)?;
        let next = FieldNext { change: scale.change, halvings: scale.halvings, refused: scale.standing.is_none() };
        Ok(match scale.standing {
            Some((field, faces)) => (field, faces, next),
            None => (before.clone(), before_faces, next),
        })
    }

    /// One section: the step the section before deposited read on its regions (only under
    /// [`FieldLearner::read_held`]), then its regions read and returned on the material that stands,
    /// the moments moved, and the step deposited at its size (the step fluxes, November 5; a step that
    /// moves no entry deposits nothing), priced by its prediction, transfer and external price
    /// ([`FieldReceipt`]) and kept for the next section's transfer.
    pub fn section(&mut self, regions: &[Region]) -> Result<FieldReceipt> {
        self.section_realized(regions, &mut HostField)
    }

    /// [`FieldLearner::section`] on a declared realization of the field's read and return; the step
    /// is deposited at its size, and the moments and the step stay on the host.
    pub fn section_realized(&mut self, regions: &[Region], realization: &mut dyn FieldRealization) -> Result<FieldReceipt> {
        let mut part = std::time::Instant::now();
        let mut mark = |k: usize| {
            SECTION_PARTS[k].fetch_add(part.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
            part = std::time::Instant::now();
        };
        // [realization; theory, November 13, P58 item 3] With no held step and no port the comparison reads each open site's face at its
        // class alone, so the realization is asked for those words ([`FieldRealization::read_and_return_at_class`]); the same pairs.
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
        let spans = spans_of(regions);
        let code_before = code_of(&faces_old, &spans);
        if faces_old.pairs.is_empty() && !faces_old.ported {
            return refuse("a section with no unresolved site");
        }
        // The sites the weighed code is a code of (§16.23): each region's domain where it reads an open site.
        let sites = spans.iter().filter(|s| s.0 > 0).map(|s| s.1 as usize).sum::<usize>()
            + regions.iter().filter_map(|r| r.port.map(|p| (p.start..p.stop.unwrap_or(r.classes.len()).min(r.classes.len())).filter(|&t| r.unresolved[t] && p.heard.is_none_or(|h| h[t])).count())).sum::<usize>();
        mark(1);
        let raw = g.clone();
        mark(2);
        let transfer = self.last.take().and_then(|s| predicted_change(&self.field, &raw, &s.step, s.halvings));
        mark(3);
        // [the unified-theory reading of November 6, 08:54] The step the moments would deposit before this section moves them,
        // priced on this section: the external price, a step this section never shaped.
        let rates = self.entry_rates();
        mark(4);
        // [realization; November 14, the engine audit's finding 1] Each entry's step reads only its own moments and rate, so the families' entries
        // are split across the host's cores, every bit kept.
        let families = self.field.families_all();
        let (first, second) = (&self.first, &self.second);
        let step_into = |out: &mut [i128]| {
            for &(start, len, grain) in &families {
                out[start..start + len].par_iter_mut().enumerate().for_each(|(k, slot)| *slot = deposit_step(first[start + k], second[start + k], grain, rates[start + k]));
            }
        };
        let mut external_step = vec![0i128; g.len()];
        step_into(&mut external_step);
        mark(5);
        let external = predicted_change(&self.field, &raw, &external_step, 0);
        mark(6);
        for &(start, len, grain) in &families {
            g[start..start + len].par_iter_mut().for_each(|v| *v = on_step_grain(grain, *v));
        }
        mark(7);
        // Each entry's moments read only its own covector; a square past its carrier refuses the section wherever it stands.
        self.first.par_iter_mut().zip(self.second.par_iter_mut()).zip(g.par_iter()).try_for_each(|((m, v), gv)| -> Result<()> {
            let square = gv.checked_mul(*gv).ok_or(TowerError::Refused("a covector's square outgrew its 128-bit carrier"))?;
            if *m == 0 && *v == 0 {
                // A coordinate opens at its own first nonzero covector.
                (*m, *v) = (*gv, square);
            } else {
                *m = toward(*m, *gv, FIRST_RATE);
                *v = toward(*v, square, SECOND_RATE);
            }
            Ok(())
        })?;
        mark(8);
        let (first, second) = (&self.first, &self.second);
        let mut step = vec![0i128; g.len()];
        for &(start, len, grain) in &families {
            step[start..start + len].par_iter_mut().enumerate().for_each(|(k, slot)| *slot = deposit_step(first[start + k], second[start + k], grain, rates[start + k]));
        }
        mark(9);
        let predicted = predicted_change(&self.field, &raw, &step, 0);
        mark(10);
        let parts = self.reading_parts();
        mark(11);
        let predicted_parts = predicted_parts(&self.field, &raw, &step, 0, &parts);
        mark(12);
        // [definition; Brandon, November 5 17:29 and 17:32] **The step fluxes**: it deposits at its size, and no reread of the
        // section certifies it. The reread kept a step only where the regions reread under it coded strictly fewer bits, a
        // selection on the code (a maximum in effect) that discarded what an expansion measures ("you can't discard failure
        // or mistakes, knowing what causes contraction in contrast to expansion is equally important") and cost a full read
        // of the section (27% of path75's second segment). What the step does is read by the passes the field makes anyway:
        // the next section's own covector prices it at first order ([`FieldReceipt::transfer`]), contraction and expansion
        // alike, and the moments carry every covector.
        let (candidate, moved) = stepped(&self.field, &step, 0)?;
        mark(13);
        if !moved {
            return Ok(FieldReceipt { sites, code_before, code_after: None, halvings: 0, deposited: false, next, predicted, change: None, transfer, external, predicted_parts, opening });
        }
        self.field = candidate;
        if self.read_held {
            self.held = Some(HeldStep { step, halvings: 0 });
        } else {
            self.last = Some(HeldStep { step, halvings: 0 });
        }
        mark(14);
        Ok(FieldReceipt { sites, code_before, code_after: None, halvings: 0, deposited: true, next, predicted, change: None, transfer, external, predicted_parts, opening })
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
            let parts = self.rate_parts.map_or(String::new(), |rp| format!("parts {} {}\n", rp.contacts_before, written_parts(d.carry, d.triads, d.opening, d.junction, d.mark).iter().map(|&p| rp.octaves[p].to_string()).collect::<Vec<_>>().join(" ")));
            // [definition; theory, November 12 00:20] Each entry's own rate, a trailing line after the parts' (`rates r₀ … r_(n−1)`).
            let own = self.own_rates.as_ref().map_or(String::new(), |r| format!("rates {}\n", r.iter().map(u32::to_string).collect::<Vec<_>>().join(" ")));
            // [definition; theory, November 12] The pass's place over a store, the text's last line and only where present ([`StorePass`]).
            let pass = self.pass.as_ref().map_or(String::new(), |p| format!("{}\n", p.to_line()));
            format!("hnn-field-learner-v3 {} {} {} {held}\n{}{}\n{}\n{step}{parts}{own}{pass}", self.rate_bits, self.drawn, self.laps, self.field.to_text(), join(&self.first), join(&self.second))
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
        let field = Field::from_lines(&mut lines)?;
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
                let (carry, triads, opening, junction, mark) = (field.declaration.carry, field.declaration.triads, field.declaration.opening, field.declaration.junction, field.declaration.mark);
                let order = written_parts(carry, triads, opening, junction, mark);
                let unmarked = written_parts(carry, triads, opening, junction, false);
                let unjoined = written_parts(carry, triads, opening, false, false);
                let unopened = written_parts(carry, triads, false, false, false);
                let before = written_parts(carry, 0, false, false, false);
                let older: Vec<usize> = if carry > 0 { (0..PLAIN_PARTS).chain(CIRCLE_PARTS).collect() } else { (0..PLAIN_PARTS).collect() };
                let n = v.len().saturating_sub(1);
                let slots: Vec<usize> = if n == order.len() {
                    order
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
        // [definition; theory, November 12] The pass's place over a store, the text's last line where present ([`StorePass`]).
        let pass = match lines.peek() {
            Some(l) if l.starts_with("pass ") => Some(StorePass::from_line(lines.next().unwrap_or(""))?),
            _ => None,
        };
        Ok(Self { field, first, second, rate_bits, read_held: held.is_some(), drawn, laps, held, rate_parts, own_rates, last: None, pass })
    }
}
