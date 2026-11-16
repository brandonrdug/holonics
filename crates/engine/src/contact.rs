//! **The contact and the tick.**
//!
//! `z_ij = 2^(−β) Σ_m [D_m Re(conj(p̃_im) k̃_jm) − D_m²|k̃_jm|²/2] − ⌊log₂|i−j|⌋`, `e_ij = 2^(z_ij)` over the support `S_i^h`;
//! `y_i = conj(U_i) ⊙ Σ e_ij D ṽ_j / Σ e_ij`, released once; `x ← x + O y + b_o` a tick
//!
//! Kind: gate (the lock) then sum over the sources; sum over the ticks. Kernels: `field_chart`, `field_affine_two_*`, `field_unit*`, `field_frame*`,
//! `field_classes`, `field_sums`, `field_row_currents`, `field_held_rows`, `field_mark_shares`, `field_spread` (`hnn/contact.rs`).
//! Lean: `HNN/Contact`, `HNN/ContactBreak`, `HNN/TickBlocks`, `HNN/TickFamily`.
//! Atlas: `contact.triad-manley-rowe-gauge`, `hnn.field-energy-opening-words`, `tower.field-growth-by-lanes`, `tower.field-matching-lock`,
//! `tower.field-one-region`, `tower.field-open-row-pairs`, `tower.field-reach-on-clock`, `tower.field-read-free-fall`,
//! `tower.field-site-power-unread`, `tower.field-temperature-log`, `tower.field-tick-running-mean`.
//! Records: `2026-11-01_THE_PROBLEM_IS_ONE_FIELD…`, `2026-11-01_THE_FIELD_DISPERSES…`. The derivations' history is in the records; the items below
//! keep their reasons.

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use rayon::prelude::*;

/// [definition; agent-inferred, November 1] **The near field**: sites closer than the solenoid's
/// finest joint closure, `0 < |i − j| < lcm(2, 3) = 6`, meet through every head whatever their
/// classes (the dispersing field's §2.4: over six sites the finest dyadic and triadic rings resolve
/// place without winding, and four bytes before a site code it at 1.98 bits, so a byte's own
/// spelling context lies inside it).
pub const NEAR: usize = 6;

/// The most shells a head's classes may carry (`3^7 = 2,187` classes, within the card's `2^12`
/// buckets a head and region).
pub const MAX_CLASS_TRITS: usize = 7;

/// A face carried as a site's state: each class with its share on `2^(−16)` ([`shares`]).
pub type Shares = Vec<(u32, u32)>;

/// [definition; agent-inferred, November 1] **A face as a state** (§21): each class's share of
/// the face, `w_a = m_a 2^16 / Σ m` to the nearest numerator on `2^(−16)` ([`STATE_BITS`]), the
/// classes whose share releases to zero left out. A site carried so opens on `Σ_a w_a E(a)`.
pub fn shares(face: &TowerFace) -> Shares {
    if face.total == 0 {
        return Vec::new();
    }
    face.masses
        .iter()
        .enumerate()
        .filter_map(|(c, &m)| {
            let w = ((m << STATE_BITS) + face.total / 2) / face.total;
            (w > 0).then_some((c as u32, w as u32))
        })
        .collect()
}

/// One tick's forward temporaries over a region.
#[derive(Clone, Debug, Default)]
pub(crate) struct TickCell {
    /// The tick's own clocks (§16.44), `None` where they are the pass's (the first tick, or a region with no blank).
    pub(crate) clock: Option<Box<TickClock>>,
    /// [theory, November 13, the junction record §7] The tick's return, where the tick has one (past the first): each site's chart read `ℓ`
    /// on `2^(−16)` and reflection `Γ` on `2^(−30)` (`[t]`), and the difference it carried, `v^k − x^(k−1)` (`[t][D]`); empty otherwise.
    pub(crate) jl: Vec<i64>,
    pub(crate) jg: Vec<i64>,
    pub(crate) jd: Vec<i64>,
    /// [measurement; theory, November 13, the junction record §13.8] The state after the tick (`x^(k+1)`, `[t][D]`), kept where the pass keeps
    /// its ticks, for the reader's reaction's reading ([`Constitution::reaction_covectors`]).
    pub(crate) after: Vec<i64>,
    /// [measurement; G162] The state the tick hands on (after the mirror's stage where it is read), kept where the pass keeps its ticks.
    pub(crate) handed: Vec<i64>,
    /// [measurement; theory, November 15 20:38Z] The state the tick began from (`x^k`, `[t][D]`), kept where the pass keeps its ticks, for the
    /// reading of what each site's tick moves ([`Constitution::tick_news`]).
    pub(crate) before: Vec<i64>,
    pub(crate) read: Vec<i32>,
    pub(crate) scale: Vec<i128>,
    /// The unframed key word `[t][2M]`, and the unframed value and probe (the clock's covector reads them, §16).
    pub(crate) word: Vec<i64>,
    pub(crate) vword: Vec<i64>,
    pub(crate) probe: Vec<i64>,
    /// The framed keys and values by head: `[h][t][2n]`, the real parts then the imaginary; the
    /// key as a ratio to its own power within its head (on `2^(−16)`), its powers `[h][t]` beside it.
    pub(crate) q: Vec<i64>,
    pub(crate) v: Vec<i64>,
    pub(crate) qscale: Vec<i128>,
    /// Every receiver's probe, framed and at unit power by head (`[h][t][2n]`), and its powers (§16.19).
    pub(crate) pq: Vec<i64>,
    pub(crate) pscale: Vec<i128>,
    /// Each head's resonance classes and their lists ([`ClassLists`]).
    pub(crate) classes: Vec<ClassLists>,
    /// Each head's and receiving site's support `[h][i]`, each source with its weight and each mode's
    /// share of its row ([`Source`]).
    pub(crate) rows: Vec<Vec<Source>>,
    /// Each head's and receiving site's crowds `[h][i]` and each head's prefix sums of the definite
    /// words and values ([`Sums`], §14.10).
    pub(crate) crowds: Vec<Vec<Crowd>>,
    pub(crate) sums: Vec<Sums>,
    /// The current `[t][2M]`, back in each site's own frame.
    pub(crate) y: Vec<i64>,
    pub(crate) read2: Vec<i32>,
    pub(crate) scale2: Vec<i128>,
    pub(crate) a: Vec<i64>,
    pub(crate) b: Vec<i64>,
    pub(crate) c: Vec<i64>,
    /// [definition; theory, November 11 17:25 and November 12 (G98)] The carry circles' operands (empty without them), what the reverse reads
    /// beside `a`, `b` and `c`, each `[t][2C]`: `qh` the turn and leak charts' reads `q` (`0..C`) and `ℓ` (`C..2C`) on `2^(−16)`, `gam` the gate
    /// `γ` (real parts then imaginary, `2^(−30)`), `kb` the drive coupled through the leak, `κ b` ([`carry_coupling`], real parts then imaginary,
    /// `2^(−16)`), the scan's operand, and `qm` `Q`'s operand `Q(t ∓ 1)` (the scan's value before the site, real parts then imaginary, `2^(−16)`).
    pub(crate) qh: Vec<i64>,
    pub(crate) gam: Vec<i64>,
    pub(crate) kb: Vec<i64>,
    pub(crate) qm: Vec<i64>,
    /// [definition; theory, November 12, the triad record §4] The triads' operands (empty without them), what the reverse reads: `abg` the charts'
    /// reads `[t][6J]` on `2^(−16)` (`α`'s real parts, then imaginary, then `β`'s, then `γ`'s), `tp` the product `p = α(t) β(t − 1)` and `ct` the
    /// triad `c^T = p γ(t + 1)`, each `[t][2J]`, real parts then imaginary, on `2^(−16)`, zero at the region's two ends.
    pub(crate) abg: Vec<i64>,
    pub(crate) tp: Vec<i64>,
    pub(crate) ct: Vec<i64>,
    /// [measurement; the lead, November 16 23:00Z] Where an open row carries its lock ([`Constitution::lock_carry`]): what each row carried
    /// from the tick before, `[h][i]` a list of `(j, S)` (the source and the row's carried lock on it at unit gain); empty otherwise.
    pub(crate) lock_prev: Vec<Vec<(u32, i64)>>,
}

/// [definition; agent-inferred, November 1] **A head's resonance classes over a region** (the
/// dispersing field's §2.2, §6 and §12): each site's class `B_h(t) = Σ_l 3^l (s_l + 1)`, `s_l` the
/// shell trit of its unframed word's mode `l` ([`shell`]), and the lists by one stable counting sort:
/// class `c`'s members are the definite sites first (known or locked, §14.1), then the rest, each in
/// ascending place, class `c`'s definite members `members[off[2c]..off[2c + 1]]` and its others
/// `members[off[2c + 1]..off[2c + 2]]`. The card lists them alike.
///
/// [definition; agent-inferred, November 1] **Only the plates radiate far** (the dispersing field's
/// §14.1): past the near field a source is heard only where it is definite, known (the question, or the
/// truth in a training region) or locked (a foil); a soft or unreached site is heard only in its near
/// field. The support is directional: a receiver of any state reads the definite run of its class. No
/// clique can form, since unresolved and soft sources are never met far. (This replaces the build's
/// bipartite rule, under which an open answer site met the question only through the class of the
/// unresolved row or of a near-flat mixture: on GSM8K the class of the space.)
///
/// [measurement, November 1] **The address is sharp and a class member is heard whole** (§15.2's
/// memberships were built, measured and retired): a mode's membership split across its cone within a
/// band `ε` of it, as amplitudes whose squares are a partition of unity, with the far weight their
/// overlap, kept the code continuous across every seam, and its covector matched the code's difference
/// across the far support; but on the learned fixtures (one row a head) it coded the cue's successor
/// at 3.307, 2.935, 3.224 and 0.599 bits and the recall at 2.461, 1.679, 0.862 and under its bar at
/// bands `2^(−3)`, `2^(−5)`, `2^(−8)` and `2^(−12)`, where the sharp address passes both bars; and
/// §15.2's `½(1 ± λ)` everywhere would give every site a share of the all-bridge class (the bridge
/// borders both plates), so every far row would be dense. §14.2's least hold had coded the cue at 2.12
/// bits. A seam is crossed at a jump. Under the law of November 1 to 3 the held step's certificate read the
/// code itself, so a step across a seam was certified or refused on what it did; since November 5 the step
/// fluxes, and what a step across a seam does is priced by the next section's covector like any other. (The
/// cue and recall fixtures these reads used are retired as copy-shaped acceptances, §16.19; the reads stand
/// as history.)
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ClassLists {
    /// Each site's class as a source, read from its key word: the class whose run lists it.
    pub class: Vec<u32>,
    /// Each receiver's own probed class, read from its probe word (§16.19).
    pub probe_class: Vec<u32>,
    pub definite: Vec<bool>,
    /// Each site's key: known, or carrying a face (§16.20). A site that carries neither has no word to be met
    /// by and is no receiver's source, its near field's included.
    pub keyed: Vec<bool>,
    pub off: Vec<u32>,
    pub members: Vec<u32>,
    /// Each receiver's other probed classes (§15.2's multi-probe, [`probes`]), empty where none.
    pub probes: Vec<Vec<u32>>,
}

impl ClassLists {
    /// The lists of the classes `class` over `buckets` classes, each class's `definite` sites first.
    pub fn of(class: Vec<u32>, definite: Vec<bool>, buckets: usize) -> Self {
        let key = |t: usize| 2 * class[t] as usize + usize::from(!definite[t]);
        let mut off = vec![0u32; 2 * buckets + 1];
        for t in 0..class.len() {
            off[key(t) + 1] += 1;
        }
        for k in 0..2 * buckets {
            off[k + 1] += off[k];
        }
        let mut filled = off.clone();
        let mut members = vec![0u32; class.len()];
        for t in 0..class.len() {
            members[filled[key(t)] as usize] = t as u32;
            filled[key(t)] += 1;
        }
        let probes = vec![Vec::new(); class.len()];
        let probe_class = class.clone();
        let keyed = vec![true; class.len()];
        Self { class, probe_class, definite, keyed, off, members, probes }
    }

    /// The lists with each site's key (§16.20): the sources a near field holds.
    pub fn keyed(mut self, keyed: Vec<bool>) -> Self {
        self.keyed = keyed;
        self
    }

    /// The lists with each receiver's own probed class and its other probed classes.
    pub fn probing(mut self, probe_class: Vec<u32>, probes: Vec<Vec<u32>>) -> Self {
        self.probe_class = probe_class;
        self.probes = probes;
        self
    }

    /// [definition; agent-inferred, November 1] **Site `i`'s support** (§2.5, §14.1, §15.9, §16.20): its near
    /// field's keyed sites (`0 < |i − j| < NEAR`, nearest first, before then after) and, past it, the definite sites
    /// it hears sharply, each site once: a definite receiver the definite members of its probe's class
    /// and of the classes it probes across its seams, an open receiver (not definite) every definite site. The
    /// support is directional: only definite sources are heard far.
    pub fn support(&self, i: usize) -> impl Iterator<Item = usize> + '_ {
        let sites = self.class.len();
        let near = (1..NEAR).flat_map(move |d| [i.checked_sub(d), Some(i + d).filter(|&j| j < sites)]).flatten().filter(move |&j| self.keyed[j]);
        let open = !self.definite[i];
        let runs = std::iter::once(self.probe_class[i]).chain(self.probes.get(i).into_iter().flatten().copied()).filter(move |_| !open);
        let far = runs.flat_map(move |c| self.members[self.off[2 * c as usize] as usize..self.off[2 * c as usize + 1] as usize].iter().map(|&j| j as usize).filter(move |&j| j.abs_diff(i) >= NEAR));
        let listened = (0..sites).filter(move |&j| open && self.definite[j] && j.abs_diff(i) >= NEAR);
        near.chain(far).chain(listened)
    }

    /// Whether receiver `i` listens to every definite site (it is open, §15.9).
    pub fn listens(&self, i: usize) -> bool {
        !self.definite[i]
    }
}

/// [definition; agent-inferred, November 1] **A receiver's probes across its seams** (§15.2's
/// multi-probe): for each address mode whose word lies within the band `ε = 2^(−k)` of its light cone,
/// `|re² − im²| 2^k < re² + im²` exactly, the shell across that cone (a plate's is the bridge, the
/// bridge's the plate on its in-phase side), and the classes every combination of those crossings
/// reaches, the receiver's own excluded. Sources stay in their own class alone and enter a probed
/// run at their full score: nothing is weighted by membership, the lock decides. Why (measured
/// November 1): with the sharp address the cue fixture's held successor codes 0.177 bits, 80 % of it in
/// 5 of its 64 problems, where the successor's earlier site shared the reader's class in at most one
/// of its four head and tick rows and was heard only blurred through its octave's crowd; with the
/// probes it codes 0.022 bits, and over six further foundings 0.026 to 0.060 bits (0.021 to 0.212
/// without), every one inside the fixture's bar of 0.0625. (That fixture is retired, a far-copy recall met
/// only through the founding's equal-word concentration; under the honest founding it coded 3.312 bits at
/// 600 sections, §16.19.)
pub fn probes(modes: impl Iterator<Item = (i64, i64)>, band: u32) -> Vec<u32> {
    let mut out = vec![0u32];
    let mut own = 0u32;
    for (l, (re, im)) in modes.enumerate() {
        let place = 3u32.pow(l as u32);
        let s = shell(re, im);
        own += place * s;
        let (rr, ii) = (re as i128 * re as i128, im as i128 * im as i128);
        let near_cone = rr + ii > 0 && ((rr - ii).abs() << band) < rr + ii;
        let across = if s != 1 { 1 } else if re >= 0 { 2 } else { 0 };
        out = out.iter().flat_map(|&c| std::iter::once(c + place * s).chain(near_cone.then_some(c + place * across))).collect();
    }
    out.retain(|&c| c != own);
    out
}

/// [agent-inferred, November 1] **The probes' band** `ε = 2^(−k)`, `k = ⌈log₂ b⌉` over a head's `b`
/// address modes: at the founding's random phases a mode lies within `ε` of its cone with probability
/// `(2/π) arcsin ε ≤ ε`, so over its `b` modes a receiver expects fewer than one crossing (`b ε ≤ 1`)
/// and reads about two runs.
pub fn band_bits(trits: usize) -> u32 {
    usize::BITS - trits.max(1).saturating_sub(1).leading_zeros()
}

/// [definition; agent-inferred, November 1] **A mode's shell** (§12) as its class digit `s + 1`:
/// the sky plate `2` where `Re > |Im|`, the ground plate `0` where `Re < −|Im|`, the bridge `1` where
/// `|Re| ≤ |Im|` (its light cone on the bridge).
pub fn shell(re: i64, im: i64) -> u32 {
    let quadrature = im.unsigned_abs();
    if re > 0 && re.unsigned_abs() > quadrature {
        2
    } else if re < 0 && re.unsigned_abs() > quadrature {
        0
    } else {
        1
    }
}

/// A source's and a crowd's value multiplier, `1` on `2^(−62)`; a crowd's mass multiplier is its count.
pub const WEIGHT_BITS: u32 = 62;

/// [definition; agent-inferred, November 1] **A mode's lock against the source that arrives** (§15.2):
/// with the receiver's mode `a` and a source `b` (a crowd's summed word over its `count`) carried by the
/// skin `(D, g)`, the receiver's power less its slip against the arriving face, `(|a|² − |a − D b|²)/2 =
/// D Re(conj(a) b) − D²|b|²/2` up to the receiver's own `|a|²/2`, which every term of its row shares and
/// so leaves its shares unchanged; returned as the integer `2·count·D·Re(conj(a) b)·2^g − D²|b|²` on
/// `2^(−(2g + 32))` (over `2 count²` for a crowd). It is greatest exactly where the arriving face equals
/// the receiver's: a key fits its lock where the two words agree, mode by mode. Why not the pairing alone
/// (`D Re(conj(a) b)`, §15.2's first statement): a mode's power is not held to one, so a louder key would
/// outscore the equal one in its mode's row, the cause the head's unit power repaired (the module doc,
/// measured November 1: the equal word peaked in 20 of 32 rows), returned mode by mode. The lock is the
/// pair contact's own slip, `Q = ⟨Δ|Δ⟩` with `Δ = a − D b`; summed over a still head's modes at unit power
/// it is the head's pairing less a constant.
pub(crate) fn lock(a: (i128, i128), b: (i128, i128), count: i128, (decay, grain): (i128, u32)) -> Result<i128> {
    let carried = |v: Option<i128>| v.ok_or(TowerError::Refused("a lock past its 128-bit carrier"));
    let pairing = carried((a.0 * b.0).checked_add(a.1 * b.1).and_then(|p| p.checked_mul(2 * count * decay)).and_then(|p| p.checked_mul(1i128 << grain)))?;
    let power = carried((b.0 * b.0).checked_add(b.1 * b.1).and_then(|p| p.checked_mul(decay * decay)))?;
    carried(pairing.checked_sub(power))
}

/// A value carried across a pair by its skin decay `(D, grain)`: `release(D v, grain)` (a still
/// head's `(1, 0)` is the value itself).
pub(crate) fn decayed((decay, grain): (i128, u32), v: i64) -> i128 {
    release(decay * v as i128, grain)
}

/// [definition; agent-inferred, November 1] **An octave's crowd** heard by a receiver (§14.10): the
/// definite sources at places `lo..=hi` (one side, `⌊log₂ |i − j|⌋ = level`, `|i − j| ≥ NEAR`), their
/// count, the crowd's score and its share of the row on `2^(−63)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Crowd {
    pub lo: usize,
    pub hi: usize,
    pub level: u32,
    pub count: u64,
    pub z: i64,
    pub e: u64,
    /// Its lock at unit gain on `2^(−16)` (before the temperature, §15.10).
    pub s: i64,
}

/// [measurement] Rows read by where their mass lies ([`Constitution::row_shares`]): `[0]` the open receivers,
/// `[1]` the definite ones.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RowShares {
    pub rows: [u64; 2],
    pub far_sources: [u64; 2],
    pub near: [u128; 2],
    pub far: [u128; 2],
    pub crowd: [u128; 2],
    /// Each row's largest share summed (its peak), on `2^(−63)`.
    pub peak: [u128; 2],
}

/// A met source of a receiver's row: its place and its share of the row on `2^(−63)`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Source {
    pub j: u32,
    pub p: u64,
    /// Its lock at unit gain on `2^(−16)` (before the temperature, §15.10).
    pub s: i64,
}

/// The crowds' ranges of receiver `i` in a region of `sites`: each octave `level ≥ 2` with
/// `2^level < sites`, on each side, the places `|i − j| ∈ [max(2^level, NEAR), 2^(level+1) − 1]`
/// within the region, the nearer side first.
pub fn crowd_ranges(i: usize, sites: usize) -> Vec<(usize, usize, u32)> {
    let mut out = Vec::new();
    let mut level = 2u32;
    while (1usize << level) < sites {
        let (near, far) = ((1usize << level).max(NEAR), (1usize << (level + 1)) - 1);
        if i >= near {
            out.push((i.saturating_sub(far), i - near, level));
        }
        if i + near < sites {
            out.push((i + near, (i + far).min(sites - 1), level));
        }
        level += 1;
    }
    out
}

/// A wide value carried by a skin decay `(D, grain)`: `release(D v, grain)`.
pub(crate) fn decayed_wide((decay, grain): (i128, u32), v: i128) -> i128 {
    release(decay * v, grain)
}

impl Forward {
    /// The clocks a tick read (§16.44): its own, or the pass's.
    pub(crate) fn paces_at<'a>(&'a self, cell: &'a TickCell) -> &'a Paces {
        cell.clock.as_ref().map_or(&self.paces, |c| &c.paces)
    }
}

/// A region's forward: each tick's temporaries (held when the reverse will read them), the last
/// read, and each unresolved site's face.
#[derive(Clone, Debug, Default)]
pub(crate) struct Forward {
    pub(crate) ticks: Vec<TickCell>,
    pub(crate) read: Vec<i32>,
    pub(crate) scale: Vec<i128>,
    /// Each unresolved site's lift `R r̂ + b_R` on `2^(−16)` (§16.26), which its face reads through the encoding.
    pub(crate) lift: Vec<i64>,
    pub(crate) faces: Vec<Option<TowerFace>>,
    /// Each unresolved site's readout logits `z_t` on `2^(−16)` bits (the face is `2^(z − peak)`).
    pub(crate) logits: Vec<Option<Vec<i64>>>,
    /// The site pairs the contact met, `Σ_(h, tick, i) |S_i^h|`.
    pub(crate) pairs: u64,
    /// Each site's echo on `2^(−63)` ([`ReadLogits`]).
    pub(crate) echo: Vec<u64>,
    /// The turned heads' clocks over the region (§16, Law 1).
    pub(crate) paces: Paces,
    /// The region's moments `[t][2M]` (§15.1), which the opening reads (§16.22).
    pub(crate) moment: Vec<i64>,
    /// A tower's forward at its split, for the reverse.
    pub(crate) tower: Option<crate::field::scale::ScalePass>,
    /// [measurement; theory, November 11 04:48, G39] The sites whose face covector a return leaves zero (empty: none), a reading of where the deposit's mass lies.
    pub(crate) skip: Vec<bool>,
    /// [definition; agent-inferred, November 14, the ring record §4] The marks this read opened its silent sites on ([`Declaration::mark`]):
    /// the shares of the faces the field's first read gave them, `None` at every other site; none on a read that is the first.
    pub(crate) marks: Option<Vec<Option<Shares>>>,
    /// [definition; agent-inferred, November 14, G180] The first read's forward, kept for its own return where the field reads twice and the
    /// read keeps its temporaries: both reads are compared ([`Constitution::read_and_return`]).
    pub(crate) first: Option<Box<Forward>>,
}

pub(crate) struct Reaches {
    pub(crate) probe: u64,
    pub(crate) q: u64,
    pub(crate) v: u64,
    pub(crate) out: u64,
    pub(crate) a: u64,
    pub(crate) b: u64,
    pub(crate) w: u64,
    pub(crate) carry: u64,
    pub(crate) triad: u64,
    pub(crate) w_triad: u64,
    pub(crate) read: u64,
    pub(crate) moment_face: u64,
    pub(crate) junction: u64,
}

impl Constitution {


    /// [definition; agent-inferred, November 2] **A row's gain bound from its temperatures' octaves** (§16.12): `4n T
    /// + 1` bits with `T ≤ 2^c`, `c` the largest `⌈log₂ T⌉` the material holds, read from `ℓ` alone (no face), so the
    /// card's launch shape needs nothing of the forward; equal to the exact gain at a whole octave (the founding's).
    pub fn row_gain(&self) -> Result<u64> {
        let mut top = i128::MIN;
        for k in 0..2 * self.declaration.heads {
            top = top.max(temper_octave(self.theta[self.layout.temper + k])?);
        }
        let reals = 4 * self.declaration.modes as u64;
        Ok(if top >= 0 { reals << top } else { reals >> -top } + 1)
    }

    /// [definition; agent-inferred, November 2] **A row's bound as the material stands** (§14.11,
    /// §15.10): [`Declaration::row_bits`] with the gain read from the largest temperature the
    /// material holds, since the temperatures are deposited.
    pub fn row_bits(&self) -> Result<u32> {
        let d = &self.declaration;
        let gain = self.row_gain()? as u32;
        let reach_bits = d.reach_bits() as u32;
        let spread = gain + (usize::BITS - 1 - d.reach.leading_zeros()) + 2;
        let terms = (usize::BITS - (d.reach + 2 * reach_bits as usize).leading_zeros()) as u32;
        Ok(62 + WEIGHT_BITS + reach_bits + spread + terms + 64 + reach_bits + 1)
    }

    pub(crate) fn reaches(&self) -> Reaches {
        let (dw, m2, f) = (self.declaration.width, 2 * self.declaration.complex(), self.declaration.contacts);
        let l = &self.layout;
        let r = |start: usize, len: usize| reach(&self.theta[start..start + len]);
        let j = self.declaration.triads;
        Reaches { probe: r(l.probe, m2 * dw), q: r(l.q, m2 * dw), v: r(l.v, m2 * dw), out: r(l.out, dw * m2), a: r(l.a, f * dw), b: r(l.b, f * dw), w: r(l.w, dw * f), carry: r(l.carry, 2 * self.declaration.carry * dw), triad: r(l.triad, 6 * j * dw), w_triad: r(l.w_triad, dw * 2 * j), read: r(l.read, dw * dw), moment_face: r(l.moment_face, dw * m2), junction: r(l.junction, usize::from(self.declaration.junction) * dw) }
    }

    /// A site's encoding row: its class, or the unresolved row.
    pub(crate) fn row(&self, region: &Region, t: usize) -> usize {
        if region.unresolved[t] { self.declaration.alphabet } else { region.classes[t] }
    }

    /// One tick of the constitution over the region's faces `x` (`[t][D]`), its temporaries
    /// written to `cell`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn tick(&self, x: &mut [i64], definite: &[bool], keyed: &[bool], paces: &Paces, moment: &[i64], reaches: &Reaches, window: Option<&[bool]>, cell: &mut TickCell) -> Result<()> {
        let d = &self.declaration;
        let (dw, m, n, f, heads) = (d.width, d.complex(), d.modes, d.contacts, d.heads);
        let m2 = 2 * m;
        let sites = x.len() / dw;
        let l = &self.layout;
        let (trits, buckets) = (d.class_trits(), d.classes());
        // The chart, lane by lane.
        cell.read = Vec::with_capacity(sites * dw);
        cell.scale = Vec::with_capacity(sites * d.lanes);
        for xt in x.chunks_exact(dw) {
            lane_chart(xt, d.lanes, &mut cell.read, &mut cell.scale)?;
        }
        // The key word a head, and the value.
        let mut q = vec![0i64; sites * m2];
        let mut v = vec![0i64; sites * m2];
        for t in 0..sites {
            let rt = &cell.read[t * dw..(t + 1) * dw];
            affine(&self.theta[l.q..l.q + m2 * dw], reaches.q, dw, rt, Some(&self.theta[l.q_bias..l.q_bias + m2]), MATERIAL_BITS, MATERIAL_BITS, &mut q[t * m2..(t + 1) * m2])?;
            affine(&self.theta[l.v..l.v + m2 * dw], reaches.v, dw, rt, Some(&self.theta[l.v_bias..l.v_bias + m2]), MATERIAL_BITS, MATERIAL_BITS, &mut v[t * m2..(t + 1) * m2])?;
            // A value is linear in its site's moment (§15.1), never normalized before it.
            for (vv, &mv) in v[t * m2..(t + 1) * m2].iter_mut().zip(&moment[t * m2..(t + 1) * m2]) {
                *vv = fit64(*vv as i128 + mv as i128)?;
            }
        }
        // Every receiver's probe (§16.19): its own chart of the same read.
        let mut pr = vec![0i64; sites * m2];
        for t in 0..sites {
            let rt = &cell.read[t * dw..(t + 1) * dw];
            affine(&self.theta[l.probe..l.probe + m2 * dw], reaches.probe, dw, rt, Some(&self.theta[l.probe_bias..l.probe_bias + m2]), MATERIAL_BITS, MATERIAL_BITS, &mut pr[t * m2..(t + 1) * m2])?;
            // [definition; §16.20] A receiver asks with what has reached its place: its probe reads its moment at the
            // turned modes, the moment its value carries (§15.1), so an open site probes by its strand's sources.
            for (pp, &mv) in pr[t * m2..(t + 1) * m2].iter_mut().zip(&moment[t * m2..(t + 1) * m2]) {
                *pp = fit64(*pp as i128 + mv as i128)?;
            }
        }
        // The resonance classes, head by head (§12, §16.19): a source's the shells of its unframed key word (the
        // class it is met in), a receiver's the shells of its unframed probe word and the classes it probes
        // across their seams (the classes it meets).
        let class_of = |word: &[i64], t: usize, h: usize| (0..trits).rev().fold(0u32, |c, li| 3 * c + shell(word[t * m2 + h * n + li], word[t * m2 + m + h * n + li]));
        cell.classes = (0..heads)
            .map(|h| {
                let class = (0..sites).map(|t| class_of(&q, t, h)).collect();
                let probe_class = (0..sites).map(|t| class_of(&pr, t, h)).collect();
                let probed = (0..sites).map(|t| probes((0..trits).map(|li| (pr[t * m2 + h * n + li], pr[t * m2 + m + h * n + li])), band_bits(trits))).collect();
                ClassLists::of(class, definite.to_vec(), buckets).probing(probe_class, probed).keyed(keyed.to_vec())
            })
            .collect();
        cell.word = q.clone();
        cell.vword = v.clone();
        cell.probe = pr.clone();
        // The frame, by head: [h][t][2n], real parts then imaginary.
        let span = 2 * n;
        cell.q = vec![0i64; heads * sites * span];
        cell.v = vec![0i64; heads * sites * span];
        for h in 0..heads {
            for t in 0..sites {
                let at = (h * sites + t) * span;
                for li in 0..n {
                    let c = h * n + li;
                    let (ur, ui) = self.frame(paces, t, h, li);
                    let (ur, ui) = (ur as i128, ui as i128);
                    let (qr, qi) = (q[t * m2 + c] as i128, q[t * m2 + m + c] as i128);
                    let (vr, vi) = (v[t * m2 + c] as i128, v[t * m2 + m + c] as i128);
                    cell.q[at + li] = fit64(release(ur * qr - ui * qi, MOVE_BITS))?;
                    cell.q[at + n + li] = fit64(release(ui * qr + ur * qi, MOVE_BITS))?;
                    cell.v[at + li] = fit64(release(ur * vr - ui * vi, MOVE_BITS))?;
                    cell.v[at + n + li] = fit64(release(ui * vr + ur * vi, MOVE_BITS))?;
                }
            }
        }
        // The contact pairs words at unit power: each head's framed word read as a ratio to its own
        // power (`ratio_to_power` over the head's `2n` reals), so a word's contact with an equal word
        // is `2n`, the most any pair reaches, and a pair's is `2n` times its cosine.
        cell.qscale = vec![0i128; heads * sites];
        for hs in 0..heads * sites {
            let slice = &mut cell.q[hs * span..(hs + 1) * span];
            let (r, s) = ratio_to_power(slice)?;
            for (slot, v) in slice.iter_mut().zip(r) {
                *slot = v as i64;
            }
            cell.qscale[hs] = s;
        }
        // The probe framed and at unit power alike.
        cell.pq = vec![0i64; heads * sites * span];
        cell.pscale = vec![0i128; heads * sites];
        for h in 0..heads {
            for t in 0..sites {
                let at = (h * sites + t) * span;
                for li in 0..n {
                    let c = h * n + li;
                    let (ur, ui) = self.frame(paces, t, h, li);
                    let (ur, ui) = (ur as i128, ui as i128);
                    let (qr, qi) = (pr[t * m2 + c] as i128, pr[t * m2 + m + c] as i128);
                    cell.pq[at + li] = fit64(release(ur * qr - ui * qi, MOVE_BITS))?;
                    cell.pq[at + n + li] = fit64(release(ui * qr + ur * qi, MOVE_BITS))?;
                }
                let slice = &mut cell.pq[at..at + span];
                let (r, s) = ratio_to_power(slice)?;
                for (slot, v) in slice.iter_mut().zip(r) {
                    *slot = v as i64;
                }
                cell.pscale[h * sites + t] = s;
            }
        }
        // The contact and the current over each site's support, head by head (§2.5, §14.10, §14.11,
        // §15.2): `z_ij = 2^(−β) Σ_m lock_m(ŵ_i, ŵ_j) − ⌊log₂ |i − j|⌋` on `2^(−16)` bits for a met source
        // (each mode's [`lock`] carried by its skin decay), and for each octave's crowd of definite
        // sources its mean word at the octave's falloff. The row is a series ([`SeriesRow`]): each term
        // `2^z` times its multiplier (a crowd's count) keeps its own exponent, the terms are summed whole,
        // and the current `ỹ_i = Σ_k e_k ṽ_k / Σ_k e_k` is released once; each term's share of the row is
        // formed once for the return. The current returns to the receiving site's own frame,
        // `y_i = conj(U_i) ỹ_i`.
        cell.rows = Vec::with_capacity(heads * sites);
        cell.y = vec![0i64; sites * m2];
        let lock_prev = std::mem::take(&mut cell.lock_prev);
        let one = 1u128 << WEIGHT_BITS;
        let carried = |v: Option<i128>| v.ok_or(TowerError::Refused("a lock past its 128-bit carrier"));
        cell.crowds = Vec::with_capacity(heads * sites);
        cell.sums = Vec::with_capacity(heads);
        for h in 0..heads {
            let lists = &cell.classes[h];
            let sums = Sums::of(&cell.q[h * sites * span..(h + 1) * sites * span], &cell.v[h * sites * span..(h + 1) * sites * span], definite, span);
            // [definition; agent-inferred, November 3, §16.38] **Conservation of faces**: a still head reads content
            // alone, so the definite sources of one resonance class are one face to it, and that face's mass is shared
            // among them: each source's score is lowered by the octave of its class's definite count, `⌊log₂ c⌋`, as
            // the falloff lowers it by the octave of its distance. A turned head reads place as well, and to it every
            // place is its own face.
            // [definition; agent-inferred, November 3, §16.38] A still head reads content at any distance, so its source is
            // weighed by its face's multiplicity and not by its distance; the octave of distance is a turned head's, which
            // reads place.
            let shared = !d.carries_moment(h);
            let falloff = |gap: usize, j: usize| -> i128 {
                if !shared {
                    return octave(gap) as i128;
                }
                let c = lists.class[j] as usize;
                octave(((lists.off[2 * c + 1] - lists.off[2 * c]) as usize).max(1)) as i128
            };
            for i in 0..sites {
                // [E] A receiver outside every window of a cut room meets no source this tick: its current is zero.
                if window.is_some_and(|w| !w[i]) {
                    cell.rows.push(Vec::new());
                    cell.crowds.push(Vec::new());
                    continue;
                }
                // Every receiver probes with its own probe word (§16.19), against each source's key.
                let wi = &cell.pq[(h * sites + i) * span..(h * sites + i + 1) * span];
                // The lock's temperature for this receiver's kind (§15.10).
                let temper = self.temper(h, lists.listens(i))?;
                let mut series = SeriesRow::new(span);
                let mut row: Vec<Source> = Vec::new();
                for j in lists.support(i) {
                    let wj = &cell.q[(h * sites + j) * span..(h * sites + j + 1) * span];
                    let vj = &cell.v[(h * sites + j) * span..(h * sites + j + 1) * span];
                    // Each mode's lock carried by its skin decay across the pair's distance, summed
                    // whole and released once (a still head's `D = 1` reads the bare lock exactly).
                    let d = i.abs_diff(j);
                    let mut s = 0i128;
                    let mut value = vec![0i128; span];
                    for li in 0..n {
                        let decay = self.pair_decay(paces, h, li, i, j);
                        s = carried(s.checked_add(lock((wi[li] as i128, wi[n + li] as i128), (wj[li] as i128, wj[n + li] as i128), 1, decay)?))?;
                        (value[li], value[n + li]) = (decayed(decay, vj[li]), decayed(decay, vj[n + li]));
                    }
                    let base = fit64(release(s, FACE_BITS + 2 * self.decay(h, 0, d).1 + 1))?;
                    // [measurement] An open row's carried lock, where read ([`Constitution::lock_carry`]).
                    let base = match (self.lock_carry, lock_prev.get(h * sites + i)) {
                        (Some(g), Some(prev)) if lists.listens(i) => {
                            let carried = prev.iter().find(|&&(pj, _)| pj as usize == j).map_or(0, |&(_, c)| c);
                            fit64(base as i128 + release(g as i128 * carried as i128, GAMMA_BITS))?
                        }
                        _ => base,
                    };
                    let z = fit64(release(temper * base as i128, MATERIAL_BITS) - (falloff(d, j) << FACE_BITS))?;
                    series.push(self.face(z), one, one, &value);
                    row.push(Source { j: j as u32, p: 0, s: base });
                }
                // The far field blurred (§14.10): each octave's crowd of definite sources on each side,
                // heard as `|C|` sources at the mean of their words at the octave's falloff; its value
                // term is its decayed value sum, its mass term `|C|` times its face.
                let mut crowds: Vec<Crowd> = Vec::new();
                // An open receiver hears every definite source sharply (§15.9), so no crowd of them.
                for (lo, hi_, level) in crowd_ranges(i, sites).into_iter().filter(|_| !lists.listens(i)) {
                    let count = sums.count(lo, hi_);
                    if count == 0 {
                        continue;
                    }
                    let word = sums.words(lo, hi_);
                    let mut score = 0i128;
                    let mut value = vec![0i128; span];
                    for li in 0..n {
                        let decay = self.octave_decay(paces, h, li, i, level, lo > i);
                        score = carried(score.checked_add(lock((wi[li] as i128, wi[n + li] as i128), (word[li], word[n + li]), count as i128, decay)?))?;
                        (value[li], value[n + li]) = (decayed_wide(decay, sums.value(lo, hi_, li)), decayed_wide(decay, sums.value(lo, hi_, n + li)));
                    }
                    let base = fit64(div_nearest(score, ((count * count) as i128) << (FACE_BITS + 2 * self.decay(h, 0, 1 << level).1 + 1)))?;
                    let z = fit64(release(temper * base as i128, MATERIAL_BITS) - ((level as i128) << FACE_BITS))?;
                    series.push(self.face(z), (count as u128) << WEIGHT_BITS, one, &value);
                    crowds.push(Crowd { lo, hi: hi_, level, count, z, e: 0, s: base });
                }
                let (framed, shares) = series.release();
                for (src, &share) in row.iter_mut().zip(&shares) {
                    src.p = share;
                }
                for (c, &share) in crowds.iter_mut().zip(&shares[row.len()..]) {
                    c.e = share;
                }
                for li in 0..n {
                    let (ur, ui) = self.frame(paces, i, h, li);
                    let (ur, ui) = (ur as i128, ui as i128);
                    let (yr, yi) = (fit64(framed[li])? as i128, fit64(framed[n + li])? as i128);
                    let c = h * n + li;
                    cell.y[i * m2 + c] = fit64(release(ur * yr + ui * yi, MOVE_BITS))?;
                    cell.y[i * m2 + m + c] = fit64(release(ur * yi - ui * yr, MOVE_BITS))?;
                }
                cell.rows.push(row);
                cell.crowds.push(crowds);
            }
            cell.sums.push(sums);
        }
        let mut o = vec![0i64; dw];
        for t in 0..sites {
            affine(&self.theta[l.out..l.out + dw * m2], reaches.out, m2, &cell.y[t * m2..(t + 1) * m2], Some(&self.theta[l.out_bias..l.out_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut o)?;
            for (xv, ov) in x[t * dw..(t + 1) * dw].iter_mut().zip(&o) {
                *xv = fit64(*xv as i128 + *ov as i128)?;
            }
        }
        // The pair contact.
        cell.read2 = Vec::with_capacity(sites * dw);
        cell.scale2 = Vec::with_capacity(sites * d.lanes);
        for xt in x.chunks_exact(dw) {
            lane_chart(xt, d.lanes, &mut cell.read2, &mut cell.scale2)?;
        }
        cell.a = vec![0i64; sites * f];
        cell.b = vec![0i64; sites * f];
        cell.c = vec![0i64; sites * f];
        for t in 0..sites {
            let rt = &cell.read2[t * dw..(t + 1) * dw];
            affine(&self.theta[l.a..l.a + f * dw], reaches.a, dw, rt, Some(&self.theta[l.a_bias..l.a_bias + f]), MATERIAL_BITS, MATERIAL_BITS, &mut cell.a[t * f..(t + 1) * f])?;
            affine(&self.theta[l.b..l.b + f * dw], reaches.b, dw, rt, Some(&self.theta[l.b_bias..l.b_bias + f]), MATERIAL_BITS, MATERIAL_BITS, &mut cell.b[t * f..(t + 1) * f])?;
        }
        let half = f / 2;
        // [definition; agent-inferred, November 3, §16.34] The complex product a contact (§15.1) is a pair contact along the strand: contact
        // `e < f/2` is `a_e + i a_(f/2+e)` at the site against its strand neighbour's `b`, the one before it at an even `e` and the one after at
        // an odd ([`strand_mate`]), so two ring faces compose by adding their phases, `q(x + y) = q(x) q(y)`, across the strand's contact; none
        // past the region's ends. The plain contacts are the first `f/2 − C` ([`Declaration::carry`]).
        let plain = d.carry_first();
        for t in 0..sites {
            for e in 0..plain {
                let (ar, ai) = (cell.a[t * f + e] as i128, cell.a[t * f + half + e] as i128);
                let (br, bi) = match strand_mate(t, e, sites) {
                    Some(s) => (cell.b[s * f + e] as i128, cell.b[s * f + half + e] as i128),
                    None => (0, 0),
                };
                cell.c[t * f + e] = fit64(release(ar * br - ai * bi, FACE_BITS))?;
                cell.c[t * f + half + e] = fit64(release(ar * bi + ai * br, FACE_BITS))?;
            }
        }
        // [definition; theory, November 11 17:25 and November 12 (G98)] **The carry circles' scan** ([`Declaration::carry`]): at each site
        // the circles' charts `q = Q r̂ + q_b`, `ℓ = L r̂ + ℓ_b` (one affine, at the grains `a` and `b` are read at), the gate
        // `γ = γ̂(q)/(1 + d₀ 2^ℓ)` ([`carry_gate`]) and the drive coupled through the same leak, `κ b` with `κ = N₀ d/(1 + d)` ([`carry_coupling`]);
        // then along the strand, one release a step in strand order (never a parallel prefix, which would reorder the releases): circle `k` is
        // contact `e = f/2 − C + k`, even `e` from the left and odd from the right, `p(t) = a(t) Qm(t)` released at the face's grain and
        // `Q(t) = κ(t) b(t) + release(γ(t) Qm(t), 30)` with `Qm(t) = Q(t ∓ 1)`, `Q` zero before the region's first site (past its last, for odd
        // `e`).
        let circles = d.carry;
        if circles > 0 {
            let c2 = 2 * circles;
            cell.qh = vec![0i64; sites * c2];
            cell.gam = vec![0i64; sites * c2];
            cell.kb = vec![0i64; sites * c2];
            cell.qm = vec![0i64; sites * c2];
            for t in 0..sites {
                let rt = &cell.read2[t * dw..(t + 1) * dw];
                affine(&self.theta[l.carry..l.carry + c2 * dw], reaches.carry, dw, rt, Some(&self.theta[l.carry_bias..l.carry_bias + c2]), MATERIAL_BITS, MATERIAL_BITS, &mut cell.qh[t * c2..(t + 1) * c2])?;
                for k in 0..circles {
                    let ((yr, yi), friction) = carry_gate(&self.exponential, cell.qh[t * c2 + k] as i128, cell.qh[t * c2 + circles + k] as i128)?;
                    cell.gam[t * c2 + k] = yr;
                    cell.gam[t * c2 + circles + k] = yi;
                    let (kappa, e) = (carry_coupling(friction), plain + k);
                    cell.kb[t * c2 + k] = carry_drive(kappa, cell.b[t * f + e])?;
                    cell.kb[t * c2 + circles + k] = carry_drive(kappa, cell.b[t * f + half + e])?;
                }
            }
            for k in 0..circles {
                let e = plain + k;
                let (mut qr, mut qi) = (0i128, 0i128);
                for step in 0..sites {
                    let t = if e % 2 == 0 { step } else { sites - 1 - step };
                    cell.qm[t * c2 + k] = fit64(qr)?;
                    cell.qm[t * c2 + circles + k] = fit64(qi)?;
                    let (ar, ai) = (cell.a[t * f + e] as i128, cell.a[t * f + half + e] as i128);
                    cell.c[t * f + e] = fit64(release(ar * qr - ai * qi, FACE_BITS))?;
                    cell.c[t * f + half + e] = fit64(release(ar * qi + ai * qr, FACE_BITS))?;
                    let (yr, yi) = (i128::from(cell.gam[t * c2 + k]), i128::from(cell.gam[t * c2 + circles + k]));
                    let next_r = cell.kb[t * c2 + k] as i128 + release(yr * qr - yi * qi, GAMMA_BITS);
                    let next_i = cell.kb[t * c2 + circles + k] as i128 + release(yr * qi + yi * qr, GAMMA_BITS);
                    (qr, qi) = (i128::from(fit64(next_r)?), i128::from(fit64(next_i)?));
                }
            }
        }
        // [definition; theory, November 12, the triad record §3 and §4] **The triads** ([`Declaration::triads`]): at each site the charts'
        // reads `α, β, γ` (one affine of the pair chart with the charts' biases, at the grains `a` and `b` are read at, `[t][6J]`), then at each
        // site with both strand mates `p = α(t) β(t − 1)` and `c^T = p γ(t + 1)`, each released at the face's grain ([`triad_products`]); none at
        // the region's two ends. Kept in the cell for the reverse.
        let (triads, j2, j6) = (d.triads, 2 * d.triads, 6 * d.triads);
        if triads > 0 {
            cell.abg = vec![0i64; sites * j6];
            for t in 0..sites {
                let rt = &cell.read2[t * dw..(t + 1) * dw];
                affine(&self.theta[l.triad..l.triad + j6 * dw], reaches.triad, dw, rt, Some(&self.theta[l.triad_bias..l.triad_bias + j6]), MATERIAL_BITS, MATERIAL_BITS, &mut cell.abg[t * j6..(t + 1) * j6])?;
            }
            (cell.tp, cell.ct) = triad_products(triads, sites, &cell.abg, d.crossing)?;
        }
        // The pair's return, `x ← x + release(W c + b_c 2^M, M)`; with triads `W c + W_T c^T + b_c 2^M` is one sum released once
        // ([`affine_joint`]), and at `J = 0` the plain affine is the one called, so every bit is as before.
        for t in 0..sites {
            if triads == 0 {
                affine(&self.theta[l.w..l.w + dw * f], reaches.w, f, &cell.c[t * f..(t + 1) * f], Some(&self.theta[l.w_bias..l.w_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut o)?;
            } else {
                affine_joint(&self.theta[l.w..l.w + dw * f], reaches.w, f, &cell.c[t * f..(t + 1) * f], &self.theta[l.w_triad..l.w_triad + dw * j2], reaches.w_triad, j2, &cell.ct[t * j2..(t + 1) * j2], &self.theta[l.w_bias..l.w_bias + dw], MATERIAL_BITS, MATERIAL_BITS, &mut o)?;
            }
            for (xv, ov) in x[t * dw..(t + 1) * dw].iter_mut().zip(&o) {
                *xv = fit64(*xv as i128 + *ov as i128)?;
            }
        }
        Ok(())
    }

    /// The region's forward: `K` ticks, then each unresolved site's face. `keep` holds each tick's
    /// temporaries for the reverse. [the ring record §4] Where the field reads twice ([`Declaration::mark`]), the first read is this one
    /// with no marks, and the forward returned is the second, each silent site opened on the shares of the face the first gave it.
    pub(crate) fn pass(&self, region: &Region, keep: bool) -> Result<Forward> {
        if !self.declaration.mark {
            return self.pass_with(region, keep, None);
        }
        let first = self.pass_with(region, keep, None)?;
        let marks: Vec<Option<Shares>> = (0..region.classes.len()).map(|t| if Self::silent(region, t) { first.faces[t].as_ref().map(shares) } else { None }).collect();
        let mut out = self.pass_with(region, keep, Some(&marks))?;
        out.marks = Some(marks);
        if keep {
            out.first = Some(Box::new(first));
        }
        Ok(out)
    }

    /// [measurement; theory, November 15 21:16Z] **The region's forward with chosen site-ticks held** ([`Constitution::pass`] as a reading):
    /// a site whose `hold[k][t]` is set leaves tick `k` in the state it began it from. Both reads where the field reads twice.
    pub(crate) fn pass_held(&self, region: &Region, hold: &[Vec<bool>]) -> Result<Forward> {
        self.pass_held_as(region, hold, false)
    }

    /// [measurement; theory, November 15 22:29Z] **The forward with chosen site-ticks carried one tick**: a site whose `hold[k][t]` is set shows
    /// its readers at tick `k + 1` the state it began tick `k` from, and its skipped move is added once tick `k + 1` has run (a carry past the
    /// last tick reaches no reader). Both reads where the field reads twice.
    pub(crate) fn pass_carried(&self, region: &Region, hold: &[Vec<bool>]) -> Result<Forward> {
        self.pass_held_as(region, hold, true)
    }

    fn pass_held_as(&self, region: &Region, hold: &[Vec<bool>], carry: bool) -> Result<Forward> {
        if !self.declaration.mark {
            return self.pass_with_held(region, false, None, Some((hold, carry)));
        }
        let first = self.pass_with_held(region, false, None, Some((hold, carry)))?;
        let marks: Vec<Option<Shares>> = (0..region.classes.len()).map(|t| if Self::silent(region, t) { first.faces[t].as_ref().map(shares) } else { None }).collect();
        self.pass_with_held(region, false, Some(&marks), Some((hold, carry)))
    }

    /// One read of the region ([`Constitution::pass`]), its silent sites opened on `marks` where given.
    pub(crate) fn pass_with(&self, region: &Region, keep: bool, marks: Option<&[Option<Shares>]>) -> Result<Forward> {
        self.pass_with_held(region, keep, marks, None)
    }


    /// [`Constitution::pass_with`], with the site-ticks of `hold` held where given (a reading: [`Constitution::pass_held`]).
    fn pass_with_held(&self, region: &Region, keep: bool, marks: Option<&[Option<Shares>]>, hold: Option<(&[Vec<bool>], bool)>) -> Result<Forward> {
        self.admit_region(region)?;
        let d = &self.declaration;
        let dw = d.width;
        let reaches = self.reaches();
        let paces = self.paces(region)?;
        let moment = self.moments_of(region, &paces)?;
        let mut x = self.open(region, &moment, marks)?;
        let definite: Vec<bool> = (0..region.classes.len()).map(|t| Self::definite(region, t)).collect();
        let keyed: Vec<bool> = (0..region.classes.len()).map(|t| !region.unresolved[t] || Self::carried(region, t).is_some()).collect();
        // [theory, November 13, the design record §4.9] The level reads the opening's news, formed before any tick.
        let news = if self.scale.is_some() { self.level_news(region)? } else { Vec::new() };
        let mut out = Forward::default();
        let sites = region.classes.len();
        let mut trips = vec![0u128; sites];
        let mut before: Option<Vec<Vec<Source>>> = None;
        // [§16.44] The blanks run at the bare rate in the first tick, and each later tick at the faces the tick before
        // gave them, its clocks and moments read again.
        let blanks = !paces.kappa.is_empty() && (0..sites).any(|t| Self::silent(region, t));
        let window = d.room_window(region);
        let mut clock: Option<Box<TickClock>> = None;
        // [theory, November 13, the junction record §7] The state the tick before began from, where the tick has the return.
        let mut prior: Option<Vec<i64>> = None;
        // [measurement] The moves carried from the tick before, added once this tick has run (`pass_carried`).
        let mut carried: Vec<i64> = Vec::new();
        // [measurement] The open rows' locks carried from the tick before, where read ([`Constitution::lock_carry`]).
        let mut locks: Vec<Vec<(u32, i64)>> = Vec::new();
        for k in 0..d.ticks {
            if let Some(s) = self.scale.as_deref().filter(|s| s.split == k) {
                out.tower = Some(self.scale_forward(s, &mut x, &news, &definite, &keyed, keep)?);
            }
            let own = clock.take();
            let (tick_paces, tick_moment) = own.as_ref().map_or((&paces, &moment), |c| (&c.paces, &c.moment));
            let mut cell = TickCell::default();
            let began = d.junction.then(|| x.clone());
            if keep {
                cell.before = x.clone();
            }
            let held_from = hold.map(|_| x.clone());
            if carried.is_empty() {
                carried = vec![0i64; x.len()];
            }
            if self.lock_carry.is_some() {
                cell.lock_prev = std::mem::take(&mut locks);
            }
            self.tick(&mut x, &definite, &keyed, tick_paces, tick_moment, &reaches, window.as_deref(), &mut cell)?;
            if self.lock_carry.is_some() {
                locks = cell.rows.iter().map(|row| row.iter().map(|src| (src.j, src.s)).collect()).collect();
            }
            if let Some(prev) = prior.as_deref() {
                self.junction_forward(&mut x, prev, &reaches, &mut cell)?;
            }
            if let (Some((h, carry)), Some(from)) = (hold, held_from.as_ref()) {
                let mut next = vec![0i64; if carry { x.len() } else { 0 }];
                for t in (0..h[k].len()).filter(|&t| h[k][t]) {
                    for i in t * dw..(t + 1) * dw {
                        if carry {
                            next[i] = fit64(i128::from(x[i]) - i128::from(from[i]))?;
                        }
                        x[i] = from[i];
                    }
                }
                if carry {
                    for (xv, &c) in x.iter_mut().zip(&carried) {
                        *xv = fit64(i128::from(*xv) + i128::from(c))?;
                    }
                    carried = next;
                }
            }
            prior = began;
            if keep || self.mirror_strength.is_some() {
                cell.after = x.clone();
            }
            // [measurement; G161] The read's mirror at uniform strength, where read: every head's mirror from the state this tick left.
            if let Some(strength) = self.mirror_strength.as_ref().filter(|_| k + 1 < d.ticks) {
                let paces_k = tick_paces;
                let mut step = vec![0i128; x.len()];
                for (h, &sh) in strength.iter().enumerate().filter(|(_, sh)| **sh != 0) {
                    let (mu, _) = self.mirror_route(&cell, paces_k, &definite, h, None)?;
                    for (st, &m) in step.iter_mut().zip(&mu) {
                        *st += release(i128::from(sh) * i128::from(m), FACE_BITS);
                    }
                }
                for (xv, st) in x.iter_mut().zip(&step) {
                    *xv = fit64(i128::from(*xv) - st)?;
                }
            }
            if keep {
                cell.handed = x.clone();
            }
            cell.clock = own;
            if blanks && k + 1 < d.ticks {
                // [the unified-theory reading of November 6, 08:16] Only the blanks a clock reads are read: every silent place up
                // to the silent stretch's first, whose rate the stretch past it runs at (every silent place under the per-blank
                // clock); a face past it is read by no clock and returns no covector (`clock_return` folds the stretch there).
                let stretch = if self.per_blank_clock { sites } else { Self::silent_stretch(region) };
                // Under `bare_stretch` no place past the last arrival reads a face, the stretch's first among them.
                let read_to = if self.bare_stretch && !self.per_blank_clock { stretch } else { stretch + 1 };
                let reads = (0..sites).map(|t| (Self::silent(region, t) && t < read_to).then(|| self.face_of(&x[t * dw..(t + 1) * dw], &reaches)).transpose()).collect::<Result<Vec<_>>>()?;
                let blank: Vec<Option<Shares>> = reads.iter().map(|r| r.as_ref().map(|r| shares(&r.face))).collect();
                let next = self.paces_with(region, &blank)?;
                let moment = self.moments_of(region, &next)?;
                clock = Some(Box::new(TickClock { paces: next, moment, blank, reads }));
            }
            out.pairs += cell.rows.iter().map(|r| r.len() as u64).sum::<u64>();
            if let Some(prev) = &before {
                round_trips(prev, &cell.rows, sites, &mut trips);
            }
            before = Some(if keep { cell.rows.clone() } else { std::mem::take(&mut cell.rows) });
            if keep {
                out.ticks.push(cell);
            }
        }
        let read = (d.ticks.saturating_sub(1) * d.heads).max(1) as u128;
        out.echo = trips.iter().map(|&t| ((t + read / 2) / read) as u64).collect();
        out.paces = paces;
        out.moment = moment;
        out.read = vec![0i32; sites * dw];
        out.lift = vec![0i64; sites * dw];
        out.scale = vec![0i128; sites * d.lanes];
        out.faces = vec![None; sites];
        out.logits = vec![None; sites];
        let l = &self.layout;
        let mut z = vec![0i64; d.alphabet];
        let (mut r, mut s) = (Vec::with_capacity(dw), Vec::with_capacity(d.lanes));
        for t in 0..sites {
            if !region.unresolved[t] {
                continue;
            }
            r.clear();
            s.clear();
            lane_chart(&x[t * dw..(t + 1) * dw], d.lanes, &mut r, &mut s)?;
            // The face reads each class through its encoding (§16.26): the lift `y = R r̂ + b_R`, then `z(a) = ⟨E(a), y⟩ + c_a`.
            let mut y = vec![0i64; dw];
            affine(&self.theta[l.read..l.read + dw * dw], reaches.read, dw, &r, Some(&self.theta[l.lift_bias..l.lift_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut y)?;
            // [Brandon, November 15 02:06Z] Where the face reads its site's loudness, its sharpness `β` from the lanes' powers.
            let beta = self.loud_beta(&s)?.map(|(b, _)| b);
            self.tied_sharp(&y, beta, &mut z)?;
            out.lift[t * dw..(t + 1) * dw].copy_from_slice(&y);
            // The cavity field (§15.3): the read less its own echo, data from the read that formed it.
            if let Some(Some(echo)) = region.echo.get(t) {
                for (zc, &lc) in z.iter_mut().zip(&echo.logits) {
                    *zc = fit64(*zc as i128 - release(echo.b as i128 * lc as i128, SHARE_BITS))?;
                }
            }
            out.faces[t] = Some(self.tempered(&z, 1));
            out.logits[t] = Some(z.clone());
            out.read[t * dw..(t + 1) * dw].copy_from_slice(&r);
            out.scale[t * d.lanes..(t + 1) * d.lanes].copy_from_slice(&s);
        }
        Ok(out)
    }
}

/// [definition; agent-inferred, November 4, §16.40] **The chart by lanes** (the tower record, D2): a site's face of `L`
/// lanes is read lane by lane, each lane's `W = D/L` coordinates a ratio to its own power, `r̂_ℓ = r_ℓ / ‖r_ℓ‖_rms`, its
/// scale `‖r_ℓ‖_rms` pushed after the lanes before it; one lane is the chart over the whole width. Why lanes: a lane
/// founded beside trained ones with every read from it at zero ([`Constitution::laned`]) leaves each other lane's chart, and so
/// every face, exactly as it was, which a chart over the whole width would not (the new coordinates would join the power
/// every coordinate is divided by), and the reads from it carry a covector at once.
pub(crate) fn lane_chart(xt: &[i64], lanes: usize, read: &mut Vec<i32>, scale: &mut Vec<i128>) -> Result<()> {
    for lane in xt.chunks_exact(xt.len() / lanes) {
        let (r, s) = ratio_to_power(lane)?;
        read.extend_from_slice(&r);
        scale.push(s);
    }
    Ok(())
}

/// The founding's scale of the charts and pair drives at width `D`, `√(3/D)` as a ratio of square
/// roots on `2^(−16)`.
pub(crate) fn chart_scale(width: usize) -> (u128, u128) {
    ((3u128 << 32).isqrt(), ((width as u128) << 32).isqrt())
}
