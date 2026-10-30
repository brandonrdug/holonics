//! **The founded split of a pair contact** (#404, #408; record
//! `2026-10-30_THE_PAIR_CONTACT_IS_RACED_BEFORE_ITS_SPLIT_FOUNDS_WHERE_THE_BODY_GROWS`, §4).
//!
//! [definition; agent-inferred, October 30] The contact field widened by two holds every pair
//! contact's split dormant ([`Tower::paired`]): contact `o` and its copy `o + f` read the same
//! drives and their return parts sum to the old column, so the face is the old face and the
//! copies' difference is a coordinate the passage does not reach (`a = 0`, free by the code). Each
//! dormant pair carries a unit direction `v` on the read `r̂` it shares, turned each section by one
//! product `M v`, `M = Σ_t δv_t r̂_t r̂_tᵀ` with `δv` the pair's covector at its product. The
//! section after, the score and its squares decide the founding by the rank-one law
//! (`code.rank-one-founding`):
//!
//! ```text
//! φ_t = (v·r̂_t)²,   g = Σ_t δv_t φ_t,   S = Σ_t (δv_t φ_t)²,   τ = d²/4,   K the dormant pairs
//! found  ⇔  (ln 2 · g)² / (τ + ln²2 · S) > ln(1 + ln²2 · S/τ) + 2 ln K
//! θ̂ = −ln 2 · g / (τ + ln²2 · S),   ε = √|θ̂|
//! W_a[o] ± ε v,   W_b[o] ± sgn(θ̂) ε v   ⇒   the face moves by c θ̂ φ
//! ```
//!
//! `g` is in bits a unit of `θ` (the face's covector is the base-two code's), so `ln 2 · g` is
//! its nats; `ln²2 · S` is the score's sampled Fisher in nats. The price is the coordinate's own
//! code, `½ ln(1 + r)`, and its address, `ln K`: the interior's description names which of the
//! `K` dormant pairs it founds, so the code charges the choice the machine makes among them.
//! `ln 2` is its navigator's face on `2^(−30)` with its one-unit enclosure, and each logarithm is
//! `ln 2 · log₂` read on `2^(−20)` from above; both sides are monotone in `ln 2`, so a pair founds
//! only when the left side at the enclosure's foot passes the right side at its head (a tie is
//! refused).
//!
//! One pair founds a section, the one with the largest surplus, and the test only proposes it: the
//! section's reread at `θ̂` measures the line exactly, and the founding deposits only where the
//! reread's code falls by more than the coordinate's price on the curvature the line has
//! ([`measured_line`], [`price_bits`]); refused, the line's own mode is read once more
//! ([`TowerLearner::section_founding`]). The squares' curvature is a sampled estimate, and on the
//! tiny parity passage the measured line was not the test's quadratic (agent-inferred, October 30).
//!
//! The score is the code's slope along the split on the tower it was read on, and only there: the
//! section's step moves the drives both copies share along the same covectors, so the split is read
//! again on the tower the step left, and the test decides on what the step did not take
//! (agent-inferred, October 30; measured: decided on the opening read, 20 of the race's first 28
//! proposed foundings raised the code they were predicted to lower).
use super::*;
use crate::ratio::Rat;
use num_bigint::BigInt;
use num_traits::ToPrimitive;

/// The read's working grain for a turned direction before it is normalized: the turned sum is
/// released until its largest entry is below `2^40`, so its squares sum in 128 bits.
const TURN_BITS: u32 = 40;

/// `log₂(1 + r)`'s grain, `2^(−20)`: the code reading's.
const PRICE_BITS: u32 = READ_BITS;

/// A cell's score term is refused at `2^48`, so its square is below `2^96` and the squares of
/// fewer than `2^31` cells sum below `2^127` (the card sums them in the same 128 bits).
pub const SCORE_BITS: u32 = 48;

/// [definition] **The paired contacts' carried directions**: `levels[l][e]` is the unit direction
/// of dormant pair `e` (contacts `e` and `e + f/2`) on the read it shares, on `2^(−16)`, or `None`
/// once the pair is founded and its copies learn on their own.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairedContacts {
    pub levels: Vec<Vec<Option<Vec<i32>>>>,
}

/// One dormant pair's read over a section: the score `Σ δv φ` on `2^(−24)` (bits a unit of `θ`),
/// its squares `Σ (δv φ)²` on `2^(−48)`, and the turned sum `Σ (δv y) r̂` on `2^(−40)`. A founded
/// pair's read is empty.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct PairRead {
    pub score: i128,
    pub squares: i128,
    pub turned: Vec<i128>,
}

/// A section's split read, `levels[l][e]`.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct SplitRead {
    pub levels: Vec<Vec<PairRead>>,
}

/// A founding the test admitted, before its certificate: the level and pair, `θ̂` on `2^(−48)`,
/// the predicted change of the section's code in bits on `2^(−20)` (`−ln 2 · g²/(2(τ + ln²2 S))`,
/// negative), the test's surplus (fit less price, nats on `2^(−20)`), and the read it was decided on.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Founding {
    pub level: usize,
    pub pair: usize,
    pub theta: i128,
    pub predicted: i64,
    pub surplus: i128,
    pub score: i128,
    pub squares: i128,
}

/// A section's founding and its certificate, codes on `2^(−20)` bits: the section's code after its
/// step, the reread's code at the test's `θ̂`, and at the measured line's mode `θ*` when the first
/// reread was refused and the line has one; the founding as deposited (its `θ` the one admitted);
/// the code the section leaves; whether a reread admitted it; and the dormant pairs left.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct FoundingReceipt {
    pub foundings: Vec<Founding>,
    pub code_before: i64,
    pub reread: i64,
    pub remeasured: Option<i64>,
    pub code_after: i64,
    pub admitted: bool,
    pub dormant: usize,
}

impl SplitRead {
    /// Two streams' reads summed entry by entry; integer addition is associative, so any partition
    /// of the streams gives the same sum.
    pub fn summed(mut self, other: &SplitRead) -> Result<Self> {
        if self.levels.is_empty() {
            return Ok(other.clone());
        }
        if other.levels.is_empty() {
            return Ok(self);
        }
        if self.levels.len() != other.levels.len() {
            return refuse("two split reads of different towers");
        }
        for (a, b) in self.levels.iter_mut().zip(&other.levels) {
            if a.len() != b.len() {
                return refuse("two split reads of different towers");
            }
            for (p, q) in a.iter_mut().zip(b) {
                if p.turned.len() != q.turned.len() {
                    return refuse("two split reads of different towers");
                }
                p.score += q.score;
                p.squares = p.squares.checked_add(q.squares).ok_or(TowerError::Refused("a pair's squares outgrew their 128-bit carrier"))?;
                for (x, y) in p.turned.iter_mut().zip(&q.turned) {
                    *x += *y;
                }
            }
        }
        Ok(self)
    }
}

/// `x` as a unit direction on `2^(−16)`: released until its largest entry is below `2^40`, then
/// divided by its norm; `None` for a zero vector (the passage did not reach it).
fn unit(x: &[i128]) -> Result<Option<Vec<i32>>> {
    let largest = x.iter().map(|v| v.unsigned_abs()).max().unwrap_or(0);
    if largest == 0 {
        return Ok(None);
    }
    let shift = (128 - largest.leading_zeros()).saturating_sub(TURN_BITS);
    let t: Vec<i128> = x.iter().map(|&v| release(v, shift)).collect();
    let power: u128 = t.iter().map(|&v| v.unsigned_abs() * v.unsigned_abs()).sum();
    let norm = power.isqrt() as i128;
    if norm == 0 {
        return Ok(None);
    }
    collect_exact(t.iter().map(|&v| fit32(div_nearest(v << FACE_BITS, norm), "a direction outgrew its 32-bit carrier"))).map(Some)
}

/// A `BigInt` numerator over `2^bits`.
fn dyadic(n: i128, bits: u32) -> Rat {
    Rat::new(BigInt::from(n), BigInt::from(1) << bits)
}

/// `x` on `2^(−bits)`, to the nearest numerator.
fn on_grain(x: &Rat, bits: u32) -> Result<i128> {
    (x * Rat::from_integer(BigInt::from(1) << bits)).round().to_integer().to_i128().ok_or(TowerError::Refused("a founding's value outgrew its 128-bit carrier"))
}

/// `log₂ x` read from above on `2^(−20)` for `x ≥ 1` given as `2^62 / x` floored on `2^(−62)`.
fn log2_above(p: &Rat) -> Result<Rat> {
    let p_int = (p * Rat::from_integer(BigInt::from(1) << 62)).floor().to_integer().to_u128().ok_or(TowerError::Refused("a price's ratio outgrew its carrier"))?;
    if p_int == 0 || p_int > 1u128 << 62 {
        return refuse("a price's ratio outside its carrier");
    }
    Ok(dyadic(-log2_face(p_int, PRICE_BITS) + 1, PRICE_BITS))
}

/// [definition] **The rank-one founding of one of `dormant` dormant pairs** (the module header):
/// `θ̂` on `2^(−48)`, the predicted change of the code on `2^(−20)` bits and the surplus of fit over
/// price (nats on `2^(−20)`) when the enclosures
/// separate above the price, `None` otherwise. `width` is the read's `d`.
pub fn founded(read: &PairRead, width: usize, dormant: usize) -> Result<Option<(i128, i64, i128)>> {
    if read.score == 0 || read.squares < 0 || dormant == 0 {
        return Ok(None);
    }
    let g = dyadic(read.score, COVECTOR_BITS);
    let s = dyadic(read.squares, 2 * COVECTOR_BITS);
    let tau = Rat::new(BigInt::from(width * width), BigInt::from(4));
    let ln2 = ln2_face();
    let (lo, hi) = (dyadic(ln2 - 1, 30), dyadic(ln2 + 1, 30));
    // The fit at the enclosure's foot: L² g² / (τ + L² S), nats.
    let fit = |l: &Rat| -> Rat { l * l * &g * &g / (&tau + l * l * &s) };
    // The price at its head: L · (log₂(1 + L² S/τ) + 2 log₂ K), each log₂ read from above.
    let address = log2_above(&Rat::new(BigInt::from(1), BigInt::from(dormant)))?;
    let price = |l: &Rat| -> Result<Rat> {
        let own = log2_above(&(&tau / (&tau + l * l * &s)))?;
        Ok(l * (own + Rat::from_integer(BigInt::from(2)) * &address))
    };
    let surplus = fit(&lo) - price(&hi)?;
    if surplus <= Rat::from_integer(BigInt::from(0)) {
        return Ok(None);
    }
    let theta = -(&lo * &g) / (&tau + &lo * &lo * &s);
    let predicted = -(&lo * &g * &g) / (Rat::from_integer(BigInt::from(2)) * (&tau + &lo * &lo * &s));
    let predicted = i64::try_from(on_grain(&predicted, PRICE_BITS)?).map_err(|_| TowerError::Refused("a predicted change outgrew its 64-bit carrier"))?;
    let theta = on_grain(&theta, 2 * MATERIAL_BITS)?;
    Ok(Some((theta, predicted, on_grain(&surplus, PRICE_BITS)?)))
}

/// [definition; agent-inferred, October 30] **The line a founding's reread measured, and the price
/// its coordinate pays on it.** The test's quadratic takes the score's squares for the curvature
/// along `θ` (the empirical Fisher); the reread reads the section's code exactly at `θ̂`, so with the
/// score `g` as the line's slope at zero its measured change `Δ` fixes the curvature the line
/// actually has, `H = 2(Δ − g θ̂)/θ̂²` (bits a unit of `θ²`). Measured on the paired parity passage,
/// the squares under-read it about threefold: a founding predicted at `−8.6` bits lowered the code by
/// `0.79`.
///
/// Returns the curvature the price is charged on, `σ = max(ln²2 · S, ln 2 · H, 0)` in nats (the
/// larger reading, since the price grows with it), and the line's posterior mode
/// `θ* = −ln 2 · g/(τ + ln 2 · H)` on `2^(−48)` when `τ + ln 2 · H > 0` (the line is bounded
/// below under the prior), else `None`.
pub fn measured_line(founding: &Founding, width: usize, measured: i64) -> Result<(Rat, Option<i128>)> {
    let g = dyadic(founding.score, COVECTOR_BITS);
    let s = dyadic(founding.squares, 2 * COVECTOR_BITS);
    let theta = dyadic(founding.theta, 2 * MATERIAL_BITS);
    if founding.theta == 0 {
        return refuse("a founding at zero measures no line");
    }
    let delta = dyadic(measured as i128, PRICE_BITS);
    let tau = Rat::new(BigInt::from(width * width), BigInt::from(4));
    let ln2 = ln2_face();
    let (lo, hi) = (dyadic(ln2 - 1, 30), dyadic(ln2 + 1, 30));
    let two = Rat::from_integer(BigInt::from(2));
    let zero = Rat::from_integer(BigInt::from(0));
    let curvature = &two * (&delta - &g * &theta) / (&theta * &theta);
    let mut sigma = &hi * &hi * &s;
    if &hi * &curvature > sigma {
        sigma = &hi * &curvature;
    }
    if sigma < zero {
        sigma = zero.clone();
    }
    let bound = &tau + &lo * &curvature;
    let mode = if bound > zero { Some(on_grain(&(-(&lo * &g) / bound), 2 * MATERIAL_BITS)?) } else { None };
    Ok((sigma, mode.filter(|&t| t != 0)))
}

/// [definition; agent-inferred, October 30] **The price of a founded coordinate at `θ`**, in bits
/// read from above: the two-part code's Laplace charge `(½ τ θ² + ½ ln(1 + σ/τ) + ln K)/ln 2`, the
/// prior's cost of the value, the coordinate's own precision and its address among the `K`
/// dormant pairs. A founding deposits only where the reread's exact code falls by more than this.
pub fn price_bits(theta: i128, sigma: &Rat, width: usize, dormant: usize) -> Result<Rat> {
    if dormant == 0 {
        return refuse("a price among no dormant pairs");
    }
    let theta = dyadic(theta, 2 * MATERIAL_BITS);
    let tau = Rat::new(BigInt::from(width * width), BigInt::from(4));
    let lo = dyadic(ln2_face() - 1, 30);
    let half = Rat::new(BigInt::from(1), BigInt::from(2));
    let value = &half * &tau * &theta * &theta / lo;
    let own = &half * log2_above(&(&tau / (&tau + sigma)))?;
    let address = log2_above(&Rat::new(BigInt::from(1), BigInt::from(dormant)))?;
    Ok(value + own + address)
}

impl PairedContacts {
    /// Each pair of `tower`'s paired contacts dormant, its direction opened at its first drive's row
    /// normalized (the read the contact already draws on).
    pub fn opened(tower: &Tower) -> Result<Self> {
        let d = &tower.declaration;
        if d.contact != ContactLaw::Pair || d.contacts % 2 != 0 {
            return refuse("paired contacts are an even count of pair contacts");
        }
        let (w, h) = (d.width, d.contacts / 2);
        let levels = tower
            .layout
            .levels
            .iter()
            .map(|lv| {
                (0..h)
                    .map(|e| {
                        let row: Vec<i128> = tower.theta[lv.contact + e * w..lv.contact + (e + 1) * w].iter().map(|&v| v as i128).collect();
                        unit(&row)?.ok_or(TowerError::Refused("a contact's first drive row at zero opens no direction")).map(Some)
                    })
                    .collect::<Result<Vec<_>>>()
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(Self { levels })
    }

    /// The pairs still dormant.
    pub fn dormant(&self) -> usize {
        self.levels.iter().flatten().filter(|v| v.is_some()).count()
    }

    /// The directions as text: `paired LEVELS PAIRS WIDTH`, then one line a level, each pair `-`
    /// once founded or its entries joined by commas.
    pub fn to_text(&self) -> String {
        let pairs = self.levels.first().map_or(0, |l| l.len());
        let width = self.levels.iter().flatten().flatten().next().map_or(0, |v| v.len());
        let mut s = format!("paired {} {pairs} {width}\n", self.levels.len());
        for level in &self.levels {
            let line: Vec<String> = level
                .iter()
                .map(|v| match v {
                    Some(v) => v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","),
                    None => "-".to_string(),
                })
                .collect();
            s.push_str(&line.join(" "));
            s.push('\n');
        }
        s
    }

    pub fn from_text(text: &str) -> Result<Self> {
        let lines: Vec<&str> = text.lines().collect();
        let head: Vec<&str> = lines.first().map_or(Vec::new(), |l| l.split(' ').collect());
        let count = |s: &str| s.parse::<usize>().map_err(|_| TowerError::Refused("a paired count that is not a count"));
        if head.len() != 4 || head[0] != "paired" {
            return refuse("not the paired contacts' directions");
        }
        let (levels, pairs, width) = (count(head[1])?, count(head[2])?, count(head[3])?);
        if lines.len() != levels + 1 {
            return refuse("the paired directions are one line a level");
        }
        let levels = lines[1..]
            .iter()
            .map(|line| {
                let tokens: Vec<&str> = line.split(' ').filter(|t| !t.is_empty()).collect();
                if tokens.len() != pairs {
                    return refuse("a paired level of the wrong extent");
                }
                tokens
                    .iter()
                    .map(|t| {
                        if *t == "-" {
                            return Ok(None);
                        }
                        let v = t.split(',').map(|x| x.parse::<i32>().map_err(|_| TowerError::Refused("a direction entry that is not an integer"))).collect::<Result<Vec<_>>>()?;
                        if v.len() != width {
                            return refuse("a direction of the wrong width");
                        }
                        Ok(Some(v))
                    })
                    .collect::<Result<Vec<_>>>()
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(Self { levels })
    }

    /// Whether these directions are `tower`'s paired contacts'.
    pub fn admits(&self, tower: &Tower) -> Result<()> {
        let d = &tower.declaration;
        if d.contact != ContactLaw::Pair || d.contacts % 2 != 0 || self.levels.len() != d.levels {
            return refuse("paired directions of another tower");
        }
        if self.levels.iter().any(|l| l.len() != d.contacts / 2 || l.iter().flatten().any(|v| v.len() != d.width)) {
            return refuse("paired directions of another tower");
        }
        Ok(())
    }
}

impl Tower {
    /// [definition; agent-inferred, October 30] **The contact field widened by two** (the module
    /// header): each contact's first and second drive rows and biases repeated (contact `o` and its
    /// copy `o + f`), its return column split into two parts that sum to it (the remainder carried
    /// by the first part), every other family kept. Every sum the forward forms is the old sum, so
    /// the face is the old face. Refused on a contact law with no split (the rectifier, the foil)
    /// and on every part whose joins also drive the contacts (participation, the passage, the
    /// strands) or read their conduction (the mutual contact), and on the pair and ring faces and
    /// the rotor, whose lifts are owed.
    pub fn paired(&self) -> Result<Self> {
        Ok(self.paired_from()?.0)
    }

    /// The paired tower and, for each of its entries, the old entry it carries and whether its
    /// covector is halved (a repeated drive row or bias) or kept (a return part, every other family).
    fn paired_from(&self) -> Result<(Self, Vec<(usize, bool)>)> {
        let old = self.declaration;
        if old.contact != ContactLaw::Pair {
            return refuse("only the pair contact splits: the rectifier's second derivative lives on its kink");
        }
        if self.pair.is_some() || self.ring.is_some() || self.rotor.is_some() || self.strands.is_some() {
            return refuse("the pairing's lift of a pair face, ring, rotor or strands is owed");
        }
        if self.participation.is_some() || self.passage || self.mutual.is_some() {
            return refuse("the pairing's lift of participation, the passage or the mutual contact is owed: each also drives or reads the contacts");
        }
        let d = TowerDeclaration { contacts: old.contacts.checked_mul(2).ok_or(TowerError::Refused("a paired extent outgrew its carrier"))?, ..old };
        let layout = Layout::new(&d, 0, 0, 0, 0, None, false, None);
        let (w, f) = (old.width, old.contacts);
        let mut new = vec![0i32; layout.len];
        let mut from = vec![(0usize, false); layout.len];
        let keep = |new: &mut [i32], from: &mut [(usize, bool)], at: usize, to: usize, len: usize| {
            new[to..to + len].copy_from_slice(&self.theta[at..at + len]);
            for (i, slot) in from[to..to + len].iter_mut().enumerate() {
                *slot = (at + i, false);
            }
        };
        let (ol, nl) = (&self.layout, &layout);
        keep(&mut new, &mut from, ol.encoding, nl.encoding, old.alphabet * w);
        for (o, l) in ol.levels.iter().zip(&nl.levels) {
            for (at, to, len) in [
                (o.move_re, l.move_re, old.modes),
                (o.move_im, l.move_im, old.modes),
                (o.push_re, l.push_re, old.modes * w),
                (o.push_im, l.push_im, old.modes * w),
                (o.read_re, l.read_re, w * old.modes),
                (o.read_im, l.read_im, w * old.modes),
                (o.ret_bias, l.ret_bias, w),
                (o.gate, l.gate, if old.gated { old.modes * w } else { 0 }),
                (o.gate_bias, l.gate_bias, if old.gated { old.modes } else { 0 }),
                (o.turn, l.turn, if old.turned { old.modes * w } else { 0 }),
                (o.turn_bias, l.turn_bias, if old.turned { old.modes } else { 0 }),
                (o.pump, l.pump, if old.pumped { old.modes * w } else { 0 }),
                (o.pump_bias, l.pump_bias, if old.pumped { old.modes } else { 0 }),
                (o.pump_axis, l.pump_axis, if old.pumped { old.modes * w } else { 0 }),
                (o.pump_axis_bias, l.pump_axis_bias, if old.pumped { old.modes } else { 0 }),
            ] {
                keep(&mut new, &mut from, at, to, len);
            }
            // The drives' rows and biases repeated, copy after copy.
            for (at, to, len) in [(o.contact, l.contact, w), (o.contact_bias, l.contact_bias, 1), (o.pair, l.pair, w), (o.pair_bias, l.pair_bias, 1)] {
                for c in 0..2 {
                    for e in 0..f {
                        for i in 0..len {
                            new[to + (c * f + e) * len + i] = self.theta[at + e * len + i];
                            from[to + (c * f + e) * len + i] = (at + e * len + i, true);
                        }
                    }
                }
            }
            // The return's columns split: row j's column e into parts (j, e) and (j, f + e).
            for j in 0..w {
                for e in 0..f {
                    let v = self.theta[o.ret + j * f + e] as i128;
                    let (q, rem) = (v.div_euclid(2), v.rem_euclid(2));
                    for c in 0..2 {
                        let at = l.ret + j * 2 * f + c * f + e;
                        new[at] = fit32(q + i128::from(c == 0 && rem == 1), "a return part outgrew its 32-bit carrier")?;
                        from[at] = (o.ret + j * f + e, false);
                    }
                }
            }
        }
        keep(&mut new, &mut from, ol.readout, nl.readout, old.alphabet * w);
        keep(&mut new, &mut from, ol.readout_bias, nl.readout_bias, old.alphabet);
        let tower = Self { declaration: d, theta: new, layout, ..self.clone() };
        Ok((tower, from))
    }

    /// One stream's split read (the module header) over its section's cells and the contact
    /// covectors the reverse kept (`dvs[level][cell][contact]`).
    fn split_read_of(&self, cells: &[Cell], dvs: &[Vec<Vec<i64>>], paired: &PairedContacts) -> Result<SplitRead> {
        let d = &self.declaration;
        let (w, h) = (d.width, d.contacts / 2);
        let levels = paired
            .levels
            .iter()
            .enumerate()
            .map(|(l, pairs)| {
                pairs
                    .iter()
                    .enumerate()
                    .map(|(e, direction)| {
                        let Some(v) = direction else { return Ok(PairRead::default()) };
                        let mut read = PairRead { score: 0, squares: 0, turned: vec![0; w] };
                        for (cell, dv) in cells.iter().zip(&dvs[l]) {
                            let r = &cell.levels[l].read;
                            let dv = dv[e] as i128 + dv[e + h] as i128;
                            let y = release(v.iter().zip(r).map(|(&a, &b)| a as i128 * b as i128).sum(), FACE_BITS);
                            let phi = release(y * y, FACE_BITS);
                            let s = release(dv * phi, FACE_BITS);
                            // Below 2^48 a term's square summed over fewer than 2^31 cells stays
                            // below 2^127, the card's bound as the host's.
                            if s.unsigned_abs() >= 1 << SCORE_BITS {
                                return refuse("a pair's score term outgrew its carrier");
                            }
                            read.score += s;
                            read.squares = read.squares.checked_add(s * s).ok_or(TowerError::Refused("a pair's squares outgrew their 128-bit carrier"))?;
                            let q = release(dv * y, FACE_BITS);
                            for (t, &x) in read.turned.iter_mut().zip(r) {
                                *t += q * x as i128;
                            }
                        }
                        Ok(read)
                    })
                    .collect::<Result<Vec<_>>>()
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(SplitRead { levels })
    }

    /// One stream's covector and its split read: [`Tower::reverse_joined`] keeping the contact
    /// covectors, read against the stream's cells.
    pub(super) fn reverse_split(&self, opening: &TowerState, cells: &[Cell], classes: &[usize], compared: Option<&[Option<usize>]>, paired: &PairedContacts) -> Result<(Vec<i128>, SplitRead)> {
        paired.admits(self)?;
        let mut dvs = Vec::new();
        let (g, _) = self.reverse_joined(opening, cells, classes, None, compared, None, Some(&mut dvs))?;
        let read = self.split_read_of(cells, &dvs, paired)?;
        Ok((g, read))
    }

    /// The founded splits mapped onto the material (the module header): for each founding, `±ε v` on
    /// the pair's first drive rows and `±sgn(θ̂) ε v` on its second.
    pub fn found_splits(&self, paired: &PairedContacts, foundings: &[Founding]) -> Result<Self> {
        paired.admits(self)?;
        let (w, h) = (self.declaration.width, self.declaration.contacts / 2);
        let mut tower = self.clone();
        for founding in foundings {
            let v = paired.levels.get(founding.level).and_then(|l| l.get(founding.pair)).and_then(|v| v.as_ref()).ok_or(TowerError::Refused("a founding of a pair that is not dormant"))?;
            let lv = self.layout.levels[founding.level];
            let epsilon = founding.theta.unsigned_abs().isqrt() as i128;
            let sign = founding.theta.signum();
            for (j, &x) in v.iter().enumerate() {
                let delta = release(epsilon * x as i128, FACE_BITS);
                for (family, signed) in [(lv.contact, delta), (lv.pair, sign * delta)] {
                    for (copy, by) in [(founding.pair, signed), (founding.pair + h, -signed)] {
                        let at = family + copy * w + j;
                        tower.theta[at] = fit32(tower.theta[at] as i128 + by, "a founded drive outgrew its 32-bit carrier")?;
                    }
                }
            }
        }
        Ok(tower)
    }
}

impl TowerLearner {
    /// [definition; agent-inferred, October 30] **The learner with its contacts paired**
    /// ([`Tower::paired`]) and every pair dormant: a repeated drive row or bias takes half the old
    /// covector (its return is half), so it carries `m/2` and `v/4`; a return part takes the old
    /// covector whole and carries `m` and `v`. Every copy opens on the old normalized step. Refused
    /// under a declared hold, whose ranges name the old material.
    pub fn paired(&self) -> Result<(Self, PairedContacts)> {
        if !self.held.is_empty() {
            return refuse("a held learner's pairing: its holds name the old material");
        }
        let (tower, from) = self.tower.paired_from()?;
        let first = from.iter().map(|&(i, halved)| if halved { div_nearest(self.first[i], 2) } else { self.first[i] }).collect();
        let second = from.iter().map(|&(i, halved)| if halved { div_nearest(self.second[i], 4) } else { self.second[i] }).collect();
        let paired = PairedContacts::opened(&tower)?;
        Ok((Self { tower, first, second, opened: self.opened, rate_bits: self.rate_bits, swell: Vec::new(), held: Vec::new() }, paired))
    }

    /// The section's founding decided (the module header): of the pairs the test admits, the one
    /// with the largest surplus, or none.
    pub(super) fn foundings(&self, paired: &PairedContacts, read: &SplitRead) -> Result<Vec<Founding>> {
        paired.admits(&self.tower)?;
        if read.levels.len() != paired.levels.len() {
            return refuse("a split read of another tower");
        }
        let (width, dormant) = (self.tower.declaration.width, paired.dormant());
        let mut out = Vec::new();
        for (l, (pairs, reads)) in paired.levels.iter().zip(&read.levels).enumerate() {
            for (e, (direction, r)) in pairs.iter().zip(reads).enumerate() {
                if direction.is_none() {
                    continue;
                }
                if let Some((theta, predicted, surplus)) = founded(r, width, dormant)? {
                    if theta != 0 {
                        out.push(Founding { level: l, pair: e, theta, predicted, surplus, score: r.score, squares: r.squares });
                    }
                }
            }
        }
        // One founding a section, the one the two-part code favours most (its address among the
        // `K` already charged for the choice): the reread measures one coordinate's line exactly,
        // while several founded together share the face and their predictions do not add
        // (measured: three foundings predicted at −20.9 bits together raised the code by 1.4).
        // Ties go to the first level and pair.
        let best = out.iter().enumerate().max_by_key(|(i, f)| (f.surplus, std::cmp::Reverse(*i))).map(|(i, _)| i);
        Ok(best.map(|i| vec![out.swap_remove(i)]).unwrap_or_default())
    }
}

impl PairedContacts {
    /// Each dormant pair's direction turned by its read (`v ← M v/‖M v‖`; kept where the passage
    /// did not reach it), and the directions of the pairs whose founding was admitted retired.
    pub fn turned(&mut self, read: &SplitRead, founded: &[Founding]) -> Result<()> {
        for (pairs, reads) in self.levels.iter_mut().zip(&read.levels) {
            for (direction, r) in pairs.iter_mut().zip(reads) {
                if direction.is_some() {
                    if let Some(v) = unit(&r.turned)? {
                        *direction = Some(v);
                    }
                }
            }
        }
        for f in founded {
            self.levels[f.level][f.pair] = None;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::super::realization::HostPass;
    use super::super::tests::tiny_contacts;
    use super::*;

    const PASSAGE: [usize; 40] = [1, 2, 0, 1, 1, 3, 2, 2, 0, 1, 2, 1, 0, 0, 3, 1, 2, 2, 1, 0, 1, 2, 3, 0, 1, 1, 2, 0, 2, 1, 3, 1, 0, 2, 2, 1, 0, 1, 2, 3];

    fn tiny_pair(gated: bool, turned: bool) -> Tower {
        tiny_contacts(2, 4, 4, gated, turned, false, ContactLaw::Pair)
    }

    /// A passage whose low bit is the parity of the two high bits before it: `u_t = 2 b_t +
    /// (b_(t−1) xor b_(t−2))`, the `b_t` from a xorshift. Its news at the low bit is a product of two
    /// heard signs, the conjunction a single quadratic direction `(v·r̂)²` carries.
    fn parity_passage(seed: u32, n: usize) -> Vec<usize> {
        let mut x = seed;
        let mut b = vec![0usize; n];
        for v in &mut b {
            x ^= x << 13;
            x ^= x >> 17;
            x ^= x << 5;
            *v = (x >> 7) as usize & 1;
        }
        (0..n).map(|t| 2 * b[t] + if t >= 2 { b[t - 1] ^ b[t - 2] } else { 0 }).collect()
    }

    /// A learner of the tiny pair tower after a few sections over the passage, so its covectors
    /// carry what the passage taught.
    fn taught() -> TowerLearner {
        let mut learner = TowerLearner::new(tiny_pair(true, false), 6);
        let mut states = vec![learner.tower.rest()];
        for k in 0..4 {
            learner.section(&mut states, &[&PASSAGE[k * 9..k * 9 + 10]]).expect("section");
        }
        learner
    }

    /// Acceptance 1: the paired tower reads the old faces class by class and keeps the old state;
    /// a repeated drive entry carries `m/2` and `v/4`, a return part `m` and `v`; the rectifier and
    /// every part whose lift is owed are refused.
    #[test]
    fn the_paired_tower_reads_the_old_faces_and_its_copies_open_on_the_old_step() {
        for tower in [tiny_pair(false, false), tiny_pair(true, false), tiny_pair(true, true)] {
            let paired = tower.paired().expect("paired");
            assert_eq!(paired.declaration.contacts, 2 * tower.declaration.contacts);
            let (mut old, mut new) = (tower.rest(), paired.rest());
            for &u in &PASSAGE {
                assert_eq!(paired.advance(&mut new, u).expect("advanced"), tower.advance(&mut old, u).expect("advanced"));
                assert_eq!(new, old);
            }
        }
        let learner = taught();
        let (paired, directions) = learner.paired().expect("paired");
        assert_eq!(directions.dormant(), 2 * 4);
        let (f, w) = (4, 4);
        for l in 0..2 {
            let (o, n) = (learner.tower.layout.levels[l], paired.tower.layout.levels[l]);
            for (e, i) in [(1, 2), (3, 0)] {
                let at = o.contact + e * w + i;
                for c in 0..2 {
                    let to = n.contact + (c * f + e) * w + i;
                    assert_eq!(paired.tower.theta[to], learner.tower.theta[at]);
                    assert_eq!(paired.first[to], div_nearest(learner.first[at], 2));
                    assert_eq!(paired.second[to], div_nearest(learner.second[at], 4));
                }
                let at = o.ret + i * f + e;
                let parts: i32 = (0..2).map(|c| paired.tower.theta[n.ret + i * 2 * f + c * f + e]).sum();
                assert_eq!(parts, learner.tower.theta[at]);
                for c in 0..2 {
                    assert_eq!(paired.first[n.ret + i * 2 * f + c * f + e], learner.first[at]);
                }
            }
        }
        assert!(tiny_contacts(2, 4, 4, true, false, false, ContactLaw::Rectifying).paired().is_err(), "the rectifier");
        assert!(tiny_contacts(2, 4, 4, true, false, false, ContactLaw::PairLinear).paired().is_err(), "the foil");
        assert!(directions.levels.iter().flatten().all(|v| v.as_ref().is_some_and(|v| v.len() == w)));
        assert_eq!(PairedContacts::from_text(&directions.to_text()).expect("read"), directions);
    }

    /// Acceptance 2: turned repeatedly on one section, each direction becomes a fixed point of the
    /// turn up to its sign, and its score is no smaller in magnitude than the opening direction's or
    /// any basis direction's.
    #[test]
    fn the_direction_turns_to_a_fixed_point_whose_score_tops_the_basis() {
        let (paired, opened) = taught().paired().expect("paired");
        let tower = &paired.tower;
        let reaches = tower.reaches();
        let opening = tower.rest();
        let mut end = opening.clone();
        let cells = tower.forward(&mut end, &PASSAGE, &reaches).expect("forward");
        let read = |dirs: &PairedContacts| tower.reverse_split(&opening, &cells, &PASSAGE, None, dirs).expect("split read").1;
        let mut directions = opened.clone();
        for _ in 0..64 {
            let r = read(&directions);
            directions.turned(&r, &[]).expect("turned");
        }
        let at = read(&directions);
        let mut once = directions.clone();
        once.turned(&at, &[]).expect("turned");
        for (a, b) in once.levels.iter().flatten().zip(directions.levels.iter().flatten()) {
            let (a, b) = (a.as_ref().expect("dormant"), b.as_ref().expect("dormant"));
            let same = a.iter().zip(b).all(|(x, y)| (x - y).abs() <= 4);
            let opposite = a.iter().zip(b).all(|(x, y)| (x + y).abs() <= 4);
            assert!(same || opposite, "{a:?} against {b:?}");
        }
        let from_opening = read(&opened);
        let w = tower.declaration.width;
        let basis: Vec<SplitRead> = (0..w)
            .map(|j| {
                let unit: Vec<i32> = (0..w).map(|i| if i == j { 1 << FACE_BITS } else { 0 }).collect();
                read(&PairedContacts { levels: opened.levels.iter().map(|l| l.iter().map(|_| Some(unit.clone())).collect()).collect() })
            })
            .collect();
        for (l, pairs) in at.levels.iter().enumerate() {
            for (e, top) in pairs.iter().enumerate() {
                let others = std::iter::once(&from_opening).chain(&basis).map(|r| r.levels[l][e].score.abs());
                for other in others {
                    assert!(top.score.abs() >= other, "level {l} pair {e}: {} under {other}", top.score);
                }
            }
        }
    }

    /// The streams' split read summed, each stream read forward from its opening on `tower`.
    fn split_of(tower: &Tower, opening: &[TowerState], parts: &[&[usize]], directions: &PairedContacts) -> SplitRead {
        let reaches = tower.reaches();
        opening.iter().zip(parts).fold(SplitRead::default(), |sum, (o, c)| {
            let mut end = o.clone();
            let cells = tower.forward(&mut end, c, &reaches).expect("forward");
            sum.summed(&tower.reverse_split(o, &cells, c, None, directions).expect("split").1).expect("summed")
        })
    }

    /// The score is the code's slope along the split on the tower it was read on: a split of
    /// `θ = ∓2^(−8)` against the score's sign moves the section's code by `g θ` within a quarter of
    /// it and `2^(−14)` bits, on every pair of the ungated, gated and turned tiny towers.
    #[test]
    fn the_score_is_the_codes_slope_along_the_split() {
        for (gated, turned) in [(false, false), (true, false), (true, true)] {
            let (paired, directions) = {
                let mut learner = TowerLearner::new(tiny_pair(gated, turned), 6);
                let mut states = vec![learner.tower.rest()];
                for k in 0..4 {
                    learner.section(&mut states, &[&PASSAGE[k * 9..k * 9 + 10]]).expect("section");
                }
                learner.paired().expect("paired")
            };
            let tower = &paired.tower;
            let opening = [tower.rest()];
            let read = split_of(tower, &opening, &[&PASSAGE], &directions);
            let code = tower.read(&mut tower.rest(), &PASSAGE).expect("read");
            for (l, pairs) in read.levels.iter().enumerate() {
                for (e, r) in pairs.iter().enumerate() {
                    let theta = -r.score.signum() << (2 * MATERIAL_BITS - 8);
                    let founding = Founding { level: l, pair: e, theta, predicted: 0, surplus: 0, score: r.score, squares: r.squares };
                    let moved = tower.found_splits(&directions, &[founding]).expect("split").read(&mut tower.rest(), &PASSAGE).expect("read") - code;
                    // g θ on 2^(−20) bits: the score on 2^(−24), θ on 2^(−48).
                    let slope = release(r.score * theta, COVECTOR_BITS + 2 * MATERIAL_BITS - READ_BITS);
                    let off = (moved as i128 - slope).abs();
                    assert!(off <= slope.abs() / 4 + (1 << 6), "gated {gated} turned {turned} level {l} pair {e}: moved {moved} against {slope}");
                }
            }
        }
    }

    /// The founding is decided on the tower the step left: a founding section's proposal and its
    /// directions' turn are those of the split read on that tower, not on the opening's, and the step
    /// moves the score (here it turns some pair's sign).
    #[test]
    fn the_founding_is_decided_on_the_tower_the_step_left() {
        let streams: Vec<Vec<usize>> = (0..4).map(|s| parity_passage(0x9e37_79b9 ^ (s as u32 + 1), 64 * 12 + 1)).collect();
        let section = |k: usize| -> Vec<&[usize]> { streams.iter().map(|p| &p[k * 64..k * 64 + 65]).collect() };
        let mut learner = TowerLearner::new(tiny_pair(true, false), 6);
        let mut states = vec![learner.tower.rest(); 4];
        for k in 0..2 {
            learner.section(&mut states, &section(k)).expect("section");
        }
        let (mut learner, mut directions) = learner.paired().expect("paired");
        let (mut deposited, mut turned_sign) = (0usize, 0usize);
        let key = |f: &Founding| (f.level, f.pair, f.score, f.squares, f.predicted, f.surplus);
        for k in 2..12 {
            let parts = section(k);
            let opening = states.clone();
            let before = directions.clone();
            let opened = split_of(&learner.tower, &opening, &parts, &before);
            let mut stepped = learner.clone();
            deposited += stepped.section(&mut opening.clone(), &parts).expect("section").deposited as usize;
            let read = split_of(&stepped.tower, &opening, &parts, &before);
            let decided = stepped.foundings(&before, &read).expect("decided");
            let (_, receipt) = learner.section_founding(&mut states, &parts, None, &mut HostPass::default(), &mut directions).expect("section");
            assert_eq!(receipt.foundings.iter().map(key).collect::<Vec<_>>(), decided.iter().map(key).collect::<Vec<_>>(), "section {k}");
            let mut expected = before.clone();
            expected.turned(&read, if receipt.admitted { &receipt.foundings } else { &[] }).expect("turned");
            assert_eq!(directions, expected, "section {k}");
            turned_sign += opened.levels.iter().flatten().zip(read.levels.iter().flatten()).filter(|(a, b)| a.score.signum() * b.score.signum() < 0).count();
        }
        assert!(deposited > 0, "no section's step deposited");
        assert!(turned_sign > 0, "the step turned no pair's score");
        eprintln!("SPLIT_STALE deposited={deposited} turned_sign={turned_sign}");
    }

    /// Acceptance 3: no news, no founding: a pair whose score is zero founds nothing at any price,
    /// and a direction the passage does not reach is kept.
    #[test]
    fn a_pair_no_news_reaches_founds_nothing_and_keeps_its_direction() {
        let quiet = PairRead { score: 0, squares: 0, turned: vec![0; 4] };
        assert_eq!(founded(&quiet, 4, 1).expect("tested"), None);
        let (paired, mut directions) = taught().paired().expect("paired");
        let before = directions.clone();
        let read = SplitRead { levels: directions.levels.iter().map(|l| l.iter().map(|_| quiet.clone()).collect()).collect() };
        directions.turned(&read, &[]).expect("turned");
        assert_eq!(directions, before);
        assert!(paired.foundings(&directions, &read).expect("tested").is_empty());
        // A score of 4 bits against squares of 4 founds alone (a fit of 1.30 nats against an own
        // price of 0.39); among two dormant pairs its address adds ln 4, and it is refused.
        let loud = PairRead { score: 4 << COVECTOR_BITS, squares: 4 << (2 * COVECTOR_BITS), turned: vec![0; 4] };
        let (theta, predicted, surplus) = founded(&loud, 4, 1).expect("tested").expect("founded");
        assert!(surplus > 0);
        assert!(theta < 0 && predicted < 0);
        assert_eq!(founded(&loud, 4, 2).expect("tested"), None, "the address raises the price");
    }

    /// Acceptance 4 (the host's reading): over a mixed passage, every certified founding lowers the
    /// section's code, and each founding carries its predicted change.
    #[test]
    fn a_certified_founding_lowers_the_code_it_was_predicted_to_lower() {
        let streams: Vec<Vec<usize>> = (0..4).map(|s| parity_passage(0x9e37_79b9 ^ (s as u32 + 1), 64 * 33 + 1)).collect();
        let section = |k: usize| -> Vec<&[usize]> { streams.iter().map(|p| &p[k * 64..k * 64 + 65]).collect() };
        let mut learner = TowerLearner::new(tiny_pair(true, false), 6);
        let mut states = vec![learner.tower.rest(); 4];
        for k in 0..8 {
            learner.section(&mut states, &section(k)).expect("section");
        }
        let (mut learner, mut directions) = learner.paired().expect("paired");
        let mut pass = HostPass::default();
        assert!(pass.forms_split());
        let (mut admitted, mut refused) = (0usize, 0usize);
        for k in 8..32 {
            let (_, receipt) = learner.section_founding(&mut states, &section(k), None, &mut pass, &mut directions).expect("section");
            if receipt.foundings.is_empty() {
                continue;
            }
            assert_eq!(receipt.foundings.len(), 1, "one founding a section");
            let f = &receipt.foundings[0];
            assert!(f.predicted < 0 && f.theta != 0 && f.surplus > 0);
            if receipt.admitted {
                admitted += 1;
                assert!(receipt.code_after < receipt.code_before);
                assert_eq!(receipt.code_after, receipt.remeasured.unwrap_or(receipt.reread));
            } else {
                refused += 1;
                assert_eq!(receipt.code_after, receipt.code_before);
            }
            eprintln!(
                "SPLIT_FOUNDING section={k} level={} pair={} predicted={} measured={} remeasured={:?} theta={} admitted={} dormant={}",
                f.level,
                f.pair,
                f.predicted,
                receipt.reread - receipt.code_before,
                receipt.remeasured.map(|c| c - receipt.code_before),
                f.theta,
                receipt.admitted,
                receipt.dormant
            );
        }
        eprintln!("SPLIT_FOUNDINGS admitted={admitted} refused={refused} dormant={}", directions.dormant());
    }
}
