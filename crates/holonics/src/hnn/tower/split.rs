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
//! θ̂ = −ln 2 · g / (τ + ln²2 · S),   s = sgn θ̂                  (the line the test reads)
//! W_a[o] ± ⟦ε v⟧,   W_b[o] ± s ⟦ε v⟧   ⇒   the face moves by c s ε² φ
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
//! One pair is proposed a section, the one with the largest surplus, and the test only proposes
//! it: the proposal is held ([`PairedContacts::pending`]) and certified on the next section, on
//! material it was not fit on: the same pair's test, read on that section's opening (the split read
//! its reverse forms), must pass again with the proposal's sign. While its founding is pending a
//! pair's direction is held, so the coordinate that opens is the one its scores read.
//!
//! The score is the code's slope along the split on the tower it was read on, and only there: the
//! section's step moves the drives both copies share along the same covectors, so the split is read
//! again on the tower the step left, and the test decides on what the step did not take
//! (agent-inferred, October 30; measured: decided on the opening read, 20 of the race's first 28
//! proposed foundings raised the code they were predicted to lower).
//!
//! Every pair deposits as one contact, dormant or founded ([`Tower::pair_entries`]): its drives'
//! covectors are summed and both copies take the sum, the old contact's covector, on the old
//! contact's moments, so they move together as its drives do; its return parts take their
//! covectors' mean (while dormant the two are equal: both parts read the same conduction), whose
//! step is read once, from the first part's moments, and split between the parts as the widening
//! split the column (Euclidean, the remainder on the first), so the column moves by the old
//! column's step. The widened learner is then the pair learner in a wider chart, up to the
//! reverse's grain (agent-inferred, October 30; measured: with each return part stepping on the old
//! column's covector whole, the column moved twice its step and the dormant control read 0.097 bits
//! a byte above the pair race at lap 0; tied, the control read 2.228 held-out at lap 0 against the
//! pair race's 2.229, on the RTX 4080 SUPER).
//!
//! A founding therefore frees one coordinate, its half-difference `ε` along the direction it was
//! founded on ([`FoundedSplit`]), in its drives' chart ([`Tower::part_split`]): copy `o`'s first
//! drive row is the pair's own `+ ⟦ε v⟧` and its second `+ s ⟦ε v⟧`, the copy's the negatives, so
//! the pair's face carries `c s ε² φ` beside the contact the pair still learns as. The coordinate
//! opens at one step of that chart (the step a moment of ratio one takes at the learner's rate),
//! carried and released by the step of the section that certified it, and then descends as a drive
//! entry does: its covector `∂ℓ/∂ε` is read from the copies' own drive covectors before they are
//! tied ([`PairedContacts::split_covectors`]), its moments open on its first covector, and its step
//! is the drives' deposit step, halved with the section's. At the tied pair `ε = 0` is a saddle of
//! the code (`∂ℓ/∂ε = 2 s ε g`), which is why the test, not the covector, opens it; past the opening
//! the covector grows it while the score keeps the sign the tests read and returns it toward zero
//! when the score turns.
//!
//! [agent-inferred, October 30] The coordinate is not deposited at the test's `θ̂`. Measured on the
//! RTX 4080 SUPER, a founding deposited at `θ̂` (nearly its section's own Newton step, `ln²2 · S`
//! far above `τ`) and certified by its reread code falling past its price stalled the step at lap
//! 0 both ways it was carried: with the founded copies learning on their own (each on its own
//! covector, its drives' moments re-lifted to `m/2`, `v/4`) the certificate halved every
//! section's step about 4.3 times; held at `θ̂`, the pair still one contact, about 3.3 times, where
//! the dormant control halved 211 times in 224 sections (821 in the held race, which stopped there
//! at 3.626 bits a byte against the control's 2.777). The first foundings, at sections 3 to 10,
//! certified falls of 1,773 to 11,157 bits on their sections; by section 32 the founded drives'
//! largest entries at levels 2 and 3 were five to six times the control's (pair drive 8,220,268 and
//! 6,976,131 against 1,363,235 and 1,185,143 on `2^(−24)`), and through section 224 those levels'
//! reads and pushes did not grow (level 3's largest read 2,243,958 to 2,256,606) while the
//! control's more than doubled. A coordinate fit by one section's Newton step lays a quadratic
//! feature whose curvature the other entries' normalized steps were never scaled to; opened at
//! one step, it grows at the rate every other entry learns at.
use super::*;
use crate::ratio::Rat;
use num_bigint::BigInt;
use num_traits::ToPrimitive;

/// How a section reads its learner's contacts: unpaired; paired with every pair dormant, the copies
/// depositing as one contact and nothing founding (the split race's control); or paired and
/// founding on the carried directions.
pub(super) enum Pairs<'a> {
    Unpaired,
    Dormant,
    Founding(&'a mut PairedContacts),
}

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
/// once the pair is founded; each founded pair's coordinate ([`FoundedSplit`]); and the founding
/// the last section proposed, held for the next section's certificate (the module header). The text
/// carries the directions and the founded coordinates: a run releases a pending founding at each
/// pass's end, before its directions rest, so a run continued from them is the run that went on.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairedContacts {
    pub levels: Vec<Vec<Option<Vec<i32>>>>,
    pub founded: Vec<FoundedSplit>,
    pub pending: Option<Founding>,
}

/// [definition; agent-inferred, October 30] **A founded pair's coordinate** (the module header):
/// pair `pair` of level `level`, the direction `v` it was founded on (held, on `2^(−16)`), the sign
/// `s` of the `θ̂` its two tests read, its half-difference `ε` on the drives' material grain
/// `2^(−24)` (copy `o`'s first drive row is the pair's own row `+ ⟦ε v⟧`, its second `+ s ⟦ε v⟧`,
/// copy `o + f/2`'s the negatives, `⟦·⟧` released to the row's grain), and `ε`'s moments on the
/// drives' step grain, opened on its first covector.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoundedSplit {
    pub level: usize,
    pub pair: usize,
    pub direction: Vec<i32>,
    pub sign: i32,
    pub epsilon: i128,
    pub first: i128,
    pub second: i128,
    pub opened: bool,
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

/// A founding the test proposed, before its certificate: the level and pair, `θ̂` on `2^(−48)`,
/// the predicted change of the code of the section it was read on, in bits on `2^(−20)`
/// (`−ln 2 · g²/(2(τ + ln²2 S))`, negative), the test's surplus (fit less price, nats on
/// `2^(−20)`), and the read it was decided on.
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

/// A founding section's receipt, codes on `2^(−20)` bits: the founding the section before proposed
/// and this one certified, if any; the section's opening code; the same pair's test read on this
/// section's opening, where it passed with the proposal's sign; whether its coordinate opened (the
/// test passed and the section's step, which carries the opening, deposited); the founding this
/// section proposes, held for the next; the dormant pairs it leaves; and the founded coordinates'
/// largest `|ε|` on `2^(−24)`.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct FoundingReceipt {
    pub certified: Option<Founding>,
    pub code_before: i64,
    pub confirmed: Option<Founding>,
    pub admitted: bool,
    pub proposed: Option<Founding>,
    pub dormant: usize,
    pub largest: i128,
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
        Ok(Self { levels, founded: Vec::new(), pending: None })
    }

    /// The pairs still dormant.
    pub fn dormant(&self) -> usize {
        self.levels.iter().flatten().filter(|v| v.is_some()).count()
    }

    /// The directions as text: `paired LEVELS PAIRS WIDTH`, then one line a level, each pair `-`
    /// once founded or its entries joined by commas, then one line a founded coordinate,
    /// `founded LEVEL PAIR SIGN EPSILON FIRST SECOND OPENED` and its direction joined by commas.
    pub fn to_text(&self) -> String {
        let pairs = self.levels.first().map_or(0, |l| l.len());
        let width = self.levels.iter().flatten().flatten().chain(self.founded.iter().map(|f| &f.direction)).next().map_or(0, |v| v.len());
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
        for f in &self.founded {
            let direction: Vec<String> = f.direction.iter().map(|x| x.to_string()).collect();
            s.push_str(&format!("founded {} {} {} {} {} {} {} {}\n", f.level, f.pair, f.sign, f.epsilon, f.first, f.second, u8::from(f.opened), direction.join(",")));
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
        if lines.len() < levels + 1 {
            return refuse("the paired directions are one line a level");
        }
        let entry = |t: &str| t.parse::<i128>().map_err(|_| TowerError::Refused("a founded coordinate's entry that is not an integer"));
        let founded = lines[levels + 1..]
            .iter()
            .map(|line| {
                let tokens: Vec<&str> = line.split(' ').collect();
                if tokens.len() != 9 || tokens[0] != "founded" {
                    return refuse("a line after the levels that is not a founded coordinate");
                }
                let direction = tokens[8].split(',').map(|x| x.parse::<i32>().map_err(|_| TowerError::Refused("a direction entry that is not an integer"))).collect::<Result<Vec<_>>>()?;
                if direction.len() != width {
                    return refuse("a direction of the wrong width");
                }
                let sign = match tokens[3] {
                    "1" => 1,
                    "-1" => -1,
                    _ => return refuse("a founded coordinate's sign that is not one"),
                };
                let opened = match tokens[7] {
                    "0" => false,
                    "1" => true,
                    _ => return refuse("a founded coordinate's opening that is not a bit"),
                };
                Ok(FoundedSplit { level: count(tokens[1])?, pair: count(tokens[2])?, direction, sign, epsilon: entry(tokens[4])?, first: entry(tokens[5])?, second: entry(tokens[6])?, opened })
            })
            .collect::<Result<Vec<_>>>()?;
        let levels = lines[1..levels + 1]
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
        Ok(Self { levels, founded, pending: None })
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
        if self.pending.as_ref().is_some_and(|f| self.levels.get(f.level).and_then(|l| l.get(f.pair)).is_none_or(|v| v.is_none())) {
            return refuse("a pending founding of a pair that is not dormant");
        }
        // Each founded pair carries exactly one coordinate, and each coordinate is a founded pair's.
        let mut carried: Vec<Vec<bool>> = self.levels.iter().map(|l| l.iter().map(|v| v.is_some()).collect()).collect();
        for f in &self.founded {
            let slot = carried.get_mut(f.level).and_then(|l| l.get_mut(f.pair)).ok_or(TowerError::Refused("a founded coordinate of another tower"))?;
            if *slot || f.direction.len() != d.width || f.sign.abs() != 1 {
                return refuse("a founded coordinate of a pair that is dormant or founded twice");
            }
            *slot = true;
        }
        if carried.iter().flatten().any(|c| !c) {
            return refuse("a founded pair without its coordinate");
        }
        Ok(())
    }

    /// [definition; agent-inferred, October 30] **Each founded coordinate's covector** (the module
    /// header), `∂ℓ/∂ε = v·(G_a[o] − G_a[o+f/2]) + s v·(G_b[o] − G_b[o+f/2])` on the material
    /// covector's grain `2^(−40)`, read from the reverse's covector `g` before its copies are tied:
    /// the chart moves copy `o`'s drive rows by `+v`, `+s v` and its copy's by `−v`, `−s v`.
    pub(super) fn split_covectors(&self, tower: &Tower, g: &[i128]) -> Result<Vec<i128>> {
        self.admits(tower)?;
        let (w, h) = (tower.declaration.width, tower.declaration.contacts / 2);
        Ok(self
            .founded
            .iter()
            .map(|f| {
                let lv = tower.layout.levels[f.level];
                let along = |start: usize| -> i128 {
                    let (a, b) = (start + f.pair * w, start + (f.pair + h) * w);
                    f.direction.iter().enumerate().map(|(j, &v)| v as i128 * (g[a + j] - g[b + j])).sum()
                };
                release(along(lv.contact) + f.sign as i128 * along(lv.pair), FACE_BITS)
            })
            .collect())
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

    /// The paired tower and, for each of its entries, the old entry it carries.
    fn paired_from(&self) -> Result<(Self, Vec<usize>)> {
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
        let mut from = vec![0usize; layout.len];
        let keep = |new: &mut [i32], from: &mut [usize], at: usize, to: usize, len: usize| {
            new[to..to + len].copy_from_slice(&self.theta[at..at + len]);
            for (i, slot) in from[to..to + len].iter_mut().enumerate() {
                *slot = at + i;
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
                            from[to + (c * f + e) * len + i] = at + e * len + i;
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
                        from[at] = o.ret + j * f + e;
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

    /// The splits at their tests' `θ̂` mapped onto the material (the module header): for each
    /// founding, the chart ([`Tower::part_split`]) from the tied pair to `ε = √|θ̂|`, `±⟦ε v⟧` on the
    /// pair's first drive rows and `±sgn(θ̂) ⟦ε v⟧` on its second, so the face moves by `c θ̂ φ`.
    pub fn found_splits(&self, paired: &PairedContacts, foundings: &[Founding]) -> Result<Self> {
        paired.admits(self)?;
        let mut tower = self.clone();
        for founding in foundings {
            let v = paired.levels.get(founding.level).and_then(|l| l.get(founding.pair)).and_then(|v| v.as_ref()).ok_or(TowerError::Refused("a founding of a pair that is not dormant"))?;
            let epsilon = founding.theta.unsigned_abs().isqrt() as i128;
            tower.part_split(founding.level, founding.pair, v, founding.theta.signum() as i32, 0, epsilon)?;
        }
        Ok(tower)
    }

    /// [definition; agent-inferred, October 30] **The split's chart** (the module header): pair
    /// `pair` of level `level` moved from half-difference `from` to `to` along `v` with sign `s`:
    /// each first drive entry's copy `o` takes `⟦to v⟧ − ⟦from v⟧` (each second drive entry's that
    /// times `s`) and its copy `o + f/2` the negative, `⟦·⟧` released from the direction's grain to
    /// the row's. The tied steps move both copies alike, so a pair opened from its tied copies
    /// carries exactly `±⟦ε v⟧` and `±s ⟦ε v⟧` at every `ε` its chart has moved it to.
    pub(super) fn part_split(&mut self, level: usize, pair: usize, v: &[i32], sign: i32, from: i128, to: i128) -> Result<()> {
        let (w, h) = (self.declaration.width, self.declaration.contacts / 2);
        let lv = self.layout.levels[level];
        for (j, &x) in v.iter().enumerate() {
            let delta = release(to * x as i128, FACE_BITS) - release(from * x as i128, FACE_BITS);
            for (family, signed) in [(lv.contact, delta), (lv.pair, sign as i128 * delta)] {
                for (copy, by) in [(pair, signed), (pair + h, -signed)] {
                    let at = family + copy * w + j;
                    self.theta[at] = fit32(self.theta[at] as i128 + by, "a founded drive outgrew its 32-bit carrier")?;
                }
            }
        }
        Ok(())
    }

    /// [definition; agent-inferred, October 30] **The pairs' entries** (the module header): for
    /// each pair `e` of each level (contacts `e` and `e + f/2`), each drive entry's two copies (both
    /// drives' rows and biases), then each return row's two parts. Refused on a tower that is not
    /// paired pair contacts.
    pub(super) fn pair_entries(&self) -> Result<(Vec<(usize, usize)>, Vec<(usize, usize)>)> {
        let d = &self.declaration;
        if d.contact != ContactLaw::Pair || d.contacts % 2 != 0 {
            return refuse("paired contacts are an even count of pair contacts");
        }
        let (w, f, h) = (d.width, d.contacts, d.contacts / 2);
        let (mut drives, mut returns) = (Vec::new(), Vec::new());
        for lv in &self.layout.levels {
            for e in 0..h {
                for (start, len) in [(lv.contact, w), (lv.contact_bias, 1), (lv.pair, w), (lv.pair_bias, 1)] {
                    drives.extend((0..len).map(|i| (start + e * len + i, start + (e + h) * len + i)));
                }
                returns.extend((0..w).map(|j| (lv.ret + j * f + e, lv.ret + j * f + e + h)));
            }
        }
        Ok((drives, returns))
    }
}

impl TowerLearner {
    /// [definition; agent-inferred, October 30] **The learner with its contacts paired**
    /// ([`Tower::paired`]) and every pair dormant: every entry carries its old entry's moments,
    /// since a dormant pair deposits as one contact (the module header): its drives' copies take the
    /// old covector summed, and each return part the old covector whole. Refused under a declared
    /// hold, whose ranges name the old material.
    pub fn paired(&self) -> Result<(Self, PairedContacts)> {
        if !self.held.is_empty() {
            return refuse("a held learner's pairing: its holds name the old material");
        }
        let (tower, from) = self.tower.paired_from()?;
        let first = from.iter().map(|&i| self.first[i]).collect();
        let second = from.iter().map(|&i| self.second[i]).collect();
        let paired = PairedContacts::opened(&tower)?;
        Ok((Self { tower, first, second, opened: self.opened, rate_bits: self.rate_bits, swell: Vec::new(), held: Vec::new() }, paired))
    }

    /// The section's proposal decided (the module header): of the pairs the test admits, the one
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
        // `K` already charged for the choice): the test reads one coordinate's line, while several
        // founded together share the face and their predictions do not add (measured: three
        // foundings predicted at −20.9 bits together raised the code by 1.4).
        // Ties go to the first level and pair.
        let best = out.iter().enumerate().max_by_key(|(i, f)| (f.surplus, std::cmp::Reverse(*i))).map(|(i, _)| i);
        Ok(best.map(|i| vec![out.swap_remove(i)]).unwrap_or_default())
    }
}

impl PairedContacts {
    /// Each dormant pair's direction turned by its read (`v ← M v/‖M v‖`; kept where the passage
    /// did not reach it), except the pending founding's, which is held for its certificate.
    pub fn turned(&mut self, read: &SplitRead) -> Result<()> {
        let held = self.pending.as_ref().map(|f| (f.level, f.pair));
        for (l, (pairs, reads)) in self.levels.iter_mut().zip(&read.levels).enumerate() {
            for (e, (direction, r)) in pairs.iter_mut().zip(reads).enumerate() {
                if direction.is_some() && held != Some((l, e)) {
                    if let Some(v) = unit(&r.turned)? {
                        *direction = Some(v);
                    }
                }
            }
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
    /// every copy carries its old entry's moments; the rectifier and every part whose lift is owed
    /// are refused.
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
                    assert_eq!(paired.first[to], learner.first[at]);
                    assert_eq!(paired.second[to], learner.second[at]);
                }
                let at = o.ret + i * f + e;
                let parts: i32 = (0..2).map(|c| paired.tower.theta[n.ret + i * 2 * f + c * f + e]).sum();
                assert_eq!(parts, learner.tower.theta[at]);
                for c in 0..2 {
                    assert_eq!(paired.first[n.ret + i * 2 * f + c * f + e], learner.first[at]);
                    assert_eq!(paired.second[n.ret + i * 2 * f + c * f + e], learner.second[at]);
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
            directions.turned(&r).expect("turned");
        }
        let at = read(&directions);
        let mut once = directions.clone();
        once.turned(&at).expect("turned");
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
                read(&PairedContacts { levels: opened.levels.iter().map(|l| l.iter().map(|_| Some(unit.clone())).collect()).collect(), founded: Vec::new(), pending: None })
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

    /// A founded coordinate's covector is the code's slope along it: on each pair of the ungated,
    /// gated and turned tiny towers opened at `ε = 2^(−8)` (either sign), the code read at
    /// `ε ± 2^(−10)` parts by `2 · 2^(−10)` times the covector read from the copies' own drive
    /// covectors, within a quarter of it and `2^(−14)` bits; and the opened tower's directions rest
    /// and return as text.
    #[test]
    fn the_founded_coordinates_covector_is_the_codes_slope_along_it() {
        let (at, by) = (1i128 << (MATERIAL_BITS - 8), 1i128 << (MATERIAL_BITS - 10));
        for (gated, turned) in [(false, false), (true, false), (true, true)] {
            let (paired, directions) = {
                let mut learner = TowerLearner::new(tiny_pair(gated, turned), 6);
                let mut states = vec![learner.tower.rest()];
                for k in 0..4 {
                    learner.section(&mut states, &[&PASSAGE[k * 9..k * 9 + 10]]).expect("section");
                }
                learner.paired().expect("paired")
            };
            for (l, pairs) in directions.levels.iter().enumerate() {
                for (e, v) in pairs.iter().enumerate() {
                    let v = v.clone().expect("dormant");
                    for sign in [1, -1] {
                        let mut founded = directions.clone();
                        founded.levels[l][e] = None;
                        founded.founded.push(FoundedSplit { level: l, pair: e, direction: v.clone(), sign, epsilon: at, first: 0, second: 0, opened: false });
                        let mut tower = paired.tower.clone();
                        tower.part_split(l, e, &v, sign, 0, at).expect("opened");
                        let opening = tower.rest();
                        let mut end = opening.clone();
                        let cells = tower.forward(&mut end, &PASSAGE, &tower.reaches()).expect("forward");
                        let (g, _) = tower.reverse_split(&opening, &cells, &PASSAGE, None, &founded).expect("split");
                        let covector = founded.split_covectors(&tower, &g).expect("covector")[0];
                        let code_at = |epsilon: i128| -> i64 {
                            let mut moved = paired.tower.clone();
                            moved.part_split(l, e, &v, sign, 0, epsilon).expect("moved");
                            moved.read(&mut moved.rest(), &PASSAGE).expect("read")
                        };
                        let moved = code_at(at + by) - code_at(at - by);
                        // The covector on 2^(−40) bits a unit of ε, the move on 2^(−24): bits on 2^(−20).
                        let slope = release(covector * 2 * by, COVECTOR_BITS + FACE_BITS + MATERIAL_BITS - READ_BITS);
                        let off = (moved as i128 - slope).abs();
                        assert!(off <= slope.abs() / 4 + (1 << 6), "gated {gated} turned {turned} level {l} pair {e} sign {sign}: moved {moved} against {slope}");
                        founded.admits(&tower).expect("the coordinate is the tower's");
                        assert_eq!(PairedContacts::from_text(&founded.to_text()).expect("read"), founded);
                    }
                }
            }
        }
    }

    /// The parity passage's streams and a section of them.
    fn parity_streams(sections: usize) -> Vec<Vec<usize>> {
        (0..4).map(|s| parity_passage(0x9e37_79b9 ^ (s as u32 + 1), 64 * sections + 1)).collect()
    }

    fn parity_section(streams: &[Vec<usize>], k: usize) -> Vec<&[usize]> {
        streams.iter().map(|p| &p[k * 64..k * 64 + 65]).collect()
    }

    /// The founding is proposed on the tower the step left: a founding section's proposal and its
    /// directions' turn are those of the split read on that tower (with the pair retired whose
    /// coordinate the step opened), not on the opening's; the pending pair's direction is held; and
    /// the step moves the score (here it turns some pair's sign).
    #[test]
    fn the_founding_is_proposed_on_the_tower_the_step_left() {
        let streams = parity_streams(33);
        let (mut learner, mut directions, _, mut states) = paired_on_parity(&streams);
        let (mut deposited, mut turned_sign, mut proposed) = (0usize, 0usize, 0usize);
        let key = |f: &Founding| (f.level, f.pair, f.score, f.squares, f.predicted, f.surplus);
        for k in 8..32 {
            let parts = parity_section(&streams, k);
            let opening = states.clone();
            let (before, tower_before) = (directions.clone(), learner.tower.clone());
            let (receipt, founding) = learner.section_founding(&mut states, &parts, None, &mut HostPass::default(), &mut directions).expect("section");
            deposited += receipt.deposited as usize;
            assert_eq!(founding.certified, before.pending, "section {k}");
            // The directions the proposal reads: the pending founding taken, its pair retired if its
            // coordinate opened, and the founded coordinates as the step left them.
            let mut at_read = PairedContacts { pending: None, founded: directions.founded.clone(), ..before.clone() };
            let stepped_from = tower_before.clone();
            if let (true, Some(f)) = (founding.admitted, &founding.certified) {
                at_read.levels[f.level][f.pair] = None;
            }
            let read = split_of(&learner.tower, &opening, &parts, &at_read);
            let decided = learner.foundings(&at_read, &read).expect("decided");
            assert_eq!(founding.proposed.as_ref().map(key), decided.first().map(key), "section {k}");
            let mut expected = PairedContacts { pending: decided.into_iter().next(), ..at_read.clone() };
            expected.turned(&read).expect("turned");
            assert_eq!(directions, expected, "section {k}");
            if let Some(f) = &directions.pending {
                proposed += 1;
                assert_eq!(directions.levels[f.level][f.pair], at_read.levels[f.level][f.pair], "the pending pair's direction is held");
            }
            let opened = split_of(&stepped_from, &opening, &parts, &at_read);
            turned_sign += opened.levels.iter().flatten().zip(read.levels.iter().flatten()).filter(|(a, b)| a.score.signum() * b.score.signum() < 0).count();
        }
        assert!(deposited > 0, "no section's step deposited");
        assert!(proposed > 0, "no section proposed a founding");
        assert!(turned_sign > 0, "the step turned no pair's score");
        eprintln!("SPLIT_STALE deposited={deposited} proposed={proposed} turned_sign={turned_sign}");
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
        directions.turned(&read).expect("turned");
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

    /// The widened learner after a few sections of the parity passage, with its streams' states.
    fn paired_on_parity(streams: &[Vec<usize>]) -> (TowerLearner, PairedContacts, TowerLearner, Vec<TowerState>) {
        let mut learner = TowerLearner::new(tiny_pair(true, false), 6);
        let mut states = vec![learner.tower.rest(); 4];
        for k in 0..8 {
            learner.section(&mut states, &parity_section(streams, k)).expect("section");
        }
        let (paired, directions) = learner.paired().expect("paired");
        (paired, directions, learner, states)
    }

    /// Acceptance 4 (the host's reading): over a mixed passage, each founding is proposed on one
    /// section and certified on the next, which it was not fit on: the receipt confirms it exactly
    /// when its pair's test, read on that section's opening, passes with the proposal's sign; a
    /// confirmed founding whose section deposits opens its coordinate at one step of its chart,
    /// released by the section's halvings, and retires its pair, and otherwise its pair stays
    /// dormant; the training code read at each opening is the tower's own. Every pair deposits as
    /// one contact: its copies' moments stay equal, a dormant pair's drive copies stay equal, and a
    /// founded pair's carry exactly its coordinate's chart, `±⟦ε v⟧` and `±s ⟦ε v⟧`.
    #[test]
    fn a_founding_is_certified_on_the_section_after_the_one_it_was_fit_on() {
        let streams = parity_streams(33);
        let (mut learner, mut directions, _, mut states) = paired_on_parity(&streams);
        let mut pass = HostPass::default();
        assert!(pass.forms_split());
        let (mut admitted, mut confirmed, mut refused, mut proposed, mut descended) = (0usize, 0usize, 0usize, 0usize, 0usize);
        let (drives, returns) = learner.tower.pair_entries().expect("entries");
        let unit = deposit_over(1, 1, MATERIAL_BITS, learner.rate_bits);
        let (w, h) = (learner.tower.declaration.width, learner.tower.declaration.contacts / 2);
        let key = |f: &Founding| (f.level, f.pair, f.theta, f.predicted, f.surplus, f.score, f.squares);
        for k in 8..32 {
            let (tower_before, before) = (learner.tower.clone(), directions.clone());
            let opening = states.clone();
            let parts = parity_section(&streams, k);
            let (receipt, founding) = learner.section_founding(&mut states, &parts, None, &mut pass, &mut directions).expect("section");
            assert_eq!(founding.code_before, receipt.code_before);
            let own: i64 = opening.iter().zip(&parts).map(|(o, c)| tower_before.read(&mut o.clone(), c).expect("read")).sum();
            assert_eq!(receipt.code_before, own, "the opening's code is the tower's own");
            assert_eq!(founding.certified, before.pending, "section {k}");
            if let Some(p) = &founding.proposed {
                proposed += 1;
                assert!(p.predicted < 0 && p.theta != 0 && p.surplus > 0);
            }
            for &(x, y) in drives.iter().chain(&returns) {
                assert_eq!((learner.first[x], learner.second[x]), (learner.first[y], learner.second[y]), "section {k}: the copies' moments");
            }
            // Each pair's copies: equal while dormant, the coordinate's chart once founded.
            for (l, lv) in learner.tower.layout.levels.iter().enumerate() {
                for e in 0..h {
                    let coordinate = directions.founded.iter().find(|f| (f.level, f.pair) == (l, e));
                    assert_eq!(coordinate.is_some(), directions.levels[l][e].is_none(), "section {k}");
                    for (family, len, scaled) in [(lv.contact, w, 1i128), (lv.contact_bias, 1, 0), (lv.pair, w, 1), (lv.pair_bias, 1, 0)] {
                        for j in 0..len {
                            let part = (learner.tower.theta[family + e * len + j] - learner.tower.theta[family + (e + h) * len + j]) as i128;
                            let chart = coordinate.map_or(0, |f| {
                                let s = if family == lv.pair { f.sign as i128 } else { 1 };
                                2 * scaled * s * release(f.epsilon * f.direction[j] as i128, FACE_BITS)
                            });
                            assert_eq!(part, chart, "section {k} level {l} pair {e}");
                        }
                    }
                }
            }
            descended += directions.founded.iter().filter(|f| before.founded.iter().any(|b| (b.level, b.pair) == (f.level, f.pair) && b.epsilon != f.epsilon)).count();
            let Some(f) = &founding.certified else {
                assert_eq!(founding.confirmed, None);
                continue;
            };
            let read = split_of(&tower_before, &opening, &parts, &PairedContacts { pending: None, ..before.clone() });
            let r = &read.levels[f.level][f.pair];
            let test = founded(r, w, before.dormant()).expect("tested").filter(|t| t.0.signum() == f.theta.signum());
            let expected = test.map(|(theta, predicted, surplus)| Founding { level: f.level, pair: f.pair, theta, predicted, surplus, score: r.score, squares: r.squares });
            assert_eq!(founding.confirmed.as_ref().map(key), expected.as_ref().map(key), "section {k}");
            confirmed += usize::from(founding.confirmed.is_some());
            if founding.admitted {
                admitted += 1;
                assert!(founding.confirmed.is_some() && receipt.deposited, "section {k}: an opened coordinate was confirmed and carried by the step");
                assert_eq!(directions.levels[f.level][f.pair], None, "an opened coordinate retires its pair");
                let opened = directions.founded.last().expect("opened");
                assert_eq!((opened.level, opened.pair, opened.sign), (f.level, f.pair, f.theta.signum() as i32));
                assert_eq!(opened.epsilon, release(unit, receipt.halvings), "section {k}: the coordinate opens at one step");
            } else {
                refused += 1;
                assert!(directions.levels[f.level][f.pair].is_some(), "a refused founding leaves its pair dormant");
            }
            eprintln!(
                "SPLIT_FOUNDING section={k} level={} pair={} predicted={} confirmed={:?} admitted={} dormant={} largest={}",
                f.level,
                f.pair,
                f.predicted,
                founding.confirmed.as_ref().map(|c| c.predicted),
                founding.admitted,
                founding.dormant,
                founding.largest
            );
        }
        assert!(proposed > 0, "no section proposed a founding");
        assert!(admitted == 0 || descended > 0, "no opened coordinate descended");
        eprintln!("SPLIT_FOUNDINGS proposed={proposed} confirmed={confirmed} admitted={admitted} refused={refused} dormant={} descended={descended}", directions.dormant());
    }

    /// How far a widened learner's drives and summed return columns part from the pair learner's,
    /// in grains of their entries.
    fn parting(plain: &TowerLearner, widened: &TowerLearner) -> i32 {
        let (f, w, h) = (widened.tower.declaration.contacts, widened.tower.declaration.width, plain.tower.declaration.contacts);
        let mut worst = 0i32;
        for l in 0..plain.tower.declaration.levels {
            let (o, n) = (plain.tower.layout.levels[l], widened.tower.layout.levels[l]);
            for e in 0..h {
                for (old, new, len) in [(o.contact, n.contact, w), (o.contact_bias, n.contact_bias, 1), (o.pair, n.pair, w), (o.pair_bias, n.pair_bias, 1)] {
                    for i in 0..len {
                        worst = worst.max((plain.tower.theta[old + e * len + i] - widened.tower.theta[new + e * len + i]).abs());
                    }
                }
                for j in 0..w {
                    let column = widened.tower.theta[n.ret + j * f + e] + widened.tower.theta[n.ret + j * f + e + h];
                    worst = worst.max((plain.tower.theta[o.ret + j * h + e] - column).abs());
                }
            }
        }
        worst
    }

    /// The dormant control is the pair learner in a wider chart: over sections of the parity
    /// passage, each dormant pair's drive copies stay equal and their moments equal, the return
    /// parts' moments stay equal, and the widened learner's codes, drives and summed return columns
    /// part from the pair learner's only by the reverse's grain carried through the sections (the
    /// copies' covectors are released one by one, so their sum is the old covector to a grain a
    /// cell). The foil is the same widened learner whose copies deposit apart (each return part on
    /// the old column's covector whole): it parts from the pair learner many times further.
    #[test]
    fn the_dormant_control_learns_as_the_pair_learner_in_its_wider_chart() {
        let streams = parity_streams(20);
        let (paired, _, mut plain, states) = paired_on_parity(&streams);
        let (mut tied, mut apart) = (paired.clone(), paired);
        let (mut states_p, mut states_t, mut states_a) = (states.clone(), states.clone(), states);
        let (mut code_tied, mut code_apart, mut step) = (0i64, 0i64, 0i32);
        for k in 8..20 {
            let parts = parity_section(&streams, k);
            let before = plain.tower.theta.clone();
            let a = plain.section(&mut states_p, &parts).expect("pair section");
            let b = tied.section_dormant(&mut states_t, &parts, None, &mut HostPass::default()).expect("dormant section");
            let c = apart.section(&mut states_a, &parts).expect("foil section");
            step = step.max(before.iter().zip(&plain.tower.theta).map(|(x, y)| (x - y).abs()).max().unwrap_or(0));
            code_tied = code_tied.max((a.code_before - b.code_before).abs()).max((a.code_after - b.code_after).abs());
            code_apart = code_apart.max((a.code_before - c.code_before).abs()).max((a.code_after - c.code_after).abs());
            let (drives, returns) = tied.tower.pair_entries().expect("entries");
            for &(x, y) in drives.iter().chain(&returns) {
                assert_eq!((tied.first[x], tied.second[x]), (tied.first[y], tied.second[y]), "section {k}: the copies' moments");
            }
            for &(x, y) in &drives {
                assert_eq!(tied.tower.theta[x], tied.tower.theta[y], "section {k}: the drive copies");
            }
            eprintln!("SPLIT_DORMANT_SECTION k={k} code={}/{}/{} tied_parting={} apart_parting={}", a.code_after, b.code_after, c.code_after, parting(&plain, &tied), parting(&plain, &apart));
        }
        let (tied_parting, apart_parting) = (parting(&plain, &tied), parting(&plain, &apart));
        eprintln!("SPLIT_DORMANT largest_step={step} code_tied={code_tied} code_apart={code_apart} tied_parting={tied_parting} apart_parting={apart_parting}");
        assert!(code_tied * 8 < code_apart, "the tied codes part by {code_tied} grains, the foil's by {code_apart}");
        assert!(tied_parting * 8 < apart_parting, "the tied entries part by {tied_parting} grains, the foil's by {apart_parting}");
    }
}
