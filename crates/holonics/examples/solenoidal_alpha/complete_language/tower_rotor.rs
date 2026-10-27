//! [definition; agent-inferred with the mathematics thread, October 26] **The rotor's steps and turns
//! located by loop closure** ([`holonics::hnn::tower::Rotor`]; the records
//! `2026-10-26_THE_GENERATOR_AND_THE_MODULATOR_ARE_ONE_MOVE_AND_THE_PLACE_DECIDES_WHICH_SO_A_RING_COPRIME_TO_TEN_NEEDS_A_ROTOR.md`,
//! §11, and
//! `2026-10-26_THE_GENERATOR_IS_THE_MODULATOR_A_TURN_IS_TWO_REFLECTIONS_AND_THE_BASE_TURNS_COLLAPSES_OR_REFLECTS_EACH_RING.md`,
//! §5), **and the strands' laws and keys located the same way**
//! ([`holonics::hnn::tower::Strands`]; the record
//! `2026-10-26_THE_OPERANDS_ARE_HELD_BY_LOCATED_STRANDS_AND_THE_RESULT_IS_READ_ON_THE_RING_THAT_CLOSES.md`,
//! §3). The step `σ` and the turns `r` are integer keys: windings, which no descent reaches, since
//! any relaxed path between two keys passes through mixtures of modes. They are located the Bombe's
//! way, by the loops a menu of contacts closes.
//!
//! **The menu** names no operator. Every stretch `w x u y v z t` of the training text (three
//! numerals, maximal runs of digit bytes, with one byte between each two and one before and after)
//! is grouped by its context `(w, u, v, t)`. A group read under a hand `(s_x, s_y)` is a set of
//! loops `z − s_x x − s_y y`. The first group, largest first, whose closure under one hand carries
//! more than under every other (the product of its torsion primes at its best step, below) gives
//! the turns; every group is then read against them on each ring and gets the one hand under which
//! all its rows close, or none. The closing groups, each oriented by its hand, are the menu.
//!
//! [agent-inferred] A group closes only where its own rows carry the closure: at the located step
//! and the period, their rank over the rationals is the count of columns they touch, so the turns
//! closing them make the rank modulo each ring's primes fall below it. One calculation is `period`
//! rows over as many columns as its digits times the modes, and closes under a hand by the
//! arithmetic of one sum, which certifies no ring. The
//! only byte named is a digit (a numeral is still a run of named digit bytes); no value of a numeral
//! enters the rows, only which byte stands at which place.
//!
//! [agent-inferred] The hand is the one that carries the most, not the one that carries any: a group
//! of short numerals also closes modulo 2 under every hand, since the last digit's parity is a
//! character of period one in the tens and `−1 ≡ 1`.
//!
//! **The rows.** Read over a ring of `period` modes under a step `s` for every byte, a turn a byte
//! puts on mode `m` reaches mode `m − s·k` after the `k` bytes read after it. So the phase the
//! numeral leaves on mode `j` is `φ_j = Σ_i θ_((j + s·k_i) mod period)[b_i]`, with `θ_m[b]` the
//! unknown turn the byte `b` puts on mode `m` and `k_i` the bytes after the `i`-th. Each loop and
//! each mode `j` is one integer row, the signed sum of its numerals' phases, over the columns
//! `(m, b)`. The period is declared, and it is how far the rows look: they close for the characters
//! whose index returns after `period` steps, the moduli dividing `10^period − 1` (4:
//! `9999 = 3²·11·101`; 6: `999999 = 3³·7·11·13·37`), without naming one.
//!
//! **The step.** A turn modulo `p` closes every loop exactly where the rows' rank modulo `p` falls
//! below their rank over the rationals: the system's torsion, located as the ring closure locates it
//! (`tower_ring`'s `rational_rank`, `readable_primes`, `echelon_mod`). The step is the `s` whose
//! torsion carries the most: the largest product of its torsion primes, the smaller `s` of a tie
//! (`s` and `period − s` read the numeral backwards, a gauge pair). At period 4, mode `j` holding the
//! character `10^j` closes every loop for `s = 1` modulo every prime of `9999`; `s = 2` holds only
//! `99 = 3²·11` and `s = 0`, the digit sum, only `9`. Those are the readings this command reports,
//! not inputs to it: the torsion is the rows' own.
//!
//! **The turns.** At each torsion prime `p` of the step whose kernel modulo `p` is one line, that line
//! is the turn `θ` modulo `p`, unique up to a unit: the character's gauge `c`, fixed at `c = 1` by
//! making the line's first entry prime to `p` one (the mathematics thread: one character per prime
//! suffices, its orbit kept whole). The line is lifted to `p^e` while the rows close modulo `p^(e+1)`
//! with it (Hensel: `x + p^e y` with `A y ≡ −A x/p^e (mod p)`), at most to the valuation at `p` of
//! the certified minor, since a line closing modulo `p^e` makes `p^e` divide every full minor (by the
//! adjugate). The ring's width is the turn's period in the mode, the order of 10 modulo `p^e`
//! (9 → 1, 11 → 2, 101 → 4). A plural kernel names no single character and founds no ring; neither
//! does a lift that outgrows the rotor's 32-bit modulus, which is refused by name.
//!
//! **The units.** A unit is read whole: it steps a ring by `s` times the count of its located bytes,
//! modulo the ring's width, and turns the ring's mode `j` by `Σ_i θ_((j + s·k_i) mod period)[b_i]`
//! over its located bytes, `k_i` those after the `i`-th within it. Bytes the menu never meets keep
//! the opening. The rings take a level's first modes in ascending modulus and the modes past them
//! hold still. The first level steps and turns; the levels above hold still (the capture holds the
//! operand there). The equation at the consumer: read from rest, the turns' residue on mode `j` of a
//! ring after the numeral `n` is `c·10^j·n` modulo the ring's modulus, the character
//! `χ_(c·10^j)(n)`, for every numeral read through the units (`the_numeral_read_is_its_characters`).
//! Under the law `free` the same rings step and never turn: the generator alone, the foil that
//! isolates the turn.
//!
//! **The strands' rings.** Ring `L`, for `L = 1..period`, is the first closing group's closure at
//! period `L` and its best step: the located primes' lifted lines joined by the Chinese remainder
//! theorem, regauged so the first entry prime to the joined modulus is one; the multiplier `μ_L` is
//! the ratio of the turns of modes a step apart, refused unless one ratio holds for every mode and
//! byte. A strand reads mode 0: a digit `b` turns it by `θ_0[b]` after stepping it by `μ_L`.
//!
//! **The strands' laws and keys** ([agent-inferred]; the record's §3, its joint search amended
//! there). Every calculation of a closing group whose result has a ring (its length at most the
//! period) is read through a comparison `(a r_s + b r_t) mod q_L` of two strands on the ring of the
//! result's length: scored first by closure at the result's end, then by the digits it writes (the
//! tenth of the comparison's conjugate face against the result's next byte's turn on the largest
//! ring). From rest, what the strands hold after `x u y v` is a symbol: for each strand, the
//! coefficients of `x` held, `x` stepped through `y`, and `y`; a comparison reads the held strands'
//! sum, the moving strands' sum and the result's coefficient. A comparison that does not read the
//! result is dead: on ring `L` every stepped residue returns after `L` digits, so a held and a
//! stepped copy of one operand cancel at every result's end and close nothing of the calculation.
//!
//! 1. The laws (27), the comparison (12) and the keys of the two largest closing groups' `u` and
//!    `v` bytes are searched together (a byte only at `u` by its 54 or fewer classes from rest, any
//!    other by all 1,372 keys): searched one group at a time, the first group fixes the equals' sheet
//!    from rest, where keeping and setting it tie, and the second group's results are then read on
//!    the sheet its own `u` reversed.
//! 2. Each other closing group's new `u` and `v` bytes, everything else held.
//! 3. On the real stream, read from rest under the current keys, every byte at a `w`, `u`, `v` or
//!    `t` of a closing group in turn takes the best of all 1,372 keys, the others held, the bytes no
//!    earlier stage located first, until no key changes. A key moves only on a strictly better
//!    score.
//!
//! The first two stages take the best total score, then the fewest changes, then the first in
//! enumeration order; the third keeps the current key on a tie. The next-digit criterion selects
//! among arrangements; it writes nothing.
//!
//! `locate-strands TRAIN TRAIN_SHA PERIOD` reports the locator's lines alone.
//!
//! `found-unit-rotor-tower UNITS UNITS_SHA TRAIN TRAIN_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS
//! RATE_BITS PERIOD LAW OUT` founds the pumped pair-contact tower exactly as
//! `train-unit-pair-pumped-tower` founds it, joins the located rotor (`LAW` is `modulated` or
//! `free`; `strands` and `strands-still` are `modulated` with the located strands joined past the
//! rotor's rings, the second with every key the identity), and writes the rested learner
//! (create-new) for that command's `FROM`.
use super::tower_ring::{echelon_mod, rational_rank, readable_primes};
use super::tower_train::{count, positive};
use super::*;
use holonics::hnn::tower::{ContactLaw, Rotor, RotorRing, Sheet, StrandKey, StrandLaw, StrandRing, Strands, Tower, TowerDeclaration, TowerLearner, TurnLadder};
use holonics::hnn::units::Units;
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use rayon::prelude::*;
use std::collections::BTreeMap;
use std::sync::OnceLock;

/// A loop: three numerals, each with its sign, closing where their signed characters sum to zero.
type Loop<'a> = [(&'a [u8], i128); 3];

/// A stretch `w x u y v z t` of the text: three numerals (maximal runs of digit bytes) with one byte
/// between each two and one before and after them, each numeral as its first and past-last place.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Stretch {
    numerals: [(usize, usize); 3],
}

impl Stretch {
    /// Its context `(w, u, v, t)`.
    fn context(&self, text: &[u8]) -> [u8; 4] {
        let [x, y, z] = self.numerals;
        [text[x.0 - 1], text[x.1], text[y.1], text[z.1]]
    }

    fn numeral<'a>(&self, text: &'a [u8], i: usize) -> &'a [u8] {
        let (a, b) = self.numerals[i];
        &text[a..b]
    }
}

/// Every stretch of the text, in order.
fn stretches_of(text: &[u8]) -> Vec<Stretch> {
    let mut runs = Vec::new();
    let mut i = 0;
    while i < text.len() {
        let start = i;
        while i < text.len() && text[i].is_ascii_digit() {
            i += 1;
        }
        if i > start {
            runs.push((start, i));
        } else {
            i += 1;
        }
    }
    runs.windows(3)
        .filter(|r| r[0].0 >= 1 && r[1].0 == r[0].1 + 1 && r[2].0 == r[1].1 + 1 && r[2].1 < text.len())
        .map(|r| Stretch { numerals: [r[0], r[1], r[2]] })
        .collect()
}

/// The stretches grouped by context, the largest group first, then ascending context.
fn groups_of(text: &[u8], stretches: &[Stretch]) -> Vec<([u8; 4], Vec<Stretch>)> {
    let mut groups: BTreeMap<[u8; 4], Vec<Stretch>> = BTreeMap::new();
    for s in stretches {
        groups.entry(s.context(text)).or_default().push(*s);
    }
    let mut groups: Vec<([u8; 4], Vec<Stretch>)> = groups.into_iter().collect();
    groups.sort_by(|a, b| b.1.len().cmp(&a.1.len()).then(a.0.cmp(&b.0)));
    groups
}

/// The four hands `(s_x, s_y)` of `s_x x + s_y y − z ≡ 0`.
const HANDS: [[i128; 2]; 4] = [[1, 1], [1, -1], [-1, 1], [-1, -1]];

/// A group's stretches as loops under a hand: `z − s_x x − s_y y`.
fn loops_of<'a>(text: &'a [u8], stretches: &[Stretch], hand: [i128; 2]) -> Vec<Loop<'a>> {
    stretches.iter().map(|s| [(s.numeral(text, 2), 1), (s.numeral(text, 0), -hand[0]), (s.numeral(text, 1), -hand[1])]).collect()
}

/// The bytes the loops' numerals hold, ascending: the menu's located bytes.
fn bytes_of(loops: &[Loop]) -> Vec<u8> {
    let mut bytes: Vec<u8> = loops.iter().flatten().flat_map(|(n, _)| n.iter().copied()).collect();
    bytes.sort_unstable();
    bytes.dedup();
    bytes
}

/// The closure rows under the step `s` over a ring of `period` modes, one a loop and a final mode,
/// over the columns `(m, b)` (`m · bytes.len()` plus the byte's place in `bytes`), deduplicated.
fn rows_of(loops: &[Loop], bytes: &[u8], s: usize, period: usize) -> Vec<Vec<i128>> {
    let width = bytes.len();
    let mut rows: Vec<Vec<i128>> = Vec::with_capacity(loops.len() * period);
    for numerals in loops {
        for j in 0..period {
            let mut row = vec![0i128; period * width];
            for &(numeral, sign) in numerals {
                for (i, b) in numeral.iter().enumerate() {
                    let after = numeral.len() - 1 - i;
                    let m = (j + s * after) % period;
                    row[m * width + bytes.binary_search(b).expect("a located byte")] += sign;
                }
            }
            rows.push(row);
        }
    }
    rows.sort_unstable();
    rows.dedup();
    rows
}

/// One step's closure: the rows' rank over the rationals, its certified minor, and the primes at
/// which the rank falls, each with its fall.
struct Closure {
    rows: usize,
    rank: usize,
    minor: BigInt,
    torsion: Vec<(i128, usize)>,
}

fn closure(rows: &[Vec<i128>]) -> Closure {
    let (rank, minor, _) = rational_rank(rows);
    let torsion = readable_primes(&minor.abs())
        .into_iter()
        .filter_map(|p| {
            let held = echelon_mod(rows, p as u64, rank).pivots.len();
            (held < rank).then_some((p, rank - held))
        })
        .collect();
    Closure { rows: rows.len(), rank, minor, torsion }
}

/// The product of a closure's torsion primes, each once.
fn carried(c: &Closure) -> BigInt {
    c.torsion.iter().map(|&(p, _)| BigInt::from(p)).product()
}

/// The torsion as `p:fall,…`, or `none`.
fn torsion_text(c: &Closure) -> String {
    let torsion: Vec<String> = c.torsion.iter().map(|(p, fall)| format!("{p}:{fall}")).collect();
    if torsion.is_empty() { "none".to_string() } else { torsion.join(",") }
}

/// The step whose closure carries the most at `period`, the smaller of a tie, with its rows,
/// closure and carried product; `each` sees every step's closure.
struct Step {
    s: usize,
    carried: BigInt,
    rows: Vec<Vec<i128>>,
    closure: Closure,
}

fn best_step(loops: &[Loop], bytes: &[u8], period: usize, mut each: impl FnMut(usize, &Closure, &BigInt)) -> Step {
    let mut best: Option<Step> = None;
    for s in 0..period {
        let rows = rows_of(loops, bytes, s, period);
        let closure = closure(&rows);
        let carried = carried(&closure);
        each(s, &closure, &carried);
        if best.as_ref().is_none_or(|b| carried > b.carried) {
            best = Some(Step { s, carried, rows, closure });
        }
    }
    best.expect("a period of one step or more")
}

/// The kernel of `rows` modulo the prime `p`, when it is one line: its free column at one and each
/// pivot column at minus the free column's entry in its reduced row.
fn kernel_line(rows: &[Vec<i128>], p: u64, columns: usize) -> Option<Vec<i128>> {
    let e = echelon_mod(rows, p, columns);
    let free: Vec<usize> = (0..columns).filter(|c| e.pivots.binary_search(c).is_err()).collect();
    let [f] = free[..] else { return None };
    let mut x = vec![0i128; columns];
    x[f] = 1;
    for (&c, row) in e.pivots.iter().zip(&e.rows) {
        x[c] = ((p - row[f]) % p) as i128;
    }
    Some(x)
}

/// The line `x` modulo `p` lifted to `p^e`, `(x, p^e)`: one lift a step while the rows close
/// modulo `p·p^e` with it, `x + p^e y` with `A y ≡ −A x/p^e (mod p)` solved on the rows augmented
/// by `A x/p^e` (no solution where that column takes a pivot), at most to `p^bound` and no further
/// once the modulus has passed the rotor's carrier.
fn lifted(rows: &[Vec<i128>], line: &[i128], p: u64, bound: u32) -> (Vec<i128>, i128) {
    let columns = line.len();
    let wide = i128::from(p);
    let mut x = line.to_vec();
    let mut q = wide;
    for _ in 1..bound {
        if q > i128::from(u32::MAX) {
            break;
        }
        let augmented: Vec<Vec<i128>> = rows
            .iter()
            .map(|row| {
                let at: i128 = row.iter().zip(&x).map(|(a, v)| a * v).sum();
                debug_assert_eq!(at % q, 0, "the line closes modulo its lift");
                let mut r = row.clone();
                r.push((at / q).rem_euclid(wide));
                r
            })
            .collect();
        let e = echelon_mod(&augmented, p, columns + 1);
        if e.pivots.last() == Some(&columns) {
            break;
        }
        for (&c, row) in e.pivots.iter().zip(&e.rows) {
            x[c] += q * ((wide - row[columns] as i128) % wide);
        }
        q *= wide;
    }
    (x, q)
}

/// The exponent of the prime `p` in `x`.
fn valuation(x: &BigInt, p: u64) -> u32 {
    let (mut x, p) = (x.abs(), BigInt::from(p));
    let mut e = 0;
    while !x.is_zero() && (&x % &p).is_zero() {
        x /= &p;
        e += 1;
    }
    e
}

/// The greatest common divisor of `a` and `b`.
fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// `a⁻¹` modulo `q` for `a` prime to `q`, by Euclid's extended division.
fn inverse_mod(a: i128, q: i128) -> i128 {
    let (mut r0, mut r1, mut s0, mut s1) = (a.rem_euclid(q), q, 1i128, 0i128);
    while r1 != 0 {
        let k = r0 / r1;
        (r0, r1) = (r1, r0 - k * r1);
        (s0, s1) = (s1, s0 - k * s1);
    }
    debug_assert_eq!(r0, 1, "a unit modulo q");
    s0.rem_euclid(q)
}

/// A ring the closure located: the prime, the lifted modulus, the width (the turn's period in the
/// mode) and the turn `θ_m[b]` for every column `(m, b)`, `m < period`, at the gauge `c = 1`.
struct Located {
    prime: i128,
    modulus: u32,
    width: usize,
    theta: Vec<u32>,
}

/// The rings a step's closure locates, one for each torsion prime, in the closure's order: the
/// located ring, or why none is founded there.
fn located(rows: &[Vec<i128>], c: &Closure, bytes: usize, period: usize) -> Vec<(i128, usize, std::result::Result<Located, &'static str>)> {
    let columns = period * bytes;
    c.torsion
        .iter()
        .map(|&(p, fall)| {
            let ring: std::result::Result<Located, &'static str> = (|| {
                let line = kernel_line(rows, p as u64, columns).ok_or("plural_kernel")?;
                let (x, q) = lifted(rows, &line, p as u64, valuation(&c.minor, p as u64));
                let modulus = u32::try_from(q).map_err(|_| "outgrew_the_32_bit_modulus")?;
                let first = *x.iter().find(|&&v| v % p != 0).ok_or("a_line_without_a_unit")?;
                let unit = inverse_mod(first, q);
                let theta: Vec<u32> = x.iter().map(|&v| (v * unit).rem_euclid(q) as u32).collect();
                let mode = |m: usize| &theta[(m % period) * bytes..(m % period + 1) * bytes];
                let width = (1..=period).find(|&w| period % w == 0 && (0..period).all(|m| mode(m) == mode(m + w))).unwrap_or(period);
                Ok(Located { prime: p, modulus, width, theta })
            })();
            (p, fall, ring)
        })
        .collect()
}

/// The rotor of `rings` on `declaration`'s tower, each unit `u` of `pieces[u]` keyed at the first
/// level by its located bytes under the step `s`, the levels above still; `turned` false keeps every
/// turn zero (the law `free`).
fn founded_rotor(declaration: &TowerDeclaration, pieces: &[&[u8]], bytes: &[u8], s: usize, period: usize, rings: &[Located], turned: bool) -> std::result::Result<Rotor, String> {
    let nb = bytes.len();
    let moving: usize = rings.iter().map(|r| r.width).sum();
    let keyed = declaration.levels * declaration.alphabet;
    let mut steps = vec![0u32; keyed * rings.len()];
    let mut turns = vec![0u32; keyed * moving];
    for (u, piece) in pieces.iter().enumerate() {
        let located: Vec<usize> = piece.iter().filter_map(|b| bytes.binary_search(b).ok()).collect();
        let n = located.len();
        let mut first = 0;
        for (k, ring) in rings.iter().enumerate() {
            steps[u * rings.len() + k] = (s * n % ring.width) as u32;
            if turned {
                for j in 0..ring.width {
                    let r: u64 = located.iter().enumerate().map(|(i, &b)| u64::from(ring.theta[((j + s * (n - 1 - i)) % period) * nb + b])).sum();
                    turns[u * moving + first + j] = (r % u64::from(ring.modulus)) as u32;
                }
            }
            first += ring.width;
        }
    }
    Rotor::new(declaration, rings.iter().map(|r| RotorRing { width: r.width, modulus: r.modulus }).collect(), steps, turns).map_err(|e| e.to_string())
}

/// The bytes as text, each byte that is not a graphic character as `\xNN`.
fn shown(bytes: &[u8]) -> String {
    bytes.iter().map(|&b| if b.is_ascii_graphic() { (b as char).to_string() } else { format!("\\x{b:02x}") }).collect()
}

/// The first group, largest first, with one hand under which its closure carries more than under
/// every other, more than one: its place in `groups` and the hand's place in [`HANDS`]. Each group
/// read is reported.
fn first_closing(text: &[u8], groups: &[([u8; 4], Vec<Stretch>)], period: usize, report: bool) -> Option<(usize, usize)> {
    for (g, (context, stretches)) in groups.iter().enumerate() {
        let carried: Vec<BigInt> = HANDS
            .iter()
            .map(|&hand| {
                let loops = loops_of(text, stretches, hand);
                let step = best_step(&loops, &bytes_of(&loops), period, |_, _, _| {});
                if report {
                    println!(
                        "STRANDS_HAND context={} stretches={} hand={},{} step={} rank={} carried={} torsion={}",
                        shown(context),
                        stretches.len(),
                        hand[0],
                        hand[1],
                        step.s,
                        step.closure.rank,
                        step.carried,
                        torsion_text(&step.closure)
                    );
                }
                step.carried
            })
            .collect();
        let most = carried.iter().max().expect("four hands");
        if *most > BigInt::from(1) && carried.iter().filter(|c| *c == most).count() == 1 {
            return Some((g, carried.iter().position(|c| c == most).expect("the most")));
        }
    }
    None
}

/// A ring of the strands, located at period `length`: the step, the modulus, the multiplier of a
/// step, each located byte's turn at mode 0, and the primes joined, each with its lifted modulus.
#[derive(Clone, Debug, PartialEq, Eq)]
struct LocatedRing {
    length: usize,
    step: usize,
    modulus: u32,
    multiplier: u32,
    turns: Vec<u32>,
    primes: Vec<(i128, u32)>,
}

/// Ring `length` of the strands from the first closing group's loops: the located lines of its best
/// step's torsion at that period joined by the Chinese remainder theorem and regauged at one, and
/// the multiplier that takes every mode's turns to those a step later; or why none is founded.
fn strand_ring(loops: &[Loop], bytes: &[u8], length: usize) -> std::result::Result<LocatedRing, String> {
    let nb = bytes.len();
    let step = best_step(loops, bytes, length, |_, _, _| {});
    let mut primes = Vec::new();
    let (mut q, mut theta) = (1i128, vec![0i128; length * nb]);
    for (p, _, ring) in located(&step.rows, &step.closure, nb, length) {
        let Ok(ring) = ring else { continue };
        let m = i128::from(ring.modulus);
        let unit = inverse_mod(q % m, m);
        for (t, &b) in theta.iter_mut().zip(&ring.theta) {
            *t += q * ((i128::from(b) - *t) * unit).rem_euclid(m);
        }
        q *= m;
        if q > i128::from(u32::MAX) {
            return Err("outgrew_the_32_bit_modulus".into());
        }
        primes.push((p, ring.modulus));
    }
    if primes.is_empty() {
        return Err(format!("no_line_at_step_{}_torsion_{}", step.s, torsion_text(&step.closure)));
    }
    let first = theta.iter().position(|&t| gcd(t, q) == 1).ok_or("no_turn_is_a_unit")?;
    let unit = inverse_mod(theta[first], q);
    for t in &mut theta {
        *t = (*t * unit).rem_euclid(q);
    }
    let b = (0..nb).find(|&b| gcd(theta[b], q) == 1).ok_or("no_mode_0_turn_is_a_unit")?;
    let s = step.s % length;
    let multiplier = (theta[s * nb + b] * inverse_mod(theta[b], q)).rem_euclid(q);
    let one_multiple = (0..length).all(|m| (0..nb).all(|c| theta[((m + s) % length) * nb + c] == (multiplier * theta[m * nb + c]).rem_euclid(q)));
    if !one_multiple {
        return Err("the_turns_a_step_apart_are_not_one_multiple".into());
    }
    Ok(LocatedRing { length, step: step.s, modulus: q as u32, multiplier: multiplier as u32, turns: theta[..nb].iter().map(|&t| t as u32).collect(), primes })
}

/// The character of `numeral` on `ring`: read from zero, each byte steps by the multiplier and
/// turns by its located turn; none when a byte has no turn.
fn character(numeral: &[u8], ring: &LocatedRing, bytes: &[u8]) -> Option<u64> {
    let q = u64::from(ring.modulus);
    numeral.iter().try_fold(0u64, |r, b| bytes.binary_search(b).ok().map(|i| (r * u64::from(ring.multiplier) + u64::from(ring.turns[i])) % q))
}

/// The one hand under which every stretch of a group closes on every ring, or none.
fn hand_of(text: &[u8], stretches: &[Stretch], rings: &[LocatedRing], bytes: &[u8]) -> Option<usize> {
    let closes = |hand: [i128; 2]| {
        stretches.iter().all(|s| {
            rings.iter().all(|ring| {
                let q = i128::from(ring.modulus);
                let read = |i: usize| character(s.numeral(text, i), ring, bytes).map(i128::from);
                matches!((read(0), read(1), read(2)), (Some(x), Some(y), Some(z)) if (hand[0] * x + hand[1] * y - z).rem_euclid(q) == 0)
            })
        })
    };
    let hands: Vec<usize> = (0..HANDS.len()).filter(|&h| closes(HANDS[h])).collect();
    match hands[..] {
        [h] => Some(h),
        _ => None,
    }
}

/// A group's rows under `hand` at the located `step` and `period`: their rank over the rationals
/// and the count of columns they touch. The group's own rows carry its closure when the two are
/// equal (the rank modulo a ring's primes then falls below the rank, since the turns close them).
fn own_rank(text: &[u8], stretches: &[Stretch], hand: usize, bytes: &[u8], step: usize, period: usize) -> (usize, usize) {
    let loops = loops_of(text, stretches, HANDS[hand]);
    let rows = rows_of(&loops, bytes, step, period);
    let touched = (0..period * bytes.len()).filter(|&c| rows.iter().any(|r| r[c] != 0)).count();
    (rational_rank(&rows).0, touched)
}

/// A closing group: its context, stretches and hand.
struct Closing {
    context: [u8; 4],
    stretches: Vec<Stretch>,
    hand: usize,
}

/// A strand's coefficients of `x` held, `x` stepped through `y`, and `y`.
type Content = [i8; 3];

/// The strands' contents after `key`: each takes zero, a strand, or its reflection.
fn moved(key: StrandKey, c: [Content; 3]) -> [Content; 3] {
    key.source.map(|v| match v {
        0 => [0; 3],
        v if v > 0 => c[v as usize - 1],
        v => c[(-v) as usize - 1].map(|x| -x),
    })
}

/// What the strands hold after `x u y v` read from rest under `laws` and the keys at `u` and `v`,
/// and whether the sheet is reversed after `v`.
fn contents(laws: [StrandLaw; 3], at_u: StrandKey, at_v: StrandKey) -> ([Content; 3], bool) {
    let after_x = laws.map(|l| if l == StrandLaw::Turned { [1, 0, 0] } else { [0; 3] });
    let after_u = moved(at_u, after_x);
    let reversed = at_u.sheet.after(false);
    let after_y: [Content; 3] = std::array::from_fn(|s| match laws[s] {
        StrandLaw::Held => after_u[s],
        StrandLaw::Stepped => [0, after_u[s][0], 0],
        StrandLaw::Turned => [0, after_u[s][0], if reversed { -1 } else { 1 }],
    });
    (moved(at_v, after_y), at_v.sheet.after(reversed))
}

/// A comparison of two strands: `(a r_s + b r_t) mod q`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Comparison {
    strands: [usize; 2],
    signs: [i8; 2],
}

impl Comparison {
    /// The twelve: each pair of strands under each pair of signs.
    fn all() -> Vec<Self> {
        let mut out = Vec::new();
        for strands in [[0, 1], [0, 2], [1, 2]] {
            for signs in [[1, 1], [1, -1], [-1, 1], [-1, -1]] {
                out.push(Self { strands, signs });
            }
        }
        out
    }

    /// Its value on a ring of `q` with the three strands' residues `r`.
    fn value(&self, r: [u32; 3], q: u64) -> u64 {
        let signed = |sign: i8, v: u32| if sign > 0 { u64::from(v) % q } else { (q - u64::from(v) % q) % q };
        (signed(self.signs[0], r[self.strands[0]]) + signed(self.signs[1], r[self.strands[1]])) % q
    }
}

/// The digit a comparison `c` on a ring of `q` writes: the tenth of its conjugate face.
fn tenth(c: u64, q: u64) -> u64 {
    10 * ((q - c) % q) / q
}

/// What a comparison reads at a calculation after `x u y v`: the held strands' signed sum, the
/// moving strands' signed sum, and the result's coefficient (each coefficient within `−2..=2`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Symbol {
    held: Content,
    moving: Content,
    result: i8,
}

/// The count of symbols: seven coefficients of five values each.
const SYMBOLS: usize = 5usize.pow(7);

impl Symbol {
    fn of(laws: [StrandLaw; 3], comparison: Comparison, contents: [Content; 3], reversed: bool) -> Self {
        let (mut held, mut moving, mut result) = ([0i8; 3], [0i8; 3], 0i8);
        for (s, sign) in comparison.strands.into_iter().zip(comparison.signs) {
            let part = if laws[s] == StrandLaw::Held { &mut held } else { &mut moving };
            for (p, c) in part.iter_mut().zip(contents[s]) {
                *p += sign * c;
            }
            if laws[s] == StrandLaw::Turned {
                result += sign;
            }
        }
        Self { held, moving, result: if reversed { -result } else { result } }
    }

    fn index(&self) -> usize {
        self.held.iter().chain(&self.moving).chain(std::iter::once(&self.result)).fold(0, |a, &v| a * 5 + (v + 2) as usize)
    }

    /// Whether it closes every calculation of `hand` by its symbols alone.
    fn closes(&self, hand: [i128; 2]) -> bool {
        let s: [i128; 3] = std::array::from_fn(|i| i128::from(self.held[i]) + i128::from(self.moving[i]));
        let p = i128::from(self.result);
        p != 0 && s[1] == 0 && s[0] + p * hand[0] == 0 && s[2] + p * hand[1] == 0
    }
}

/// A calculation the strands are read on: its group, its ring (that of its result's length), the
/// characters there of `x`, `x` stepped through `y` and `y`, the result's prefixes' characters and
/// the step's powers along it (`0..=L`), the digits the result writes (each byte's turn on the
/// largest ring), and its stretch.
struct Row {
    group: usize,
    ring: usize,
    x: u64,
    stepped: u64,
    y: u64,
    prefixes: Vec<u64>,
    powers: Vec<u64>,
    tenths: Vec<u64>,
    stretch: Stretch,
}

/// The closing groups' calculations whose result has a ring, in group order, and the count of
/// those without (longer than every ring, or holding a byte with no turn).
fn rows_on(text: &[u8], closing: &[Closing], rings: &[LocatedRing], bytes: &[u8]) -> (Vec<Row>, Vec<usize>) {
    let largest = rings.last().expect("a ring");
    let mut rows = Vec::new();
    let mut beyond = vec![0usize; closing.len()];
    for (group, c) in closing.iter().enumerate() {
        for &stretch in &c.stretches {
            let z = stretch.numeral(text, 2);
            let row = rings.iter().position(|r| r.length == z.len()).and_then(|ring| {
                let r = &rings[ring];
                let q = u64::from(r.modulus);
                let (x, y) = (character(stretch.numeral(text, 0), r, bytes)?, character(stretch.numeral(text, 1), r, bytes)?);
                let mu = u64::from(r.multiplier);
                let stepped = (0..stretch.numeral(text, 1).len()).fold(x, |v, _| v * mu % q);
                let prefixes: Vec<u64> = (0..=z.len()).map(|k| character(&z[..k], r, bytes)).collect::<Option<_>>()?;
                let powers: Vec<u64> = std::iter::successors(Some(1 % q), |v| Some(v * mu % q)).take(z.len() + 1).collect();
                let tenths: Vec<u64> = z.iter().map(|b| bytes.binary_search(b).ok().map(|i| u64::from(largest.turns[i]))).collect::<Option<_>>()?;
                Some(Row { group, ring, x, stepped, y, prefixes, powers, tenths, stretch })
            });
            match row {
                Some(row) => rows.push(row),
                None => beyond[group] += 1,
            }
        }
    }
    (rows, beyond)
}

/// A count of calculations closed and digits written right.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
struct Score {
    closed: usize,
    digits: usize,
}

impl std::ops::Add for Score {
    type Output = Self;
    fn add(self, o: Self) -> Self {
        Self { closed: self.closed + o.closed, digits: self.digits + o.digits }
    }
}

/// The score of a symbol over rows: on each row's ring, the comparison after `k` digits is
/// `H + μ^k M + P p_k`; its tenth against the next digit while `k < L`, and closure at `k = L`.
fn read(symbol: &Symbol, rows: &[&Row], rings: &[LocatedRing]) -> Score {
    let mut score = Score::default();
    for row in rows {
        let q = i128::from(rings[row.ring].modulus);
        let at = |c: Content| (i128::from(c[0]) * i128::from(row.x) + i128::from(c[1]) * i128::from(row.stepped) + i128::from(c[2]) * i128::from(row.y)).rem_euclid(q);
        let (h, m, p) = (at(symbol.held), at(symbol.moving), i128::from(symbol.result));
        let length = row.tenths.len();
        for k in 0..=length {
            let c = (h + i128::from(row.powers[k]) * m + p * i128::from(row.prefixes[k])).rem_euclid(q) as u64;
            if k < length {
                score.digits += usize::from(tenth(c, q as u64) == row.tenths[k]);
            } else {
                score.closed += usize::from(c == 0);
            }
        }
    }
    score
}

/// A group as the search reads it: its context, hand and rows.
struct Searched<'a> {
    context: [u8; 4],
    hand: [i128; 2],
    rows: Vec<&'a Row>,
}

/// The keys at a `u` read from rest under `laws`, one for each thing they do there (what each strand
/// takes, and the sheet): of each class, the key of fewest changes, the first of a tie; in the
/// order of [`StrandKey::all`].
fn classes_from_rest(laws: [StrandLaw; 3], all: &[StrandKey]) -> Vec<usize> {
    let after_x = laws.map(|l| if l == StrandLaw::Turned { [1, 0, 0] } else { [0; 3] });
    let mut classes: Vec<(([Content; 3], bool), usize)> = Vec::new();
    for (i, key) in all.iter().enumerate() {
        let class = (moved(*key, after_x), key.sheet.after(false));
        match classes.iter_mut().find(|(c, _)| *c == class) {
            Some((_, rep)) if key.changes() < all[*rep].changes() => *rep = i,
            Some(_) => {}
            None => classes.push((class, i)),
        }
    }
    let mut reps: Vec<usize> = classes.into_iter().map(|(_, i)| i).collect();
    reps.sort_unstable();
    reps
}

/// The count of picks across `lists`, one from each.
fn combos(lists: &[Vec<usize>]) -> usize {
    lists.iter().map(Vec::len).product()
}

/// The `n`-th pick across `lists`, the last list turning fastest.
fn nth(lists: &[Vec<usize>], mut n: usize) -> Vec<usize> {
    let mut picks = vec![0; lists.len()];
    for (pick, list) in picks.iter_mut().zip(lists).rev() {
        *pick = list[n % list.len()];
        n /= list.len();
    }
    picks
}

/// What a search found: the laws, the comparison, the searched bytes' keys, each group's score
/// and the keys' changes.
#[derive(Clone, Debug)]
struct Found {
    laws: [StrandLaw; 3],
    comparison: Comparison,
    keys: Vec<(u8, StrandKey)>,
    scores: Vec<Score>,
    changes: usize,
    order: (usize, usize),
}

impl Found {
    fn total(&self) -> Score {
        self.scores.iter().fold(Score::default(), |a, &s| a + s)
    }

    /// The better of two: the higher total, then fewer changes, then the first in order.
    fn better(self, other: Self) -> Self {
        let key = |f: &Self| (std::cmp::Reverse(f.total()), f.changes, f.order);
        if key(&other) < key(&self) { other } else { self }
    }
}

/// The best arrangement over `laws`, `comparisons` and the keys of the `open` bytes, the others
/// held at `held` (or the identity): a byte standing only at `u` is searched by its classes from
/// rest, any other by every key. Open bytes standing in more than one group are enumerated
/// together; each group's own open bytes are then the best for that group. Every group's
/// calculations are scored through the symbol the arrangement puts there, each symbol read once.
fn search(groups: &[Searched], rings: &[LocatedRing], laws: &[[StrandLaw; 3]], comparisons: &[Comparison], held: &BTreeMap<u8, StrandKey>, open: &[u8]) -> Option<Found> {
    let all = StrandKey::all();
    let tables: Vec<Vec<OnceLock<Score>>> = groups.iter().map(|_| (0..SYMBOLS).map(|_| OnceLock::new()).collect()).collect();
    let at = |g: &Searched, b: u8| g.context[1] == b || g.context[2] == b;
    let shared: Vec<u8> = open.iter().copied().filter(|&b| groups.iter().filter(|g| at(g, b)).count() > 1).collect();
    let free: Vec<Vec<u8>> = groups.iter().map(|g| open.iter().copied().filter(|&b| at(g, b) && !shared.contains(&b)).collect()).collect();
    let only_u = |b: u8| groups.iter().all(|g| g.context[2] != b);
    let items: Vec<(usize, usize)> = (0..laws.len()).flat_map(|l| (0..comparisons.len()).map(move |c| (l, c))).collect();
    items
        .par_iter()
        .enumerate()
        .filter_map(|(item, &(l, c))| {
            let (laws, comparison) = (laws[l], comparisons[c]);
            let classes = classes_from_rest(laws, &all);
            let every: Vec<usize> = (0..all.len()).collect();
            let choices = |b: u8| if only_u(b) { classes.clone() } else { every.clone() };
            let shared_choices: Vec<Vec<usize>> = shared.iter().map(|&b| choices(b)).collect();
            let free_choices: Vec<Vec<Vec<usize>>> = free.iter().map(|f| f.iter().map(|&b| choices(b)).collect()).collect();
            let mut best: Option<Found> = None;
            'shared: for n in 0..combos(&shared_choices) {
                let picks = nth(&shared_choices, n);
                let mut keys: Vec<(u8, StrandKey)> = shared.iter().zip(&picks).map(|(&b, &i)| (b, all[i])).collect();
                let mut changes: usize = picks.iter().map(|&i| all[i].changes()).sum();
                let mut scores = Vec::with_capacity(groups.len());
                for (g, group) in groups.iter().enumerate() {
                    let mut best_g: Option<(Score, usize, usize, Vec<usize>)> = None;
                    for m in 0..combos(&free_choices[g]) {
                        let own = nth(&free_choices[g], m);
                        let key = |b: u8| -> StrandKey {
                            if let Some(i) = shared.iter().position(|&s| s == b) {
                                all[picks[i]]
                            } else if let Some(i) = free[g].iter().position(|&f| f == b) {
                                all[own[i]]
                            } else {
                                held.get(&b).copied().unwrap_or(StrandKey::IDENTITY)
                            }
                        };
                        let (contents, reversed) = contents(laws, key(group.context[1]), key(group.context[2]));
                        let symbol = Symbol::of(laws, comparison, contents, reversed);
                        if symbol.result == 0 {
                            continue;
                        }
                        let score = *tables[g][symbol.index()].get_or_init(|| read(&symbol, &group.rows, rings));
                        let own_changes: usize = own.iter().map(|&i| all[i].changes()).sum();
                        if best_g.as_ref().is_none_or(|(s, ch, _, _)| score > *s || (score == *s && own_changes < *ch)) {
                            best_g = Some((score, own_changes, m, own));
                        }
                    }
                    let Some((score, own_changes, _, own)) = best_g else { continue 'shared };
                    scores.push(score);
                    changes += own_changes;
                    keys.extend(free[g].iter().zip(&own).map(|(&b, &i)| (b, all[i])));
                }
                keys.sort_by_key(|&(b, _)| b);
                let found = Found { laws, comparison, keys, scores, changes, order: (item, n) };
                best = Some(match best {
                    Some(b) => b.better(found),
                    None => found,
                });
            }
            best
        })
        .reduce_with(Found::better)
}

/// What the strands meet along the text: a run of bytes no keyed byte stands between (each located
/// digit stepping, and turning a turned strand, on every ring: `(μ^n, N)` for each ring), the keyed
/// bytes that stand together with no located digit between them (they act as one key, composed),
/// or a scored calculation's result, read digit by digit.
enum Event {
    Run(Vec<(u64, u64)>),
    Keys(Vec<u8>),
    Result(usize),
}

/// `first` then `then`, as one key: each strand takes what `then` names of what `first` left, and
/// the sheet takes `then`'s act after `first`'s.
fn composed(first: StrandKey, then: StrandKey) -> StrandKey {
    let source = then.source.map(|v| match v {
        0 => 0,
        v if v > 0 => first.source[v as usize - 1],
        v => -first.source[(-v) as usize - 1],
    });
    let sheet = match (then.sheet.after(first.sheet.after(false)), then.sheet.after(first.sheet.after(true))) {
        (false, true) => Sheet::Kept,
        (true, false) => Sheet::Flipped,
        (false, false) => Sheet::Plus,
        (true, true) => Sheet::Minus,
    };
    StrandKey { source, sheet }
}

/// The text as its events, read from its first byte.
fn events_of(text: &[u8], rows: &[Row], rings: &[LocatedRing], digit: &[Option<usize>; 256], keyed: &[bool; 256]) -> Vec<Event> {
    let mut results: Vec<(usize, usize)> = rows.iter().enumerate().map(|(r, row)| (row.stretch.numerals[2].0, r)).collect();
    results.sort_unstable();
    let mut results = results.into_iter().peekable();
    let mut events = Vec::new();
    let mut run: Option<Vec<(u64, u64)>> = None;
    let mut i = 0;
    while i < text.len() {
        if let Some(&(at, r)) = results.peek() {
            if at == i {
                events.extend(run.take().map(Event::Run));
                events.push(Event::Result(r));
                i = rows[r].stretch.numerals[2].1;
                results.next();
                continue;
            }
        }
        let b = usize::from(text[i]);
        if keyed[b] {
            if let Some(steps) = run.take() {
                events.push(Event::Run(steps));
            }
            match events.last_mut() {
                Some(Event::Keys(bytes)) => bytes.push(text[i]),
                _ => events.push(Event::Keys(vec![text[i]])),
            }
        } else if let Some(d) = digit[b] {
            let steps = run.get_or_insert_with(|| vec![(1, 0); rings.len()]);
            for ((m, n), ring) in steps.iter_mut().zip(rings) {
                let (q, mu) = (u64::from(ring.modulus), u64::from(ring.multiplier));
                (*m, *n) = (*m * mu % q, (*n * mu + u64::from(ring.turns[d])) % q);
            }
        }
        i += 1;
    }
    events.extend(run.take().map(Event::Run));
    events
}

/// The strands' residues on one ring after a digit of turn `turn`.
fn digit_read(r: &mut [u32; 3], laws: [StrandLaw; 3], turn: u32, ring: &LocatedRing, reversed: bool) {
    let ring = StrandRing { modulus: ring.modulus, multiplier: ring.multiplier };
    for (v, law) in r.iter_mut().zip(laws) {
        *v = law.at_digit(*v, turn, ring, reversed);
    }
}

/// Each group's score on the stream of `events` from rest under `keys` (one for every byte).
#[allow(clippy::too_many_arguments)]
fn stream(events: &[Event], text: &[u8], rows: &[Row], rings: &[LocatedRing], digit: &[Option<usize>; 256], laws: [StrandLaw; 3], comparison: Comparison, keys: &[StrandKey; 256], groups: usize) -> Vec<Score> {
    let mut r = vec![[0u32; 3]; rings.len()];
    let mut reversed = false;
    let mut scores = vec![Score::default(); groups];
    for event in events {
        match event {
            Event::Run(steps) => {
                for ((v, &(m, n)), ring) in r.iter_mut().zip(steps).zip(rings) {
                    let q = u64::from(ring.modulus);
                    let add = if reversed { (q - n) % q } else { n };
                    for (x, law) in v.iter_mut().zip(laws) {
                        *x = match law {
                            StrandLaw::Turned => ((u64::from(*x) * m + add) % q) as u32,
                            StrandLaw::Stepped => (u64::from(*x) * m % q) as u32,
                            StrandLaw::Held => *x,
                        };
                    }
                }
            }
            Event::Keys(bytes) => {
                let key = bytes.iter().fold(StrandKey::IDENTITY, |k, &b| composed(k, keys[usize::from(b)]));
                for (v, ring) in r.iter_mut().zip(rings) {
                    *v = key.apply(*v, ring.modulus);
                }
                reversed = key.sheet.after(reversed);
            }
            Event::Result(i) => {
                let row = &rows[*i];
                let q = u64::from(rings[row.ring].modulus);
                let score = &mut scores[row.group];
                for (k, b) in row.stretch.numeral(text, 2).iter().enumerate() {
                    score.digits += usize::from(tenth(comparison.value(r[row.ring], q), q) == row.tenths[k]);
                    let d = digit[usize::from(*b)].expect("a result's bytes are located");
                    for (v, ring) in r.iter_mut().zip(rings) {
                        digit_read(v, laws, ring.turns[d], ring, reversed);
                    }
                }
                score.closed += usize::from(comparison.value(r[row.ring], q) == 0);
            }
        }
    }
    scores
}

/// The key as `S,S,S:sheet`.
fn key_text(k: &StrandKey) -> String {
    let sheet = match k.sheet {
        Sheet::Kept => "kept",
        Sheet::Flipped => "flipped",
        Sheet::Plus => "plus",
        Sheet::Minus => "minus",
    };
    format!("{},{},{}:{sheet}", k.source[0], k.source[1], k.source[2])
}

/// The keys as `BYTE=KEY` pairs.
fn keys_text(keys: &[(u8, StrandKey)]) -> String {
    keys.iter().map(|(b, k)| format!("{}={}", shown(&[*b]), key_text(k))).collect::<Vec<_>>().join(" ")
}

fn laws_text(laws: [StrandLaw; 3]) -> String {
    laws.map(|l| match l {
        StrandLaw::Turned => "turned",
        StrandLaw::Stepped => "stepped",
        StrandLaw::Held => "held",
    })
    .join(",")
}

/// The strands' located arrangement: the laws, the comparison the location read, and the key of
/// every byte at a closing group's `w`, `u`, `v` or `t` (the identity included).
struct Arrangement {
    laws: [StrandLaw; 3],
    comparison: Comparison,
    keys: Vec<(u8, StrandKey)>,
}

/// The strands' laws and keys located on `text` over its closing groups and rings (the three
/// stages above), each stage reported.
fn locate_strands(text: &[u8], closing: &[Closing], rings: &[LocatedRing], bytes: &[u8], started: Instant) -> std::result::Result<Arrangement, String> {
    let (rows, beyond) = rows_on(text, closing, rings, bytes);
    let searched: Vec<Searched> = closing
        .iter()
        .enumerate()
        .map(|(g, c)| Searched { context: c.context, hand: HANDS[c.hand], rows: rows.iter().filter(|r| r.group == g).collect() })
        .collect();
    for (g, s) in searched.iter().enumerate() {
        let digits: usize = s.rows.iter().map(|r| r.tenths.len()).sum();
        println!(
            "STRANDS_GROUP context={} hand={},{} stretches={} rows={} beyond={} digits={}",
            shown(&s.context),
            s.hand[0],
            s.hand[1],
            closing[g].stretches.len(),
            s.rows.len(),
            beyond[g],
            digits
        );
    }
    // Stage 1: the two largest closing groups' `u` and `v` bytes, with the laws and the comparison.
    let first = &searched[..searched.len().min(2)];
    let mut open: Vec<u8> = first.iter().flat_map(|g| [g.context[1], g.context[2]]).collect();
    open.sort_unstable();
    open.dedup();
    let all_laws: Vec<[StrandLaw; 3]> = StrandLaw::ALL.iter().flat_map(|&a| StrandLaw::ALL.iter().flat_map(move |&b| StrandLaw::ALL.iter().map(move |&c| [a, b, c]))).collect();
    let found = search(first, rings, &all_laws, &Comparison::all(), &BTreeMap::new(), &open).ok_or("no arrangement reads the largest closing groups")?;
    let predicted: Vec<bool> = first
        .iter()
        .map(|g| {
            let key = |b: u8| found.keys.iter().find(|(k, _)| *k == b).map_or(StrandKey::IDENTITY, |&(_, k)| k);
            let (c, reversed) = contents(found.laws, key(g.context[1]), key(g.context[2]));
            Symbol::of(found.laws, found.comparison, c, reversed).closes(g.hand)
        })
        .collect();
    println!(
        "STRANDS_LOCATED stage=1 laws={} comparison={},{}:{},{} keys={} changes={} {} elapsed_ms={}",
        laws_text(found.laws),
        found.comparison.strands[0],
        found.comparison.strands[1],
        found.comparison.signs[0],
        found.comparison.signs[1],
        keys_text(&found.keys),
        found.changes,
        first
            .iter()
            .zip(&found.scores)
            .zip(&predicted)
            .map(|((g, s), p)| format!("{}:closed={}/{},digits={},symbolic={}", shown(&g.context), s.closed, g.rows.len(), s.digits, p))
            .collect::<Vec<_>>()
            .join(" "),
        started.elapsed().as_millis()
    );
    let (laws, comparison) = (found.laws, found.comparison);
    let mut held: BTreeMap<u8, StrandKey> = found.keys.into_iter().collect();
    // Stage 2: each other closing group's new `u` and `v` bytes.
    for group in searched.iter().skip(2) {
        let mut new: Vec<u8> = [group.context[1], group.context[2]].into_iter().filter(|b| !held.contains_key(b)).collect();
        new.dedup();
        if new.is_empty() {
            continue;
        }
        let one = std::slice::from_ref(group);
        let found = search(one, rings, &[laws], &[comparison], &held, &new).ok_or("no key reads a closing group")?;
        println!(
            "STRANDS_LOCATED stage=2 context={} keys={} closed={}/{} digits={} elapsed_ms={}",
            shown(&group.context),
            keys_text(&found.keys),
            found.scores[0].closed,
            group.rows.len(),
            found.scores[0].digits,
            started.elapsed().as_millis()
        );
        held.extend(found.keys);
    }
    // Stage 3: every byte at a closing group's `w`, `u`, `v` or `t`, on the real stream.
    let mut keyed = [false; 256];
    for c in closing {
        for b in c.context {
            keyed[usize::from(b)] = true;
        }
    }
    let mut digit = [None; 256];
    for (i, &b) in bytes.iter().enumerate() {
        digit[usize::from(b)] = Some(i);
    }
    let events = events_of(text, &rows, rings, &digit, &keyed);
    let mut keys = [StrandKey::IDENTITY; 256];
    for (&b, &k) in &held {
        keys[usize::from(b)] = k;
    }
    let all = StrandKey::all();
    let keyed_bytes: Vec<u8> = (0..=255u8).filter(|&b| keyed[usize::from(b)]).collect();
    // [agent-inferred] The bytes no symbolic stage located go first: those stages read every
    // calculation from rest, and the stream's state before `w` is rest only once `w`'s key is
    // located, so a located key moved first against a state its stage never assumed loses the
    // evidence it carried (measured on the synthetic menu: moved first, the sums' `u` key took a
    // key that read the leftover strands and the stream closed 4 of 45).
    let order: Vec<u8> = keyed_bytes.iter().copied().filter(|b| !held.contains_key(b)).chain(keyed_bytes.iter().copied().filter(|b| held.contains_key(b))).collect();
    let total = |scores: &[Score]| scores.iter().fold(Score::default(), |a, &s| a + s);
    let read_all = |keys: &[StrandKey; 256]| stream(&events, text, &rows, rings, &digit, laws, comparison, keys, closing.len());
    let mut current = total(&read_all(&keys));
    println!(
        "STRANDS_STREAM_START events={} keyed={} closed={} digits={} elapsed_ms={}",
        events.len(),
        shown(&keyed_bytes),
        current.closed,
        current.digits,
        started.elapsed().as_millis()
    );
    for round in 1.. {
        let mut changed = false;
        for &b in &order {
            let at = usize::from(b);
            let now = keys[at];
            let scored: Vec<Score> = all
                .par_iter()
                .map(|&k| {
                    let mut trial = keys;
                    trial[at] = k;
                    total(&read_all(&trial))
                })
                .collect();
            // A key moves only on a strictly better score, so the ascent keeps what a tie cannot
            // decide and ends.
            let rank = |i: usize| (std::cmp::Reverse(scored[i]), all[i] != now, all[i].changes(), i);
            let best = (0..all.len()).min_by_key(|&i| rank(i)).expect("keys");
            if all[best] != now {
                keys[at] = all[best];
                changed = true;
            }
            current = scored[best];
            println!(
                "STRANDS_ASCENT round={round} byte={} key={} closed={} digits={} elapsed_ms={}",
                shown(&[b]),
                key_text(&keys[at]),
                current.closed,
                current.digits,
                started.elapsed().as_millis()
            );
        }
        if !changed {
            break;
        }
    }
    let scores = read_all(&keys);
    for (s, score) in searched.iter().zip(&scores) {
        let digits: usize = s.rows.iter().map(|r| r.tenths.len()).sum();
        println!("STRANDS_STREAM context={} rows={} closed={} digits={}/{}", shown(&s.context), s.rows.len(), score.closed, score.digits, digits);
    }
    let two = searched.len().min(2);
    let rows_two: usize = searched[..two].iter().map(|s| s.rows.len()).sum();
    let closed_two: usize = scores[..two].iter().map(|s| s.closed).sum();
    println!("STRANDS_CLOSED groups={two} closed={closed_two} rows={rows_two} elapsed_ms={}", started.elapsed().as_millis());
    let keys = keyed_bytes.iter().map(|&b| (b, keys[usize::from(b)])).collect();
    Ok(Arrangement { laws, comparison, keys })
}

/// The menu read from `text`: its closing groups, the first closing group's rings and located
/// bytes. Each stage is reported when `report` holds.
struct Menu {
    closing: Vec<Closing>,
    rings: Vec<LocatedRing>,
    bytes: Vec<u8>,
}

fn menu_of(text: &[u8], period: usize, report: bool) -> std::result::Result<Menu, String> {
    let stretches = stretches_of(text);
    let groups = groups_of(text, &stretches);
    if report {
        println!("STRANDS_MENU stretches={} groups={} period={period}", stretches.len(), groups.len());
    }
    let (g, h) = first_closing(text, &groups, period, report).ok_or("no group closes under one hand")?;
    let loops = loops_of(text, &groups[g].1, HANDS[h]);
    let bytes = bytes_of(&loops);
    if report {
        println!("STRANDS_FIRST context={} stretches={} hand={},{} bytes={}", shown(&groups[g].0), groups[g].1.len(), HANDS[h][0], HANDS[h][1], shown(&bytes));
    }
    let mut rings = Vec::new();
    for length in 1..=period {
        match strand_ring(&loops, &bytes, length) {
            Ok(ring) => {
                if report {
                    let primes: Vec<String> = ring.primes.iter().map(|(p, q)| format!("{p}:{q}")).collect();
                    let turns: Vec<String> = ring.turns.iter().map(u32::to_string).collect();
                    println!(
                        "STRANDS_RING length={length} step={} modulus={} multiplier={} primes={} turns={}",
                        ring.step,
                        ring.modulus,
                        ring.multiplier,
                        primes.join(","),
                        turns.join(",")
                    );
                }
                rings.push(ring);
            }
            Err(why) => {
                if report {
                    println!("STRANDS_RING length={length} refused={why}");
                }
            }
        }
    }
    if rings.is_empty() {
        return Err("the first closing group locates no ring".into());
    }
    let largest = rings.last().expect("a ring");
    let mut closing = Vec::new();
    let mut refused = 0;
    for (context, stretches) in groups {
        let Some(hand) = hand_of(text, &stretches, &rings, &bytes) else { continue };
        let (rank, touched) = own_rank(text, &stretches, hand, &bytes, largest.step, largest.length);
        if rank == touched {
            closing.push(Closing { context, stretches, hand });
        } else {
            refused += 1;
            if report {
                println!("STRANDS_UNCARRIED context={} stretches={} hand={},{} rank={rank} touched={touched}", shown(&context), stretches.len(), HANDS[hand][0], HANDS[hand][1]);
            }
        }
    }
    if report {
        println!("STRANDS_CLOSING groups={} stretches={} uncarried={refused}", closing.len(), closing.iter().map(|c| c.stretches.len()).sum::<usize>());
    }
    Ok(Menu { closing, rings, bytes })
}

/// `locate-strands TRAIN TRAIN_SHA PERIOD` reads the training text's menu, rings and closing groups
/// and locates the strands' laws and keys on it, reporting each stage and founding nothing: the
/// locator's lines, read before a founding.
pub(super) fn locate_strands_on(args: &[String]) -> Result<()> {
    if args.len() != 4 {
        return Err("locate-strands TRAIN TRAIN_SHA PERIOD".into());
    }
    let started = Instant::now();
    let text = pinned_read(&args[1], &args[2], READ_BUDGET as usize)?;
    let period = positive(&args[3])?;
    let menu = menu_of(&text, period, true)?;
    locate_strands(&text, &menu.closing, &menu.rings, &menu.bytes, started)?;
    Ok(())
}

pub(super) fn found_unit_rotor_tower(args: &[String]) -> Result<()> {
    if args.len() != 15 {
        return Err("found-unit-rotor-tower UNITS UNITS_SHA TRAIN TRAIN_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS RATE_BITS PERIOD LAW OUT".into());
    }
    let started = Instant::now();
    let units = Units::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], READ_BUDGET as usize)?)?).map_err(|e| e.to_string())?;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let keys = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let declaration = TowerDeclaration {
        alphabet: units.len(),
        width: count(&args[7])?,
        modes: count(&args[8])?,
        contacts: count(&args[9])?,
        levels: positive(&args[10])?,
        gated: true,
        turned: true,
        pumped: true,
        contact: ContactLaw::Pair,
    };
    let rate_bits: u32 = args[11].parse()?;
    let period = positive(&args[12])?;
    // Whether the rotor turns, and whether strands join (with their located keys or none).
    let (turned, strands) = match args[13].as_str() {
        "modulated" => (true, None),
        "free" => (false, None),
        "strands" => (true, Some(true)),
        "strands-still" => (true, Some(false)),
        _ => return Err("LAW is modulated (the rings step and turn), free (they step alone), strands (modulated with the located strands) or strands-still (with every strands' key the identity)".into()),
    };
    let out = Path::new(&args[14]);
    if out.exists() {
        return Err("OUT exists: the learner is written create-new".into());
    }
    let menu = menu_of(&text, period, true)?;
    let loops: Vec<Loop> = menu.closing.iter().flat_map(|c| loops_of(&text, &c.stretches, HANDS[c.hand])).collect();
    let bytes = bytes_of(&loops);
    println!("ROTOR_MENU loops={} bytes={} period={period} columns={}", loops.len(), bytes.len(), period * bytes.len());
    // The step whose torsion carries the most, the smaller of a tie.
    let step = best_step(&loops, &bytes, period, |s, c, product| {
        println!(
            "ROTOR_CLOSURE step={s} rows={} rank={} minor_bits={} torsion={} carried={product} elapsed_ms={}",
            c.rows,
            c.rank,
            c.minor.bits(),
            torsion_text(c),
            started.elapsed().as_millis()
        );
    });
    let (s, product) = (step.s, step.carried.clone());
    let mut rings = Vec::new();
    for (p, fall, ring) in located(&step.rows, &step.closure, bytes.len(), period) {
        match ring {
            Ok(ring) => {
                let modes: Vec<String> = (0..ring.width).map(|m| ring.theta[m * bytes.len()..(m + 1) * bytes.len()].iter().map(u32::to_string).collect::<Vec<_>>().join(",")).collect();
                println!(
                    "ROTOR_KEY prime={p} fall={fall} modulus={} width={} bytes={} turns={} elapsed_ms={}",
                    ring.modulus,
                    ring.width,
                    String::from_utf8_lossy(&bytes),
                    modes.join("/"),
                    started.elapsed().as_millis()
                );
                rings.push(ring);
            }
            Err(why) => println!("ROTOR_KEY prime={p} fall={fall} refused={why}"),
        }
    }
    rings.sort_by_key(|r| r.modulus);
    let pieces: Vec<&[u8]> = (0..declaration.alphabet).map(|u| units.piece(u)).collect();
    let rotor = founded_rotor(&declaration, &pieces, &bytes, s, period, &rings, turned)?;
    let moving: usize = rings.iter().map(|r| r.width).sum();
    let (k, alphabet) = (rings.len(), declaration.alphabet);
    let stepping = (0..alphabet).filter(|&u| rotor.steps()[u * k..(u + 1) * k].iter().any(|&v| v != 0)).count();
    let turning = (0..alphabet).filter(|&u| rotor.turns()[u * moving..(u + 1) * moving].iter().any(|&v| v != 0)).count();
    let first = rotor.moving();
    let mut tower = Tower::found_on(declaration, &keys, TurnLadder::Fixed).map_err(|e| e.to_string())?;
    tower.join_rotor(rotor).map_err(|e| e.to_string())?;
    if let Some(keyed) = strands {
        let arrangement = locate_strands(&text, &menu.closing, &menu.rings, &menu.bytes, started)?;
        let keys: Vec<(u8, StrandKey)> = if keyed { arrangement.keys.iter().copied().filter(|&(_, k)| k != StrandKey::IDENTITY).collect() } else { Vec::new() };
        let digits: Vec<(u8, Vec<u32>)> = menu.bytes.iter().enumerate().map(|(i, &b)| (b, menu.rings.iter().map(|r| r.turns[i]).collect())).collect();
        let strand_rings: Vec<StrandRing> = menu.rings.iter().map(|r| StrandRing { modulus: r.modulus, multiplier: r.multiplier }).collect();
        let words: Vec<Vec<u8>> = pieces.iter().map(|p| p.to_vec()).collect();
        let strands = Strands::new(&declaration, 0, first, strand_rings, arrangement.laws, digits, keys.clone(), words).map_err(|e| e.to_string())?;
        tower.join_strands(strands).map_err(|e| e.to_string())?;
        println!(
            "STRANDS_FOUNDED level=0 first={first} written={} rings={} laws={} comparison={},{}:{},{} keys={}",
            3 * menu.rings.len(),
            menu.rings.iter().map(|r| format!("{}:{}", r.modulus, r.multiplier)).collect::<Vec<_>>().join(","),
            laws_text(arrangement.laws),
            arrangement.comparison.strands[0],
            arrangement.comparison.strands[1],
            arrangement.comparison.signs[0],
            arrangement.comparison.signs[1],
            if keys.is_empty() { "none".to_string() } else { keys_text(&keys) }
        );
    }
    let written = TowerLearner::new(tower, rate_bits).to_text().into_bytes();
    write_new(out, &written)?;
    let named: Vec<String> = rings.iter().map(|r| format!("{}:{}", r.modulus, r.width)).collect();
    println!(
        "ROTOR_FOUNDED step={s} law={} carried={product} rings={} moving={moving} still={} primes={} units={alphabet} stepping_units={stepping} turning_units={turning} levels_stepped=1 bytes={} sha256={} elapsed_ms={}",
        args[13],
        if named.is_empty() { "none".to_string() } else { named.join(",") },
        declaration.modes.saturating_sub(moving),
        rings.iter().map(|r| r.prime.to_string()).collect::<Vec<_>>().join(","),
        written.len(),
        sha256(&written)?,
        started.elapsed().as_millis()
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every stretch of three numerals with single bytes between and around them, grouped by its
    /// context; a numeral at the text's end has no byte after it and closes no stretch.
    #[test]
    fn the_menu_is_the_stretches_grouped_by_context() {
        let text = b"x <<12+7=19>> y <<40-15=25>> <<1.5+2=3.5>> <<4*2=8>> <<9+1=10";
        let stretches = stretches_of(text);
        let groups = groups_of(text, &stretches);
        let contexts: Vec<&[u8; 4]> = groups.iter().map(|(c, _)| c).collect();
        assert_eq!(contexts, vec![b"+=.>", b".+=.", b"<*=>", b"<+=>", b"<-=>", b"<.+="]);
        assert!(groups.iter().all(|(_, s)| s.len() == 1));
        let sums = &groups.iter().find(|(c, _)| c == b"<+=>").expect("the sum").1;
        assert_eq!(loops_of(text, sums, HANDS[0]), vec![[(&b"19"[..], 1), (&b"12"[..], -1), (&b"7"[..], -1)]]);
    }

    /// A menu of products, sums and differences, the products the most numerous; no result is all
    /// nines.
    fn menu_text(products: usize, sums: usize, differences: usize) -> Vec<u8> {
        let mut text = Vec::new();
        let mut x = 7u64;
        let mut next = |bound: u64| {
            x = x * 48271 % 2147483647;
            x % bound
        };
        let (mut p, mut s, mut d) = (0, 0, 0);
        while p < products || s < sums || d < differences {
            let (a, b) = (next(9973), next(997));
            let all_nines = |n: u64| n.to_string().bytes().all(|c| c == b'9');
            if all_nines(a + b) || all_nines(a) {
                continue;
            }
            if p < products {
                text.extend_from_slice(format!("<<{a}*{b}={}>> ", a * b).as_bytes());
                p += 1;
            }
            if s < sums {
                text.extend_from_slice(format!("<<{a}+{b}={}>> ", a + b).as_bytes());
                s += 1;
            }
            if d < differences {
                text.extend_from_slice(format!("<<{}-{b}={a}>>\n", a + b).as_bytes());
                d += 1;
            }
        }
        text
    }

    /// The products close under no hand, so the sums are the first closing group, under `(1, 1)`;
    /// ring `L` holds the tens' character modulo a divisor of `10^L − 1` with multiplier 10, and
    /// the differences close under `(1, −1)`.
    #[test]
    fn the_closing_groups_and_their_hands() {
        let text = menu_text(60, 50, 40);
        let menu = menu_of(&text, 4, false).expect("a menu");
        let closing: Vec<(&[u8; 4], usize, usize)> = menu.closing.iter().map(|c| (&c.context, c.stretches.len(), c.hand)).collect();
        assert_eq!(closing, vec![(b"<+=>", 50, 0), (b"<-=>", 40, 1)]);
        assert_eq!(menu.bytes, b"0123456789".to_vec());
        assert_eq!(menu.rings.iter().map(|r| r.length).collect::<Vec<_>>(), vec![1, 2, 3, 4]);
        for ring in &menu.rings {
            let tens = 10u64.pow(ring.length as u32) - 1;
            let q = u64::from(ring.modulus);
            assert_eq!(tens % q, 0, "{q} divides {tens}");
            assert_eq!(u64::from(ring.multiplier), 10 % q);
            assert_eq!(ring.turns, (0..10u64).map(|d| (d % q) as u32).collect::<Vec<_>>());
        }
        assert_eq!(menu.rings.iter().map(|r| r.modulus).collect::<Vec<_>>(), vec![9, 99, 999, 9999]);
    }

    /// Over enough loops, the tenfold step closes them modulo every prime of `9999`, the half step
    /// modulo those of `99`, and the still step modulo 3 alone (the digit sum).
    #[test]
    fn the_tenfold_step_carries_the_most_torsion() {
        let text = menu_text(0, 300, 300);
        let menu = menu_of(&text, 4, false).expect("a menu");
        let loops: Vec<Loop> = menu.closing.iter().flat_map(|c| loops_of(&text, &c.stretches, HANDS[c.hand])).collect();
        let bytes = bytes_of(&loops);
        let primes = |s: usize| closure(&rows_of(&loops, &bytes, s, 4)).torsion.iter().map(|&(p, _)| p).collect::<Vec<_>>();
        assert_eq!(primes(1), vec![3, 11, 101]);
        assert_eq!(primes(3), vec![3, 11, 101]);
        assert_eq!(primes(2), vec![3, 11]);
        assert_eq!(primes(0), vec![3]);
    }

    /// The tenfold step's kernels are the tenfold characters: modulo 3 lifted to 9 the turn of
    /// every mode is the digit, modulo 11 it alternates `d, 10d` (width 2), modulo 101 it is
    /// `10^m d` over the whole ring of four; nothing lifts past them.
    #[test]
    fn the_turns_are_the_tenfold_characters() {
        let text = menu_text(0, 300, 300);
        let menu = menu_of(&text, 4, false).expect("a menu");
        let loops: Vec<Loop> = menu.closing.iter().flat_map(|c| loops_of(&text, &c.stretches, HANDS[c.hand])).collect();
        let bytes = bytes_of(&loops);
        let rows = rows_of(&loops, &bytes, 1, 4);
        let rings: Vec<Located> = located(&rows, &closure(&rows), 10, 4).into_iter().map(|(_, _, r)| r.expect("a located ring")).collect();
        assert_eq!(rings.iter().map(|r| (r.modulus, r.width)).collect::<Vec<_>>(), vec![(9, 1), (11, 2), (101, 4)]);
        for ring in &rings {
            let q = u64::from(ring.modulus);
            let mut tenfold = 1u64;
            for m in 0..4 {
                let expected: Vec<u32> = (0..10u64).map(|d| (tenfold * d % q) as u32).collect();
                assert_eq!(ring.theta[m * 10..(m + 1) * 10], expected[..], "modulus {q}, mode {m}");
                tenfold = tenfold * 10 % q;
            }
        }
    }

    /// The equation at the consumer: read from rest through units of one byte and of several, with
    /// bytes the menu never meets between them, the turns' residue on mode `j` of each ring is
    /// `10^j·n` modulo the ring's modulus for the numeral `n` read (`(T P^σ h)_m` adds the key to the
    /// residue of the mode it takes). The law `free` steps the same rings and turns nothing, and the
    /// second level holds still.
    #[test]
    fn the_numeral_read_is_its_characters() {
        let text = menu_text(0, 300, 300);
        let menu = menu_of(&text, 4, false).expect("a menu");
        let loops: Vec<Loop> = menu.closing.iter().flat_map(|c| loops_of(&text, &c.stretches, HANDS[c.hand])).collect();
        let bytes = bytes_of(&loops);
        let rows = rows_of(&loops, &bytes, 1, 4);
        let mut rings: Vec<Located> = located(&rows, &closure(&rows), bytes.len(), 4).into_iter().map(|(_, _, r)| r.expect("a located ring")).collect();
        rings.sort_by_key(|r| r.modulus);
        let mut pieces: Vec<&[u8]> = (0..10).map(|d| &b"0123456789"[d..d + 1]).collect();
        pieces.extend([&b"12"[..], b"345", b"00", b",", b" ", b"x7"]);
        let declaration = TowerDeclaration { alphabet: pieces.len(), width: 1, modes: 8, contacts: 1, levels: 2, gated: false, turned: false, pumped: false, contact: ContactLaw::Rectifying };
        let rotor = founded_rotor(&declaration, &pieces, &bytes, 1, 4, &rings, true).expect("rotor");
        let free = founded_rotor(&declaration, &pieces, &bytes, 1, 4, &rings, false).expect("rotor");
        assert_eq!(free.steps(), rotor.steps());
        assert!(free.turns().iter().all(|&r| r == 0));
        let moduli: Vec<u64> = rotor.rings().iter().flat_map(|g| std::iter::repeat(u64::from(g.modulus)).take(g.width)).collect();
        // Each reading as the units it is read in, and the numeral it holds.
        let mut readings: Vec<(Vec<usize>, u64)> =
            loops.iter().flatten().map(|(n, _)| (n.iter().map(|b| usize::from(b - b'0')).collect(), std::str::from_utf8(n).expect("digits").parse().expect("a numeral"))).collect();
        readings.extend([(vec![1, 10, 11], 112_345), (vec![13, 10, 14, 11], 12_345), (vec![10, 12, 15], 12_007), (vec![14, 11, 13, 12, 11], 34_500_345)]);
        for (read, n) in readings {
            let mut residue = vec![0u64; moduli.len()];
            for &u in &read {
                residue = (0..moduli.len()).map(|m| (u64::from(rotor.turn(0, u, m)) + residue[rotor.source(0, u, m)]) % moduli[m]).collect();
            }
            let mut first = 0;
            for ring in rotor.rings() {
                let q = u64::from(ring.modulus);
                let mut character = n % q;
                for j in 0..ring.width {
                    assert_eq!(residue[first + j], character, "{n} modulo {q}, mode {j}");
                    character = character * 10 % q;
                }
                first += ring.width;
            }
        }
        for u in 0..pieces.len() {
            assert!((0..rotor.rings().len()).all(|k| rotor.step(1, u, k) == 0) && (0..8).all(|m| rotor.turn(1, u, m) == 0));
        }
    }

    /// The equation at the consumer (the record's §2 and §3): on a menu of sums and differences the
    /// joint search finds laws, a comparison and keys under which every calculation with a ring
    /// closes and writes every digit right, by its symbols alone; the sums' and the differences'
    /// `u` keys put `y` on opposite sheets. Read on the stream, the located keys of the `w`, `u`,
    /// `v` and `t` bytes close every calculation, and the stream's events leave the strands where
    /// the strands' own law leaves them, byte by byte.
    #[test]
    fn the_located_strands_close_the_menu() {
        let text = menu_text(30, 25, 20);
        let menu = menu_of(&text, 4, false).expect("a menu");
        let (rows, _) = rows_on(&text, &menu.closing, &menu.rings, &menu.bytes);
        let searched: Vec<Searched> = menu
            .closing
            .iter()
            .enumerate()
            .map(|(g, c)| Searched { context: c.context, hand: HANDS[c.hand], rows: rows.iter().filter(|r| r.group == g).collect() })
            .collect();
        let laws: Vec<[StrandLaw; 3]> = StrandLaw::ALL.iter().flat_map(|&a| StrandLaw::ALL.iter().flat_map(move |&b| StrandLaw::ALL.iter().map(move |&c| [a, b, c]))).collect();
        let found = search(&searched, &menu.rings, &laws, &Comparison::all(), &BTreeMap::new(), b"+-=").expect("found");
        for (g, score) in searched.iter().zip(&found.scores) {
            let digits: usize = g.rows.iter().map(|r| r.tenths.len()).sum();
            assert_eq!(*score, Score { closed: g.rows.len(), digits }, "{}", shown(&g.context));
        }
        let key = |b: u8| found.keys.iter().find(|(k, _)| *k == b).expect("a key").1;
        for g in &searched {
            let (c, reversed) = contents(found.laws, key(g.context[1]), key(g.context[2]));
            assert!(Symbol::of(found.laws, found.comparison, c, reversed).closes(g.hand));
        }
        assert_ne!(key(b'+').sheet.after(false), key(b'-').sheet.after(false));
        let arrangement = locate_strands(&text, &menu.closing, &menu.rings, &menu.bytes, Instant::now()).expect("located");
        assert_eq!(arrangement.keys.iter().map(|(b, _)| *b).collect::<Vec<_>>(), b"+-<=>".to_vec());
        let mut keys = [StrandKey::IDENTITY; 256];
        for &(b, k) in &arrangement.keys {
            keys[usize::from(b)] = k;
        }
        let (mut keyed, mut digit) = ([false; 256], [None; 256]);
        for &(b, _) in &arrangement.keys {
            keyed[usize::from(b)] = true;
        }
        for (i, &b) in menu.bytes.iter().enumerate() {
            digit[usize::from(b)] = Some(i);
        }
        let events = events_of(&text, &rows, &menu.rings, &digit, &keyed);
        let scores = stream(&events, &text, &rows, &menu.rings, &digit, arrangement.laws, arrangement.comparison, &keys, 2);
        for (g, score) in searched.iter().zip(&scores) {
            assert_eq!(score.closed, g.rows.len(), "{}", shown(&g.context));
        }
        // The strands' own law, byte by byte, at every result's end against the events.
        let declaration = TowerDeclaration { alphabet: 1, width: 1, modes: 12, contacts: 1, levels: 1, gated: false, turned: false, pumped: false, contact: ContactLaw::Rectifying };
        let digits: Vec<(u8, Vec<u32>)> = menu.bytes.iter().enumerate().map(|(i, &b)| (b, menu.rings.iter().map(|r| r.turns[i]).collect())).collect();
        let strand_rings: Vec<StrandRing> = menu.rings.iter().map(|r| StrandRing { modulus: r.modulus, multiplier: r.multiplier }).collect();
        let strands = Strands::new(&declaration, 0, 0, strand_rings, arrangement.laws, digits, arrangement.keys.clone(), vec![Vec::new()]).expect("strands");
        let (mut residues, mut reversed) = (vec![0u32; 12], false);
        let mut ends: Vec<(usize, &Row)> = rows.iter().map(|r| (r.stretch.numerals[2].1, r)).collect();
        ends.sort_by_key(|&(e, _)| e);
        let mut ends = ends.into_iter().peekable();
        let n = menu.rings.len();
        let mut closed = 0;
        for (i, &b) in text.iter().enumerate() {
            strands.hear_byte(&mut residues, &mut reversed, b);
            if let Some(&(end, row)) = ends.peek() {
                if end == i + 1 {
                    let g = row.ring;
                    let r = [residues[g], residues[n + g], residues[2 * n + g]];
                    closed += usize::from(arrangement.comparison.value(r, u64::from(menu.rings[g].modulus)) == 0);
                    ends.next();
                }
            }
        }
        assert_eq!(closed, rows.len());
    }
}
