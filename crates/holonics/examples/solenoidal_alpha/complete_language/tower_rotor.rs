//! [definition; agent-inferred with the mathematics thread, October 26] **The rotor's steps and turns
//! located by loop closure** ([`holonics::hnn::tower::Rotor`]; the records
//! `2026-10-26_THE_GENERATOR_AND_THE_MODULATOR_ARE_ONE_MOVE_AND_THE_PLACE_DECIDES_WHICH_SO_A_RING_COPRIME_TO_TEN_NEEDS_A_ROTOR.md`,
//! §11, and
//! `2026-10-26_THE_GENERATOR_IS_THE_MODULATOR_A_TURN_IS_TWO_REFLECTIONS_AND_THE_BASE_TURNS_COLLAPSES_OR_REFLECTS_EACH_RING.md`,
//! §5). The step `σ` and the turns `r` are integer keys: windings, which no descent reaches, since
//! any relaxed path between two keys passes through mixtures of modes. They are located the Bombe's
//! way, by the loops a menu of contacts closes.
//!
//! **The menu** is the training text's own calculations, `<<a+b=c>>` and `<<a-b=c>>` of whole
//! numerals, each a loop `left = first + second` (`c = a + b`, `a = b + c`). The markup is received
//! material, a landmark: it says where to look, never what to find. No value of a numeral enters the
//! rows; only which byte stands at which place.
//!
//! **The rows.** Read over a ring of `period` modes under a step `s` for every byte, a turn a byte
//! puts on mode `m` reaches mode `m − s·k` after the `k` bytes read after it. So the phase the
//! numeral leaves on mode `j` is `φ_j = Σ_i θ_((j + s·k_i) mod period)[b_i]`, with `θ_m[b]` the
//! unknown turn the byte `b` puts on mode `m` and `k_i` the bytes after the `i`-th. Each loop and
//! each mode `j` is one integer row, `φ_j(left) − φ_j(first) − φ_j(second) = 0`, over the columns
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
//! **The navigator** (laws `captured` and `numeral`; [`holonics::hnn::tower::Navigator`], the
//! second record's §7). The located rings are joined by Chinese remainders into one ring modulo
//! the product of their moduli (`9·11·101 = 9999`) over the least common multiple of their widths
//! (4), each located byte's turns joined with them. Its menu is the text's calculations
//! `<<x∘y=z>>` of three whole numerals with any one byte `∘` but `=`; read from rest by the
//! navigator's own digit law, each is a row `(φ(x), φ(y), φ(z))`, `φ(n)` the residue mode 0
//! holds. An operator gets a hand where, at every located ring, its rows' kernel modulo the ring's
//! prime is one line with a unit first entry, read at the gauge one and lifted to the ring's
//! modulus while the rows close: the line `(1, e_∘, e_=)`, the rings' lines joined. `=` takes the
//! hand every located operator's line agrees on. No operator is named: on a synthetic menu `+`
//! locates at one, `-` and `=` at minus one, and the product at none
//! (`the_hands_are_located_by_closure`). The navigator writes the first level's modes past the
//! rotor's moving ones; `captured` holds the located hands and `numeral` none, so there every
//! byte but a digit restarts (each numeral's own character, nothing captured). The equation at
//! the consumer: from rest, `<<a∘b=` leaves `K_j = 10^j (a + e_∘ b)`, and the result `c` then
//! `K_j + R_j = 10^j (a + e_∘ b + e_= c)`, zero for every sum and difference of the menu, read
//! through units of one byte and of several (`the_fold_is_the_calculation`).
//!
//! `found-unit-rotor-tower UNITS UNITS_SHA TRAIN TRAIN_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS
//! RATE_BITS PERIOD LAW OUT` founds the pumped pair-contact tower exactly as
//! `train-unit-pair-pumped-tower` founds it, joins the located rotor (`LAW` is `modulated`,
//! `free`, `captured` or `numeral`) and, under the last two, the navigator, and writes the rested
//! learner (create-new) for that command's `FROM`.
use super::tower_ring::{echelon_mod, rational_rank, readable_primes};
use super::tower_train::{count, positive};
use super::*;
use holonics::hnn::tower::{ContactLaw, Navigator, Rotor, RotorRing, Tower, TowerDeclaration, TowerLearner, TurnLadder};
use holonics::hnn::units::Units;
use num_bigint::BigInt;
use num_traits::{Signed, Zero};

/// The loops the text's calculations close, each `[left, first, second]` with
/// `left = first + second`: a sum `<<a+b=c>>` is `[c, a, b]` and a difference `<<a-b=c>>` is
/// `[a, b, c]`. Only calculations of three whole numerals (digits alone) are read.
fn loops_of(text: &[u8]) -> Vec<[&[u8]; 3]> {
    let digits = |at: usize| text.get(at..).map_or(0, |r| r.iter().take_while(|b| b.is_ascii_digit()).count());
    let mut out = Vec::new();
    let mut i = 0;
    while i + 1 < text.len() {
        if &text[i..i + 2] != b"<<" {
            i += 1;
            continue;
        }
        let a = i + 2;
        let op = a + digits(a);
        let b = op + 1;
        let eq = b + digits(b);
        let c = eq + 1;
        let end = c + digits(c);
        let whole = op > a && eq > b && end > c && matches!(text.get(op), Some(b'+' | b'-')) && text.get(eq) == Some(&b'=') && text.get(end..end + 2) == Some(b">>");
        if !whole {
            i += 2;
            continue;
        }
        let (x, y, z) = (&text[a..op], &text[b..eq], &text[c..end]);
        out.push(if text[op] == b'+' { [z, x, y] } else { [x, y, z] });
        i = end + 2;
    }
    out
}

/// The bytes the loops' numerals hold, ascending: the menu's located bytes.
fn bytes_of(loops: &[[&[u8]; 3]]) -> Vec<u8> {
    let mut bytes: Vec<u8> = loops.iter().flatten().flat_map(|n| n.iter().copied()).collect();
    bytes.sort_unstable();
    bytes.dedup();
    bytes
}

/// The closure rows under the step `s` over a ring of `period` modes, one a loop and a final mode,
/// over the columns `(m, b)` (`m · bytes.len()` plus the byte's place in `bytes`), deduplicated.
fn rows_of(loops: &[[&[u8]; 3]], bytes: &[u8], s: usize, period: usize) -> Vec<Vec<i128>> {
    let width = bytes.len();
    let mut rows: Vec<Vec<i128>> = Vec::with_capacity(loops.len() * period);
    for numerals in loops {
        for j in 0..period {
            let mut row = vec![0i128; period * width];
            for (numeral, sign) in numerals.iter().zip([1i128, -1, -1]) {
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

/// The calculations `<<x∘y=z>>` of three whole numerals with any one byte `∘` but `=` between the
/// first two, each `(∘, [x, y, z])`: the navigator's menu (`=` is the markup's own byte).
fn calculations_of(text: &[u8]) -> Vec<(u8, [&[u8]; 3])> {
    let digits = |at: usize| text.get(at..).map_or(0, |r| r.iter().take_while(|b| b.is_ascii_digit()).count());
    let mut out = Vec::new();
    let mut i = 0;
    while i + 1 < text.len() {
        if &text[i..i + 2] != b"<<" {
            i += 1;
            continue;
        }
        let a = i + 2;
        let op = a + digits(a);
        let b = op + 1;
        let eq = b + digits(b);
        let c = eq + 1;
        let end = c + digits(c);
        let whole = op > a && eq > b && end > c && text.get(op).is_some_and(|&o| o != b'=') && text.get(eq) == Some(&b'=') && text.get(end..end + 2) == Some(b">>");
        if !whole {
            i += 2;
            continue;
        }
        out.push((text[op], [&text[a..op], &text[b..eq], &text[c..end]]));
        i = end + 2;
    }
    out
}

/// The greatest common divisor, by Euclid's remainders.
fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// `x` modulo `m` with `x ≡ a_k (mod m_k)` for coprime `m_k`, by Chinese remainders.
fn chinese(residues: &[(i128, i128)]) -> (i128, i128) {
    residues.iter().fold((0i128, 1i128), |(x, m), &(a, n)| {
        let t = ((a - x).rem_euclid(n) * inverse_mod(m % n, n)).rem_euclid(n);
        ((x + m * t).rem_euclid(m * n), m * n)
    })
}

/// The navigator's ring: the located rings joined by Chinese remainders, `q` the product of their
/// moduli and `w` the least common multiple of their widths, and each located byte's joined turns
/// `θ_j[b]`, `j < w`.
struct Joined {
    modulus: u32,
    width: usize,
    digits: Vec<(u8, Vec<u32>)>,
}

fn joined(rings: &[Located], bytes: &[u8], period: usize) -> std::result::Result<Joined, &'static str> {
    if rings.is_empty() {
        return Err("no_located_ring");
    }
    let modulus = rings.iter().try_fold(1u64, |q, r| q.checked_mul(u64::from(r.modulus)).filter(|&q| q <= u64::from(u32::MAX))).ok_or("outgrew_the_32_bit_modulus")?;
    let width = rings.iter().fold(1, |w, r| w / gcd(w as u64, r.width as u64) as usize * r.width);
    let digits = bytes
        .iter()
        .enumerate()
        .map(|(i, &b)| {
            let turns = (0..width).map(|j| chinese(&rings.iter().map(|r| (i128::from(r.theta[(j % period) * bytes.len() + i]), i128::from(r.modulus))).collect::<Vec<_>>()).0 as u32).collect();
            (b, turns)
        })
        .collect();
    Ok(Joined { modulus: modulus as u32, width, digits })
}

/// `φ(n)`: the residue mode 0 holds after the navigator reads the numeral `n` from rest at the
/// hand one, by its own digit law `R_j ← R_((j + s) mod w) + θ_j[b]` (none where a byte is not
/// located).
fn residue_of(numeral: &[u8], ring: &Joined, s: usize) -> Option<u64> {
    let q = u64::from(ring.modulus);
    let mut r = vec![0u64; ring.width];
    for b in numeral {
        let at = ring.digits.binary_search_by_key(b, |(d, _)| *d).ok()?;
        r.rotate_left(s % ring.width);
        for (v, &t) in r.iter_mut().zip(&ring.digits[at].1) {
            *v = (*v + u64::from(t)) % q;
        }
    }
    Some(r[0])
}

/// The hands of one operator located by closure: at each located ring of prime `p`, the rows
/// `(φ(x), φ(y), φ(z))` of its calculations have a kernel modulo `p` of one line whose first entry
/// is a unit; read at the gauge one, it is lifted to the ring's modulus while the rows close
/// (refused where they stop closing first), and the rings' lines are joined: `(e_∘, e_=)`.
fn hands_of(rows: &[[u64; 3]], rings: &[Located]) -> std::result::Result<(u32, u32), &'static str> {
    let mut op = Vec::with_capacity(rings.len());
    let mut equals = Vec::with_capacity(rings.len());
    for ring in rings {
        let (p, m) = (ring.prime, i128::from(ring.modulus));
        let integer: Vec<Vec<i128>> = rows.iter().map(|row| row.iter().map(|&v| i128::from(v) % m).collect()).collect();
        let line = kernel_line(&integer, p as u64, 3).ok_or("no_single_line")?;
        if line[0] % p == 0 {
            return Err("a_line_without_a_unit_first_entry");
        }
        let unit = inverse_mod(line[0], p);
        let line: Vec<i128> = line.iter().map(|&v| (v * unit).rem_euclid(p)).collect();
        let (x, lift) = lifted(&integer, &line, p as u64, valuation(&BigInt::from(m), p as u64));
        if lift != m {
            return Err("the_rows_stop_closing_below_the_ring_modulus");
        }
        let unit = inverse_mod(x[0], m);
        op.push(((x[1] * unit).rem_euclid(m), m));
        equals.push(((x[2] * unit).rem_euclid(m), m));
    }
    Ok((chinese(&op).0 as u32, chinese(&equals).0 as u32))
}

/// Each operator of the menu with its count of calculations and its located hands, ascending by
/// byte, and `=`'s hand where every located operator's line agrees on it (none otherwise).
struct Hands {
    operators: Vec<(u8, usize, std::result::Result<(u32, u32), &'static str>)>,
    equals: std::result::Result<u32, &'static str>,
}

impl Hands {
    /// The navigator's hand table: the located operators, and `=` where its hand is located.
    fn table(&self) -> Vec<(u8, u32)> {
        let mut out: Vec<(u8, u32)> = self.operators.iter().filter_map(|(b, _, h)| h.as_ref().ok().map(|&(e, _)| (*b, e))).collect();
        if let Ok(e) = self.equals {
            out.push((b'=', e));
        }
        out.sort_unstable();
        out
    }
}

fn located_hands(calculations: &[(u8, [&[u8]; 3])], ring: &Joined, rings: &[Located], s: usize) -> Hands {
    let mut rows: std::collections::BTreeMap<u8, Vec<[u64; 3]>> = std::collections::BTreeMap::new();
    for (op, numerals) in calculations {
        let read: Option<Vec<u64>> = numerals.iter().map(|n| residue_of(n, ring, s)).collect();
        if let Some(read) = read {
            rows.entry(*op).or_default().push([read[0], read[1], read[2]]);
        }
    }
    let operators: Vec<(u8, usize, std::result::Result<(u32, u32), &'static str>)> = rows
        .iter()
        .map(|(&op, rows)| {
            let unit = |v: u32| gcd(u64::from(v), u64::from(ring.modulus)) == 1;
            let hands = hands_of(rows, rings).and_then(|(e, f)| if unit(e) && unit(f) { Ok((e, f)) } else { Err("a_hand_that_is_not_a_unit") });
            (op, rows.len(), hands)
        })
        .collect();
    let mut agreed: Vec<u32> = operators.iter().filter_map(|(_, _, h)| h.as_ref().ok().map(|&(_, f)| f)).collect();
    agreed.sort_unstable();
    agreed.dedup();
    let equals = match agreed[..] {
        [f] => Ok(f),
        [] => Err("no_located_operator"),
        _ => Err("the_operators_disagree"),
    };
    Hands { operators, equals }
}

/// The navigator on the first level from mode `first`, each class's word its unit's bytes.
fn founded_navigator(declaration: &TowerDeclaration, pieces: &[&[u8]], ring: &Joined, first: usize, s: usize, hands: Vec<(u8, u32)>) -> std::result::Result<Navigator, String> {
    let words = pieces.iter().map(|p| p.to_vec()).collect();
    Navigator::new(declaration, 0, first, ring.modulus, ring.width, s % ring.width, ring.digits.clone(), hands, words).map_err(|e| e.to_string())
}

/// A byte as it reads: itself where it is printable ASCII, else its hexadecimal.
fn shown(b: u8) -> String {
    if b.is_ascii_graphic() { (b as char).to_string() } else { format!("0x{b:02x}") }
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
    let (turned, navigated, handed) = match args[13].as_str() {
        "modulated" => (true, false, false),
        "free" => (false, false, false),
        "captured" => (true, true, true),
        "numeral" => (true, true, false),
        _ => return Err("LAW is modulated (the rings step and turn), free (they step alone), captured (modulated, with the navigator and its located hands) or numeral (modulated, with the navigator and no hand)".into()),
    };
    let out = Path::new(&args[14]);
    if out.exists() {
        return Err("OUT exists: the learner is written create-new".into());
    }
    let loops = loops_of(&text);
    if loops.is_empty() {
        return Err("the text closes no calculation's loop".into());
    }
    let bytes = bytes_of(&loops);
    println!("ROTOR_MENU loops={} bytes={} period={period} columns={}", loops.len(), bytes.len(), period * bytes.len());
    // Each step's closure; the step whose torsion carries the most, the smaller of a tie.
    let mut best: Option<(usize, BigInt, Vec<Vec<i128>>, Closure)> = None;
    for s in 0..period {
        let rows = rows_of(&loops, &bytes, s, period);
        let c = closure(&rows);
        let product = carried(&c);
        let torsion: Vec<String> = c.torsion.iter().map(|(p, fall)| format!("{p}:{fall}")).collect();
        println!(
            "ROTOR_CLOSURE step={s} rows={} rank={} minor_bits={} torsion={} carried={product} elapsed_ms={}",
            c.rows,
            c.rank,
            c.minor.bits(),
            if torsion.is_empty() { "none".to_string() } else { torsion.join(",") },
            started.elapsed().as_millis()
        );
        if best.as_ref().is_none_or(|(_, b, _, _)| product > *b) {
            best = Some((s, product, rows, c));
        }
    }
    let (s, product, rows, c) = best.expect("a step was read");
    let mut rings = Vec::new();
    for (p, fall, ring) in located(&rows, &c, bytes.len(), period) {
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
    let mut tower = Tower::found_on(declaration, &keys, TurnLadder::Fixed).map_err(|e| e.to_string())?;
    tower.join_rotor(rotor).map_err(|e| e.to_string())?;
    let named: Vec<String> = rings.iter().map(|r| format!("{}:{}", r.modulus, r.width)).collect();
    if navigated {
        let ring = joined(&rings, &bytes, period).map_err(|why| format!("no navigator is founded: {why}"))?;
        let calculations = calculations_of(&text);
        let hands = located_hands(&calculations, &ring, &rings, s);
        println!(
            "NAVIGATOR_MENU modulus={} width={} step={} calculations={} operators={} elapsed_ms={}",
            ring.modulus,
            ring.width,
            s % ring.width,
            calculations.len(),
            hands.operators.len(),
            started.elapsed().as_millis()
        );
        for (op, n, h) in &hands.operators {
            match h {
                Ok((e, f)) => println!("NAVIGATOR_HAND byte={} calculations={n} hand={e} equals={f}", shown(*op)),
                Err(why) => println!("NAVIGATOR_HAND byte={} calculations={n} refused={why}", shown(*op)),
            }
        }
        match hands.equals {
            Ok(f) => println!("NAVIGATOR_EQUALS hand={f}"),
            Err(why) => println!("NAVIGATOR_EQUALS refused={why}"),
        }
        let table = if handed { hands.table() } else { Vec::new() };
        let navigator = founded_navigator(&declaration, &pieces, &ring, moving, s, table.clone())?;
        tower.join_navigator(navigator).map_err(|e| e.to_string())?;
        let held: Vec<String> = table.iter().map(|&(b, e)| format!("{}:{e}", shown(b))).collect();
        println!(
            "NAVIGATOR_FOUNDED law={} level=0 first={moving} written={} hands={} elapsed_ms={}",
            args[13],
            2 * ring.width,
            if held.is_empty() { "none".to_string() } else { held.join(",") },
            started.elapsed().as_millis()
        );
    }
    let written = TowerLearner::new(tower, rate_bits).to_text().into_bytes();
    write_new(out, &written)?;
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

    /// The calculations of whole numerals close, a difference read as the sum it inverts; a
    /// decimal, a negative result or an open calculation is not a loop.
    #[test]
    fn the_menu_is_the_whole_calculations() {
        let text = b"x <<12+7=19>> y <<40-15=25>> z <<1.5+2=3.5>> <<3-5=-2>> <<4*2=8>> <<9+1=10";
        let loops = loops_of(text);
        assert_eq!(loops, vec![[&b"19"[..], b"12", b"7"], [&b"40"[..], b"15", b"25"]]);
    }

    /// A menu of 400 sums and their differences.
    fn menu_text() -> Vec<u8> {
        let mut text = Vec::new();
        let mut x = 7u64;
        for _ in 0..400 {
            x = x * 48271 % 2147483647;
            let (a, b) = (x % 9973, (x / 7) % 997);
            text.extend_from_slice(format!("<<{a}+{b}={}>> <<{}-{b}={a}>>\n", a + b, a + b).as_bytes());
        }
        text
    }

    /// Over enough loops, the tenfold step closes them modulo every prime of `9999`, the half step
    /// modulo those of `99`, and the still step modulo 3 alone (the digit sum).
    #[test]
    fn the_tenfold_step_carries_the_most_torsion() {
        let text = menu_text();
        let loops = loops_of(&text);
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
        let text = menu_text();
        let loops = loops_of(&text);
        let bytes = bytes_of(&loops);
        assert_eq!(bytes, b"0123456789".to_vec());
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
        let text = menu_text();
        let loops = loops_of(&text);
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
        let mut readings: Vec<(Vec<usize>, u64)> = loops.iter().flatten().map(|n| (n.iter().map(|b| usize::from(b - b'0')).collect(), std::str::from_utf8(n).expect("digits").parse().expect("a numeral"))).collect();
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

    /// The navigator's menu: any one byte but `=` between two whole numerals, then `=` and a whole
    /// numeral; a decimal, a second `=` or an open calculation is not one.
    #[test]
    fn the_calculations_hold_any_operator_between_whole_numerals() {
        let text = b"<<12+7=19>> <<6*7=42>> <<8/2=4>> <<3=4=7>> <<1.5+2=3.5>> <<5x2=10>> <<9-1=8";
        let found = calculations_of(text);
        let expected: Vec<(u8, [&[u8]; 3])> = vec![(b'+', [b"12", b"7", b"19"]), (b'*', [b"6", b"7", b"42"]), (b'/', [b"8", b"2", b"4"]), (b'x', [b"5", b"2", b"10"])];
        assert_eq!(found, expected);
    }

    /// The menu of [`menu_text`] with as many products, and the navigator's ring joined from its
    /// located rings: modulo 9999 over four modes.
    fn navigator_ring() -> (Vec<u8>, Joined, Vec<Located>, Vec<u8>) {
        let mut text = menu_text();
        let mut x = 11u64;
        for _ in 0..400 {
            x = x * 48271 % 2147483647;
            let (a, b) = (x % 997, (x / 13) % 97);
            text.extend_from_slice(format!("<<{a}*{b}={}>>\n", a * b).as_bytes());
        }
        let loops = loops_of(&text);
        let bytes = bytes_of(&loops);
        let rows = rows_of(&loops, &bytes, 1, 4);
        let mut rings: Vec<Located> = located(&rows, &closure(&rows), bytes.len(), 4).into_iter().map(|(_, _, r)| r.expect("a located ring")).collect();
        rings.sort_by_key(|r| r.modulus);
        let ring = joined(&rings, &bytes, 4).expect("joined");
        (text, ring, rings, bytes)
    }

    /// The joined ring is the tenfold character modulo 9999, and the hands are located by closure:
    /// `+` at one and `-` at minus one, `=` at minus one where both agree, and the product at none
    /// (its rows' kernel modulo 3 is not one line).
    #[test]
    fn the_hands_are_located_by_closure() {
        let (text, ring, rings, _) = navigator_ring();
        assert_eq!((ring.modulus, ring.width), (9999, 4));
        for (b, turns) in &ring.digits {
            let d = u32::from(b - b'0');
            assert_eq!(turns, &vec![d, 10 * d, 100 * d, 1000 * d], "digit {d}");
        }
        assert_eq!(residue_of(b"4321", &ring, 1), Some(4321));
        let hands = located_hands(&calculations_of(&text), &ring, &rings, 1);
        let found: Vec<(u8, usize, Option<(u32, u32)>)> = hands.operators.iter().map(|(b, n, h)| (*b, *n, h.as_ref().ok().copied())).collect();
        assert_eq!(found, vec![(b'*', 400, None), (b'+', 400, Some((1, 9998))), (b'-', 400, Some((9998, 9998)))]);
        assert_eq!(hands.equals, Ok(9998));
        assert_eq!(hands.table(), vec![(b'+', 1), (b'-', 9998), (b'=', 9998)]);
    }

    /// The equation at the consumer: from rest, through units of one byte and of several,
    /// `<<a∘b=` leaves `K_j = 10^j (a + e_∘ b)` modulo 9999, the result `c` then
    /// `K_j + R_j = 10^j (a + e_∘ b − c)`, zero exactly for every sum and difference of the menu
    /// and one character off where the result is one more. With no hand (the law `numeral`) the
    /// operator restarts: after `<<a+b`, `K` is zero and `R` holds `b` alone.
    #[test]
    fn the_fold_is_the_calculation() {
        let (text, ring, rings, _) = navigator_ring();
        let hands = located_hands(&calculations_of(&text), &ring, &rings, 1).table();
        let mut pieces: Vec<Vec<u8>> = b"0123456789+-*=<> \n".iter().map(|&b| vec![b]).collect();
        pieces.extend([b"<<".to_vec(), b">>".to_vec(), b"12".to_vec(), b"+3".to_vec(), b"=4".to_vec(), b"00".to_vec()]);
        let refs: Vec<&[u8]> = pieces.iter().map(Vec::as_slice).collect();
        let declaration = TowerDeclaration { alphabet: pieces.len(), width: 1, modes: 8, contacts: 1, levels: 1, gated: false, turned: false, pumped: false, contact: ContactLaw::Rectifying };
        let captured = founded_navigator(&declaration, &refs, &ring, 0, 1, hands).expect("navigator");
        let numeral = founded_navigator(&declaration, &refs, &ring, 0, 1, Vec::new()).expect("navigator");
        // The longest unit at each place, and the residues after the text is heard from rest.
        let units = |text: &[u8]| -> Vec<usize> {
            let mut out = Vec::new();
            let mut i = 0;
            while i < text.len() {
                let u = (0..pieces.len()).filter(|&u| text[i..].starts_with(&pieces[u])).max_by_key(|&u| pieces[u].len()).expect("a unit");
                out.push(u);
                i += pieces[u].len();
            }
            out
        };
        let heard = |nav: &Navigator, text: &[u8]| -> Vec<u32> {
            let (mut residues, mut hand) = (vec![0u32; 8], 1u32);
            for u in units(text) {
                nav.heard(&mut residues, &mut hand, u).expect("heard");
            }
            residues
        };
        let character = |n: i64| -> Vec<u32> { (0..4).map(|j| (n * 10i64.pow(j)).rem_euclid(9999) as u32).collect() };
        let closed = |r: &[u32]| -> Vec<u32> { (0..4).map(|j| (r[j] + r[4 + j]) % 9999).collect() };
        let mut read = 0;
        for (op, [a, b, c]) in calculations_of(&text).into_iter().filter(|(op, _)| *op != b'*') {
            let n = |v: &[u8]| -> i64 { std::str::from_utf8(v).expect("digits").parse().expect("a numeral") };
            let e = if op == b'+' { 1 } else { -1 };
            let opened = [&b"<<"[..], a, &[op], b, b"="].concat();
            assert_eq!(heard(&captured, &opened)[..4], character(n(a) + e * n(b))[..], "{}", String::from_utf8_lossy(&opened));
            assert_eq!(closed(&heard(&captured, &[&opened[..], c].concat())), vec![0; 4]);
            let wrong = (n(c) + 1).to_string();
            assert_eq!(closed(&heard(&captured, &[&opened[..], wrong.as_bytes()].concat())), character(-1));
            let unhanded = heard(&numeral, &[&b"<<"[..], a, &[op], b].concat());
            assert_eq!(unhanded, [vec![0; 4], character(n(b))].concat());
            read += 1;
        }
        assert_eq!(read, 800);
        // A unit of several bytes folds within itself: `12+3=4` read as `12`, `+3`, `=4`.
        assert_eq!(units(b"12+3=4"), vec![20, 21, 22]);
        assert_eq!(closed(&heard(&captured, b"12+3=4")), character(11));
    }
}
