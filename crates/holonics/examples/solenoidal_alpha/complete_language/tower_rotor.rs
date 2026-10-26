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
//! `found-unit-rotor-tower UNITS UNITS_SHA TRAIN TRAIN_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS
//! RATE_BITS PERIOD LAW OUT` founds the pumped pair-contact tower exactly as
//! `train-unit-pair-pumped-tower` founds it, joins the located rotor (`LAW` is `modulated` or
//! `free`), and writes the rested learner (create-new) for that command's `FROM`.
use super::tower_ring::{echelon_mod, rational_rank, readable_primes};
use super::tower_train::{count, positive};
use super::*;
use holonics::hnn::tower::{ContactLaw, Rotor, RotorRing, Tower, TowerDeclaration, TowerLearner, TurnLadder};
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
    let turned = match args[13].as_str() {
        "modulated" => true,
        "free" => false,
        _ => return Err("LAW is modulated (the rings step and turn) or free (they step alone)".into()),
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
}
