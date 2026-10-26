//! [definition; agent-inferred with the mathematics thread, October 26] **The rotor's step located
//! by loop closure** ([`holonics::hnn::tower::Rotor`]; the record
//! `2026-10-26_THE_GENERATOR_AND_THE_MODULATOR_ARE_ONE_MOVE_AND_THE_PLACE_DECIDES_WHICH_SO_A_RING_COPRIME_TO_TEN_NEEDS_A_ROTOR.md`,
//! §11). The step `σ` is an integer key in `ℤ/4`: a winding, which no descent reaches, since any
//! relaxed path between two steps passes through mixtures of modes. It is located the Bombe's way,
//! by the loops a menu of contacts closes.
//!
//! **The menu** is the training text's own calculations, `<<a+b=c>>` and `<<a-b=c>>` of whole
//! numerals, each a loop `left = first + second` (`c = a + b`, `a = b + c`). The markup is received
//! material, a landmark: it says where to look, never what to find. No value of a numeral enters the
//! rows; only which byte stands at which place.
//!
//! **The rows.** Under a step `s` for every byte of a numeral, a turn a byte puts on mode `m` of a
//! ring of four reaches mode `m − s·k` after the `k` bytes read after it. So the phase the numeral
//! leaves on mode `j` is `φ_j = Σ_i θ_((j + s·k_i) mod 4)[b_i]`, with `θ_m[b]` the unknown turn the
//! byte `b` puts on mode `m` and `k_i` the bytes after the `i`-th. Each loop and each mode `j` is one
//! integer row, `φ_j(left) − φ_j(first) − φ_j(second) = 0`, over the columns `(m, b)`.
//!
//! **The key.** A turn modulo `p` closes every loop exactly where the rows' rank modulo `p` falls
//! below their rank over the rationals: the system's torsion, located as the ring closure locates it
//! (`tower_ring`'s `rational_rank`, `readable_primes`, `echelon_mod`). The step is the `s` whose
//! torsion carries the most: the largest product of its torsion primes, the smaller `s` of a tie
//! (`s` and `4 − s` read the numeral backwards, a gauge pair). Mode `j` holding the character
//! `10^j` closes every loop for `s = 1` modulo every prime of `9999 = 3²·11·101`; `s = 2` holds only
//! `99 = 3²·11` and `s = 0`, the digit sum, only `9`. Those are the readings this command reports,
//! not inputs to it: the torsion is the rows' own.
//!
//! **The units.** A unit is read whole, so it steps by the sum of its bytes' steps: `s` times the
//! count of its bytes the menu located, modulo 4. Bytes the menu never meets keep the opening, 0. The
//! first level steps; the levels above hold still (the capture holds the operand there).
//!
//! `found-unit-rotor-tower UNITS UNITS_SHA TRAIN TRAIN_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS
//! RATE_BITS OUT` founds the pumped pair-contact tower exactly as `train-unit-pair-pumped-tower`
//! founds it, joins the located rotor, and writes the rested learner (create-new) for that command's
//! `FROM`.
use super::tower_ring::{echelon_mod, rational_rank, readable_primes};
use super::tower_train::{count, positive};
use super::*;
use holonics::hnn::tower::{ContactLaw, Rotor, Tower, TowerDeclaration, TowerLearner, TurnLadder, ROTOR_RING};
use holonics::hnn::units::Units;
use num_bigint::BigInt;
use num_traits::Signed;

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

/// The closure rows under the step `s`, one a loop and a final mode, over the columns `(m, b)`
/// (`m · bytes.len()` plus the byte's place in `bytes`), deduplicated.
fn rows_of(loops: &[[&[u8]; 3]], bytes: &[u8], s: usize) -> Vec<Vec<i128>> {
    let width = bytes.len();
    let mut rows: Vec<Vec<i128>> = Vec::with_capacity(loops.len() * ROTOR_RING);
    for numerals in loops {
        for j in 0..ROTOR_RING {
            let mut row = vec![0i128; ROTOR_RING * width];
            for (numeral, sign) in numerals.iter().zip([1i128, -1, -1]) {
                for (i, b) in numeral.iter().enumerate() {
                    let after = numeral.len() - 1 - i;
                    let m = (j + s * after) % ROTOR_RING;
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

/// One step's closure: the rows' rank over the rationals, the bits of its certified minor, and the
/// primes at which the rank falls, each with its fall.
struct Closure {
    rows: usize,
    rank: usize,
    minor_bits: u64,
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
    Closure { rows: rows.len(), rank, minor_bits: minor.bits(), torsion }
}

/// The product of a closure's torsion primes, each once.
fn carried(c: &Closure) -> BigInt {
    c.torsion.iter().map(|&(p, _)| BigInt::from(p)).product()
}

pub(super) fn found_unit_rotor_tower(args: &[String]) -> Result<()> {
    if args.len() != 13 {
        return Err("found-unit-rotor-tower UNITS UNITS_SHA TRAIN TRAIN_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS RATE_BITS OUT".into());
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
    let out = Path::new(&args[12]);
    if out.exists() {
        return Err("OUT exists: the learner is written create-new".into());
    }
    let loops = loops_of(&text);
    if loops.is_empty() {
        return Err("the text closes no calculation's loop".into());
    }
    let mut bytes: Vec<u8> = loops.iter().flatten().flat_map(|n| n.iter().copied()).collect();
    bytes.sort_unstable();
    bytes.dedup();
    println!("ROTOR_MENU loops={} bytes={} columns={}", loops.len(), bytes.len(), ROTOR_RING * bytes.len());
    // Each step's closure; the step whose torsion carries the most, the smaller of a tie.
    let mut best: Option<(usize, BigInt)> = None;
    for s in 0..ROTOR_RING {
        let c = closure(&rows_of(&loops, &bytes, s));
        let product = carried(&c);
        let torsion: Vec<String> = c.torsion.iter().map(|(p, fall)| format!("{p}:{fall}")).collect();
        println!(
            "ROTOR_CLOSURE step={s} rows={} rank={} minor_bits={} torsion={} carried={product} elapsed_ms={}",
            c.rows,
            c.rank,
            c.minor_bits,
            if torsion.is_empty() { "none".to_string() } else { torsion.join(",") },
            started.elapsed().as_millis()
        );
        if best.as_ref().is_none_or(|(_, b)| product > *b) {
            best = Some((s, product));
        }
    }
    let (s, product) = best.expect("four steps were read");
    // A unit steps by the sum of its bytes' steps; the levels above the first hold still.
    let rings = declaration.modes / ROTOR_RING;
    let mut steps = vec![0u8; declaration.levels * declaration.alphabet * rings];
    let mut stepping = 0usize;
    for u in 0..declaration.alphabet {
        let located = units.piece(u).iter().filter(|b| bytes.binary_search(b).is_ok()).count();
        let sigma = (s * located % ROTOR_RING) as u8;
        stepping += (sigma != 0) as usize;
        steps[u * rings..(u + 1) * rings].fill(sigma);
    }
    let rotor = Rotor::new(&declaration, steps).map_err(|e| e.to_string())?;
    let mut tower = Tower::found_on(declaration, &keys, TurnLadder::Fixed).map_err(|e| e.to_string())?;
    tower.join_rotor(rotor).map_err(|e| e.to_string())?;
    let written = TowerLearner::new(tower, rate_bits).to_text().into_bytes();
    write_new(out, &written)?;
    println!(
        "ROTOR_FOUNDED step={s} carried={product} units={} stepping_units={stepping} rings={rings} levels_stepped=1 bytes={} sha256={} elapsed_ms={}",
        declaration.alphabet,
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

    /// Over enough loops, the tenfold step closes them modulo every prime of `9999`, the half step
    /// modulo those of `99`, and the still step modulo 3 alone (the digit sum).
    #[test]
    fn the_tenfold_step_carries_the_most_torsion() {
        let mut text = Vec::new();
        let mut x = 7u64;
        for _ in 0..400 {
            x = x * 48271 % 2147483647;
            let (a, b) = (x % 9973, (x / 7) % 997);
            text.extend_from_slice(format!("<<{a}+{b}={}>> <<{}-{b}={a}>>\n", a + b, a + b).as_bytes());
        }
        let loops = loops_of(&text);
        let mut bytes: Vec<u8> = loops.iter().flatten().flat_map(|n| n.iter().copied()).collect();
        bytes.sort_unstable();
        bytes.dedup();
        let primes = |s: usize| closure(&rows_of(&loops, &bytes, s)).torsion.iter().map(|&(p, _)| p).collect::<Vec<_>>();
        assert_eq!(primes(1), vec![3, 11, 101]);
        assert_eq!(primes(3), vec![3, 11, 101]);
        assert_eq!(primes(2), vec![3, 11]);
        assert_eq!(primes(0), vec![3]);
    }
}
