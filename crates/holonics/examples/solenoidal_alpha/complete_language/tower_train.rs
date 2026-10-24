//! The moment tower's exterior commands: train on text over passes, read the held-out partition,
//! release a continuation.
//!
//! [definition; agent-inferred, October 23] The tower (`holonics::hnn::tower`) reads the codec's
//! bytes as its classes. The training text is cut into `S` contiguous streams; a pass walks every
//! stream in sections of `T` bytes, each stream's modes carried from section to section and opened
//! at rest at the pass's start. Each section's covector is the sum of its streams'; its deposit is
//! certified by rereading the section. After each pass the frozen tower reads the held-out text in
//! the same number of streams, and the reading is printed beside the pass. A sample is a fork of
//! the rested tower: it opens at rest, receives the prompt, and releases each byte by an exact draw
//! on its face.
use super::*;
use holonics::hnn::passage::{PassageDeclaration, PassageTree};
use holonics::hnn::tower::{ContactLaw, Tower, TowerDeclaration, TowerFace, TowerLearner, TowerState, READ_BITS};
use holonics::hnn::units::{Units, CODE_BITS};
use holonics::receiver::coupling::coupling;
use num_bigint::BigUint;
use rayon::prelude::*;

/// A learner's state read ceiling, `2^30` bytes.
const STATE_BUDGET: usize = 1 << 30;

pub(super) fn count(s: &str) -> Result<usize> {
    Ok(s.parse::<usize>()?)
}

/// The regions an exterior partition names, in order: question, answer prose, answer numbers,
/// calculation markup.
pub(super) const REGIONS: [&str; 4] = ["Q", "P", "N", "M"];

/// The held-out reading: the frozen tower's code of `classes`, cut into `streams` contiguous
/// parts, each read from rest; per region of `roles` (the coded class's region, the region of its
/// first byte), on `2^(−20)` bits, with the bytes coded (`lengths`, each class's bytes).
fn held_out(tower: &Tower, classes: &[usize], lengths: &[u32], roles: &[u8], streams: usize) -> Result<[(i64, usize); 4]> {
    let chunk = classes.len().div_ceil(streams);
    let starts: Vec<usize> = (0..classes.len()).step_by(chunk).collect();
    let parts: Vec<[(i64, usize); 4]> = starts
        .par_iter()
        .map(|&start| {
            let part = &classes[start..(start + chunk).min(classes.len())];
            let mut state = tower.rest();
            let codes = tower.read_cells(&mut state, part).map_err(|e| e.to_string())?;
            let mut regions = [(0i64, 0usize); 4];
            for (i, code) in codes.into_iter().enumerate() {
                let region = &mut regions[roles[start + i + 1] as usize];
                region.0 += code;
                region.1 += lengths[start + i + 1] as usize;
            }
            Ok(regions)
        })
        .collect::<std::result::Result<_, String>>()?;
    let mut regions = [(0i64, 0usize); 4];
    for part in parts {
        for (r, (code, n)) in part.into_iter().enumerate() {
            regions[r].0 += code;
            regions[r].1 += n;
        }
    }
    Ok(regions)
}

/// [agent-inferred, October 23] The modes' faces over a text, read through a frozen tower in the
/// held-out read's streams (`held_out`): per level and mode, `max |h|` and `Σ |h|²` over the cells;
/// per level and region of `roles` (the region of the class the state predicts next), the cells'
/// `Σ max_k |h_k|²` against `Σ Σ_k |h_k|²`, the largest mode's share of the level's face energy. A
/// reading beside the code, not material: it locates whether a few swollen modes carry a level's
/// face where the code is lost.
pub(super) fn read_tower_faces(args: &[String]) -> Result<()> {
    if args.len() != 8 {
        return Err("read-tower-faces STATE STATE_SHA TEXT TEXT_SHA ROLES ROLES_SHA STREAMS".into());
    }
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let roles = roles_of(&args[5], &args[6], text.len())?;
    let streams = count(&args[7])?;
    let tower = &learner.tower;
    let (levels, modes) = (tower.declaration.levels, tower.declaration.modes);
    // Per level: each mode's max |h|² and Σ|h|², then per region (Σ max_k |h_k|², Σ Σ_k |h_k|², cells),
    // `h` on `2^(−24)`.
    type Faces = Vec<(Vec<(u128, u128)>, [(u128, u128, usize); 4])>;
    let empty = || -> Faces { (0..levels).map(|_| (vec![(0u128, 0u128); modes], [(0u128, 0u128, 0usize); 4])).collect() };
    let chunk = text.len().div_ceil(streams);
    let starts: Vec<usize> = (0..text.len()).step_by(chunk).collect();
    let parts: Vec<Faces> = starts
        .par_iter()
        .map(|&start| {
            let end = (start + chunk).min(text.len());
            let mut state = tower.rest();
            let mut faces = empty();
            for i in start..end.saturating_sub(1) {
                tower.advance(&mut state, text[i] as usize).map_err(|e| e.to_string())?;
                let region = roles[i + 1] as usize;
                for (l, (per_mode, per_region)) in faces.iter_mut().enumerate() {
                    let (mut largest, mut whole) = (0u128, 0u128);
                    let outgrew = || "a face sum outgrew its 128-bit carrier".to_string();
                    for (k, &(re, im)) in state.modes[l].iter().enumerate() {
                        let e = (re.unsigned_abs() as u128).pow(2).checked_add((im.unsigned_abs() as u128).pow(2)).ok_or_else(outgrew)?;
                        per_mode[k].0 = per_mode[k].0.max(e);
                        per_mode[k].1 = per_mode[k].1.checked_add(e).ok_or_else(outgrew)?;
                        largest = largest.max(e);
                        whole = whole.checked_add(e).ok_or_else(outgrew)?;
                    }
                    let r = &mut per_region[region];
                    r.0 = r.0.checked_add(largest).ok_or_else(outgrew)?;
                    r.1 = r.1.checked_add(whole).ok_or_else(outgrew)?;
                    r.2 += 1;
                }
            }
            Ok(faces)
        })
        .collect::<std::result::Result<_, String>>()?;
    let mut faces = empty();
    for part in parts {
        for (l, (per_mode, per_region)) in part.into_iter().enumerate() {
            let outgrew = || "a face sum outgrew its 128-bit carrier";
            for (k, (m, s)) in per_mode.into_iter().enumerate() {
                faces[l].0[k].0 = faces[l].0[k].0.max(m);
                faces[l].0[k].1 = faces[l].0[k].1.checked_add(s).ok_or_else(outgrew)?;
            }
            for (r, (a, b, n)) in per_region.into_iter().enumerate() {
                faces[l].1[r].0 = faces[l].1[r].0.checked_add(a).ok_or_else(outgrew)?;
                faces[l].1[r].1 = faces[l].1[r].1.checked_add(b).ok_or_else(outgrew)?;
                faces[l].1[r].2 += n;
            }
        }
    }
    // `|h|` on `2^(−24)` written on the face's grain `2^(−16)`, as the swell line writes it.
    let unit = |e: u128| e.isqrt() >> (24 - 16);
    let cells: usize = faces.first().map_or(0, |f| f.1.iter().map(|r| r.2).sum());
    for (l, (per_mode, per_region)) in faces.iter().enumerate() {
        let mut order: Vec<usize> = (0..modes).collect();
        order.sort_by_key(|&k| std::cmp::Reverse(per_mode[k].0));
        let top: Vec<String> = order.iter().take(8).map(|&k| format!("{k}:{}/{}", unit(per_mode[k].0), unit(per_mode[k].1 / cells.max(1) as u128))).collect();
        let mut shares = Vec::with_capacity(REGIONS.len());
        for (name, &(a, b, _)) in REGIONS.iter().zip(per_region) {
            let permille = if b == 0 { 0 } else { a.checked_mul(1000).ok_or("a face share outgrew its 128-bit carrier")? / b };
            shares.push(format!("{name}={permille}"));
        }
        println!("TOWER_FACES level={l} cells={cells} largest_share_permille {} top_modes(mode:max/rms, 2^-16) {}", shares.join(" "), top.join(" "));
    }
    Ok(())
}

/// `Q=… P=… N=… M=…`: bits a byte per region.
/// `read-tower-pair STATE STATE_SHA`: where a pair tower's bilinear weight sits
/// ([`Tower::bilinear_rungs`]), each level's weight on the founded memory rungs of the two drives'
/// modes, in thousandths of the level's whole (`TOWER_PAIR_RUNGS`, the first drive's rung by row),
/// and its three parts with the ladder's upper half as the held rungs and its lower half as the
/// fast (agent-inferred: the halves of the declared ladder, no cut chosen from the material):
/// held × fast (both orders), fast × fast and held × held (`TOWER_PAIR`).
pub(super) fn read_tower_pair(args: &[String]) -> Result<()> {
    if args.len() != 3 {
        return Err("read-tower-pair STATE STATE_SHA".into());
    }
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let levels = learner.tower.bilinear_rungs().map_err(|e| e.to_string())?;
    let thousandths = |part: &BigUint, whole: &BigUint| -> String {
        if *whole == BigUint::from(0u32) { "0".into() } else { ((part * 1000u32 + whole / 2u32) / whole).to_string() }
    };
    for (l, e) in levels.iter().enumerate() {
        let rungs = e.len();
        let whole: BigUint = e.iter().flatten().sum();
        let held = |s: usize| 2 * s >= rungs;
        let part = |keep: &dyn Fn(usize, usize) -> bool| -> BigUint {
            (0..rungs).flat_map(|s| (0..rungs).map(move |t| (s, t))).filter(|&(s, t)| keep(s, t)).map(|(s, t)| e[s][t].clone()).sum()
        };
        let held_fast = part(&|s, t| held(s) != held(t));
        let fast_fast = part(&|s, t| !held(s) && !held(t));
        let held_held = part(&|s, t| held(s) && held(t));
        println!(
            "TOWER_PAIR level={l} rungs={rungs} held_from_rung={} held_x_fast={} fast_x_fast={} held_x_held={} whole_bits={}",
            rungs.div_ceil(2),
            thousandths(&held_fast, &whole),
            thousandths(&fast_fast, &whole),
            thousandths(&held_held, &whole),
            whole.bits()
        );
        let rows: Vec<String> = e.iter().map(|row| row.iter().map(|x| thousandths(x, &whole)).collect::<Vec<_>>().join(",")).collect();
        println!("TOWER_PAIR_RUNGS level={l} {}", rows.join(";"));
    }
    Ok(())
}

/// `read-tower-tension STATE STATE_SHA TEXT TEXT_SHA ROLES ROLES_SHA STREAMS`: the tension a frozen
/// tower leaves on a text ([`TensionCell`], the mathematics thread's split of October 24), per
/// region of `roles`, at line starts (the cells read just after a line feed, pooled over the
/// regions) and over the whole, read in the held-out read's streams from rest.
///
/// [agent-inferred, October 24] Each cell `v = (top, 1, quadrature, below, foil, dz)` deposits
/// `v vᵀ` into its region's joint Gram, exact in `i128`; the foil is the quadrature read half a
/// stream away in the same stream, a face of the same medium that is not aligned with the cell's
/// comparison; the region is the exterior reader's own face (one cell of four on, the region of the
/// arriving class), read only here: how much of the tension a face that carried the medium
/// perfectly would bridge, the reference the tower's own faces are read against. Fraction-free elimination of the face block `f̄ = (top, 1)` leaves `d·S` on the
/// covector block, `d` the last pivot, so every reading below is a ratio of exact integers:
/// `tr T` per cell is the Brier score of the faces; `S` is what no readout of `top` bridges;
/// the most opposed class pairs are the most negative `S_ab`; a candidate face's drop is the part
/// of `tr S` its own unread part carries (eliminating its block after the face's).
pub(super) fn read_tower_tension(args: &[String]) -> Result<()> {
    if args.len() != 8 {
        return Err("read-tower-tension STATE STATE_SHA TEXT TEXT_SHA ROLES ROLES_SHA STREAMS".into());
    }
    let started = std::time::Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let roles = roles_of(&args[5], &args[6], text.len())?;
    let streams = count(&args[7])?;
    let tower = &learner.tower;
    let (w, a) = (tower.declaration.width, tower.declaration.alphabet);
    let layout = TensionLayout { w, a };
    let dim = layout.dim();
    let chunk = text.len().div_ceil(streams.max(1));
    let starts: Vec<usize> = (0..text.len()).step_by(chunk).collect();
    // Per stream, each region's upper triangle and `Σ max|v|²`, the bound its carrier must hold.
    let grams: Vec<Vec<(Vec<i128>, u128, usize)>> = starts
        .par_iter()
        .map(|&start| {
            let end = (start + chunk).min(text.len());
            let classes: Vec<usize> = text[start..end].iter().map(|&b| b as usize).collect();
            let mut state = tower.rest();
            let mut cells = Vec::with_capacity(classes.len());
            tower.read_tension(&mut state, &classes, |cell| {
                cells.push(cell);
                Ok(())
            })
            .map_err(|e| e.to_string())?;
            // The four regions, then the line starts.
            let mut regions: Vec<(Vec<i128>, u128, usize)> = (0..5).map(|_| (vec![0i128; dim * dim], 0u128, 0usize)).collect();
            let half = cells.len() / 2;
            let mut v = vec![0i64; dim];
            for (i, cell) in cells.iter().enumerate() {
                let foil = &cells[(i + half) % cells.len()].quadrature;
                layout.fill(&mut v, cell, foil, roles[start + i + 1] as usize);
                let reach = v.iter().map(|x| x.unsigned_abs() as u128).max().unwrap_or(0);
                let start_of_line = classes[i] == b'\n' as usize;
                for part in [roles[start + i + 1] as usize].into_iter().chain(start_of_line.then_some(4)) {
                    let region = &mut regions[part];
                    region.1 = region.1.checked_add(reach * reach).filter(|&b| b < 1u128 << 126).ok_or("a tension Gram outgrew its 128-bit carrier")?;
                    region.2 += 1;
                    for (r, &vi) in v.iter().enumerate() {
                        if vi == 0 {
                            continue;
                        }
                        let row = &mut region.0[r * dim..(r + 1) * dim];
                        for (slot, &vj) in row[r..].iter_mut().zip(&v[r..]) {
                            *slot += vi as i128 * vj as i128;
                        }
                    }
                }
            }
            Ok(regions)
        })
        .collect::<std::result::Result<_, String>>()?;
    // The four regions, the line starts and the whole (the regions' sum).
    let mut parts: Vec<(Vec<i128>, u128, usize)> = (0..6).map(|_| (vec![0i128; dim * dim], 0u128, 0usize)).collect();
    for stream in grams {
        for (r, (g, bound, n)) in stream.into_iter().enumerate() {
            for p in if r < 4 { vec![r, 5] } else { vec![4] } {
                let part = &mut parts[p];
                part.1 = part.1.checked_add(bound).filter(|&b| b < 1u128 << 126).ok_or("a tension Gram outgrew its 128-bit carrier")?;
                part.2 += n;
                for (slot, x) in part.0.iter_mut().zip(&g) {
                    *slot += x;
                }
            }
        }
    }
    println!("TENSION_READ cells={} streams={} dim={dim} read_ms={}", parts[5].2, streams, started.elapsed().as_millis());
    let names = ["prose", "lean", "rust", "digits", "starts", "all"];
    for (p, (g, _, n)) in parts.iter().enumerate() {
        if *n == 0 {
            continue;
        }
        tension_part(&layout, names[p], g, *n, started)?;
    }
    Ok(())
}

/// The joint face of one cell: `top`, the unit, the quadrature, the face below, the foil, the
/// exterior region and the covector, in that order.
struct TensionLayout {
    w: usize,
    a: usize,
}

impl TensionLayout {
    fn dim(&self) -> usize {
        4 * self.w + 5 + self.a
    }
    fn face(&self) -> std::ops::Range<usize> {
        0..self.w + 1
    }
    fn quadrature(&self) -> std::ops::Range<usize> {
        self.w + 1..2 * self.w + 1
    }
    fn below(&self) -> std::ops::Range<usize> {
        2 * self.w + 1..3 * self.w + 1
    }
    fn foil(&self) -> std::ops::Range<usize> {
        3 * self.w + 1..4 * self.w + 1
    }
    fn region(&self) -> std::ops::Range<usize> {
        4 * self.w + 1..4 * self.w + 5
    }
    fn covector(&self) -> std::ops::Range<usize> {
        4 * self.w + 5..self.dim()
    }
    fn fill(&self, v: &mut [i64], cell: &holonics::hnn::tower::TensionCell, foil: &[i32], region: usize) {
        let w = self.w;
        for j in 0..w {
            v[j] = cell.top[j] as i64;
            v[w + 1 + j] = cell.quadrature[j] as i64;
            v[2 * w + 1 + j] = cell.below[j] as i64;
            v[3 * w + 1 + j] = foil[j] as i64;
        }
        v[w] = 1;
        for (k, slot) in v[4 * w + 1..4 * w + 5].iter_mut().enumerate() {
            *slot = (k == region) as i64;
        }
        v[4 * w + 5..].copy_from_slice(&cell.covector);
    }
}

/// A symmetric matrix kept by its upper rows, `rows[i][j − i]`.
struct Upper {
    rows: Vec<Vec<num_bigint::BigInt>>,
}

impl Upper {
    fn from_gram(g: &[i128], dim: usize) -> Self {
        Self { rows: (0..dim).map(|i| (i..dim).map(|j| num_bigint::BigInt::from(g[i * dim + j])).collect()).collect() }
    }
    fn get(&self, i: usize, j: usize) -> &num_bigint::BigInt {
        if i <= j { &self.rows[i][j - i] } else { &self.rows[j][i - j] }
    }

    /// Fraction-free (Bareiss) elimination of `pivots` in order, over the entries whose indices are
    /// both live (the pivots not yet eliminated and `keep`), skipping a pair `thin` names; `last`
    /// is the last pivot before. A zero pivot of a positive semidefinite matrix has a zero row and
    /// is passed over (refused otherwise). Returns the last pivot and the pivots that were not zero.
    fn eliminate(&mut self, pivots: &[usize], keep: &[usize], mut last: num_bigint::BigInt, thin: &(dyn Fn(usize, usize) -> bool + Sync)) -> Result<(num_bigint::BigInt, usize)> {
        use num_traits::Zero;
        let dim = self.rows.len();
        let mut live = vec![false; dim];
        for &i in pivots.iter().chain(keep) {
            live[i] = true;
        }
        let mut rank = 0;
        for &p in pivots {
            live[p] = false;
            let pivot = self.get(p, p).clone();
            let column: Vec<num_bigint::BigInt> = (0..dim).map(|i| if live[i] { self.get(i, p).clone() } else { num_bigint::BigInt::zero() }).collect();
            if pivot.is_zero() {
                if column.iter().any(|x| !x.is_zero()) {
                    return Err("a zero pivot with a nonzero row: the Gram is not positive semidefinite".into());
                }
                continue;
            }
            rank += 1;
            let live_ref = &live;
            self.rows.par_iter_mut().enumerate().filter(|(i, _)| live_ref[*i]).for_each(|(i, row)| {
                for (k, slot) in row.iter_mut().enumerate() {
                    let j = i + k;
                    if !live_ref[j] || thin(i, j) {
                        continue;
                    }
                    *slot = (&pivot * &*slot - &column[i] * &column[j]) / &last;
                }
            });
            last = pivot;
        }
        Ok((last, rank))
    }
}

/// `num/den` as a decimal with three places (both nonnegative), or with a sign.
fn thousandths_of(num: &num_bigint::BigInt, den: &num_bigint::BigInt) -> String {
    use num_traits::Signed;
    let milli = (num.abs() * 1000 + den / 2) / den;
    format!("{}{}.{:03}", if num.is_negative() { "-" } else { "" }, &milli / 1000, &milli % 1000)
}

/// A class byte as text.
fn class_name(c: usize) -> String {
    if c < 0x80 { format!("{:?}", c as u8 as char) } else { format!("0x{c:02x}") }
}

fn tension_part(layout: &TensionLayout, name: &str, gram: &[i128], cells: usize, started: std::time::Instant) -> Result<()> {
    use num_bigint::BigInt;
    use num_traits::{One, Signed, Zero};
    let dim = layout.dim();
    let mut m = Upper::from_gram(gram, dim);
    let z = layout.covector();
    let in_z = |i: usize| z.contains(&i);
    // The covector block's trace: `tr T` before any elimination, `d·tr S` after the face's.
    let trace = |m: &Upper| -> BigInt { z.clone().map(|c| m.get(c, c).clone()).sum() };
    // `tr T`, on 2^(−48) a cell.
    let tr_t = trace(&m);
    let unit = BigInt::from(cells) << 48;
    let face: Vec<usize> = layout.face().collect();
    let rest: Vec<usize> = (layout.w + 1..dim).collect();
    let (d, rank) = m.eliminate(&face, &rest, BigInt::one(), &|_, _| false)?;
    let tr_ds = trace(&m);
    // tr S = tr_ds / d.
    let bridged = &tr_t * &d - &tr_ds;
    println!(
        "TENSION part={name} cells={cells} face_rank={rank} brier_T={} tension_S={} bridged_by_readout_permille={} tension_permille={} elapsed_ms={}",
        thousandths_of(&tr_t, &unit),
        thousandths_of(&tr_ds, &(&unit * &d)),
        thousandths_of(&(&bridged * 1000), &(&tr_t * &d)),
        thousandths_of(&(&tr_ds * 1000), &(&tr_t * &d)),
        started.elapsed().as_millis()
    );
    // The most opposed class pairs: the most negative d·S_ab, with S_ab/√(S_aa S_bb).
    let mut pairs: Vec<(BigInt, usize, usize)> = Vec::new();
    for i in z.clone() {
        for j in i + 1..z.end {
            let s = m.get(i, j);
            if s.is_negative() {
                pairs.push((s.clone(), i, j));
            }
        }
    }
    pairs.sort_by(|x, y| x.0.cmp(&y.0));
    let opposed: Vec<String> = pairs
        .iter()
        .take(16)
        .map(|(s, i, j)| {
            let scale = (m.get(*i, *i) * m.get(*j, *j)).sqrt();
            let corr = if scale.is_zero() { "0".into() } else { thousandths_of(s, &scale) };
            format!("{}|{}:{}:{}", class_name(i - z.start), class_name(j - z.start), thousandths_of(s, &(&unit * &d)), corr)
        })
        .collect();
    println!("TENSION_OPPOSED part={name} (a|b:S_ab per cell:correlation) {}", opposed.join(" "));
    // Each class's own tension S_aa per cell, the largest.
    let mut own: Vec<(BigInt, usize)> = z.clone().map(|c| (m.get(c, c).clone(), c - z.start)).collect();
    own.sort_by(|x, y| y.0.cmp(&x.0));
    let own: Vec<String> = own.iter().take(16).map(|(s, c)| format!("{}:{}", class_name(*c), thousandths_of(s, &(&unit * &d)))).collect();
    println!("TENSION_OWN part={name} (a:S_aa per cell) {}", own.join(" "));
    // The candidates: each eliminated after the face, on the covector's diagonal.
    let zs: Vec<usize> = z.clone().collect();
    let thin = |i: usize, j: usize| i != j && in_z(i) && in_z(j);
    let candidates: [(&str, Vec<usize>, Vec<usize>); 5] = [
        ("quadrature", layout.quadrature().collect(), Vec::new()),
        ("below", layout.below().collect(), Vec::new()),
        ("foil", layout.foil().collect(), Vec::new()),
        ("quadrature+below", layout.quadrature().collect(), layout.below().collect()),
        ("region", layout.region().collect(), Vec::new()),
    ];
    for (label, first, second) in candidates {
        let mut c = Upper { rows: m.rows.clone() };
        let pivots: Vec<usize> = first.iter().chain(&second).copied().collect();
        let (d2, rank2) = c.eliminate(&pivots, &zs, d.clone(), &thin)?;
        let tr_after = trace(&c);
        // drop = tr S − tr S_after = tr_ds/d − tr_after/d2.
        let drop = &tr_ds * &d2 - &tr_after * &d;
        let dd = &d * &d2;
        println!(
            "TENSION_CANDIDATE part={name} face={label} novel_rank={rank2} drop={} drop_of_tension_permille={} elapsed_ms={}",
            thousandths_of(&drop, &(&unit * &dd)),
            thousandths_of(&(&drop * 1000 * &d), &(&tr_ds * &dd)),
            started.elapsed().as_millis()
        );
    }
    Ok(())
}


/// `read-tower-floor STATE STATE_SHA TRAIN TRAIN_SHA TRAIN_ROLES TRAIN_ROLES_SHA DEV DEV_SHA
/// DEV_ROLES DEV_ROLES_SHA STREAMS ORDER`: how much of the tension a frozen tower leaves is the
/// text's floor and how much a new face could still carry, read against two exterior references
/// (the mathematics thread's split of October 24): a count model of the last bytes, and the linear
/// face of the last `ORDER` bytes' encodings.
///
/// [agent-inferred, October 24] The count model is an exterior reader, never a face of the
/// machine: the bytes that followed each context of `j ≤ 2·ORDER` bytes in the training text,
/// interpolated from the longest context down (Witten–Bell: a context that has been followed by
/// `n` distinct bytes in `C` arrivals keeps `n/(C + n)` for the order below) to the training
/// text's byte counts, on `2^(−48)` rounded to nearest at each order and read on `2^(−24)`, the
/// covector's grain. On the held-out text it counts the training text; on the training text it
/// counts it with the cell's own arrival deleted (the deleted estimate), so both of its Brier
/// scores are out of sample. Its Brier per region beside the tower's is the first split: what a
/// conjunction of the last bytes knows that the tower does not.
///
/// The second split is read on the training text, whose 1.8 million cells keep a face of a few
/// hundred coordinates from removing more than a thousandth of the tension by chance (the held-out
/// text's twelve thousand cells a medium would let it remove about 2% by chance, the size of the
/// signal). Each cell `v = (top, 1, E(u_t), …, E(u_(t−ORDER+1)), p_ORDER, foil, dz)` deposits
/// `v vᵀ` into one joint Gram, exact in `i128` (the covector's off-diagonal entries are not kept:
/// only its trace and diagonal are read). After the face's elimination the encodings are eliminated
/// one block at a time (the drop of the linear face of the last `k` bytes, what a new mode driven
/// by the encodings could carry), then the count model's prediction (the conjunction past that
/// linear face); separately the count model alone, and the foil (the encoding of the byte half a
/// stream away). Per class, the drops of its own tension `S_aa` say which contrasts a mode could
/// carry and which only a conjunction.
pub(super) fn read_tower_floor(args: &[String]) -> Result<()> {
    if args.len() != 13 {
        return Err("read-tower-floor STATE STATE_SHA TRAIN TRAIN_SHA TRAIN_ROLES TRAIN_ROLES_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA STREAMS ORDER".into());
    }
    let started = std::time::Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let train = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let train_roles = roles_of(&args[5], &args[6], train.len())?;
    let dev = pinned_read(&args[7], &args[8], READ_BUDGET as usize)?;
    let dev_roles = roles_of(&args[9], &args[10], dev.len())?;
    let streams = count(&args[11])?;
    let order = count(&args[12])?;
    if order == 0 || 2 * order > 7 {
        return Err("the reference order must be between one and three (contexts of up to seven bytes are keyed in 64 bits)".into());
    }
    let tower = &learner.tower;
    let (w, a) = (tower.declaration.width, tower.declaration.alphabet);
    let cut = |text: &[u8]| -> Vec<Vec<usize>> {
        let chunk = text.len().div_ceil(streams.max(1));
        text.chunks(chunk).map(|s| s.iter().map(|&b| b as usize).collect()).collect()
    };
    let (train_streams, dev_streams) = (cut(&train), cut(&dev));
    let followers = Followers::count(&train_streams, 2 * order, a);
    println!(
        "FLOOR_COUNTS contexts_per_order={} seen_classes={} counted_ms={}",
        followers.orders.iter().map(|o| o.len().to_string()).collect::<Vec<_>>().join(","),
        followers.seen.len(),
        started.elapsed().as_millis()
    );
    // The Brier scores, per part: the tower's and the count model's at each order. The held-out
    // text is read here; the training text beside its Gram, below.
    let names = ["prose", "lean", "rust", "digits", "starts", "all"];
    let top = 2 * order;
    let chunk = dev_roles.len().div_ceil(streams.max(1));
    let held_out: Vec<BrierParts> = dev_streams
        .par_iter()
        .enumerate()
        .map(|(s, classes)| {
            let mut parts = BrierParts::new(top);
            let mut state = tower.rest();
            let mut ps = vec![vec![0u128; a]; top + 1];
            let mut i = 0usize;
            tower.read_tension(&mut state, classes, |cell| {
                followers.predict(classes, i, false, &mut ps);
                parts.add(&followers, &cell, &ps, classes, i, dev_roles[s * chunk + i + 1] as usize);
                i += 1;
                Ok(())
            })
            .map_err(|e| e.to_string())?;
            Ok(parts)
        })
        .collect::<std::result::Result<_, String>>()?;
    BrierParts::print("held_out", &names, &held_out, started);
    // The joint Gram on the training text, the whole, with the deleted count model's Brier.
    let layout = FloorLayout { w, a, order };
    let dim = layout.dim();
    let chunk = train_roles.len().div_ceil(streams.max(1));
    let grams: Vec<(Vec<i128>, u128, usize, BrierParts)> = train_streams
        .par_iter()
        .enumerate()
        .map(|(s, classes)| {
            let mut gram = vec![0i128; dim * dim];
            let (mut bound, mut n) = (0u128, 0usize);
            let mut parts = BrierParts::new(top);
            let mut state = tower.rest();
            let mut ps = vec![vec![0u128; a]; top + 1];
            let mut v = vec![0i64; dim];
            let mut nz: Vec<usize> = Vec::with_capacity(dim);
            let half = classes.len().saturating_sub(1) / 2;
            let cells = classes.len().saturating_sub(1);
            let cov = layout.covector();
            // The cross moments are kept for the coordinates the eliminations read: every one but
            // the covector of a class that never arrives, whose diagonal alone is kept.
            let mut crossed = vec![true; dim];
            for c in cov.clone() {
                crossed[c] = false;
            }
            for &c in &followers.seen {
                crossed[cov.start + c] = true;
            }
            let mut i = 0usize;
            tower.read_tension(&mut state, classes, |cell| {
                followers.predict(classes, i, true, &mut ps);
                parts.add(&followers, &cell, &ps, classes, i, train_roles[s * chunk + i + 1] as usize);
                let foil = classes[(i + half) % cells.max(1)];
                layout.fill(&mut v, tower, &cell, classes, i, &ps[order], foil);
                let reach = v.iter().map(|x| x.unsigned_abs() as u128).max().unwrap_or(0);
                bound = bound.saturating_add(reach * reach);
                n += 1;
                nz.clear();
                for r in 0..dim {
                    if v[r] == 0 {
                        continue;
                    }
                    if crossed[r] {
                        nz.push(r);
                    } else {
                        gram[r * dim + r] += v[r] as i128 * v[r] as i128;
                    }
                }
                for (x, &r) in nz.iter().enumerate() {
                    let vr = v[r] as i128;
                    let row = &mut gram[r * dim..(r + 1) * dim];
                    if cov.contains(&r) {
                        row[r] += vr * vr;
                        continue;
                    }
                    for &c in &nz[x..] {
                        row[c] += vr * v[c] as i128;
                    }
                }
                i += 1;
                Ok(())
            })
            .map_err(|e| e.to_string())?;
            if bound >= 1u128 << 126 {
                return Err("a floor Gram outgrew its 128-bit carrier".to_string());
            }
            Ok((gram, bound, n, parts))
        })
        .collect::<std::result::Result<_, String>>()?;
    let mut gram = vec![0i128; dim * dim];
    let (mut bound, mut cells) = (0u128, 0usize);
    let mut training = Vec::with_capacity(grams.len());
    for (g, b, n, parts) in grams {
        bound = bound.checked_add(b).filter(|&b| b < 1u128 << 126).ok_or("a floor Gram outgrew its 128-bit carrier")?;
        cells += n;
        for (slot, x) in gram.iter_mut().zip(&g) {
            *slot += x;
        }
        training.push(parts);
    }
    BrierParts::print("training_deleted", &names, &training, started);
    println!("FLOOR_READ cells={cells} streams={streams} dim={dim} read_ms={}", started.elapsed().as_millis());
    floor_chains(&layout, &gram, cells, &followers.seen, started)
}

/// The Brier scores of one stream, per part (the four regions, the line starts, the whole): the
/// tower's (`tr T`, `Σ dz²` on `2^(−48)`), the count model's at each order, and the cells.
struct BrierParts {
    parts: Vec<(i128, Vec<i128>, usize)>,
}

impl BrierParts {
    fn new(top: usize) -> Self {
        Self { parts: (0..6).map(|_| (0i128, vec![0i128; top + 1], 0usize)).collect() }
    }

    /// Cell `i`, read after `classes[i]` at `classes[i + 1]`, of `role` (the arriving class's
    /// region): into its region, the whole, and the line starts when it reads a line feed.
    fn add(&mut self, followers: &Followers, cell: &holonics::hnn::tower::TensionCell, ps: &[Vec<u128>], classes: &[usize], i: usize, role: usize) {
        let target = classes[i + 1];
        let tower: i128 = cell.covector.iter().map(|&x| x as i128 * x as i128).sum();
        let start_of_line = classes[i] == b'\n' as usize;
        for p in [role, 5].into_iter().chain(start_of_line.then_some(4)) {
            let part = &mut self.parts[p];
            part.0 += tower;
            for (slot, prediction) in part.1.iter_mut().zip(ps) {
                *slot += followers.brier(prediction, target);
            }
            part.2 += 1;
        }
    }

    fn print(label: &str, names: &[&str], streams: &[BrierParts], started: std::time::Instant) {
        for (p, name) in names.iter().enumerate() {
            let top = streams.first().map_or(0, |s| s.parts[p].1.len());
            let (mut tower, mut counts, mut n) = (0i128, vec![0i128; top], 0usize);
            for stream in streams {
                tower += stream.parts[p].0;
                for (slot, x) in counts.iter_mut().zip(&stream.parts[p].1) {
                    *slot += x;
                }
                n += stream.parts[p].2;
            }
            if n == 0 {
                continue;
            }
            let unit = num_bigint::BigInt::from(n) << 48;
            let orders: Vec<String> = counts.iter().enumerate().map(|(j, x)| format!("order{j}={}", thousandths_of(&num_bigint::BigInt::from(*x), &unit))).collect();
            println!("FLOOR_BRIER text={label} part={name} cells={n} tower={} {} elapsed_ms={}", thousandths_of(&num_bigint::BigInt::from(tower), &unit), orders.join(" "), started.elapsed().as_millis());
        }
    }
}

/// The bytes that followed each context of a text, per order, and the bytes it contains.
struct Followers {
    /// `orders[j]`: a context of `j` bytes (keyed by its bytes, the last lowest) → the bytes that
    /// followed it with their counts, and their total.
    orders: Vec<std::collections::HashMap<u64, (Vec<(u8, u32)>, u32)>>,
    /// The classes the text contains, the only ones a count gives mass.
    seen: Vec<usize>,
}

impl Followers {
    /// The context of `j` bytes ending at cell `i`.
    fn key(classes: &[usize], i: usize, j: usize) -> u64 {
        classes[i + 1 - j..=i].iter().fold(0u64, |k, &c| (k << 8) | c as u64)
    }

    fn count(streams: &[Vec<usize>], top: usize, a: usize) -> Self {
        let mut orders: Vec<std::collections::HashMap<u64, (Vec<(u8, u32)>, u32)>> = (0..=top).map(|_| std::collections::HashMap::new()).collect();
        for s in streams {
            for i in 0..s.len().saturating_sub(1) {
                let next = s[i + 1] as u8;
                for (j, order) in orders.iter_mut().enumerate().take(top.min(i + 1) + 1) {
                    let entry = order.entry(Self::key(s, i, j)).or_insert_with(|| (Vec::new(), 0));
                    match entry.0.iter_mut().find(|(b, _)| *b == next) {
                        Some(slot) => slot.1 += 1,
                        None => entry.0.push((next, 1)),
                    }
                    entry.1 += 1;
                }
            }
        }
        let seen = orders[0].get(&0).map(|(f, _)| f.iter().map(|&(b, _)| b as usize).filter(|&b| b < a).collect::<Vec<_>>()).unwrap_or_default();
        let mut seen = seen;
        seen.sort_unstable();
        Self { orders, seen }
    }

    /// The count model's prediction after cell `i` at each order `j < ps.len()`, on `2^(−48)`:
    /// `p_0(b) = c(b)/C`; `p_j(b) = (c_j(b) + n_j p_(j−1)(b))/(C_j + n_j)`, the order below where
    /// the context is shorter than `j` or was never followed. `deleted`: the cell's own arrival,
    /// `classes[i + 1]`, is removed from every count it entered.
    fn predict(&self, classes: &[usize], i: usize, deleted: bool, ps: &mut [Vec<u128>]) {
        let target = classes[i + 1];
        for j in 0..ps.len() {
            let (below, here) = ps.split_at_mut(j);
            let here = &mut here[0];
            let found = (i + 1 >= j).then(|| self.orders[j].get(&Self::key(classes, i, j))).flatten();
            let Some((list, total)) = found else {
                match below.last() {
                    Some(prior) => here.copy_from_slice(prior),
                    None => here.fill(0),
                }
                continue;
            };
            let own = if deleted { list.iter().find(|(b, _)| *b as usize == target).map_or(0, |&(_, c)| c) } else { 0 };
            let arrivals = (*total - deleted as u32) as u128;
            let distinct = (list.len() - (deleted && own == 1) as usize) as u128;
            if arrivals == 0 {
                match below.last() {
                    Some(prior) => here.copy_from_slice(prior),
                    None => here.fill(0),
                }
                continue;
            }
            let denom = if j == 0 { arrivals } else { arrivals + distinct };
            for &b in &self.seen {
                let interpolated = if j == 0 { 0 } else { distinct * below[j - 1][b] };
                here[b] = (interpolated + denom / 2) / denom;
            }
            for &(b, c) in list {
                let c = c - (deleted && b as usize == target) as u32;
                let interpolated = if j == 0 { 0 } else { distinct * below[j - 1][b as usize] };
                here[b as usize] = (((c as u128) << 48) + interpolated + denom / 2) / denom;
            }
        }
    }

    /// The Brier score of a prediction on `2^(−48)` read at `target`, on `2^(−48)`:
    /// `Σ q_b² − 2 q_target + 1` with `q` on `2^(−24)`.
    fn brier(&self, p: &[u128], target: usize) -> i128 {
        let q = |b: usize| ((p[b] + (1 << 23)) >> 24) as i128;
        let squares: i128 = self.seen.iter().map(|&b| q(b) * q(b)).sum();
        squares - 2 * (q(target) << 24) + (1i128 << 48)
    }
}

/// The floor reading's joint face of one cell: `top`, the unit, the last `order` encodings, the
/// count model's prediction, the foil and the covector, in that order.
struct FloorLayout {
    w: usize,
    a: usize,
    order: usize,
}

impl FloorLayout {
    fn dim(&self) -> usize {
        self.w + 1 + self.order * self.w + self.a + self.w + self.a
    }
    fn face(&self) -> std::ops::Range<usize> {
        0..self.w + 1
    }
    fn encoding(&self, j: usize) -> std::ops::Range<usize> {
        let s = self.w + 1 + j * self.w;
        s..s + self.w
    }
    fn count(&self) -> std::ops::Range<usize> {
        let s = self.w + 1 + self.order * self.w;
        s..s + self.a
    }
    fn foil(&self) -> std::ops::Range<usize> {
        let s = self.count().end;
        s..s + self.w
    }
    fn covector(&self) -> std::ops::Range<usize> {
        self.foil().end..self.dim()
    }
    #[allow(clippy::too_many_arguments)]
    fn fill(&self, v: &mut [i64], tower: &Tower, cell: &holonics::hnn::tower::TensionCell, classes: &[usize], i: usize, p: &[u128], foil: usize) {
        let w = self.w;
        for (slot, &x) in v[..w].iter_mut().zip(&cell.top) {
            *slot = x as i64;
        }
        v[w] = 1;
        for j in 0..self.order {
            let range = self.encoding(j);
            if i >= j {
                for (slot, &x) in v[range].iter_mut().zip(tower.encoding(classes[i - j])) {
                    *slot = x as i64;
                }
            } else {
                v[range].fill(0);
            }
        }
        for (slot, &x) in v[self.count()].iter_mut().zip(p) {
            *slot = ((x + (1 << 23)) >> 24) as i64;
        }
        for (slot, &x) in v[self.foil()].iter_mut().zip(tower.encoding(foil)) {
            *slot = x as i64;
        }
        v[self.covector()].copy_from_slice(&cell.covector);
    }
}

/// The floor reading's eliminations on the joint Gram: the face, then the chains. The covector and
/// the count model are read on the classes that arrive in the training text (`arriving`): the count
/// model gives no other class mass, and another class's coordinate of the covector is its face's
/// mass alone, whose tension is at most its `T_cc`, printed beside the reading.
fn floor_chains(layout: &FloorLayout, gram: &[i128], cells: usize, arriving: &[usize], started: std::time::Instant) -> Result<()> {
    use num_bigint::BigInt;
    use num_traits::One;
    let dim = layout.dim();
    let z = layout.covector();
    let zs: Vec<usize> = arriving.iter().map(|&c| z.start + c).collect();
    let in_z = |i: usize| z.contains(&i);
    let thin = |i: usize, j: usize| i != j && in_z(i) && in_z(j);
    let unit = BigInt::from(cells) << 48;
    let mut base = Upper::from_gram(gram, dim);
    let diagonal = |m: &Upper| -> Vec<BigInt> { zs.iter().map(|&c| m.get(c, c).clone()).collect() };
    let t_diag = diagonal(&base);
    let tr_t: BigInt = t_diag.iter().sum();
    let tr_t_all: BigInt = z.clone().map(|c| base.get(c, c).clone()).sum();
    println!(
        "FLOOR_CLASSES arriving={} brier_T_all={} brier_T_arriving={} brier_T_never_arriving={}",
        arriving.len(),
        thousandths_of(&tr_t_all, &unit),
        thousandths_of(&tr_t, &unit),
        thousandths_of(&(&tr_t_all - &tr_t), &unit)
    );
    let face: Vec<usize> = layout.face().collect();
    let encodings: Vec<Vec<usize>> = (0..layout.order).map(|j| layout.encoding(j).collect()).collect();
    let count: Vec<usize> = arriving.iter().map(|&c| layout.count().start + c).collect();
    let foil: Vec<usize> = layout.foil().collect();
    let rest: Vec<usize> = encodings.iter().flatten().chain(&count).chain(&foil).chain(&zs).copied().collect();
    let (d, rank) = base.eliminate(&face, &rest, BigInt::one(), &thin)?;
    let s_diag = diagonal(&base);
    let tr_ds: BigInt = s_diag.iter().sum();
    println!(
        "FLOOR part=all cells={cells} face_rank={rank} brier_T={} tension_S={} tension_permille={} elapsed_ms={}",
        thousandths_of(&tr_t, &unit),
        thousandths_of(&tr_ds, &(&unit * &d)),
        thousandths_of(&(&tr_ds * 1000), &(&tr_t * &d)),
        started.elapsed().as_millis()
    );
    let order = layout.order;
    // Each chain: its blocks in order, each eliminated after the ones before, with the labels.
    let mut linear: Vec<(String, Vec<usize>)> = encodings.iter().enumerate().map(|(j, e)| (if j == 0 { "E(u_t)".to_string() } else { format!("+E(u_(t-{j}))") }, e.clone())).collect();
    linear.push((format!("+count{order}"), count.clone()));
    let chains: Vec<(&str, Vec<(String, Vec<usize>)>)> = vec![("linear", linear), ("count", vec![(format!("count{order}"), count.clone())]), ("foil", vec![("E(foil)".to_string(), foil.clone())])];
    // The chains run together, each on its own copy of the face's elimination; each step prints as
    // it closes. Per class: the diagonal after each step of each chain.
    let chained: Vec<Vec<(String, BigInt, Vec<BigInt>)>> = chains
        .into_par_iter()
        .map(|(name, blocks)| {
            let mut m = Upper { rows: base.rows.clone() };
            let mut steps = Vec::new();
            let mut last = d.clone();
            let mut prior = tr_ds.clone();
            let mut prior_d = d.clone();
            for (b, (label, pivots)) in blocks.iter().enumerate() {
                let later: Vec<usize> = blocks[b + 1..].iter().flat_map(|(_, p)| p.iter().copied()).chain(zs.iter().copied()).collect();
                let (d2, rank2) = m.eliminate(pivots, &later, last.clone(), &thin).map_err(|e| e.to_string())?;
                let after = diagonal(&m);
                let tr_after: BigInt = after.iter().sum();
                // drop = prior/prior_d − tr_after/d2; from the face: tr_ds/d − tr_after/d2.
                let drop = &prior * &d2 - &tr_after * &prior_d;
                let total = &tr_ds * &d2 - &tr_after * &d;
                println!(
                    "FLOOR_DROP chain={name} step={label} novel_rank={rank2} drop={} drop_of_tension_permille={} chain_drop_of_tension_permille={} elapsed_ms={}",
                    thousandths_of(&drop, &(&unit * &prior_d * &d2)),
                    thousandths_of(&(&drop * 1000 * &d), &(&tr_ds * &prior_d * &d2)),
                    thousandths_of(&(&total * 1000), &(&tr_ds * &d2)),
                    started.elapsed().as_millis()
                );
                steps.push((format!("{name}:{label}"), d2.clone(), after));
                prior = tr_after;
                prior_d = d2.clone();
                last = d2;
            }
            Ok(steps)
        })
        .collect::<std::result::Result<_, String>>()?;
    let steps: Vec<(String, BigInt, Vec<BigInt>)> = chained.into_iter().flatten().collect();
    // The classes with the most tension: each step's remaining share of the class's own tension.
    let mut own: Vec<(BigInt, usize)> = s_diag.iter().cloned().zip(0..).collect();
    own.sort_by(|x, y| y.0.cmp(&x.0));
    for (s, c) in own.iter().take(24) {
        let shares: Vec<String> = steps
            .iter()
            .map(|(label, d2, after)| format!("{label}={}", thousandths_of(&(&after[*c] * 1000 * &d), &(s * d2))))
            .collect();
        println!("FLOOR_CLASS class={} S_aa={} remaining_permille {}", class_name(arriving[*c]), thousandths_of(s, &(&unit * &d)), shares.join(" "));
    }
    Ok(())
}

pub(super) fn region_line(regions: &[(i64, usize); 4]) -> String {
    REGIONS
        .iter()
        .zip(regions)
        .map(|(name, &(code, n))| format!("{name}={}", per(code, n.max(1))))
        .collect::<Vec<_>>()
        .join(" ")
}

/// An exterior region file: one region index below four for each byte of `bytes`.
pub(super) fn roles_of(path: &str, sha: &str, bytes: usize) -> Result<Vec<u8>> {
    let roles = pinned_read(path, sha, READ_BUDGET as usize)?;
    if roles.len() != bytes || roles.iter().any(|&r| r > 3) {
        return Err("the region file does not name one of four regions for each byte".into());
    }
    Ok(roles)
}

/// `x / 2^20` bits over `n` as thousandths, written `0.xxx`.
/// A signed code on `2^(−20)` bits written in bits.
fn signed_bits(code: i64) -> String {
    format!("{}{}", if code < 0 { "-" } else { "" }, per(code.abs(), 1))
}

pub(super) fn per(code: i64, n: usize) -> String {
    let milli = (code as i128 * 1000 + ((n as i128) << (READ_BITS - 1))) / ((n as i128) << READ_BITS);
    format!("{}.{:03}", milli / 1000, milli % 1000)
}

/// `train-tower` trains the ungated tower, `train-gated-tower` the gated one (its modes' decay keyed by
/// their input), `train-turned-tower` the turned one (its gated modes' turn keyed by their input too),
/// `train-pumped-tower` the pumped one (its turned modes pumped by their input, so a phase can lock),
/// and `train-credited-tower` the gated one whose streams carry their passage credit
/// (`hnn::tower::LevelCredit`), so a section's covector reaches the history its opening carries;
/// `train-pair-pumped-tower` the pumped one whose contacts are pair contacts
/// (`hnn::tower::ContactLaw::Pair`) and `train-pair-linear-pumped-tower` its foil, the pair contact
/// with its bilinear block held at zero. A continued learner must carry the same declaration.
pub(super) fn train(args: &[String], gated: bool, turned: bool, pumped: bool, credit: bool, contact: ContactLaw) -> Result<()> {
    train_looking_or_not(args, gated, turned, pumped, credit, contact, None)
}

/// `train-looking-gated-tower|train-looking-turned-tower|train-looking-pumped-tower LOOK_KEYS
/// LOOK_KEYS_SHA AGREE MOMENT END TRAIN …` trains with the look inside training ([`Looking`]):
/// `MOMENT` and `END` are the bytes at which the terrain asks for a release and ends a line, and
/// `AGREE` the release's agreeing draws; the rest are `train-tower`'s arguments.
pub(super) fn train_looking(args: &[String], gated: bool, turned: bool, pumped: bool) -> Result<()> {
    if args.len() != 23 && args.len() != 25 {
        return Err("train-looking-gated-tower|train-looking-turned-tower|train-looking-pumped-tower LOOK_KEYS LOOK_KEYS_SHA AGREE MOMENT END TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS STREAMS SECTION PASSES RATE_BITS OUT [FROM FROM_SHA]".into());
    }
    let looking = Looking {
        keys: pinned_read(&args[1], &args[2], READ_BUDGET as usize)?,
        agree: agreement(args.get(3))?,
        moment: args[4].parse::<u8>()? as usize,
        end: args[5].parse::<u8>()? as usize,
    };
    if looking.moment == looking.end {
        return Err("a moment and a line's end are different bytes".into());
    }
    let rest: Vec<String> = std::iter::once(args[0].clone()).chain(args[6..].iter().cloned()).collect();
    train_looking_or_not(&rest, gated, turned, pumped, false, ContactLaw::Rectifying, Some(&looking))
}

fn train_looking_or_not(args: &[String], gated: bool, turned: bool, pumped: bool, credit: bool, contact: ContactLaw, looking: Option<&Looking>) -> Result<()> {
    if args.len() != 18 && args.len() != 20 {
        return Err("train-tower|train-gated-tower|train-turned-tower|train-pumped-tower|train-credited-tower TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS STREAMS SECTION PASSES RATE_BITS OUT [FROM FROM_SHA]".into());
    }
    let train = pinned_read(&args[1], &args[2], READ_BUDGET as usize)?;
    let dev = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let roles = roles_of(&args[5], &args[6], dev.len())?;
    let reading = Reading {
        train: train.iter().map(|&b| b as usize).collect(),
        train_lengths: vec![1; train.len()],
        dev: dev.iter().map(|&b| b as usize).collect(),
        dev_lengths: vec![1; dev.len()],
        dev_roles: roles,
        alphabet: 256,
    };
    fit(&args[7..], reading, gated, turned, pumped, credit, contact, looking)
}

/// `train-unit-tower` trains the gated tower on founded units (`hnn::units`): the training and
/// held-out text are read in the units, and each code is reported over the bytes its units decode
/// to.
pub(super) fn train_units(args: &[String]) -> Result<()> {
    if args.len() != 20 && args.len() != 22 {
        return Err("train-unit-tower UNITS UNITS_SHA TRAIN TRAIN_SHA DEV DEV_SHA DEV_ROLES DEV_ROLES_SHA KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS STREAMS SECTION PASSES RATE_BITS OUT [FROM FROM_SHA]".into());
    }
    let units = Units::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], READ_BUDGET as usize)?)?).map_err(|e| e.to_string())?;
    let train = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let dev = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let byte_roles = roles_of(&args[7], &args[8], dev.len())?;
    let read = |bytes: &[u8]| -> Result<(Vec<usize>, Vec<u32>)> {
        let parsed = units.parse(bytes).map_err(|e| e.to_string())?;
        let lengths = parsed.iter().map(|&u| units.piece(u as usize).len() as u32).collect();
        Ok((parsed.into_iter().map(|u| u as usize).collect(), lengths))
    };
    let (train_classes, train_lengths) = read(&train)?;
    let (dev_classes, dev_lengths) = read(&dev)?;
    // Each unit's region is the region of its first byte.
    let mut dev_roles = Vec::with_capacity(dev_classes.len());
    let mut at = 0usize;
    for &n in &dev_lengths {
        dev_roles.push(byte_roles[at]);
        at += n as usize;
    }
    println!(
        "UNIT_READ units={} train_bytes={} train_units={} dev_bytes={} dev_units={}",
        units.len(), train.len(), train_classes.len(), dev.len(), dev_classes.len()
    );
    let reading = Reading { train: train_classes, train_lengths, dev: dev_classes, dev_lengths, dev_roles, alphabet: units.len() };
    fit(&args[9..], reading, true, false, false, false, ContactLaw::Rectifying, None)
}

/// A passage read in a tower's classes: the training and held-out classes, the bytes each class
/// decodes to, and the held-out classes' regions.
struct Reading {
    train: Vec<usize>,
    train_lengths: Vec<u32>,
    dev: Vec<usize>,
    dev_lengths: Vec<u32>,
    dev_roles: Vec<u8>,
    alphabet: usize,
}

/// The passes: `args` are `KEYS KEYS_SHA WIDTH MODES CONTACTS LEVELS STREAMS SECTION PASSES RATE_BITS
/// OUT [FROM FROM_SHA]`.
fn fit(args: &[String], reading: Reading, gated: bool, turned: bool, pumped: bool, credit: bool, contact: ContactLaw, looking: Option<&Looking>) -> Result<()> {
    let started = Instant::now();
    let keys = pinned_read(&args[0], &args[1], READ_BUDGET as usize)?;
    let declaration = TowerDeclaration {
        alphabet: reading.alphabet,
        width: count(&args[2])?,
        modes: count(&args[3])?,
        contacts: count(&args[4])?,
        levels: count(&args[5])?,
        gated,
        turned,
        pumped,
        contact,
    };
    let streams = count(&args[6])?;
    let section = count(&args[7])?;
    let passes = count(&args[8])?;
    let rate_bits: u32 = args[9].parse()?;
    let out = Path::new(&args[10]);
    std::fs::create_dir(out)?;
    let classes = &reading.train;
    if streams == 0 || section == 0 || classes.len() < streams * (section + 1) {
        return Err("the training text must hold one section a stream".into());
    }
    // A run continues a rested learner (its tower and moments) when one is named; its declaration
    // and rate must be the declared ones.
    let mut learner = if args.len() == 13 {
        let from = pinned_read(&args[11], &args[12], STATE_BUDGET)?;
        let learner = TowerLearner::from_text(std::str::from_utf8(&from)?).map_err(|e| e.to_string())?;
        if learner.tower.declaration != declaration || learner.rate_bits != rate_bits {
            return Err("the continued learner's declaration or rate differs from the declared one".into());
        }
        learner
    } else {
        TowerLearner::new(Tower::found(declaration, &keys).map_err(|e| e.to_string())?, rate_bits)
    };
    let chunk = classes.len() / streams;
    let sections_a_pass = (chunk - 1) / section;
    let dev_bytes: usize = reading.dev_lengths.iter().map(|&n| n as usize).sum();
    println!(
        "TOWER_TRAIN material={} streams={} section={} sections_a_pass={} train_bytes={} dev_bytes={}",
        learner.tower.theta.len(),
        streams,
        section,
        sections_a_pass,
        reading.train_lengths.iter().map(|&n| n as usize).sum::<usize>(),
        dev_bytes
    );
    // Each stream releases from its own share of the look's keys, so the releases do not depend on
    // the order the streams are filled in.
    let mut look_keys: Vec<KeyStream> = match looking {
        Some(l) => {
            let share = l.keys.len() / streams / 8 * 8;
            (0..streams).map(|s| KeyStream::new(l.keys[s * share..(s + 1) * share].to_vec(), 8)).collect::<std::result::Result<_, _>>()?
        }
        None => Vec::new(),
    };
    for pass in 0..passes {
        let pass_started = Instant::now();
        let mut states: Vec<TowerState> =
            (0..streams).map(|_| if credit { learner.tower.rest_with_credit() } else { learner.tower.rest() }).collect();
        let (mut code, mut bytes, mut deposits, mut halvings) = (0i64, 0usize, 0usize, 0u32);
        let mut window = (0i64, 0usize);
        let mut sections_run = sections_a_pass;
        if let Some(look) = looking {
            let mut lookers: Vec<Looker> = look_keys.drain(..).enumerate().map(|(s, keys)| Looker::new(s * chunk, (s + 1) * chunk, keys)).collect();
            let mut k = 0usize;
            // Over the pass's deposits: the plain streams' code change and the forks', and the
            // deposits under which the plain streams' code rose while the whole code fell.
            let (mut plain_change, mut fork_change, mut plain_rose) = (0i64, 0i64, 0usize);
            loop {
                let tower = &learner.tower;
                let filled: Vec<bool> = lookers
                    .par_iter_mut()
                    .zip(states.par_iter())
                    .map(|(l, open)| l.fill(tower, classes, open, section + 1, look).map_err(|e| e.to_string()))
                    .collect::<std::result::Result<_, String>>()?;
                if filled.contains(&false) {
                    break;
                }
                // The streams' plain parts, then the forks their moments opened in the section,
                // each from its own state; the forks' states end with the section.
                let forks: Vec<Fork> = lookers.iter_mut().flat_map(|l| l.forks.drain(..)).collect();
                let mut parts: Vec<&[usize]> = lookers.iter().map(|l| &l.built[..=section]).collect();
                parts.extend(forks.iter().map(|f| f.classes.as_slice()));
                let plain: Vec<Vec<Option<usize>>> = lookers.iter().map(|l| l.built[..=section].iter().map(|&c| Some(c)).collect()).collect();
                let mut compared: Vec<&[Option<usize>]> = plain.iter().map(|c| c.as_slice()).collect();
                compared.extend(forks.iter().map(|f| f.compared.as_slice()));
                states.extend(forks.iter().map(|f| f.opening.clone()));
                let result = learner.section_compared(&mut states, &parts, Some(&compared));
                states.truncate(streams);
                let receipt = match result {
                    Ok(receipt) => receipt,
                    Err(e) => {
                        println!("TOWER_SWELL pass={} section={} {}", pass, k + 1, learner.swell_line());
                        return Err(e.to_string().into());
                    }
                };
                if receipt.deposited {
                    let change = |parts: &[(i64, i64)]| parts.iter().map(|&(before, after)| after - before).sum::<i64>();
                    let plain = change(&receipt.parts[..streams]);
                    plain_change += plain;
                    fork_change += change(&receipt.parts[streams..]);
                    plain_rose += (plain > 0) as usize;
                }
                // Each compared place after a part's first is one byte coded.
                let coded: usize = compared.iter().map(|c| c[1..].iter().filter(|x| x.is_some()).count()).sum();
                for l in &mut lookers {
                    l.built.drain(..section);
                }
                code += receipt.code_before;
                bytes += coded;
                window.0 += receipt.code_before;
                window.1 += coded;
                deposits += receipt.deposited as usize;
                halvings += receipt.halvings;
                k += 1;
                if k % 32 == 0 {
                    println!(
                        "TOWER_SECTION pass={} section={} bits_a_byte={} deposits={} halvings={} elapsed_ms={}",
                        pass, k, per(window.0, window.1), deposits, halvings, started.elapsed().as_millis()
                    );
                    window = (0, 0);
                }
            }
            let (looks, right, read) = lookers.iter().fold((0usize, 0usize, 0usize), |a, l| (a.0 + l.looks, a.1 + l.right, a.2 + l.at - l.start));
            println!(
                "TOWER_LOOKS pass={} sections={} looks={} right={} text_read={} of {} keys_left={}",
                pass, k, looks, right, read, streams * chunk, lookers.iter().map(|l| l.keys_left()).min().unwrap_or(0)
            );
            println!(
                "TOWER_PARTS pass={} deposits={} plain_rose={} plain_change_bits={} fork_change_bits={}",
                pass, deposits, plain_rose, signed_bits(plain_change), signed_bits(fork_change)
            );
            look_keys = lookers.into_iter().map(|l| l.keys).collect();
            sections_run = k;
        }
        for k in 0..if looking.is_some() { 0 } else { sections_a_pass } {
            let ranges: Vec<std::ops::Range<usize>> =
                (0..streams).map(|s| s * chunk + k * section..s * chunk + (k + 1) * section + 1).collect();
            let parts: Vec<&[usize]> = ranges.iter().map(|r| &classes[r.clone()]).collect();
            let receipt = match learner.section(&mut states, &parts) {
                Ok(receipt) => receipt,
                Err(e) => {
                    println!("TOWER_SWELL pass={} section={} {}", pass, k + 1, learner.swell_line());
                    return Err(e.to_string().into());
                }
            };
            // The section codes every class of a part after its first.
            let coded: usize = ranges.iter().map(|r| reading.train_lengths[r.start + 1..r.end].iter().map(|&n| n as usize).sum::<usize>()).sum();
            code += receipt.code_before;
            bytes += coded;
            window.0 += receipt.code_before;
            window.1 += coded;
            deposits += receipt.deposited as usize;
            halvings += receipt.halvings;
            if (k + 1) % 32 == 0 || k + 1 == sections_a_pass {
                println!(
                    "TOWER_SECTION pass={} section={} bits_a_byte={} deposits={} halvings={} elapsed_ms={}",
                    pass, k + 1, per(window.0, window.1), deposits, halvings, started.elapsed().as_millis()
                );
                println!("TOWER_SWELL pass={} section={} {}", pass, k + 1, learner.swell_line());
                window = (0, 0);
            }
        }
        // Each pass's learner rests beside the run before the held-out read, so a run stopped at
        // its deadline or refused in the read keeps its last trained pass.
        let text = learner.to_text();
        let name = format!("STATE.{pass}");
        write_new(&out.join(&name), text.as_bytes())?;
        println!("TOWER_STATE {name} state_bytes={} state_sha256={}", text.len(), sha256(text.as_bytes())?);
        let regions = held_out(&learner.tower, &reading.dev, &reading.dev_lengths, &reading.dev_roles, streams)?;
        let (dev_code, dev_coded) = regions.iter().fold((0i64, 0usize), |a, r| (a.0 + r.0, a.1 + r.1));
        println!(
            "TOWER_PASS pass={} train_bits_a_byte={} dev_bits_a_byte={} dev_regions {} deposits={}/{} pass_ms={} elapsed_ms={}",
            pass, per(code, bytes), per(dev_code, dev_coded), region_line(&regions), deposits, sections_run,
            pass_started.elapsed().as_millis(), started.elapsed().as_millis()
        );
    }
    let text = learner.to_text();
    write_new(&out.join("STATE"), text.as_bytes())?;
    println!("TOWER_DONE state_bytes={} state_sha256={} elapsed_ms={}", text.len(), sha256(text.as_bytes())?, started.elapsed().as_millis());
    Ok(())
}

/// `found-units TRAIN TRAIN_SHA OUT`: found units from the training text (`hnn::units`) and write
/// the founding list.
pub(super) fn found_units(args: &[String]) -> Result<()> {
    if args.len() != 4 {
        return Err("found-units TRAIN TRAIN_SHA OUT".into());
    }
    let started = Instant::now();
    let train = pinned_read(&args[1], &args[2], READ_BUDGET as usize)?;
    let out = Path::new(&args[3]);
    std::fs::create_dir(out)?;
    let (units, read, receipt) = Units::found(&train).map_err(|e| e.to_string())?;
    let text = units.to_text();
    write_new(&out.join("UNITS"), text.as_bytes())?;
    let bits = |code: i128| per((code >> (CODE_BITS - READ_BITS)) as i64, train.len());
    println!(
        "UNITS_FOUNDED units={} founded={} refused={} undecided={} priced={} symbols={}->{} order_one_bits_a_byte={}->{} description_bits_a_byte={} complete_bits_a_byte={} elapsed_ms={}",
        units.len(), receipt.founded, receipt.refused, receipt.undecided, receipt.priced, receipt.symbols_before, receipt.symbols_after,
        bits(receipt.code_before), bits(receipt.code_after), bits(receipt.description), bits(receipt.code_after + receipt.description),
        started.elapsed().as_millis()
    );
    println!("UNITS_STATE units_bytes={} units_sha256={}", text.len(), sha256(text.as_bytes())?);
    // The units the passage reads most, with their counts, and the longest founded.
    let mut counts = vec![0usize; units.len()];
    for &u in &read {
        counts[u as usize] += 1;
    }
    let mut order: Vec<usize> = (256..units.len()).collect();
    order.sort_by_key(|&u| std::cmp::Reverse(counts[u]));
    let show = |u: usize| format!("{:?}:{}", String::from_utf8_lossy(units.piece(u)), counts[u]);
    println!("UNITS_READ_MOST {}", order.iter().take(60).map(|&u| show(u)).collect::<Vec<_>>().join(" "));
    order.sort_by_key(|&u| std::cmp::Reverse(units.piece(u).len()));
    println!("UNITS_LONGEST {}", order.iter().take(30).map(|&u| show(u)).collect::<Vec<_>>().join(" "));
    Ok(())
}

/// `sample-unit-tower UNITS UNITS_SHA STATE STATE_SHA PROMPT PROMPT_SHA KEYS KEYS_SHA BYTES OUT
/// [AGREE]`: the prompt read in the units, then units released until the declared bytes.
pub(super) fn sample_units(args: &[String]) -> Result<()> {
    if args.len() != 11 && args.len() != 12 {
        return Err("sample-unit-tower UNITS UNITS_SHA STATE STATE_SHA PROMPT PROMPT_SHA KEYS KEYS_SHA BYTES OUT [AGREE]".into());
    }
    let units = Units::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], READ_BUDGET as usize)?)?).map_err(|e| e.to_string())?;
    release(&args[2..], Some(&units))
}

pub(super) fn sample(args: &[String]) -> Result<()> {
    if args.len() != 9 && args.len() != 10 {
        return Err("sample-tower STATE STATE_SHA PROMPT PROMPT_SHA KEYS KEYS_SHA BYTES OUT [AGREE]".into());
    }
    release(args, None)
}

/// A fork of the rested tower: it receives the prompt (read in the units when named) and releases
/// classes by exact draws on its face until the declared bytes are released. `args` are
/// `_ STATE STATE_SHA PROMPT PROMPT_SHA KEYS KEYS_SHA BYTES OUT [AGREE]`.
fn release(args: &[String], units: Option<&Units>) -> Result<()> {
    let agree = agreement(args.get(9))?;
    let started = Instant::now();
    let state = pinned_read(&args[1], &args[2], STATE_BUDGET)?;
    let prompt = pinned_read(&args[3], &args[4], QUERY_BYTE_BUDGET)?;
    let keys = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let count: usize = args[7].parse()?;
    if keys.len() < count.checked_mul(8).ok_or("key extent overflow")? {
        return Err("fewer eight-byte keys than declared bytes".into());
    }
    let out = Path::new(&args[8]);
    std::fs::create_dir(out)?;
    let learner = TowerLearner::from_text(std::str::from_utf8(&state)?).map_err(|e| e.to_string())?;
    let tower = &learner.tower;
    let mut modes = tower.rest();
    let classes: Vec<usize> = match units {
        Some(u) => u.parse(&prompt).map_err(|e| e.to_string())?.into_iter().map(|c| c as usize).collect(),
        None => prompt.iter().map(|&b| b as usize).collect(),
    };
    let prompt_code = if classes.len() > 1 { tower.read(&mut modes.clone(), &classes).map_err(|e| e.to_string())? } else { 0 };
    let mut face = None;
    for &c in &classes {
        face = Some(tower.advance(&mut modes, c).map_err(|e| e.to_string())?);
    }
    let mut face = face.ok_or("an empty prompt")?;
    let mut key_stream = KeyStream::new(keys, 8)?;
    let mut released = Vec::with_capacity(count);
    while released.len() < count {
        let key = key_stream.next_key().ok_or("fewer keys than declared bytes")?;
        let class = holonics::receiver::release::draw_exact(&agreement_face(&face.masses, agree), &key)?
            .drawn_class()
            .ok_or("an unresolved draw at an exact face")?;
        match units {
            Some(u) => released.extend_from_slice(u.piece(class)),
            None => released.push(class as u8),
        }
        face = tower.advance(&mut modes, class).map_err(|e| e.to_string())?;
    }
    write_new(&out.join("OUTPUT.bin"), &released)?;
    let prompt_bytes = match units {
        Some(u) => classes[1..].iter().map(|&c| u.piece(c).len()).sum::<usize>(),
        None => classes.len().saturating_sub(1),
    };
    println!(
        "TOWER_SAMPLE prompt_bits_a_byte={} bytes={} agree={} elapsed_ms={}",
        per(prompt_code, prompt_bytes.max(1)), released.len(), agree, started.elapsed().as_millis()
    );
    println!("TOWER_SAMPLE_TEXT {:?}", String::from_utf8_lossy(&released));
    Ok(())
}

/// A text field of `LINES.tsv` or `LOOKS.tsv`: the bytes escaped (`read_lines`).
fn field(bytes: &[u8]) -> String {
    bytes.iter().map(|&b| if b == b'|' { "\\x7c".to_string() } else { b.escape_ascii().to_string() }).collect()
}

/// `read-lines STATE STATE_SHA TEXT TEXT_SHA KEYS KEYS_SHA WRITTEN AGREE OUT`: each line of the
/// text read alone. The frozen tower opens at rest on a line's end, receives the line through its
/// first `=`, and codes the rest of the line class by class (`LINES.tsv`: the line's index, its
/// head, the rest as given and each class's code on `2^(−20)` bits). For the first `WRITTEN` lines
/// a fork at the `=` releases its own rest by exact agreeing draws until a line's end (or as many
/// classes as the given rest and four more), written beside it. An exterior reading of terrain
/// lines (`tools/arithmetic_terrain.py`): what the tower writes after an expression it may never
/// have met. `read-lines-stream` opens each line instead on the state the text's true earlier
/// lines left, the condition the tower trained in: the fork writes from that state, and the true
/// line, not the release, carries the stream on.
///
/// `read-lines-again … AGREE LOOKS OUT` writes in the stream and then looks again: the fork
/// carries the rest it wrote, its line's end and the line's head once more, and releases again,
/// until two looks in a row write the same rest or `LOOKS` looks are spent. `read-lines-redraw`
/// is its foil: each later look draws again at the same moment and carries nothing of the looks
/// before it. The first look spends the key file as the one-look read does, so its releases are
/// that read's; the later looks draw from the file's second half. `LINES.tsv` writes the last look
/// and `LOOKS.tsv` every look (the line's index, its head, the rest as given, whether the last two
/// looks agree, the looks joined by `|`, and what the true rest costs from where each look stands,
/// on `2^(−20)` bits: the frustration's floor and how fast the looks approach it; then each look's
/// lock with the true rest, `λ` and `F*` joined by `|`, the micro-control's success reading: `λ`
/// grows or holds and `F*` falls or holds at 0 from look to look).
/// `read-lines-carried` looks as `read-lines-again` does, and its stream carries each written
/// line's first look, line end and head again before the true rest, the passage a tower trained
/// with the look (`Looking`) met: its codes are read where that tower was taught.
/// `read-lines-own` lets the tower decide: after each look and its line's end the fork writes on,
/// and it looks again only where it writes its line's head again, at most `LOOKS` looks. Its
/// stream is the plain text, the passage a tower trained with the look (`Looking`) read.
///
/// `read-lines-located … AGREE LOOKS DEPTH OUT` looks as `read-lines-again` does at a moment no
/// byte declares: the first place in a line where a located key fires. The passage tree
/// ([`PassageTree`]) hears the read stream class by class, and the moment is the first cell whose
/// line holds `DEPTH` classes up to it that the tree's lock locates at full depth, an earlier
/// visit of the same context (the located equality `(t, t − δ)`), with at least one class of the
/// line still to come. The key is the line's own expression, in any medium, and the look asks for
/// what follows it. A line where no key fires is carried in the stream unread, as a line without
/// `=` is in the other reads.
///
/// Every text field of both files (head, rest, looks) is its bytes escaped as Rust's
/// `escape_ascii` writes them, with `|` written `\x7c`, so a field holds no tab or `|` and reads
/// back to its exact bytes (Python's `codecs.escape_decode`). A look is the tower's bytes, which
/// need not be UTF-8.
pub(super) fn read_lines(args: &[String], in_stream: bool, look: Look, located: bool) -> Result<()> {
    let arity = if look == Look::Once { 10 } else { 11 } + usize::from(located);
    if args.len() != arity {
        return Err("read-lines|read-lines-stream STATE STATE_SHA TEXT TEXT_SHA KEYS KEYS_SHA WRITTEN AGREE OUT; read-lines-again|read-lines-redraw|read-lines-carried|read-lines-own STATE STATE_SHA TEXT TEXT_SHA KEYS KEYS_SHA WRITTEN AGREE LOOKS OUT; read-lines-located STATE STATE_SHA TEXT TEXT_SHA KEYS KEYS_SHA WRITTEN AGREE LOOKS DEPTH OUT".into());
    }
    let started = Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let keys = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let written: usize = args[7].parse()?;
    let agree = agreement(args.get(8))?;
    let looks: usize = if look == Look::Once { 1 } else { args[9].parse()? };
    if looks == 0 {
        return Err("a written line needs at least one look".into());
    }
    let out = Path::new(&args[arity - 1]);
    std::fs::create_dir(out)?;
    let tower = &learner.tower;
    let mut later_keys = KeyStream::new(keys[keys.len() / 2..].to_vec(), 8)?;
    let mut key_stream = KeyStream::new(keys, 8)?;
    let mut rows = String::new();
    let mut look_rows = String::new();
    let (mut spent, mut settled) = (0usize, 0usize);
    let mut lines = 0usize;
    let mut carried = tower.rest();
    let mut carried_face = tower.advance(&mut carried, b'\n' as usize).map_err(|e| e.to_string())?;
    let moments = if located {
        let moments = located_moments(&text, args[10].parse()?)?;
        println!("MOMENTS_LOCATED depth={} lines={} located={}", args[10], moments.len(), moments.iter().flatten().count());
        moments
    } else {
        text.split(|&b| b == b'\n').filter(|l| !l.is_empty()).map(|l| l.iter().position(|&b| b == b'=')).collect()
    };
    for (i, line) in text.split(|&b| b == b'\n').filter(|l| !l.is_empty()).enumerate() {
        let Some(eq) = moments[i] else {
            for &b in line.iter().chain(b"\n") {
                carried_face = tower.advance(&mut carried, b as usize).map_err(|e| e.to_string())?;
            }
            continue;
        };
        let (mut modes, mut face) = if in_stream {
            (carried.clone(), carried_face.clone())
        } else {
            let mut modes = tower.rest();
            let face = tower.advance(&mut modes, b'\n' as usize).map_err(|e| e.to_string())?;
            (modes, face)
        };
        for &b in &line[..=eq] {
            face = tower.advance(&mut modes, b as usize).map_err(|e| e.to_string())?;
        }
        let rest: Vec<u8> = line[eq + 1..].iter().copied().chain([b'\n']).collect();
        let mut looked: Vec<Vec<u8>> = Vec::new();
        let mut costs: Vec<i64> = Vec::new();
        let mut first_look: Vec<usize> = Vec::new();
        let mut locks: Vec<(usize, usize)> = Vec::new();
        if i < written {
            let cap = rest.len() + 4;
            let mut fork = modes.clone();
            let written = |r: Vec<usize>| r.into_iter().map(|c| c as u8).collect::<Vec<u8>>();
            costs.push(rest_code(tower, &modes, face.clone(), &rest)?);
            first_look = release_rest(tower, &mut fork, face.clone(), &mut key_stream, cap, agree)?.0;
            looked.push(written(first_look.clone()));
            while looked.len() < looks && (look == Look::Own || looked.len() < 2 || looked[looked.len() - 1] != looked[looked.len() - 2]) {
                let again = match look {
                    Look::Once => break,
                    Look::Again | Look::Carried => {
                        let mut f = tower.advance(&mut fork, b'\n' as usize).map_err(|e| e.to_string())?;
                        for &b in &line[..=eq] {
                            f = tower.advance(&mut fork, b as usize).map_err(|e| e.to_string())?;
                        }
                        costs.push(rest_code(tower, &fork, f.clone(), &rest)?);
                        written(release_rest(tower, &mut fork, f, &mut later_keys, cap, agree)?.0)
                    }
                    Look::Redraw => {
                        costs.push(costs[0]);
                        written(release_rest(tower, &mut modes.clone(), face.clone(), &mut later_keys, cap, agree)?.0)
                    }
                    Look::Own => {
                        // The fork's attempt meets its line's end and the tower writes on: it
                        // looks again only where it writes its line's head again.
                        let f = tower.advance(&mut fork, b'\n' as usize).map_err(|e| e.to_string())?;
                        let (asked, f) = release_rest(tower, &mut fork, f, &mut later_keys, eq + 1, agree)?;
                        if asked.iter().map(|&c| c as u8).ne(line[..=eq].iter().copied()) {
                            break;
                        }
                        costs.push(rest_code(tower, &fork, f.clone(), &rest)?);
                        written(release_rest(tower, &mut fork, f, &mut later_keys, cap, agree)?.0)
                    }
                };
                looked.push(again);
            }
            // Each look read by the lock with the true rest (micro-control §7): the longest
            // order-consistent coupling `λ` and its friction `F* = |H| + |T| − 2λ`, the look's end
            // counted where it wrote one (a look cut at `cap` wrote none).
            for l in &looked {
                let mut h = l.clone();
                if h.len() < cap {
                    h.push(b'\n');
                }
                let c = coupling(&h, &rest).map_err(|e| e.to_string())?;
                locks.push((c.lambda, c.least_friction));
            }
            spent += looked.len();
            let agreed = looked.len() >= 2 && looked[looked.len() - 1] == looked[looked.len() - 2];
            settled += usize::from(agreed);
            if look != Look::Once {
                look_rows.push_str(&format!(
                    "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                    i,
                    field(&line[..=eq]),
                    field(&rest[..rest.len() - 1]),
                    u8::from(agreed),
                    looked.iter().map(|l| field(l)).collect::<Vec<_>>().join("|"),
                    costs.iter().map(|c| c.to_string()).collect::<Vec<_>>().join("|"),
                    locks.iter().map(|l| l.0.to_string()).collect::<Vec<_>>().join("|"),
                    locks.iter().map(|l| l.1.to_string()).collect::<Vec<_>>().join("|")
                ));
            }
        }
        let release = looked.last().cloned().unwrap_or_default();
        if look == Look::Carried && i < written {
            // The stream carries the first look, its line's end and the head again before the
            // true rest, as a tower trained with the look met its lines.
            let carried_in: Vec<usize> = first_look.iter().copied().chain([b'\n' as usize]).chain(line[..=eq].iter().map(|&b| b as usize)).collect();
            for b in carried_in {
                face = tower.advance(&mut modes, b).map_err(|e| e.to_string())?;
            }
        }
        let mut codes = Vec::with_capacity(rest.len());
        for &b in &rest {
            codes.push(face.code(b as usize).to_string());
            face = tower.advance(&mut modes, b as usize).map_err(|e| e.to_string())?;
        }
        (carried, carried_face) = (modes, face);
        rows.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\n",
            i,
            field(&line[..=eq]),
            field(&rest[..rest.len() - 1]),
            field(&release),
            codes.join(",")
        ));
        lines += 1;
    }
    write_new(&out.join("LINES.tsv"), rows.as_bytes())?;
    if look != Look::Once {
        write_new(&out.join("LOOKS.tsv"), look_rows.as_bytes())?;
        println!("LOOKS_READ looks={} spent={} settled={} looks_sha256={}", looks, spent, settled, sha256(look_rows.as_bytes())?);
    }
    println!("LINES_READ lines={} written={} agree={} lines_sha256={} elapsed_ms={}", lines, written.min(lines), agree, sha256(rows.as_bytes())?, started.elapsed().as_millis());
    Ok(())
}

/// The moment of each nonempty line of `text` where a located key fires (`read-lines-located`):
/// the passage tree hears the stream the reads carry (a line's end, then each nonempty line and its
/// end), and a line's moment is its first cell `p` whose `depth` classes up to `p` lie in the line
/// and are a context the tree's lock locates at full depth (visited before, so followed before),
/// with a class of the line after `p`. The lock reads node visits only, so the horizon and backoff
/// (the GSM8K route's, `2^13` and one occurrence) do not move a moment.
fn located_moments(text: &[u8], depth: usize) -> Result<Vec<Option<usize>>> {
    if depth == 0 {
        return Err("a located key holds at least one class".into());
    }
    let mut tree = PassageTree::new(PassageDeclaration { alphabet: 256, phases: 1, depth, horizon: 13, backoff: 1 })?;
    let mut context = vec![b'\n' as usize];
    let mut now = 0u64;
    let mut moments = Vec::new();
    for line in text.split(|&b| b == b'\n').filter(|l| !l.is_empty()) {
        let mut moment = None;
        for (p, &b) in line.iter().chain(b"\n").enumerate() {
            tree.deposit(0, &context, b as usize, now)?;
            now += 1;
            context.insert(0, b as usize);
            context.truncate(depth);
            if moment.is_none() && p + 1 >= depth && p + 1 < line.len() && tree.lock(0, &context, now)?.is_some_and(|(_, d, _)| d == depth) {
                moment = Some(p);
            }
        }
        moments.push(moment);
    }
    Ok(moments)
}

/// How a written line meets its own moment again (`read_lines`).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Look {
    /// One look: the release at the `=` is written as it comes.
    Once,
    /// The fork carries its own release, its line's end and the head again, and releases again.
    Again,
    /// The foil: each later look draws again at the same moment, carrying nothing.
    Redraw,
    /// As `Again`, and the stream carries the first look before the true rest.
    Carried,
    /// The tower decides: after a look and its line's end it writes on, and looks again only
    /// where it writes its line's head again.
    Own,
}

/// What the line's true rest costs read from `state` and its `face`: its classes' codes summed on
/// `2^(−20)` bits, the rest's line end included. An exterior reading at a look: the state is not
/// moved.
fn rest_code(tower: &Tower, state: &TowerState, mut face: TowerFace, rest: &[u8]) -> Result<i64> {
    let mut s = state.clone();
    let mut code = 0i64;
    for &b in rest {
        code += face.code(b as usize);
        face = tower.advance(&mut s, b as usize).map_err(|e| e.to_string())?;
    }
    Ok(code)
}

/// The rest a fork releases from `face` by exact agreeing draws: classes until a line's end, or
/// `cap` classes, with the face the fork stands at after the last class it wrote. The fork moves
/// through every class it writes.
fn release_rest(tower: &Tower, fork: &mut TowerState, mut face: TowerFace, keys: &mut KeyStream, cap: usize, agree: u32) -> Result<(Vec<usize>, TowerFace)> {
    let mut release = Vec::new();
    while release.len() < cap {
        let key = keys.next_key().ok_or("fewer keys than the written lines draw")?;
        let class = agreeing_class(&face.masses, agree, &key)?;
        if class == b'\n' as usize {
            break;
        }
        release.push(class);
        face = tower.advance(fork, class).map_err(|e| e.to_string())?;
    }
    Ok((release, face))
}

/// The look inside training: at each moment the terrain declares (the byte at which a line asks
/// for its rest), the tower releases its own rest from the state its stream has reached, by
/// `agree` exact agreeing draws from its stream's share of `keys`. The stream's own passage stays
/// the plain text, so every first arrival is compared at every place. Where the release and its
/// line end part from the true rest, a fork opens from the stream's state at the moment and reads
/// the release and its end, compared with nothing (up to the place they part its faces are the
/// stream's own, compared already; past it the passage is the fork's own), then the line's head
/// again and the true rest and its end. On the fork only the news is compared
/// (`TowerLearner::section_compared`): the true rest's places that lie on no least-friction
/// coupling with the release and its end (`receiver::coupling`, the micro-control's §7 lock), the
/// places the release carries at no lag. The lock reads both strands from both ends alike, so no
/// place, first or last, frames the comparison. The head again and the true rest's places the
/// release can hold are what the fork has just read, so they are read with nothing compared:
/// compared, the head taught that a line's question returns after its answer, against the passage,
/// and the held places were learned by copying the release (the record of October 23 on a terrain
/// of interacting digits, "Reading the side-fork tower's faces"; the fork that compared them is at
/// [`79a440c06`](https://github.com/brandonrdug/holonics/tree/79a440c06), and the fork that
/// compared the true rest from the first place it parts from the release, a teacher's frame that
/// privileges the beginning, at
/// [`0ef7c4fc4`](https://github.com/brandonrdug/holonics/tree/0ef7c4fc4)). The fork joins the
/// section its moment falls in, deposits with the streams and ends there. Where the release is the
/// true rest no fork opens. The terrain's moment and line end are its codec's declared bytes, read
/// outside the tower.
pub(super) struct Looking {
    keys: Vec<u8>,
    agree: u32,
    moment: usize,
    end: usize,
}

/// One stream's plain passage from the section's first class on, and the forks its moments opened
/// in the section.
struct Looker {
    start: usize,
    end: usize,
    at: usize,
    line_start: Option<usize>,
    built: Vec<usize>,
    forks: Vec<Fork>,
    keys: KeyStream,
    looks: usize,
    right: usize,
}

/// A look's fork: the state having received every class before the moment, and the classes it
/// reads from the moment on, each with the class its face is compared with, or nothing.
struct Fork {
    opening: TowerState,
    classes: Vec<usize>,
    compared: Vec<Option<usize>>,
}

impl Looker {
    fn new(start: usize, end: usize, keys: KeyStream) -> Self {
        Self { start, end, at: start, line_start: None, built: Vec::new(), forks: Vec::new(), keys, looks: 0, right: 0 }
    }

    fn keys_left(&self) -> usize {
        self.keys.remaining()
    }

    /// Fill the passage to `need` classes from the stream's text, the state `opening` having
    /// received every class before the first, and open a fork at each moment where the release
    /// parts from the true rest: false when the stream's text ends first. A line's head is whole
    /// only after the stream has met a line's end, so a stream releases only from its first whole
    /// line on.
    fn fill(&mut self, tower: &Tower, text: &[usize], opening: &TowerState, need: usize, look: &Looking) -> Result<bool> {
        let mut probe = opening.clone();
        let mut probed = 0usize;
        while self.built.len() < need {
            if self.at >= self.end {
                return Ok(false);
            }
            let c = text[self.at];
            self.at += 1;
            self.built.push(c);
            if c == look.end {
                self.line_start = Some(self.at);
            } else if let (true, Some(head)) = (c == look.moment, self.line_start) {
                let moment = self.built.len() - 1;
                for &b in &self.built[probed..moment] {
                    tower.advance(&mut probe, b).map_err(|e| e.to_string())?;
                }
                let before = probe.clone();
                let face = tower.advance(&mut probe, c).map_err(|e| e.to_string())?;
                probed = self.built.len();
                let given = text[self.at..self.end].iter().position(|&b| b == look.end).unwrap_or(self.end - self.at);
                let release = release_rest(tower, &mut probe.clone(), face, &mut self.keys, given + 4, look.agree)?.0;
                let attempt: Vec<usize> = release.into_iter().chain(std::iter::once(look.end)).collect();
                let truth = &text[self.at..(self.at + given + 1).min(self.end)];
                self.looks += 1;
                if attempt == truth {
                    self.right += 1;
                } else {
                    let head = &text[head..self.at];
                    // The true rest's places the release holds on no least-friction coupling.
                    let slips = coupling(&attempt, truth).map_err(|e| e.to_string())?.never_held_t_indices;
                    let classes: Vec<usize> = std::iter::once(c).chain(attempt.iter().copied()).chain(head.iter().copied()).chain(truth.iter().copied()).collect();
                    let compared: Vec<Option<usize>> = std::iter::once(Some(c))
                        .chain(attempt.iter().chain(head).map(|_| None))
                        .chain(truth.iter().enumerate().map(|(j, &b)| slips.binary_search(&j).is_ok().then_some(b)))
                        .collect();
                    self.forks.push(Fork { opening: before, classes, compared });
                }
            }
        }
        Ok(true)
    }
}

/// The release at which `agree` independent draws from the face fall on the same class: the face's
/// masses raised to that power over their sum. One draw is the face itself; two give its collision
/// face `p²/Σp²`, the release where two receivers of the same face agree. The release is exact and
/// spends one key a draw whatever `agree` is.
pub(super) fn agreement_face(masses: &[u128], agree: u32) -> Vec<Rat> {
    let powered: Vec<num_bigint::BigInt> = masses.iter().map(|&u| num_bigint::BigInt::from(u).pow(agree)).collect();
    let total: num_bigint::BigInt = powered.iter().sum();
    powered.into_iter().map(|u| Rat::new(u, total.clone())).collect()
}

/// The class `agree` agreeing draws fall on at `key = n/d`: the inverse-CDF class of the face
/// `m^agree / Σ m^agree`, the first `c` with `d Σ_(j≤c) m_j^agree > n Σ m^agree`. It is
/// `release::draw_exact` over [`agreement_face`] read in integers, without normalizing a ratio for
/// every class.
pub(super) fn agreeing_class(masses: &[u128], agree: u32, key: &Rat) -> Result<usize> {
    if key < &Rat::from_integer(0.into()) || key >= &Rat::from_integer(1.into()) {
        return Err("a key outside [0, 1)".into());
    }
    let powered: Vec<num_bigint::BigInt> = masses.iter().map(|&m| num_bigint::BigInt::from(m).pow(agree)).collect();
    let total: num_bigint::BigInt = powered.iter().sum();
    let target = key.numer() * &total;
    let mut through = num_bigint::BigInt::from(0);
    for (class, p) in powered.iter().enumerate() {
        through += p;
        if &through * key.denom() > target {
            return Ok(class);
        }
    }
    Err("an empty face".into())
}

/// The declared number of agreeing draws: one when none is named.
pub(super) fn agreement(arg: Option<&String>) -> Result<u32> {
    let agree = arg.map_or(Ok(1), |a| a.parse::<u32>())?;
    if agree == 0 {
        return Err("a release needs at least one draw".into());
    }
    Ok(agree)
}
