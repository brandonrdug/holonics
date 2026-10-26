//! **The reset clock: a navigator's clock that holds the arrival after its class** (#404, #405, #386).
//!
//! [definition; record
//! `2026-10-26_THE_ROLE_KEY_IS_A_RESET_CLOCK_THE_POOL_FOUNDS_AND_ITS_ACCEPTANCE_IS_FIXED_BEFORE_THE_BUILD.md`,
//! §1] Why it is built. The bank's read at a named answer's opening never reaches the name the
//! question opened on: a key the passage reaches only by diffusion is read to its square root, and
//! the slow mode is founded, not waited for. A reset clock of class `A` resets when `A` arrives and
//! holds the arrival that follows; its resident face is that arrival's encoding, joined to a level's
//! output through a map that opens at zero:
//!
//! ```text
//! held_t  = u_t          when u_(t−1) = A      (the rest counts as a class, `A = alphabet`)
//!         = held_(t−1)   otherwise; nothing is held before the first reset
//! join    x^(ℓ+1)_t += O_A E(held_t)           O_A: d × d on 2^(−24), opening at zero
//! reverse G_(O_A) = Σ_t δx_t E(held_t)ᵀ,  G_(E(u)) += Σ_(t: held_t = u) O_Aᵀ δx_t
//! ```
//!
//! - **Retention.** The clock's state is the held class alone ([`TowerState::held`]): the
//!   future-sufficient quotient of what it reads, no tape and no window.
//! - **Every medium.** The law names a class and an encoding, so it is the same object over any
//!   codec's units.
//! - **The opening.** `O_A` opens at zero, so a clocked tower reads every passage bit-identically to
//!   its twin, and the covector moves it from the first deposit. Its material follows every other
//!   face's, so a tower's text and its other faces stay as they are.
//! - **The founding.** Which class is clocked is the pool's choice ([`ClockPool`]): every class's
//!   clock and the rest's, ranked by the exact drop at the join's covector, never named by a
//!   designer.
use super::*;
use num_bigint::BigInt;
use num_traits::{Signed, Zero};

/// [definition; agent-inferred, October 26] **The clocks' declared law**: the level whose output
/// they join and the classes that reset them, in the order they were founded (`alphabet` is the
/// rest).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClockDeclaration {
    pub level: usize,
    pub classes: Vec<usize>,
}

impl ClockDeclaration {
    fn check(&self, d: &TowerDeclaration) -> Result<()> {
        if self.level >= d.levels {
            return refuse("a clock joins a level of the tower");
        }
        if self.classes.is_empty() || self.classes.iter().any(|&c| c > d.alphabet) {
            return refuse("a clock resets at a class of the alphabet or at the rest");
        }
        for (i, c) in self.classes.iter().enumerate() {
            if self.classes[..i].contains(c) {
                return refuse("a class resets one clock");
            }
        }
        Ok(())
    }

    /// The clocks' line of the tower's text.
    pub fn to_text(&self) -> String {
        let classes = self.classes.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(" ");
        format!("clock {} {classes}\n", self.level)
    }

    pub(super) fn from_text(line: &str, d: &TowerDeclaration) -> Result<Self> {
        let words: Vec<&str> = line.split(' ').collect();
        let num = |s: &str| s.parse::<usize>().map_err(|_| TowerError::Refused("a clock's line that is not counts"));
        if words.len() < 3 || words[0] != "clock" {
            return refuse("not a clock's line");
        }
        let clock = Self { level: num(words[1])?, classes: words[2..].iter().map(|w| num(w)).collect::<Result<_>>()? };
        clock.check(d)?;
        Ok(clock)
    }
}

impl Tower {
    /// [agent-inferred, October 26] **A reset clock joined to the tower**: the clock of `class` at
    /// `level`, its join `O` appended after every other face's material at zero, so the clocked tower
    /// reads every passage exactly as the tower did, and the section's covector moves it from there.
    /// A further clock joins the same level. A stream rested before the join carries no clock: rest
    /// it again.
    pub fn join_clock(&mut self, level: usize, class: usize) -> Result<()> {
        let d = self.declaration;
        let mut clock = self.clock.clone().unwrap_or(ClockDeclaration { level, classes: Vec::new() });
        if clock.level != level {
            return refuse("every clock joins one level");
        }
        clock.classes.push(class);
        clock.check(&d)?;
        let layout = Layout::new(&d, self.pair.as_ref().map_or(0, PairFace::forms), self.ring.as_ref().map_or(0, RingFace::ranks), self.ring.as_ref().map_or(0, RingFace::harmonics), self.bank.as_ref(), clock.classes.len());
        self.theta.resize(layout.len, 0);
        self.layout = layout;
        self.clock = Some(clock);
        Ok(())
    }

    /// The joined clocks' declaration, when any is joined.
    pub fn clock(&self) -> Option<&ClockDeclaration> {
        self.clock.as_ref()
    }

    /// The material range of the clocks' joins, when any is joined.
    pub fn clock_join(&self) -> Option<std::ops::Range<usize>> {
        let (clock, start) = (self.clock.as_ref()?, self.layout.clock?);
        let w = self.declaration.width;
        Some(start..start + clock.classes.len() * w * w)
    }

    /// The clocks' state at rest: nothing held.
    pub(super) fn clock_rest(&self) -> Vec<usize> {
        vec![self.declaration.alphabet; self.clock.as_ref().map_or(0, |c| c.classes.len())]
    }

    /// Each clock's join reach.
    pub(super) fn clock_reaches(&self) -> Vec<u64> {
        let (Some(clock), Some(start)) = (self.clock.as_ref(), self.layout.clock) else {
            return Vec::new();
        };
        let ww = self.declaration.width * self.declaration.width;
        (0..clock.classes.len()).map(|c| reach(&self.theta[start + c * ww..start + (c + 1) * ww])).collect()
    }

    /// One cell of the clocks at their level: `u` arrives after `seam`; each clock of `seam` resets
    /// and holds `u`; the return is what the clocks add to the level's output, `Σ_A O_A E(held_A)` on
    /// `2^(−16)`, and the classes held after the cell.
    pub(super) fn clock_step(&self, reaches: &[u64], held: &mut [usize], seam: usize, u: usize) -> Result<Vec<i64>> {
        let (clock, start) = (self.clock.as_ref().expect("a clock"), self.layout.clock.expect("a clock's layout"));
        let (w, a) = (self.declaration.width, self.declaration.alphabet);
        if held.len() != clock.classes.len() {
            return refuse("a clock's state of another shape");
        }
        let t = &self.theta;
        let mut joined = vec![0i64; w];
        let mut part = vec![0i64; w];
        for (c, &class) in clock.classes.iter().enumerate() {
            if class == seam {
                held[c] = u;
            }
            let h = held[c];
            if h >= a {
                continue;
            }
            let e = self.layout.encoding + h * w;
            let o = start + c * w * w;
            affine(&t[o..o + w * w], reaches[c], w, &t[e..e + w], None, 0, MATERIAL_BITS, &mut part)?;
            for (v, p) in joined.iter_mut().zip(&part) {
                *v = fit64(*v as i128 + *p as i128)?;
            }
        }
        Ok(joined)
    }

    /// The clocks' reverse scan over one section at their level: `out` is the covector of each
    /// cell's level output (on `2^(−24)`) and `helds` the classes each cell held. `O_A` takes the
    /// covector against the held class's encoding, and the encoding takes `O_Aᵀ δx` at the held
    /// class; the held class is the passage's, so nothing returns through it.
    pub(super) fn clock_reverse(&self, reaches: &[u64], helds: &[&[usize]], out: &[Vec<i64>], g: &mut [i128]) -> Result<()> {
        let (clock, start) = (self.clock.as_ref().expect("a clock"), self.layout.clock.expect("a clock's layout"));
        let (w, a) = (self.declaration.width, self.declaration.alphabet);
        let t = &self.theta;
        let enc = self.layout.encoding;
        let mut back = vec![0i64; w];
        for c in 0..clock.classes.len() {
            let o = start + c * w * w;
            let cells: Vec<usize> = (0..out.len()).filter(|&i| helds[i][c] < a).collect();
            let ys: Vec<&[i64]> = cells.iter().map(|&i| out[i].as_slice()).collect();
            let xs: Vec<&[i32]> = cells.iter().map(|&i| &t[enc + helds[i][c] * w..enc + (helds[i][c] + 1) * w]).collect();
            outer_sum(&mut g[o..o + w * w], w, &ys, &xs)?;
            for &i in &cells {
                transposed(&t[o..o + w * w], reaches[c], w, &out[i], MATERIAL_BITS, &mut back)?;
                let h = helds[i][c];
                for (slot, &v) in g[enc + h * w..enc + (h + 1) * w].iter_mut().zip(&back) {
                    *slot += v as i128;
                }
            }
        }
        Ok(())
    }
}

/// [definition; agent-inferred, October 26] **One clock's drop in the pool**: the clock of `class`
/// read over a passage's join covectors (record §2).
///
/// ```text
/// c(t) = E(held_t)     M = Σ_t δx_t c(t)ᵀ     C = Σ_t c(t) c(t)ᵀ     drop = tr(M C⁺ Mᵀ)
/// ceiling = Σ_u ‖D_u‖² / n_u,   D_u = Σ_(t: held_t = u) δx_t
/// ```
///
/// `drop` is a ratio of exact integers on `2^(−48)` (the covector's grain squared): the square of the
/// steepest first-order descent the clock's face `O c` can give per unit of the power it adds. The
/// ceiling is what a table of the held class could carry (`contact.context-table-ceiling`), each
/// term released to the nearest `2^(−48)`, so it is read within `followers / 2` of that grain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClockDrop {
    pub class: usize,
    /// The cells a class was held at, and the distinct classes held.
    pub cells: u64,
    pub followers: usize,
    /// The rank of `C`.
    pub rank: usize,
    pub drop_numerator: BigInt,
    pub drop_denominator: BigInt,
    pub ceiling: BigInt,
}

impl ClockDrop {
    /// Whether this drop is larger than `other`'s, exactly.
    pub fn exceeds(&self, other: &Self) -> bool {
        &self.drop_numerator * &other.drop_denominator > &other.drop_numerator * &self.drop_denominator
    }
}

/// [definition; agent-inferred, October 26] **The pool of every class's reset clock** (record §2):
/// the context sums each clock's drop reads, gathered from a frozen tower's join covectors
/// ([`Tower::read_join_covectors`]) stream by stream.
///
/// A clock's face is constant between its resets, so a stream's sums are read from the running sum
/// of its covectors at the reset cells: every cell resets exactly one clock (the clock of the class
/// that arrived before it, or the rest's at the stream's first cell), and the whole pool costs one
/// pass. Integer addition is associative, so streams gathered in any order give the same sums.
#[derive(Clone, Debug, Default)]
pub struct ClockPool {
    /// `(clock, held) ↦ (n, D)`: the cells held and their covectors' sum on `2^(−24)`.
    pub(super) sums: std::collections::HashMap<(usize, usize), (u64, Vec<i128>)>,
    /// `Σ_t ‖δx_t‖²` on `2^(−48)`, and the cells.
    pub energy: i128,
    pub cells: u64,
}

/// A stream's gathering: each clock's open hold (the cell it opened at, the class held and the
/// running sum then), and the running sum.
#[derive(Clone, Debug)]
pub struct ClockStream {
    alphabet: usize,
    previous: usize,
    at: u64,
    running: Vec<i128>,
    open: std::collections::HashMap<usize, (u64, usize, Vec<i128>)>,
}

impl ClockPool {
    /// A stream opened at rest.
    pub fn open_stream(alphabet: usize, width: usize) -> ClockStream {
        ClockStream { alphabet, previous: alphabet, at: 0, running: vec![0; width], open: std::collections::HashMap::new() }
    }

    /// The class `u` arrives in `stream` and its cell's join covector is `dx` (on `2^(−24)`).
    pub fn cell(&mut self, stream: &mut ClockStream, u: usize, dx: &[i64]) -> Result<()> {
        if u >= stream.alphabet || dx.len() != stream.running.len() {
            return refuse("a pool's cell outside its alphabet or width");
        }
        let seam = stream.previous;
        if let Some((from, held, start)) = stream.open.remove(&seam) {
            self.close(stream.at - from, seam, held, &stream.running, &start)?;
        }
        stream.open.insert(seam, (stream.at, u, stream.running.clone()));
        for (r, &v) in stream.running.iter_mut().zip(dx) {
            *r += v as i128;
        }
        let e = dx.iter().try_fold(0i128, |s, &v| s.checked_add(v as i128 * v as i128)).ok_or(TowerError::Refused("a covector's energy outgrew its 128-bit carrier"))?;
        self.energy = self.energy.checked_add(e).ok_or(TowerError::Refused("the pool's energy outgrew its 128-bit carrier"))?;
        self.cells += 1;
        stream.previous = u;
        stream.at += 1;
        Ok(())
    }

    /// The stream's end: every open hold closes.
    pub fn close_stream(&mut self, mut stream: ClockStream) -> Result<()> {
        let open: Vec<_> = stream.open.drain().collect();
        for (clock, (from, held, start)) in open {
            self.close(stream.at - from, clock, held, &stream.running, &start)?;
        }
        Ok(())
    }

    fn close(&mut self, n: u64, clock: usize, held: usize, running: &[i128], start: &[i128]) -> Result<()> {
        let slot = self.sums.entry((clock, held)).or_insert_with(|| (0, vec![0; running.len()]));
        slot.0 += n;
        for ((d, &r), &s) in slot.1.iter_mut().zip(running).zip(start) {
            *d = d.checked_add(r - s).ok_or(TowerError::Refused("a held covector sum outgrew its 128-bit carrier"))?;
        }
        Ok(())
    }

    /// Another pool's sums added to this one's.
    pub fn absorb(&mut self, other: ClockPool) -> Result<()> {
        for (key, (n, d)) in other.sums {
            let slot = self.sums.entry(key).or_insert_with(|| (0, vec![0; d.len()]));
            slot.0 += n;
            for (s, v) in slot.1.iter_mut().zip(d) {
                *s = s.checked_add(v).ok_or(TowerError::Refused("a held covector sum outgrew its 128-bit carrier"))?;
            }
        }
        self.energy = self.energy.checked_add(other.energy).ok_or(TowerError::Refused("the pool's energy outgrew its 128-bit carrier"))?;
        self.cells += other.cells;
        Ok(())
    }

    /// Every clock's drop under `tower`'s encoding, the clocks read in parallel, largest drop first
    /// (ties by class).
    pub fn drops(&self, tower: &Tower) -> Result<Vec<ClockDrop>> {
        let w = tower.declaration.width;
        let mut by_clock: std::collections::BTreeMap<usize, Vec<(usize, u64, &[i128])>> = std::collections::BTreeMap::new();
        for (&(clock, held), (n, d)) in &self.sums {
            by_clock.entry(clock).or_default().push((held, *n, d.as_slice()));
        }
        let mut drops: Vec<ClockDrop> = by_clock
            .into_par_iter()
            .map(|(clock, mut held)| {
                held.sort_by_key(|h| h.0);
                clock_drop(clock, &held, w, |u| tower.encoding(u))
            })
            .collect::<Result<_>>()?;
        drops.sort_by(|x, y| if x.exceeds(y) { std::cmp::Ordering::Less } else if y.exceeds(x) { std::cmp::Ordering::Greater } else { x.class.cmp(&y.class) });
        Ok(drops)
    }
}

/// One clock's drop from its held sums: `C = Σ n E Eᵀ` and `M = Σ D Eᵀ` exactly, then the bordered
/// fraction-free elimination of `C`, whose `M` diagonal ends at `−d (M C⁺ Mᵀ)_jj`, `d` the last
/// pivot that is not zero.
fn clock_drop<'a>(class: usize, held: &[(usize, u64, &[i128])], w: usize, encoding: impl Fn(usize) -> &'a [i32]) -> Result<ClockDrop> {
    let wide = |what| TowerError::Refused(what);
    let mut c = vec![0i128; w * w];
    let mut m = vec![0i128; w * w];
    let mut ceiling = BigInt::zero();
    let mut cells = 0u64;
    for &(u, n, d) in held {
        let e = encoding(u);
        cells += n;
        for i in 0..w {
            let ne = (n as i128).checked_mul(e[i] as i128).ok_or_else(|| wide("a clock's Gram outgrew its 128-bit carrier"))?;
            for k in 0..w {
                c[i * w + k] = ne.checked_mul(e[k] as i128).and_then(|x| c[i * w + k].checked_add(x)).ok_or_else(|| wide("a clock's Gram outgrew its 128-bit carrier"))?;
                m[i * w + k] = d[i].checked_mul(e[k] as i128).and_then(|x| m[i * w + k].checked_add(x)).ok_or_else(|| wide("a clock's cross sum outgrew its 128-bit carrier"))?;
            }
        }
        // ‖D‖² / n to the nearest 2^(−48).
        let norm: BigInt = d.iter().map(|&x| BigInt::from(x) * BigInt::from(x)).sum();
        let n = BigInt::from(n);
        ceiling += (&norm * 2 + &n) / (&n * 2);
    }
    // The bordered matrix: rows 0..w the Gram (upper part kept), rows w..2w the cross sum's rows and
    // their diagonal, which opens at zero.
    let mut g: Vec<Vec<BigInt>> = (0..w).map(|i| (0..w).map(|k| BigInt::from(c[i * w + k])).collect()).collect();
    let mut cross: Vec<Vec<BigInt>> = (0..w).map(|j| (0..w).map(|k| BigInt::from(m[j * w + k])).collect()).collect();
    let mut diag = vec![BigInt::zero(); w];
    let mut last = BigInt::from(1);
    let mut rank = 0;
    for p in 0..w {
        let pivot = g[p][p].clone();
        if pivot.is_zero() {
            if (p + 1..w).any(|k| !g[p][k].is_zero()) || cross.iter().any(|row| !row[p].is_zero()) {
                return refuse("a zero pivot with a nonzero row: the clock's Gram is not positive semidefinite");
            }
            continue;
        }
        rank += 1;
        let row: Vec<BigInt> = g[p].clone();
        for i in p + 1..w {
            let gip = g[i][p].clone();
            for k in i..w {
                let v = (&pivot * &g[i][k] - &gip * &row[k]) / &last;
                g[i][k] = v.clone();
                g[k][i] = v;
            }
        }
        for j in 0..w {
            let mjp = cross[j][p].clone();
            if mjp.is_zero() {
                for k in p + 1..w {
                    cross[j][k] = &pivot * &cross[j][k] / &last;
                }
                diag[j] = &pivot * &diag[j] / &last;
                continue;
            }
            for k in p + 1..w {
                cross[j][k] = (&pivot * &cross[j][k] - &mjp * &row[k]) / &last;
            }
            diag[j] = (&pivot * &diag[j] - &mjp * &mjp) / &last;
        }
        last = pivot;
    }
    let numerator: BigInt = -diag.iter().sum::<BigInt>();
    if numerator.is_negative() {
        return refuse("a clock's drop below zero: the elimination is not exact");
    }
    Ok(ClockDrop { class, cells, followers: held.len(), rank, drop_numerator: numerator, drop_denominator: last, ceiling })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The bordered elimination returns `tr(M C⁺ Mᵀ)` exactly: on independent encodings it is the
    /// table's ceiling `Σ ‖D_u‖²/n_u`, and on a dependent pair it is the projection's.
    #[test]
    fn a_clock_drop_is_the_projection_of_its_covector_sums() {
        // w = 2, encodings e1 = (1, 0), e2 = (0, 1): independent, so drop = |D1|²/n1 + |D2|²/n2.
        let enc = [vec![1i32, 0], vec![0, 1], vec![1, 1]];
        let d1 = [3i128, 4];
        let d2 = [-2i128, 6];
        let held = [(0usize, 2u64, &d1[..]), (1, 4, &d2[..])];
        let r = clock_drop(7, &held, 2, |u| enc[u].as_slice()).unwrap();
        // 25/2 + 40/4 = 45/2.
        assert_eq!(&r.drop_numerator * BigInt::from(2), BigInt::from(45) * &r.drop_denominator);
        assert_eq!(r.rank, 2);
        assert_eq!(r.ceiling, BigInt::from(13 + 10)); // 12.5 rounds to 13 at the grain
        // One encoding (1, 1) held at two classes of the same face is one direction: C = (n1 + n2) e eᵀ,
        // M = (D1 + D2) eᵀ, drop = |D1 + D2|² / (n1 + n2) = |(1, 10)|²/6 = 101/6.
        let held = [(2usize, 2u64, &d1[..]), (2, 4, &d2[..])];
        let r = clock_drop(7, &held, 2, |u| enc[u].as_slice()).unwrap();
        assert_eq!(&r.drop_numerator * BigInt::from(6), BigInt::from(101) * &r.drop_denominator);
        assert_eq!(r.rank, 1);
    }

    /// A stream's holds: each cell resets the clock of the class before it, and the sums each clock
    /// gathers are the covectors of the cells it held.
    #[test]
    fn a_pool_gathers_each_clock_over_the_cells_it_holds() {
        let mut pool = ClockPool::default();
        let mut s = ClockPool::open_stream(3, 1);
        // Arrivals 0 1 0 2, covectors 1 10 100 1000; the rest is class 3.
        for (u, dx) in [(0usize, 1i64), (1, 10), (0, 100), (2, 1000)] {
            pool.cell(&mut s, u, &[dx]).unwrap();
        }
        pool.close_stream(s).unwrap();
        // rest: holds 0 over every cell (1111); clock 0: resets at cells 1 and 3, holding 1 over
        // cell 1..2 (10 + 100) and 2 over cell 3 (1000); clock 1: resets at cell 2, holding 0 over
        // cells 2..3 (1100).
        let get = |c: usize, h: usize| pool.sums.get(&(c, h)).map(|(n, d)| (*n, d[0]));
        assert_eq!(get(3, 0), Some((4, 1111)));
        assert_eq!(get(0, 1), Some((2, 110)));
        assert_eq!(get(0, 2), Some((1, 1000)));
        assert_eq!(get(1, 0), Some((2, 1100)));
        assert_eq!(pool.sums.len(), 4);
        assert_eq!(pool.energy, 1 + 100 + 10_000 + 1_000_000);
    }
}
