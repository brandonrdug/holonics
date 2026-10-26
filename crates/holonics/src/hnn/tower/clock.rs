//! **The reset clock: a navigator's clock that holds the arrival after its class, copied at the
//! output** (#404, #405, #386).
//!
//! [definition; records
//! `2026-10-26_THE_ROLE_KEY_IS_A_RESET_CLOCK_THE_POOL_FOUNDS_AND_ITS_ACCEPTANCE_IS_FIXED_BEFORE_THE_BUILD.md`
//! §1 and
//! `2026-10-26_THE_CLOCK_GAINS_ONLY_WHERE_ITS_ARRIVAL_RECURS_SO_ITS_JOIN_BECOMES_A_COPY_AT_THE_OUTPUT_AND_ITS_ACCEPTANCE_IS_FIXED_BEFORE_THE_BUILD.md`
//! §3] Why it is built. The bank's read at a named answer's opening never reaches the name the
//! question opened on: a key the passage reaches only by diffusion is read to its square root, and
//! the slow mode is founded, not waited for. A reset clock of class `A` resets when `A` arrives and
//! holds the arrival that follows. Its join is a copy at the readout: the held class's logit alone
//! takes a weight read from the face the readout reads, opening at zero:
//!
//! ```text
//! held_t  = u_t          when u_(t−1) = A      (the rest counts as a class, `A = alphabet`)
//!         = held_(t−1)   otherwise; nothing is held before the first reset
//! copy    z_t[held_t] += ⟨r_A, x_t⟩ + b_A       r_A: d entries on 2^(−24), b_A on 2^(−16), opening at zero
//! reverse G_(r_A) = Σ_t δz_t[held_t] x_t,  G_(b_A) = Σ_t δz_t[held_t],  δx_t += δz_t[held_t] r_A
//! ```
//!
//! - **Why the output.** The clock's first join, `O_A E(held_t)` at the first level's output, added a
//!   direction for each held class at every cell. Founded on the blank line's clock, its pass gained
//!   0.417 bits a cell on the 1,168 held-out cells that repeat the held arrival and paid on every
//!   other cell, 12,813.3 bits above its twin in all (the record's §1). The copy has one coordinate
//!   of the readout's covector a cell and one row for every held class, so a mean covector for each
//!   held class has no direction to land in.
//! - **What it is.** The face table's `x`-alone block (atlas `contact.face-table-blocks`): the pair
//!   contact between the next arrival and the held one, whose lock is the cancellation of the slip
//!   `[u_(t+1) ≠ held_t]`, at the offset the clock's reset locates (the passage node lock reads the
//!   same lock where its tree locates it, `hnn.passage-node-lock`). Whether the held arrival recurs
//!   at a cell is what the tower's state says, through `⟨r_A, x_t⟩ + b_A`.
//! - **Retention.** The clock's state is the held class alone ([`TowerState::held`]): the
//!   future-sufficient quotient of what it reads, no tape and no window.
//! - **Every medium.** The law names a class and the readout, so it is the same object over any
//!   codec's units.
//! - **The opening.** `r_A` and `b_A` open at zero, so a clocked tower reads every passage
//!   bit-identically to its twin, and the covector moves them from the first deposit. Each clock's
//!   material follows every other face's, so a tower's text and its other faces stay as they are.
//! - **The founding.** Which class is clocked is the pool's choice ([`ClockPool`]): every class's
//!   clock and the rest's, ranked by the exact drop at the copy's port, never named by a designer.
use super::*;
use num_bigint::BigInt;
use num_traits::{Signed, Zero};

/// [definition; agent-inferred, October 26] **The clocks' declared law**: the classes that reset
/// them, in the order they were founded (`alphabet` is the rest).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClockDeclaration {
    pub classes: Vec<usize>,
}

impl ClockDeclaration {
    fn check(&self, d: &TowerDeclaration) -> Result<()> {
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
        format!("clock {classes}\n")
    }

    pub(super) fn from_text(line: &str, d: &TowerDeclaration) -> Result<Self> {
        let words: Vec<&str> = line.split(' ').collect();
        let num = |s: &str| s.parse::<usize>().map_err(|_| TowerError::Refused("a clock's line that is not counts"));
        if words.len() < 2 || words[0] != "clock" {
            return refuse("not a clock's line");
        }
        let clock = Self { classes: words[1..].iter().map(|w| num(w)).collect::<Result<_>>()? };
        clock.check(d)?;
        Ok(clock)
    }
}

impl Tower {
    /// [agent-inferred, October 26] **A reset clock joined to the tower**: the clock of `class`,
    /// its copy's row and bias appended after every other face's material at zero, so the clocked
    /// tower reads every passage exactly as the tower did, and the section's covector moves it from
    /// there. A stream rested before the join carries no clock: rest it again.
    pub fn join_clock(&mut self, class: usize) -> Result<()> {
        let d = self.declaration;
        let mut clock = self.clock.clone().unwrap_or(ClockDeclaration { classes: Vec::new() });
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

    /// The material range of the clocks' copies, each clock's row `r_A` and its bias `b_A` in
    /// turn, when any is joined.
    pub fn clock_join(&self) -> Option<std::ops::Range<usize>> {
        let (clock, start) = (self.clock.as_ref()?, self.layout.clock?);
        Some(start..start + clock.classes.len() * (self.declaration.width + 1))
    }

    /// The clocks' state at rest: nothing held.
    pub(super) fn clock_rest(&self) -> Vec<usize> {
        vec![self.declaration.alphabet; self.clock.as_ref().map_or(0, |c| c.classes.len())]
    }

    /// Each clock's row reach.
    pub(super) fn clock_reaches(&self) -> Vec<u64> {
        let (Some(clock), Some(start)) = (self.clock.as_ref(), self.layout.clock) else {
            return Vec::new();
        };
        let w = self.declaration.width;
        (0..clock.classes.len()).map(|c| reach(&self.theta[start + c * (w + 1)..start + c * (w + 1) + w])).collect()
    }

    /// One cell of the clocks: `u` arrives after `seam`, and each clock of `seam` resets and holds
    /// `u`.
    pub(super) fn clock_reset(&self, held: &mut [usize], seam: usize, u: usize) -> Result<()> {
        let clock = self.clock.as_ref().expect("a clock");
        if held.len() != clock.classes.len() {
            return refuse("a stream rested before the clock joined carries no clock: rest it again");
        }
        for (h, &class) in held.iter_mut().zip(&clock.classes) {
            if class == seam {
                *h = u;
            }
        }
        Ok(())
    }

    /// The clocks' copies at the readout: each clock holding a class adds `⟨r_A, x⟩ + b_A` to that
    /// class's logit, on `2^(−40)` released to the logit's `2^(−16)` as the readout is.
    pub(super) fn clock_copy(&self, reaches: &[u64], held: &[usize], x: &[i32], z: &mut [i64]) -> Result<()> {
        for (&h, raise) in held.iter().zip(self.clock_raises(reaches, held, x)?) {
            if let Some(v) = raise {
                z[h] = fit64(z[h] as i128 + v as i128)?;
            }
        }
        Ok(())
    }

    /// Each clock's raise `⟨r_A, x⟩ + b_A` on the logit's `2^(−16)`, none where it holds nothing.
    fn clock_raises(&self, reaches: &[u64], held: &[usize], x: &[i32]) -> Result<Vec<Option<i64>>> {
        let start = self.layout.clock.expect("a clock's layout");
        let (w, a) = (self.declaration.width, self.declaration.alphabet);
        let t = &self.theta;
        held.iter()
            .enumerate()
            .map(|(c, &h)| {
                if h >= a {
                    return Ok(None);
                }
                let row = start + c * (w + 1);
                let mut v = [0i64; 1];
                affine(&t[row..row + w], reaches[c], w, x, Some(&t[row + w..row + w + 1]), MATERIAL_BITS, MATERIAL_BITS, &mut v)?;
                Ok(Some(v[0]))
            })
            .collect()
    }

    /// The copies' reverse scan over one section: `dzs` is each cell's readout covector (on
    /// `2^(−24)`), `tops` the faces the readout read and `helds` the classes each cell held. Each
    /// copy takes the held class's coordinate of the covector against the face, and returns it to
    /// the face through its row; the held class is the passage's, so nothing returns through it.
    pub(super) fn clock_reverse(&self, reaches: &[u64], helds: &[&[usize]], dzs: &[Vec<i64>], tops: &[&[i32]], dx: &mut [Vec<i64>], g: &mut [i128]) -> Result<()> {
        let (clock, start) = (self.clock.as_ref().expect("a clock"), self.layout.clock.expect("a clock's layout"));
        let (w, a) = (self.declaration.width, self.declaration.alphabet);
        let t = &self.theta;
        let mut back = vec![0i64; w];
        for c in 0..clock.classes.len() {
            let row = start + c * (w + 1);
            let cells: Vec<usize> = (0..dzs.len()).filter(|&i| helds[i][c] < a).collect();
            let ys: Vec<[i64; 1]> = cells.iter().map(|&i| [dzs[i][helds[i][c]]]).collect();
            let xs: Vec<&[i32]> = cells.iter().map(|&i| tops[i]).collect();
            outer_sum(&mut g[row..row + w], w, &ys, &xs)?;
            for (&i, y) in cells.iter().zip(&ys) {
                g[row + w] += y[0] as i128;
                transposed(&t[row..row + w], reaches[c], w, y, MATERIAL_BITS, &mut back)?;
                for (v, &e) in dx[i].iter_mut().zip(&back) {
                    *v = fit64(*v as i128 + e as i128)?;
                }
            }
        }
        Ok(())
    }

    /// [agent-inferred, October 26] **The pool's reading**: the frozen tower reads `classes` from
    /// the state, and each cell's arriving class, the face the readout reads and the readout's
    /// covector against the class that arrives next (`p̂ − q` on `2^(−24)`) are handed to the pool's
    /// stream ([`ClockPool::cell`]). A reading beside the code: the tower is not moved, and the
    /// pool keeps only its sums, never the cells. The covector is the readout's, so no reverse scan
    /// is read.
    pub fn read_clock_pool(&self, state: &mut TowerState, classes: &[usize], pool: &mut ClockPool, stream: &mut ClockStream) -> Result<()> {
        let reaches = self.reaches();
        for i in 0..classes.len().saturating_sub(1) {
            let cell = self.step(state, classes[i], &reaches)?;
            pool.cell(stream, classes[i], &cell.top, &covector(&cell.face, classes[i + 1]))?;
        }
        Ok(())
    }

    /// [agent-inferred, October 26; record
    /// `2026-10-26_THE_THIRD_LAP_FOUNDS_THE_CLOCK_AFTER_EQUALS_AND_ITS_PASS_LOWERS_THE_ROLE_FROM_53_TO_43.md`
    /// §4] **The copies' reading**: the frozen tower reads `classes` from the state, and each cell's
    /// index, face (the masses of the class that arrives next), each clock's held class (the
    /// alphabet where it holds nothing) and its copy's raise `⟨r_A, x⟩ + b_A` on the logit's
    /// `2^(−16)` are handed to `each`. A reading beside the code: the tower is not moved. Refused
    /// without a clock.
    pub fn read_clocks(&self, state: &mut TowerState, classes: &[usize], mut each: impl FnMut(usize, &TowerFace, &[usize], &[Option<i64>]) -> Result<()>) -> Result<()> {
        if self.clock.is_none() {
            return refuse("a copies' reading needs a clock");
        }
        let reaches = self.reaches();
        for i in 0..classes.len().saturating_sub(1) {
            let cell = self.step(state, classes[i], &reaches)?;
            let held = cell.clock.as_deref().expect("a clocked tower's cell holds its clocks");
            let raises = self.clock_raises(&reaches.clock, held, &cell.top)?;
            each(i, &cell.face, held, &raises)?;
        }
        Ok(())
    }
}

/// [definition; agent-inferred, October 26] **One clock's drop in the pool**: the clock of `class`
/// read at the copy's port over a passage (the record's §4).
///
/// ```text
/// x̄_t = (x_t, 1)    M = Σ_(t held) δz_t[held_t] x̄_t    C = Σ_(t held) x̄_t x̄_tᵀ    drop = Mᵀ C⁺ M
/// ```
///
/// `drop` is a ratio of exact integers, on the covector's grain squared beside the face's: the
/// square of the steepest first-order descent the copy `⟨r, x̄⟩` can give its held class's logit per
/// unit of the power it adds there, which does not depend on the scale of `x̄`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClockDrop {
    pub class: usize,
    /// The cells the clock held a class at.
    pub cells: u64,
    /// The rank of `C`.
    pub rank: usize,
    pub drop_numerator: BigInt,
    pub drop_denominator: BigInt,
}

impl ClockDrop {
    /// Whether this drop is larger than `other`'s, exactly.
    pub fn exceeds(&self, other: &Self) -> bool {
        &self.drop_numerator * &other.drop_denominator > &other.drop_numerator * &self.drop_denominator
    }
}

/// [definition; agent-inferred, October 26] **The pool of every class's reset clock** (the record's
/// §4): the sums each clock's drop reads at the copy's port, gathered from a frozen tower's
/// readout ([`Tower::read_clock_pool`]) stream by stream.
///
/// Every cell resets exactly one clock (the clock of the class that arrived before it, or the
/// rest's at the stream's first cell), and every clock holding a class there takes that class's
/// coordinate of the covector against the face: `(alphabet + 1)·(d + 1)` products a cell. A clock's
/// Gram is the passage's less, in each stream, the cells before its first reset there, read from
/// the stream's running Gram at that reset. Integer addition is associative, so streams gathered in
/// any order give the same sums.
#[derive(Clone, Debug)]
pub struct ClockPool {
    alphabet: usize,
    /// `d + 1`: the face and its unit.
    width: usize,
    /// Each clock's cells held (the rest's last).
    held_cells: Vec<u64>,
    /// Each clock's `M`, `d + 1` entries a clock: `Σ δz[held] x̄` on `2^(−40)`, the unit's entry on
    /// `2^(−24)`.
    cross: Vec<i128>,
    /// Each clock's Gram over the cells before its first reset in each stream, summed over the
    /// streams, packed upper (`(d + 1)(d + 2)/2` entries a clock).
    before: Vec<i128>,
    /// `Σ_t x̄_t x̄_tᵀ` over every cell, packed upper.
    gram: Vec<i128>,
    /// `Σ_t ‖δz_t‖²` on `2^(−48)`, and the cells.
    pub energy: i128,
    pub cells: u64,
}

/// A stream's gathering: the class before the next cell, each clock's held class (the alphabet
/// where nothing is held yet) and the stream's running Gram.
#[derive(Clone, Debug)]
pub struct ClockStream {
    previous: usize,
    held: Vec<usize>,
    running: Vec<i128>,
}

fn packed(k: usize) -> usize {
    k * (k + 1) / 2
}

impl ClockPool {
    /// An empty pool for an alphabet of `alphabet` classes and faces of `width` entries.
    pub fn new(alphabet: usize, width: usize) -> Self {
        let (clocks, k) = (alphabet + 1, width + 1);
        Self { alphabet, width: k, held_cells: vec![0; clocks], cross: vec![0; clocks * k], before: vec![0; clocks * packed(k)], gram: vec![0; packed(k)], energy: 0, cells: 0 }
    }

    /// A stream opened at rest.
    pub fn open_stream(&self) -> ClockStream {
        ClockStream { previous: self.alphabet, held: vec![self.alphabet; self.alphabet + 1], running: vec![0; packed(self.width)] }
    }

    /// The class `u` arrives in `stream`, the readout reads `top` (on `2^(−16)`) at its cell and the
    /// readout's covector there is `dz` (on `2^(−24)`). The products are bounded by `2^31 · 2^31`
    /// and `2^24 · 2^31` a cell, so a pool of fewer than `2^60` cells sums them in `i128` exactly.
    pub fn cell(&mut self, stream: &mut ClockStream, u: usize, top: &[i32], dz: &[i64]) -> Result<()> {
        let (a, k) = (self.alphabet, self.width);
        if u >= a || top.len() + 1 != k || dz.len() != a || stream.held.len() != a + 1 {
            return refuse("a pool's cell outside its alphabet or width");
        }
        let seam = stream.previous;
        if stream.held[seam] == a {
            // The clock's first reset in this stream: the cells before it held nothing.
            let slot = &mut self.before[seam * packed(k)..(seam + 1) * packed(k)];
            for (b, &r) in slot.iter_mut().zip(&stream.running) {
                *b += r;
            }
        }
        stream.held[seam] = u;
        let bar: Vec<i128> = top.iter().map(|&v| v as i128).chain([1]).collect();
        for (clock, &h) in stream.held.iter().enumerate() {
            if h == a {
                continue;
            }
            self.held_cells[clock] += 1;
            let y = dz[h] as i128;
            if y != 0 {
                for (m, &x) in self.cross[clock * k..(clock + 1) * k].iter_mut().zip(&bar) {
                    *m += y * x;
                }
            }
        }
        let mut at = 0;
        for i in 0..k {
            for j in i..k {
                let p = bar[i] * bar[j];
                stream.running[at] += p;
                self.gram[at] += p;
                at += 1;
            }
        }
        self.energy += dz.iter().map(|&v| v as i128 * v as i128).sum::<i128>();
        self.cells += 1;
        stream.previous = u;
        Ok(())
    }

    /// Another pool's sums added to this one's.
    pub fn absorb(&mut self, other: ClockPool) -> Result<()> {
        if other.alphabet != self.alphabet || other.width != self.width {
            return refuse("pools of another alphabet or width");
        }
        let add = |s: &mut [i128], o: &[i128]| s.iter_mut().zip(o).for_each(|(s, o)| *s += o);
        add(&mut self.cross, &other.cross);
        add(&mut self.before, &other.before);
        add(&mut self.gram, &other.gram);
        for (s, o) in self.held_cells.iter_mut().zip(&other.held_cells) {
            *s += o;
        }
        self.energy += other.energy;
        self.cells += other.cells;
        Ok(())
    }

    /// The clock of `class`'s cells held, `M` and `C` (full, row-major).
    pub fn sums(&self, class: usize) -> (u64, Vec<i128>, Vec<i128>) {
        let k = self.width;
        let (gram, before) = (&self.gram, &self.before[class * packed(k)..(class + 1) * packed(k)]);
        let mut c = vec![0i128; k * k];
        let mut at = 0;
        for i in 0..k {
            for j in i..k {
                let v = gram[at] - before[at];
                c[i * k + j] = v;
                c[j * k + i] = v;
                at += 1;
            }
        }
        (self.held_cells[class], self.cross[class * k..(class + 1) * k].to_vec(), c)
    }

    /// Every clock that held a cell, its drop read, the clocks read in parallel, largest drop first
    /// (ties by class).
    pub fn drops(&self) -> Result<Vec<ClockDrop>> {
        let mut drops: Vec<ClockDrop> = (0..=self.alphabet)
            .into_par_iter()
            .filter(|&class| self.held_cells[class] > 0)
            .map(|class| {
                let (cells, m, c) = self.sums(class);
                let (numerator, denominator, rank) = projected(&c, &m, self.width)?;
                Ok(ClockDrop { class, cells, rank, drop_numerator: numerator, drop_denominator: denominator })
            })
            .collect::<Result<_>>()?;
        drops.sort_by(|x, y| if x.exceeds(y) { std::cmp::Ordering::Less } else if y.exceeds(x) { std::cmp::Ordering::Greater } else { x.class.cmp(&y.class) });
        Ok(drops)
    }
}

/// `Mᵀ C⁺ M` for a positive semidefinite `C` (`k × k`, row-major) by the bordered fraction-free
/// elimination of `C`: the border's diagonal opens at zero and ends at `−d (Mᵀ C⁺ M)`, `d` the last
/// pivot that is not zero. Returns the numerator, that pivot and the rank of `C`.
fn projected(c: &[i128], m: &[i128], k: usize) -> Result<(BigInt, BigInt, usize)> {
    let mut g: Vec<Vec<BigInt>> = (0..k).map(|i| (0..k).map(|j| BigInt::from(c[i * k + j])).collect()).collect();
    let mut cross: Vec<BigInt> = m.iter().map(|&v| BigInt::from(v)).collect();
    let mut diag = BigInt::zero();
    let mut last = BigInt::from(1);
    let mut rank = 0;
    for p in 0..k {
        let pivot = g[p][p].clone();
        if pivot.is_zero() {
            if (p + 1..k).any(|j| !g[p][j].is_zero()) || !cross[p].is_zero() {
                return refuse("a zero pivot with a nonzero row: the clock's Gram is not positive semidefinite");
            }
            continue;
        }
        rank += 1;
        let row: Vec<BigInt> = g[p].clone();
        for i in p + 1..k {
            let gip = g[i][p].clone();
            for j in i..k {
                let v = (&pivot * &g[i][j] - &gip * &row[j]) / &last;
                g[i][j] = v.clone();
                g[j][i] = v;
            }
        }
        let mp = cross[p].clone();
        for j in p + 1..k {
            cross[j] = (&pivot * &cross[j] - &mp * &row[j]) / &last;
        }
        diag = (&pivot * &diag - &mp * &mp) / &last;
        last = pivot;
    }
    let numerator = -diag;
    if numerator.is_negative() {
        return refuse("a clock's drop below zero: the elimination is not exact");
    }
    Ok((numerator, last, rank))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The bordered elimination returns `Mᵀ C⁺ M` exactly, at full rank and below it.
    #[test]
    fn a_clock_drop_is_the_projection_of_its_covector_sums() {
        // C = diag(2, 4), M = (3, 4): 9/2 + 16/4 = 17/2.
        let (n, d, rank) = projected(&[2, 0, 0, 4], &[3, 4], 2).unwrap();
        assert_eq!(n * BigInt::from(2), BigInt::from(17) * d);
        assert_eq!(rank, 2);
        // C = v vᵀ with v = (1, 1) is one direction: C⁺ = v vᵀ/4, M = (2, 2), Mᵀ C⁺ M = 16/4 = 4.
        let (n, d, rank) = projected(&[1, 1, 1, 1], &[2, 2], 2).unwrap();
        assert_eq!(n, BigInt::from(4) * d);
        assert_eq!(rank, 1);
        // A covector outside the Gram's range is refused, not projected away.
        assert!(projected(&[1, 1, 1, 1], &[2, 3], 2).is_err());
    }

    /// A stream's holds: each cell resets the clock of the class before it, every clock holding a
    /// class takes that class's coordinate of the covector against the face and its unit, and a
    /// clock's Gram leaves out the cells before its first reset.
    #[test]
    fn a_pool_gathers_each_clock_over_the_cells_it_holds() {
        let mut pool = ClockPool::new(3, 1);
        let mut s = pool.open_stream();
        // Arrivals 0 1 0 2 with faces 1 2 3 4; covector `dz[c] = 10^c · (cell + 1)`. The rest is 3.
        let faces = [1i32, 2, 3, 4];
        for (t, &u) in [0usize, 1, 0, 2].iter().enumerate() {
            let dz: Vec<i64> = (0..3).map(|c| 10i64.pow(c as u32) * (t as i64 + 1)).collect();
            pool.cell(&mut s, u, &[faces[t]], &dz).unwrap();
        }
        // rest: holds 0 at every cell: M = Σ dz_t[0] (x_t, 1) = (1·1 + 2·2 + 3·3 + 4·4, 1 + 2 + 3 + 4).
        assert_eq!(pool.sums(3).0, 4);
        assert_eq!(pool.sums(3).1, vec![30, 10]);
        // clock 0: resets at cells 1 and 3, holding 1 over cells 1..2 and 2 at cell 3:
        // M = 20·(2, 1) + 30·(3, 1) + 400·(4, 1).
        let (n, m, c) = pool.sums(0);
        assert_eq!((n, m), (3, vec![40 + 90 + 1600, 20 + 30 + 400]));
        // Its Gram leaves out cell 0: Σ_(t ≥ 1) (x_t, 1)(x_t, 1)ᵀ.
        assert_eq!(c, vec![4 + 9 + 16, 2 + 3 + 4, 2 + 3 + 4, 3]);
        // clock 1: resets at cell 2, holding 0 at cells 2..3: M = 3·(3, 1) + 4·(4, 1).
        assert_eq!(pool.sums(1).1, vec![9 + 16, 7]);
        assert_eq!(pool.sums(2).0, 0);
        assert_eq!(pool.drops().unwrap().len(), 3);
        assert_eq!(pool.energy, (1..=4).map(|t| t * t * (1 + 100 + 10_000)).sum::<i128>());
    }
}
