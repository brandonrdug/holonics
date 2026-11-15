//! **Readings no law consumes.**
//!
//! a ruler measures the machine on a saved state or beside a run: it changes neither what the state carries nor what the
//! deposit consumes
//!
//! Kind: readings. Kernels: `field_yard_*` and readings' gathers (`hnn/profile.rs`).
//! Lean: none.
//! Atlas: `tower.field-card-realization`, `tower.field-carried-founding`, `tower.field-echo`, `tower.field-reaction-mirror`,
//! `tower.field-read-free-fall`, `tower.field-redraw`, `tower.field-state-charge`, `tower.field-tick-return`.
//! Records: THE_ENGINE §3. The derivations' history is in the records; the items below keep their reasons.

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use rayon::prelude::*;

/// [measurement; agent-inferred, November 2] **A held read's rows at the answer sites by where their mass
/// lies** ([`Constitution::held_rows`]), one cell a tick and head, over the unresolved sites of the regions read:
/// the rows, and the shares (on `2^(−63)`, summed) of the sources of three groups: `question`, the definite
/// sites before the region's answer start; `soft_near`, the near field's sources that are not definite
/// (unresolved or soft answer neighbours); `other`, everything else (the far definite sites, the near
/// definite sites at or past the answer start, the crowds). `question_current` is the current's part from the
/// question group, `Σ p · Σ_x |D ṽ_x|` over its sources (each source's `release(p Σ_x |D ṽ_x|, 63)`, on the
/// value's grain).
/// [measurement; agent-inferred, November 2] The question's far part (§16.19's far-contact review): `question_far`, the
/// shares of the question sources past the near field (`|i − j| ≥ NEAR`); per row its collision
/// `C = Σ release(p², 63)` over them, and where `C > 0` its effective count of far sources, the Rényi-2 count
/// `(Σ p)² / Σ p²` (a lower bound of `2^H`), on `2^(−8)`, summed in `far_effective` over the `far_rows` rows
/// counted. Region-level groups only: no source is paired with a receiver by its class.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HeldRows {
    pub rows: u64,
    pub question: u128,
    pub soft_near: u128,
    pub other: u128,
    pub question_current: i128,
    pub question_far: u128,
    pub far_effective: u128,
    pub far_rows: u64,
    /// [measurement; agent-inferred, November 3, §16.31] The shares of the near field's definite sources at or past the
    /// answer start (the answer's own resolved neighbours, `|i − j| < NEAR`), taken out of `other`.
    pub near_definite: u128,
}

/// [measurement; November 15, the theory thread's T6 (#841, `contact.crowd-slip-bound`)] **An open row's shares by where they lie**
/// ([`Constitution::open_rows`]): at each tick and head (`[tick · heads + head]`), over a region's open receivers (not definite), the
/// shares on `2^(−63)`, summed: `near` the near field's (`|i − j| < NEAR`), `crowd` the crowds' (none on an open row under the present law,
/// §15.9), and the far sources' by octave `⌊log₂|i − j|⌋` (`OPEN_OCTAVES` bins, the last holding every farther source), each split by whether
/// the source's class is one the receiver probes (its own probed class or a class it probes across its seams: `[octave][probed]`). For each
/// row and octave with a far share it adds the Rényi-2 count of its far sources `(Σ p)² / Σ p²` on `2^(−8)` (a lower bound of `2^H`) and its
/// largest share over their sum on `2^(−16)`, and counts the row. A reading: nothing in the law reads it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct OpenRows {
    pub rows: u64,
    pub near: u128,
    pub crowd: u128,
    pub far: [[u128; 2]; OPEN_OCTAVES],
    pub effective: [[u128; 2]; OPEN_OCTAVES],
    pub peak: [[u128; 2]; OPEN_OCTAVES],
    pub counted: [[u64; 2]; OPEN_OCTAVES],
}

/// The octaves of distance an [`OpenRows`] reading keeps apart (the last holds every farther source).
pub const OPEN_OCTAVES: usize = 16;

impl OpenRows {
    /// The sum of two readings of the same cell.
    pub fn add(&mut self, o: &Self) {
        self.rows += o.rows;
        self.near += o.near;
        self.crowd += o.crowd;
        for b in 0..OPEN_OCTAVES {
            for k in 0..2 {
                self.far[b][k] += o.far[b][k];
                self.effective[b][k] += o.effective[b][k];
                self.peak[b][k] += o.peak[b][k];
                self.counted[b][k] += o.counted[b][k];
            }
        }
    }
}

/// [measurement; November 15, T7 of the theory thread's #841, `contact.crowd-slip-bound`] **An open row's far pairs heard as crowds where a
/// band admits them** ([`Constitution::open_crowds`]): at each tick and head (`[tick · heads + head]`), over a region's open receivers, each
/// octave's crowd of definite sources on each side (`crowd_ranges`) tested by the band `B_C = Σ_r (max − min of q_r on I_r)`, `q_r(c) =
/// 2^(g+1) a_r c − c²` the lock's real `r` (the receiver's framed probe `a`), `I_r` the hull of `{D_lo, D_hi} × {min_r, max_r}` over the
/// crowd's members (their framed unit words and their skins), admitted as one source where `T B_C` on the face's grain stands at or under
/// `ε = 2^(FACE_BITS − 4)` (a sixteenth of a bit), else split into its halves down to members. Beside it the same test on the members' own
/// locks (`max − min` of their bases, the band's floor). By octave (`OPEN_OCTAVES` bins): the far pairs met, the terms after the band's
/// split and after the locks' own, and the crowds admitted whole. A reading only.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct OpenCrowds {
    pub rows: u64,
    pub pairs: [u64; OPEN_OCTAVES],
    pub band_terms: [u64; OPEN_OCTAVES],
    pub lock_terms: [u64; OPEN_OCTAVES],
    pub crowds: [u64; OPEN_OCTAVES],
    pub band_whole: [u64; OPEN_OCTAVES],
    pub lock_whole: [u64; OPEN_OCTAVES],
    /// The terms the band's and the locks' splits leave at the wider tolerances of [`OPEN_TOLERANCES`] (`[tolerance][octave]`).
    pub band_at: [[u64; OPEN_OCTAVES]; 3],
    pub lock_at: [[u64; OPEN_OCTAVES]; 3],
    /// [the theory thread, 19:03Z] The floor of any grouping of a crowd's members by their own locks, `N(ε)`: the fewest intervals of width
    /// `ε` on the face's grain that cover the members' `z` (sorted, greedy), summed by octave, at a sixteenth of a bit and the three wider
    /// tolerances (`[tolerance][octave]`).
    pub cover: [[u64; OPEN_OCTAVES]; OPEN_GRAINS],
    /// [the theory thread, 19:10Z] The floor of the grouping a word tree shared by every receiver gives, at the same four tolerances: the
    /// head's definite words split by medians of their projections on the principal directions of its open rows' probes (then `|b|²`),
    /// and a crowd's members heard as one in a tree cell where their `z` spread stands within the tolerance, else in its two children.
    pub tree: [[u64; OPEN_OCTAVES]; OPEN_GRAINS],
}

/// The tolerances the lock cover and the word tree are read at, as shifts of the face's grain: `2^(−6)` to `2^2` bits, one an octave, so a
/// reading can take each head's, tick's and octave's own jitter as its grain (the theory thread, 19:20Z).
pub const OPEN_GRAINS: usize = 9;
pub const OPEN_GRAIN_LEAST: u32 = FACE_BITS - 6;

/// [measurement; the theory thread, November 15 19:10Z] **A word tree** over a head's definite sources: each cell's members split by the
/// median of their projections on one direction (the open rows' probes' principal directions in turn, then the words' power), down to one
/// member. A ruler: nothing in the law reads it.
struct WordTree {
    members: Vec<usize>,
    children: Option<Box<(WordTree, WordTree)>>,
}

impl WordTree {
    fn build(mut members: Vec<usize>, depth: usize, key: &dyn Fn(usize, usize) -> i128, directions: usize) -> Self {
        if members.len() <= 1 {
            return Self { members, children: None };
        }
        let dir = depth % directions;
        members.sort_by_key(|&x| key(x, dir));
        let half = members.len() / 2;
        let (lo, hi) = (members[..half].to_vec(), members[half..].to_vec());
        let left = Self::build(lo, depth + 1, key, directions);
        let right = Self::build(hi, depth + 1, key, directions);
        Self { members, children: Some(Box::new((left, right))) }
    }

    /// The terms a crowd's members (`inside`) leave in this cell at a tolerance: one where their `z` spread stands within it, else the
    /// children's.
    fn terms(&self, inside: &[bool], z: &[i128], width: i128) -> u64 {
        let (mut count, mut lo, mut hi) = (0u64, i128::MAX, i128::MIN);
        for &j in &self.members {
            if inside[j] {
                count += 1;
                lo = lo.min(z[j]);
                hi = hi.max(z[j]);
            }
        }
        if count <= 1 || hi - lo <= width {
            return count.min(1);
        }
        match &self.children {
            Some(c) => c.0.terms(inside, z, width) + c.1.terms(inside, z, width),
            None => count,
        }
    }
}

/// The principal directions of a set of integer vectors (`rows` of `dim` words), the largest first: the power iteration of `M = Σ a aᵀ`
/// on integer vectors held near `2^20` in their largest entry, each direction deflated of the ones before it, kept while its Rayleigh
/// quotient stands above `2^(−30)` of the first's. A ruler's directions: any basis near the principal one serves a tree's splits.
fn principal_directions(rows: &[&[i64]], dim: usize) -> Vec<Vec<i64>> {
    let mut m = vec![vec![0i128; dim]; dim];
    for a in rows {
        for x in 0..dim {
            for y in 0..dim {
                m[x][y] += a[x] as i128 * a[y] as i128;
            }
        }
    }
    let scale = |w: &mut Vec<i128>| {
        let top = w.iter().map(|v| v.unsigned_abs()).max().unwrap_or(0);
        if top == 0 {
            return;
        }
        let bits = 128 - top.leading_zeros();
        if bits > 21 {
            for v in w.iter_mut() {
                *v >>= bits - 21;
            }
        } else {
            for v in w.iter_mut() {
                *v <<= 21 - bits;
            }
        }
    };
    let mut dirs: Vec<Vec<i128>> = Vec::new();
    let mut quotients: Vec<i128> = Vec::new();
    for start in 0..dim {
        let mut v: Vec<i128> = (0..dim).map(|x| i128::from(x == start) << 20).collect();
        for _ in 0..40 {
            let mut w: Vec<i128> = (0..dim).map(|x| (0..dim).map(|y| (m[x][y] >> 20) * v[y]).sum::<i128>()).collect();
            for u in &dirs {
                let (uw, uu) = ((0..dim).map(|x| u[x] * w[x]).sum::<i128>(), (0..dim).map(|x| u[x] * u[x]).sum::<i128>());
                if uu > 0 {
                    for x in 0..dim {
                        w[x] -= uw / uu * u[x] + (uw % uu) * u[x] / uu;
                    }
                }
            }
            scale(&mut w);
            if w.iter().all(|&x| x == 0) {
                break;
            }
            v = w;
        }
        let vv: i128 = (0..dim).map(|x| v[x] * v[x]).sum();
        if vv == 0 {
            continue;
        }
        let mv: Vec<i128> = (0..dim).map(|x| (0..dim).map(|y| (m[x][y] >> 20) * v[y]).sum::<i128>()).collect();
        let q = (0..dim).map(|x| v[x] * mv[x]).sum::<i128>() / vv;
        if q <= 0 || quotients.first().is_some_and(|&first| q < first >> 30) {
            continue;
        }
        dirs.push(v);
        quotients.push(q);
    }
    let mut order: Vec<usize> = (0..dirs.len()).collect();
    order.sort_by_key(|&k| std::cmp::Reverse(quotients[k]));
    order.into_iter().map(|k| dirs[k].iter().map(|&x| x as i64).collect()).collect()
}

/// The wider tolerances an [`OpenCrowds`] reading reads beside its sixteenth of a bit, as shifts of the face's grain: a quarter of a bit,
/// one bit and four bits.
pub const OPEN_TOLERANCES: [u32; 3] = [FACE_BITS - 2, FACE_BITS, FACE_BITS + 2];

impl OpenCrowds {
    /// The sum of two readings of the same cell.
    pub fn add(&mut self, o: &Self) {
        self.rows += o.rows;
        for b in 0..OPEN_OCTAVES {
            self.pairs[b] += o.pairs[b];
            self.band_terms[b] += o.band_terms[b];
            self.lock_terms[b] += o.lock_terms[b];
            self.crowds[b] += o.crowds[b];
            self.band_whole[b] += o.band_whole[b];
            self.lock_whole[b] += o.lock_whole[b];
            for t in 0..3 {
                self.band_at[t][b] += o.band_at[t][b];
                self.lock_at[t][b] += o.lock_at[t][b];
            }
            for t in 0..OPEN_GRAINS {
                self.cover[t][b] += o.cover[t][b];
                self.tree[t][b] += o.tree[t][b];
            }
        }
    }
}

/// [measurement; agent-inferred, November 4, §16.42] **A receiver's near field by offset** ([`Constitution::near_offsets`]): at
/// each tick and head (`[tick · heads + head]`), the share on `2^(−63)` of the source `d` sites before the receiver
/// (`before[d − 1]`) and `d` sites after it (`after[d − 1]`), `0 < d < NEAR`, zero where that source is not met; and the
/// receiver's readout logits on `2^(−16)` bits where it is unresolved. Two shares of one row compare as their locks do:
/// `log₂(e_ij / e_ik) = z_ij − z_ik` bits.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct NearOffsets {
    pub before: Vec<[u64; NEAR - 1]>,
    pub after: Vec<[u64; NEAR - 1]>,
    pub logits: Option<Vec<i64>>,
}

/// [measurement; agent-inferred, November 2] **A held answer row's current by where it comes from** (§16.21,
/// [`Constitution::row_currents`]): one row (a tick, a head and an unresolved site), its framed current's part from the
/// question past the near field (`far`, the definite sites before the answer start at `|i − j| ≥ NEAR`) and its part
/// from the near field (`near`, every source at `|i − j| < NEAR`) and from every other source (`rest`: the answer's own
/// sites past the near field and any site after the answer start), each `Σ release(p D ṽ_j, 63)` entry by entry on the
/// value's grain over the head's `2n` reals, so `far + near + rest` is the row's current; the row's largest share on `2^(−63)`; and, where read with its return,
/// the code's covector of the row's framed current `δỹ` (the reverse's, on the covector's grain). Region-level groups
/// only: no source is paired with a receiver by its class.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RowCurrent {
    pub tick: u32,
    pub head: u32,
    pub site: u32,
    pub far: Vec<i128>,
    pub near: Vec<i128>,
    pub rest: Vec<i128>,
    pub top: u64,
    pub covector: Vec<i64>,
}

/// [measurement; theory, November 13, the junction record §13.9; G157] **A turned head's reach on its own clock, its founding covector by
/// receiver row**: over one tick's receiver rows of one head and kind, each row's `r_w = −Σ_j ζ_ij log₂(max(Δσ_ij, 1)/d_ij)` and
/// `r_u = −Σ_j ζ_ij frac(log₂ d_ij)` ([`reach_logs`], the logs on `2^(−16)`, `ζ` the reverse's score covector at a met source, a crowd taking the
/// clock's term at the place its skin reads and no remainder): their sums, their sums in magnitude and their squares after a release of 32 bits
/// (a random-sign level's input), with the rows counted. Its grain is the reverse's; no unit of `w` or `u` is read.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ReachSums {
    pub rows: u64,
    pub w: i128,
    pub w_abs: u128,
    pub w_sq: u128,
    pub u: i128,
    pub u_abs: u128,
    pub u_sq: u128,
}

/// [measurement; theory, November 13, the junction record §13.8; G158] **The reader's reaction at its founding, by written source**: over one
/// tick's written sources of one head and kind of reader, `a_j = ⟨λ_j^(k+1), ρ_j⟩` ([`Constitution::reaction_covectors`]): their sum, sum in magnitude
/// and squares after a release of 32 bits (a random-sign level's input), with the sources counted, and `Σ|ρ_j|²` and `Σ|x_j|²` each entry
/// released 8 bits before its square (`m² = Σ|ρ|²/Σ|x|²`, the unit `κ` is read in, on the reverse's grain).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ReactionSums {
    pub rows: u64,
    pub a: i128,
    pub a_abs: u128,
    pub a_sq: u128,
    pub rho_sq: u128,
    pub x_sq: u128,
}

/// [measurement; G159] **The reaction's forms at one tick and head** ([`Constitution::reaction_forms`]): the written sources and the readers counted;
/// the route's `Σ_j a_j` and the pair decomposition's, with the sources where the two agree in sign; the source's chart's covector by coordinate
/// (`Σ_j a_j r̂_j`, `Σ_j |a_j r̂_j|`) and the reader's (`Σ_i b_i r̂_i`, `Σ_i |b_i r̂_i|`); and the strength raised by the source's metric,
/// summed, in magnitude and squared after a release of 8 bits.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ReactionForms {
    pub sources: u64,
    pub readers: u64,
    pub route: i128,
    pub pair: i128,
    pub agree: u64,
    pub src: Vec<(i128, u128)>,
    pub rdr: Vec<(i128, u128)>,
    pub w: i128,
    pub w_abs: u128,
    pub w_sq: u128,
}

/// [measurement; G160] **The read's mirror at one tick, head and kind of reader** ([`Constitution::mirror_covectors`]): the written sources heard,
/// the sum of `a_j = ⟨λ_j, μ_j⟩`, in magnitude and squared after a release of 32 bits; and with readers of both kinds the source's chart's
/// covector by coordinate, the audience summed on `2^(−31)`, and the lanes' powers as `log₂` on `2^(−16)` summed and squared, with the lanes
/// counted.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MirrorSums {
    pub sources: u64,
    pub a: i128,
    pub a_abs: u128,
    pub a_sq: u128,
    pub chart: Vec<(i128, u128)>,
    pub audience: u128,
    pub power_log: i128,
    pub power_log_sq: u128,
    pub lanes: u64,
}

/// [measurement; G162] **One stage of the free ring** ([`Constitution::free_ring`]): the open places, their code and the faces' expected code on
/// `2^(−20)` bits summed, and the charts' change from the stage before (`Σ |Δr̂|²`, unsigned) and its pairing with the change before that.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RingStage {
    pub places: u64,
    pub code: i128,
    pub expected: i128,
    pub norm: u128,
    pub inner: i128,
}

/// The octaves a [`TickNews`] histogram holds.
pub const TICK_OCTAVES: usize = 160;

/// [measurement; theory, November 15 20:38Z, the return on the clock of news] **What each site's tick moves, and what reaches it**, one tick:
/// for each site (`[0]` written, `[1]` open), with `Δx = x^(k+1) − x^k` the tick's own update and `λ^(k+1)` the covector its reverse
/// receives, `a = ⟨λ^(k+1), Δx⟩` on `2^(−40)` bits (the code's first-order move were the site's tick held, the mirror's grain), counted by
/// its octave (`0` where `a = 0`, else `⌊log₂|a|⌋ + 1`) with `Σ |a|`; the update against the state it moved, by the octave of
/// `‖Δx‖² / ‖x^k‖²` (`80 + bits(‖Δx‖²) − bits(‖x^k‖²)`); and the covector's power, by the octave of `‖λ^(k+1)‖²`. A reading only.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TickNews {
    pub sites: [u64; 2],
    pub cost: [[u64; TICK_OCTAVES]; 2],
    pub cost_abs: [u128; 2],
    /// `Σ |a|` by the octave of `|a|`.
    pub cost_mass: [[u128; TICK_OCTAVES]; 2],
    pub update: [[u64; TICK_OCTAVES]; 2],
    pub covector: [[u64; TICK_OCTAVES]; 2],
}

impl Default for TickNews {
    fn default() -> Self {
        Self { sites: [0; 2], cost: [[0; TICK_OCTAVES]; 2], cost_abs: [0; 2], cost_mass: [[0; TICK_OCTAVES]; 2], update: [[0; TICK_OCTAVES]; 2], covector: [[0; TICK_OCTAVES]; 2] }
    }
}

impl TickNews {
    pub fn add(&mut self, o: &TickNews) {
        for kind in 0..2 {
            self.sites[kind] += o.sites[kind];
            self.cost_abs[kind] += o.cost_abs[kind];
            for b in 0..TICK_OCTAVES {
                self.cost[kind][b] += o.cost[kind][b];
                self.cost_mass[kind][b] += o.cost_mass[kind][b];
                self.update[kind][b] += o.update[kind][b];
                self.covector[kind][b] += o.covector[kind][b];
            }
        }
    }
}

/// [measurement; theory, November 15 21:16Z] **What holding the quiet written site-ticks costs** ([`Constitution::held_forward`]), one region:
/// the compared places and written sites; the compared places' code on `2^(−20)` bits, whole and held (by `a`, the oracle, and by the
/// chart's move at the oracle's count), a section each; and by section and tick the sites held, `Σ a` and `Σ |a|` held (`2^(−40)` bits),
/// `Σ |a|` the chart's criterion holds, with `Σ a` and `Σ |a|` over every written site a tick.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HeldRead {
    pub compared: u64,
    pub written: u64,
    pub code_full: i128,
    pub code_oracle: Vec<i128>,
    pub code_chart: Vec<i128>,
    pub held: Vec<Vec<u64>>,
    pub a_held: Vec<Vec<i128>>,
    pub abs_held: Vec<Vec<u128>>,
    pub abs_chart: Vec<Vec<u128>>,
    pub a_all: Vec<i128>,
    pub abs_all: Vec<u128>,
}

impl HeldRead {
    pub fn add(&mut self, o: &HeldRead) {
        self.compared += o.compared;
        self.written += o.written;
        self.code_full += o.code_full;
        let grow = |v: &mut Vec<i128>, w: &[i128]| {
            v.resize(v.len().max(w.len()), 0);
            v.iter_mut().zip(w).for_each(|(x, y)| *x += y);
        };
        let grow_u = |v: &mut Vec<u128>, w: &[u128]| {
            v.resize(v.len().max(w.len()), 0);
            v.iter_mut().zip(w).for_each(|(x, y)| *x += y);
        };
        grow(&mut self.code_oracle, &o.code_oracle);
        grow(&mut self.code_chart, &o.code_chart);
        grow(&mut self.a_all, &o.a_all);
        grow_u(&mut self.abs_all, &o.abs_all);
        for (mine, theirs) in [(&mut self.a_held, &o.a_held)] {
            mine.resize(mine.len().max(theirs.len()), Vec::new());
            mine.iter_mut().zip(theirs).for_each(|(m, t)| grow(m, t));
        }
        for (mine, theirs) in [(&mut self.abs_held, &o.abs_held), (&mut self.abs_chart, &o.abs_chart)] {
            mine.resize(mine.len().max(theirs.len()), Vec::new());
            mine.iter_mut().zip(theirs).for_each(|(m, t)| grow_u(m, t));
        }
        self.held.resize(self.held.len().max(o.held.len()), Vec::new());
        for (m, t) in self.held.iter_mut().zip(&o.held) {
            m.resize(m.len().max(t.len()), 0);
            m.iter_mut().zip(t).for_each(|(x, y)| *x += y);
        }
    }
}

fn octave_of(v: u128) -> usize {
    ((128 - v.leading_zeros()) as usize).min(TICK_OCTAVES - 1)
}

/// `log₂ n` on `2^(−16)` for `n ≥ 1` ([`log2_face`] of `n/2^(⌊log₂ n⌋ + 1)` and the whole part).
pub(crate) fn log2_grain(n: u128) -> i64 {
    let whole = 127 - i64::from(n.max(1).leading_zeros());
    let p = n.max(1) << (61 - whole);
    (log2_face(p, FACE_BITS) + (i128::from(whole + 1) << FACE_BITS)) as i64
}

/// [measurement; G157] The reach's two logs between receiver `i` and source `j` on the face's grain: `log₂(max(Δσ, one plain tick)/d)` with
/// `Δσ = |σ_i − σ_j|` on `2^(−24)` and `d = |i − j|` places, and the octave's remainder `frac(log₂ d)`.
pub(crate) fn reach_logs(sigma: &[i64], i: usize, j: usize) -> (i64, i64) {
    let d = i.abs_diff(j).max(1) as u128;
    let ld = log2_grain(d);
    let ds = (sigma[i] - sigma[j]).unsigned_abs().max(1 << PACE_BITS) as u128;
    let ls = log2_grain(ds) - ((PACE_BITS as i64) << FACE_BITS);
    (ls - ld, ld - ((ld >> FACE_BITS) << FACE_BITS))
}

/// The round trips `Σ_j p_ji^(t) p_ij^(t+1)` of each site over consecutive ticks' rows (`[h][i]`), each
/// product released to `2^(−63)`, added into `trips`.
pub(crate) fn round_trips(before: &[Vec<Source>], after: &[Vec<Source>], sites: usize, trips: &mut [u128]) {
    for (hi, row) in after.iter().enumerate() {
        let (h, i) = (hi / sites, hi % sites);
        for src in row {
            let Some(back) = before[h * sites + src.j as usize].iter().find(|b| b.j as usize == i) else { continue };
            trips[i] += (src.p as u128 * back.p as u128 + (1u128 << (SHARE_BITS - 1))) >> SHARE_BITS;
        }
    }
}

impl Constitution {

    /// [measurement] **A region's rows read by where their mass lies** (§15.9's reading): over every
    /// tick, head and receiver, open receivers (`[0]`) and definite ones (`[1]`) apart: the rows, the far
    /// sources they meet, and the mass of their shares (on `2^(−63)`) on the near field, on far sources
    /// and on crowds.
    pub fn row_shares(&self, region: &Region) -> Result<RowShares> {
        let pass = self.pass(region, true)?;
        let sites = region.classes.len();
        let mut out = RowShares::default();
        for cell in &pass.ticks {
            for (hi, row) in cell.rows.iter().enumerate() {
                let i = hi % sites;
                let k = usize::from(Self::definite(region, i));
                out.rows[k] += 1;
                for src in row {
                    if (src.j as usize).abs_diff(i) < NEAR {
                        out.near[k] += src.p as u128;
                    } else {
                        out.far[k] += src.p as u128;
                        out.far_sources[k] += 1;
                    }
                }
                out.crowd[k] += cell.crowds[hi].iter().map(|c| c.e as u128).sum::<u128>();
                out.peak[k] += row.iter().map(|src| src.p).chain(cell.crowds[hi].iter().map(|c| c.e)).max().unwrap_or(0) as u128;
            }
        }
        Ok(out)
    }

    /// [measurement; theory, November 13, the junction record §9 item 1] **Each site's echo by head** (`[h][i]` on `2^(−63)`): head `h`'s
    /// `B_i^h`, the mean over consecutive ticks of `Σ_j p_ji^(t) p_ij^(t+1)` ([`round_trips`]), the share of a site's arrival that is its own
    /// state of two ticks before, returned by the sites it told. [`ReadLogits::echo`] is its mean over heads. An unresolved site is no source,
    /// so its row reads zero. A reading only: nothing in the law reads it.
    pub fn echo_by_head(&self, region: &Region) -> Result<Vec<Vec<u64>>> {
        let pass = self.pass(region, true)?;
        let (sites, heads) = (region.classes.len(), self.declaration.heads);
        let mut trips = vec![vec![0u128; sites]; heads];
        for w in pass.ticks.windows(2) {
            for (h, t) in trips.iter_mut().enumerate() {
                round_trips(&w[0].rows[h * sites..(h + 1) * sites], &w[1].rows[h * sites..(h + 1) * sites], sites, t);
            }
        }
        let read = (pass.ticks.len().saturating_sub(1)).max(1) as u128;
        Ok(trips.iter().map(|t| t.iter().map(|&b| ((b + read / 2) / read) as u64).collect()).collect())
    }

    /// [measurement; theory, November 13, the theory thread's order after G151, item (c)] **Each site's round trips across heads** (`[h][h′][i]` on
    /// `2^(−63)`): the mean over consecutive ticks of `Σ_j p_ji^(t, h′) p_ij^(t+1, h)`, what site `i` told `j` in head `h′` coming back to it in head
    /// `h` a tick later; the diagonal is [`Constitution::echo_by_head`]. The strand's pair contacts, triads and carry circles are outside it (they are two-way
    /// by build). A reading only: nothing in the law reads it.
    pub fn echo_across_heads(&self, region: &Region) -> Result<Vec<Vec<Vec<u64>>>> {
        let pass = self.pass(region, true)?;
        let (sites, heads) = (region.classes.len(), self.declaration.heads);
        let mut trips = vec![vec![vec![0u128; sites]; heads]; heads];
        for w in pass.ticks.windows(2) {
            for (h, by_h) in trips.iter_mut().enumerate() {
                for (h2, t) in by_h.iter_mut().enumerate() {
                    round_trips(&w[0].rows[h2 * sites..(h2 + 1) * sites], &w[1].rows[h * sites..(h + 1) * sites], sites, t);
                }
            }
        }
        let read = (pass.ticks.len().saturating_sub(1)).max(1) as u128;
        Ok(trips.iter().map(|by_h| by_h.iter().map(|t| t.iter().map(|&b| ((b + read / 2) / read) as u64).collect()).collect()).collect())
    }

    /// [measurement; November 15, T6 of #841] **An open row's shares by where they lie** ([`OpenRows`]), each tick and head of the region's
    /// forward. A reading only.
    pub fn open_rows(&self, region: &Region) -> Result<Vec<OpenRows>> {
        let pass = self.pass(region, true)?;
        let (sites, d) = (region.classes.len(), &self.declaration);
        let heads = d.heads;
        let mut out = vec![OpenRows::default(); d.ticks * heads];
        for (tick, cell) in pass.ticks.iter().enumerate() {
            for h in 0..heads {
                let acc = &mut out[tick * heads + h];
                let lists = &cell.classes[h];
                for i in (0..sites).filter(|&i| !Self::definite(region, i)) {
                    acc.rows += 1;
                    let hi = h * sites + i;
                    let (mut m, mut sq, mut pk) = ([[0u128; 2]; OPEN_OCTAVES], [[0u128; 2]; OPEN_OCTAVES], [[0u128; 2]; OPEN_OCTAVES]);
                    for src in &cell.rows[hi] {
                        let j = src.j as usize;
                        let gap = i.abs_diff(j);
                        let p = src.p as u128;
                        if gap < NEAR {
                            acc.near += p;
                            continue;
                        }
                        let o = ((usize::BITS - 1 - gap.leading_zeros()) as usize).min(OPEN_OCTAVES - 1);
                        let c = lists.class[j];
                        let k = usize::from(c == lists.probe_class[i] || lists.probes[i].contains(&c));
                        m[o][k] += p;
                        sq[o][k] += (p * p) >> SHARE_BITS;
                        pk[o][k] = pk[o][k].max(p);
                    }
                    acc.crowd += cell.crowds[hi].iter().map(|c| c.e as u128).sum::<u128>();
                    for o in 0..OPEN_OCTAVES {
                        for k in 0..2 {
                            if m[o][k] == 0 {
                                continue;
                            }
                            acc.far[o][k] += m[o][k];
                            acc.counted[o][k] += 1;
                            if sq[o][k] > 0 {
                                acc.effective[o][k] += ((m[o][k] * m[o][k]) >> (SHARE_BITS - 8)) / sq[o][k];
                            }
                            acc.peak[o][k] += (pk[o][k] << 16) / m[o][k];
                        }
                    }
                }
            }
        }
        Ok(out)
    }

    /// [measurement; November 15, T7 of #841] **An open row's far pairs heard as crowds where a band admits them** ([`OpenCrowds`]), each tick
    /// and head of the region's forward. A reading only.
    pub fn open_crowds(&self, region: &Region) -> Result<Vec<OpenCrowds>> {
        let pass = self.pass(region, true)?;
        let (sites, d) = (region.classes.len(), &self.declaration);
        let (heads, n) = (d.heads, d.modes);
        let span = 2 * n;
        let epsilon = 1i128 << (FACE_BITS - 4);
        let mut out = vec![OpenCrowds::default(); d.ticks * heads];
        for (tick, cell) in pass.ticks.iter().enumerate() {
            let paces = pass.paces_at(cell);
            for h in 0..heads {
                let acc = &mut out[tick * heads + h];
                // The head's word tree this tick, shared by its open rows: the definite sources split along the open rows' probes'
                // principal directions, then by their words' power.
                let tree = {
                    let probes: Vec<&[i64]> = (0..sites).filter(|&i| !Self::definite(region, i)).map(|i| &cell.pq[(h * sites + i) * span..(h * sites + i + 1) * span]).collect();
                    let dirs = if probes.is_empty() { Vec::new() } else { principal_directions(&probes, span) };
                    let word = |j: usize| &cell.q[(h * sites + j) * span..(h * sites + j + 1) * span];
                    let nd = dirs.len() + 1;
                    let key = |j: usize, dir: usize| -> i128 {
                        let w = word(j);
                        if dir < dirs.len() { (0..span).map(|x| dirs[dir][x] as i128 * w[x] as i128).sum() } else { w.iter().map(|&x| x as i128 * x as i128).sum() }
                    };
                    let definite: Vec<usize> = (0..sites).filter(|&j| Self::definite(region, j)).collect();
                    WordTree::build(definite, 0, &key, nd)
                };
                for i in (0..sites).filter(|&i| !Self::definite(region, i)) {
                    acc.rows += 1;
                    let temper = self.temper(h, true)?;
                    let a = &cell.pq[(h * sites + i) * span..(h * sites + i + 1) * span];
                    // Each met source's base (the lock at unit gain), read once a row.
                    let mut base_of = vec![0i128; sites];
                    for src in &cell.rows[h * sites + i] {
                        base_of[src.j as usize] = src.s as i128;
                    }
                    // A crowd's members tested whole: the band over their words and skins, and their own locks' spread, each on the face's
                    // grain at the head's temper (`T · width ≤ ε`).
                    let widths = |members: &[usize]| -> Result<(i128, i128)> {
                        let mut band = 0i128;
                        let (mut lo_base, mut hi_base) = (i128::MAX, i128::MIN);
                        let mut grain = 0u32;
                        for l in 0..n {
                            let (mut dlo, mut dhi) = (i128::MAX, i128::MIN);
                            let (mut wlo, mut whi) = ([i128::MAX; 2], [i128::MIN; 2]);
                            for &j in members {
                                let (dj, g) = self.pair_decay(paces, h, l, i, j);
                                grain = g;
                                dlo = dlo.min(dj);
                                dhi = dhi.max(dj);
                                let q = &cell.q[(h * sites + j) * span..(h * sites + j + 1) * span];
                                for (r, x) in [q[l] as i128, q[n + l] as i128].into_iter().enumerate() {
                                    wlo[r] = wlo[r].min(x);
                                    whi[r] = whi[r].max(x);
                                }
                            }
                            for (r, ar) in [a[l] as i128, a[n + l] as i128].into_iter().enumerate() {
                                let ends = [dlo * wlo[r], dlo * whi[r], dhi * wlo[r], dhi * whi[r]];
                                let (clo, chi) = (*ends.iter().min().expect("four ends"), *ends.iter().max().expect("four ends"));
                                let q = |c: i128| (ar << (grain + 1)) * c - c * c;
                                let top = q((ar << grain).clamp(clo, chi));
                                let bottom = q(clo).min(q(chi));
                                band += top - bottom;
                            }
                        }
                        for &j in members {
                            lo_base = lo_base.min(base_of[j]);
                            hi_base = hi_base.max(base_of[j]);
                        }
                        let band_base = band >> (FACE_BITS + 2 * grain + 1);
                        Ok((release(temper * band_base, MATERIAL_BITS), release(temper * (hi_base - lo_base), MATERIAL_BITS)))
                    };
                    let test_at = |members: &[usize], eps: i128| -> Result<(bool, bool)> {
                        let (b, l) = widths(members)?;
                        Ok((b <= eps, l <= eps))
                    };
                    let test = |members: &[usize]| test_at(members, epsilon);
                    // The terms a crowd leaves under a test: one where it admits, else its two halves', down to members.
                    fn terms(members: &[usize], which: usize, test: &dyn Fn(&[usize]) -> Result<(bool, bool)>) -> Result<u64> {
                        if members.len() <= 1 {
                            return Ok(members.len() as u64);
                        }
                        let ok = test(members)?;
                        if if which == 0 { ok.0 } else { ok.1 } {
                            return Ok(1);
                        }
                        let half = members.len() / 2;
                        Ok(terms(&members[..half], which, test)? + terms(&members[half..], which, test)?)
                    }
                    for (lo, hi_, level) in crate::contact::crowd_ranges(i, sites) {
                        let members: Vec<usize> = (lo..=hi_).filter(|&j| Self::definite(region, j)).collect();
                        if members.is_empty() {
                            continue;
                        }
                        let o = (level as usize).min(OPEN_OCTAVES - 1);
                        acc.pairs[o] += members.len() as u64;
                        acc.crowds[o] += 1;
                        let whole = test(&members)?;
                        acc.band_whole[o] += u64::from(whole.0 || members.len() == 1);
                        acc.lock_whole[o] += u64::from(whole.1 || members.len() == 1);
                        acc.band_terms[o] += terms(&members, 0, &test)?;
                        acc.lock_terms[o] += terms(&members, 1, &test)?;
                        let mut inside = vec![false; sites];
                        let mut zfull = vec![0i128; sites];
                        for &j in &members {
                            inside[j] = true;
                            zfull[j] = release(temper * base_of[j], MATERIAL_BITS);
                        }
                        for t in 0..OPEN_GRAINS {
                            acc.tree[t][o] += tree.terms(&inside, &zfull, 1i128 << (OPEN_GRAIN_LEAST + t as u32));
                        }
                        let mut zs: Vec<i128> = members.iter().map(|&j| release(temper * base_of[j], MATERIAL_BITS)).collect();
                        zs.sort_unstable();
                        for t in 0..OPEN_GRAINS {
                            let width = 1i128 << (OPEN_GRAIN_LEAST + t as u32);
                            let (mut count, mut start) = (0u64, i128::MIN);
                            for &z in &zs {
                                if start == i128::MIN || z > start + width {
                                    count += 1;
                                    start = z;
                                }
                            }
                            acc.cover[t][o] += count;
                        }
                        for (t, &shift) in OPEN_TOLERANCES.iter().enumerate() {
                            let wide_test = |m: &[usize]| test_at(m, 1i128 << shift);
                            acc.band_at[t][o] += terms(&members, 0, &wide_test)?;
                            acc.lock_at[t][o] += terms(&members, 1, &wide_test)?;
                        }
                    }
                }
            }
        }
        Ok(out)
    }

    /// [measurement; November 15, the theory thread's ε from the field's own temperature] **How far a far pair's face moves between two
    /// constitutions** (a lap's end and its mean): at each tick and head (`[tick · heads + head]`), over the region's open rows and their far
    /// sources (`|i − j| ≥ NEAR`), `|z_j(self) − z_j(other)|` with `z = release(T base, 24)` each at its own constitution's temper, on the
    /// face's grain, counted in octaves of its size (`[octave of distance][⌊log₂(1 + |Δz|)⌋]`, 40 bins). A reading only.
    pub fn far_jitter(&self, other: &Constitution, region: &Region) -> Result<Vec<[[u64; 40]; OPEN_OCTAVES]>> {
        let (pa, pb) = (self.pass(region, true)?, other.pass(region, true)?);
        let (sites, d) = (region.classes.len(), &self.declaration);
        let heads = d.heads;
        let mut out = vec![[[0u64; 40]; OPEN_OCTAVES]; d.ticks * heads];
        for (tick, (ca, cb)) in pa.ticks.iter().zip(&pb.ticks).enumerate() {
            for h in 0..heads {
                let (ta, tb) = (self.temper(h, true)?, other.temper(h, true)?);
                let hist = &mut out[tick * heads + h];
                for i in (0..sites).filter(|&i| !Self::definite(region, i)) {
                    let hi = h * sites + i;
                    let mut zb = vec![None; sites];
                    for src in &cb.rows[hi] {
                        zb[src.j as usize] = Some(release(tb * src.s as i128, MATERIAL_BITS));
                    }
                    for src in &ca.rows[hi] {
                        let j = src.j as usize;
                        let gap = i.abs_diff(j);
                        if gap < NEAR {
                            continue;
                        }
                        let Some(z_other) = zb[j] else { continue };
                        let dz = (release(ta * src.s as i128, MATERIAL_BITS) - z_other).unsigned_abs();
                        let o = ((usize::BITS - 1 - gap.leading_zeros()) as usize).min(OPEN_OCTAVES - 1);
                        let bin = (u128::BITS - (dz + 1).leading_zeros() - 1).min(39) as usize;
                        hist[o][bin] += 1;
                    }
                }
            }
        }
        Ok(out)
    }

    /// [measurement; agent-inferred, November 2] **A held read's rows by where their mass lies** ([`HeldRows`]):
    /// for each tick and head (`[tick · heads + head]`), over the region's unresolved sites, the shares of
    /// the question group (definite sites before `question`), of the soft near field and of the rest, and the
    /// current's part from the question group. A reading only: nothing in the law reads it.
    pub fn held_rows(&self, region: &Region, question: usize) -> Result<Vec<HeldRows>> {
        let pass = self.pass(region, true)?;
        let (sites, d) = (region.classes.len(), &self.declaration);
        let (heads, n, span) = (d.heads, d.modes, 2 * d.modes);
        let mut out = vec![HeldRows::default(); d.ticks * heads];
        for (tick, cell) in pass.ticks.iter().enumerate() {
            for h in 0..heads {
                let acc = &mut out[tick * heads + h];
                for i in (0..sites).filter(|&i| region.unresolved[i]) {
                    acc.rows += 1;
                    let hi = h * sites + i;
                    let (mut far, mut collision) = (0u128, 0u128);
                    for src in &cell.rows[hi] {
                        let j = src.j as usize;
                        let definite = Self::definite(region, j);
                        if definite && j < question {
                            acc.question += src.p as u128;
                            if i.abs_diff(j) >= NEAR {
                                far += src.p as u128;
                                collision += release(src.p as i128 * src.p as i128, SHARE_BITS) as u128;
                            }
                            let vj = &cell.v[(h * sites + j) * span..(h * sites + j + 1) * span];
                            let current: i128 = (0..span).map(|x| decayed(self.pair_decay(pass.paces_at(cell), h, x % n, i, j), vj[x]).abs()).sum();
                            acc.question_current += release(src.p as i128 * current, SHARE_BITS);
                        } else if i.abs_diff(j) < NEAR && !definite {
                            acc.soft_near += src.p as u128;
                        } else if i.abs_diff(j) < NEAR {
                            acc.near_definite += src.p as u128;
                        } else {
                            acc.other += src.p as u128;
                        }
                    }
                    acc.other += cell.crowds[hi].iter().map(|c| c.e as u128).sum::<u128>();
                    acc.question_far += far;
                    if collision > 0 {
                        acc.far_effective += ((far * far) >> (SHARE_BITS - 8)) / collision;
                        acc.far_rows += 1;
                    }
                }
            }
        }
        Ok(out)
    }

    /// [measurement; agent-inferred, November 2] **The contact covector by where its pairs lie** (§16.20): over
    /// `regions` read and returned, for each head `[near, far]`, `Σ |δs_ij|` over the near pairs (`|i − j| < NEAR`)
    /// and over the far pairs and the crowds, on the contact covector's grain. The far share, `far / (near + far)`, is
    /// the part of the probes' and keys' learning a far contact receives. A reading only.
    pub fn covector_shares(&self, regions: &[Region]) -> Result<Vec<[u128; 2]>> {
        let heads = self.declaration.heads;
        let mut out = vec![0u128; 2 * heads];
        for region in regions {
            let pass = self.pass(region, true)?;
            let mut g = vec![0i128; self.material_len()];
            self.returned_with(region, &pass, &mut g, Some(&mut out), None, None, None, None, None)?;
        }
        Ok(out.chunks_exact(2).map(|c| [c[0], c[1]]).collect())
    }

    /// [measurement; agent-inferred, November 2] **The held answer rows' currents by where they come from**
    /// ([`RowCurrent`], §16.21): for each tick, head and unresolved site of `region` in that order, the framed current's
    /// part from the question past the near field (definite sites before `question`) and from the near field, the
    /// row's largest share and, with `returning`, the code's covector of the row's framed current. A reading only.
    pub fn row_currents(&self, region: &Region, question: usize, returning: bool) -> Result<Vec<RowCurrent>> {
        let pass = self.pass(region, true)?;
        let (sites, d) = (region.classes.len(), &self.declaration);
        let (heads, n, span) = (d.heads, d.modes, 2 * d.modes);
        let mut covectors: Vec<Vec<i64>> = Vec::new();
        if returning {
            let mut g = vec![0i128; self.material_len()];
            self.returned_with(region, &pass, &mut g, None, Some(&mut covectors), None, None, None, None)?;
            covectors.reverse();
        }
        let mut out = Vec::new();
        for (tick, cell) in pass.ticks.iter().enumerate() {
            for h in 0..heads {
                for i in (0..sites).filter(|&i| region.unresolved[i]) {
                    let (mut far, mut near, mut rest) = (vec![0i128; span], vec![0i128; span], vec![0i128; span]);
                    let mut top = 0u64;
                    for src in &cell.rows[h * sites + i] {
                        let j = src.j as usize;
                        top = top.max(src.p);
                        let gap = i.abs_diff(j);
                        let into = if gap < NEAR { &mut near } else if Self::definite(region, j) && j < question { &mut far } else { &mut rest };
                        let vj = &cell.v[(h * sites + j) * span..(h * sites + j + 1) * span];
                        for (x, slot) in into.iter_mut().enumerate() {
                            *slot += release(src.p as i128 * decayed(self.pair_decay(pass.paces_at(cell), h, x % n, i, j), vj[x]), SHARE_BITS);
                        }
                    }
                    let covector = covectors.get(tick).map(|c| c[(h * sites + i) * span..(h * sites + i + 1) * span].to_vec()).unwrap_or_default();
                    out.push(RowCurrent { tick: tick as u32, head: h as u32, site: i as u32, far, near, rest, top, covector });
                }
            }
        }
        Ok(out)
    }

    /// [`Constitution::held_rows`] summed over `regions` (each with its own answer start `questions[r]`).
    pub fn held_rows_all(&self, regions: &[Region], questions: &[usize]) -> Result<Vec<HeldRows>> {
        if regions.len() != questions.len() {
            return refuse("a held read's answer starts that are not one a region");
        }
        let mut out = vec![HeldRows::default(); self.declaration.ticks * self.declaration.heads];
        for (region, &question) in regions.iter().zip(questions) {
            for (acc, one) in out.iter_mut().zip(self.held_rows(region, question)?) {
                acc.rows += one.rows;
                acc.question += one.question;
                acc.soft_near += one.soft_near;
                acc.other += one.other;
                acc.question_current += one.question_current;
                acc.question_far += one.question_far;
                acc.far_effective += one.far_effective;
                acc.far_rows += one.far_rows;
                acc.near_definite += one.near_definite;
            }
        }
        Ok(out)
    }

    /// The site pairs the region's contact meets over its ticks and heads (`Σ |S_i^h|`).
    pub fn met_pairs(&self, region: &Region) -> Result<u64> {
        Ok(self.pass(region, false)?.pairs)
    }

    /// [measurement; theory, November 13, the junction record §13.8; G158] **The reader's reaction's route**: for tick `k` and head `h`, each
    /// source's `ρ_j = J_r̂(x_j^k)ᵀ V_hᵀ conj(U_j) Σ_(i: j ∈ S_i^h) p_ij D_ij U_i (O_hᵀ x_i^(k+1))`, the reverse's value route alone (the frame,
    /// each met source's share and skin, a crowd's share spread over its definite sources at the octave's decay, the unframing, `V`'s transpose and
    /// the chart's lane adjoint, every release the reverse's), fed each reader's state after the tick where the reverse feeds its covector; with
    /// `readers` only the readers of that kind (`false` open, `true` written). `[t][D]`. It repeats `Constitution::tick_return`'s value route, which a
    /// change there must carry here.
    pub(crate) fn reaction_route(&self, cell: &TickCell, paces: &Paces, definite: &[bool], h: usize, readers: bool) -> Result<Vec<i64>> {
        let d = &self.declaration;
        let (dw, m, n, lanes) = (d.width, d.complex(), d.modes, d.lanes);
        let (m2, span) = (2 * m, 2 * n);
        let sites = definite.len();
        let (l, reaches) = (&self.layout, self.reaches());
        // `O_hᵀ x^(k+1)`, the head's block of the current's transpose at each reader of the kind, framed: `U_i δy_i`.
        let mut dyh = vec![0i64; sites * span];
        let mut dy = vec![0i64; m2];
        for t in (0..sites).filter(|&t| definite[t] == readers) {
            transposed(&self.theta[l.out..l.out + dw * m2], reaches.out, m2, &cell.after[t * dw..(t + 1) * dw], MATERIAL_BITS, &mut dy)?;
            for li in 0..n {
                let c = h * n + li;
                let (ur, ui) = self.frame(paces, t, h, li);
                let (ur, ui) = (ur as i128, ui as i128);
                let (gr, gi) = (dy[c] as i128, dy[m + c] as i128);
                dyh[t * span + li] = fit64(release(ur * gr - ui * gi, MOVE_BITS))?;
                dyh[t * span + n + li] = fit64(release(ui * gr + ur * gi, MOVE_BITS))?;
            }
        }
        let rows = &cell.rows[h * sites..(h + 1) * sites];
        let crowds = &cell.crowds[h * sites..(h + 1) * sites];
        let mut sv = vec![0i128; sites * span];
        let mut crowd_v = vec![0i128; (sites + 1) * span];
        for i in 0..sites {
            for src in &rows[i] {
                let j = src.j as usize;
                for r in 0..span {
                    sv[j * span + r] += src.p as i128 * decayed(self.pair_decay(paces, h, r % n, i, j), dyh[i * span + r]);
                }
            }
            for c in &crowds[i] {
                for r in 0..span {
                    let part = div_nearest(c.e as i128 * decayed(self.octave_decay(paces, h, r % n, i, c.level, c.lo > i), dyh[i * span + r]), c.count as i128);
                    crowd_v[c.lo * span + r] += part;
                    crowd_v[(c.hi + 1) * span + r] -= part;
                }
            }
        }
        let mut spread = crowd_v[..sites * span].to_vec();
        for t in 1..sites {
            for r in 0..span {
                spread[t * span + r] += spread[(t - 1) * span + r];
            }
        }
        let mut dv = vec![0i64; sites * m2];
        for j in 0..sites {
            for r in 0..span {
                let c = h * n + r % n;
                let slot = j * m2 + if r < n { c } else { m + c };
                dv[slot] = fit64(release(sv[j * span + r], SHARE_BITS))?;
                if definite[j] {
                    dv[slot] = fit64(dv[slot] as i128 + release(spread[j * span + r], SHARE_BITS))?;
                }
            }
        }
        for t in 0..sites {
            for li in 0..n {
                let c = h * n + li;
                let (ur, ui) = self.frame(paces, t, h, li);
                let (ur, ui) = (ur as i128, ui as i128);
                let (gr, gi) = (dv[t * m2 + c] as i128, dv[t * m2 + m + c] as i128);
                dv[t * m2 + c] = fit64(release(ur * gr + ui * gi, MOVE_BITS))?;
                dv[t * m2 + m + c] = fit64(release(ur * gi - ui * gr, MOVE_BITS))?;
            }
        }
        let mut out = vec![0i64; sites * dw];
        let mut back = vec![0i64; dw];
        for t in 0..sites {
            transposed(&self.theta[l.v..l.v + m2 * dw], reaches.v, dw, &dv[t * m2..(t + 1) * m2], MATERIAL_BITS, &mut back)?;
            let rho = lane_adjoint(&cell.read[t * dw..(t + 1) * dw], &cell.scale[t * lanes..(t + 1) * lanes], &back)?;
            out[t * dw..(t + 1) * dw].copy_from_slice(&rho);
        }
        Ok(out)
    }

    /// [measurement; theory, November 13, the junction record §13.8; G158] **The reader's reaction, read at its founding**: one region's forward
    /// and reverse, and for each tick (in the forward's order), head and kind of reader (`[0]` open readers, `[1]` written) the written sources'
    /// [`ReactionSums`] of `a_j = ⟨λ_j^(k+1), ρ_j^(h,k)⟩` ([`Constitution::reaction_route`]), so `d(code)/dκ_h = −Σ_k Σ_j a_j` for the stage
    /// `x_j ← x_j − κ_h ρ_j` after tick `k`. A reading only: nothing in the law reads it.
    /// [measurement; agent-inferred, November 13, the ring record's §4 first reading] **The release carried as a face, at its founding**: for
    /// each site `t`, `r_t = ⟨λ⁰_t, D_t⟩`, the opening's covector `λ⁰` of the region's own comparison against the change the opening of `t`
    /// would take were every open site's row to move toward its carried face at strength `α`: `D_t = Δ_t(enc) + Δ_(t−1)(before) +
    /// Δ_(t+1)(after)`, `Δ_s(base) = release(Σ_c w_(s,c) E_base(c), 16) − E_base(∗)` at an open site `s` carrying `faces[s]` (its shares on
    /// `2^(−16)`, [`shares`]) and zero at a written one. So `d(code)/dα` at `α = 0` is `Σ_t r_t` on the covector's grain against the state's
    /// (`2^(−40)` bits a unit), the opening's part of the strength only: the carried site's voice (a source at strength `α`) is not read. A
    /// reading: no state changes.
    pub fn carried_slopes(&self, region: &Region, faces: &[Option<TowerFace>]) -> Result<Vec<i128>> {
        let pass = self.pass(region, true)?;
        let mut g = vec![0i128; self.material_len()];
        let mut dx = Vec::new();
        self.returned_with(region, &pass, &mut g, None, None, None, None, None, Some(&mut dx))?;
        let (dw, sites, a) = (self.declaration.width, region.classes.len(), self.declaration.alphabet);
        let l = &self.layout;
        let delta = |base: usize, s: usize| -> Option<Vec<i64>> {
            if !region.unresolved[s] {
                return None;
            }
            let sh = shares(faces.get(s)?.as_ref()?);
            let open = base + a * dw;
            Some((0..dw).map(|i| release(sh.iter().map(|&(c, w)| w as i128 * self.theta[base + c as usize * dw + i] as i128).sum(), STATE_BITS) as i64 - self.theta[open + i] as i64).collect())
        };
        let mut r = vec![0i128; sites];
        for (t, slot) in r.iter_mut().enumerate() {
            let dxt = &dx[t * dw..(t + 1) * dw];
            let parts = [delta(l.enc, t), t.checked_sub(1).and_then(|s| delta(l.before, s)), (t + 1 < sites).then(|| delta(l.after, t + 1)).flatten()];
            for d in parts.into_iter().flatten() {
                *slot += dxt.iter().zip(&d).map(|(&x, &y)| i128::from(x) * i128::from(y)).sum::<i128>();
            }
        }
        Ok(r)
    }

    pub fn reaction_covectors(&self, region: &Region) -> Result<Vec<Vec<[ReactionSums; 2]>>> {
        let pass = self.pass(region, true)?;
        let mut g = vec![0i128; self.material_len()];
        let mut lambdas: Vec<Vec<i64>> = Vec::new();
        self.returned_with(region, &pass, &mut g, None, None, None, None, Some(&mut lambdas), None)?;
        lambdas.reverse();
        let (sites, dw, heads) = (region.classes.len(), self.declaration.width, self.declaration.heads);
        let definite: Vec<bool> = (0..sites).map(|t| Self::definite(region, t)).collect();
        let mut out = Vec::with_capacity(pass.ticks.len());
        for (cell, lambda) in pass.ticks.iter().zip(&lambdas) {
            let paces = pass.paces_at(cell);
            let mut by_head = Vec::with_capacity(heads);
            for h in 0..heads {
                let mut kinds = [ReactionSums::default(); 2];
                for (kind, sums) in kinds.iter_mut().enumerate() {
                    let rho = self.reaction_route(cell, paces, &definite, h, kind == 1)?;
                    for j in (0..sites).filter(|&j| definite[j]) {
                        let span = j * dw..(j + 1) * dw;
                        let a: i128 = lambda[span.clone()].iter().zip(&rho[span.clone()]).map(|(&y, &r)| i128::from(y) * i128::from(r)).sum();
                        sums.rows += 1;
                        (sums.a, sums.a_abs, sums.a_sq) = (sums.a + a, sums.a_abs + a.unsigned_abs(), sums.a_sq + (a.unsigned_abs() >> 32).pow(2));
                        sums.rho_sq += rho[span.clone()].iter().map(|&r| (r.unsigned_abs() as u128 >> 8).pow(2)).sum::<u128>();
                        sums.x_sq += cell.after[span].iter().map(|&x| (x.unsigned_abs() as u128 >> 8).pow(2)).sum::<u128>();
                    }
                }
                by_head.push(kinds);
            }
            out.push(by_head);
        }
        Ok(out)
    }

    /// [definition; agent-inferred, November 13, from the junction record §13.8 and the theory thread's last input of 20:26Z; G160] **The read's
    /// mirror**: the forward read of head `h` is `x_i += Σ_j W_ij r̂_j` with `W_ij = p_ij D_ij O_h conj(U_i) U_j V_h` (the current's return over
    /// the framed, shared and decayed values of the sources' rays). Its mirror is the same read taken by each source of its readers,
    /// `μ_j = (1/n_j) Σ_i W_ijᵀ r̂_i`, with `n_j = Σ_i p_ij D̄_ij` the source's audience (`D̄` the mean of the head's skins over its modes; a crowd's
    /// share spread over its definite sources at the octave's decay): the readers' rays `r̂_i` (the chart of their state after the tick,
    /// `cell.after`), `O_hᵀ`, the frame `U_i`, the shares and skins, `conj(U_j)` and `V_hᵀ`, every release the forward's grain, so `μ` is on the
    /// state's grain and a pure number times it is a step a ray reads. No lane adjoint at the source and no raw reader state: every read takes
    /// rays. With `readers` only the readers of that kind (`false` open, `true` written). Returns `μ` (`[t][D]`, zero at a site no reader hears) and
    /// each site's audience on `2^(−63)`.
    pub(crate) fn mirror_route(&self, cell: &TickCell, paces: &Paces, definite: &[bool], h: usize, readers: Option<bool>) -> Result<(Vec<i64>, Vec<u128>)> {
        let d = &self.declaration;
        let (dw, m, n, lanes) = (d.width, d.complex(), d.modes, d.lanes);
        let (m2, span) = (2 * m, 2 * n);
        let sites = definite.len();
        let (l, reaches) = (&self.layout, self.reaches());
        // Each reader's ray after the tick, its head's block of `O_hᵀ r̂_i`, framed `U_i`.
        let mut hy = vec![0i64; sites * span];
        let (mut rays, mut scales) = (Vec::with_capacity(dw), Vec::with_capacity(lanes));
        let mut dy = vec![0i64; m2];
        for t in (0..sites).filter(|&t| readers.is_none_or(|k| definite[t] == k)) {
            (rays.clear(), scales.clear());
            lane_chart(&cell.after[t * dw..(t + 1) * dw], lanes, &mut rays, &mut scales)?;
            let ray: Vec<i64> = rays.iter().map(|&r| i64::from(r)).collect();
            transposed(&self.theta[l.out..l.out + dw * m2], reaches.out, m2, &ray, MATERIAL_BITS, &mut dy)?;
            for li in 0..n {
                let c = h * n + li;
                let (ur, ui) = self.frame(paces, t, h, li);
                let (ur, ui) = (ur as i128, ui as i128);
                let (gr, gi) = (dy[c] as i128, dy[m + c] as i128);
                hy[t * span + li] = fit64(release(ur * gr - ui * gi, MOVE_BITS))?;
                hy[t * span + n + li] = fit64(release(ui * gr + ur * gi, MOVE_BITS))?;
            }
        }
        let rows = &cell.rows[h * sites..(h + 1) * sites];
        let crowds = &cell.crowds[h * sites..(h + 1) * sites];
        let mut sv = vec![0i128; sites * span];
        let mut crowd_v = vec![0i128; (sites + 1) * span];
        let mut audience = vec![0u128; sites];
        let mut crowd_n = vec![0i128; sites + 1];
        for i in (0..sites).filter(|&i| readers.is_none_or(|k| definite[i] == k)) {
            for src in &rows[i] {
                let j = src.j as usize;
                let mut mean = 0i128;
                for r in 0..span {
                    let decay = self.pair_decay(paces, h, r % n, i, j);
                    sv[j * span + r] += src.p as i128 * decayed(decay, hy[i * span + r]);
                    if r < n {
                        mean += release(src.p as i128 * decay.0, decay.1);
                    }
                }
                audience[j] += (mean / n as i128).max(0) as u128;
            }
            for c in &crowds[i] {
                let mut mean = 0i128;
                for r in 0..span {
                    let decay = self.octave_decay(paces, h, r % n, i, c.level, c.lo > i);
                    let part = div_nearest(c.e as i128 * decayed(decay, hy[i * span + r]), c.count as i128);
                    crowd_v[c.lo * span + r] += part;
                    crowd_v[(c.hi + 1) * span + r] -= part;
                    if r < n {
                        mean += release(c.e as i128 * decay.0, decay.1);
                    }
                }
                let share = div_nearest(mean / n as i128, c.count as i128);
                crowd_n[c.lo] += share;
                crowd_n[c.hi + 1] -= share;
            }
        }
        let (mut run_v, mut run_n) = (vec![0i128; span], 0i128);
        let mut out = vec![0i64; sites * dw];
        let mut dv = vec![0i64; m2];
        let mut back = vec![0i64; dw];
        for j in 0..sites {
            for r in 0..span {
                run_v[r] += crowd_v[j * span + r];
            }
            run_n += crowd_n[j];
            if definite[j] {
                audience[j] += run_n.max(0) as u128;
            }
            if audience[j] == 0 {
                continue;
            }
            dv.iter_mut().for_each(|v| *v = 0);
            for li in 0..n {
                let c = h * n + li;
                let (ur, ui) = self.frame(paces, j, h, li);
                let (ur, ui) = (ur as i128, ui as i128);
                let crowd = |r: usize| if definite[j] { run_v[r] } else { 0 };
                let (gr, gi) = (release(sv[j * span + li] + crowd(li), SHARE_BITS), release(sv[j * span + n + li] + crowd(n + li), SHARE_BITS));
                dv[c] = fit64(release(ur * gr + ui * gi, MOVE_BITS))?;
                dv[m + c] = fit64(release(ur * gi - ui * gr, MOVE_BITS))?;
            }
            transposed(&self.theta[l.v..l.v + m2 * dw], reaches.v, dw, &dv, MATERIAL_BITS, &mut back)?;
            for (o, &b) in out[j * dw..(j + 1) * dw].iter_mut().zip(&back) {
                *o = fit64(div_nearest(i128::from(b) << SHARE_BITS, audience[j] as i128))?;
            }
        }
        Ok((out, audience))
    }

    /// [measurement; theory, November 15 20:38Z] **What each site's tick moves, and what reaches it** ([`TickNews`]), one region's forward and
    /// reverse, a [`TickNews`] a tick in the forward's order. A reading only.
    pub fn tick_news(&self, region: &Region) -> Result<Vec<TickNews>> {
        let pass = self.pass(region, true)?;
        let mut g = vec![0i128; self.material_len()];
        let mut lambdas: Vec<Vec<i64>> = Vec::new();
        self.returned_with(region, &pass, &mut g, None, None, None, None, Some(&mut lambdas), None)?;
        lambdas.reverse();
        let (sites, dw) = (region.classes.len(), self.declaration.width);
        let mut out = Vec::with_capacity(pass.ticks.len());
        for (cell, lambda) in pass.ticks.iter().zip(&lambdas) {
            let mut r = TickNews::default();
            for t in 0..sites {
                let kind = usize::from(!Self::definite(region, t));
                let span = t * dw..(t + 1) * dw;
                let (mut a, mut dd, mut xx, mut ll) = (0i128, 0u128, 0u128, 0u128);
                for ((&after, &before), &l) in cell.after[span.clone()].iter().zip(&cell.before[span.clone()]).zip(&lambda[span.clone()]) {
                    let dx = i128::from(after) - i128::from(before);
                    a += i128::from(l) * dx;
                    dd += dx.unsigned_abs().pow(2);
                    xx += i128::from(before).unsigned_abs().pow(2);
                    ll += i128::from(l).unsigned_abs().pow(2);
                }
                r.sites[kind] += 1;
                r.cost[kind][octave_of(a.unsigned_abs())] += 1;
                r.cost_mass[kind][octave_of(a.unsigned_abs())] += a.unsigned_abs();
                r.cost_abs[kind] += a.unsigned_abs();
                let rel = (80 + octave_of(dd) as i64 - octave_of(xx) as i64).clamp(0, TICK_OCTAVES as i64 - 1) as usize;
                r.update[kind][if dd == 0 { 0 } else { rel }] += 1;
                r.covector[kind][octave_of(ll)] += 1;
            }
            out.push(r);
        }
        Ok(out)
    }

    /// [measurement; theory, November 15 21:16Z] **The forward with its quiet written site-ticks held** ([`HeldRead`]): one region's forward and
    /// reverse give each written site-tick its `a = ⟨λ^(k+1), Δx^k⟩` ([`TickNews`]); for each section `σ = 2^(40−e)` on `2^(−40)` bits (`e` in
    /// `sigmas`) the forward is read again with every written site-tick of `|a| < σ` held (the oracle), and again with as many written sites held
    /// at each tick by the chart's move (`Σ (r̂(x^(k+1)) − r̂(x^k))²` over the lanes' rays, least first: a criterion the forward can read), and
    /// the compared places' code is summed for each. A reading only.
    pub fn held_forward(&self, region: &Region, sigmas: &[u32]) -> Result<HeldRead> {
        let pass = self.pass(region, true)?;
        let mut g = vec![0i128; self.material_len()];
        let mut lambdas: Vec<Vec<i64>> = Vec::new();
        self.returned_with(region, &pass, &mut g, None, None, None, None, Some(&mut lambdas), None)?;
        lambdas.reverse();
        let d = &self.declaration;
        let (sites, dw, lanes, ticks) = (region.classes.len(), d.width, d.lanes, pass.ticks.len());
        let code = |f: &Forward| -> i128 { f.faces.iter().zip(region.classes).filter_map(|(face, &c)| face.as_ref().map(|x| i128::from(x.code(c)))).sum() };
        let written: Vec<bool> = (0..sites).map(|t| Self::definite(region, t)).collect();
        let mut out = HeldRead { compared: pass.faces.iter().filter(|f| f.is_some()).count() as u64, written: written.iter().filter(|&&w| w).count() as u64, code_full: code(&pass), ..HeldRead::default() };
        // Each written site-tick's `a` and its chart's move.
        let (mut a, mut moved) = (vec![vec![0i128; sites]; ticks], vec![vec![0u128; sites]; ticks]);
        let (mut rb, mut sb, mut ra, mut sa) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
        for (k, (cell, lambda)) in pass.ticks.iter().zip(&lambdas).enumerate() {
            for t in (0..sites).filter(|&t| written[t]) {
                let span = t * dw..(t + 1) * dw;
                a[k][t] = cell.after[span.clone()].iter().zip(&cell.before[span.clone()]).zip(&lambda[span.clone()]).map(|((&x1, &x0), &l)| i128::from(l) * (i128::from(x1) - i128::from(x0))).sum();
                (rb.clear(), sb.clear(), ra.clear(), sa.clear());
                lane_chart(&cell.before[span.clone()], lanes, &mut rb, &mut sb)?;
                lane_chart(&cell.after[span.clone()], lanes, &mut ra, &mut sa)?;
                moved[k][t] = rb.iter().zip(&ra).map(|(&p, &q)| (i128::from(q) - i128::from(p)).unsigned_abs().pow(2)).sum();
            }
            out.a_all.push(a[k].iter().sum());
            out.abs_all.push(a[k].iter().map(|v| v.unsigned_abs()).sum());
        }
        for &e in sigmas {
            let sigma = 1u128 << (40 - e);
            let oracle: Vec<Vec<bool>> = (0..ticks).map(|k| (0..sites).map(|t| written[t] && a[k][t].unsigned_abs() < sigma).collect()).collect();
            let mut by_chart = vec![vec![false; sites]; ticks];
            let (mut held, mut a_held, mut abs_held, mut abs_chart) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
            for k in 0..ticks {
                let n = oracle[k].iter().filter(|&&h| h).count();
                let mut order: Vec<usize> = (0..sites).filter(|&t| written[t]).collect();
                order.sort_by_key(|&t| (moved[k][t], t));
                for &t in order.iter().take(n) {
                    by_chart[k][t] = true;
                }
                held.push(n as u64);
                a_held.push((0..sites).filter(|&t| oracle[k][t]).map(|t| a[k][t]).sum::<i128>());
                abs_held.push((0..sites).filter(|&t| oracle[k][t]).map(|t| a[k][t].unsigned_abs()).sum::<u128>());
                abs_chart.push((0..sites).filter(|&t| by_chart[k][t]).map(|t| a[k][t].unsigned_abs()).sum::<u128>());
            }
            out.code_oracle.push(code(&self.pass_held(region, &oracle)?));
            out.code_chart.push(code(&self.pass_held(region, &by_chart)?));
            (out.held.push(held), out.a_held.push(a_held), out.abs_held.push(abs_held), out.abs_chart.push(abs_chart));
        }
        Ok(out)
    }

    /// [measurement; G160] **The read's mirror at its founding** ([`Constitution::mirror_route`]): one region's forward and reverse, and for each tick
    /// (in the forward's order), head and kind of reader (`[0]` open readers, `[1]` written, `[2]` both) the written sources' [`MirrorSums`] of
    /// `a_j = ⟨λ_j^(k+1), μ_j⟩`, so for the stage `x_j ← x_j − s_h μ_j` after tick `k` the code moves by `−s_h Σ_j a_j 2^(−40)` bits (the
    /// covector's grain against the state's, read from the reverse's checked central differences), and with both kinds the source's chart's
    /// covector `Σ_j a_j r̂_j` (its ray after the tick), the audience and the lane powers. A reading only.
    pub fn mirror_covectors(&self, region: &Region) -> Result<Vec<Vec<[MirrorSums; 3]>>> {
        let pass = self.pass(region, true)?;
        let mut g = vec![0i128; self.material_len()];
        let mut lambdas: Vec<Vec<i64>> = Vec::new();
        self.returned_with(region, &pass, &mut g, None, None, None, None, Some(&mut lambdas), None)?;
        lambdas.reverse();
        let d = &self.declaration;
        let (sites, dw, heads, lanes) = (region.classes.len(), d.width, d.heads, d.lanes);
        let definite: Vec<bool> = (0..sites).map(|t| Self::definite(region, t)).collect();
        let mut out = Vec::with_capacity(pass.ticks.len());
        let (mut rays, mut scales) = (Vec::with_capacity(dw), Vec::with_capacity(lanes));
        for (cell, lambda) in pass.ticks.iter().zip(&lambdas) {
            let paces = pass.paces_at(cell);
            let mut by_head = Vec::with_capacity(heads);
            for h in 0..heads {
                let mut kinds: [MirrorSums; 3] = Default::default();
                for (kind, sums) in kinds.iter_mut().enumerate() {
                    let readers = [Some(false), Some(true), None][kind];
                    let (mu, audience) = self.mirror_route(cell, paces, &definite, h, readers)?;
                    if readers.is_none() {
                        sums.chart = vec![(0, 0); dw];
                    }
                    for j in (0..sites).filter(|&j| definite[j] && audience[j] > 0) {
                        let span = j * dw..(j + 1) * dw;
                        let a: i128 = lambda[span.clone()].iter().zip(&mu[span.clone()]).map(|(&y, &r)| i128::from(y) * i128::from(r)).sum();
                        sums.sources += 1;
                        (sums.a, sums.a_abs, sums.a_sq) = (sums.a + a, sums.a_abs + a.unsigned_abs(), sums.a_sq + (a.unsigned_abs() >> 32).pow(2));
                        if readers.is_none() {
                            (rays.clear(), scales.clear());
                            lane_chart(&cell.after[span.clone()], lanes, &mut rays, &mut scales)?;
                            for (slot, &r) in sums.chart.iter_mut().zip(&rays) {
                                let v = a * i128::from(r);
                                (slot.0, slot.1) = (slot.0 + v, slot.1 + v.unsigned_abs());
                            }
                            sums.audience += audience[j] >> 32;
                            for &sc in &scales {
                                let b = log2_grain(sc.max(1) as u128);
                                (sums.power_log, sums.power_log_sq, sums.lanes) = (sums.power_log + i128::from(b), sums.power_log_sq + (i128::from(b) * i128::from(b)) as u128, sums.lanes + 1);
                            }
                        }
                    }
                }
                by_head.push(kinds);
            }
            out.push(by_head);
        }
        Ok(out)
    }

    /// [measurement; theory, November 13, the theory thread's answers of 20:20Z on the reader's reaction; G159] **The reaction's forms at its
    /// founding**, from one region's forward and reverse, for each tick and head ([`ReactionForms`]): the pair's impulse decomposed by reader
    /// and source, `a_ij = p_ij Σ_l D_ijl ⟨g_jl, h_il⟩` with `g_j = U_j V_h J_r̂(x_j^k) λ_j^(k+1)` (the chart's Jacobian read through its
    /// adjoint, which is symmetric) and `h_i = U_i O_hᵀ x_i^(k+1)`, a crowd's share spread over its definite sources at the octave's decay; the
    /// source's chart's covector `Σ_j a_j r̂_j` and the reader's `Σ_i b_i r̂_i` (`a_j = Σ_i a_ij`, `b_i = Σ_j a_ij`), each coordinate with its
    /// magnitude; and the covector of the strength raised by the source's metric, `Σ_j Σ_lane a_j,lane ‖x_j,lane‖²/n_j` with `n_j = Σ_i p_ij D̄_ij`
    /// the source's audience (`D̄` the mean over the head's modes; the reaches' `γ_h²` a constant a head, left out). Beside them the route's own
    /// `a_j` ([`Constitution::reaction_route`]) and the share of written sources where the two agree in sign. A reading only.
    pub fn reaction_forms(&self, region: &Region) -> Result<Vec<Vec<ReactionForms>>> {
        let pass = self.pass(region, true)?;
        let mut g = vec![0i128; self.material_len()];
        let mut lambdas: Vec<Vec<i64>> = Vec::new();
        self.returned_with(region, &pass, &mut g, None, None, None, None, Some(&mut lambdas), None)?;
        lambdas.reverse();
        let d = &self.declaration;
        let (sites, dw, heads, n, m, lanes) = (region.classes.len(), d.width, d.heads, d.modes, d.complex(), d.lanes);
        let (m2, span, lw) = (2 * m, 2 * d.modes, d.width / d.lanes);
        let (l, reaches) = (&self.layout, self.reaches());
        let definite: Vec<bool> = (0..sites).map(|t| Self::definite(region, t)).collect();
        let mut out = Vec::with_capacity(pass.ticks.len());
        for (cell, lambda) in pass.ticks.iter().zip(&lambdas) {
            let paces = pass.paces_at(cell);
            let mut by_head = Vec::with_capacity(heads);
            for h in 0..heads {
                let mut f = ReactionForms { src: vec![(0, 0); dw], rdr: vec![(0, 0); dw], ..ReactionForms::default() };
                // The route's own impulse, readers of both kinds.
                let mut rho = self.reaction_route(cell, paces, &definite, h, false)?;
                for (r, w) in rho.iter_mut().zip(self.reaction_route(cell, paces, &definite, h, true)?) {
                    *r = fit64(i128::from(*r) + i128::from(w))?;
                }
                // `h_i`, the reader's framed current transposed, and `g_j`, the source's framed value pushed forward from `λ_j`.
                let (mut hi_, mut gj) = (vec![0i128; sites * span], vec![0i128; sites * span]);
                let mut dy = vec![0i64; m2];
                for t in 0..sites {
                    transposed(&self.theta[l.out..l.out + dw * m2], reaches.out, m2, &cell.after[t * dw..(t + 1) * dw], MATERIAL_BITS, &mut dy)?;
                    let dr = lane_adjoint(&cell.read[t * dw..(t + 1) * dw], &cell.scale[t * lanes..(t + 1) * lanes], &lambda[t * dw..(t + 1) * dw])?;
                    for li in 0..n {
                        let c = h * n + li;
                        let (ur, ui) = self.frame(paces, t, h, li);
                        let (ur, ui) = (ur as i128, ui as i128);
                        let (yr, yi) = (dy[c] as i128, dy[m + c] as i128);
                        hi_[t * span + li] = release(ur * yr - ui * yi, MOVE_BITS);
                        hi_[t * span + n + li] = release(ui * yr + ur * yi, MOVE_BITS);
                        let row = |cc: usize| -> i128 { (0..dw).map(|i| i128::from(self.theta[l.v + cc * dw + i]) * i128::from(dr[i])).sum::<i128>() >> MATERIAL_BITS };
                        let (vr, vi) = (row(c), row(m + c));
                        gj[t * span + li] = release(ur * vr - ui * vi, MOVE_BITS);
                        gj[t * span + n + li] = release(ui * vr + ur * vi, MOVE_BITS);
                    }
                }
                let dot = |a: &[i128], b: &[i128], decay: &dyn Fn(usize) -> (i128, u32)| -> i128 {
                    (0..n).map(|li| { let (dec, grain) = decay(li); release(dec * (a[li] * b[li] + a[n + li] * b[n + li]), grain) }).sum()
                };
                let (mut a_src, mut b_rdr, mut audience) = (vec![0i128; sites], vec![0i128; sites], vec![0u128; sites]);
                let mut spread_h = vec![0i128; (sites + 1) * span];
                let mut spread_n = vec![0i128; sites + 1];
                let rows = &cell.rows[h * sites..(h + 1) * sites];
                let crowds = &cell.crowds[h * sites..(h + 1) * sites];
                // The definite sources' `g` summed over the places, for a crowd's members.
                let mut gsum = vec![0i128; (sites + 1) * span];
                for t in 0..sites {
                    for r in 0..span {
                        gsum[(t + 1) * span + r] = gsum[t * span + r] + if definite[t] { gj[t * span + r] } else { 0 };
                    }
                }
                for i in 0..sites {
                    let hrow = &hi_[i * span..(i + 1) * span];
                    for src in &rows[i] {
                        let j = src.j as usize;
                        let term = dot(&gj[j * span..(j + 1) * span], hrow, &|li| self.pair_decay(paces, h, li, i, j));
                        let a = release(src.p as i128 * term, SHARE_BITS);
                        (a_src[j], b_rdr[i]) = (a_src[j] + a, b_rdr[i] + a);
                        let mean: i128 = (0..n).map(|li| { let (dec, grain) = self.pair_decay(paces, h, li, i, j); release(src.p as i128 * dec, grain) }).sum::<i128>() / n as i128;
                        audience[j] += mean.max(0) as u128;
                    }
                    for c in &crowds[i] {
                        let members: Vec<i128> = (0..span).map(|r| gsum[(c.hi + 1) * span + r] - gsum[c.lo * span + r]).collect();
                        let decay = |li: usize| self.octave_decay(paces, h, li, i, c.level, c.lo > i);
                        let term = dot(&members, hrow, &decay);
                        b_rdr[i] += release(div_nearest(c.e as i128 * term, c.count as i128), SHARE_BITS);
                        for r in 0..span {
                            let (dec, grain) = decay(r % n);
                            let part = div_nearest(c.e as i128 * release(dec * hrow[r], grain), c.count as i128);
                            spread_h[c.lo * span + r] += part;
                            spread_h[(c.hi + 1) * span + r] -= part;
                        }
                        let mean: i128 = (0..n).map(|li| { let (dec, grain) = decay(li); release(c.e as i128 * dec, grain) }).sum::<i128>() / n as i128;
                        let share = div_nearest(mean, c.count as i128);
                        spread_n[c.lo] += share;
                        spread_n[c.hi + 1] -= share;
                    }
                }
                let (mut run_h, mut run_n) = (vec![0i128; span], 0i128);
                for j in 0..sites {
                    for r in 0..span {
                        run_h[r] += spread_h[j * span + r];
                    }
                    run_n += spread_n[j];
                    if !definite[j] {
                        continue;
                    }
                    a_src[j] += release((0..span).map(|r| gj[j * span + r] * run_h[r]).sum::<i128>(), SHARE_BITS);
                    audience[j] += run_n.max(0) as u128;
                }
                for j in (0..sites).filter(|&j| definite[j]) {
                    let span_j = j * dw..(j + 1) * dw;
                    let route: i128 = lambda[span_j.clone()].iter().zip(&rho[span_j.clone()]).map(|(&y, &r)| i128::from(y) * i128::from(r)).sum();
                    f.sources += 1;
                    f.route += route;
                    f.pair += a_src[j];
                    f.agree += u64::from((route > 0) == (a_src[j] > 0));
                    for (i, slot) in f.src.iter_mut().enumerate() {
                        let v = a_src[j] * i128::from(cell.read[j * dw + i]);
                        (slot.0, slot.1) = (slot.0 + v, slot.1 + v.unsigned_abs());
                    }
                    // The strength raised by the source's metric: each lane's impulse times its power squared, over the audience.
                    let n_j = (audience[j] >> 32).max(1) as i128;
                    let mut weighted = 0i128;
                    for lane in 0..lanes {
                        let at = j * dw + lane * lw..j * dw + (lane + 1) * lw;
                        let a_lane: i128 = lambda[at.clone()].iter().zip(&rho[at]).map(|(&y, &r)| i128::from(y) * i128::from(r)).sum();
                        let power = (cell.scale[j * lanes + lane] >> 8).pow(2);
                        weighted += a_lane.checked_mul(power).ok_or(TowerError::Refused("a reaction's metric-raised reading past its carrier"))? / n_j;
                    }
                    (f.w, f.w_abs, f.w_sq) = (f.w + weighted, f.w_abs + weighted.unsigned_abs(), f.w_sq + (weighted.unsigned_abs() >> 8).pow(2));
                }
                for i in 0..sites {
                    f.readers += u64::from(b_rdr[i] != 0);
                    for (k, slot) in f.rdr.iter_mut().enumerate() {
                        let v = b_rdr[i] * i128::from(cell.read[i * dw + k]);
                        (slot.0, slot.1) = (slot.0 + v, slot.1 + v.unsigned_abs());
                    }
                }
                by_head.push(f);
            }
            out.push(by_head);
        }
        Ok(out)
    }

    /// [measurement; agent-inferred, November 13; G167] **Every site's face after the ticks** (written sites included), read through the
    /// readout from the state the last tick hands on: where the passage holds a written site's class, its code there is evidence a loop can
    /// read of whether its releases mislead what is known. A reading only.
    pub fn faces_everywhere(&self, region: &Region) -> Result<Vec<TowerFace>> {
        let pass = self.pass(region, true)?;
        let (dw, reaches) = (self.declaration.width, self.reaches());
        let last = pass.ticks.last().ok_or(TowerError::Refused("a pass with no tick"))?;
        (0..region.classes.len()).map(|t| Ok(self.face_of(&last.handed[t * dw..(t + 1) * dw], &reaches)?.face)).collect()
    }

    /// [measurement; agent-inferred, November 13; G162] **The free ring on the host**: one region's forward at the field's declared ticks (a caller
    /// sets them past the trained depth), and for each stage (the state each tick hands on, after the mirror's stage where
    /// [`Constitution::mirror_strength`] is set) over the region's open places: the code of the place's class and the face's expected code, both on
    /// `2^(−20)` bits summed, and the changes of the places' charts between stages, `Σ |Δr̂_k|²` and `Σ ⟨Δr̂_k, Δr̂_(k−1)⟩` (on `2^(−32)`, from
    /// the second stage), the free iteration's relaxation or turning as read-depth reads it on the card (G149). A reading only.
    pub fn free_ring(&self, region: &Region) -> Result<Vec<RingStage>> {
        let pass = self.pass(region, true)?;
        let d = &self.declaration;
        let (dw, lanes) = (d.width, d.lanes);
        let reaches = self.reaches();
        let open: Vec<usize> = (0..region.classes.len()).filter(|&t| region.unresolved[t]).collect();
        let mut out = Vec::with_capacity(pass.ticks.len());
        let (mut prev, mut prev_change): (Option<Vec<i32>>, Option<Vec<i64>>) = (None, None);
        let (mut rays, mut scales) = (Vec::new(), Vec::new());
        for cell in &pass.ticks {
            let mut stage = RingStage::default();
            let mut charts = Vec::with_capacity(open.len() * dw);
            for &t in &open {
                let xt = &cell.handed[t * dw..(t + 1) * dw];
                let read = self.face_of(xt, &reaches)?;
                stage.code += i128::from(read.face.code(region.classes[t]));
                let sum: i128 = read.face.masses.iter().map(|&m| m as i128 * face_code(m, read.face.total) as i128).sum();
                stage.expected += sum / (read.face.total as i128).max(1);
                (rays.clear(), scales.clear());
                lane_chart(xt, lanes, &mut rays, &mut scales)?;
                charts.extend_from_slice(&rays);
            }
            stage.places = open.len() as u64;
            if let Some(p) = prev.as_ref() {
                let change: Vec<i64> = charts.iter().zip(p).map(|(&a, &b)| i64::from(a) - i64::from(b)).collect();
                stage.norm = change.iter().map(|&c| (c as i128 * c as i128) as u128).sum();
                if let Some(pc) = prev_change.as_ref() {
                    stage.inner = change.iter().zip(pc).map(|(&a, &b)| a as i128 * b as i128).sum();
                }
                prev_change = Some(change);
            }
            prev = Some(charts);
            out.push(stage);
        }
        Ok(out)
    }

    /// [measurement; theory, November 13, the junction record §13.9; G157] **A turned head's reach on its own clock, read at its founding**: one
    /// region's forward and reverse, and for each tick (in the reverse's order turned back to the forward's) and head the receiver rows'
    /// [`ReachSums`] by kind (`[0]` open, `[1]` written); a still head's are empty. A reading only: nothing in the law reads it.
    pub fn reach_covectors(&self, region: &Region) -> Result<Vec<Vec<[ReachSums; 2]>>> {
        let pass = self.pass(region, true)?;
        let mut g = vec![0i128; self.material_len()];
        let mut flat: Vec<[ReachSums; 2]> = Vec::new();
        self.returned_with(region, &pass, &mut g, None, None, None, Some(&mut flat), None, None)?;
        let heads = self.declaration.heads;
        let mut by_tick: Vec<Vec<[ReachSums; 2]>> = flat.chunks(heads).map(<[_]>::to_vec).collect();
        by_tick.reverse();
        Ok(by_tick)
    }

    /// [measurement; theory, November 13, the junction record §9 and the theory thread's order after G151, item (a)] **The return's chart covector
    /// by tick**: on a field with the junction's return, one region's forward and reverse, and for each tick with a return (past the first) its
    /// index, each site's `δℓ` (`[t]`, `ℓ`'s covector on `2^(−16)` at the covector's grain, [`junction_return`]) and the tick's opening chart `r̂`
    /// (`[t][D]`), with the code's covector over the whole material beside them. At the founding (`Γ = 0`) the forward is the built tick's and the
    /// reverse the built reverse, so `δℓ = (ln 2/2) ⟨λ^(k+1), x^(k+1) − x^(k−1)⟩` reads what a first deposit of the return would see. A reading only.
    pub fn junction_covectors(&self, region: &Region) -> Result<(Vec<(usize, Vec<i64>, Vec<i32>)>, Vec<i128>)> {
        if !self.declaration.junction {
            return refuse("a reading of the junction's return on a field without it");
        }
        let pass = self.pass(region, true)?;
        let mut g = vec![0i128; self.material_len()];
        let mut by_tick: Vec<(usize, Vec<i64>)> = Vec::new();
        self.returned_with(region, &pass, &mut g, None, None, Some(&mut by_tick), None, None, None)?;
        by_tick.reverse();
        Ok((by_tick.into_iter().map(|(k, dl)| (k, dl, pass.ticks[k].read.clone())).collect(), g))
    }

    /// [measurement; agent-inferred, November 5, §16.44] **Each of `sites`' clocks by tick** ([`BlankClocks`]): whether a
    /// blank gap's expected duration holds its written length, and whether the faces the clocks read still predict the
    /// byte. A reading only: nothing in the law reads it.
    pub fn blank_clocks(&self, region: &Region, sites: &[usize]) -> Result<Vec<BlankClocks>> {
        let pass = self.pass(region, true)?;
        if sites.iter().any(|&i| i >= region.classes.len()) {
            return refuse("a clock's site outside its region");
        }
        Ok(sites
            .iter()
            .map(|&i| BlankClocks {
                ticks: pass
                    .ticks
                    .iter()
                    .map(|cell| cell.clock.as_deref().and_then(|c| c.reads.get(i).and_then(Option::as_ref).map(|r| (c.paces.kappa.iter().map(|k| k[i]).collect(), r.face.clone()))))
                    .collect(),
            })
            .collect())
    }

    /// [measurement; agent-inferred, November 4, §16.42] **Each of `sites`' near field by offset** ([`NearOffsets`]): whether
    /// a receiver tells its neighbouring offsets apart where their faces are equal, as a restated result needs (in
    /// `<<E=C>>D` the result C is written again as D, and D's `k`-th site reads C's `k`-th at offset `|C| + 2`). A reading
    /// only: nothing in the law reads it.
    pub fn near_offsets(&self, region: &Region, sites: &[usize]) -> Result<Vec<NearOffsets>> {
        let pass = self.pass(region, true)?;
        let n = region.classes.len();
        if sites.iter().any(|&i| i >= n) {
            return refuse("a near-field site outside its region");
        }
        let heads = self.declaration.heads;
        Ok(sites
            .iter()
            .map(|&i| {
                let mut out = NearOffsets { logits: pass.logits[i].clone(), ..NearOffsets::default() };
                for cell in &pass.ticks {
                    for h in 0..heads {
                        let (mut before, mut after) = ([0u64; NEAR - 1], [0u64; NEAR - 1]);
                        for src in &cell.rows[h * n + i] {
                            let j = src.j as usize;
                            if j < i && i - j < NEAR {
                                before[i - j - 1] = src.p;
                            } else if j > i && j - i < NEAR {
                                after[j - i - 1] = src.p;
                            }
                        }
                        out.before.push(before);
                        out.after.push(after);
                    }
                }
                out
            })
            .collect())
    }
}

/// [measurement; agent-inferred, November 4] **A tick's read of a region**: each site's chart `r̂` on `2^(−16)` and its scales (the
/// faces' power, one a lane) at the opening of each tick, the field's state as its ticks meet it (a reading of expansion and
/// volume); and (§16.40) the pair contact's chart and scales, the state after the tick's current and before its pair contact.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TickRead {
    pub read: Vec<i32>,
    pub scale: Vec<i128>,
    pub pair_read: Vec<i32>,
    pub pair_scale: Vec<i128>,
}

impl Constitution {
    /// [measurement; theory, November 11 04:48, G39] **A section's return read twice**: each region's forward once, then its return `G`, then its return with the face covector of
    /// every loud place zeroed, `G_quiet`. A place's news mass is `m_t = ½ |p_t − q_t|₁` of its face `p_t` against its truth `q_t` (one-hot at the region's class), which is
    /// `1 − p_t(x_t)`: quiet where `m_t < 2^(−bits)`, i.e. `(total − mass(x_t)) 2^bits < total` on the face's integers. The deposit weights `m/K` are as they stand. A reading: the field and
    /// the regions are not changed.
    pub fn read_and_return_split(&self, regions: &[Region], bits: u32) -> Result<SplitReturn> {
        let len = self.material_len();
        let mut out = regions
            .par_iter()
            .try_fold(
                || SplitReturn { total: vec![0i128; len], quiet: vec![0i128; len], ..Default::default() },
                |mut acc, region| -> Result<_> {
                    let t0 = std::time::Instant::now();
                    let mut pass = self.pass(region, true)?;
                    acc.forward_ns += t0.elapsed().as_nanos();
                    let t1 = std::time::Instant::now();
                    self.returned(region, &pass, &mut acc.total)?;
                    acc.return_ns += t1.elapsed().as_nanos();
                    let mut loud = vec![false; region.classes.len()];
                    for (t, face) in pass.faces.iter().enumerate() {
                        let Some(face) = face else { continue };
                        let own = face.masses.get(region.classes[t]).copied().unwrap_or(0);
                        let news = face.total.saturating_sub(own);
                        if news.checked_shl(bits).is_some_and(|n| n < face.total) {
                            acc.quiet_places += 1;
                        } else {
                            loud[t] = true;
                            acc.loud += 1;
                        }
                    }
                    pass.skip = loud;
                    let t2 = std::time::Instant::now();
                    self.returned(region, &pass, &mut acc.quiet)?;
                    acc.quiet_return_ns += t2.elapsed().as_nanos();
                    Ok(acc)
                },
            )
            .try_reduce(
                || SplitReturn { total: vec![0i128; len], quiet: vec![0i128; len], ..Default::default() },
                |mut a, b| {
                    for (x, y) in a.total.iter_mut().zip(&b.total) {
                        *x += y;
                    }
                    for (x, y) in a.quiet.iter_mut().zip(&b.quiet) {
                        *x += y;
                    }
                    (a.loud, a.quiet_places) = (a.loud + b.loud, a.quiet_places + b.quiet_places);
                    (a.forward_ns, a.return_ns, a.quiet_return_ns) = (a.forward_ns + b.forward_ns, a.return_ns + b.return_ns, a.quiet_return_ns + b.quiet_return_ns);
                    Ok(a)
                },
            )?;
        // [G180] Where the field reads twice, both sums are the two reads' mean ([`Constitution::both_reads_mean`]).
        out.total = self.both_reads_mean(out.total);
        out.quiet = self.both_reads_mean(out.quiet);
        Ok(out)
    }

    /// [measurement; theory, November 13, P57 item 2 (G132)] **A region's charts by stage**: the chart `r̂` of every site's state at each tick's
    /// opening (stage `k` the state before tick `k`, stage 0 the opening `x⁰`) and after the last tick (the stage the faces read), `[t][D]` on
    /// `2^(−16)` each. A reading: no state changes.
    pub fn tick_charts(&self, region: &Region) -> Result<Vec<Vec<i32>>> {
        let pass = self.pass(region, true)?;
        let mut stages: Vec<Vec<i32>> = pass.ticks.iter().map(|c| c.read.clone()).collect();
        stages.push(pass.read.clone());
        Ok(stages)
    }

    /// [measurement; Brandon, November 15 00:58Z; the record of November 13 on loudness beside surprise, §4 and test 1] **A region's lane
    /// powers by stage**: every site's lane scales `‖r_ℓ‖_rms` (the powers the chart divides by, [`lane_chart`]) at each tick's opening and
    /// after the last tick (the stage the faces read), `[t][L]` each, on the state's grain. Its stages are those of [`Constitution::tick_charts`]. A
    /// reading: no state changes.
    pub fn tick_scales(&self, region: &Region) -> Result<Vec<Vec<i128>>> {
        let pass = self.pass(region, true)?;
        let mut stages: Vec<Vec<i128>> = pass.ticks.iter().map(|c| c.scale.clone()).collect();
        stages.push(pass.scale.clone());
        Ok(stages)
    }

    /// Each tick's read of `region` ([`TickRead`]), in tick order.
    pub fn tick_reads(&self, region: &Region) -> Result<Vec<TickRead>> {
        let pass = self.pass(region, true)?;
        Ok(pass.ticks.iter().map(|c| TickRead { read: c.read.clone(), scale: c.scale.clone(), pair_read: c.read2.clone(), pair_scale: c.scale2.clone() }).collect())
    }
}

impl Learner {

    /// [measurement; agent-inferred, November 3, §16.31] **Each family's step coherence**: over the family's entries, `Σ |m|`
    /// and `Σ √v` of the covector's two moments, so `Σ|m| / Σ√v` is near one where the family's covector keeps its sign
    /// from section to section (its step is driven) and near zero where its signs cancel (its step is noise). A reading only.
    pub fn step_coherence(&self) -> Vec<(usize, u128, u128)> {
        self.field
            .families_all()
            .iter()
            .map(|&(start, len, _)| {
                let m: u128 = self.first[start..start + len].iter().map(|v| v.unsigned_abs()).sum();
                let v: u128 = self.second[start..start + len].iter().map(|v| v.unsigned_abs().isqrt()).sum();
                (len, m, v)
            })
            .collect()
    }
}

/// [definition; theory, November 10 03:55] **An answer's letter balance**: each letter's count `N(a)` on `2^72` and the
/// faces' summed share `F(a) = Σ_t f_t(a)` on `2^(−72)` (each share floored on `2^(−40)`, its remainder carried on `2^(−72)`).
pub fn letter_balance(x: &[usize], faces: &[TowerFace]) -> (Vec<i128>, Vec<i128>) {
    let a = faces.first().map_or(0, |f| f.masses.len());
    let mut n = vec![0i128; a];
    for &c in x {
        n[c] += 1 << 72;
    }
    let mut f = vec![0i128; a];
    for face in faces {
        for (c, &m) in face.masses.iter().enumerate() {
            let share = (m << 40) / face.total;
            let rem = (m << 40) - share * face.total;
            f[c] += ((share as i128) << 32) + (((rem << 32) + face.total / 2) / face.total) as i128;
        }
    }
    (n, f)
}

/// [definition; §16.47] A face's entropy `Σ_a p(a) (−log₂ p(a))` on the codes' `2^(−20)` bits, each class's code
/// ([`TowerFace::code`]) weighed by its mass over the total and the sum released once at its nearest.
pub fn entropy(face: &TowerFace) -> i128 {
    let sum: i128 = face.masses.iter().enumerate().filter(|&(_, &m)| m > 0).map(|(a, &m)| m as i128 * face.code(a) as i128).sum();
    div_nearest(sum, face.total as i128)
}
