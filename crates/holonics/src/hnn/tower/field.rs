//! **The field: a problem is one relatively complete region, and one constitution is iterated over
//! all of its sites at once** (#404, #406; record
//! `2026-11-01_THE_PROBLEM_IS_ONE_FIELD_EVERY_SITE_READS_EVERY_OTHER_AND_THE_ANSWER_IS_REFINED_NOT_SPOKEN`).
//!
//! [definition; agent-inferred, November 1] Why it is built. The tower hears a passage one class
//! after another through a clocked scan: a site reads the past through its modes' running state,
//! the release speaks one class a pass, and on the card each stream is one serial, latency-bound
//! scan. Read on GSM8K, an answer's digit could not reach the question's number a median 190
//! bytes back (no built level gives a fine site full reach), the founded units spelled the same
//! number differently in the question and in its calculation, and nothing refined an answer
//! before it was released. The generation law asks for a joint field that is refined and whose
//! boundary is released. This owner is that law on one problem.
//!
//! **The object.** A problem is one relatively complete region: its question's sites are resolved
//! (their classes arrived), its answer's are unresolved (a held operand, the encoding's last row).
//! Each site carries a face `x_t` on `2^(−16)` and is framed by its place: a mode `m` of a head
//! carries the ring phasor `U_(t,m) = e^(2πi (t mod n_m)/n_m)`, `n_m` a prime power (the turned
//! modes; the CRT of coprime closures names a site's place), or `U = 1` (the still modes, which
//! read content without place). One constitution `F_Θ` is iterated `K` ticks, `x^(k+1) = F_Θ(x^k)`:
//!
//! ```text
//! open       x⁰_t = E(u_t), or E(∗) where t is unresolved
//! chart      r̂_t = x_t / ‖x_t‖_rms,   q_t = Q r̂_t + b_q,   k_t = K r̂_t + b_k,   v_t = V r̂_t + b_v
//! frame      q̃_t = U_t ⊙ q_t,   k̃_t = U_t ⊙ k_t                          complex modes, by head
//! contact    z_ij = 2^(−β) Σ_(m∈h) Re(conj(q̃_im) k̃_jm)                   every pair of sites, both ways
//! weights    e_ij = 2^(z_ij − max_j z_ij),   p_ij = e_ij / Σ_j e_ij      the Gibbs face, in bits
//! current    y_i = Σ_j p_ij v_j,   x ← x + O y + b_o
//! pair       r̂'_t = x_t / ‖x_t‖_rms,   a = W_a r̂' + b_a,   b = W_b r̂' + b_b,   x ← x + W_c (a ⊙ b) + b_c
//! face       z_t = R r̂(x^K_t) + c,   p̂_t(a) = 2^(z_a) / Σ_b 2^(z_b)        at the unresolved sites
//! ```
//!
//! The pairing `Re(conj(q̃_i) k̃_j) = Re(conj(q_i) U_i^* U_j k_j)` turns mode `m` by
//! `2π (j − i)/n_m`: a turned mode reads the relative place modulo its ring, a still mode reads the
//! contents alone, at any distance. There is no clock between sites and no carry across problems:
//! the region is the whole terrain the constitution meets, so the transferred response a scan's
//! carried state would owe is absent by construction.
//!
//! **Learning.** The comparison is completion: any subset of the region is unresolved, its targets
//! the classes that arrived there, and the code is `Σ −log₂ p̂_t(u_t)` over the unresolved sites.
//! The covector `p̂ − q` returns exactly through the `K` ticks (the operands that produced each
//! carrier, held from the forward). The deposit is the tower's: the covector's two moments, the
//! step `m/(√v + 2^(−32))` at `2^(−k)`, certified on the section's own regions by an exact
//! comparison of the products of their faces, halved until it is certified or moves nothing.
//!
//! **Release.** The answer's sites open unresolved and the field is refined over `S` sweeps: each
//! sweep reads every unresolved site's face, releases the `⌈r/(S − s)⌉` most locked (top mass
//! share, compared exactly by cross products) at width zero, and holds the rest. A site released
//! as the void class ends the answer: every site after the earliest released void is void. The
//! released sites are present terrain for the next sweep. A class is never spoken in order.
//!
//! **Exact integers, grains declared.** Faces, charts, framed charts and currents on `2^(−16)`;
//! material on `2^(−24)`; frames and weights' shares on `2^(−30)`; Gibbs weights on `2^(−62)`
//! relative to their peak; covectors on `2^(−24)`, the contact's on `2^(−40)`. Every product's
//! remainder below its grain is released to the nearest numerator and every sum is an integer
//! sum, so the sites, heads and regions summed in any order give the same bits: the host and any
//! partition of the card agree bit for bit.
//!
//! [definition] The computational object is the helical pair interaction: every pair of sites
//! meets through its framed modes' contact `Re(conj(q̃_i) k̃_j)`, the ring phasors carry the helix
//! (residue and whole winding modulo each closure), and the pair contact `a ⊙ b` is the
//! bilinear contact between two reads of one site. Of the winding guide's six general objects it
//! touches the **helix** (the ring phasors), the **pair** (site contacts and the bilinear
//! contact), **faces and placement** (the Gibbs face, the release by lock) and the **tube** (the
//! `K` ticks of one constitution); the cell holonomy and the tower thread stay attached through the
//! tower, which this owner does not replace.

use super::{affine, covector, deposit_step, div_nearest, exp_series, face_code, fewer_bits, fit32, fit64, half_turn, on_step_grain, outer_sum, ratio_adjoint, ratio_to_power, reach, refuse, release, toward, transposed, Result, TowerError, TowerFace, FACE_BITS, FIRST_RATE, MATERIAL_BITS, MOVE_BITS, SECOND_RATE};
use crate::hnn::keyed_modes::{ln2_face, Exponential};
use num_bigint::BigUint;
use rayon::prelude::*;

/// The weights' shares, `p_ij` on `2^(−30)`.
const SHARE_BITS: u32 = 30;
/// The contact covector's grain, `2^(−40)` (`δz` and `δs`).
const CONTACT_BITS: u32 = 40;

/// [definition; agent-inferred, November 1] **The field's declared law**: an alphabet of `A`
/// classes (the face's; the encoding carries one more row, the unresolved operand), a face width
/// `D`, `H` heads of `n` complex modes each (the first `still` of every head unframed, the rest on
/// the prime-power rings), `f` pair contacts and `K` ticks of the one constitution.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldDeclaration {
    pub alphabet: usize,
    pub width: usize,
    pub heads: usize,
    pub modes: usize,
    pub still: usize,
    pub contacts: usize,
    pub ticks: usize,
}

impl FieldDeclaration {
    /// `M = H n`, the complex modes over every head.
    pub fn complex(&self) -> usize {
        self.heads * self.modes
    }

    /// The contact's scale `β` (agent-inferred): a head's pairing sums `2n` products of reads at
    /// unit power, so its spread is `√(2n)`; `2^(−β)` with `β = ⌈½ ⌈log₂ 2n⌉⌉` brings it to about
    /// one bit (`β = 2` at `n = 8`).
    pub fn score_shift(&self) -> u32 {
        let reals = 2 * self.modes;
        let bits = usize::BITS - (reals - 1).leading_zeros();
        bits.div_ceil(2)
    }

    /// The key draws the founding reads, four bytes a draw: the encoding, the three charts and
    /// both pair drives.
    pub fn founding_draws(&self) -> usize {
        let m2 = 2 * self.complex();
        (self.alphabet + 1) * self.width + 3 * m2 * self.width + 2 * self.contacts * self.width
    }

    /// The declaration grown by `factor`: width, heads and contacts (a head's modes and its
    /// frames are kept).
    pub fn grown(&self, factor: usize) -> Result<Self> {
        let grow = |v: usize| v.checked_mul(factor).ok_or(TowerError::Refused("a grown extent outgrew its carrier"));
        Ok(Self { width: grow(self.width)?, heads: grow(self.heads)?, contacts: grow(self.contacts)?, ..*self })
    }

    fn admit(&self) -> Result<()> {
        if self.alphabet < 2 || self.width == 0 || self.heads == 0 || self.modes == 0 || self.still > self.modes || self.contacts == 0 || self.ticks == 0 {
            return refuse("a field needs two classes, a nonempty width, heads, modes, contacts and ticks, and no more still modes than a head has");
        }
        Ok(())
    }

    fn to_text(self) -> String {
        format!("hnn-field-v1 {} {} {} {} {} {} {}", self.alphabet, self.width, self.heads, self.modes, self.still, self.contacts, self.ticks)
    }

    fn from_text(line: &str) -> Result<Self> {
        let words: Vec<&str> = line.split(' ').collect();
        if words.len() != 8 || words[0] != "hnn-field-v1" {
            return refuse("a field's head line that is not hnn-field-v1");
        }
        let n = |w: &str| w.parse::<usize>().map_err(|_| TowerError::Refused("a field's declaration that is not a count"));
        let d = Self { alphabet: n(words[1])?, width: n(words[2])?, heads: n(words[3])?, modes: n(words[4])?, still: n(words[5])?, contacts: n(words[6])?, ticks: n(words[7])? };
        d.admit()?;
        Ok(d)
    }
}

/// The material's families in order: each family's first entry, the material's length, and
/// each family as `(start, len, grain)`. A realization reads the material through it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldLayout {
    pub enc: usize,
    pub q: usize,
    pub q_bias: usize,
    pub k: usize,
    pub k_bias: usize,
    pub v: usize,
    pub v_bias: usize,
    pub out: usize,
    pub out_bias: usize,
    pub a: usize,
    pub a_bias: usize,
    pub b: usize,
    pub b_bias: usize,
    pub w: usize,
    pub w_bias: usize,
    pub read: usize,
    pub read_bias: usize,
    pub len: usize,
    pub families: Vec<(usize, usize, u32)>,
}

impl FieldLayout {
    fn new(d: &FieldDeclaration) -> Self {
        let (dw, m2, f, a) = (d.width, 2 * d.complex(), d.contacts, d.alphabet);
        let mut families = Vec::new();
        let mut at = 0usize;
        let mut push = |len: usize, grain: u32| -> usize {
            families.push((at, len, grain));
            at += len;
            at - len
        };
        let enc = push((a + 1) * dw, FACE_BITS);
        let q = push(m2 * dw, MATERIAL_BITS);
        let q_bias = push(m2, FACE_BITS);
        let k = push(m2 * dw, MATERIAL_BITS);
        let k_bias = push(m2, FACE_BITS);
        let v = push(m2 * dw, MATERIAL_BITS);
        let v_bias = push(m2, FACE_BITS);
        let out = push(dw * m2, MATERIAL_BITS);
        let out_bias = push(dw, FACE_BITS);
        let a_ = push(f * dw, MATERIAL_BITS);
        let a_bias = push(f, FACE_BITS);
        let b = push(f * dw, MATERIAL_BITS);
        let b_bias = push(f, FACE_BITS);
        let w = push(dw * f, MATERIAL_BITS);
        let w_bias = push(dw, FACE_BITS);
        let read = push(a * dw, MATERIAL_BITS);
        let read_bias = push(a, FACE_BITS);
        Self { enc, q, q_bias, k, k_bias, v, v_bias, out, out_bias, a: a_, a_bias, b, b_bias, w, w_bias, read, read_bias, len: at, families }
    }
}

/// Whether `v ≥ 2` is a prime power.
fn prime_power(v: usize) -> bool {
    let mut p = 2usize;
    while p * p <= v && v % p != 0 {
        p += 1;
    }
    if v % p != 0 {
        return true;
    }
    let mut w = v;
    while w % p == 0 {
        w /= p;
    }
    w == 1
}

/// [agent-inferred, November 1] The turned modes' ring periods: the prime powers in ascending order
/// (`2, 3, 4, 5, 7, 8, 9, 11, 13, 16, …`), one a turned mode of each head. A prime's powers are its
/// own closures refined; coprime closures meet once per residue pair modulo their product, so the
/// rings together name a site's place past any region a GSM8K problem fills.
pub fn ring_periods(count: usize) -> Vec<usize> {
    let mut out = Vec::with_capacity(count);
    let mut v = 2usize;
    while out.len() < count {
        if prime_power(v) {
            out.push(v);
        }
        v += 1;
    }
    out
}

/// `e^(2πi r/n)` on `2^(−30)`, `r` taken in `(−n/2, n/2]`, from the half turn on `2^(−46)` by the
/// exponential's series: the ring's navigator face, read once and held resident. The four quarter
/// points are the turn's own constraint identities (`1`, `i`, `−1`, `−i`) and are held exactly; only
/// the faces between them are the series' attained faces.
fn ring_phasor(r: usize, n: usize, pi: i128) -> (i64, i64) {
    let one = 1i64 << MOVE_BITS;
    let (r, n) = (r as i128, n as i128);
    let c = if 2 * r > n { r - n } else { r };
    match (c, 2 * c == n, 4 * c == n, 4 * c == -n) {
        (0, ..) => return (one, 0),
        (_, true, ..) => return (-one, 0),
        (_, _, true, _) => return (0, one),
        (_, _, _, true) => return (0, -one),
        _ => {}
    }
    let theta = div_nearest(2 * pi * c, n);
    let (re, im) = exp_series(0, release(theta, 16));
    (re as i64, im as i64)
}

/// [definition; agent-inferred, November 1] **The field**: its declaration, its material `Θ`
/// (one vector, the families of [`FieldLayout`] in order), the rings' resident faces and the
/// exponential's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field {
    pub declaration: FieldDeclaration,
    pub theta: Vec<i32>,
    layout: FieldLayout,
    /// Each turned slot's period and its ring's phasors on `2^(−30)`.
    rings: Vec<(usize, Vec<(i64, i64)>)>,
    exponential: Exponential,
}

/// [definition; agent-inferred, November 1] A region: each site's class and whether it is
/// unresolved. An unresolved site opens on the encoding's last row; its class is the target its
/// face is compared with (a release ignores it).
#[derive(Clone, Copy, Debug)]
pub struct Region<'a> {
    pub classes: &'a [usize],
    pub unresolved: &'a [bool],
}

/// One tick's forward temporaries over a region.
#[derive(Clone, Debug, Default)]
struct TickCell {
    read: Vec<i32>,
    scale: Vec<i128>,
    /// Framed charts and values by head: `[h][t][2n]`, the real parts then the imaginary.
    q: Vec<i64>,
    k: Vec<i64>,
    v: Vec<i64>,
    /// Shares `[h][i][j]` on `2^(−30)`.
    p: Vec<i64>,
    /// The current `[t][2M]`.
    y: Vec<i64>,
    read2: Vec<i32>,
    scale2: Vec<i128>,
    a: Vec<i64>,
    b: Vec<i64>,
    c: Vec<i64>,
}

/// A region's forward: each tick's temporaries (held when the reverse will read them), the last
/// read, and each unresolved site's face.
#[derive(Clone, Debug, Default)]
struct FieldPass {
    ticks: Vec<TickCell>,
    read: Vec<i32>,
    scale: Vec<i128>,
    faces: Vec<Option<TowerFace>>,
}

/// Each family's `max |w|`, read once a pass.
struct Reaches {
    q: u64,
    k: u64,
    v: u64,
    out: u64,
    a: u64,
    b: u64,
    w: u64,
    read: u64,
}

impl Field {
    /// **The founding configuration** (agent-inferred, November 1), read from a declared exterior
    /// key stream (four bytes a key, a signed 32-bit integer read as a uniform draw on `[−1, 1)`):
    /// the encoding uniform on `[−1, 1)`; the charts `Q, K, V` and both pair drives `W_a, W_b`
    /// uniform on `±√(3/D)`, so each read of a unit-power face opens at unit power; the current's
    /// return `O`, the contact's return `W_c`, the readout and every bias at zero, so the field
    /// opens on the flat face and each tick on the identity.
    pub fn found(declaration: FieldDeclaration, keys: &[u8]) -> Result<Self> {
        declaration.admit()?;
        let layout = FieldLayout::new(&declaration);
        let mut theta = vec![0i32; layout.len];
        let mut cursor = 0usize;
        let mut draw = || -> Result<i64> {
            let word = keys.get(cursor..cursor + 4).ok_or(TowerError::Refused("fewer key bytes than the field's founding reads"))?;
            cursor += 4;
            Ok(i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i64)
        };
        let mut uniform = |slice: &mut [i32], num: u128, den: u128, bits: u32| -> Result<()> {
            for v in slice.iter_mut() {
                let k = draw()? as i128;
                let scaled = (k * ((num << bits) / den) as i128) >> 31;
                *v = fit32(scaled, "a founded value outgrew its 32-bit carrier")?;
            }
            Ok(())
        };
        let (dw, a) = (declaration.width, declaration.alphabet);
        let m2 = 2 * declaration.complex();
        let f = declaration.contacts;
        uniform(&mut theta[layout.enc..layout.enc + (a + 1) * dw], 1, 1, FACE_BITS)?;
        // √(3/D) as (√3·2^16)/(√D·2^16), each square root on 2^(−16).
        let (three, dd) = chart_scale(dw);
        for start in [layout.q, layout.k, layout.v] {
            uniform(&mut theta[start..start + m2 * dw], three, dd, MATERIAL_BITS)?;
        }
        for start in [layout.a, layout.b] {
            uniform(&mut theta[start..start + f * dw], three, dd, MATERIAL_BITS)?;
        }
        Ok(Self::with_theta(declaration, theta))
    }

    fn with_theta(declaration: FieldDeclaration, theta: Vec<i32>) -> Self {
        let layout = FieldLayout::new(&declaration);
        let pi = half_turn(MOVE_BITS + 16);
        let rings = ring_periods(declaration.modes - declaration.still).into_iter().map(|n| (n, (0..n).map(|r| ring_phasor(r, n, pi)).collect())).collect();
        Self { declaration, theta, layout, rings, exponential: Exponential::new(FACE_BITS) }
    }

    /// The material's families, each `(start, len, grain)`.
    pub fn families(&self) -> &[(usize, usize, u32)] {
        &self.layout.families
    }

    /// The material's layout.
    pub fn layout(&self) -> &FieldLayout {
        &self.layout
    }

    /// Each turned slot's period and its ring's phasors on `2^(−30)` (a realization's resident
    /// frames).
    pub fn rings(&self) -> &[(usize, Vec<(i64, i64)>)] {
        &self.rings
    }

    /// The exponential's resident face (the Gibbs weights' navigator).
    pub fn exponential(&self) -> &Exponential {
        &self.exponential
    }

    /// `ln 2` on `2^(−30)`, the weights' return reads it.
    pub fn ln2(&self) -> i128 {
        ln2_face()
    }

    /// The frame of local mode `l` of a head at site `t`, on `2^(−30)`.
    fn frame(&self, t: usize, l: usize) -> (i64, i64) {
        if l < self.declaration.still {
            return (1i64 << MOVE_BITS, 0);
        }
        let (n, ring) = &self.rings[l - self.declaration.still];
        ring[t % n]
    }

    fn reaches(&self) -> Reaches {
        let (dw, m2, f, a) = (self.declaration.width, 2 * self.declaration.complex(), self.declaration.contacts, self.declaration.alphabet);
        let l = &self.layout;
        let r = |start: usize, len: usize| reach(&self.theta[start..start + len]);
        Reaches { q: r(l.q, m2 * dw), k: r(l.k, m2 * dw), v: r(l.v, m2 * dw), out: r(l.out, dw * m2), a: r(l.a, f * dw), b: r(l.b, f * dw), w: r(l.w, dw * f), read: r(l.read, a * dw) }
    }

    fn admit_region(&self, region: &Region) -> Result<()> {
        if region.classes.len() != region.unresolved.len() || region.classes.is_empty() {
            return refuse("a region needs one class and one resolution a site");
        }
        if region.classes.iter().any(|&c| c >= self.declaration.alphabet) {
            return refuse("a region's class outside the field's alphabet");
        }
        Ok(())
    }

    /// The region's opening faces `x⁰`.
    fn open(&self, region: &Region) -> Vec<i64> {
        let dw = self.declaration.width;
        let unresolved_row = self.declaration.alphabet;
        let mut x = vec![0i64; region.classes.len() * dw];
        for (t, xt) in x.chunks_exact_mut(dw).enumerate() {
            let row = if region.unresolved[t] { unresolved_row } else { region.classes[t] };
            let start = self.layout.enc + row * dw;
            for (slot, &e) in xt.iter_mut().zip(&self.theta[start..start + dw]) {
                *slot = e as i64;
            }
        }
        x
    }

    /// One tick of the constitution over the region's faces `x` (`[t][D]`), its temporaries
    /// written to `cell`.
    fn tick(&self, x: &mut [i64], reaches: &Reaches, cell: &mut TickCell) -> Result<()> {
        let d = &self.declaration;
        let (dw, m, n, f, heads) = (d.width, d.complex(), d.modes, d.contacts, d.heads);
        let m2 = 2 * m;
        let sites = x.len() / dw;
        let l = &self.layout;
        let beta = d.score_shift();
        // The chart.
        cell.read = Vec::with_capacity(sites * dw);
        cell.scale = Vec::with_capacity(sites);
        for xt in x.chunks_exact(dw) {
            let (r, s) = ratio_to_power(xt)?;
            cell.read.extend_from_slice(&r);
            cell.scale.push(s);
        }
        let mut q = vec![0i64; sites * m2];
        let mut k = vec![0i64; sites * m2];
        let mut v = vec![0i64; sites * m2];
        for t in 0..sites {
            let rt = &cell.read[t * dw..(t + 1) * dw];
            affine(&self.theta[l.q..l.q + m2 * dw], reaches.q, dw, rt, Some(&self.theta[l.q_bias..l.q_bias + m2]), MATERIAL_BITS, MATERIAL_BITS, &mut q[t * m2..(t + 1) * m2])?;
            affine(&self.theta[l.k..l.k + m2 * dw], reaches.k, dw, rt, Some(&self.theta[l.k_bias..l.k_bias + m2]), MATERIAL_BITS, MATERIAL_BITS, &mut k[t * m2..(t + 1) * m2])?;
            affine(&self.theta[l.v..l.v + m2 * dw], reaches.v, dw, rt, Some(&self.theta[l.v_bias..l.v_bias + m2]), MATERIAL_BITS, MATERIAL_BITS, &mut v[t * m2..(t + 1) * m2])?;
        }
        // The frame, by head: [h][t][2n], real parts then imaginary.
        let span = 2 * n;
        cell.q = vec![0i64; heads * sites * span];
        cell.k = vec![0i64; heads * sites * span];
        cell.v = vec![0i64; heads * sites * span];
        for h in 0..heads {
            for t in 0..sites {
                let at = (h * sites + t) * span;
                for li in 0..n {
                    let c = h * n + li;
                    let (ur, ui) = self.frame(t, li);
                    let (ur, ui) = (ur as i128, ui as i128);
                    let (qr, qi) = (q[t * m2 + c] as i128, q[t * m2 + m + c] as i128);
                    let (kr, ki) = (k[t * m2 + c] as i128, k[t * m2 + m + c] as i128);
                    cell.q[at + li] = fit64(release(ur * qr - ui * qi, MOVE_BITS))?;
                    cell.q[at + n + li] = fit64(release(ui * qr + ur * qi, MOVE_BITS))?;
                    cell.k[at + li] = fit64(release(ur * kr - ui * ki, MOVE_BITS))?;
                    cell.k[at + n + li] = fit64(release(ui * kr + ur * ki, MOVE_BITS))?;
                    cell.v[at + li] = v[t * m2 + c];
                    cell.v[at + n + li] = v[t * m2 + m + c];
                }
            }
        }
        // The contact, the weights and the current, head by head.
        cell.p = vec![0i64; heads * sites * sites];
        cell.y = vec![0i64; sites * m2];
        let mut z = vec![0i64; sites];
        for h in 0..heads {
            for i in 0..sites {
                let qi = &cell.q[(h * sites + i) * span..(h * sites + i + 1) * span];
                for (j, zj) in z.iter_mut().enumerate() {
                    let kj = &cell.k[(h * sites + j) * span..(h * sites + j + 1) * span];
                    let s: i128 = qi.iter().zip(kj).map(|(&a, &b)| a as i128 * b as i128).sum();
                    *zj = fit64(release(s, FACE_BITS + beta))?;
                }
                let peak = *z.iter().max().unwrap_or(&0);
                let e: Vec<u128> = z.iter().map(|&zj| self.exponential.below_one(zj as i128 - peak as i128)).collect();
                let mass: u128 = e.iter().sum();
                let row = &mut cell.p[(h * sites + i) * sites..(h * sites + i + 1) * sites];
                for (pj, &ej) in row.iter_mut().zip(&e) {
                    *pj = (((ej << SHARE_BITS) + mass / 2) / mass) as i64;
                }
                for r in 0..span {
                    let mut sum = 0i128;
                    for (j, &pj) in row.iter().enumerate() {
                        sum += pj as i128 * cell.v[(h * sites + j) * span + r] as i128;
                    }
                    let c = h * n + r % n;
                    let slot = if r < n { c } else { m + c };
                    cell.y[i * m2 + slot] = fit64(release(sum, SHARE_BITS))?;
                }
            }
        }
        let mut o = vec![0i64; dw];
        for t in 0..sites {
            affine(&self.theta[l.out..l.out + dw * m2], reaches.out, m2, &cell.y[t * m2..(t + 1) * m2], Some(&self.theta[l.out_bias..l.out_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut o)?;
            for (xv, ov) in x[t * dw..(t + 1) * dw].iter_mut().zip(&o) {
                *xv = fit64(*xv as i128 + *ov as i128)?;
            }
        }
        // The pair contact.
        cell.read2 = Vec::with_capacity(sites * dw);
        cell.scale2 = Vec::with_capacity(sites);
        for xt in x.chunks_exact(dw) {
            let (r, s) = ratio_to_power(xt)?;
            cell.read2.extend_from_slice(&r);
            cell.scale2.push(s);
        }
        cell.a = vec![0i64; sites * f];
        cell.b = vec![0i64; sites * f];
        cell.c = vec![0i64; sites * f];
        for t in 0..sites {
            let rt = &cell.read2[t * dw..(t + 1) * dw];
            affine(&self.theta[l.a..l.a + f * dw], reaches.a, dw, rt, Some(&self.theta[l.a_bias..l.a_bias + f]), MATERIAL_BITS, MATERIAL_BITS, &mut cell.a[t * f..(t + 1) * f])?;
            affine(&self.theta[l.b..l.b + f * dw], reaches.b, dw, rt, Some(&self.theta[l.b_bias..l.b_bias + f]), MATERIAL_BITS, MATERIAL_BITS, &mut cell.b[t * f..(t + 1) * f])?;
            for e in t * f..(t + 1) * f {
                cell.c[e] = fit64(release(cell.a[e] as i128 * cell.b[e] as i128, FACE_BITS))?;
            }
            affine(&self.theta[l.w..l.w + dw * f], reaches.w, f, &cell.c[t * f..(t + 1) * f], Some(&self.theta[l.w_bias..l.w_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut o)?;
            for (xv, ov) in x[t * dw..(t + 1) * dw].iter_mut().zip(&o) {
                *xv = fit64(*xv as i128 + *ov as i128)?;
            }
        }
        Ok(())
    }

    /// The region's forward: `K` ticks, then each unresolved site's face. `keep` holds each tick's
    /// temporaries for the reverse.
    fn pass(&self, region: &Region, keep: bool) -> Result<FieldPass> {
        self.admit_region(region)?;
        let d = &self.declaration;
        let dw = d.width;
        let reaches = self.reaches();
        let mut x = self.open(region);
        let mut out = FieldPass::default();
        for _ in 0..d.ticks {
            let mut cell = TickCell::default();
            self.tick(&mut x, &reaches, &mut cell)?;
            if keep {
                out.ticks.push(cell);
            }
        }
        let sites = region.classes.len();
        out.read = vec![0i32; sites * dw];
        out.scale = vec![0i128; sites];
        out.faces = vec![None; sites];
        let l = &self.layout;
        let mut z = vec![0i64; d.alphabet];
        for t in 0..sites {
            if !region.unresolved[t] {
                continue;
            }
            let (r, s) = ratio_to_power(&x[t * dw..(t + 1) * dw])?;
            affine(&self.theta[l.read..l.read + d.alphabet * dw], reaches.read, dw, &r, Some(&self.theta[l.read_bias..l.read_bias + d.alphabet]), MATERIAL_BITS, MATERIAL_BITS, &mut z)?;
            let peak = *z.iter().max().unwrap_or(&0);
            let masses: Vec<u128> = z.iter().map(|&zc| self.exponential.below_one(zc as i128 - peak as i128)).collect();
            let total = masses.iter().sum();
            out.faces[t] = Some(TowerFace { masses, total });
            out.read[t * dw..(t + 1) * dw].copy_from_slice(&r);
            out.scale[t] = s;
        }
        Ok(out)
    }

    /// Each unresolved site's face over the region (`None` at a resolved site).
    pub fn faces(&self, region: &Region) -> Result<Vec<Option<TowerFace>>> {
        Ok(self.pass(region, false)?.faces)
    }

    /// The region's code, `Σ −log₂ p̂_t(u_t)` over its unresolved sites, on `2^(−20)` bits, and
    /// the number of sites it read.
    pub fn code(&self, region: &Region) -> Result<(i64, usize)> {
        let faces = self.faces(region)?;
        let mut code = 0i64;
        let mut count = 0usize;
        for (face, &class) in faces.iter().zip(region.classes) {
            if let Some(face) = face {
                code += face.code(class);
                count += 1;
            }
        }
        Ok((code, count))
    }

    /// The exact reverse of [`Field::pass`] against each unresolved site's class, added into `g`
    /// on each family's natural grain (a face family's `Σ δz` on `2^(−24)`, a material family's
    /// `Σ δz x` on `2^(−40)`).
    fn reverse(&self, region: &Region, pass: &FieldPass, g: &mut [i128]) -> Result<()> {
        let d = &self.declaration;
        let (dw, m, n, f, heads, a) = (d.width, d.complex(), d.modes, d.contacts, d.heads, d.alphabet);
        let m2 = 2 * m;
        let span = 2 * n;
        let sites = region.classes.len();
        let l = &self.layout;
        let reaches = self.reaches();
        let beta = d.score_shift();
        let ln2 = ln2_face();
        if pass.ticks.len() != d.ticks {
            return refuse("a reverse reads a forward that held every tick");
        }
        // The face.
        let mut dx = vec![0i64; sites * dw];
        {
            let mut ys: Vec<Vec<i64>> = Vec::new();
            let mut xs: Vec<&[i32]> = Vec::new();
            for t in 0..sites {
                let Some(face) = &pass.faces[t] else { continue };
                let dz = covector(face, region.classes[t]);
                for (o, &dzo) in dz.iter().enumerate() {
                    g[l.read_bias + o] += dzo as i128;
                }
                let rt = &pass.read[t * dw..(t + 1) * dw];
                let mut dr = vec![0i64; dw];
                transposed(&self.theta[l.read..l.read + a * dw], reaches.read, dw, &dz, MATERIAL_BITS, &mut dr)?;
                let back = ratio_adjoint(rt, pass.scale[t], &dr)?;
                dx[t * dw..(t + 1) * dw].copy_from_slice(&back);
                ys.push(dz);
                xs.push(rt);
            }
            outer_sum(&mut g[l.read..l.read + a * dw], dw, &ys, &xs)?;
        }
        for cell in pass.ticks.iter().rev() {
            // The pair contact: x_out = x_mid + W_c c + b_c.
            let dxs: Vec<&[i64]> = dx.chunks_exact(dw).collect();
            for dxt in &dxs {
                for (i, &v) in dxt.iter().enumerate() {
                    g[l.w_bias + i] += v as i128;
                }
            }
            let cs: Vec<&[i64]> = cell.c.chunks_exact(f).collect();
            outer_sum(&mut g[l.w..l.w + dw * f], f, &dxs, &cs)?;
            let mut da = vec![0i64; sites * f];
            let mut db = vec![0i64; sites * f];
            let mut dc = vec![0i64; f];
            for t in 0..sites {
                transposed(&self.theta[l.w..l.w + dw * f], reaches.w, f, dxs[t], MATERIAL_BITS, &mut dc)?;
                for e in 0..f {
                    let at = t * f + e;
                    da[at] = fit64(release(dc[e] as i128 * cell.b[at] as i128, FACE_BITS))?;
                    db[at] = fit64(release(dc[e] as i128 * cell.a[at] as i128, FACE_BITS))?;
                }
            }
            let das: Vec<&[i64]> = da.chunks_exact(f).collect();
            let dbs: Vec<&[i64]> = db.chunks_exact(f).collect();
            let r2s: Vec<&[i32]> = cell.read2.chunks_exact(dw).collect();
            outer_sum(&mut g[l.a..l.a + f * dw], dw, &das, &r2s)?;
            outer_sum(&mut g[l.b..l.b + f * dw], dw, &dbs, &r2s)?;
            for t in 0..sites {
                for e in 0..f {
                    g[l.a_bias + e] += das[t][e] as i128;
                    g[l.b_bias + e] += dbs[t][e] as i128;
                }
            }
            let mut dmid = vec![0i64; sites * dw];
            let mut ra = vec![0i64; dw];
            let mut rb = vec![0i64; dw];
            for t in 0..sites {
                transposed(&self.theta[l.a..l.a + f * dw], reaches.a, dw, das[t], MATERIAL_BITS, &mut ra)?;
                transposed(&self.theta[l.b..l.b + f * dw], reaches.b, dw, dbs[t], MATERIAL_BITS, &mut rb)?;
                let dr: Vec<i64> = ra.iter().zip(&rb).map(|(&p, &q)| p + q).collect();
                let back = ratio_adjoint(r2s[t], cell.scale2[t], &dr)?;
                for i in 0..dw {
                    dmid[t * dw + i] = fit64(dx[t * dw + i] as i128 + back[i] as i128)?;
                }
            }
            // The current: x_mid = x_in + O y + b_o.
            let dms: Vec<&[i64]> = dmid.chunks_exact(dw).collect();
            for dmt in &dms {
                for (i, &v) in dmt.iter().enumerate() {
                    g[l.out_bias + i] += v as i128;
                }
            }
            let ys: Vec<&[i64]> = cell.y.chunks_exact(m2).collect();
            outer_sum(&mut g[l.out..l.out + dw * m2], m2, &dms, &ys)?;
            let mut dy = vec![0i64; sites * m2];
            for t in 0..sites {
                transposed(&self.theta[l.out..l.out + dw * m2], reaches.out, m2, dms[t], MATERIAL_BITS, &mut dy[t * m2..(t + 1) * m2])?;
            }
            // The weights and the contact, head by head.
            let mut dq = vec![0i64; sites * m2];
            let mut dk = vec![0i64; sites * m2];
            let mut dv = vec![0i64; sites * m2];
            let mut dyh = vec![0i64; sites * span];
            let mut ds = vec![0i128; sites * sites];
            for h in 0..heads {
                for t in 0..sites {
                    for r in 0..span {
                        let c = h * n + r % n;
                        dyh[t * span + r] = dy[t * m2 + if r < n { c } else { m + c }];
                    }
                }
                let p = &cell.p[h * sites * sites..(h + 1) * sites * sites];
                let vh = &cell.v[h * sites * span..(h + 1) * sites * span];
                let qh = &cell.q[h * sites * span..(h + 1) * sites * span];
                let kh = &cell.k[h * sites * span..(h + 1) * sites * span];
                // δv_j = Σ_i p_ij δy_i.
                for j in 0..sites {
                    for r in 0..span {
                        let mut sum = 0i128;
                        for i in 0..sites {
                            sum += p[i * sites + j] as i128 * dyh[i * span + r] as i128;
                        }
                        let c = h * n + r % n;
                        dv[j * m2 + if r < n { c } else { m + c }] = fit64(release(sum, SHARE_BITS))?;
                    }
                }
                // δz_ij = ln 2 · p_ij (δp_ij − Σ_k p_ik δp_ik), δp_ij = ⟨δy_i, v_j⟩ on 2^(−40).
                for i in 0..sites {
                    let dyi = &dyh[i * span..(i + 1) * span];
                    let dp: Vec<i128> = (0..sites).map(|j| dyi.iter().zip(&vh[j * span..(j + 1) * span]).map(|(&a, &b)| a as i128 * b as i128).sum()).collect();
                    let row = &p[i * sites..(i + 1) * sites];
                    let mean = release(row.iter().zip(&dp).map(|(&pj, &dpj)| pj as i128 * dpj).sum(), SHARE_BITS);
                    for j in 0..sites {
                        let dz = release(ln2 * release(row[j] as i128 * (dp[j] - mean), SHARE_BITS), SHARE_BITS);
                        ds[i * sites + j] = release(dz, beta);
                    }
                }
                // δq̃_i = Σ_j δs_ij k̃_j,   δk̃_j = Σ_i δs_ij q̃_i, released from 2^(−56) to 2^(−24).
                let back = CONTACT_BITS + FACE_BITS - super::COVECTOR_BITS;
                for i in 0..sites {
                    for r in 0..span {
                        let mut sq = 0i128;
                        let mut sk = 0i128;
                        for j in 0..sites {
                            sq += ds[i * sites + j] * kh[j * span + r] as i128;
                            sk += ds[j * sites + i] * qh[j * span + r] as i128;
                        }
                        let (sq, sk) = (release(sq, back), release(sk, back));
                        // Held in the framed chart until the frame is undone below.
                        let c = h * n + r % n;
                        let slot = if r < n { c } else { m + c };
                        dq[i * m2 + slot] = fit64(sq)?;
                        dk[i * m2 + slot] = fit64(sk)?;
                    }
                }
            }
            // Undo the frame: δq = conj(U) δq̃.
            for t in 0..sites {
                for c in 0..m {
                    let (ur, ui) = self.frame(t, c % n);
                    let (ur, ui) = (ur as i128, ui as i128);
                    for chart in [&mut dq, &mut dk] {
                        let (gr, gi) = (chart[t * m2 + c] as i128, chart[t * m2 + m + c] as i128);
                        chart[t * m2 + c] = fit64(release(ur * gr + ui * gi, MOVE_BITS))?;
                        chart[t * m2 + m + c] = fit64(release(ur * gi - ui * gr, MOVE_BITS))?;
                    }
                }
            }
            let reads: Vec<&[i32]> = cell.read.chunks_exact(dw).collect();
            let mut dr_all = vec![0i64; sites * dw];
            for (w, bias, reach_w, dfam) in [(l.q, l.q_bias, reaches.q, &dq), (l.k, l.k_bias, reaches.k, &dk), (l.v, l.v_bias, reaches.v, &dv)] {
                let rows: Vec<&[i64]> = dfam.chunks_exact(m2).collect();
                outer_sum(&mut g[w..w + m2 * dw], dw, &rows, &reads)?;
                let mut back = vec![0i64; dw];
                for t in 0..sites {
                    for (e, &v) in rows[t].iter().enumerate() {
                        g[bias + e] += v as i128;
                    }
                    transposed(&self.theta[w..w + m2 * dw], reach_w, dw, rows[t], MATERIAL_BITS, &mut back)?;
                    for i in 0..dw {
                        dr_all[t * dw + i] = fit64(dr_all[t * dw + i] as i128 + back[i] as i128)?;
                    }
                }
            }
            for t in 0..sites {
                let back = ratio_adjoint(reads[t], cell.scale[t], &dr_all[t * dw..(t + 1) * dw])?;
                for i in 0..dw {
                    dx[t * dw + i] = fit64(dmid[t * dw + i] as i128 + back[i] as i128)?;
                }
            }
        }
        // The opening: each site's row of the encoding.
        for t in 0..sites {
            let row = if region.unresolved[t] { a } else { region.classes[t] };
            let start = l.enc + row * dw;
            for i in 0..dw {
                g[start + i] += dx[t * dw + i] as i128;
            }
        }
        Ok(())
    }

    /// Each region's faces and the covector over the regions, summed in any order to the same bits.
    pub fn read_and_return(&self, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
        let len = self.layout.len;
        let (mut faces, g) = regions
            .par_iter()
            .enumerate()
            .try_fold(
                || (Vec::new(), vec![0i128; len]),
                |(mut faces, mut g), (n, region)| -> Result<_> {
                    let pass = self.pass(region, true)?;
                    self.reverse(region, &pass, &mut g)?;
                    faces.push((n, pass.faces));
                    Ok((faces, g))
                },
            )
            .try_reduce(
                || (Vec::new(), vec![0i128; len]),
                |(mut fa, mut ga), (fb, gb)| {
                    fa.extend(fb);
                    for (x, y) in ga.iter_mut().zip(gb) {
                        *x += y;
                    }
                    Ok((fa, ga))
                },
            )?;
        faces.sort_by_key(|(n, _)| *n);
        Ok((faces.into_iter().map(|(_, f)| f).collect(), g))
    }

    /// Each region's faces, read in parallel.
    pub fn read_faces(&self, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>> {
        regions.par_iter().map(|r| self.faces(r)).collect()
    }

    /// [`Field::release`] on a declared realization.
    pub fn release_realized(&self, question: &[usize], answer: usize, sweeps: usize, void: usize, realization: &mut dyn FieldRealization) -> Result<Vec<usize>> {
        self.release_with(question, answer, sweeps, void, &mut |region| Ok(realization.read_faces(self, &[region])?.remove(0)))
    }

    /// **The release by refinement** ([definition; agent-inferred, November 1]): the region of the
    /// `question`'s resolved sites and `answer` unresolved sites is refined over `sweeps` sweeps.
    /// Sweep `s` reads every unresolved site's face and releases the `⌈r/(S − s)⌉` most locked
    /// (the top class's share of its face, compared by exact cross products; a tie takes the
    /// earlier site) at their top class (a tie takes the lower class); every site after the earliest
    /// released `void` leaves the region (the answer has ended). Returns the answer's classes, ending
    /// at its void when one was released.
    pub fn release(&self, question: &[usize], answer: usize, sweeps: usize, void: usize) -> Result<Vec<usize>> {
        self.release_with(question, answer, sweeps, void, &mut |region| self.faces(&region))
    }

    fn release_with(&self, question: &[usize], answer: usize, sweeps: usize, void: usize, read: &mut dyn FnMut(Region) -> Result<Vec<Option<TowerFace>>>) -> Result<Vec<usize>> {
        if sweeps == 0 || answer == 0 || void >= self.declaration.alphabet {
            return refuse("a release needs a sweep, an answer site and a void class in the alphabet");
        }
        let start = question.len();
        let mut classes: Vec<usize> = question.iter().copied().chain(std::iter::repeat_n(void, answer)).collect();
        let mut unresolved: Vec<bool> = std::iter::repeat_n(false, start).chain(std::iter::repeat_n(true, answer)).collect();
        for s in 0..sweeps {
            let remaining = unresolved.iter().filter(|&&u| u).count();
            if remaining == 0 {
                break;
            }
            let faces = read(Region { classes: &classes, unresolved: &unresolved })?;
            let mut open: Vec<(usize, usize, u128, u128)> = Vec::with_capacity(remaining);
            for (t, face) in faces.iter().enumerate() {
                let Some(face) = face else { continue };
                let (top, &mass) = face.masses.iter().enumerate().fold((0usize, &0u128), |best, (c, mass)| if *mass > *best.1 { (c, mass) } else { best });
                open.push((t, top, mass, face.total));
            }
            // Most locked first: a larger share m/T first, the earlier site on an exact tie.
            open.sort_by(|x, y| {
                let left = BigUint::from(y.2) * BigUint::from(x.3);
                let right = BigUint::from(x.2) * BigUint::from(y.3);
                left.cmp(&right).then(x.0.cmp(&y.0))
            });
            let take = remaining.div_ceil(sweeps - s);
            for &(t, top, _, _) in open.iter().take(take) {
                classes[t] = top;
                unresolved[t] = false;
            }
            // The answer ends at its earliest released void, and the region with it: the sites past
            // it leave, so the next sweep reads a region one site past its answer, as a training
            // region is read (agent-inferred, November 1: a release opened at the longest training
            // answer would otherwise carry its void tail through every sweep).
            if let Some(end) = (start..classes.len()).find(|&t| !unresolved[t] && classes[t] == void) {
                classes.truncate(end + 1);
                unresolved.truncate(end + 1);
            }
        }
        Ok(classes[start..].to_vec())
    }

    /// The field as text: its head line, then its material on one line.
    pub fn to_text(&self) -> String {
        let theta: Vec<String> = self.theta.iter().map(i32::to_string).collect();
        format!("{}\n{}\n", self.declaration.to_text(), theta.join(" "))
    }

    pub fn from_text(text: &str) -> Result<Self> {
        let mut lines = text.lines();
        let d = FieldDeclaration::from_text(lines.next().unwrap_or(""))?;
        let theta = read_numbers::<i32>(lines.next())?;
        if theta.len() != FieldLayout::new(&d).len {
            return refuse("a field's material that is not its declaration's length");
        }
        Ok(Self::with_theta(d, theta))
    }
}

/// The founding's scale of the charts and pair drives at width `D`, `√(3/D)` as a ratio of square
/// roots on `2^(−16)`.
fn chart_scale(width: usize) -> (u128, u128) {
    ((3u128 << 32).isqrt(), ((width as u128) << 32).isqrt())
}

impl Field {
    /// The key draws a growth by `factor` reads, four bytes a draw: `f − 1` a part of each row
    /// copy's entry of every family the founding opens away from zero (the charts and the pair
    /// drives).
    pub fn growth_draws(&self, factor: usize) -> usize {
        let d = &self.declaration;
        factor * factor.saturating_sub(1) * d.width * (3 * 2 * d.complex() + 2 * d.contacts)
    }

    /// [definition; agent-inferred, November 1] **The field widened by `factor`**, by the tower's
    /// growth law (`hnn::tower::growth`): every face coordinate gets `f` equal copies (the encoding
    /// and every bias repeated), every head is repeated (one head a copy, its modes and frames
    /// kept, so `M' = fM` with copy `b` of mode `c` at `bM + c`), every contact repeated, and every
    /// matrix entry split over its `f` column copies into parts that sum to it, its rows repeated
    /// (the readout's kept). A part's zero-sum difference is the grown founding's draw at its
    /// scale (`√(3/fD)` for the charts and pair drives, read from `keys` four bytes a draw); the
    /// families founded at zero (the returns and the readout) split evenly. Every sum the forward
    /// forms is then the old sum, so the grown field reads the old faces exactly, and the copies
    /// part under learning.
    ///
    /// Returns the grown field and, for each grown entry, the old entry it carries and whether its
    /// covector is divided among the copies (every family but the readout's).
    pub fn grown(&self, factor: usize, keys: &[u8]) -> Result<(Self, Vec<(usize, bool)>)> {
        if factor < 2 {
            return refuse("a growth makes at least two copies");
        }
        let old = self.declaration;
        let d = old.grown(factor)?;
        let layout = FieldLayout::new(&d);
        let (ol, f) = (&self.layout, factor);
        let (dw, m, fc, a) = (old.width, old.complex(), old.contacts, old.alphabet);
        let (dw2, m2g) = (d.width, d.complex());
        let mut new = vec![0i32; layout.len];
        let mut from = vec![(0usize, true); layout.len];
        let mut cursor = 0usize;
        let mut draw = |scale: Option<(u128, u128)>| -> Result<i128> {
            let Some((num, den)) = scale else { return Ok(0) };
            let word = keys.get(cursor..cursor + 4).ok_or(TowerError::Refused("fewer key bytes than the growth draws"))?;
            cursor += 4;
            let k = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i128;
            Ok((k * ((num << MATERIAL_BITS) / den) as i128) >> 31)
        };
        // A matrix of `rows × cols` (old), its rows mapped by `row_of(b, r)` over `row_copies`
        // copies and each column's `f` parts placed at `col_of(c, j)` in a row of `new_cols`.
        let mut split = |old_at: usize, new_at: usize, rows: usize, cols: usize, row_copies: usize, row_of: &dyn Fn(usize, usize) -> usize, new_cols: usize, col_of: &dyn Fn(usize, usize) -> usize, scale: Option<(u128, u128)>, divided: bool| -> Result<()> {
            for b in 0..row_copies {
                for r in 0..rows {
                    let nr = row_of(b, r);
                    for j in 0..cols {
                        let v = self.theta[old_at + r * cols + j] as i128;
                        let (q, rem) = (v.div_euclid(f as i128), v.rem_euclid(f as i128));
                        let mut spent = 0i128;
                        for c in 0..f {
                            let delta = if c + 1 < f { draw(scale)? } else { -spent };
                            spent += delta;
                            let at = new_at + nr * new_cols + col_of(c, j);
                            new[at] = fit32(q + i128::from((c as i128) < rem) + delta, "a grown part outgrew its 32-bit carrier")?;
                            from[at] = (old_at + r * cols + j, divided);
                        }
                    }
                }
            }
            Ok(())
        };
        let scale = Some(chart_scale(dw2));
        // Index maps: a face coordinate's copy `c` at `cD + j`; a complex chart row's (real or
        // imaginary part, copy `b`, mode `c`) at `part·M' + bM + c`; a contact's at `bf + e`.
        let face = |c: usize, j: usize| c * dw + j;
        let chart_row = |b: usize, r: usize| (r / m) * m2g + b * m + r % m;
        let contact = |c: usize, e: usize| c * fc + e;
        let kept = |_: usize, r: usize| r;
        split(ol.q, layout.q, 2 * m, dw, f, &chart_row, dw2, &face, scale, true)?;
        split(ol.k, layout.k, 2 * m, dw, f, &chart_row, dw2, &face, scale, true)?;
        split(ol.v, layout.v, 2 * m, dw, f, &chart_row, dw2, &face, scale, true)?;
        split(ol.out, layout.out, dw, 2 * m, f, &face, 2 * m2g, &chart_row, None, true)?;
        split(ol.a, layout.a, fc, dw, f, &contact, dw2, &face, scale, true)?;
        split(ol.b, layout.b, fc, dw, f, &contact, dw2, &face, scale, true)?;
        split(ol.w, layout.w, dw, fc, f, &face, f * fc, &contact, None, true)?;
        split(ol.read, layout.read, a, dw, 1, &kept, dw2, &face, None, false)?;
        // Vector families: each entry's copies.
        let mut repeat = |old_at: usize, new_at: usize, len: usize, copies: usize, index: &dyn Fn(usize, usize) -> usize, divided: bool| {
            for c in 0..copies {
                for i in 0..len {
                    new[new_at + index(c, i)] = self.theta[old_at + i];
                    from[new_at + index(c, i)] = (old_at + i, divided);
                }
            }
        };
        for row in 0..=a {
            repeat(ol.enc + row * dw, layout.enc + row * dw2, dw, f, &face, true);
        }
        repeat(ol.q_bias, layout.q_bias, 2 * m, f, &chart_row, true);
        repeat(ol.k_bias, layout.k_bias, 2 * m, f, &chart_row, true);
        repeat(ol.v_bias, layout.v_bias, 2 * m, f, &chart_row, true);
        repeat(ol.out_bias, layout.out_bias, dw, f, &face, true);
        repeat(ol.a_bias, layout.a_bias, fc, f, &contact, true);
        repeat(ol.b_bias, layout.b_bias, fc, f, &contact, true);
        repeat(ol.w_bias, layout.w_bias, dw, f, &face, true);
        repeat(ol.read_bias, layout.read_bias, a, 1, &kept, false);
        Ok((Self::with_theta(d, new), from))
    }
}

fn read_numbers<T: std::str::FromStr>(line: Option<&str>) -> Result<Vec<T>> {
    let line = line.ok_or(TowerError::Refused("a field's text ended before its material"))?;
    if line.is_empty() {
        return Ok(Vec::new());
    }
    line.split(' ').map(|w| w.parse::<T>().map_err(|_| TowerError::Refused("a field's material that is not a number"))).collect()
}

/// [definition; agent-inferred, November 1] **A realization of the field's read and return**: a
/// region's faces and the covector over a section's regions, bit for bit the host's
/// ([`HostField`]). The card's realization is one such; a realization that cannot read a region
/// refuses, never substitutes.
pub trait FieldRealization {
    fn read_and_return(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)>;
    fn read_faces(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>>;
}

/// The host's realization: the regions on the host's cores, each region's forward and reverse on
/// one core.
#[derive(Clone, Copy, Debug, Default)]
pub struct HostField;

impl FieldRealization for HostField {
    fn read_and_return(&mut self, field: &Field, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
        field.read_and_return(regions)
    }
    fn read_faces(&mut self, field: &Field, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>> {
        field.read_faces(regions)
    }
}

/// A section's receipt: its unresolved sites, its code before and after (on `2^(−20)` bits), the
/// halvings the certificate took, and whether a step was deposited.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FieldReceipt {
    pub sites: usize,
    pub code_before: i64,
    pub code_after: i64,
    pub halvings: u32,
    pub deposited: bool,
}

/// [definition; agent-inferred, November 1] **The field's learner**: the field, the covector's two
/// moments and the step's rate `2^(−k)`. The deposit is the tower's ([`super::TowerLearner`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldLearner {
    pub field: Field,
    first: Vec<i128>,
    second: Vec<i128>,
    opened: bool,
    pub rate_bits: u32,
    /// The founding key bytes read so far: the founding's, then each growth's.
    pub drawn: usize,
}

impl FieldLearner {
    /// The learner of a field founded on its declared key stream (the founding read
    /// [`FieldDeclaration::founding_draws`] draws).
    pub fn new(field: Field, rate_bits: u32) -> Self {
        let len = field.theta.len();
        let drawn = 4 * field.declaration.founding_draws();
        Self { field, first: vec![0; len], second: vec![0; len], opened: false, rate_bits, drawn }
    }

    /// [definition; agent-inferred, November 1] **The learner widened** ([`Field::grown`]), its
    /// differences read from the founding key stream past every draw read before, and its moments
    /// lifted as the tower's are: split evenly, each grown coordinate's covector at the growth
    /// point is the old one divided among its `f` copies and the readout's the old one, so a grown
    /// coordinate carries `m/f` and `v/f²`, the readout `m` and `v`, and opens on the old
    /// normalized step.
    pub fn widened(&self, factor: usize, keys: &[u8]) -> Result<Self> {
        let rest = keys.get(self.drawn..).ok_or(TowerError::Refused("fewer key bytes than the growth draws"))?;
        let (field, from) = self.field.grown(factor, rest)?;
        let (f, f2) = (factor as i128, (factor * factor) as i128);
        let first = from.iter().map(|&(i, divided)| if divided { div_nearest(self.first[i], f) } else { self.first[i] }).collect();
        let second = from.iter().map(|&(i, divided)| if divided { div_nearest(self.second[i], f2) } else { self.second[i] }).collect();
        let drawn = self.drawn + 4 * self.field.growth_draws(factor);
        Ok(Self { field, first, second, opened: self.opened, rate_bits: self.rate_bits, drawn })
    }

    /// One section: its regions read and returned on the standing material, the moments moved, and
    /// the step deposited where the regions reread under it code strictly fewer bits (the
    /// certificate halves it until then, or until it moves nothing).
    pub fn section(&mut self, regions: &[Region]) -> Result<FieldReceipt> {
        self.section_realized(regions, &mut HostField)
    }

    /// [`FieldLearner::section`] on a declared realization of the field's read and return; the
    /// moments, the step and the certificate's decision stay on the host.
    pub fn section_realized(&mut self, regions: &[Region], realization: &mut dyn FieldRealization) -> Result<FieldReceipt> {
        let (faces, mut g) = realization.read_and_return(&self.field, regions)?;
        let compared = |faces: &[Vec<Option<TowerFace>>]| -> Vec<(u128, u128)> {
            faces.iter().zip(regions).flat_map(|(f, r)| f.iter().zip(r.classes).filter_map(|(face, &c)| face.as_ref().map(|face| (face.masses[c], face.total)))).collect()
        };
        let code_of = |pairs: &[(u128, u128)]| -> i64 { pairs.par_iter().map(|&(m, t)| face_code(m, t)).sum() };
        let faces_old = compared(&faces);
        let code_before = code_of(&faces_old);
        let sites = faces_old.len();
        if sites == 0 {
            return refuse("a section with no unresolved site");
        }
        for &(start, len, grain) in self.field.families() {
            for v in &mut g[start..start + len] {
                *v = on_step_grain(grain, *v);
            }
        }
        if !self.opened {
            self.first.clone_from(&g);
            self.second = g.iter().map(|v| v.checked_mul(*v).ok_or(TowerError::Refused("a covector's square outgrew its 128-bit carrier"))).collect::<Result<_>>()?;
            self.opened = true;
        } else {
            for ((m, v), gv) in self.first.iter_mut().zip(self.second.iter_mut()).zip(&g) {
                let square = gv.checked_mul(*gv).ok_or(TowerError::Refused("a covector's square outgrew its 128-bit carrier"))?;
                *m = toward(*m, *gv, FIRST_RATE);
                *v = toward(*v, square, SECOND_RATE);
            }
        }
        let mut step = vec![0i128; g.len()];
        for &(start, len, grain) in self.field.families() {
            for i in start..start + len {
                step[i] = deposit_step(self.first[i], self.second[i], grain, self.rate_bits);
            }
        }
        let mut halvings = 0u32;
        loop {
            let mut candidate = self.field.clone();
            let mut moved = false;
            for (slot, &q) in candidate.theta.iter_mut().zip(&step) {
                let s = release(q, halvings);
                if s != 0 {
                    moved = true;
                    *slot = fit32(*slot as i128 - s, "a deposited parameter outgrew its 32-bit carrier")?;
                }
            }
            if !moved {
                return Ok(FieldReceipt { sites, code_before, code_after: code_before, halvings, deposited: false });
            }
            let reread = realization.read_faces(&candidate, regions)?;
            let faces_new = compared(&reread);
            if fewer_bits(&faces_old, &faces_new) {
                let code_after = code_of(&faces_new);
                self.field = candidate;
                return Ok(FieldReceipt { sites, code_before, code_after, halvings, deposited: true });
            }
            halvings += 1;
        }
    }

    /// The learner as text: its head line, the field, then each moment on one line.
    pub fn to_text(&self) -> String {
        let join = |v: &[i128]| v.iter().map(i128::to_string).collect::<Vec<_>>().join(" ");
        format!("hnn-field-learner-v1 {} {} {}\n{}{}\n{}\n", self.rate_bits, u8::from(self.opened), self.drawn, self.field.to_text(), join(&self.first), join(&self.second))
    }

    pub fn from_text(text: &str) -> Result<Self> {
        let mut lines = text.lines();
        let head: Vec<&str> = lines.next().unwrap_or("").split(' ').collect();
        if head.len() != 4 || head[0] != "hnn-field-learner-v1" {
            return refuse("a learner's head line that is not hnn-field-learner-v1");
        }
        let rate_bits = head[1].parse::<u32>().map_err(|_| TowerError::Refused("a learner's rate that is not a count"))?;
        let opened = match head[2] {
            "0" => false,
            "1" => true,
            _ => return refuse("a learner's opening that is neither 0 nor 1"),
        };
        let drawn = head[3].parse::<usize>().map_err(|_| TowerError::Refused("a learner's drawn keys that are not a count"))?;
        let field_text = format!("{}\n{}\n", lines.next().unwrap_or(""), lines.next().unwrap_or(""));
        let field = Field::from_text(&field_text)?;
        let first = read_numbers::<i128>(lines.next())?;
        let second = read_numbers::<i128>(lines.next())?;
        if first.len() != field.theta.len() || second.len() != field.theta.len() {
            return refuse("a learner's moments that are not its field's length");
        }
        Ok(Self { field, first, second, opened, rate_bits, drawn })
    }
}

#[cfg(test)]
mod tests;
