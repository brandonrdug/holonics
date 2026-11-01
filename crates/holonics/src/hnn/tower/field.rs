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
//! carries the ring phasor `U_(t,m) = e^(2πi (t mod n_m)/n_m)`, `n_m` a closure of the solenoid's
//! dyadic or triadic tower ([`ring_periods`]: each ring reads the finer ring's residue and its
//! whole winding, and the top rings span the region), or `U = 1` (the still modes, which read
//! content without place). One constitution `F_Θ` is iterated `K` ticks, `x^(k+1) = F_Θ(x^k)`:
//!
//! ```text
//! open       x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1)),   u = ∗ where a site is unresolved
//! chart      r̂_t = x_t / ‖x_t‖_rms,   q_t = Q r̂_t + b_q,   k_t = K r̂_t + b_k,   v_t = V r̂_t + b_v
//! frame      q̃_t = U_t ⊙ q_t,   k̃_t = U_t ⊙ k_t,   ṽ_t = U_t ⊙ v_t       complex modes, by head
//! contact    z_ij = 2^(−β) Σ_(m∈h) Re(conj(q̃_im) k̃_jm)                   every pair of sites, both ways
//! weights    e_ij = 2^(z_ij − max_j z_ij)                                 the Gibbs face, in bits
//! current    y_i = conj(U_i) ⊙ Σ_j e_ij ṽ_j / Σ_j e_ij,   x ← x + O y + b_o
//! pair       r̂'_t = x_t / ‖x_t‖_rms,   a = W_a r̂' + b_a,   b = W_b r̂' + b_b,   x ← x + W_c (a ⊙ b) + b_c
//! face       z_t = R r̂(x^K_t) + c,   p̂_t(a) = 2^(z_a) / Σ_b 2^(z_b)        at the unresolved sites
//! ```
//!
//! [definition; agent-inferred, November 1] **The opening carries the site's strand contacts.** A
//! site is a ring of the strand, joined to the sites before and after it by pair contacts, so its
//! opening face is its own class's row with its two neighbours' rows of the contact encodings
//! `E₋` and `E₊` (founded at zero: the founded field opens as before and the contacts are learned).
//! The face of a site is then its word, the address the navigator reads it by: two sites whose
//! neighbours agree meet through their charts in one tick, so a site can find, anywhere in the
//! region, the site whose word continues its own, and gather what stands there. Why (the sixth
//! reading, November 1): after thirteen laps the held answers coded within 0.01 bits a digit
//! alike beside their own question and beside another problem's, so the field read nothing of
//! the question; with only its own class at the opening, a site's word reaches its charts only
//! through a first tick's contact with its neighbours, and finding a site by its word is then a
//! composition of two learned contacts, which thirteen laps did not form.
//!
//! The pairing `Re(conj(q̃_i) k̃_j) = Re(conj(q_i) U_i^* U_j k_j)` turns mode `m` by
//! `2π (j − i)/n_m`: a turned mode reads the relative place modulo its ring, a still mode reads the
//! contents alone, at any distance. The current is the phase-carried moment
//! `y_i = Σ_j p_ij U_i^* U_j v_j`: what a site gathers carries where each source stood relative
//! to it, so place is content after the read, not only the choice of what is read. There is no clock between sites and no carry across problems:
//! the region is the whole terrain the constitution meets, so the transferred response a scan's
//! carried state would owe is absent by construction.
//!
//! **Learning.** The comparison is completion: any subset of the region is unresolved, its targets
//! the classes that arrived there, and the code is `Σ −log₂ p̂_t(u_t)` over the unresolved sites.
//! The covector `p̂ − q` returns exactly through the `K` ticks (the operands that produced each
//! carrier, held from the forward). The deposit is the tower's: the covector's two moments, the
//! step `m/(√v + 2^(−32))` at `2^(−k)`, certified on the section's own regions by an exact
//! comparison of the products of their faces, halved until it is certified or moves nothing; then
//! held and read on the next section's regions, which it was not fit on, and halved again or
//! refused where it codes them higher (the tower's acceptance 77, [`FieldLearner`]).
//!
//! **Release.** The answer's sites open unresolved and the field is refined over at most `S`
//! sweeps: each sweep reads every unresolved site's face and releases every site the field
//! resolves (its top class outweighs every other together); where it resolves none, the face is
//! read again with the question's sites unresolved and the one site whose top class carries the
//! most news ([`by_news`]) is released. The void is the answer's boundary, one nested variable
//! (a void at `t` implies the void past `t`): its extent is read once, at the opening, where the
//! earliest site whose void the field resolves is released and the sites past it leave the region;
//! after the opening the void is released only at the answer's first open site, every answer site
//! before it released, and it ends the answer. The released sites are
//! present terrain for the next sweep. A class is never spoken in order. Every sweep releases a
//! site of every open problem, so `S` at the answer's open sites lets every release end; the
//! exterior bounds its time ([`ReleaseSweep`]).
//!
//! **Exact integers, grains declared.** Faces, charts, framed charts and currents on `2^(−16)`;
//! material on `2^(−24)`; frames on `2^(−30)`; Gibbs weights on `2^(−40)` relative to their row's
//! peak, the numerators summed whole over the row's one denominator; covectors on `2^(−24)`, the
//! contact's on `2^(−40)`. Every product's
//! remainder below its grain is released to the nearest numerator and every sum is an integer
//! sum, so the sites, heads and regions summed in any order give the same bits: the host and any
//! partition of the card agree bit for bit.
//!
//! [definition] The computational object is the helical pair interaction: every pair of sites
//! meets through its framed modes' contact `Re(conj(q̃_i) k̃_j)`, the ring phasors carry the helix
//! (a tower's residues are each finer ring's residue with its whole winding), and the pair contact `a ⊙ b` is the
//! bilinear contact between two reads of one site. Of the winding guide's six general objects it
//! touches the **helix** (the ring phasors), the **pair** (site contacts and the bilinear
//! contact), **faces and placement** (the Gibbs face, the release by lock) and the **tube** (the
//! `K` ticks of one constitution); the cell holonomy and the tower thread stay attached through the
//! tower, which this owner does not replace.

use super::{affine, covector, deposit_step, div_nearest, exp_series, face_code, fewer_bits, fit32, fit64, half_turn, on_step_grain, outer_sum, ratio_adjoint, ratio_to_power, reach, refuse, release, toward, transposed, Result, TowerError, TowerFace, FACE_BITS, FIRST_RATE, MATERIAL_BITS, MOVE_BITS, SECOND_RATE};
use crate::hnn::keyed_modes::{ln2_face, Exponential};
use rayon::prelude::*;

/// The Gibbs weights' grain relative to their row's peak, `e_ij` on `2^(−40)` (the exponential's
/// `2^(−62)` face released; a pair below `2^(−40)` of its row's peak weighs nothing).
const WEIGHT_BITS: u32 = 40;
/// The reverse's per-site return of a row's denominator carries `2^(−30)` past the covector's
/// grain (the precision the first draft's shares carried), so the sum over sites releases once.
const SHARE_BITS: u32 = 30;
/// The exponential's face is on `2^(−62)`; the weights keep `2^(−40)` of it.
const WEIGHT_BITS_FROM: u32 = 62 - WEIGHT_BITS;
/// The contact covector's grain, `2^(−40)` (`δz` and `δs`).
const CONTACT_BITS: u32 = 40;
/// The release's order key, `p̂(top)` times the news in bits, on `2^(−40)`: the code's `2^(−20)`
/// bits carried `2^(−20)` further by the share.
const NEWS_BITS: u32 = 20;

/// [definition; agent-inferred, November 1] **The field's declared law**: an alphabet of `A`
/// classes (the face's; the encoding carries one more row, the unresolved operand), a face width
/// `D`, `H` heads of `n` complex modes each (the first `still` of every head unframed, the rest on
/// the solenoid's rings, [`ring_periods`]), `f` pair contacts and `K` ticks of the one
/// constitution; `frames`, the founding's heads, whose ring sets every grown head copies; and
/// `reach`, the most sites a region may span (the terrain's extent, read from the passages the
/// field will meet), which the rings' coarsest closures cover.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldDeclaration {
    pub alphabet: usize,
    pub width: usize,
    pub heads: usize,
    pub modes: usize,
    pub still: usize,
    pub contacts: usize,
    pub ticks: usize,
    pub frames: usize,
    pub reach: usize,
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

    /// The key draws a growth by `factor` reads ([`Field::growth_draws`]).
    pub fn growth_draws(&self, factor: usize) -> usize {
        factor * factor.saturating_sub(1) * self.width * (3 * 2 * self.complex() + 2 * self.contacts)
    }

    /// The declaration grown by `factor`: width, heads and contacts (a head's modes, its ring set,
    /// the ring sets and the reach are kept).
    pub fn grown(&self, factor: usize) -> Result<Self> {
        let grow = |v: usize| v.checked_mul(factor).ok_or(TowerError::Refused("a grown extent outgrew its carrier"));
        Ok(Self { width: grow(self.width)?, heads: grow(self.heads)?, contacts: grow(self.contacts)?, ..*self })
    }

    /// The turned slots: `frames · (n − still)`, slot `(l − still) · frames + g` the ring of local
    /// mode `l` in every head of ring set `g`.
    pub fn turned_slots(&self) -> usize {
        self.frames * (self.modes - self.still)
    }

    fn admit(&self) -> Result<()> {
        if self.alphabet < 2 || self.width == 0 || self.heads == 0 || self.modes == 0 || self.still > self.modes || self.contacts == 0 || self.ticks == 0 {
            return refuse("a field needs two classes, a nonempty width, heads, modes, contacts and ticks, and no more still modes than a head has");
        }
        if self.frames == 0 || self.heads % self.frames != 0 || self.reach == 0 {
            return refuse("a field's ring sets divide its heads and its reach spans a site");
        }
        Ok(())
    }

    fn to_text(self) -> String {
        format!("hnn-field-v2 {} {} {} {} {} {} {} {} {}", self.alphabet, self.width, self.heads, self.modes, self.still, self.contacts, self.ticks, self.frames, self.reach)
    }

    fn from_text(line: &str) -> Result<Self> {
        let words: Vec<&str> = line.split(' ').collect();
        if words.len() != 10 || words[0] != "hnn-field-v2" {
            return refuse("a field's head line that is not hnn-field-v2");
        }
        let n = |w: &str| w.parse::<usize>().map_err(|_| TowerError::Refused("a field's declaration that is not a count"));
        let d = Self { alphabet: n(words[1])?, width: n(words[2])?, heads: n(words[3])?, modes: n(words[4])?, still: n(words[5])?, contacts: n(words[6])?, ticks: n(words[7])?, frames: n(words[8])?, reach: n(words[9])? };
        d.admit()?;
        Ok(d)
    }
}

/// The material's families in order: each family's first entry, the material's length, and
/// each family as `(start, len, grain)`. A realization reads the material through it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldLayout {
    pub enc: usize,
    pub before: usize,
    pub after: usize,
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
        let before = push((a + 1) * dw, FACE_BITS);
        let after = push((a + 1) * dw, FACE_BITS);
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
        Self { enc, before, after, q, q_bias, k, k_bias, v, v_bias, out, out_bias, a: a_, a_bias, b, b_bias, w, w_bias, read, read_bias, len: at, families }
    }
}

/// A prime's tower of closures from `p` to the first power that spans `reach` sites.
fn tower(p: usize, reach: usize) -> Vec<usize> {
    let mut out = vec![p];
    while let Some(&top) = out.last() {
        if top >= reach {
            break;
        }
        match top.checked_mul(p) {
            Some(next) => out.push(next),
            None => break,
        }
    }
    out
}

/// [definition; agent-inferred, November 1] **The turned slots' ring periods**: the solenoid's two
/// coprime towers, the dyadic `2, 4, 8, …` and the triadic `3, 9, 27, …`, each from its finest
/// closure to the first that spans the reach. A tower's ring `p^(k+1)` reads the residue of ring
/// `p^k` and its whole winding, so a tower read together is a place's residue and its windings at
/// every scale, and its top ring turns less than once across any region (a distance, not only a
/// residue). The slots take `⌈S/2⌉` rings of the dyadic tower and `⌊S/2⌋` of the triadic, each
/// spread evenly from the finest to the top (a lone slot takes the top; more slots than closures
/// cycle the tower), merged in ascending period. Slot `s` of [`FieldDeclaration::turned_slots`]
/// is ring set `s mod frames`'s local mode `still + s / frames`, so every ring set spans fine to
/// coarse. Two sites that agree modulo every ring are at least the top dyadic closure apart,
/// beyond the reach: no two sites of an admitted region share every frame.
///
/// (The prime powers `2, 3, 4, 5, 7, 8, …` of the first draft closed every ring within a few
/// tens of sites and aliased sites `lcm` apart, 840 for six rings: the review of November 1.)
pub fn ring_periods(slots: usize, reach: usize) -> Vec<usize> {
    let sample = |tower: &[usize], count: usize| -> Vec<usize> {
        (0..count)
            .map(|k| match count {
                1 => tower[tower.len() - 1],
                _ if count <= tower.len() => tower[k * (tower.len() - 1) / (count - 1)],
                _ => tower[k % tower.len()],
            })
            .collect()
    };
    let mut out = sample(&tower(2, reach), slots.div_ceil(2));
    out.extend(sample(&tower(3, reach), slots / 2));
    out.sort_unstable();
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
    /// Each turned slot's period and its ring's phasors on `2^(−30)` (the residues a region within
    /// the reach reads).
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
    /// Gibbs weights `[h][i][j]` on `2^(−40)` of their row's peak, and each row's mass `[h][i]`:
    /// the numerators and their shared denominator.
    e: Vec<u64>,
    mass: Vec<u64>,
    /// The current `[t][2M]`, back in each site's own frame.
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
        let rings = ring_periods(declaration.turned_slots(), declaration.reach).into_iter().map(|n| (n, (0..n.min(declaration.reach)).map(|r| ring_phasor(r, n, pi)).collect())).collect();
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

    /// The frame of local mode `l` of head `h` at site `t`, on `2^(−30)`.
    fn frame(&self, t: usize, h: usize, l: usize) -> (i64, i64) {
        let d = &self.declaration;
        if l < d.still {
            return (1i64 << MOVE_BITS, 0);
        }
        let (n, ring) = &self.rings[(l - d.still) * d.frames + h % d.frames];
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
        if region.classes.len() > self.declaration.reach {
            return refuse("a region past the field's reach, where its frames would repeat");
        }
        if region.classes.iter().any(|&c| c >= self.declaration.alphabet) {
            return refuse("a region's class outside the field's alphabet");
        }
        Ok(())
    }

    /// A site's encoding row: its class, or the unresolved row.
    fn row(&self, region: &Region, t: usize) -> usize {
        if region.unresolved[t] { self.declaration.alphabet } else { region.classes[t] }
    }

    /// The region's opening faces `x⁰`: each site's row of the encoding with its strand
    /// neighbours' rows of their own encodings, `x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1))` (a
    /// region's first site has no site before it, its last none after).
    fn open(&self, region: &Region) -> Vec<i64> {
        let dw = self.declaration.width;
        let sites = region.classes.len();
        let mut x = vec![0i64; sites * dw];
        for (t, xt) in x.chunks_exact_mut(dw).enumerate() {
            let mut rows = vec![self.layout.enc + self.row(region, t) * dw];
            if t > 0 {
                rows.push(self.layout.before + self.row(region, t - 1) * dw);
            }
            if t + 1 < sites {
                rows.push(self.layout.after + self.row(region, t + 1) * dw);
            }
            for start in rows {
                for (slot, &e) in xt.iter_mut().zip(&self.theta[start..start + dw]) {
                    *slot += e as i64;
                }
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
                    let (ur, ui) = self.frame(t, h, li);
                    let (ur, ui) = (ur as i128, ui as i128);
                    let (qr, qi) = (q[t * m2 + c] as i128, q[t * m2 + m + c] as i128);
                    let (kr, ki) = (k[t * m2 + c] as i128, k[t * m2 + m + c] as i128);
                    cell.q[at + li] = fit64(release(ur * qr - ui * qi, MOVE_BITS))?;
                    cell.q[at + n + li] = fit64(release(ui * qr + ur * qi, MOVE_BITS))?;
                    let (vr, vi) = (v[t * m2 + c] as i128, v[t * m2 + m + c] as i128);
                    cell.k[at + li] = fit64(release(ur * kr - ui * ki, MOVE_BITS))?;
                    cell.k[at + n + li] = fit64(release(ui * kr + ur * ki, MOVE_BITS))?;
                    cell.v[at + li] = fit64(release(ur * vr - ui * vi, MOVE_BITS))?;
                    cell.v[at + n + li] = fit64(release(ui * vr + ur * vi, MOVE_BITS))?;
                }
            }
        }
        // The contact, the weights and the current, head by head. The current gathers each
        // site's framed value, `ỹ_i = Σ_j e_ij ṽ_j / Σ_j e_ij` (the numerators summed whole over
        // their shared denominator, one release), and returns it to the receiving site's own frame,
        // `y_i = conj(U_i) ỹ_i`: the moment carries each source's place relative to its receiver.
        cell.e = vec![0u64; heads * sites * sites];
        cell.mass = vec![0u64; heads * sites];
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
                let row = &mut cell.e[(h * sites + i) * sites..(h * sites + i + 1) * sites];
                for (ej, &zj) in row.iter_mut().zip(z.iter()) {
                    *ej = release(self.exponential.below_one(zj as i128 - peak as i128) as i128, WEIGHT_BITS_FROM) as u64;
                }
                let mass: u64 = row.iter().sum();
                cell.mass[h * sites + i] = mass;
                let mut framed = vec![0i64; span];
                for (r, slot) in framed.iter_mut().enumerate() {
                    let mut sum = 0i128;
                    for (j, &ej) in row.iter().enumerate() {
                        sum += ej as i128 * cell.v[(h * sites + j) * span + r] as i128;
                    }
                    *slot = fit64(div_nearest(sum, mass as i128))?;
                }
                for li in 0..n {
                    let (ur, ui) = self.frame(i, h, li);
                    let (ur, ui) = (ur as i128, ui as i128);
                    let (yr, yi) = (framed[li] as i128, framed[n + li] as i128);
                    let c = h * n + li;
                    cell.y[i * m2 + c] = fit64(release(ur * yr + ui * yi, MOVE_BITS))?;
                    cell.y[i * m2 + m + c] = fit64(release(ur * yi - ui * yr, MOVE_BITS))?;
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
            let mut w = vec![0i64; sites * span];
            let mut ds = vec![0i128; sites * sites];
            let carried = WEIGHT_BITS + SHARE_BITS;
            for h in 0..heads {
                // δỹ_i = U_i δy_i, the adjoint of the return to the receiver's frame.
                for t in 0..sites {
                    for li in 0..n {
                        let c = h * n + li;
                        let (ur, ui) = self.frame(t, h, li);
                        let (ur, ui) = (ur as i128, ui as i128);
                        let (gr, gi) = (dy[t * m2 + c] as i128, dy[t * m2 + m + c] as i128);
                        dyh[t * span + li] = fit64(release(ur * gr - ui * gi, MOVE_BITS))?;
                        dyh[t * span + n + li] = fit64(release(ui * gr + ur * gi, MOVE_BITS))?;
                    }
                }
                let e = &cell.e[h * sites * sites..(h + 1) * sites * sites];
                let mass = &cell.mass[h * sites..(h + 1) * sites];
                let vh = &cell.v[h * sites * span..(h + 1) * sites * span];
                let qh = &cell.q[h * sites * span..(h + 1) * sites * span];
                let kh = &cell.k[h * sites * span..(h + 1) * sites * span];
                // δṽ_j = Σ_i (e_ij / Σ_k e_ik) δỹ_i: each receiver's covector over its row's
                // denominator, carried 2^(−30) finer, then one integer sum over receivers.
                for i in 0..sites {
                    for r in 0..span {
                        let scaled = (dyh[i * span + r] as i128).checked_mul(1i128 << carried).ok_or(TowerError::Refused("a current's covector outgrew its 128-bit carrier"))?;
                        w[i * span + r] = fit64(div_nearest(scaled, mass[i] as i128))?;
                    }
                }
                for j in 0..sites {
                    for r in 0..span {
                        let mut sum = 0i128;
                        for i in 0..sites {
                            sum += e[i * sites + j] as i128 * w[i * span + r] as i128;
                        }
                        // Held in the framed chart until the frame is undone below.
                        let c = h * n + r % n;
                        dv[j * m2 + if r < n { c } else { m + c }] = fit64(release(sum, carried))?;
                    }
                }
                // δz_ij = ln 2 · (e_ij/Σe)(δp_ij − Σ_k (e_ik/Σe) δp_ik), δp_ij = ⟨δỹ_i, ṽ_j⟩ on
                // 2^(−40), each numerator summed whole over the row's one denominator.
                for i in 0..sites {
                    let dyi = &dyh[i * span..(i + 1) * span];
                    let dp: Vec<i128> = (0..sites).map(|j| dyi.iter().zip(&vh[j * span..(j + 1) * span]).map(|(&a, &b)| a as i128 * b as i128).sum()).collect();
                    let row = &e[i * sites..(i + 1) * sites];
                    let denominator = mass[i] as i128;
                    let mean = div_nearest(row.iter().zip(&dp).map(|(&ej, &dpj)| ej as i128 * dpj).sum(), denominator);
                    for j in 0..sites {
                        let dz = release(ln2 * div_nearest(row[j] as i128 * (dp[j] - mean), denominator), MOVE_BITS);
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
            // Undo the frame: δq = conj(U) δq̃, and so for the keys and the values.
            for t in 0..sites {
                for c in 0..m {
                    let (ur, ui) = self.frame(t, c / n, c % n);
                    let (ur, ui) = (ur as i128, ui as i128);
                    for chart in [&mut dq, &mut dk, &mut dv] {
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
        // The opening: each site's row of the encoding and its neighbours' rows of theirs.
        for t in 0..sites {
            let mut rows = vec![l.enc + self.row(region, t) * dw];
            if t > 0 {
                rows.push(l.before + self.row(region, t - 1) * dw);
            }
            if t + 1 < sites {
                rows.push(l.after + self.row(region, t + 1) * dw);
            }
            for start in rows {
                for i in 0..dw {
                    g[start + i] += dx[t * dw + i] as i128;
                }
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

    /// [`Field::release`] of many problems at once on a declared realization: every problem's sweep
    /// is read in one call (a region's faces do not depend on the regions read beside it, so the
    /// releases are each problem's own). `problems` are each question's classes and its answer's
    /// open sites.
    /// `sweep` is asked before every sweep whether it runs ([`ReleaseSweep`]).
    pub fn release_realized(&self, problems: &[(&[usize], usize)], sweeps: usize, void: usize, realization: &mut dyn FieldRealization, sweep: &mut dyn FnMut(&ReleaseSweep) -> bool) -> Result<Vec<Vec<usize>>> {
        self.release_with(problems, sweeps, void, &mut |regions| realization.read_faces(self, regions), sweep)
    }

    /// **The release by refinement** ([definition; agent-inferred, November 1]): the region of the
    /// `question`'s resolved sites and `answer` unresolved sites is refined over at most `sweeps`
    /// sweeps. Sweep `s` reads every unresolved site's face and releases every site the field
    /// resolves: whose top class outweighs every other class together (`2 m_c > Σ m`). When it
    /// resolves none, the face is read again with the question's sites unresolved (the released
    /// answer sites kept) and the one site whose top class carries the most news ([`by_news`]) is
    /// released, so a sweep always releases at least one site. The `void` is the answer's boundary,
    /// one nested variable: at the opening, the earliest site whose void the field resolves is
    /// released and every site past it leaves the region; after it, a site whose top class is the
    /// void is released only when it is the answer's first open site (every answer site before it
    /// released), and it ends the answer. Returns the answer as released: its classes up to its
    /// first site still unresolved after the last sweep, or through its void.
    ///
    /// Why the extent is read at the opening (the fifth reading, November 1): with the void
    /// released only at the front, every region kept the codec's whole extent (1,229 sites against
    /// held answers of median 254) until its content reached the end, so every sweep read the whole
    /// extent and the free release stopped at its deadline with 82 of 128 answers open, their marks
    /// never read. At the opening nothing is released, so no void is read beside a released void
    /// and the void's face at `t` is the field's `P(L ≤ t)`: the earliest `t` where it resolves
    /// (`2 m_void > Σ m`) is the extent's median, the majority release of the one variable, read
    /// once. The creep of §15 came from iterating that release against its own released voids,
    /// which the front alone now does.
    ///
    /// Why the boundary follows the content (the fourth reading on the card, November 1): released
    /// as an ordinary class, the void crept. A released void at `t + 1` says the answer's extent `L`
    /// is at most `t`, and given that, the void at `t` is likely by `1 − h(t)`, `h` the hazard of
    /// `L` at `t`, which is small wherever `L` is spread: each released void made the void before it
    /// resolve, while the answer sites before it stayed open and could not stop it. The release by
    /// marginal majority, iterated on the one variable whose classes nest (`void at t` implies `void
    /// past t`), moves the boundary toward the least extent the field admits, whatever the field:
    /// every one of the 128 held releases ended at its void after 7 to 54 sites (mean 27) against held
    /// answers of median 254. Released only after the content before it, no void is ever read
    /// beside another released void, so the boundary is read against the content alone.
    ///
    /// Why (the third reading on the card, November 1): a sweep released `⌈r/(S − s)⌉` sites
    /// whether the field resolved them or not, 77 of the 1,229 open sites at the first sweep, each
    /// with no answer site resolved beside it. There the field's face is near the bytes' own table
    /// (the held answers coded at 5.34 bits a byte; the training answers' byte table codes them at
    /// 5.05), whose top class is the space, so 125 of 128 releases were spaces alone. An answer's
    /// bytes are written by their neighbours (four bytes before a site code it at 1.98 bits on the
    /// same table's terms): a site released before its neighbours pays the difference, and once
    /// released it is their context. Released only where the field resolves it, a site waits for
    /// the sites that inform it.
    pub fn release(&self, question: &[usize], answer: usize, sweeps: usize, void: usize) -> Result<Vec<usize>> {
        Ok(self.release_with(&[(question, answer)], sweeps, void, &mut |regions| self.read_faces(regions), &mut |_| true)?.remove(0))
    }

    fn release_with(&self, problems: &[(&[usize], usize)], sweeps: usize, void: usize, read: &mut dyn FnMut(&[Region]) -> Result<Vec<Vec<Option<TowerFace>>>>, sweep: &mut dyn FnMut(&ReleaseSweep) -> bool) -> Result<Vec<Vec<usize>>> {
        if sweeps == 0 || void >= self.declaration.alphabet || problems.iter().any(|&(_, answer)| answer == 0) {
            return refuse("a release needs a sweep, an answer site and a void class in the alphabet");
        }
        // Each problem's region: its classes, its unresolved sites and its answer's first site.
        let mut states: Vec<(Vec<usize>, Vec<bool>, usize)> = problems
            .iter()
            .map(|&(question, answer)| {
                let start = question.len();
                let classes = question.iter().copied().chain(std::iter::repeat_n(void, answer)).collect();
                let unresolved = std::iter::repeat_n(false, start).chain(std::iter::repeat_n(true, answer)).collect();
                (classes, unresolved, start)
            })
            .collect();
        let open = |states: &[(Vec<usize>, Vec<bool>, usize)]| -> Vec<usize> { (0..states.len()).filter(|&k| states[k].1.iter().any(|&u| u)).collect() };
        let mut progress = ReleaseSweep::default();
        for done in 0..sweeps {
            let live = open(&states);
            progress.done = done;
            progress.live = live.len();
            if live.is_empty() || !sweep(&progress) {
                break;
            }
            progress.done = done + 1;
            let faces = {
                let views: Vec<Region> = live.iter().map(|&k| Region { classes: &states[k].0, unresolved: &states[k].1 }).collect();
                read(&views)?
            };
            // Each open problem's first open answer site: after the opening, the one site where its
            // boundary, the void, may be released (every answer site before it released).
            let first: Vec<usize> = live.iter().map(|&k| (states[k].2..states[k].1.len()).find(|&t| states[k].1[t]).unwrap_or(states[k].1.len())).collect();
            // At the opening, the extent: the earliest site whose void the field resolves.
            let extent: Vec<Option<usize>> = if done == 0 {
                faces.iter().map(|faces| faces.iter().enumerate().find_map(|(t, face)| face.as_ref().and_then(|f| resolved(f)).filter(|&c| c == void).map(|_| t))).collect()
            } else {
                vec![None; live.len()]
            };
            for (&k, end) in live.iter().zip(&extent) {
                if let Some(end) = end {
                    progress.cut += 1;
                    progress.cut_sites += end - states[k].2;
                }
            }
            // A site past the extent leaves with the region, so it is not released.
            let admitted = |j: usize, (t, c): (usize, usize)| (c != void || t == first[j] || extent[j] == Some(t)) && extent[j].is_none_or(|e| t <= e);
            // The sites the field resolves: the top class outweighs every other together.
            let mut released: Vec<Vec<(usize, usize)>> = faces.iter().enumerate().map(|(j, faces)| faces.iter().enumerate().filter_map(|(t, face)| face.as_ref().and_then(|f| resolved(f).map(|c| (t, c)))).filter(|&tc| admitted(j, tc)).collect()).collect();
            progress.resolved += released.iter().map(Vec::len).sum::<usize>();
            // Where it resolves none, the prior read: the question's sites unresolved, so a face
            // reads only the place the question spans and the answer released so far; the site
            // the question tells most about is released (the first open site is always admitted,
            // so one is).
            let unsure: Vec<usize> = (0..live.len()).filter(|&j| released[j].is_empty()).collect();
            progress.by_news += unsure.len();
            if !unsure.is_empty() {
                let priors: Vec<Vec<bool>> = unsure.iter().map(|&j| states[live[j]].1.iter().enumerate().map(|(t, &u)| u || t < states[live[j]].2).collect()).collect();
                let prior_views: Vec<Region> = unsure.iter().zip(&priors).map(|(&j, p)| Region { classes: &states[live[j]].0, unresolved: p }).collect();
                let prior = read(&prior_views)?;
                for (&j, prior) in unsure.iter().zip(&prior) {
                    released[j].extend(by_news(&faces[j], prior)?.into_iter().find(|&tc| admitted(j, tc)));
                }
            }
            for (&k, released) in live.iter().zip(&released) {
                let (classes, unresolved, start) = &mut states[k];
                for &(t, top) in released {
                    classes[t] = top;
                    unresolved[t] = false;
                }
                // The region ends at its released void: the sites past it leave.
                if let Some(end) = (*start..classes.len()).find(|&t| !unresolved[t] && classes[t] == void) {
                    classes.truncate(end + 1);
                    unresolved.truncate(end + 1);
                }
            }
        }
        // The closing report: the sweeps run and the problems left open.
        progress.live = open(&states).len();
        sweep(&progress);
        // The answer as released: up to its first site still unresolved.
        Ok(states
            .into_iter()
            .map(|(classes, unresolved, start)| {
                let end = (start..classes.len()).find(|&t| unresolved[t]).unwrap_or(classes.len());
                classes[start..end].to_vec()
            })
            .collect())
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

/// [agent-inferred, November 1] **A release's sweeps as its exterior reads them**: asked before
/// every sweep, `done` sweeps run, `live` problems still open, and the sites released so far by
/// resolution (`resolved`) and by news (`by_news`, one a problem whose sweep resolved none); its
/// answer decides whether the sweep runs. Asked once more after the last sweep, its answer unread.
/// The release reads no clock: the exterior that holds the run's projected deadline stops it there
/// (the waiting standard), and the answers are returned as released.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ReleaseSweep {
    pub done: usize,
    pub live: usize,
    pub resolved: usize,
    pub by_news: usize,
    /// The problems whose extent the opening read bounded, and those extents' answer sites.
    pub cut: usize,
    pub cut_sites: usize,
}

/// [definition; agent-inferred, November 1] **The release's order is the news a site's top class
/// carries** (the record's §11). `faces` are a region's faces with its question resolved and
/// `prior` the same region's with the question's sites unresolved: the prior face reads what the
/// field predicts from the place alone and the answer released so far. A site's top class `c`
/// (the lower class on a tie) carries the news `ν = (−log₂ p̄(c)) − (−log₂ p̂(c))`, the bits the
/// question tells about it, the perceived difference that what the field already predicts cancels;
/// its key is `p̂(c) ν` (the expected news of releasing it), on `2^(−40)` bits. Returns each open
/// site and its top class, the largest key first, the earlier site on a tie.
///
/// Why (the first reading on the card, November 1): released by the top class's share, the field
/// released its commonest classes first, a space, `e` and the void wherever the place alone
/// predicted them, and each release made the next likelier; 228 of 396 written values were `10`,
/// no release used its problem's words, and releases ended a median 71 classes into a held answer
/// of 254. The share counts certainty the question did not supply. The news counts only what the
/// question supplies, so a void the place alone predicts, or a space the released words around it
/// predict, is released after the classes the question decides.
pub fn by_news(faces: &[Option<TowerFace>], prior: &[Option<TowerFace>]) -> Result<Vec<(usize, usize)>> {
    let mut open: Vec<(i128, usize, usize)> = Vec::new();
    for (t, face) in faces.iter().enumerate() {
        let Some(face) = face else { continue };
        let Some(base) = prior.get(t).and_then(Option::as_ref) else {
            return refuse("a release's prior read has no face at an open site");
        };
        if base.masses.len() != face.masses.len() || face.total == 0 {
            return refuse("a release's two faces of one site over different alphabets");
        }
        let (top, &mass) = face.masses.iter().enumerate().fold((0usize, &0u128), |best, (c, mass)| if *mass > *best.1 { (c, mass) } else { best });
        let news = i128::from(face_code(base.masses[top], base.total)) - i128::from(face_code(mass, face.total));
        let total = i128::try_from(face.total).map_err(|_| TowerError::Refused("a face's total outgrew its 128-bit carrier"))?;
        let scaled = i128::try_from(mass).ok().and_then(|m| m.checked_mul(news)).and_then(|v| v.checked_mul(1i128 << NEWS_BITS)).ok_or(TowerError::Refused("a release's news outgrew its 128-bit carrier"))?;
        open.push((div_nearest(scaled, total), t, top));
    }
    open.sort_by(|x, y| y.0.cmp(&x.0).then(x.1.cmp(&y.1)));
    Ok(open.into_iter().map(|(_, t, top)| (t, top)).collect())
}

/// The class a face resolves: its top class when that class's mass outweighs every other class's
/// together (`2 m_c > Σ m`), so the release is likelier right than wrong ([`Field::release`]).
fn resolved(face: &TowerFace) -> Option<usize> {
    let (top, &mass) = face.masses.iter().enumerate().fold((0usize, &0u128), |best, (c, mass)| if *mass > *best.1 { (c, mass) } else { best });
    (mass.checked_mul(2)? > face.total).then_some(top)
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
        self.declaration.growth_draws(factor)
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
            repeat(ol.before + row * dw, layout.before + row * dw2, dw, f, &face, true);
            repeat(ol.after + row * dw, layout.after + row * dw2, dw, f, &face, true);
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

/// [agent-inferred, November 1] A held step read on regions it was not fit on
/// ([`FieldLearner::read_step_on`]): its change to those regions' code (the stepped material's
/// code less the material's before the step, on `2^(−20)` bits), the further halvings of the last
/// size read ([`FieldLearner::next_scale`]: the step stands at them unless refused), and whether
/// it refused the step.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FieldNext {
    pub change: i64,
    pub halvings: u32,
    pub refused: bool,
}

/// A section's receipt: its unresolved sites, its code before and after (on `2^(−20)` bits), the
/// halvings the certificate took, whether a step was deposited, and the read of the step the
/// section before deposited on this section's regions.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FieldReceipt {
    pub sites: usize,
    pub code_before: i64,
    pub code_after: i64,
    pub halvings: u32,
    pub deposited: bool,
    pub next: Option<FieldNext>,
}

/// A deposited step held for the next regions' read: the proposed step on each family's grain and
/// the halvings it was certified at. The material before it is the material less nothing: the
/// deposit subtracted `release(step, halvings)` from each entry, so adding it back is exact.
#[derive(Clone, Debug, PartialEq, Eq)]
struct HeldStep {
    step: Vec<i128>,
    halvings: u32,
}

/// Each unresolved site's face read at its class, the faces the certificates compare.
fn compared(faces: &[Vec<Option<TowerFace>>], regions: &[Region]) -> Vec<(u128, u128)> {
    faces.iter().zip(regions).flat_map(|(f, r)| f.iter().zip(r.classes).filter_map(|(face, &c)| face.as_ref().map(|face| (face.masses[c], face.total)))).collect()
}

fn code_of(pairs: &[(u128, u128)]) -> i64 {
    pairs.par_iter().map(|&(m, t)| face_code(m, t)).sum()
}

/// `base` less `release(step, halvings)` in each entry, and whether any entry moved.
fn stepped(base: &Field, step: &[i128], halvings: u32) -> Result<(Field, bool)> {
    let mut candidate = base.clone();
    let mut moved = false;
    for (slot, &q) in candidate.theta.iter_mut().zip(step) {
        let s = release(q, halvings);
        if s != 0 {
            moved = true;
            *slot = fit32(*slot as i128 - s, "a deposited parameter outgrew its 32-bit carrier")?;
        }
    }
    Ok((candidate, moved))
}

/// What [`scaled`] read: the regions' code under the step at its size less `old`'s (on `2^(−20)`
/// bits), the further halvings of the last size read, and the stepped material that stands with
/// its faces (`None`: the step stands at no size read).
struct Scaled {
    change: i64,
    halvings: u32,
    standing: Option<(Field, Vec<Vec<Option<TowerFace>>>)>,
}

/// [definition; agent-inferred, November 1] **A step's size read in at most three reads**, the one
/// law of the certificate ([`FieldLearner::section_realized`], `strict`: the stepped material must
/// code the regions strictly fewer bits than `old`) and of the held step's read on the next
/// regions ([`FieldLearner::next_scale`]: no more bits). The step `base − release(step, h0)` is
/// read; where it stands, it stands. Otherwise it is read at half its size; where that stands, it
/// stands halved. Otherwise the excess `e(μ)` of the regions' code over `old`'s at the step's
/// fraction `μ` is read at `μ = 1` and `μ = ½`, and the parabola `e(μ) = aμ + bμ²` through them
/// (`e(0) = 0`) has `a = 4e(½) − e(1)`, `b = 2e(1) − 4e(½)`: with `a ≥ 0` (or an excess the codes
/// read at or below zero where the exact comparison did not stand) the step's direction raises the
/// regions' code at every size the reads resolve, and it stands nowhere; with `a < 0` (then
/// `b > 0`) the parabola is lowest at `μ* = −a/2b ≤ ¼`, and the step is read once more at the
/// largest halving `2^(−h) ≤ μ*`, where the parabola is below zero, standing there or nowhere. A
/// size that moves no entry stands nowhere.
///
/// Why bounded (the second reading, receipts `…_receipts/reading-2/`): halving until the step
/// stood took 1,608 rereads of the next regions over 131 of 336 sections, 67 of the 105 halved
/// steps standing only at `2^(−12)` of their size or less, and the certificate's own halvings
/// reached 9 to 18 on 14 sections; their direction, not their size, raised the code, which the
/// parabola reads from two reads where the halvings read it from a dozen.
fn scaled(base: &Field, step: &[i128], h0: u32, old: &[(u128, u128)], strict: bool, regions: &[Region], realization: &mut dyn FieldRealization) -> Result<Scaled> {
    let stands = |new: &[(u128, u128)]| if strict { fewer_bits(old, new) } else { !fewer_bits(new, old) };
    let code_old = code_of(old);
    let (full, moved) = stepped(base, step, h0)?;
    if !moved {
        return Ok(Scaled { change: 0, halvings: 0, standing: None });
    }
    let full_faces = realization.read_faces(&full, regions)?;
    let at_full = compared(&full_faces, regions);
    let change = code_of(&at_full) - code_old;
    if stands(&at_full) {
        return Ok(Scaled { change, halvings: 0, standing: Some((full, full_faces)) });
    }
    let nowhere = |halvings: u32| Scaled { change, halvings, standing: None };
    let (half, moved) = stepped(base, step, h0 + 1)?;
    if !moved {
        return Ok(nowhere(1));
    }
    let half_faces = realization.read_faces(&half, regions)?;
    let at_half = compared(&half_faces, regions);
    if stands(&at_half) {
        return Ok(Scaled { change, halvings: 1, standing: Some((half, half_faces)) });
    }
    // The parabola through the two excesses (on the codes' `2^(−20)` bits).
    let (e1, e2) = (i128::from(change), i128::from(code_of(&at_half) - code_old));
    let a = 4 * e2 - e1;
    if e1 <= 0 || e2 <= 0 || a >= 0 {
        return Ok(nowhere(1));
    }
    // `1/μ* = 2b/(−a) = (4e(1) − 8e(½))/(e(1) − 4e(½))`; `h` the least with `2^h ≥ 1/μ*`.
    let (num, den) = (4 * e1 - 8 * e2, e1 - 4 * e2);
    let mut h = 2u32;
    while h < 127 && (den << h) < num {
        h += 1;
    }
    let (candidate, moved) = stepped(base, step, h0 + h)?;
    if !moved {
        return Ok(nowhere(h));
    }
    let candidate_faces = realization.read_faces(&candidate, regions)?;
    if stands(&compared(&candidate_faces, regions)) {
        return Ok(Scaled { change, halvings: h, standing: Some((candidate, candidate_faces)) });
    }
    Ok(nowhere(h))
}

/// [definition; agent-inferred, November 1] **The field's learner**: the field, the covector's two
/// moments and the step's rate `2^(−k)`. The deposit is the tower's ([`super::TowerLearner`]),
/// with one difference: a coordinate's moments open at its own first nonzero covector (`m = g`,
/// `v = g²`), not at the section the learner first read. The returns and the readout open at zero,
/// so the charts' covectors first arrive sections later; moments opened from zero would step them
/// two to four times the declared rate until the second moment caught up (the review of
/// November 1).
///
/// **A step is held and read on the next regions** (the tower's acceptance 77,
/// [`super::TowerLearner::next_section`], always declared here): a step certified on its own
/// section is held, and the next section's regions are read under the material before it and its
/// size read on them by the one bounded law of a step's size ([`scaled`]): it stands at its size,
/// at half, or at the parabola's halving where it codes them no higher, or is refused (the
/// material before it stands). The moments stay as they moved. Why
/// (the first reading on the card, November 1): the certificate read only its own section, and
/// the held-out answer code rose at the second lap and the third (5.38, 5.49, 6.18 bits a class)
/// while the passage's own code fell every section; the tower had recorded this failure and its
/// repair, and the field was built without it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldLearner {
    pub field: Field,
    first: Vec<i128>,
    second: Vec<i128>,
    pub rate_bits: u32,
    /// The founding key bytes read so far: the founding's, then each growth's.
    pub drawn: usize,
    /// The laps the learner has read (an exterior walk's count, so a continued run keeps its
    /// keyed masks and order moving rather than replaying the first lap's).
    pub laps: u64,
    held: Option<HeldStep>,
}

impl FieldLearner {
    /// The learner of a field founded on its declared key stream (the founding read
    /// [`FieldDeclaration::founding_draws`] draws).
    pub fn new(field: Field, rate_bits: u32) -> Self {
        let len = field.theta.len();
        let drawn = 4 * field.declaration.founding_draws();
        Self { field, first: vec![0; len], second: vec![0; len], rate_bits, drawn, laps: 0, held: None }
    }

    /// Whether a deposited step is held for the next regions' read.
    pub fn holds_step(&self) -> bool {
        self.held.is_some()
    }

    /// [definition; agent-inferred, November 1] **The learner widened** ([`Field::grown`]), its
    /// differences read from the founding key stream past every draw read before, and its moments
    /// lifted as the tower's are: split evenly, each grown coordinate's covector at the growth
    /// point is the old one divided among its `f` copies and the readout's the old one, so a grown
    /// coordinate carries `m/f` and `v/f²`, the readout `m` and `v`, and opens on the old
    /// normalized step. Each copy then steps as the old coordinate did, and the `f` copies of a
    /// sum move together, so the rate falls by `⌈log₂ f⌉` bits: the field's step stays the old one.
    /// A learner holding a step is refused: the step is read first ([`FieldLearner::read_step_on`]).
    pub fn widened(&self, factor: usize, keys: &[u8]) -> Result<Self> {
        if self.held.is_some() {
            return refuse("a learner widens after its held step is read");
        }
        let rest = keys.get(self.drawn..).ok_or(TowerError::Refused("fewer key bytes than the growth draws"))?;
        let (field, from) = self.field.grown(factor, rest)?;
        let (f, f2) = (factor as i128, (factor * factor) as i128);
        let first = from.iter().map(|&(i, divided)| if divided { div_nearest(self.first[i], f) } else { self.first[i] }).collect();
        let second = from.iter().map(|&(i, divided)| if divided { div_nearest(self.second[i], f2) } else { self.second[i] }).collect();
        let drawn = self.drawn + 4 * self.field.growth_draws(factor);
        let rate_bits = self.rate_bits + (usize::BITS - (factor - 1).leading_zeros());
        Ok(Self { field, first, second, rate_bits, drawn, laps: self.laps, held: None })
    }

    /// The held step read on `regions` without a deposit: the faces of `regions` under the
    /// material that stands after the read, and the read (`None` when no step was held).
    pub fn read_step_on(&mut self, regions: &[Region], realization: &mut dyn FieldRealization) -> Result<(Vec<Vec<Option<TowerFace>>>, Option<FieldNext>)> {
        let (faces, _, next) = self.open(regions, realization, false)?;
        Ok((faces, next))
    }

    /// The opening read of `regions` (with the covector when `returning`), after the held step,
    /// if any, is read on them ([`FieldLearner::next_scale`]): the material before it and the
    /// stepped material read first, the material that stands decided, and the opening read read
    /// on it (a read already made is not made again).
    fn open(&mut self, regions: &[Region], realization: &mut dyn FieldRealization, returning: bool) -> Result<(Vec<Vec<Option<TowerFace>>>, Option<Vec<i128>>, Option<FieldNext>)> {
        let Some(held) = self.held.take() else {
            return if returning {
                let (faces, g) = realization.read_and_return(&self.field, regions)?;
                Ok((faces, Some(g), None))
            } else {
                Ok((realization.read_faces(&self.field, regions)?, None, None))
            };
        };
        let mut before = self.field.clone();
        for (slot, &q) in before.theta.iter_mut().zip(&held.step) {
            *slot = fit32(*slot as i128 + release(q, held.halvings), "a held step's material outgrew its 32-bit carrier")?;
        }
        let (standing, faces, next) = Self::next_scale(&before, &held, regions, realization)?;
        self.field = standing;
        if returning {
            let (faces, g) = realization.read_and_return(&self.field, regions)?;
            return Ok((faces, Some(g), Some(next)));
        }
        Ok((faces, None, Some(next)))
    }

    /// [definition; agent-inferred, November 1] **The held step read on regions it was not fit
    /// on** (the tower's acceptance 77, `TowerLearner::next_section`): the regions are read under
    /// the material before the step (`old`), and the step's size is read on them by [`scaled`]
    /// against `old`, standing where it codes them no higher. A refused step leaves the material
    /// before it, so the material that stands never codes the regions higher than `old`. At most
    /// four reads of the regions are made before the opening read.
    ///
    /// Returns the material that stands, its faces, and the read.
    #[allow(clippy::type_complexity)]
    fn next_scale(before: &Field, held: &HeldStep, regions: &[Region], realization: &mut dyn FieldRealization) -> Result<(Field, Vec<Vec<Option<TowerFace>>>, FieldNext)> {
        let before_faces = realization.read_faces(before, regions)?;
        let old = compared(&before_faces, regions);
        let scale = scaled(before, &held.step, held.halvings, &old, false, regions, realization)?;
        let next = FieldNext { change: scale.change, halvings: scale.halvings, refused: scale.standing.is_none() };
        Ok(match scale.standing {
            Some((field, faces)) => (field, faces, next),
            None => (before.clone(), before_faces, next),
        })
    }

    /// One section: the step the section before deposited read on its regions, then its regions
    /// read and returned on the material that stands, the moments moved, and the step deposited
    /// at the size where the regions reread under it code strictly fewer bits ([`scaled`]: its
    /// size, half, or the parabola's halving; none of them, no deposit) and held for the next
    /// section.
    pub fn section(&mut self, regions: &[Region]) -> Result<FieldReceipt> {
        self.section_realized(regions, &mut HostField)
    }

    /// [`FieldLearner::section`] on a declared realization of the field's read and return; the
    /// moments, the step and the certificates' decisions stay on the host.
    pub fn section_realized(&mut self, regions: &[Region], realization: &mut dyn FieldRealization) -> Result<FieldReceipt> {
        let (faces, g, next) = self.open(regions, realization, true)?;
        let mut g = g.ok_or(TowerError::Refused("a section's opening read returned no covector"))?;
        let faces_old = compared(&faces, regions);
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
        for ((m, v), gv) in self.first.iter_mut().zip(self.second.iter_mut()).zip(&g) {
            let square = gv.checked_mul(*gv).ok_or(TowerError::Refused("a covector's square outgrew its 128-bit carrier"))?;
            if *m == 0 && *v == 0 {
                // A coordinate opens at its own first nonzero covector.
                (*m, *v) = (*gv, square);
            } else {
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
        let scale = scaled(&self.field, &step, 0, &faces_old, true, regions, realization)?;
        let halvings = scale.halvings;
        let Some((candidate, faces_new)) = scale.standing else {
            return Ok(FieldReceipt { sites, code_before, code_after: code_before, halvings, deposited: false, next });
        };
        let code_after = code_of(&compared(&faces_new, regions));
        self.field = candidate;
        self.held = Some(HeldStep { step, halvings });
        Ok(FieldReceipt { sites, code_before, code_after, halvings, deposited: true, next })
    }

    /// The learner as text: its head line (the held step's halvings, or `-`), the field, each
    /// moment on one line, then the held step on one line when one is held.
    pub fn to_text(&self) -> String {
        let join = |v: &[i128]| v.iter().map(i128::to_string).collect::<Vec<_>>().join(" ");
        let (held, step) = match &self.held {
            Some(h) => (h.halvings.to_string(), format!("{}\n", join(&h.step))),
            None => ("-".to_string(), String::new()),
        };
        format!("hnn-field-learner-v3 {} {} {} {held}\n{}{}\n{}\n{step}", self.rate_bits, self.drawn, self.laps, self.field.to_text(), join(&self.first), join(&self.second))
    }

    pub fn from_text(text: &str) -> Result<Self> {
        let mut lines = text.lines();
        let head: Vec<&str> = lines.next().unwrap_or("").split(' ').collect();
        if head.len() != 5 || head[0] != "hnn-field-learner-v3" {
            return refuse("a learner's head line that is not hnn-field-learner-v3");
        }
        let rate_bits = head[1].parse::<u32>().map_err(|_| TowerError::Refused("a learner's rate that is not a count"))?;
        let drawn = head[2].parse::<usize>().map_err(|_| TowerError::Refused("a learner's drawn keys that are not a count"))?;
        let laps = head[3].parse::<u64>().map_err(|_| TowerError::Refused("a learner's laps that are not a count"))?;
        let field_text = format!("{}\n{}\n", lines.next().unwrap_or(""), lines.next().unwrap_or(""));
        let field = Field::from_text(&field_text)?;
        let first = read_numbers::<i128>(lines.next())?;
        let second = read_numbers::<i128>(lines.next())?;
        if first.len() != field.theta.len() || second.len() != field.theta.len() {
            return refuse("a learner's moments that are not its field's length");
        }
        let held = match head[4] {
            "-" => None,
            h => {
                let halvings = h.parse::<u32>().map_err(|_| TowerError::Refused("a learner's held halvings that are not a count"))?;
                let step = read_numbers::<i128>(lines.next())?;
                if step.len() != field.theta.len() {
                    return refuse("a learner's held step that is not its field's length");
                }
                Some(HeldStep { step, halvings })
            }
        };
        Ok(Self { field, first, second, rate_bits, drawn, laps, held })
    }
}

#[cfg(test)]
mod tests;
