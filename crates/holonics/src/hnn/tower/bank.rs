//! **The binding bank: a strand clocked by its antecedent, read by content** (#404, #405, #386).
//!
//! [definition; the mathematics thread's specification, record
//! `2026-10-26_THE_BINDING_BANK_IS_A_STRAND_CLOCKED_BY_ITS_ANTECEDENT_AND_A_RELEASE_IS_TRACED_BY_ITS_ADDRESS.md`,
//! §2] Why it is built. The tower's modes are one complex number each: no read of them returns
//! the one earlier arrival that followed a context like the present one. The bank clocks the
//! helical strand by content instead of position. Each arrival is bound to the face it arrived
//! into, and a read at the present face returns what followed faces like it.
//!
//! ```text
//! antecedent  a_t    = [r̂_(t−1), x^ℓ_(t−1)]                      the face the arrival came into
//! key turn    s(k_t) = 2^(−σ) (W_k a_t + b_k)                     d turns, half turns on 2^(−16)
//! query turn  s(q_t) = 2^(−σ) (W_q [r̂_t, x^ℓ_t] + b_q)            the present face
//! value       v_t    = W_v x^ℓ_t + b_v                            d_v real channels
//! harmonic    φ_n(s) = e^(iπ⟨n, s⟩),  n ∈ N = Π_i {0..M_i−1}      |N| = 2^m
//! news        e_t    = v_t − 2^(−m) S_(t−1) φ(s(k_t))             what the bank did not already say
//! write       S_t    = ρ (S_(t−1) + g_t e_t φ(s(k_t))ᴴ)           S: d_v × |N| complex
//! gate        g_t    = 1/(1 + 2^(−(W_g x^ℓ_t + b_g))),  ρ = 1/(1 + 2^(−h)), held at 1 − 2^(−12)
//! read        v̂_t    = 2^(−m) S_t φ(s(q_t))
//! join        x^(ℓ+1)_t = x^ℓ_t + W₂ v_t + b₂ + O [Re v̂_t ; Im v̂_t]
//! ```
//!
//! `σ = ⌈log₂ 2d⌉` spreads the turn over the antecedent's width, as a turned mode's turn is spread
//! over the level's. `S` is carried on the state's grain `2^(−24)`, each harmonic on the moves'
//! `2^(−30)`.
//!
//! [agent-inferred, October 26] **The placement's choices, each with its reason.**
//! - **One recurrence, no chunk.** Each cell's reads and writes are sums of co-present products
//!   over the bank's entries; integer addition is associative, so a realization that sums them
//!   in any order, on any partition of the card, rounds the same terms and returns the same bits.
//!   The record's chunk form regroups the same series for throughput across time, and rounds other
//!   terms; it is a later declaration (chunk length `C`), not this one (`C = 1`).
//! - **The bank joins like the tower's other faces** ([`Tower::join_bank`]), its material
//!   appended after them, rather than as a field of the declaration, so every founded tower and
//!   its text stay as they are.
//! - **The opening.** `O` opens at zero, so a banked tower reads every passage bit-identically to
//!   its bankless twin. The value opens on the identity (`v = x^ℓ`, the arrival's own face): a value
//!   at zero binds nothing, and `O`'s covector `Σ δx [Re v̂; Im v̂]ᵀ` would then be zero too, so
//!   nothing would open. The gate opens at its midpoint, `g = ½`. The hold opens at
//!   `h = 11`, `ρ = 1/(1 + 2^(−11))`: a memory of some 2,048 cells, one rung inside the margin, so
//!   its covector is read (a hold at the margin is held, and a held value carries none).
//! - **The key opens on a founded draw over the face block, and the query on the same draw.** The
//!   record opens both turns at zero. On a box with equal sides the two turn coordinates then
//!   receive equal covectors at every cell (`Σ_n n₁ f(n₁ + n₂) = Σ_n n₂ f(n₁ + n₂)`), so the key
//!   never leaves the box's diagonal and the bank holds 8 grid keys instead of 64 (measured on the
//!   founding's own reading of `K` on the diagonal). The key's material on the face block `x^ℓ` is
//!   therefore drawn uniform on `±2^σ/√d` from the declared key stream (a unit face's key turn opens
//!   at about half a half turn, two grid steps of an 8-harmonic side), its read block `r̂` and its
//!   bias at zero; the query opens on the same material. The key at a cell then names the face
//!   that arrived before it and the query the face arriving now, so the read at an arrival returns
//!   what followed that face's last arrival from the first cell, and the read block enters by its
//!   covector. Drawn over both blocks, the context read moves key and query apart: on the MQAR
//!   terrain at the top level the held-out answers stayed at 6.03 bits, the code of a uniform guess
//!   among the 64 values, from the 128th deposit to the 512th, since a read that recalls nothing
//!   gives `O`'s covector nothing to correlate with. The read reaches nothing until `O` opens, so
//!   the opening is still the twin's.
//! - **The opening state's covector is held as given.** As the tower's passage credit is declared
//!   for its modes only, a section's covector reaches the bank it opened on, and stops there: the
//!   bank's history credit across sections is owed, not carried.
use super::*;

/// [definition; agent-inferred, October 26] **The bank's declared law**: the level it reads and
/// joins, the harmonic box's side per key turn `M_i` (powers of two, so `|N| = 2^m` and the read's
/// `2^(−m)` is a shift), and the value channels `d_v`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BankDeclaration {
    pub level: usize,
    pub harmonics: Vec<usize>,
    pub values: usize,
}

impl BankDeclaration {
    /// The record's first declaration: one bank at the top level, two turns, an `8 × 8` box, and
    /// `d_v` the level's width.
    pub fn first(tower: &TowerDeclaration) -> Self {
        Self { level: tower.levels - 1, harmonics: vec![8, 8], values: tower.width }
    }

    /// The box's extent `|N|`.
    pub fn harmonics_len(&self) -> usize {
        self.harmonics.iter().product()
    }

    /// `m = log₂ |N|`.
    fn box_bits(&self) -> u32 {
        self.harmonics_len().trailing_zeros()
    }

    fn check(&self, d: &TowerDeclaration) -> Result<()> {
        if self.level >= d.levels {
            return refuse("a bank reads a level of the tower");
        }
        if self.harmonics.is_empty() || self.harmonics.iter().any(|&m| m < 2 || !m.is_power_of_two()) || self.values == 0 {
            return refuse("a bank needs a key turn, sides that are powers of two of at least two, and a value channel");
        }
        // The read sums |N| products of S on 2^(−24) and a harmonic on 2^(−30) in 128 bits.
        if self.harmonics_len() > 1 << 16 {
            return refuse("a harmonic box past 2^16 harmonics outgrows the read's 128-bit carrier");
        }
        Ok(())
    }

    /// The bank's line of the tower's text.
    pub fn to_text(&self) -> String {
        let sides = self.harmonics.iter().map(|m| m.to_string()).collect::<Vec<_>>().join(" ");
        format!("bank {} {} {sides}\n", self.level, self.values)
    }

    pub(super) fn from_text(line: &str, d: &TowerDeclaration) -> Result<Self> {
        let words: Vec<&str> = line.split(' ').collect();
        let num = |s: &str| s.parse::<usize>().map_err(|_| TowerError::Refused("a bank's line that is not counts"));
        if words.len() < 4 || words[0] != "bank" {
            return refuse("not a bank's line");
        }
        let bank = Self { level: num(words[1])?, values: num(words[2])?, harmonics: words[3..].iter().map(|w| num(w)).collect::<Result<_>>()? };
        bank.check(d)?;
        Ok(bank)
    }
}

/// Where the bank's families sit in the material.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct BankLayout {
    pub(super) key: usize,
    pub(super) key_bias: usize,
    pub(super) query: usize,
    pub(super) query_bias: usize,
    pub(super) value: usize,
    pub(super) value_bias: usize,
    pub(super) gate: usize,
    pub(super) gate_bias: usize,
    pub(super) hold: usize,
    pub(super) join: usize,
}

impl BankLayout {
    /// The bank's families taken in order from `take(len, grain)`.
    pub(super) fn new(bank: &BankDeclaration, width: usize, mut take: impl FnMut(usize, u32) -> usize) -> Self {
        let (turns, dv, a) = (bank.harmonics.len(), bank.values, 2 * width);
        Self {
            key: take(turns * a, MATERIAL_BITS),
            key_bias: take(turns, FACE_BITS),
            query: take(turns * a, MATERIAL_BITS),
            query_bias: take(turns, FACE_BITS),
            value: take(dv * width, MATERIAL_BITS),
            value_bias: take(dv, FACE_BITS),
            gate: take(width, MATERIAL_BITS),
            gate_bias: take(1, FACE_BITS),
            hold: take(1, FACE_BITS),
            join: take(width * 2 * dv, MATERIAL_BITS),
        }
    }
}

/// [definition; agent-inferred, October 26] **A stream's bank**: `S` (`d_v × |N|`, channel-major,
/// `(re, im)` on `2^(−24)`), and the face the next arrival comes into, `[r̂_t, x^ℓ_t]` on `2^(−16)`.
/// A cold start opens it empty: the bank is state, never constitution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BankState {
    pub bindings: Vec<(i64, i64)>,
    pub antecedent: Vec<i32>,
}

/// The bank's forward temporaries at one cell, for the reverse scan.
#[derive(Clone, Debug, Default)]
pub(super) struct BankCell {
    /// `S_(t−1)`, the bank the arrival met.
    before: Vec<(i64, i64)>,
    antecedent: Vec<i32>,
    key_phase: Vec<(i128, i128)>,
    query_phase: Vec<(i128, i128)>,
    /// `g_t e_t` on `2^(−24)`, and `e_t`.
    written: Vec<(i128, i128)>,
    news: Vec<(i128, i128)>,
    /// `g_t` on `2^(−30)`.
    gate: i128,
    /// `[Re v̂_t ; Im v̂_t]` on `2^(−16)`, what `O` reads.
    read: Vec<i32>,
}

/// The bank's reaches and its hold, read once a section.
#[derive(Clone, Debug)]
pub(super) struct BankReaches {
    key: u64,
    query: u64,
    value: u64,
    gate: u64,
    join: u64,
    /// `ρ` on `2^(−30)`, and whether it is held at the margin.
    rho: i128,
    held: bool,
    ladder: Vec<(i128, i128)>,
    half_turn: i128,
}

/// The covector's working grain inside the bank's reverse scan, `2^(−48)`.
const BANK_COVECTOR_BITS: u32 = 48;

/// `e^(iπ⟨n, s⟩)` on `2^(−30)` for every `n` of the box, the first turn's index fastest: each
/// coordinate's `M_i` faces read from the turn ladder, then their products.
fn harmonics(sides: &[usize], s: &[i64], ladder: &[(i128, i128)]) -> Vec<(i128, i128)> {
    let mut out = vec![(1i128 << MOVE_BITS, 0i128)];
    for (&m, &turn) in sides.iter().zip(s) {
        let faces: Vec<(i128, i128)> = (0..m as i64).map(|n| turn_face(n * turn, ladder)).collect();
        let mut next = Vec::with_capacity(out.len() * m);
        for &(fr, fi) in &faces {
            for &(or, oi) in &out {
                next.push((release(or * fr - oi * fi, MOVE_BITS), release(or * fi + oi * fr, MOVE_BITS)));
            }
        }
        out = next;
    }
    out
}

/// `2^(−m) S φ` per channel, on `2^(−24)`: `S` on `2^(−24)`, `φ` on `2^(−30)`.
fn read_at(bindings: &[(i64, i64)], phase: &[(i128, i128)], m: u32) -> Vec<(i128, i128)> {
    bindings
        .chunks_exact(phase.len())
        .map(|row| {
            let (mut re, mut im) = (0i128, 0i128);
            for (&(sr, si), &(pr, pi)) in row.iter().zip(phase) {
                let (sr, si) = (sr as i128, si as i128);
                re += sr * pr - si * pi;
                im += sr * pi + si * pr;
            }
            (release(re, MOVE_BITS + m), release(im, MOVE_BITS + m))
        })
        .collect()
}

/// `S_t = ρ (S_(t−1) + w φᴴ)`, `w = g e` on `2^(−24)`, and `S′ = S_(t−1) + w φᴴ` when `primed`.
fn written(before: &[(i64, i64)], w: &[(i128, i128)], phase: &[(i128, i128)], rho: i128, primed: bool) -> Result<Vec<(i64, i64)>> {
    let mut out = Vec::with_capacity(before.len());
    for (row, &(wr, wi)) in before.chunks_exact(phase.len()).zip(w) {
        for (&(sr, si), &(pr, pi)) in row.iter().zip(phase) {
            // w conj(φ) = (wr pr + wi pi) + i (wi pr − wr pi).
            let ar = sr as i128 + release(wr * pr + wi * pi, MOVE_BITS);
            let ai = si as i128 + release(wi * pr - wr * pi, MOVE_BITS);
            let (br, bi) = if primed { (ar, ai) } else { (release(rho * ar, MOVE_BITS), release(rho * ai, MOVE_BITS)) };
            out.push((fit64(br)?, fit64(bi)?));
        }
    }
    Ok(out)
}

impl Tower {
    /// [agent-inferred, October 26] **The binding bank joined to the tower** (the module
    /// [`crate::hnn::tower::bank`]): its families are appended after the tower's other faces and
    /// opened as the module states, so the joined tower reads every passage exactly as the tower
    /// did, and the section's covector moves them from there. The key's draw is read from `keys`,
    /// four bytes a value as the founding reads them. A stream rested before the join carries no
    /// bank: rest it again. Refused when a bank is already joined.
    pub fn join_bank(&mut self, bank: BankDeclaration, keys: &[u8]) -> Result<()> {
        if self.bank.is_some() {
            return refuse("a tower takes one bank");
        }
        let d = self.declaration;
        bank.check(&d)?;
        let start = self.layout.len;
        let layout = Layout::new(&d, self.pair.as_ref().map_or(0, PairFace::forms), self.ring.as_ref().map_or(0, RingFace::ranks), self.ring.as_ref().map_or(0, RingFace::harmonics), Some(&bank));
        self.theta.resize(layout.len, 0);
        let bl = layout.bank.expect("a bank's layout");
        debug_assert_eq!(bl.key, start);
        let (turns, a, w) = (bank.harmonics.len(), 2 * d.width, d.width);
        // The key's draw on the face block, uniform on ±2^σ/√d on the material's grain, the read
        // block at zero; the query on the same draw.
        let spread = turn_spread(a);
        let root = ((w as u128) << 32).isqrt(); // √d on 2^(−16)
        let reach = ((1u128 << (spread + MATERIAL_BITS + FACE_BITS)) / root) as i128;
        for i in 0..turns * a {
            let word = keys.get(4 * i..4 * i + 4).ok_or(TowerError::Refused("fewer key bytes than the bank's founding reads"))?;
            let k = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i128; // on 2^(−31)
            let v = if i % a < w { 0 } else { fit32((k * reach) >> 31, "a bank's founded key outgrew its 32-bit carrier")? };
            self.theta[bl.key + i] = v;
            self.theta[bl.query + i] = v;
        }
        // The value on the identity.
        for c in 0..bank.values.min(w) {
            self.theta[bl.value + c * w + c] = 1 << MATERIAL_BITS;
        }
        // The hold at h = 11.
        self.theta[bl.hold] = 11 << FACE_BITS;
        self.layout = layout;
        self.bank = Some(bank);
        Ok(())
    }

    /// The joined bank's declaration, when one is joined.
    pub fn bank(&self) -> Option<&BankDeclaration> {
        self.bank.as_ref()
    }

    /// The material range of the bank's join `O`, when one is joined: the read's ablation sets it
    /// to zero.
    pub fn bank_join(&self) -> Option<std::ops::Range<usize>> {
        let (bank, bl) = (self.bank.as_ref()?, self.layout.bank?);
        Some(bl.join..bl.join + self.declaration.width * 2 * bank.values)
    }

    /// The material range of every family of the bank, when one is joined.
    pub fn bank_families(&self) -> Option<std::ops::Range<usize>> {
        let bl = self.layout.bank?;
        Some(bl.key..self.bank_join()?.end)
    }

    /// The bank's empty state, when one is joined.
    pub(super) fn bank_rest(&self) -> Option<BankState> {
        let bank = self.bank.as_ref()?;
        Some(BankState { bindings: vec![(0, 0); bank.values * bank.harmonics_len()], antecedent: vec![0; 2 * self.declaration.width] })
    }

    pub(super) fn bank_reaches(&self) -> Option<BankReaches> {
        let (bank, bl) = (self.bank.as_ref()?, self.layout.bank?);
        let (t, w, a, turns, dv) = (&self.theta, self.declaration.width, 2 * self.declaration.width, bank.harmonics.len(), bank.values);
        let mut rho = logistic(&self.exponential, t[bl.hold] as i64);
        let held = rho > radius();
        if held {
            rho = radius();
        }
        Some(BankReaches {
            key: reach(&t[bl.key..bl.key + turns * a]),
            query: reach(&t[bl.query..bl.query + turns * a]),
            value: reach(&t[bl.value..bl.value + dv * w]),
            gate: reach(&t[bl.gate..bl.gate + w]),
            join: reach(&t[bl.join..bl.join + w * 2 * dv]),
            rho,
            held,
            ladder: turn_ladder_faces(),
            half_turn: half_turn(MOVE_BITS),
        })
    }

    /// The turns `2^(−σ) (W r + b)` of a key or query face `r` (`2d` entries), half turns on
    /// `2^(−16)`.
    fn bank_turns(&self, material: usize, bias: usize, wmax: u64, face: &[i32]) -> Result<Vec<i64>> {
        let bank = self.bank.as_ref().expect("a bank");
        let (turns, a) = (bank.harmonics.len(), face.len());
        let t = &self.theta;
        let mut s = vec![0i64; turns];
        affine(&t[material..material + turns * a], wmax, a, face, Some(&t[bias..bias + turns]), MATERIAL_BITS, MATERIAL_BITS, &mut s)?;
        for v in &mut s {
            *v = fit64(release(*v as i128, turn_spread(a)))?;
        }
        Ok(s)
    }

    /// One cell of the bank at its level: the arrival's face `x` (`x^ℓ_t`) and the level's read
    /// `read` (`r̂_t`) arrive; the bank binds the news at the antecedent's key, reads at the present
    /// face, and returns what it adds to the level's output, `O [Re v̂; Im v̂]` on `2^(−16)`.
    pub(super) fn bank_step(&self, reaches: &BankReaches, state: &mut BankState, x: &[i32], read: &[i32]) -> Result<(Vec<i64>, BankCell)> {
        let (bank, bl) = (self.bank.as_ref().expect("a bank"), self.layout.bank.expect("a bank's layout"));
        let t = &self.theta;
        let (w, dv, m) = (self.declaration.width, bank.values, bank.box_bits());
        if state.antecedent.len() != 2 * w || state.bindings.len() != dv * bank.harmonics_len() {
            return refuse("a bank's state of another shape");
        }
        let present: Vec<i32> = read.iter().chain(x).copied().collect();
        let key_phase = harmonics(&bank.harmonics, &self.bank_turns(bl.key, bl.key_bias, reaches.key, &state.antecedent)?, &reaches.ladder);
        let query_phase = harmonics(&bank.harmonics, &self.bank_turns(bl.query, bl.query_bias, reaches.query, &present)?, &reaches.ladder);
        let mut value = vec![0i64; dv];
        affine(&t[bl.value..bl.value + dv * w], reaches.value, w, x, Some(&t[bl.value_bias..bl.value_bias + dv]), MATERIAL_BITS, MATERIAL_BITS, &mut value)?;
        let mut q = [0i64];
        affine(&t[bl.gate..bl.gate + w], reaches.gate, w, x, Some(&t[bl.gate_bias..bl.gate_bias + 1]), MATERIAL_BITS, MATERIAL_BITS, &mut q)?;
        let gate = logistic(&self.exponential, q[0]);
        // The news e = v − 2^(−m) S φ(k) on 2^(−24), and what is written, g e.
        let said = read_at(&state.bindings, &key_phase, m);
        let news: Vec<(i128, i128)> = value.iter().zip(&said).map(|(&v, &(ur, ui))| (((v as i128) << (STATE_BITS - FACE_BITS)) - ur, -ui)).collect();
        let w_news: Vec<(i128, i128)> = news.iter().map(|&(er, ei)| (release(gate * er, MOVE_BITS), release(gate * ei, MOVE_BITS))).collect();
        let after = written(&state.bindings, &w_news, &key_phase, reaches.rho, false)?;
        let before = std::mem::replace(&mut state.bindings, after);
        let heard = read_at(&state.bindings, &query_phase, m);
        let mut face = Vec::with_capacity(2 * dv);
        for &(re, _) in &heard {
            face.push(fit32(release(re, STATE_BITS - FACE_BITS), "a bank's read outgrew the face's 32-bit carrier")?);
        }
        for &(_, im) in &heard {
            face.push(fit32(release(im, STATE_BITS - FACE_BITS), "a bank's read outgrew the face's 32-bit carrier")?);
        }
        let mut joined = vec![0i64; w];
        affine(&t[bl.join..bl.join + w * 2 * dv], reaches.join, 2 * dv, &face, None, 0, MATERIAL_BITS, &mut joined)?;
        let antecedent = std::mem::replace(&mut state.antecedent, present);
        Ok((joined, BankCell { before, antecedent, key_phase, query_phase, written: w_news, news, gate, read: face }))
    }

    /// The bank's reverse scan over one section at its level: `out` is the covector of each cell's
    /// level output `x^(ℓ+1)_t` (on `2^(−24)`), `inputs` and `reads` each cell's `x^ℓ_t` and `r̂_t`.
    /// The families' covectors are added to `g` on their natural grains; returned are the covectors
    /// the bank sends to each cell's `r̂_t` and `x^ℓ_t`, on `2^(−24)` (the record's §2.5).
    pub(super) fn bank_reverse(&self, reaches: &BankReaches, cells: &[&BankCell], inputs: &[&[i32]], reads: &[&[i32]], out: &[Vec<i64>], g: &mut [i128]) -> Result<(Vec<Vec<i64>>, Vec<Vec<i64>>)> {
        let (bank, bl) = (self.bank.as_ref().expect("a bank"), self.layout.bank.expect("a bank's layout"));
        let t = &self.theta;
        let (w, dv, nn, m, turns) = (self.declaration.width, bank.values, bank.harmonics_len(), bank.box_bits(), bank.harmonics.len());
        let (a, span) = (2 * w, cells.len());
        let gb = BANK_COVECTOR_BITS;
        let spread = turn_spread(a);
        let one = 1i128 << MOVE_BITS;
        let ln2 = ln2_face();
        // O takes the output's covector against the read, and returns γ̂ = Oᵀ δx.
        let faces: Vec<&[i32]> = cells.iter().map(|c| c.read.as_slice()).collect();
        outer_sum(&mut g[bl.join..bl.join + w * 2 * dv], 2 * dv, out, &faces)?;
        // Each turn coordinate's harmonic index, for ∂φ_n/∂s_i = iπ n_i φ_n.
        let index: Vec<Vec<i128>> = (0..nn)
            .map(|mut n| {
                bank.harmonics
                    .iter()
                    .map(|&side| {
                        let i = (n % side) as i128;
                        n /= side;
                        i
                    })
                    .collect()
            })
            .collect();
        // Σ_n n_i Re(conj(G_n) i φ_n) = Σ_n n_i (G_im φ_re − G_re φ_im), times π and 2^(−σ), on 2^(−24).
        let turn_covector = |gphi: &[(i128, i128)], phase: &[(i128, i128)]| -> Result<Vec<i64>> {
            let mut sums = vec![0i128; turns];
            for ((&(gr, gi), &(pr, pi)), idx) in gphi.iter().zip(phase).zip(&index) {
                let v = release(gi * pr - gr * pi, MOVE_BITS);
                for (s, &k) in sums.iter_mut().zip(idx) {
                    *s += k * v;
                }
            }
            collect_exact(sums.into_iter().map(|s| fit64(release(release(reaches.half_turn * s, MOVE_BITS), gb - COVECTOR_BITS + spread))))
        };
        let mut gs = vec![(0i128, 0i128); dv * nn];
        let (mut key_cov, mut query_cov) = (vec![Vec::new(); span], vec![Vec::new(); span]);
        let (mut value_cov, mut gate_cov) = (vec![Vec::new(); span], vec![Vec::new(); span]);
        let mut hold_sum = 0i128;
        for i in (0..span).rev() {
            let cell = cells[i];
            let mut gamma = vec![0i64; 2 * dv];
            transposed(&t[bl.join..bl.join + w * 2 * dv], reaches.join, 2 * dv, &out[i], MATERIAL_BITS, &mut gamma)?;
            // The read: G_S += 2^(−m) γ̂ conj(φ_q), and G_φ(q) = 2^(−m) S_tᴴ γ̂.
            let after = written(&cell.before, &cell.written, &cell.key_phase, reaches.rho, false)?;
            let mut gq = vec![(0i128, 0i128); nn];
            for c in 0..dv {
                let (yr, yi) = (gamma[c] as i128, gamma[dv + c] as i128);
                if yr == 0 && yi == 0 {
                    continue;
                }
                for n in 0..nn {
                    let (pr, pi) = cell.query_phase[n];
                    let slot = &mut gs[c * nn + n];
                    slot.0 += release(yr * pr + yi * pi, MOVE_BITS + COVECTOR_BITS - gb + m);
                    slot.1 += release(yi * pr - yr * pi, MOVE_BITS + COVECTOR_BITS - gb + m);
                    let (sr, si) = (after[c * nn + n].0 as i128, after[c * nn + n].1 as i128);
                    gq[n].0 += sr * yr + si * yi;
                    gq[n].1 += sr * yi - si * yr;
                }
            }
            for v in &mut gq {
                *v = (release(v.0, STATE_BITS + COVECTOR_BITS - gb + m), release(v.1, STATE_BITS + COVECTOR_BITS - gb + m));
            }
            query_cov[i] = turn_covector(&gq, &cell.query_phase)?;
            // The write: G_S′ = ρ G_S; G_ρ = Re⟨G_S, S′⟩; w_c = Σ_n G′_cn φ_n(k).
            let primed = written(&cell.before, &cell.written, &cell.key_phase, reaches.rho, true)?;
            let mut rho_term = 0i128;
            for (&(gr, gi), &(sr, si)) in gs.iter().zip(&primed) {
                rho_term += gr * sr as i128 + gi * si as i128;
            }
            hold_sum += release(rho_term, STATE_BITS);
            for v in &mut gs {
                *v = (release(reaches.rho * v.0, MOVE_BITS), release(reaches.rho * v.1, MOVE_BITS));
            }
            let mut g_gate = 0i128;
            let mut g_news = Vec::with_capacity(dv);
            for c in 0..dv {
                let (mut wr, mut wi) = (0i128, 0i128);
                for (&(gr, gi), &(pr, pi)) in gs[c * nn..(c + 1) * nn].iter().zip(&cell.key_phase) {
                    wr += gr * pr - gi * pi;
                    wi += gr * pi + gi * pr;
                }
                let (wr, wi) = (release(wr, MOVE_BITS), release(wi, MOVE_BITS));
                let (er, ei) = cell.news[c];
                g_gate += release(er * wr + ei * wi, STATE_BITS);
                g_news.push((release(cell.gate * wr, MOVE_BITS), release(cell.gate * wi, MOVE_BITS)));
            }
            value_cov[i] = collect_exact(g_news.iter().map(|&(gr, _)| fit64(release(gr, gb - COVECTOR_BITS))))?;
            // ∂g/∂q = ln 2 · g (1 − g), on 2^(−30).
            let slope = release(release(ln2 * cell.gate, MOVE_BITS) * (one - cell.gate), MOVE_BITS);
            gate_cov[i] = vec![fit64(release(g_gate * slope, MOVE_BITS + gb - COVECTOR_BITS))?];
            // G_φ(k) = g G′ᴴ e − 2^(−m) S_(t−1)ᴴ G_e, then G_S ← G′ − 2^(−m) G_e conj(φ_k).
            let mut gk = vec![(0i128, 0i128); nn];
            for c in 0..dv {
                let (er, ei) = cell.news[c];
                let (hr, hi) = g_news[c];
                for n in 0..nn {
                    let (gr, gi) = gs[c * nn + n];
                    let (sr, si) = (cell.before[c * nn + n].0 as i128, cell.before[c * nn + n].1 as i128);
                    let first = (release(gr * er + gi * ei, STATE_BITS), release(gr * ei - gi * er, STATE_BITS));
                    let second = (release(sr * hr + si * hi, STATE_BITS + m), release(sr * hi - si * hr, STATE_BITS + m));
                    gk[n].0 += release(cell.gate * first.0, MOVE_BITS) - second.0;
                    gk[n].1 += release(cell.gate * first.1, MOVE_BITS) - second.1;
                    let (pr, pi) = cell.key_phase[n];
                    let slot = &mut gs[c * nn + n];
                    slot.0 -= release(hr * pr + hi * pi, MOVE_BITS + m);
                    slot.1 -= release(hi * pr - hr * pi, MOVE_BITS + m);
                }
            }
            key_cov[i] = turn_covector(&gk, &cell.key_phase)?;
        }
        // The hold: ∂ρ/∂h = ln 2 · ρ (1 − ρ), zero while ρ is held.
        if !reaches.held {
            let slope = release(release(ln2 * reaches.rho, MOVE_BITS) * (one - reaches.rho), MOVE_BITS);
            g[bl.hold] += release(hold_sum * slope, MOVE_BITS + gb - COVECTOR_BITS);
        }
        // The families' covectors against their faces, and the faces' covectors.
        let antecedents: Vec<&[i32]> = cells.iter().map(|c| c.antecedent.as_slice()).collect();
        let presents: Vec<Vec<i32>> = reads.iter().zip(inputs).map(|(r, x)| r.iter().chain(x.iter()).copied().collect()).collect();
        outer_sum(&mut g[bl.key..bl.key + turns * a], a, &key_cov, &antecedents)?;
        outer_sum(&mut g[bl.query..bl.query + turns * a], a, &query_cov, &presents)?;
        outer_sum(&mut g[bl.value..bl.value + dv * w], w, &value_cov, inputs)?;
        outer_sum(&mut g[bl.gate..bl.gate + w], w, &gate_cov, inputs)?;
        for i in 0..span {
            for (slot, &v) in g[bl.key_bias..bl.key_bias + turns].iter_mut().zip(&key_cov[i]) {
                *slot += v as i128;
            }
            for (slot, &v) in g[bl.query_bias..bl.query_bias + turns].iter_mut().zip(&query_cov[i]) {
                *slot += v as i128;
            }
            for (slot, &v) in g[bl.value_bias..bl.value_bias + dv].iter_mut().zip(&value_cov[i]) {
                *slot += v as i128;
            }
            g[bl.gate_bias] += gate_cov[i][0] as i128;
        }
        let (mut to_read, mut to_input) = (vec![vec![0i64; w]; span], vec![vec![0i64; w]; span]);
        let mut back = vec![0i64; a];
        let add = |dst: &mut [i64], src: &[i64]| -> Result<()> {
            for (d, &s) in dst.iter_mut().zip(src) {
                *d = fit64(*d as i128 + s as i128)?;
            }
            Ok(())
        };
        for i in 0..span {
            transposed(&t[bl.query..bl.query + turns * a], reaches.query, a, &query_cov[i], MATERIAL_BITS, &mut back)?;
            add(&mut to_read[i], &back[..w])?;
            add(&mut to_input[i], &back[w..])?;
            // The key at cell i reads cell i − 1's face; the opening's is held as given.
            if i > 0 {
                transposed(&t[bl.key..bl.key + turns * a], reaches.key, a, &key_cov[i], MATERIAL_BITS, &mut back)?;
                add(&mut to_read[i - 1], &back[..w])?;
                add(&mut to_input[i - 1], &back[w..])?;
            }
            let mut through = vec![0i64; w];
            transposed(&t[bl.value..bl.value + dv * w], reaches.value, w, &value_cov[i], MATERIAL_BITS, &mut through)?;
            add(&mut to_input[i], &through)?;
            transposed(&t[bl.gate..bl.gate + w], reaches.gate, w, &gate_cov[i], MATERIAL_BITS, &mut through)?;
            add(&mut to_input[i], &through)?;
        }
        Ok((to_read, to_input))
    }
}
