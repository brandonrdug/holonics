//! **The constitution: the store and its loci.**
//!
//! the material `θ` on `2^(−24)` by block, with the level's field and the glue where a level is grown; `to_text` and `from_text`
//! write and read it line by line (THE_ENGINE §5)
//!
//! Kind: the state every phase reads; no index of its own. Kernels: uploaded whole (`hnn/resident.rs`).
//! Lean: `Foundation/Standing` (retention as a quotient).
//! Atlas: `hnn.field-energy-opening-at-force`, `hnn.field-energy-width-law`, `tower.field-one-region`, `tower.field-pace`,
//! `tower.field-reach-on-clock`.
//! Records: `2026-11-01_THE_PROBLEM_IS_ONE_FIELD…`. The derivations' history is in the records; the items below keep their reasons.

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use rayon::prelude::*;

/// [definition; agent-inferred, November 1] **The field**: its declaration, its material `Θ`
/// (one vector, the families of [`Loci`] in order), the rings' resident faces and the
/// exponential's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constitution {
    pub declaration: Declaration,
    pub theta: Vec<i32>,
    pub(crate) layout: Loci,
    /// Each turned slot's period and its ring's phasors on `2^(−30)` (the residues a region within
    /// the reach reads).
    pub(crate) rings: Vec<(usize, Vec<(i64, i64)>)>,
    /// Each turned slot's skin decay `e^(−2π d/n)` on `2^(−30)` at every distance `d` within the
    /// reach ([`skin_decay`]).
    pub(crate) decays: Vec<Vec<i64>>,
    pub(crate) exponential: Exponential,
    /// The exponential's navigator at the material's grain (`2^(−24)`), the temperatures' face (§16.12): its
    /// first sixteen roots are [`Constitution::exponential`]'s.
    pub(crate) fine: Exponential,
    /// The half turn on `2^(−46)`, the turn's faces' navigator.
    pub(crate) pi: i128,
    /// The packets' level of a tower of scales ([`Constitution::scaled_up`]), none for a field on one scale.
    pub scale: Option<Box<Scale>>,
    /// [measurement; agent-inferred, November 6] Where set, every silent place runs its own per-blank rate past the last arrival
    /// too (the clock before §16.47's one-rate stretch), a declared comparison; not part of the state.
    pub per_blank_clock: bool,
    /// [definition; agent-inferred, November 6, the unified-theory reading of 10:31] Where set, **past the last arrival a silent
    /// place runs at the bare rate** (`κ = 1`, §16.28) and returns nothing: nothing arrives there, so no guessed duration
    /// drives its clock; between arrivals each blank keeps its expected duration (§16.44). Not part of the state.
    pub bare_stretch: bool,
    /// [measurement; agent-inferred, November 13, G161] Where set, **the read's mirror at uniform strength** `s_h` a head on `2^(−16)`: after
    /// each tick but the last, `x_j ← x_j − release(s_h μ_j, 16)` summed over the heads ([`Constitution::mirror_route`], every head's mirror read from
    /// the state the tick left), a reading at finite strength before the stage is a law; not part of the state, and no reverse reads it.
    pub mirror_strength: Option<Vec<i64>>,
    /// [measurement; the lead, November 16 23:00Z; the record of the lock, §4.5] Where set, **an open row carries its lock along the ticks**:
    /// with `γ` on `2^(−30)`, a listener's lock on source `j` at unit gain is `S^(k) = s^(k) + release(γ S^(k−1), 30)` (its fresh lock and what
    /// the row carried of the same source from the tick before), read through the temperature and the falloff as the fresh lock is,
    /// `z = T S − falloff`. A reading at a set `γ` of what a row that keeps its evidence does, before the stage is a law: not part of the
    /// state, and no reverse reads it.
    pub lock_carry: Option<i64>,
    /// [measurement; the lead, November 21, the leak's founding record's reads B1 to B5] Where set, **a lane leak at a set strength** `δ = n 2^(−b)`
    /// (`(n, b)`): after each tick, `x ← x − release(n x_began, b)` over every entry, `x_began` the state the tick began from, so the tick is
    /// `x ← (1 − δ) x + g` (the law founded at `δ = 0` is the built tick). A ruler's read of the leak before its stage is built: not part of the
    /// state, and no reverse reads it.
    pub ruler_leak: Option<(i64, u32)>,
    /// [measurement; the lead, November 21, the formal thread's check of 02:52Z] Where set with [`Constitution::ruler_leak`], the ruler's leak holds
    /// the pass's opening, `x ← x − release(n (x_began − x⁰), b)`, as the lane leak's law does.
    pub ruler_leak_hold: bool,
    /// [measurement; the lead, November 21, the formal thread's reads S1 and S2] Where set, **the circles' scan carries its residue**: the chain's
    /// state is kept 48 bits finer than the operand (`Q*`, the orbit released once at each read, `release.transported-residue`), and each site's
    /// operand is that orbit released to `2^(−16)`. A ruler's read of the scan's per-step section: not part of the state, and no reverse reads it.
    pub ruler_scan_carry: bool,
    /// [measurement; the lead, November 21, the reach] Where set, **a head's friction of distance as a ruler sets it**: entry `2 h + kind` (kind
    /// one a listener) on `2^(−16)` bits an octave, so a source `d` places from its receiver scores `ψ ⌊log₂ d⌋` lower on top of the falloff
    /// that stands (a turned head's octave of distance, a still head's octave of its class's count), and an octave's crowd `ψ` times its
    /// level lower. The finite difference of a code under it is the slope a friction founded at zero would have (atlas
    /// `wave.matched-friction-reach`), read before the stage is a law: not part of the state, and no reverse reads it.
    pub ruler_friction: Option<Vec<i64>>,
    /// [measurement; the lead, November 21, the precision pass's G-W3] Where set, **every state rounded to `2^(−g)` after each tick** of a
    /// passage read by two streams: `x ← release(x, 16 − g) ≪ (16 − g)` over every site, `x` on the state's `2^(−16)`. A ruler's read of how
    /// many of the state's places the code reads: not part of the state, and no reverse reads it.
    pub ruler_state_grain: Option<u32>,
    /// [measurement; the lead, November 22, the second precision pass's G-R4] Where set to `(j, k, relative)`, **lane `j` of every site's
    /// state rounded after each tick** of a passage read by two streams, the other lanes kept: a lane is the `j`-th of the
    /// `Declaration::lanes` equal blocks of a site's `D` coordinates, the block the readout reads as a ratio to its own power. With
    /// `relative` the lane is rounded to the power of two `k` places under that site's own lane's root mean square at that tick; without
    /// it, `k` places are dropped from the state's `2^(−16)` (a place under the point, or over it past 16). A ruler's read of how many of a
    /// lane's places the code reads and from which unit they count: not part of the state, and no reverse reads it.
    pub ruler_lane_grain: Option<(usize, u32, bool)>,
    /// [measurement; the lead, November 18, the frontier record §5] **What an open receiver hears far, as a ruler reads it**: `0`, the law
    /// (every definite site past its near field, each sharply, [`crate::contact::ClassLists::support`]); `1`, as a definite receiver hears
    /// (the definite members of its probe's classes sharply and each octave's crowd at its mean word); `2`, its near field alone; `4`, the
    /// law's hearing in one read with the level unheard; `3`, as `4` with every site hearing only what stands before it (the moments' and
    /// the opening's after rows absent, the support, the crowds and the strand's contacts one side), each site keeping its kind. A reading of
    /// which sources carry what a place at the frontier takes from many known places, before a read that compares every place at its
    /// frontier is built: not part of the state, and no reverse reads it (a forward under `1` or `2` is never returned).
    /// [November 18, the known stream's trial] Two more split what `3` leaves out: `5`, the law's hearing in one read with the level heard
    /// (so `4` less `5` is the level's part and `5` less the law the second read's); `6`, as `3` with the field's second read kept (each
    /// silent site opened on the shares of the face its first read gave it, which under one-sided hearing changes the open places alone).
    /// Two more read what the strand's own contacts carry to the frontier in a known stream: `7`, as `3` with every carry circle at rest;
    /// `8`, as `3` with every plain strand contact unmet. Forwards only. And `9`, as `3` with the strand's odd contacts facing the past
    /// ([`crate::field::Region::past`]), the forward a card's batch of such regions runs under.
    pub ruler_far: u8,
    /// [measurement; the lead, November 18, the record of the two streams §10] **How a ruler's forward hears the level**, to read by which
    /// path the level reaches a place at the frontier before the level is made one-sided: `0`, as the law or [`Constitution::ruler_far`]
    /// has it. Under the law's hearing in one read with the level heard (`ruler_far` at `5`): `1`, no open place takes a prolonged row
    /// (the level reaches it through the known places' states alone); `2`, every place reads the epoch before its own, the first epoch's
    /// places none (the delay a one-sided level has, by itself); `3`, the open places alone read the epoch before their own. Under a
    /// known stream (`ruler_far` at `3`): `4`, **the level made one-sided, as designed**: the news is the retarded opening's, a place is
    /// a site where no earlier place within a section of news carries news as large ([`crate::field::level_anchors_before`]), the
    /// level's ticks hear only the epochs before, and every place reads the epoch before its own; `5`, the law's level (its cut and
    /// each place's own epoch) over the known stream's ticks, which no stream could run (a known place then reads places after it
    /// through its epoch) and which bounds what a one-sided level can hand the frontier on the state read. Forwards only: no reverse
    /// reads it, and it is not part of the state.
    pub ruler_level: u8,
    /// [measurement; agent-inferred, November 13, G176; the ring record's §4] Where set, **the release marked in the opening at strength**
    /// `α` on `2^(−16)`: an open, silent site `s` with `marks[s]` (the face a read before gave it, its shares) opens on `E(∗) +
    /// release(α (release(Σ_c w_c E(c), 16) − E(∗)), 16)` in each encoding its row enters ([`Constitution::opening_term`]), and stays silent
    /// everywhere else (no voice, no moment, no clock of its own): the opening's part of the carried release, a ruler of the law's
    /// response along its strength before the strength is a part. Not part of the state, and no reverse reads it.
    pub mark: Option<(i64, Vec<Option<Shares>>)>,
}

impl Constitution {
    /// **The founding configuration** (agent-inferred, November 1), read from a declared exterior
    /// key stream (four bytes a key, a signed 32-bit integer read as a uniform draw on `[−1, 1)`):
    /// the encoding and both strand contacts uniform on `[−1, 1)` at every class, their unresolved
    /// rows at zero (a site whose class has not arrived carries no word); the key chart `W_k`, the
    /// value chart `V`, both pair drives `W_a, W_b` and the probe chart `W_p` uniform on `±√(3/D)`,
    /// each its own keyed draw, so each read of a unit-power face opens at unit power and a probe is
    /// founded apart from the key it meets (the module doc); the moment's chart into the face `C` uniform on `±√(3/2T)`
    /// at the turned modes (§16.22), drawn last; the current's return `O`, the contact's return `W_c`, the
    /// readout and every bias at zero, so the field opens on the flat face and each tick on the
    /// identity.
    pub fn found(declaration: Declaration, keys: &[u8]) -> Result<Self> {
        declaration.admit()?;
        if declaration.carry > 0 {
            // [theory, November 11 17:25] The circles are grown onto a founded field, their `W` columns at zero ([`Constitution::with_carry`]).
            return refuse("a founding with carry circles (they are grown onto a founded field, Constitution::with_carry)");
        }
        if declaration.triads > 0 {
            // [theory, November 12, the triad record §4] The triads are grown onto a field, their return at zero ([`Constitution::with_triads`]).
            return refuse("a founding with triads (they are grown onto a founded field, Constitution::with_triads)");
        }
        let layout = Loci::new(&declaration);
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
        for start in [layout.enc, layout.before, layout.after] {
            uniform(&mut theta[start..start + a * dw], 1, 1, FACE_BITS)?;
        }
        // √(3/D) as (√3·2^16)/(√D·2^16), each square root on 2^(−16).
        let (three, dd) = chart_scale(dw);
        for start in [layout.q, layout.v] {
            uniform(&mut theta[start..start + m2 * dw], three, dd, MATERIAL_BITS)?;
        }
        for start in [layout.a, layout.b] {
            uniform(&mut theta[start..start + f * dw], three, dd, MATERIAL_BITS)?;
        }
        // [agent-inferred, November 2, §16.19] Every receiver's probe is its own keyed draw, after the key's, the value's
        // and the pair drives' (so their draws stand as before). Why not the key itself (the founding until
        // November 2): a probe equal to its key meets, from the founding, the sites whose word is its own, and so
        // the crowned contact was handed to the field rather than located by it.
        uniform(&mut theta[layout.probe..layout.probe + m2 * dw], three, dd, MATERIAL_BITS)?;
        // [agent-inferred, November 2, §16.22] The moment's chart into the face is a read of the moments, drawn last (so
        // every earlier draw stands) at `±√(3/2T)` over its `2T` moment reals, so a moment at unit power opens a unit-power
        // term; a still mode's column carries no moment and opens at zero. The moment encodings open at zero, so the
        // founding's faces are as before, and the chart gives the encodings a covector from the face's first deposit.
        let tm = declaration.moment_modes();
        if tm > 0 {
            let (three_m, dd_m) = chart_scale(2 * tm);
            let n = declaration.modes;
            let carries: Vec<bool> = (0..m2).map(|k| declaration.carries_moment((k % declaration.complex()) / n)).collect();
            for o in 0..dw {
                for (k, &on) in carries.iter().enumerate() {
                    if on {
                        uniform(&mut theta[layout.moment_face + o * m2 + k..layout.moment_face + o * m2 + k + 1], three_m, dd_m, MATERIAL_BITS)?;
                    }
                }
            }
        }
        // The temperatures open at their derived gains (§15.10), `T = 2^(−β)`, held as `log₂ T = −β` (§16.12).
        for h in 0..declaration.heads {
            for (kind, beta) in [(0usize, declaration.score_shift()), (1, declaration.listen_shift())] {
                theta[layout.temper + 2 * h + kind] = fit32((-beta as i128) << MATERIAL_BITS, "a founded temperature outgrew its 32-bit carrier")?;
            }
        }
        Ok(Self::with_theta(declaration, theta))
    }

    /// A head's temperature for a receiver of `kind` (0 a class receiver, 1 a listener) on `2^(−24)`, read from
    /// its logarithm ([`temperature_of`]).
    pub fn temper(&self, h: usize, listens: bool) -> Result<i128> {
        temperature_of(self.theta[self.layout.temper + 2 * h + usize::from(listens)], &self.fine)
    }

    /// [definition; the lead, November 21] **A head's friction of distance** for a receiver of `kind` (one a listener) on `2^(−16)` bits an
    /// octave ([`Declaration::friction`]; zero where the field has none), with a ruler's beside it where one is set
    /// ([`Constitution::ruler_friction`]).
    pub fn friction(&self, h: usize, listens: bool) -> i128 {
        let k = 2 * h + usize::from(listens);
        let law = if self.declaration.friction { i128::from(self.theta[self.layout.friction + k]) } else { 0 };
        law + self.ruler_friction.as_ref().map_or(0, |f| i128::from(f[k]))
    }

    /// Each turned slot's skin decay on `2^(−30)` at every distance within the reach (a
    /// realization's resident face).
    pub fn decays(&self) -> &[Vec<i64>] {
        &self.decays
    }

    /// [definition; agent-inferred, November 1] **The skin decay of local mode `l` of head `h` across
    /// `d` sites** (the dispersing field's §12) and the bits it is carried on: `e^(−2π d/n_m)` on
    /// `2^(−30)` in a turned head, one e-fold a radian of turn; in a still head (period infinite) the
    /// exact `1`, carried on no bits, so a still head's sums are the bare ones (the same integers a
    /// `2^30` on `2^(−30)` would release to).
    pub(crate) fn decay(&self, h: usize, l: usize, d: usize) -> (i128, u32) {
        let dd = &self.declaration;
        let set = h % dd.frames;
        if set < dd.still || dd.is_depth(h) {
            return (1, 0);
        }
        (self.decays[l * (dd.frames - dd.still) + set - dd.still][d] as i128, MOVE_BITS)
    }

    /// [definition; agent-inferred, November 2] **The skin across a pair** (§16, Law 1): local mode `l` of head
    /// `h` between sites `i` and `j`, `e^(−2π |σ_h(i) − σ_h(j)|/n)` on a head that reads a pace (its byte distance's
    /// [`Constitution::decay`] where the pace is plain), the exact `1` on a still head.
    pub(crate) fn pair_decay(&self, paces: &Paces, h: usize, l: usize, i: usize, j: usize) -> (i128, u32) {
        self.pair_decay_placed(paces, h, l, i, j, i.abs_diff(j))
    }

    /// [`Constitution::pair_decay`] of a pair whose clocks are `paces`' at `i` and `j` and whose places stand `gap` apart (their
    /// indices' distance, but for an open place of a strand's second stream).
    pub(crate) fn pair_decay_placed(&self, paces: &Paces, h: usize, l: usize, i: usize, j: usize, gap: usize) -> (i128, u32) {
        match paces.row.get(h).copied().flatten() {
            Some(p) if !paces.plain[p] && !self.declaration.is_depth(h) => (self.skin(self.slot(h, l), paces.sigma[p][i] as i128 - paces.sigma[p][j] as i128) as i128, MOVE_BITS),
            _ => self.decay(h, l, gap),
        }
    }

    /// [the boundary chart] The skin across a pair whose receiver `i` stands on the clock it holds before its own symbol arrives (`rx`) and
    /// whose source `j` stands on its own (`paces`): [`Constitution::pair_decay`] between the two clocks.
    pub(crate) fn pair_decay_between(&self, rx: &Paces, i: usize, paces: &Paces, j: usize, h: usize, l: usize) -> (i128, u32) {
        match paces.row.get(h).copied().flatten() {
            Some(p) if !paces.plain[p] && !self.declaration.is_depth(h) => (self.skin(self.slot(h, l), rx.sigma[p][i] as i128 - paces.sigma[p][j] as i128) as i128, MOVE_BITS),
            _ => self.decay(h, l, i.abs_diff(j)),
        }
    }

    /// The skin of an octave's crowd from site `i` (§14.10, §16): its byte distance `2^ℓ`'s, or on a paced head
    /// the skin to the place `2^ℓ` away on the crowd's side (inside the region wherever the octave is).
    pub(crate) fn octave_decay(&self, paces: &Paces, h: usize, l: usize, i: usize, level: u32, right: bool) -> (i128, u32) {
        match paces.row.get(h).copied().flatten() {
            Some(p) if !paces.plain[p] && !self.declaration.is_depth(h) => {
                let k = if right { i + (1 << level) } else { i - (1 << level) };
                (self.skin(self.slot(h, l), paces.sigma[p][i] as i128 - paces.sigma[p][k] as i128) as i128, MOVE_BITS)
            }
            _ => self.decay(h, l, 1 << level),
        }
    }

    /// The material's families, each `(start, len, grain)`.
    pub fn families(&self) -> &[(usize, usize, u32)] {
        &self.layout.families
    }

    /// The material's layout.
    pub fn layout(&self) -> &Loci {
        &self.layout
    }

    /// The field as text: its head line, then its material on one line.
    /// The field as text: its declaration and its material, each on one line; a level adds a line `level H split`, the
    /// level's field's lines and the glue's one.
    pub fn to_text(&self) -> String {
        let theta: Vec<String> = self.theta.iter().map(i32::to_string).collect();
        let mut out = format!("{}\n{}\n", self.declaration.to_text(), theta.join(" "));
        if let Some(s) = &self.scale {
            let glue: Vec<String> = s.glue.iter().map(i32::to_string).collect();
            out.push_str(&format!("level {} {}\n{}{}\n", s.harmonics, s.split, s.coarse.to_text(), glue.join(" ")));
        }
        out
    }

    pub fn from_text(text: &str) -> Result<Self> {
        Self::from_lines(&mut text.lines().peekable())
    }

    /// A field read from its text's lines ([`Constitution::to_text`]), the lines after it left unread.
    pub fn from_lines<'a>(lines: &mut std::iter::Peekable<impl Iterator<Item = &'a str>>) -> Result<Self> {
        let d = Declaration::from_text(lines.next().unwrap_or(""))?;
        let theta = read_numbers::<i32>(lines.next())?;
        if theta.len() != Loci::new(&d).len {
            return refuse("a field's material that is not its declaration's length");
        }
        let mut field = Self::with_theta(d, theta);
        // [November 13, G145] A `scale` line held the packets of November 3, a superseded prototype: it is refused, never read as a level.
        if lines.peek().is_some_and(|l| l.starts_with("scale ")) {
            return refuse("a packets' scale (retired November 13 for the level above): found the level again");
        }
        if let Some(head) = lines.peek().copied().filter(|l| l.starts_with("level ")) {
            lines.next();
            let words: Vec<usize> = head.split(' ').skip(1).map(|w| w.parse::<usize>().map_err(|_| TowerError::Refused("a level's line that is not two counts"))).collect::<Result<_>>()?;
            let [harmonics, split] = words[..] else { return refuse("a level's line that is not two counts") };
            let coarse = Self::from_lines(lines)?;
            let glue = read_numbers::<i32>(lines.next())?;
            let (.., len) = crate::field::scale::glue_len(harmonics, field.declaration.width, coarse.declaration.width);
            let before = crate::field::scale::glue_before_len(harmonics, field.declaration.width, coarse.declaration.width);
            if (glue.len() != len && glue.len() != len + before) || harmonics == 0 || split == 0 || split >= field.declaration.ticks || !field.declaration.opening {
                return refuse("a level's glue that is not its declaration's length, a split outside the ticks, or a field without the opening's block");
            }
            field.scale = Some(Box::new(Scale { harmonics, split, coarse, glue }));
        }
        Ok(field)
    }
}

pub(crate) fn read_numbers<T: std::str::FromStr>(line: Option<&str>) -> Result<Vec<T>> {
    let line = line.ok_or(TowerError::Refused("a field's text ended before its material"))?;
    if line.is_empty() {
        return Ok(Vec::new());
    }
    line.split(' ').map(|w| w.parse::<T>().map_err(|_| TowerError::Refused("a field's material that is not a number"))).collect()
}
