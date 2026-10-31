//! **The duplex: the tower read from both sides, its two strands meeting at every place** (#405,
//! #404).
//!
//! [definition; agent-inferred, October 23] Why it is built. On a terrain of sums, differences and
//! products with operand pairs held out, the forward tower locates a result's size, its leading
//! face and its units crossing, and is blind where the most crossings land: a product's tens digit
//! costs 3.3 bits, unmoved from 12 passes to 24 (record
//! `2026-10-23_ON_A_TERRAIN_OF_INTERACTING_DIGITS_…`). The base's cheap faces (atlas
//! `radix.cheap-faces`: the digit sum on the ring of `b − 1`, the alternating sum on the ring of
//! `b + 1`) are carry-free: each is one crossing on a small ring, and with the size and the units
//! they fix the word. A reader that codes each place from its left meets a face of the whole word
//! only at the word's last place, which the units crossing already codes, so those faces never pay:
//! the products it writes match the truth modulo 9 and 11 at chance. The generation law
//! (THE_MACHINE, "Generation and reception") refines one joint field. The duplex reads that field:
//! a second strand reads the same passage backward, and the two meet at each place, so each class
//! is coded given everything on both sides.
//!
//! ```text
//! forward strand  F reads u_0 … u_(T−1) from its carried state; its top x_F(t−1) has read u_(<t)
//! reverse strand  R reads u_T … u_1 from rest; its top x_R(t+1) has read u_(>t)
//! meeting         z_t = z_F(t) + z_R(t) + U max(W [x_F(t−1); x_R(t+1)] + b, 0) + c
//!                 z_F, z_R each strand's own face at the place, read from its top: their sum is
//!                 the product of the two receivers' faces; the rectifying contacts take the
//!                 conjunction neither strand carries alone
//! code            each strand codes its own next class; the meeting codes u_t for 0 < t < T
//! covector        δz_t = p̂_t − [· = u_t] reaches the meeting's material, both strands' readouts and
//!                 each strand's top, whose reverse scan carries it into that strand
//! certificate     the section reread codes strictly fewer bits over all three faces
//! ```
//!
//! The meeting's readout opens at zero, so the duplex opens on the product of its strands' faces.
//! The forward strand releases (nothing lies to its right); the meeting refines a release, each
//! place redrawn from its meeting given all the others, until a sweep changes nothing. A redrawn
//! place moves only the reading's own hypothetical state; it is never received as testimony.
//!
//! **Not claimed.** The reverse strand opens at rest at each section's end, so its reach is the
//! section. The meeting does not choose a release's length.
use super::*;

/// The meeting's material: the contacts `W` (`f × 2d`) and their bias, the readout `U` (`A × f`)
/// and its bias.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct MeetingLayout {
    contact: usize,
    contact_bias: usize,
    readout: usize,
    readout_bias: usize,
    len: usize,
}

impl MeetingLayout {
    fn new(alphabet: usize, width: usize, contacts: usize) -> Self {
        let contact_bias = contacts * 2 * width;
        let readout = contact_bias + contacts;
        let readout_bias = readout + alphabet * contacts;
        Self { contact: 0, contact_bias, readout, readout_bias, len: readout_bias + alphabet }
    }

    /// `(start, length, grain)` of each family.
    fn families(&self) -> [(usize, usize, u32); 4] {
        [
            (self.contact, self.contact_bias - self.contact, MATERIAL_BITS),
            (self.contact_bias, self.readout - self.contact_bias, FACE_BITS),
            (self.readout, self.readout_bias - self.readout, MATERIAL_BITS),
            (self.readout_bias, self.len - self.readout_bias, FACE_BITS),
        ]
    }
}

/// The key draws a tower's founding reads (`Tower::found`): the encoding, and each level's push,
/// read and contacts.
fn founding_draws(d: &TowerDeclaration) -> usize {
    d.alphabet * d.width + d.levels * (4 * d.modes * d.width + d.contacts * d.width)
}

/// [definition; agent-inferred, October 23] **The duplex**: two strands of one declaration and
/// their meeting.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Duplex {
    pub forward: Tower,
    pub reverse: Tower,
    /// The meeting's rectifying contacts a place.
    pub contacts: usize,
    /// The meeting's material, every family in one vector on its grain.
    pub meeting: Vec<i32>,
    layout: MeetingLayout,
    exponential: Exponential,
}

/// One place's meeting: the strands' tops read together, the contacts' drive and conduction, and
/// the face.
#[derive(Clone, Debug)]
struct Meeting {
    input: Vec<i32>,
    drive: Vec<i32>,
    conduct: Vec<i32>,
    face: TowerFace,
}

/// One stream's section read by the duplex: the forward's cells and end state, the reverse's cells
/// (from rest, over the section backward) and the meetings at the interior places.
struct Strands {
    forward: Vec<Cell>,
    end: TowerState,
    reverse: Vec<Cell>,
    meetings: Vec<Meeting>,
}

impl Tower {
    /// The face's exponents `z = U x + c` read at a top, on `2^(−16)`.
    fn exponents(&self, top: &[i32], reaches: &Reaches) -> Result<Vec<i64>> {
        if self.pair.is_some() {
            return refuse("the duplex reads its towers' faces off their tops, which a pair face does not read alone");
        }
        if self.mutual.is_some() {
            return refuse("the duplex reads its towers' faces through their readouts, which a mutual contact replaces");
        }
        let (a, w) = (self.declaration.alphabet, self.declaration.width);
        let (ro, rb) = (self.layout.readout, self.layout.readout_bias);
        let mut z = vec![0i64; a];
        affine(&self.theta[ro..ro + a * w], reaches.readout, w, top, Some(&self.theta[rb..rb + a]), MATERIAL_BITS, MATERIAL_BITS, &mut z)?;
        Ok(z)
    }

    /// The face of the next class after `u` arrives and the top it is read from, the state moved.
    pub fn advance_top(&self, state: &mut TowerState, u: usize) -> Result<(TowerFace, Vec<i32>)> {
        let reaches = self.reaches();
        let cell = self.step(state, u, &reaches)?;
        Ok((cell.face, cell.top))
    }
}

/// A duplex section's receipt: each face's code before the deposit (on `2^(−20)` bits) and the
/// classes the forward and the meeting code, the whole code after, the halvings the certificate
/// took and whether a deposit was admitted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DuplexReceipt {
    pub forward_cells: usize,
    pub meeting_cells: usize,
    pub forward_before: i64,
    pub reverse_before: i64,
    pub meeting_before: i64,
    pub code_after: i64,
    pub halvings: u32,
    pub deposited: bool,
}

impl DuplexReceipt {
    pub fn code_before(&self) -> i64 {
        self.forward_before + self.reverse_before + self.meeting_before
    }
}

impl Duplex {
    /// **The founding** (agent-inferred, October 23): the forward strand from the key stream as a
    /// tower's, the reverse from the keys after it, the meeting's contacts after those by `√(6/2d)`
    /// (a level's contacts' scale over its doubled input), its readout and biases at zero, so the
    /// duplex opens on the product of its strands' faces.
    pub fn found(declaration: TowerDeclaration, contacts: usize, keys: &[u8]) -> Result<Self> {
        if contacts == 0 {
            return refuse("a meeting needs a contact");
        }
        let used = 4 * founding_draws(&declaration);
        let forward = Tower::found(declaration, keys)?;
        let reverse = Tower::found(declaration, keys.get(used..).unwrap_or(&[]))?;
        let layout = MeetingLayout::new(declaration.alphabet, declaration.width, contacts);
        let mut meeting = vec![0i32; layout.len];
        let words = keys.get(2 * used..2 * used + 4 * layout.contact_bias).ok_or(TowerError::Refused("fewer key bytes than the founding reads"))?;
        // √(6/2d) as (√6·2^16)/(√(2d)·2^16): a rectifier passes half its drive.
        let six = (6u128 << 32).isqrt();
        let dd = (((2 * declaration.width) as u128) << 32).isqrt();
        for (v, word) in meeting[..layout.contact_bias].iter_mut().zip(words.chunks_exact(4)) {
            let k = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i128;
            *v = fit32((k * ((six << MATERIAL_BITS) / dd) as i128) >> 31, "a founded value outgrew its 32-bit carrier")?;
        }
        Ok(Self { forward, reverse, contacts, meeting, layout, exponential: Exponential::new(FACE_BITS) })
    }

    /// The material's extent: the forward's, the reverse's, the meeting's.
    fn len(&self) -> usize {
        self.forward.theta.len() + self.reverse.theta.len() + self.meeting.len()
    }

    /// Every family of the material in the one vector, with its grain.
    fn families(&self) -> Vec<(usize, usize, u32)> {
        let nf = self.forward.theta.len();
        let nr = self.reverse.theta.len();
        let mut out = self.forward.layout.families.clone();
        out.extend(self.reverse.layout.families.iter().map(|&(s, l, g)| (s + nf, l, g)));
        out.extend(self.layout.families().iter().map(|&(s, l, g)| (s + nf + nr, l, g)));
        out
    }

    /// `max |W|` and `max |U|` of the meeting.
    fn reach_meeting(&self) -> [u64; 2] {
        let l = &self.layout;
        [reach(&self.meeting[l.contact..l.contact_bias]), reach(&self.meeting[l.readout..l.readout_bias])]
    }

    fn meet(&self, top_f: &[i32], top_r: &[i32], rf: &Reaches, rr: &Reaches, wmax: [u64; 2]) -> Result<Meeting> {
        let d = &self.forward.declaration;
        let (a, w, f) = (d.alphabet, d.width, self.contacts);
        let (l, m) = (&self.layout, &self.meeting);
        let mut input = Vec::with_capacity(2 * w);
        input.extend_from_slice(top_f);
        input.extend_from_slice(top_r);
        let mut drive = vec![0i64; f];
        affine(&m[l.contact..l.contact_bias], wmax[0], 2 * w, &input, Some(&m[l.contact_bias..l.readout]), MATERIAL_BITS, MATERIAL_BITS, &mut drive)?;
        let drive = to32(&drive, "a meeting's drive outgrew its 32-bit carrier")?;
        let conduct: Vec<i32> = drive.iter().map(|&v| v.max(0)).collect();
        let mut z = vec![0i64; a];
        affine(&m[l.readout..l.readout_bias], wmax[1], f, &conduct, Some(&m[l.readout_bias..l.len]), MATERIAL_BITS, MATERIAL_BITS, &mut z)?;
        let zf = self.forward.exponents(top_f, rf)?;
        let zr = self.reverse.exponents(top_r, rr)?;
        let z: Vec<i64> = collect_exact(z.iter().zip(&zf).zip(&zr).map(|((a, b), c)| fit64(*a as i128 + *b as i128 + *c as i128)))?;
        let zmax = *z.iter().max().expect("a nonempty alphabet");
        let masses: Vec<u128> = z.iter().map(|&v| self.exponential.below_one((v - zmax) as i128)).collect();
        let total = masses.iter().sum();
        Ok(Meeting { input, drive, conduct, face: TowerFace { masses, total } })
    }

    /// The meeting's face at a place, from the forward top that has read what lies before it and
    /// the reverse top that has read what lies after it.
    pub fn meeting_face(&self, top_f: &[i32], top_r: &[i32]) -> Result<TowerFace> {
        Ok(self.meet(top_f, top_r, &self.forward.reaches(), &self.reverse.reaches(), self.reach_meeting())?.face)
    }

    /// [definition; agent-inferred, October 23] **The refinement of a release.** The forward
    /// strand has read `head` from rest and released `release`, which the class `tail` closes.
    /// Each sweep redraws every place of the release, left to right, from its meeting: the forward
    /// top that has read the head and the release so far (this sweep's redraws included), the
    /// reverse top that has read, from rest, the tail and the release after the place. The draw
    /// is the exterior's (its keys, and any conditioning it declares, such as the release's
    /// length). The sweeps stop when one changes nothing, or after `sweeps`; returned are the
    /// sweeps run and whether the last changed nothing. A sweep that changes nothing is a fixed
    /// point of the draws taken, not a certificate that the conditionals share one joint law.
    pub fn refine(
        &self,
        head: &[usize],
        release: &mut [usize],
        tail: usize,
        sweeps: usize,
        draw: &mut dyn FnMut(&TowerFace) -> Result<usize>,
    ) -> Result<(usize, bool)> {
        if head.is_empty() || release.is_empty() {
            return refuse("a refinement needs a head and a release");
        }
        let (rf, rr, wmax) = (self.forward.reaches(), self.reverse.reaches(), self.reach_meeting());
        let mut opened = self.forward.rest();
        let mut opened_top = Vec::new();
        for &u in head {
            opened_top = self.forward.step(&mut opened, u, &rf)?.top;
        }
        let n = release.len();
        for sweep in 0..sweeps {
            // tops_r[k] has read the tail and release[k + 1..].
            let mut r = self.reverse.rest();
            let mut tops_r = vec![Vec::new(); n];
            tops_r[n - 1] = self.reverse.step(&mut r, tail, &rr)?.top;
            for k in (0..n - 1).rev() {
                tops_r[k] = self.reverse.step(&mut r, release[k + 1], &rr)?.top;
            }
            let (mut f, mut top) = (opened.clone(), opened_top.clone());
            let mut changed = false;
            for k in 0..n {
                let face = self.meet(&top, &tops_r[k], &rf, &rr, wmax)?.face;
                let class = draw(&face)?;
                if class >= face.masses.len() {
                    return refuse("a drawn class outside the alphabet");
                }
                changed |= class != release[k];
                release[k] = class;
                top = self.forward.step(&mut f, class, &rf)?.top;
            }
            if !changed {
                return Ok((sweep + 1, true));
            }
        }
        Ok((sweeps, false))
    }

    fn read_stream(&self, open: &TowerState, classes: &[usize], rf: &Reaches, rr: &Reaches, wmax: [u64; 2]) -> Result<Strands> {
        let t = classes.len() - 1;
        let mut end = open.clone();
        let forward = self.forward.forward(&mut end, classes, rf)?;
        let backward: Vec<usize> = classes.iter().rev().copied().collect();
        let mut rest = self.reverse.rest();
        let reverse = self.reverse.forward(&mut rest, &backward, rr)?;
        // Reverse cell j has read u_T … u_(T−j): the place t = T − 1 − j lies just before it.
        let meetings = collect_exact((1..t).map(|p| self.meet(&forward[p - 1].top, &reverse[t - 1 - p].top, rf, rr, wmax)))?;
        Ok(Strands { forward, end, reverse, meetings })
    }

    /// Each coded class's mass and its face's total: the forward's, the reverse's, the meeting's.
    fn faces(strands: &Strands, classes: &[usize]) -> Vec<(u128, u128)> {
        let t = classes.len() - 1;
        let f = strands.forward.iter().enumerate().map(|(i, c)| (c.face.masses[classes[i + 1]], c.face.total));
        let r = strands.reverse.iter().enumerate().map(|(j, c)| (c.face.masses[classes[t - 1 - j]], c.face.total));
        let m = strands.meetings.iter().enumerate().map(|(i, c)| (c.face.masses[classes[i + 1]], c.face.total));
        f.chain(r).chain(m).collect()
    }

    /// The three faces' codes on `2^(−20)` bits.
    fn codes(strands: &Strands, classes: &[usize]) -> [i64; 3] {
        let t = classes.len() - 1;
        [
            strands.forward.iter().enumerate().map(|(i, c)| c.face.code(classes[i + 1])).sum(),
            strands.reverse.iter().enumerate().map(|(j, c)| c.face.code(classes[t - 1 - j])).sum(),
            strands.meetings.iter().enumerate().map(|(i, c)| c.face.code(classes[i + 1])).sum(),
        ]
    }

    /// One stream's covector of the whole material, on each family's natural grain (the forward's,
    /// then the reverse's, then the meeting's).
    fn covector(&self, open: &TowerState, classes: &[usize], strands: &Strands, rf: &Reaches, rr: &Reaches, wmax: [u64; 2]) -> Result<Vec<i128>> {
        let d = &self.forward.declaration;
        let (a, w, f) = (d.alphabet, d.width, self.contacts);
        let t = classes.len() - 1;
        let (l, m) = (&self.layout, &self.meeting);
        let (fo, fb) = (self.forward.layout.readout, self.forward.layout.readout_bias);
        let (ro, rb) = (self.reverse.layout.readout, self.reverse.layout.readout_bias);
        let mut gm = vec![0i128; l.len];
        let mut joined_f = vec![vec![0i64; w]; t];
        let mut joined_r = vec![vec![0i64; w]; t];
        let mut dzs: Vec<Vec<i64>> = Vec::with_capacity(strands.meetings.len());
        let mut das: Vec<Vec<i64>> = Vec::with_capacity(strands.meetings.len());
        for (i, meeting) in strands.meetings.iter().enumerate() {
            let p = i + 1;
            let target = classes[p];
            let face = &meeting.face;
            let dz: Vec<i64> = (0..a)
                .map(|c| {
                    let q = ((face.masses[c] << COVECTOR_BITS) + face.total / 2) / face.total;
                    q as i64 - if c == target { 1i64 << COVECTOR_BITS } else { 0 }
                })
                .collect();
            let mut dv = vec![0i64; f];
            transposed(&m[l.readout..l.readout_bias], wmax[1], f, &dz, MATERIAL_BITS, &mut dv)?;
            let da: Vec<i64> = dv.iter().zip(&meeting.drive).map(|(&v, &drive)| if drive > 0 { v } else { 0 }).collect();
            let mut dx = vec![0i64; 2 * w];
            transposed(&m[l.contact..l.contact_bias], wmax[0], 2 * w, &da, MATERIAL_BITS, &mut dx)?;
            let mut back_f = vec![0i64; w];
            transposed(&self.forward.theta[fo..fo + a * w], rf.readout, w, &dz, MATERIAL_BITS, &mut back_f)?;
            let mut back_r = vec![0i64; w];
            transposed(&self.reverse.theta[ro..ro + a * w], rr.readout, w, &dz, MATERIAL_BITS, &mut back_r)?;
            for k in 0..w {
                joined_f[p - 1][k] = fit64(dx[k] as i128 + back_f[k] as i128)?;
                joined_r[t - 1 - p][k] = fit64(dx[w + k] as i128 + back_r[k] as i128)?;
            }
            for (slot, &v) in gm[l.readout_bias..l.len].iter_mut().zip(&dz) {
                *slot += v as i128;
            }
            for (slot, &v) in gm[l.contact_bias..l.readout].iter_mut().zip(&da) {
                *slot += v as i128;
            }
            dzs.push(dz);
            das.push(da);
        }
        let conducts: Vec<&[i32]> = strands.meetings.iter().map(|m| m.conduct.as_slice()).collect();
        let inputs: Vec<&[i32]> = strands.meetings.iter().map(|m| m.input.as_slice()).collect();
        outer_sum(&mut gm[l.readout..l.readout_bias], f, &dzs, &conducts)?;
        outer_sum(&mut gm[l.contact..l.contact_bias], 2 * w, &das, &inputs)?;
        let mut gf = self.forward.reverse_joined(open, &strands.forward, classes, Some(&joined_f), None, None, None, None)?.0;
        let tops_f: Vec<&[i32]> = (1..t).map(|p| strands.forward[p - 1].top.as_slice()).collect();
        outer_sum(&mut gf[fo..fo + a * w], w, &dzs, &tops_f)?;
        let backward: Vec<usize> = classes.iter().rev().copied().collect();
        let mut gr = self.reverse.reverse_joined(&self.reverse.rest(), &strands.reverse, &backward, Some(&joined_r), None, None, None, None)?.0;
        let tops_r: Vec<&[i32]> = (1..t).map(|p| strands.reverse[t - 1 - p].top.as_slice()).collect();
        outer_sum(&mut gr[ro..ro + a * w], w, &dzs, &tops_r)?;
        for dz in &dzs {
            for (c, &v) in dz.iter().enumerate() {
                gf[fb + c] += v as i128;
                gr[rb + c] += v as i128;
            }
        }
        gf.extend(gr);
        gf.extend(gm);
        Ok(gf)
    }

    /// The covector on the deposit's grain `2^(−32)`, the strands' moves in their chart.
    fn to_step_grain(&self, g: &mut [i128]) {
        let nf = self.forward.theta.len();
        let nr = self.reverse.theta.len();
        let (gf, rest) = g.split_at_mut(nf);
        let (gr, gm) = rest.split_at_mut(nr);
        self.forward.to_step_grain(gf);
        self.forward.to_move_chart(gf);
        self.reverse.to_step_grain(gr);
        self.reverse.to_move_chart(gr);
        for (start, len, grain) in self.layout.families() {
            for v in &mut gm[start..start + len] {
                *v = if grain == MATERIAL_BITS { release(*v, COVECTOR_BITS + FACE_BITS - STEP_BITS) } else { *v << (STEP_BITS - COVECTOR_BITS) };
            }
        }
    }

    /// The material moved by `step` released `halvings` coarser, the moves in their chart and back
    /// inside the margin; whether anything moved.
    fn move_by(&mut self, step: &[i128], halvings: u32) -> Result<bool> {
        let nf = self.forward.theta.len();
        let nr = self.reverse.theta.len();
        let mut moved = false;
        for (tower, offset) in [(&mut self.forward, 0), (&mut self.reverse, nf)] {
            let s = &step[offset..offset + tower.theta.len()];
            for &(start, len, grain) in &tower.layout.families.clone() {
                if grain == MOVE_BITS {
                    continue;
                }
                for i in start..start + len {
                    let released = release(s[i], halvings);
                    moved |= released != 0;
                    tower.theta[i] = fit32(tower.theta[i] as i128 - released, "a deposited parameter outgrew its 32-bit carrier")?;
                }
            }
            moved |= tower.move_by_chart(s, halvings)?;
            tower.project();
        }
        for (v, &s) in self.meeting.iter_mut().zip(&step[nf + nr..]) {
            let released = release(s, halvings);
            moved |= released != 0;
            *v = fit32(*v as i128 - released, "a deposited parameter outgrew its 32-bit carrier")?;
        }
        Ok(moved)
    }

    /// A frozen reading of a part, the forward from rest: the forward's code of `classes[1..]` and
    /// the meeting's code of `classes[1..n − 1]`, each entry on `2^(−20)` bits. The reverse opens
    /// at rest at the part's end and, when a section is declared, at every multiple of it, as a
    /// learner's sections open it. Only the strands' tops are held, so a long part reads in the
    /// memory of its tops.
    pub fn read_cells(&self, classes: &[usize], section: Option<usize>) -> Result<(Vec<i64>, Vec<i64>)> {
        let n = classes.len();
        if n < 3 || section == Some(0) {
            return refuse("a duplex reading needs three classes and a nonempty section");
        }
        let (rf, rr, wmax) = (self.forward.reaches(), self.reverse.reaches(), self.reach_meeting());
        let mut s = self.forward.rest();
        let mut forward = Vec::with_capacity(n - 1);
        let mut tops_f = Vec::with_capacity(n - 1);
        for i in 0..n - 1 {
            let cell = self.forward.step(&mut s, classes[i], &rf)?;
            forward.push(cell.face.code(classes[i + 1]));
            tops_f.push(cell.top);
        }
        // tops_r[p] has read u_(n−1) … u_p.
        let mut r = self.reverse.rest();
        let mut tops_r = vec![Vec::new(); n];
        for p in (2..n).rev() {
            if section.is_some_and(|t| p % t == 0) && p != n - 1 {
                r = self.reverse.rest();
            }
            tops_r[p] = self.reverse.step(&mut r, classes[p], &rr)?.top;
        }
        let meeting = collect_exact((1..n - 1).map(|p| Ok(self.meet(&tops_f[p - 1], &tops_r[p + 1], &rf, &rr, wmax)?.face.code(classes[p]))))?;
        Ok((forward, meeting))
    }

    /// The duplex as text: its declaration line, each strand's text, the meeting's material.
    pub fn to_text(&self) -> String {
        let mut s = format!("duplex-v1 {}\n", self.contacts);
        s.push_str(&self.forward.to_text());
        s.push_str(&self.reverse.to_text());
        s.push_str(&self.meeting.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" "));
        s.push('\n');
        s
    }

    /// The duplex from its text, refused unless it restores whole.
    pub fn from_text(text: &str) -> Result<Self> {
        let lines: Vec<&str> = text.lines().collect();
        if lines.len() != 6 {
            return refuse("a duplex's text has six lines");
        }
        let head: Vec<&str> = lines[0].split(' ').collect();
        if head.len() != 2 || head[0] != "duplex-v1" {
            return refuse("not a duplex's text");
        }
        let contacts = head[1].parse::<usize>().map_err(|_| TowerError::Refused("a declaration that is not a count"))?;
        let forward = Tower::from_text(&format!("{}\n{}\n", lines[1], lines[2]))?;
        let reverse = Tower::from_text(&format!("{}\n{}\n", lines[3], lines[4]))?;
        if forward.declaration != reverse.declaration || contacts == 0 {
            return refuse("a duplex's strands share one declaration and meet through a contact");
        }
        let layout = MeetingLayout::new(forward.declaration.alphabet, forward.declaration.width, contacts);
        let meeting: Vec<i32> = lines[5]
            .split(' ')
            .map(|s| s.parse::<i32>().map_err(|_| TowerError::Refused("material that is not an integer")))
            .collect::<Result<_>>()?;
        if meeting.len() != layout.len {
            return refuse("material of the wrong extent");
        }
        Ok(Self { forward, reverse, contacts, meeting, layout, exponential: Exponential::new(FACE_BITS) })
    }
}

/// [definition; agent-inferred] **The duplex's learner**: the material, the covector's moments,
/// the step's rate. The deposit is the tower's (`TowerLearner`) over the whole material.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DuplexLearner {
    pub duplex: Duplex,
    first: Vec<i128>,
    second: Vec<i128>,
    opened: bool,
    /// The step's rate, `2^(−k)`.
    pub rate_bits: u32,
}

impl DuplexLearner {
    pub fn new(duplex: Duplex, rate_bits: u32) -> Self {
        let len = duplex.len();
        Self { duplex, first: vec![0; len], second: vec![0; len], opened: false, rate_bits }
    }

    /// One section over parallel streams, each stream's classes `[0..=T]` from its carried forward
    /// state: the streams' covectors summed, the moments moved, the step certified by the reread
    /// of all three faces, and each stream's forward state continued under the material the
    /// section ends with.
    pub fn section(&mut self, states: &mut [TowerState], classes: &[&[usize]]) -> Result<DuplexReceipt> {
        if states.len() != classes.len() || classes.iter().any(|c| c.len() < 3) {
            return refuse("a duplex section needs one carried state and three classes a stream");
        }
        let duplex = &self.duplex;
        let (rf, rr, wmax) = (duplex.forward.reaches(), duplex.reverse.reaches(), duplex.reach_meeting());
        let opening: Vec<TowerState> = states.to_vec();
        let reads: Vec<Strands> =
            opening.par_iter().zip(classes.par_iter()).map(|(open, c)| duplex.read_stream(open, c, &rf, &rr, wmax)).collect::<Result<_>>()?;
        let faces_old: Vec<(u128, u128)> = reads.iter().zip(classes).flat_map(|(s, c)| Duplex::faces(s, c)).collect();
        let before = reads.iter().zip(classes).fold([0i64; 3], |acc, (s, c)| {
            let k = Duplex::codes(s, c);
            [acc[0] + k[0], acc[1] + k[1], acc[2] + k[2]]
        });
        let gradients: Vec<Vec<i128>> = opening
            .par_iter()
            .zip(reads.par_iter())
            .zip(classes.par_iter())
            .map(|((open, s), c)| duplex.covector(open, c, s, &rf, &rr, wmax))
            .collect::<Result<_>>()?;
        let mut g = vec![0i128; duplex.len()];
        for gs in &gradients {
            for (a, b) in g.iter_mut().zip(gs) {
                *a += *b;
            }
        }
        duplex.to_step_grain(&mut g);
        if !self.opened {
            self.first.clone_from(&g);
            self.second = g
                .iter()
                .map(|v| v.checked_mul(*v).ok_or(TowerError::Refused("a covector's square outgrew its 128-bit carrier")))
                .collect::<Result<_>>()?;
            self.opened = true;
        } else {
            for ((m, v), gv) in self.first.iter_mut().zip(self.second.iter_mut()).zip(&g) {
                let square = gv.checked_mul(*gv).ok_or(TowerError::Refused("a covector's square outgrew its 128-bit carrier"))?;
                *m = toward(*m, *gv, FIRST_RATE);
                *v = toward(*v, square, SECOND_RATE);
            }
        }
        let mut step = vec![0i128; g.len()];
        for (start, len, grain) in duplex.families() {
            for i in start..start + len {
                let root = (self.second[i].max(0) as u128).isqrt() as i128 + 1;
                step[i] = ((self.first[i] << grain) >> self.rate_bits) / root;
            }
        }
        let forward_cells = reads.iter().map(|s| s.forward.len()).sum();
        let meeting_cells = reads.iter().map(|s| s.meetings.len()).sum();
        let receipt = |code_after, halvings, deposited| DuplexReceipt {
            forward_cells,
            meeting_cells,
            forward_before: before[0],
            reverse_before: before[1],
            meeting_before: before[2],
            code_after,
            halvings,
            deposited,
        };
        let mut halvings = 0u32;
        loop {
            let mut candidate = self.duplex.clone();
            if !candidate.move_by(&step, halvings)? {
                for (s, r) in states.iter_mut().zip(reads) {
                    *s = r.end;
                }
                return Ok(receipt(before.iter().sum(), halvings, false));
            }
            let (cf, cr, cw) = (candidate.forward.reaches(), candidate.reverse.reaches(), candidate.reach_meeting());
            let rereads: Vec<Strands> =
                opening.par_iter().zip(classes.par_iter()).map(|(open, c)| candidate.read_stream(open, c, &cf, &cr, cw)).collect::<Result<_>>()?;
            let faces_new: Vec<(u128, u128)> = rereads.iter().zip(classes).flat_map(|(s, c)| Duplex::faces(s, c)).collect();
            if fewer_bits(&faces_old, &faces_new) {
                let after = rereads.iter().zip(classes).map(|(s, c)| Duplex::codes(s, c).iter().sum::<i64>()).sum();
                for (s, r) in states.iter_mut().zip(rereads) {
                    *s = r.end;
                }
                self.duplex = candidate;
                return Ok(receipt(after, halvings, true));
            }
            halvings += 1;
        }
    }

    /// The learner as text: the duplex, then the moments.
    pub fn to_text(&self) -> String {
        let mut s = self.duplex.to_text();
        s.push_str(&format!("moments {} {}\n", self.rate_bits, self.opened as u8));
        s.push_str(&self.first.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" "));
        s.push('\n');
        s.push_str(&self.second.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" "));
        s.push('\n');
        s
    }

    pub fn from_text(text: &str) -> Result<Self> {
        let lines: Vec<&str> = text.lines().collect();
        if lines.len() != 9 {
            return refuse("a duplex learner's text has nine lines");
        }
        let duplex = Duplex::from_text(&(lines[..6].join("\n") + "\n"))?;
        let head: Vec<&str> = lines[6].split(' ').collect();
        if head.len() != 3 || head[0] != "moments" {
            return refuse("not a learner's moments");
        }
        let rate_bits = head[1].parse::<u32>().map_err(|_| TowerError::Refused("a rate that is not a count"))?;
        let opened = head[2] == "1";
        let parse = |l: &str| -> Result<Vec<i128>> { l.split(' ').map(|s| s.parse::<i128>().map_err(|_| TowerError::Refused("a moment that is not an integer"))).collect() };
        let first = parse(lines[7])?;
        let second = parse(lines[8])?;
        if first.len() != duplex.len() || second.len() != duplex.len() {
            return refuse("moments of the wrong extent");
        }
        Ok(Self { duplex, first, second, opened, rate_bits })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn keys(n: usize) -> Vec<u8> {
        // A fixed exterior key stream for the fixtures: the bytes of a counter's squares.
        (0..n as u64).flat_map(|i| (i.wrapping_mul(2654435761) ^ (i * i)).to_be_bytes()[4..].to_vec()).collect()
    }

    /// A tiny duplex whose strands' readouts and returns and the meeting's readout open away from
    /// zero, so every family carries a covector.
    fn tiny(gated: bool) -> Duplex {
        let declaration = TowerDeclaration { alphabet: 4, width: 4, modes: 2, contacts: 4, levels: 2, gated, turned: false, pumped: false, contact: super::ContactLaw::Rectifying };
        let mut duplex = Duplex::found(declaration, 4, &keys(16384)).expect("founded");
        let k = keys(32768);
        let mut i = 9000;
        let mut fill = |slice: &mut [i32]| {
            for v in slice {
                *v = (i32::from_be_bytes([k[4 * i], k[4 * i + 1], k[4 * i + 2], k[4 * i + 3]]) >> 8) / 4;
                i += 1;
            }
        };
        for tower in [&mut duplex.forward, &mut duplex.reverse] {
            let layout = tower.layout.clone();
            fill(&mut tower.theta[layout.readout..layout.readout + 16]);
            for lv in &layout.levels {
                fill(&mut tower.theta[lv.ret..lv.ret + 16]);
                if gated {
                    fill(&mut tower.theta[lv.gate..lv.gate + 8]);
                    for v in &mut tower.theta[lv.gate..lv.gate + 8] {
                        *v *= 8;
                    }
                }
            }
        }
        let l = duplex.layout;
        fill(&mut duplex.meeting[l.readout..l.readout_bias]);
        duplex
    }

    fn total_code(duplex: &Duplex, classes: &[usize]) -> i64 {
        let (rf, rr, wmax) = (duplex.forward.reaches(), duplex.reverse.reaches(), duplex.reach_meeting());
        let s = duplex.read_stream(&duplex.forward.rest(), classes, &rf, &rr, wmax).expect("read");
        Duplex::codes(&s, classes).iter().sum()
    }

    #[test]
    fn text_restores_exactly() {
        let duplex = tiny(true);
        assert_eq!(Duplex::from_text(&duplex.to_text()).expect("restored"), duplex);
        let mut learner = DuplexLearner::new(duplex, 6);
        let seq: Vec<usize> = (0..17).map(|i| i % 4).collect();
        let mut states = vec![learner.duplex.forward.rest()];
        learner.section(&mut states, &[&seq]).expect("section");
        let restored = DuplexLearner::from_text(&learner.to_text()).expect("restored");
        assert_eq!(restored, learner);
    }

    #[test]
    fn the_frozen_reading_reads_the_section_faces() {
        let duplex = tiny(true);
        let classes = [0usize, 2, 1, 3, 3, 0, 1, 2, 2, 0, 3, 1, 0];
        let (rf, rr, wmax) = (duplex.forward.reaches(), duplex.reverse.reaches(), duplex.reach_meeting());
        let s = duplex.read_stream(&duplex.forward.rest(), &classes, &rf, &rr, wmax).expect("read");
        let (forward, meeting) = duplex.read_cells(&classes, None).expect("cells");
        let codes = Duplex::codes(&s, &classes);
        assert_eq!(forward.iter().sum::<i64>(), codes[0]);
        assert_eq!(meeting.iter().sum::<i64>(), codes[2]);
        // Read in two sections of six, the reverse opening at rest at each section's end as a
        // learner's sections open it: the meetings are the sections' own, and the place between
        // them is read once more.
        let first = duplex.read_stream(&duplex.forward.rest(), &classes[..7], &rf, &rr, wmax).expect("read");
        let second = duplex.read_stream(&first.end, &classes[6..], &rf, &rr, wmax).expect("read");
        let (_, sectioned) = duplex.read_cells(&classes, Some(6)).expect("cells");
        let own = Duplex::codes(&first, &classes[..7])[2] + Duplex::codes(&second, &classes[6..])[2];
        assert_eq!(sectioned.iter().sum::<i64>() - sectioned[5], own);
        // The meeting at a place from the tops a release reads.
        let p = 5;
        let mut f = duplex.forward.rest();
        let mut top_f = Vec::new();
        for &u in &classes[..p] {
            top_f = duplex.forward.advance_top(&mut f, u).expect("advance").1;
        }
        let mut r = duplex.reverse.rest();
        let mut top_r = Vec::new();
        for &u in classes[p + 1..].iter().rev() {
            top_r = duplex.reverse.advance_top(&mut r, u).expect("advance").1;
        }
        assert_eq!(duplex.meeting_face(&top_f, &top_r).expect("face").code(classes[p]), meeting[p - 1]);
    }

    #[test]
    fn a_refinement_reads_each_place_from_its_meeting() {
        let duplex = tiny(true);
        let classes = [0usize, 2, 1, 3, 3, 0, 1, 2, 2, 0, 3, 1, 0];
        let (_, meeting) = duplex.read_cells(&classes, None).expect("cells");
        // The release is classes[4..12], read after classes[..4] and closed by classes[12]; a draw
        // that keeps each place sees the meetings the frozen reading reads, and one sweep settles.
        let mut release = classes[4..12].to_vec();
        let mut k = 4;
        let mut seen = Vec::new();
        let mut keep = |face: &TowerFace| -> Result<usize> {
            seen.push(face.code(classes[k]));
            k += 1;
            Ok(classes[k - 1])
        };
        assert_eq!(duplex.refine(&classes[..4], &mut release, classes[12], 3, &mut keep).expect("refined"), (1, true));
        assert_eq!(seen, meeting[3..11].to_vec());
        assert_eq!(release, classes[4..12].to_vec());
    }

    #[test]
    fn the_covector_matches_the_code_difference() {
        the_covector_matches_the_code_difference_of(false);
        the_covector_matches_the_code_difference_of(true);
    }

    fn the_covector_matches_the_code_difference_of(gated: bool) {
        let duplex = tiny(gated);
        let classes = [0usize, 2, 1, 3, 3, 0, 1, 2, 2, 0, 3, 1, 0];
        let opening = duplex.forward.rest();
        let (rf, rr, wmax) = (duplex.forward.reaches(), duplex.reverse.reaches(), duplex.reach_meeting());
        let s = duplex.read_stream(&opening, &classes, &rf, &rr, wmax).expect("read");
        let mut g = duplex.covector(&opening, &classes, &s, &rf, &rr, wmax).expect("covector");
        // On the deposit's grain, the moves in Cartesian form (the chart is the tower's, tested
        // there): every family but the moves.
        let nf = duplex.forward.theta.len();
        let nr = duplex.reverse.theta.len();
        {
            let (gf, rest) = g.split_at_mut(nf);
            let (gr, gm) = rest.split_at_mut(nr);
            duplex.forward.to_step_grain(gf);
            duplex.reverse.to_step_grain(gr);
            for (start, len, grain) in duplex.layout.families() {
                for v in &mut gm[start..start + len] {
                    *v = if grain == MATERIAL_BITS { release(*v, COVECTOR_BITS + FACE_BITS - STEP_BITS) } else { *v << (STEP_BITS - COVECTOR_BITS) };
                }
            }
        }
        // Which contacts conduct and which gated moves are held, in both strands and the meeting:
        // the covector is the derivative on the passage's own side of every kink.
        let conducting = |d: &Duplex| -> Vec<bool> {
            let (rf, rr, wmax) = (d.forward.reaches(), d.reverse.reaches(), d.reach_meeting());
            let s = d.read_stream(&d.forward.rest(), &classes, &rf, &rr, wmax).expect("read");
            let cells = s.forward.iter().chain(&s.reverse).flat_map(|c| c.levels.iter().flat_map(|l| l.drive.iter().map(|&a| a > 0).chain(l.gate.iter().map(|m| m.held))));
            cells.chain(s.meetings.iter().flat_map(|m| m.drive.iter().map(|&a| a > 0))).collect()
        };
        let base = conducting(&duplex);
        let base_code = total_code(&duplex, &classes);
        let (mut checked, mut families) = (0, 0);
        for (start, len, grain) in duplex.families() {
            if grain == MOVE_BITS {
                continue;
            }
            families += 1;
            let mut order: Vec<usize> = (start..start + len).collect();
            order.sort_by_key(|&i| std::cmp::Reverse(g[i].abs()));
            'parameter: for i in order {
                let gi = g[i];
                if gi.abs() < 1i128 << (STEP_BITS - 6) {
                    break;
                }
                // The code's fitted slope over sixteen steps `k h`, `h = 2^(grain − shift)`.
                let slope = |shift: u32| -> Option<i128> {
                    let h = 1i32 << (grain - shift);
                    let (mut moment, mut spread) = (0i128, 0i128);
                    for k in (-8i32..=8).filter(|&k| k != 0) {
                        let mut moved = duplex.clone();
                        if i < nf {
                            moved.forward.theta[i] += k * h;
                        } else if i < nf + nr {
                            moved.reverse.theta[i - nf] += k * h;
                        } else {
                            moved.meeting[i - nf - nr] += k * h;
                        }
                        if conducting(&moved) != base {
                            return None;
                        }
                        moment += k as i128 * (total_code(&moved, &classes) - base_code) as i128;
                        spread += (k * k) as i128;
                    }
                    Some((moment << (STEP_BITS - READ_BITS)) * (1i128 << grain) / (h as i128 * spread))
                };
                // Three faces released to 2^(−16) move the code by their grain at narrow steps, and
                // wide steps cross kinks, so the slope is read at each width from 2^(−6) to 2^(−11)
                // units that crosses none, and the covector must lie within what they read, to a
                // tenth of itself: on this fixture the forward's largest gate covector, −70.6 (×10⁶),
                // reads −70.4, −69.9, −73.6, −79.3, −89.8 and −84.4 from the widest step down.
                let mut slopes: Vec<i128> = (6u32..=11).filter_map(|shift| slope(shift)).collect();
                if slopes.len() < 3 {
                    continue 'parameter;
                }
                slopes.sort_unstable();
                let margin = gi.abs() / 10;
                assert!(
                    slopes[0] - margin <= gi && gi <= slopes[slopes.len() - 1] + margin,
                    "family at {start} grain {grain}, parameter {i}: covector {gi} against {slopes:?}"
                );
                checked += 1;
                break;
            }
        }
        // The meeting's four families and most of each strand's carry a readable covector.
        assert!(checked * 4 >= families * 3, "only {checked} of {families} families carried a readable covector");
    }

    #[test]
    fn a_section_learns_a_repeating_passage() {
        let declaration = TowerDeclaration { alphabet: 4, width: 8, modes: 4, contacts: 8, levels: 1, gated: true, turned: false, pumped: false, contact: super::ContactLaw::Rectifying };
        let duplex = Duplex::found(declaration, 8, &keys(16384)).expect("founded");
        let mut learner = DuplexLearner::new(duplex, 5);
        let passage: Vec<usize> = (0..4096).map(|i| [0, 1, 2, 1, 3][i % 5]).collect();
        let mut states = vec![learner.duplex.forward.rest(), learner.duplex.forward.rest()];
        let mut last = None;
        for section in 0..60 {
            let a = &passage[section * 32..section * 32 + 33];
            let b = &passage[2048 + section * 32..2048 + section * 32 + 33];
            last = Some(learner.section(&mut states, &[a, b]).expect("section"));
        }
        let last = last.expect("sections");
        // The meeting codes under a quarter of a bit a class (the flat face codes two bits).
        assert!(last.meeting_before * 4 < (last.meeting_cells as i64) << READ_BITS, "{last:?}");
    }
}
