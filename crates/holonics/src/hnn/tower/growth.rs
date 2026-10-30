//! **The body grows by copies whose parts sum to what it learned** (#404, #407; record
//! `2026-10-29_THE_BODY_GROWS_BY_COPIES_WHOSE_PARTS_SUM_TO_WHAT_IT_LEARNED_SO_IT_RESTARTS_WIDER_ON_THE_SAME_FACES`).
//!
//! [definition; agent-inferred, October 29] A tower widened by `f` repeats its encoding and every
//! vector family, so each coordinate has `f` equal copies, and splits every matrix entry over its
//! `f` column copies into parts that sum to it, repeating the rows (the readout keeps its rows):
//!
//! ```text
//! x' = (x, …, x)        W'[(b, r), (c, j)] = W[r, j]/f + δ_c[(b, r), j],  Σ_c δ_c = 0
//! ⇒  face'_t = face_t,   widen(advance(σ, u)) = advance'(widen(σ), u)
//! ```
//!
//! `W[r, j]/f` is the Euclidean split, its remainder carried by the first parts, so the parts sum
//! exactly. The zero-sum differences are what the founding of the grown declaration founds there,
//! drawn from the declared founding key stream four bytes a draw as [`Tower::found_on`] draws; a
//! family the founding opens at zero splits evenly. They cancel in every forward sum while the
//! copies are equal and part the copies' covectors once the encoding's copies move apart, so the
//! copies specialize under learning. Participation's heads are repeated, one head a copy. Ported
//! from Codex's growth map (branch `codex/counting-faces-20261028`), whose seeded generator and
//! sixteenth-of-the-largest perturbation the declared keys and the founding's scales replace.
use super::participation::{LevelSites, ParticipationDeclaration};
use super::*;

/// One family's split: the founding scale `num/den` on the family's grain, or an even split.
#[derive(Clone, Copy)]
struct Scale {
    num: u128,
    den: u128,
    bits: u32,
}

/// The grown material and moments, filled family by family from the old ones.
struct Grower<'a> {
    old: &'a [i32],
    new: Vec<i32>,
    /// For each grown entry, the old entry it carries and whether its covector is divided among
    /// the copies (every family but the readout's).
    from: Vec<(usize, bool)>,
    f: usize,
    keys: &'a [u8],
    cursor: usize,
}

impl Grower<'_> {
    fn draw(&mut self, scale: Scale) -> Result<i128> {
        let word = self.keys.get(self.cursor..self.cursor + 4).ok_or(TowerError::Refused("fewer key bytes than the growth draws"))?;
        self.cursor += 4;
        let k = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i128;
        Ok((k * ((scale.num << scale.bits) / scale.den) as i128) >> 31)
    }

    /// A vector family of `len` entries repeated, one copy after another.
    fn repeat(&mut self, from: usize, to: usize, len: usize, divided: bool) {
        for c in 0..self.f {
            for i in 0..len {
                self.new[to + c * len + i] = self.old[from + i];
                self.from[to + c * len + i] = (from + i, divided);
            }
        }
    }

    /// A `rows × cols` matrix: each entry split over its `f` column copies, the rows repeated
    /// `f` times when `repeated` (once for the readout), copy-major on both axes.
    fn split(&mut self, from: usize, to: usize, rows: usize, cols: usize, repeated: bool, scale: Option<Scale>) -> Result<()> {
        let f = self.f;
        let row_copies = if repeated { f } else { 1 };
        let stride = cols * f;
        for b in 0..row_copies {
            for r in 0..rows {
                for j in 0..cols {
                    let v = self.old[from + r * cols + j] as i128;
                    let (q, rem) = (v.div_euclid(f as i128), v.rem_euclid(f as i128));
                    let mut spent = 0i128;
                    for c in 0..f {
                        let delta = match scale {
                            Some(s) if c + 1 < f => self.draw(s)?,
                            Some(_) => -spent,
                            None => 0,
                        };
                        spent += delta;
                        let part = q + i128::from((c as i128) < rem) + delta;
                        let at = to + (b * rows + r) * stride + c * cols + j;
                        self.new[at] = fit32(part, "a grown part outgrew its 32-bit carrier")?;
                        self.from[at] = (from + r * cols + j, repeated);
                    }
                }
            }
        }
        Ok(())
    }
}

impl Tower {
    /// [definition; agent-inferred, October 29] **The tower widened by `factor`** (module header):
    /// width, modes and contacts, the differences drawn from `keys`. Refused where a part's lift is
    /// owed: the pair face, the ring, the rotor, the strands, the turned and pumped modes (their
    /// own charts) and the mutual contact (whose `⟨y, E_a⟩` and `‖E_a‖²` would count the copies).
    pub fn widened(&self, factor: usize, keys: &[u8]) -> Result<Self> {
        Ok(self.grown(factor, keys)?.0)
    }

    /// The draws a growth by `factor` reads from the founding keys, four bytes a draw: `f − 1` an
    /// entry of each row copy of every family the founding opens away from zero (the pushes, the
    /// reads, the contacts and participation's charts and reads).
    pub fn growth_draws(&self, factor: usize) -> usize {
        let d = &self.declaration;
        let (w, n, f) = (d.width, d.modes, d.contacts);
        let charts = if self.participation.is_some() { 6 * n * w + 2 * w * n } else { 0 };
        d.levels * factor * factor.saturating_sub(1) * (4 * n * w + f * w + charts)
    }

    fn grown(&self, factor: usize, keys: &[u8]) -> Result<(Self, Vec<(usize, bool)>)> {
        let old = self.declaration;
        if factor < 2 {
            return refuse("a growth makes at least two copies");
        }
        if self.pair.is_some() || self.ring.is_some() || self.rotor.is_some() || self.strands.is_some() || old.turned || old.pumped {
            return refuse("the growth's lift of a pair face, ring, rotor, strands or turned mode is owed");
        }
        if self.mutual.is_some() {
            return refuse("the growth's lift of the mutual contact is owed: its slip would count the copies");
        }
        let grow = |v: usize| v.checked_mul(factor).ok_or(TowerError::Refused("a grown extent outgrew its carrier"));
        let d = TowerDeclaration { width: grow(old.width)?, modes: grow(old.modes)?, contacts: grow(old.contacts)?, ..old };
        let participation = match &self.participation {
            Some(p) => Some(ParticipationDeclaration::new(p.heads.repeat(factor), p.section, p.beta_shift)?),
            None => None,
        };
        let layout = Layout::new(&d, 0, 0, 0, 0, participation.as_ref(), false, self.heard_from());
        let mut g = Grower { old: &self.theta, new: vec![0; layout.len], from: vec![(0, true); layout.len], f: factor, keys, cursor: 0 };
        let (a, w, n, f) = (old.alphabet, old.width, old.modes, old.contacts);
        // The founding's scales in the grown declaration (`Tower::found_on`): the push and
        // participation's charts at 1/√d, the reads at 1/√N, the contacts at √(6/d).
        let push = Some(Scale { num: 1, den: (d.width as u128).isqrt().max(1), bits: MATERIAL_BITS });
        let read = Some(Scale { num: 1, den: (d.modes as u128).isqrt().max(1), bits: MATERIAL_BITS });
        let contact = Some(Scale { num: (6u128 << 32).isqrt(), den: ((d.width as u128) << 32).isqrt(), bits: MATERIAL_BITS });
        let (ol, nl) = (&self.layout, &layout);
        // The encoding repeats its coordinates rather than splitting them.
        for class in 0..a {
            g.repeat(ol.encoding + class * w, nl.encoding + class * d.width, w, true);
        }
        for (o, l) in ol.levels.iter().zip(&nl.levels) {
            g.repeat(o.move_re, l.move_re, n, true);
            g.repeat(o.move_im, l.move_im, n, true);
            g.split(o.push_re, l.push_re, n, w, true, push)?;
            g.split(o.push_im, l.push_im, n, w, true, push)?;
            g.split(o.read_re, l.read_re, w, n, true, read)?;
            g.split(o.read_im, l.read_im, w, n, true, read)?;
            g.split(o.contact, l.contact, f, w, true, contact)?;
            g.repeat(o.contact_bias, l.contact_bias, f, true);
            g.split(o.ret, l.ret, w, f, true, None)?;
            g.repeat(o.ret_bias, l.ret_bias, w, true);
            if old.gated {
                g.split(o.gate, l.gate, n, w, true, None)?;
                g.repeat(o.gate_bias, l.gate_bias, n, true);
            }
            if old.contact != ContactLaw::Rectifying {
                g.split(o.pair, l.pair, f, w, true, None)?;
                g.repeat(o.pair_bias, l.pair_bias, f, true);
            }
        }
        g.split(ol.readout, nl.readout, a, w, false, None)?;
        for c in 0..a {
            g.new[nl.readout_bias + c] = self.theta[ol.readout_bias + c];
            g.from[nl.readout_bias + c] = (ol.readout_bias + c, false);
        }
        if let Some(p) = &self.participation {
            for (o, l) in ol.levels.iter().zip(&nl.levels) {
                for (from, to) in [(o.pa_probe_re, l.pa_probe_re), (o.pa_probe_im, l.pa_probe_im), (o.pa_key_re, l.pa_key_re), (o.pa_key_im, l.pa_key_im), (o.pa_value_re, l.pa_value_re), (o.pa_value_im, l.pa_value_im)] {
                    g.split(from, to, n, w, true, push)?;
                }
                g.split(o.pa_read_re, l.pa_read_re, w, n, true, read)?;
                g.split(o.pa_read_im, l.pa_read_im, w, n, true, read)?;
                g.split(o.pa_contact, l.pa_contact, f, w, true, None)?;
                g.repeat(o.pa_friction, l.pa_friction, p.heads.len(), true);
            }
        }
        // The passage's `W₁ˣ` splits as the contacts do, from zero where it is at zero, on the levels
        // the clock holds.
        if let Some(first) = self.heard_from() {
            for (o, l) in ol.levels.iter().zip(&nl.levels).skip(first) {
                g.split(o.passage, l.passage, f, w, true, None)?;
            }
        }
        let tower = Self { declaration: d, theta: g.new, participation, layout, ..self.clone() };
        Ok((tower, g.from))
    }

    /// [definition; agent-inferred, October 29] **A stream's state widened** with this tower by
    /// `factor`: each level's modes repeated, one copy after another, its open packet with them, and
    /// participation's open section with them (frames, met dissipation, keys, values and the held current a mode, each
    /// site's dissipation a head). Refused on a state that carries a passage credit, whose lift is
    /// owed.
    pub fn widen_state(&self, state: &TowerState, factor: usize) -> Result<TowerState> {
        let d = &self.declaration;
        if state.credit.is_some() {
            return refuse("the growth's lift of a passage credit is owed");
        }
        if state.modes.len() != d.levels || state.modes.iter().any(|m| m.len() != d.modes) || !state.ring.is_empty() || !state.strands.is_empty() {
            return refuse("a state of another tower");
        }
        let repeat = |v: &[Phasor]| -> Vec<Phasor> { v.repeat(factor) };
        let sites = state
            .sites
            .iter()
            .map(|s| LevelSites {
                frame: repeat(&s.frame),
                met: s.met.repeat(factor),
                keys: s.keys.iter().map(|k| repeat(k)).collect(),
                values: s.values.iter().map(|v| repeat(v)).collect(),
                dissipation: s.dissipation.iter().map(|h| h.repeat(factor)).collect(),
                current: repeat(&s.current),
            })
            .collect();
        let packets = state.packets.iter().map(|a| repeat(a)).collect();
        Ok(TowerState { modes: state.modes.iter().map(|m| repeat(m)).collect(), sites, packets, ..state.clone() })
    }
}

impl TowerLearner {
    /// [definition; agent-inferred, October 29] **The learner widened**: its tower
    /// ([`Tower::widened`]) and its moments lifted. Split evenly, each grown coordinate's covector
    /// at the growth point is the old one divided among its `f` copies, and the readout's (whose
    /// rows are not repeated) the old one; the moments are the covector's statistics, so a grown
    /// coordinate carries `m/f` and `v/f²`, the readout `m` and `v`, and opens on the old
    /// normalized step `m/√v`.
    pub fn widened(&self, factor: usize, keys: &[u8]) -> Result<Self> {
        let (tower, from) = self.tower.grown(factor, keys)?;
        let (f, f2) = (factor as i128, (factor * factor) as i128);
        let first = from.iter().map(|&(i, divided)| if divided { div_nearest(self.first[i], f) } else { self.first[i] }).collect();
        let second = from.iter().map(|&(i, divided)| if divided { div_nearest(self.second[i], f2) } else { self.second[i] }).collect();
        Ok(Self { tower, first, second, opened: self.opened, rate_bits: self.rate_bits, swell: Vec::new(), held: Vec::new() })
    }
}

#[cfg(test)]
mod tests {
    use super::super::realization::HostPass;
    use super::super::tests::{keys, tiny_clocked_participating, tiny_contacts, tiny_participating};
    use super::*;

    const PASSAGE: [usize; 40] = [1, 2, 0, 1, 1, 3, 2, 2, 0, 1, 2, 1, 0, 0, 3, 1, 2, 2, 1, 0, 1, 2, 3, 0, 1, 1, 2, 0, 2, 1, 3, 1, 0, 2, 2, 1, 0, 1, 2, 3];

    /// Acceptance 1: the grown tower read from the widened state gives the old faces class by
    /// class, its state after each the widened old state, across participation's section closes,
    /// and on a news clock across each level's own closes and held currents.
    #[test]
    fn the_grown_tower_reads_the_old_faces_from_the_widened_state() {
        for tower in [tiny_contacts(2, 4, 4, true, false, false, ContactLaw::Rectifying), tiny_contacts(2, 4, 4, true, false, false, ContactLaw::Pair), tiny_participating(ContactLaw::Rectifying, true), tiny_clocked_participating(ContactLaw::Rectifying, false, 3)] {
            for factor in [2, 3] {
                let grown = tower.widened(factor, &keys(1 << 16)).expect("grown");
                assert_eq!(grown.declaration.modes, factor * tower.declaration.modes);
                let mut old = tower.rest();
                let mut new = tower.widen_state(&old, factor).expect("widened");
                assert_eq!(new, grown.rest());
                for &u in &PASSAGE {
                    assert_eq!(grown.advance(&mut new, u).expect("advanced"), tower.advance(&mut old, u).expect("advanced"));
                    assert_eq!(new, tower.widen_state(&old, factor).expect("widened"));
                }
            }
        }
    }

    /// Acceptance 2 and 6: every entry's parts sum to it; the push's differences are the founding's
    /// draws and the readout splits evenly; each unlifted part is refused.
    #[test]
    fn the_parts_sum_to_the_learned_entry_and_the_unlifted_parts_are_refused() {
        let tower = tiny_contacts(2, 4, 4, true, false, false, ContactLaw::Rectifying);
        let grown = tower.widened(2, &keys(1 << 16)).expect("grown");
        let (w, n, a) = (tower.declaration.width, tower.declaration.modes, tower.declaration.alphabet);
        let (o, l) = (tower.layout.levels[0], grown.layout.levels[0]);
        let mut differs = false;
        for b in 0..2 {
            for r in 0..n {
                for j in 0..w {
                    let at = |c: usize| grown.theta[l.push_re + (b * n + r) * 2 * w + c * w + j] as i64;
                    assert_eq!(at(0) + at(1), tower.theta[o.push_re + r * w + j] as i64);
                    differs |= (at(0) - at(1)).abs() > 1;
                }
            }
        }
        assert!(differs, "the push's copies differ by the founding's draws");
        for c in 0..a {
            for j in 0..w {
                let (p, q) = (grown.theta[grown.layout.readout + c * 2 * w + j], grown.theta[grown.layout.readout + c * 2 * w + w + j]);
                assert_eq!(p as i64 + q as i64, tower.theta[tower.layout.readout + c * w + j] as i64);
                assert!((p - q).abs() <= 1, "the readout founds at zero and splits evenly");
            }
        }
        let draws = tower.growth_draws(2);
        assert!(tower.widened(2, &keys(draws)).is_ok() && tower.widened(2, &keys(draws - 1)).is_err(), "the draws counted are the draws read");
        let participating = tiny_participating(ContactLaw::Rectifying, true);
        let draws = participating.growth_draws(3);
        assert!(participating.widened(3, &keys(draws)).is_ok() && participating.widened(3, &keys(draws - 1)).is_err());
        assert!(tower.widened(1, &keys(1 << 16)).is_err(), "one copy is no growth");
        assert!(tower.widened(2, &keys(8)).is_err(), "fewer keys than the draws");
        assert!(tiny_contacts(2, 4, 4, true, true, false, ContactLaw::Rectifying).widened(2, &keys(1 << 16)).is_err(), "a turned mode");
        let mut mutual = Tower::found(TowerDeclaration { alphabet: 4, width: 4, modes: 4, contacts: 4, levels: 2, gated: true, turned: false, pumped: false, contact: ContactLaw::Rectifying }, &keys(4096)).expect("founded");
        mutual.join_mutual_contact(2).expect("joined");
        assert!(mutual.widened(2, &keys(1 << 16)).is_err(), "the mutual contact");
        assert!(tower.widen_state(&tower.rest_with_credit(), 2).is_err(), "a carried credit");
    }

    /// Acceptance 3 and 4: the grown learner carries the moments of the divided covector (the
    /// readout's whole), and one learned section parts some pair of mode copies.
    #[test]
    fn the_moments_are_divided_and_a_section_parts_the_copies() {
        let tower = tiny_participating(ContactLaw::Rectifying, true);
        let mut learner = TowerLearner::new(tower, 6);
        let pass = &mut HostPass::default();
        let mut states = vec![learner.tower.rest(); 2];
        learner.section_realized(&mut states, &[&PASSAGE[..17], &PASSAGE[17..34]], None, pass).expect("learned");
        let grown = learner.widened(2, &keys(1 << 16)).expect("grown");
        let (o, l) = (learner.tower.layout.levels[1], grown.tower.layout.levels[1]);
        let (w, n) = (learner.tower.declaration.width, learner.tower.declaration.modes);
        let (old, new) = (o.read_re + 2 * n + 1, l.read_re + (w + 2) * 2 * n + n + 1);
        assert_eq!(grown.first[new], div_nearest(learner.first[old], 2));
        assert_eq!(grown.second[new], div_nearest(learner.second[old], 4));
        let readout = learner.tower.layout.readout + 3;
        assert_eq!(grown.first[grown.tower.layout.readout + w + 3], learner.first[readout]);
        assert!(grown.opened && learner.first[old] != 0);
        let mut grown = grown;
        let mut states: Vec<TowerState> = states.iter().map(|s| learner.tower.widen_state(s, 2).expect("widened")).collect();
        let receipt = grown.section_realized(&mut states, &[&PASSAGE[23..40], &PASSAGE[3..20]], None, pass).expect("learned");
        assert!(receipt.deposited);
        let gl = grown.tower.layout.levels[0];
        let w2 = 2 * w;
        let parted = (0..n).any(|k| grown.tower.theta[gl.push_re + k * w2..gl.push_re + (k + 1) * w2] != grown.tower.theta[gl.push_re + (n + k) * w2..gl.push_re + (n + k + 1) * w2]);
        assert!(parted, "a section parts some pair of mode copies");
    }
}
