//! **Readings beside the bits** (#404, #406; record
//! `2026-10-29_A_COARSE_LEVELS_SITES_ARE_ITS_OWN_TICKS…` §5, and the radix record
//! `2026-10-29_A_VALUE_IS_A_RADIX_MOVE…` §§3–4): faces of the tower's own material and covector that
//! the race's measurement reads lap by lap. Each decides nothing, trains nothing and selects no lap.
//!
//! - [`Tower::participation_shares`]: where each head's covector goes, to the charts that decide
//!   where it looks (probe and key) or to the chart that decides what it carries (value). The
//!   return's `g_z_ij = ln 2 · a_ij (g_a_ij − Σ_k a_ik g_a_ik)` vanishes on a head whose weights sit
//!   on one site, so such a head's score charts receive almost nothing.
//! - [`Tower::mode_octaves`]: each mode's friction octave `⌊log₂(3(1 − |λ|)/2)⌋`, the octave
//!   [`Tower::founded_participation`] reads, so a level's histogram over the octaves is the reach
//!   its modes' frictions match (the radix record §4: friction matched to the distance it carries).
//! - [`Tower::participation_bridge`]: the join `W₁ᵃ` from the participating current into the
//!   contacts beside the contacts' own material: it opens at zero, and its size against the
//!   contacts' is whether participation has founded its conduction at that level (the radix record
//!   §3, consumer (a)).
use super::*;

/// [agent-inferred, October 29] One head's share of a section's covector: the sum of squares of
/// its score charts' entries (the probe's and the key's rows of its modes, both parts) and of its
/// value chart's, all on the material's grain, and its friction's covector on the face's grain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HeadShare {
    pub modes: usize,
    pub score: BigUint,
    pub value: BigUint,
    pub friction: i128,
}

impl HeadShare {
    /// The score charts' share of the head's chart covector, in thousandths, to the nearest; `None`
    /// when the head's charts received no covector.
    pub fn score_thousandths(&self) -> Option<u32> {
        let whole = &self.score + &self.value;
        if whole == BigUint::default() {
            return None;
        }
        let share: BigUint = (&self.score * 2000u32 + &whole) / (&whole * 2u32);
        u32::try_from(share).ok()
    }
}

/// [agent-inferred, October 29] A level's join `W₁ᵃ` beside its contacts' material: each family's
/// sum of squared entries and its largest entry in magnitude, on the material's grain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BridgeReading {
    pub bridge_squares: u128,
    pub bridge_largest: u32,
    pub contact_squares: u128,
    pub contact_largest: u32,
    pub entries: usize,
}

impl Tower {
    /// [agent-inferred, October 29] **Each participating level's heads' covector shares**, from a
    /// covector `g` on the families' natural grains ([`realization::PassRealization::reverse`]):
    /// per level, per head (its run of modes), the squares of its probe and key rows and of its value
    /// rows, and its friction's entry. Refused without participation or for a covector of another
    /// material.
    pub fn participation_shares(&self, g: &[i128]) -> Result<Vec<Vec<HeadShare>>> {
        let Some(p) = &self.participation else { return refuse("a participation's shares on a participating tower") };
        if g.len() != self.theta.len() {
            return refuse("a covector of this tower's material");
        }
        let w = self.declaration.width;
        let squares = |base: usize, from: usize, modes: usize| -> BigUint { g[base + from * w..base + (from + modes) * w].iter().map(|&v| BigUint::from(v.unsigned_abs()).pow(2)).sum() };
        Ok(self
            .layout
            .levels
            .iter()
            .map(|lv| {
                let mut from = 0;
                p.heads
                    .iter()
                    .enumerate()
                    .map(|(h, &modes)| {
                        let score = [lv.pa_probe_re, lv.pa_probe_im, lv.pa_key_re, lv.pa_key_im].iter().map(|&b| squares(b, from, modes)).sum();
                        let value = [lv.pa_value_re, lv.pa_value_im].iter().map(|&b| squares(b, from, modes)).sum();
                        from += modes;
                        HeadShare { modes, score, value, friction: g[lv.pa_friction + h] }
                    })
                    .collect()
            })
            .collect())
    }

    /// [agent-inferred, October 29] **Each level's modes' friction octaves**, `⌊log₂(3(1 − |λ|)/2)⌋`
    /// with `1 − |λ|` on `2^(−30)` (at least one grain): the nearest octave of the friction
    /// `1 − ρ = 2^(−s)` the turn ladder founds, read off the move's material. Level 0's octaves
    /// found the participation's heads ([`Tower::founded_participation`]).
    pub fn mode_octaves(&self) -> Vec<Vec<i128>> {
        self.layout
            .levels
            .iter()
            .map(|lv| {
                (0..self.declaration.modes)
                    .map(|k| {
                        let distance = ((1i128 << MOVE_BITS) - modulus_and_gamma(self.theta[lv.move_re + k] as i128, self.theta[lv.move_im + k] as i128).0).max(1);
                        (distance + distance / 2).ilog2() as i128
                    })
                    .collect()
            })
            .collect()
    }

    /// [agent-inferred, October 30] **Each level's slowest mode**, `min_k max(1, 1 − |λ_k|)` on
    /// `2^(−30)`: its span `1/(1 − |λ|)` is `2^30` over this, in the level's own ticks.
    pub fn slowest_distances(&self) -> Vec<i128> {
        self.layout
            .levels
            .iter()
            .map(|lv| (0..self.declaration.modes).map(|k| ((1i128 << MOVE_BITS) - modulus_and_gamma(self.theta[lv.move_re + k] as i128, self.theta[lv.move_im + k] as i128).0).max(1)).min().unwrap_or(1))
            .collect()
    }

    /// [agent-inferred, October 30] **The material's families by name**, as the learner's layout
    /// places them: each family's level (`None` for the encoding and the faces the levels share),
    /// its name (a material and its bias share one) and its range, in order. A reading splits a
    /// covector by these; it decides nothing.
    pub fn named_families(&self) -> Vec<(Option<usize>, &'static str, std::ops::Range<usize>)> {
        let ly = &self.layout;
        let shared = |start: usize| -> Option<&'static str> {
            match start {
                s if s == ly.encoding => Some("encoding"),
                s if s == ly.readout || s == ly.readout_bias => Some("readout"),
                s if s == ly.pair_readout || s == ly.pair_encoding => Some("pair_face"),
                s if s == ly.ring_readout || s == ly.ring_factors => Some("ring_face"),
                s if s == ly.strand_contact || s == ly.strand_pair => Some("strands"),
                _ => None,
            }
        };
        let level = |lv: &LevelLayout, start: usize| -> Option<&'static str> {
            let named: [(&[usize], &'static str); 13] = [
                (&[lv.move_re, lv.move_im], "moves"),
                (&[lv.push_re, lv.push_im], "push"),
                (&[lv.read_re, lv.read_im], "read"),
                (&[lv.contact, lv.contact_bias, lv.pair, lv.pair_bias], "contacts"),
                (&[lv.ret, lv.ret_bias], "return"),
                (&[lv.gate, lv.gate_bias], "gate"),
                (&[lv.turn, lv.turn_bias], "turn"),
                (&[lv.pump, lv.pump_bias, lv.pump_axis, lv.pump_axis_bias], "pump"),
                (&[lv.pa_probe_re, lv.pa_probe_im, lv.pa_key_re, lv.pa_key_im, lv.pa_value_re, lv.pa_value_im], "participation_charts"),
                (&[lv.pa_read_re, lv.pa_read_im, lv.pa_contact, lv.pa_friction], "participation_read"),
                (&[lv.passage], "passage"),
                (&[lv.heading_re, lv.heading_im], "heading"),
                (&[lv.descent], "descent"),
            ];
            named.iter().find(|(starts, _)| starts.contains(&start)).map(|&(_, name)| name)
        };
        ly.families
            .iter()
            .filter(|&&(_, len, _)| len > 0)
            .map(|&(start, len, _)| {
                // An absent family's start reads 0, the encoding's start, so the encoding is named
                // first and a level's names only off it.
                let at = if start == ly.encoding { None } else { ly.levels.iter().enumerate().find_map(|(l, lv)| level(lv, start).map(|name| (l, name))) };
                match at {
                    Some((l, name)) => (Some(l), name, start..start + len),
                    None => (None, shared(start).unwrap_or("unnamed"), start..start + len),
                }
            })
            .collect()
    }

    /// [agent-inferred, October 29] **Each participating level's bridge `W₁ᵃ` beside its contacts**:
    /// the join's and the contacts' sums of squared entries and largest entries, on the material's
    /// grain. `None` without participation.
    pub fn participation_bridge(&self) -> Option<Vec<BridgeReading>> {
        self.participation.as_ref()?;
        let entries = self.declaration.contacts * self.declaration.width;
        let read = |base: usize| -> (u128, u32) {
            let part = &self.theta[base..base + entries];
            (part.iter().map(|&v| (v.unsigned_abs() as u128).pow(2)).sum(), part.iter().map(|v| v.unsigned_abs()).max().unwrap_or(0))
        };
        Some(
            self.layout
                .levels
                .iter()
                .map(|lv| {
                    let ((bridge_squares, bridge_largest), (contact_squares, contact_largest)) = (read(lv.pa_contact), read(lv.contact));
                    BridgeReading { bridge_squares, bridge_largest, contact_squares, contact_largest, entries }
                })
                .collect(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::super::participation::{Participation, ENTROPY_BITS};
    use super::super::tests::tiny_participating;
    use super::*;

    /// A participation's entropy is zero on one site, `log₂ k` on `k` even sites, and between
    /// them otherwise, each read below `log₂` by at most a few grains.
    #[test]
    fn a_participations_entropy_reads_its_spread_in_bits() {
        let unit = 1u128 << 62;
        let at = |weights: Vec<u128>| Participation { current: Vec::new(), mass: weights.iter().sum(), weights, released: 0 }.entropy();
        assert_eq!(at(vec![unit]), 0);
        assert_eq!(at(vec![0, unit, 0]), 0, "a released site carries nothing");
        for k in [2u128, 4, 8, 64] {
            let h = at(vec![unit; k as usize]);
            let exact = (k.ilog2() as i128) << ENTROPY_BITS;
            assert!((h - exact).abs() <= 4, "{k} even sites: {h} against {exact}");
        }
        let three = at(vec![unit; 3]);
        assert!(three > 1 << ENTROPY_BITS && three < 2 << ENTROPY_BITS, "{three}");
        let skewed = at(vec![unit, unit >> 10]);
        assert!(skewed > 0 && skewed < (1 << ENTROPY_BITS) / 50, "{skewed}");
    }

    /// The shares read the covector's own entries: a covector on one head's probe rows is all
    /// score, on its value rows all value, and every other head reads nothing; level 0's octaves
    /// found the participation's heads.
    #[test]
    fn the_shares_and_octaves_read_the_towers_own_entries() {
        let tower = tiny_participating(ContactLaw::Rectifying, true);
        let p = tower.participation().expect("participating").clone();
        let lv = tower.layout.levels[1];
        let w = tower.declaration.width;
        let mut g = vec![0i128; tower.theta.len()];
        g[lv.pa_probe_re] = 3;
        g[lv.pa_key_im + w] = -4;
        g[lv.pa_value_re + (p.heads[0] + 1) * w - 1] = 12;
        let shares = tower.participation_shares(&g).expect("shares");
        assert_eq!(shares.len(), tower.declaration.levels);
        assert!(shares[0].iter().all(|h| h.score_thousandths().is_none()));
        assert_eq!((shares[1][0].score.clone(), shares[1][0].value.clone()), (BigUint::from(25u32), BigUint::from(0u32)));
        assert_eq!(shares[1][0].score_thousandths(), Some(1000));
        assert_eq!(shares[1][1].value, BigUint::from(144u32), "the value row past the first head's modes is the second head's");
        assert_eq!(shares[1][1].score_thousandths(), Some(0));
        assert!(tower.participation_shares(&g[1..]).is_err());
        let octaves = tower.mode_octaves();
        assert_eq!(ParticipationDeclaration::founded(&octaves[0], p.section).expect("founded").heads, tower.founded_participation(p.section).expect("founded").heads);
        let bridge = tower.participation_bridge().expect("participating");
        assert!(bridge.iter().all(|b| b.contact_squares > 0 && b.entries == tower.declaration.contacts * w));
    }
}
