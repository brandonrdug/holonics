//! **The overture founds a participating level** (#146 step 2; record
//! `2026-10-29_INHERITED_WEIGHTS_ARE_AN_OVERTURE…` §§3 and 6).
//!
//! [definition; agent-inferred, October 30] A source's attention block ([`AttentionBlock`]) founds
//! one level's participation ([`Tower::found_attention`]). Each query head of dimension `d` is one
//! native head of `d` modes:
//!
//! ```text
//! rotary modes   m < d/2     u_m = e^(−iω_m),  ω_m = θ^(−2m/d)      Ȟ_m = c (q_m + i q_(m+d/2)),  H_m = k_m + i k_(m+d/2)
//! still modes    d/2 + j     u = 1                                  Ψ_j = v_j + i v_(j+d/2)
//! read           Cᵃ_re[o, d/2 + j] = O[o, h d + j],   Cᵃ_im[o, d/2 + j] = −O[o, h d + j + d/2]
//! scale          c = log₂ e · 2^(beta_shift) / √d
//! ```
//!
//! with `q = Q (g ⊙ x)` and `k`, `v` likewise (a grouped key/value head read by each query head it
//! serves). Through the frames, `Re⟨conj(U_i) Ȟ_i, conj(U_j) H_j⟩ = c q'_i · k'_j`, the source's
//! rotated score (its turn `e^(i t ω_m)` and the frame's `e^(i (t+1) ω_m)` differ by one place on
//! every site, which the pairing does not see). The source weighs by `e^s` and participation by
//! `2^z`, so `c` carries `log₂ e`, and `β = 2^(−beta_shift)` with it gives `z = s log₂ e`. A still
//! mode's current is the weighted value untransported, the source's head, and `Re(Cᵃ y)` is the
//! output projection's read of all the heads. The moves sit at the margin `|λ| = 1 − 2^(−12)`, and
//! the friction at zero, so only the frames carry the source's place. The modes' own push and read,
//! the gate and the turn rest at zero: the level's modes are silent, and a site's frame is its
//! moves'.
//!
//! Every chart and read coefficient is formed exactly (the gain folded into the charts, `log₂ e`
//! and `ω_m` as their navigators' faces) and released onto the material grain `2^(−24)` once, its
//! remainder counted ([`Released`]); the moves are released onto `2^(−30)`.
//!
//! **The check** ([`Tower::attention_check`]). The charts read the level's input as it arrives,
//! and the source reads its norm (record §6, owed term 1), so the check presents inputs of unit
//! power, where the two agree up to the source's `ε`. A sibling of the founded tower whose
//! encoding rows are those inputs reads them in order, and each site's participating current and
//! read are compared with the source's operation computed at the boundary
//! ([`AttentionBlock::reference`]).
use super::*;
use crate::hnn::overture::{cis, log2_e_face, rotary_rate, AttentionBlock, AttentionReference, AttentionShape, Dyadic, IntakeRefusal, Released, REFERENCE_BITS};

/// What founding an attention block released: its charts' coefficients and its read's.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AttentionFounding {
    pub charts: Released,
    pub read: Released,
}

/// How far the native reading lies from the source's, on `2^(−REFERENCE_BITS)`: the largest
/// difference of a component and the largest component of the source's.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Gap {
    pub difference: i128,
    pub largest: i128,
}

impl Gap {
    fn meet(&mut self, native: i128, source: i128) {
        self.difference = self.difference.max((native - source).abs());
        self.largest = self.largest.max(source.abs());
    }

    /// Whether the difference is at most `2^(−bits)` of the largest component.
    pub fn within(self, bits: u32) -> bool {
        self.difference << bits <= self.largest
    }
}

/// [definition; agent-inferred, October 30] **The extraction check's reading**: each head's
/// current against the source's head, its rotary modes against zero, and the read against the
/// output projection's, over every site; beside them each head's participation entropy at the
/// last site ([`Participation::entropy`], on `2^(−20)` bits), which reads whether the weights the
/// check passed through were spread evenly (`log₂` of the sites) or held by a few sites.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttentionCheck {
    pub heads: Vec<Gap>,
    pub read: Gap,
    pub sites: usize,
    pub entropies: Vec<i128>,
}

impl AttentionCheck {
    /// Whether every head and the read lie within `2^(−bits)` of their largest component.
    pub fn within(&self, bits: u32) -> bool {
        self.heads.iter().all(|g| g.within(bits)) && self.read.within(bits)
    }
}

impl Tower {
    /// [definition; agent-inferred, October 30] **An attention block founds `level`'s
    /// participation** (the module's law). Refused without participation, under a news clock (a
    /// clocked level's sites are its own ticks, not every arrival), and when the block's width,
    /// heads or head dimension are not the level's: participation's heads `d` modes each, `h` of
    /// them over a bank of `h d` modes and a face of the block's width.
    pub fn found_attention(&mut self, level: usize, block: &AttentionBlock) -> std::result::Result<AttentionFounding, IntakeRefusal> {
        let refused = |what| IntakeRefusal::Founding { what };
        let Some(p) = self.participation.clone() else {
            return Err(refused("an attention founds a participating level: participation joins first"));
        };
        if self.news.is_some() {
            return Err(refused("an attention founded under a news clock: a clocked level's sites are its own ticks"));
        }
        let AttentionShape { width: w, heads: h, kv_heads: hk, head_dim: d, theta } = block.shape;
        let dec = self.declaration;
        if level >= dec.levels || dec.width != w || dec.modes != h * d || p.heads != vec![d; h] || hk == 0 || h % hk != 0 {
            return Err(refused("an attention block whose width, heads or head dimension are not the level's"));
        }
        if block.gain.len() != w || block.query.len() != h * d * w || block.key.len() != hk * d * w || block.value.len() != hk * d * w || block.output.len() != w * h * d {
            return Err(refused("an attention block whose parts are not of its declared shape"));
        }
        let root = d.isqrt();
        if root * root != d {
            return Err(refused("a head dimension whose square root is not an integer"));
        }
        let (n, half, group) = (dec.modes, d / 2, h / hk);
        let lv = self.layout.levels[level];
        let t = &mut self.theta;
        let mut rest = |start: usize, len: usize| t[start..start + len].fill(0);
        for (start, len) in [(lv.push_re, n * w), (lv.push_im, n * w), (lv.read_re, w * n), (lv.read_im, w * n), (lv.gate, n * w), (lv.gate_bias, n)] {
            rest(start, len);
        }
        if dec.turned {
            rest(lv.turn, n * w);
            rest(lv.turn_bias, n);
        }
        for start in [lv.pa_probe_re, lv.pa_probe_im, lv.pa_key_re, lv.pa_key_im, lv.pa_value_re, lv.pa_value_im] {
            rest(start, n * w);
        }
        rest(lv.pa_read_re, w * n);
        rest(lv.pa_read_im, w * n);
        rest(lv.pa_friction, h);
        // c = log₂ e · 2^(beta_shift) / √d on 2^(−60).
        let scale = super::div_nearest(log2_e_face() << p.beta_shift, root as i128);
        let mut founding = AttentionFounding::default();
        // A chart row: projection row `row` of `rows` with the gain folded in (and `c` on the
        // probe), released onto the material grain.
        let mut chart = |out: usize, rows: &[Dyadic], row: usize, scaled: bool, released: &mut Released| -> std::result::Result<(), IntakeRefusal> {
            for (i, (a, g)) in rows[row * w..(row + 1) * w].iter().zip(&block.gain).enumerate() {
                let (mut numerator, mut exponent) = (a.numerator as i128 * g.numerator as i128, a.exponent + g.exponent);
                if scaled {
                    numerator *= scale;
                    exponent -= 60;
                }
                t[out + i] = released.take(numerator, exponent, MATERIAL_BITS)?;
            }
            Ok(())
        };
        for head in 0..h {
            let kv = head / group;
            for m in 0..half {
                let (rotary, still) = (head * d + m, head * d + half + m);
                chart(lv.pa_probe_re + rotary * w, &block.query, head * d + m, true, &mut founding.charts)?;
                chart(lv.pa_probe_im + rotary * w, &block.query, head * d + m + half, true, &mut founding.charts)?;
                chart(lv.pa_key_re + rotary * w, &block.key, kv * d + m, false, &mut founding.charts)?;
                chart(lv.pa_key_im + rotary * w, &block.key, kv * d + m + half, false, &mut founding.charts)?;
                chart(lv.pa_value_re + still * w, &block.value, kv * d + m, false, &mut founding.charts)?;
                chart(lv.pa_value_im + still * w, &block.value, kv * d + m + half, false, &mut founding.charts)?;
            }
        }
        let cols = h * d;
        for o in 0..w {
            for head in 0..h {
                for j in 0..half {
                    let still = head * d + half + j;
                    let (re, im) = (block.output[o * cols + head * d + j], block.output[o * cols + head * d + j + half]);
                    t[lv.pa_read_re + o * n + still] = founding.read.take(re.numerator as i128, re.exponent, MATERIAL_BITS)?;
                    t[lv.pa_read_im + o * n + still] = founding.read.take(-(im.numerator as i128), im.exponent, MATERIAL_BITS)?;
                }
            }
        }
        // The moves at the margin: a rotary mode turns by e^(−iω_m) a site, a still mode not at all.
        let margin = radius();
        for head in 0..h {
            for m in 0..half {
                let (c, s) = cis(-rotary_rate(theta, m, d, MOVE_BITS), MOVE_BITS)?;
                let (rotary, still) = (head * d + m, head * d + half + m);
                t[lv.move_re + rotary] = fit32(release(margin * c, MOVE_BITS), "a founded move outgrew its 32-bit carrier")?;
                t[lv.move_im + rotary] = fit32(release(margin * s, MOVE_BITS), "a founded move outgrew its 32-bit carrier")?;
                t[lv.move_re + still] = fit32(margin, "a founded move outgrew its 32-bit carrier")?;
                t[lv.move_im + still] = 0;
            }
        }
        Ok(founding)
    }

    /// [definition; agent-inferred, October 30] **The extraction check** (the module's law): a
    /// sibling of this tower whose encoding rows `0..k` are `inputs` (on the face's `2^(−16)`, each
    /// of unit power) reads the classes `0..k` from rest, and at each site level 0's participating
    /// current and read are compared with `reference`, the source block's operation on the same
    /// inputs. A head's still mode `j` holds the source head's `(o_j, o_(j+d/2))`, its rotary modes
    /// hold nothing, and the read is `r̂ · ‖r‖_rms`. Refused without participation, under a news
    /// clock, for more inputs than the alphabet holds or one section spans, and for a reference of
    /// other sites or heads.
    pub fn attention_check(&self, inputs: &[Vec<i32>], reference: &AttentionReference) -> std::result::Result<AttentionCheck, IntakeRefusal> {
        let refused = |what| IntakeRefusal::Founding { what };
        let Some(p) = &self.participation else {
            return Err(refused("a check of a participating level: participation joins first"));
        };
        let dec = self.declaration;
        let (w, k) = (dec.width, inputs.len());
        let d = p.heads[0];
        if self.news.is_some() || k == 0 || k > dec.alphabet || k > p.section || p.heads.iter().any(|&m| m != d) || d % 2 != 0 {
            return Err(refused("a check reads every arrival as a site of one section, over heads of one even dimension"));
        }
        let h = p.heads.len();
        if inputs.iter().any(|x| x.len() != w) || reference.heads.len() != k || reference.output.len() != k || reference.heads.iter().any(|s| s.len() != h || s.iter().any(|o| o.len() != d)) || reference.output.iter().any(|o| o.len() != w) {
            return Err(refused("a check whose inputs or reference are not the level's"));
        }
        let mut sibling = self.clone();
        let e = sibling.layout.encoding;
        for (u, x) in inputs.iter().enumerate() {
            sibling.theta[e + u * w..e + (u + 1) * w].copy_from_slice(x);
        }
        let reaches = sibling.reaches();
        let mut state = sibling.rest();
        let to = REFERENCE_BITS - FACE_BITS;
        let mut check = AttentionCheck { heads: vec![Gap::default(); h], read: Gap::default(), sites: k, entropies: Vec::new() };
        for u in 0..k {
            let cell = sibling.step(&mut state, u, &reaches)?;
            let pc = cell.levels[0].participation.as_ref().ok_or(refused("a participating level read no participation"))?;
            for (head, gap) in check.heads.iter_mut().enumerate() {
                let source = &reference.heads[u][head];
                for m in 0..d / 2 {
                    let (rotary, still) = (pc.current[head * d + m], pc.current[head * d + d / 2 + m]);
                    gap.meet((rotary.0 as i128) << to, 0);
                    gap.meet((rotary.1 as i128) << to, 0);
                    gap.meet((still.0 as i128) << to, source[m]);
                    gap.meet((still.1 as i128) << to, source[m + d / 2]);
                }
            }
            if u + 1 == k {
                let site = pc.site.as_ref().ok_or(refused("a participating level admitted no site"))?;
                check.entropies = site.parts.iter().map(Participation::entropy).collect();
            }
            // r = r̂ ‖r‖_rms: both on 2^(−16), their product on 2^(−32).
            for (o, &r) in pc.read.iter().enumerate() {
                check.read.meet((r as i128 * pc.read_scale) << (REFERENCE_BITS - 2 * FACE_BITS), reference.output[u][o]);
            }
        }
        Ok(check)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::overture::{AttentionShape, Dyadic};

    /// A key stream's word read as a dyadic `±(1..=127) · 2^(−8)`, zero kept out.
    fn coefficient(word: u32) -> Dyadic {
        let magnitude = (word % 127) as i64 + 1;
        Dyadic::reduced(if word & 0x8000_0000 != 0 { -magnitude } else { magnitude }, -8)
    }

    fn block(shape: AttentionShape, seed: u64) -> AttentionBlock {
        let AttentionShape { width: w, heads: h, kv_heads: hk, head_dim: d, .. } = shape;
        let mut at = seed;
        let mut draw = |count: usize| -> Vec<Dyadic> {
            (0..count)
                .map(|_| {
                    at = at.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    coefficient((at >> 32) as u32)
                })
                .collect()
        };
        let gain = (0..w).map(|i| Dyadic::reduced(64 + (i as i64 % 5) * 16, -6)).collect();
        AttentionBlock { shape, gain, query: draw(h * d * w), key: draw(hk * d * w), value: draw(hk * d * w), output: draw(w * h * d) }
    }

    /// `±1` inputs on `2^(−16)`, each of unit power.
    fn inputs(k: usize, w: usize) -> Vec<Vec<i32>> {
        (0..k).map(|u| (0..w).map(|i| if (u * 7 + i * i * 3 + i * u) % 5 < 2 { -(1 << FACE_BITS) } else { 1 << FACE_BITS }).collect()).collect()
    }

    fn founded(shape: AttentionShape, sites: usize) -> Tower {
        let AttentionShape { width: w, heads: h, head_dim: d, .. } = shape;
        let declaration = TowerDeclaration { alphabet: sites.max(2), width: w, modes: h * d, contacts: 2, levels: 1, gated: true, turned: false, pumped: false, contact: ContactLaw::Rectifying };
        let keys: Vec<u8> = (0..20_000u64).flat_map(|i| (i.wrapping_mul(2654435761) ^ (i * i)).to_be_bytes()[4..].to_vec()).collect();
        let mut tower = Tower::found(declaration, &keys).expect("founded");
        tower.join_participation(ParticipationDeclaration::new(vec![d; h], sites, 1).expect("declared")).expect("joined");
        tower
    }

    /// [agent-inferred, October 30] A founded level reads a grouped block's attention as the
    /// source computes it: every head's current and the read within `2^(−8)` of their largest
    /// component over six sites (`d = 4`, so `c = log₂ e`; two query heads share a key/value head).
    #[test]
    fn a_founded_level_reads_the_source_blocks_attention() {
        let shape = AttentionShape { width: 8, heads: 2, kv_heads: 1, head_dim: 4, theta: 10_000 };
        let source = block(shape, 7);
        let mut tower = founded(shape, 6);
        let founding = tower.found_attention(0, &source).expect("founded");
        // Six charts' rows of the width on each of a head's two rotary/still pairs; the read's two
        // parts on each still mode.
        assert_eq!(founding.charts.coefficients, 2 * 2 * 6 * 8);
        assert_eq!(founding.read.coefficients, 8 * 2 * 2 * 2);
        let x = inputs(6, 8);
        let wide: Vec<Vec<i64>> = x.iter().map(|r| r.iter().map(|&v| v as i64).collect()).collect();
        let reference = source.reference(&wide, FACE_BITS).expect("reference");
        let check = tower.attention_check(&x, &reference).expect("checked");
        assert!(check.within(8), "{check:?}");
        assert!(check.heads.iter().all(|g| g.largest > 0) && check.read.largest > 0);
        // The foil: the rotary modes turned the other way. The frames then carry the source's
        // place backwards and the check fails, so it reads the turn, not only the values.
        let mut turned = tower.clone();
        let lv = turned.layout.levels[0];
        for head in 0..2 {
            for m in 0..2 {
                turned.theta[lv.move_im + head * 4 + m] *= -1;
            }
        }
        let foil = turned.attention_check(&x, &reference).expect("checked");
        assert!(!foil.within(8), "{foil:?}");
    }

    /// The founding is refused off its law: without participation, and for a block whose head
    /// dimension is not the level's.
    #[test]
    fn a_founding_off_the_levels_shape_is_refused() {
        let shape = AttentionShape { width: 8, heads: 2, kv_heads: 1, head_dim: 4, theta: 10_000 };
        let source = block(shape, 7);
        let mut tower = founded(shape, 6);
        let other = AttentionShape { head_dim: 2, heads: 4, ..shape };
        assert!(matches!(tower.found_attention(0, &AttentionBlock { shape: other, ..source.clone() }), Err(IntakeRefusal::Founding { .. })));
        let declaration = TowerDeclaration { alphabet: 6, width: 8, modes: 8, contacts: 2, levels: 1, gated: true, turned: false, pumped: false, contact: ContactLaw::Rectifying };
        let keys: Vec<u8> = (0..20_000u64).flat_map(|i| (i.wrapping_mul(2654435761) ^ (i * i)).to_be_bytes()[4..].to_vec()).collect();
        let mut bare = Tower::found(declaration, &keys).expect("founded");
        assert!(matches!(bare.found_attention(0, &source), Err(IntakeRefusal::Founding { .. })));
    }
}
