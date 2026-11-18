//! [definition; the lead, November 17, the founding records; agent-inferred realization] **The closed face**: what a site's rows close to
//! on a ring whose keys were located from the field's own rows, mixed with the field's own face ([`Declaration::closed`]).
//!
//! A head's row at the last tick holds known sources `s` with shares `p_s` and classes `u_s`. On a ring with keys `K_e` (a member's
//! eigenvalue at unit modulus under each closed character, zero off the ring) the likelihood that a pair of members composes to `x` is
//! `c(u, u′, x) = (1 + Σ_e Re K_e(u) K_e(u′) conj K_e(x)) / (E + 1)`: one where `u + u′ = x` on the ring and zero elsewhere with true
//! characters. The row's ring density is `R_h(x) = Σ_(s ≠ s′) p_s p_s′ c(u_s, u_s′, x)`, its mass `M_h = Σ_x R_h(x)` (the share of the row's
//! pairs that are pairs of members), and the site's face is
//!
//! `p(x) = (1 − Σ_h w_h M_h) p_field(x) + Σ_h w_h R_h(x)`,
//!
//! with `w` the face of the odds `(0, z_1 … z_H)`, `z_h = L_h r̂ + ℓ_h` read from the chart the readout reads. A mixture's harm at a place
//! where no pair closes is bounded by its weight, and its covector on the row's shares, `−(w_h / (p ln 2)) (∂R_h(x*) − p_field(x*) ∂M_h)`,
//! is the closure's pull: it draws the row to the pairs that close with the written symbol (atlas `key.closure-target-of-a-row`), which
//! the comparison of the field's own face cannot do while the product has no reader (the saddle of November 16).
//!
//! Why this form and not a return into the site's state: read on November 17, a product returned into the state lowered a one-place
//! receiver's digits and harmed every place where no pair closes once a run extended past its answer (the places past a line feed from
//! 1.99 to 3.89 nats, held), and a release derailed. An attempt: the keys take no deposit yet, the densities are released to `2^(−30)`,
//! and a density a located key leaves below zero is read as zero (the reverse then reads its slope as if it stood).

use crate::field::*;

/// The grain of the closed face's weights, densities and masses, `2^(−30)`.
pub(crate) const CLOSED_BITS: u32 = 30;

/// What a site's mixture keeps for its reverse.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Mix {
    /// The field's own face.
    pub(crate) field: Option<TowerFace>,
    /// Each head's weight `w_h` on `2^(−30)`.
    pub(crate) weights: Vec<i128>,
    /// Each head's ring density at each ring class, `[h][x]` on `2^(−30)`.
    pub(crate) ring: Vec<Vec<i128>>,
    /// Each head's mass `M_h` on `2^(−30)`.
    pub(crate) mass: Vec<i128>,
    /// `1 − Σ_h w_h M_h` on `2^(−60)`.
    pub(crate) alpha: i128,
}

/// A row's members: each known source on the ring as (its index in the row, its class, its share on `2^(−30)`).
type Members = Vec<(usize, usize, i128)>;

impl Constitution {
    /// The ring's classes: those whose key is not zero.
    pub(crate) fn closed_ring(&self) -> Vec<usize> {
        let (d, l) = (&self.declaration, &self.layout);
        let w = 2 * d.closed;
        (0..d.alphabet).filter(|a| self.theta[l.closed_key + a * w..l.closed_key + (a + 1) * w].iter().any(|&v| v != 0)).collect()
    }

    fn closed_key(&self, class: usize, e: usize) -> (i128, i128) {
        let (d, l) = (&self.declaration, &self.layout);
        (self.theta[l.closed_key + class * 2 * d.closed + e] as i128, self.theta[l.closed_key + class * 2 * d.closed + d.closed + e] as i128)
    }

    /// A row's members, the sum of their shares, and `Y_e = Σ_s p_s K_e(u_s)` on `2^(−30)`.
    fn closed_row(&self, row: &[Source], known: &[usize]) -> (Members, i128, Vec<(i128, i128)>) {
        let d = &self.declaration;
        let w = 2 * d.closed;
        let l = &self.layout;
        let members: Members = row
            .iter()
            .enumerate()
            .filter(|(_, src)| known[src.j as usize] < d.alphabet && self.theta[l.closed_key + known[src.j as usize] * w..l.closed_key + (known[src.j as usize] + 1) * w].iter().any(|&v| v != 0))
            .map(|(k, src)| (k, known[src.j as usize], release(src.p as i128, SHARE_BITS - CLOSED_BITS)))
            .collect();
        let total = members.iter().map(|m| m.2).sum();
        let y = (0..d.closed)
            .map(|e| {
                members.iter().fold((0i128, 0i128), |(yr, yi), &(_, u, p)| {
                    let (kr, ki) = self.closed_key(u, e);
                    (yr + release(p * kr, FACE_BITS), yi + release(p * ki, FACE_BITS))
                })
            })
            .collect();
        (members, total, y)
    }

    /// A row's ring density at each ring class, on `2^(−30)`: `(P_pairs + Σ_e Re conj K_e(x) E_e) / (E + 1)` with `E_e = Y_e² − Σ_s t_s²`
    /// and `P_pairs = (Σ p)² − Σ p²`, a value below zero read as zero.
    fn closed_density(&self, members: &Members, total: i128, y: &[(i128, i128)], ring: &[usize]) -> Vec<i128> {
        let closed = self.declaration.closed;
        if members.len() < 2 {
            return vec![0; ring.len()];
        }
        let pairs = total * total - members.iter().map(|m| m.2 * m.2).sum::<i128>();
        let e: Vec<(i128, i128)> = (0..closed)
            .map(|e| {
                let (mut sr, mut si) = (0i128, 0i128);
                for &(_, u, p) in members {
                    let (kr, ki) = self.closed_key(u, e);
                    let (tr, ti) = (release(p * kr, FACE_BITS), release(p * ki, FACE_BITS));
                    sr += tr * tr - ti * ti;
                    si += 2 * tr * ti;
                }
                let (yr, yi) = y[e];
                (yr * yr - yi * yi - sr, 2 * yr * yi - si)
            })
            .collect();
        ring.iter()
            .map(|&x| {
                let num = pairs + (0..closed).map(|k| { let (kr, ki) = self.closed_key(x, k); release(kr * e[k].0 + ki * e[k].1, FACE_BITS) }).sum::<i128>();
                release(div_nearest(num, closed as i128 + 1).max(0), CLOSED_BITS)
            })
            .collect()
    }

    /// The site's face mixed with what its heads' last-tick rows close to ([`crate::closed`]): `field` the field's own face, `rows` each
    /// head's row at the site, `known` each site's written class where known, `chart` the chart the readout read.
    pub(crate) fn closed_mix(&self, field: TowerFace, rows: &[&[Source]], known: &[usize], chart: &[i32]) -> Result<(TowerFace, Mix)> {
        let (d, l) = (&self.declaration, &self.layout);
        let (heads, dw) = (d.heads, d.width);
        let mut z = vec![0i64; heads + 1];
        affine(&self.theta[l.closed_odds..l.closed_odds + heads * dw], reach(&self.theta[l.closed_odds..l.closed_odds + heads * dw]), dw, chart, Some(&self.theta[l.closed_odds_bias..l.closed_odds_bias + heads]), MATERIAL_BITS, MATERIAL_BITS, &mut z[1..])?;
        let odds = self.tempered(&z, 1);
        let weights: Vec<i128> = (0..heads).map(|h| div_nearest((odds.masses[h + 1] as i128) << CLOSED_BITS, odds.total as i128)).collect();
        let ring_classes = self.closed_ring();
        let ring: Vec<Vec<i128>> = rows
            .iter()
            .map(|row| {
                let (members, total, y) = self.closed_row(row, known);
                self.closed_density(&members, total, &y, &ring_classes)
            })
            .collect();
        let mass: Vec<i128> = ring.iter().map(|r| r.iter().sum()).collect();
        let alpha = ((1i128 << (2 * CLOSED_BITS)) - weights.iter().zip(&mass).map(|(w, m)| w * m).sum::<i128>()).max(0);
        let mut masses: Vec<u128> = field.masses.iter().map(|&m| release(m as i128 * alpha, 2 * CLOSED_BITS) as u128).collect();
        for (xi, &c) in ring_classes.iter().enumerate() {
            let mixed = release(weights.iter().zip(&ring).map(|(w, r)| w * r[xi]).sum::<i128>(), CLOSED_BITS);
            masses[c] += release(field.total as i128 * mixed, CLOSED_BITS) as u128;
        }
        let total = masses.iter().sum();
        Ok((TowerFace { masses, total }, Mix { field: Some(field), weights, ring, mass, alpha }))
    }

    /// The mixture's reverse at a site compared with `target` ([`crate::closed`]): the field's responsibility `ρ = α p_field(x*) / p(x*)` on
    /// `2^(−30)`, by which the field's own covector is scaled; each head's odds covector on `2^(−24)`; and each head's covector on its
    /// row's shares on `2^(−40)`, a value a source (empty where the head's row holds no pair of members). `wm / wk` is the region's
    /// weight on the place, as the face's covector takes it. `None` where the mixed face gives the written class no mass.
    #[allow(clippy::type_complexity)]
    pub(crate) fn closed_back(&self, mix: &Mix, mixed: &TowerFace, rows: &[&[Source]], known: &[usize], target: usize, wm: u64, wk: u64) -> Result<Option<(i128, Vec<i64>, Vec<Vec<i128>>)>> {
        let closed = self.declaration.closed;
        let field = mix.field.as_ref().ok_or(TowerError::Refused("a mixture without its field's face"))?;
        let one = 1i128 << CLOSED_BITS;
        let pf = div_nearest((field.masses[target] as i128) << CLOSED_BITS, field.total as i128);
        let pm = div_nearest((mixed.masses[target] as i128) << CLOSED_BITS, mixed.total as i128);
        if pm == 0 {
            return Ok(None);
        }
        let weigh = |v: i128| -> i128 { if wm == wk { v } else { div_nearest(v * wm as i128, wk as i128) } };
        let rho = div_nearest(release(mix.alpha * pf, CLOSED_BITS), pm).clamp(0, one);
        let ring_classes = self.closed_ring();
        let at = ring_classes.iter().position(|&c| c == target);
        // A_h = R_h(x*) − M_h p_field(x*), and its mean under the weights.
        let a: Vec<i128> = (0..rows.len()).map(|h| at.map_or(0, |xi| mix.ring[h][xi]) - release(mix.mass[h] * pf, CLOSED_BITS)).collect();
        let mean = release(mix.weights.iter().zip(&a).map(|(w, a)| w * a).sum::<i128>(), CLOSED_BITS);
        let dzo: Vec<i64> = (0..rows.len())
            .map(|h| fit64(weigh(release(div_nearest(-mix.weights[h] * (a[h] - mean), pm), CLOSED_BITS - crate::field::COVECTOR_BITS))))
            .collect::<Result<_>>()?;
        let ln2 = ln2_face();
        let mut extra = Vec::with_capacity(rows.len());
        for (h, row) in rows.iter().enumerate() {
            let (members, total, y) = self.closed_row(row, known);
            if members.len() < 2 || mix.weights[h] == 0 {
                extra.push(Vec::new());
                continue;
            }
            let mut dp = vec![0i128; row.len()];
            for &(k, u, p) in &members {
                // a_s(x) = ((P − p_s) + Re Σ_e K_e(u_s) conj K_e(x) (Y_e − t_s,e)) / (E + 1) on 2^(−30), at the target and summed over the ring.
                let slope = |x: usize| -> i128 {
                    let keyed: i128 = (0..closed)
                        .map(|e| {
                            let ((kr, ki), (xr, xi)) = (self.closed_key(u, e), self.closed_key(x, e));
                            let (dr, di) = (y[e].0 - release(p * kr, FACE_BITS), y[e].1 - release(p * ki, FACE_BITS));
                            // Re[(K conj K_x)(Y − t)], the keys' product released once.
                            let (pr, pi) = (release(kr * xr + ki * xi, FACE_BITS), release(ki * xr - kr * xi, FACE_BITS));
                            release(pr * dr - pi * di, FACE_BITS)
                        })
                        .sum();
                    div_nearest(total - p + keyed, closed as i128 + 1)
                };
                let here = at.map_or(0, |xi| slope(ring_classes[xi]));
                let every: i128 = ring_classes.iter().map(|&x| slope(x)).sum();
                let v = here - release(pf * every, CLOSED_BITS);
                // −2 w_h v / (p ln 2), from 2^(−30) to the shares' covector grain 2^(−40).
                let bits = div_nearest(div_nearest(-2 * mix.weights[h] * v, pm) << LN2_BITS, ln2);
                dp[k] = weigh(bits << (FACE_BITS + crate::field::COVECTOR_BITS - CLOSED_BITS));
            }
            extra.push(dp);
        }
        Ok(Some((rho, dzo, extra)))
    }
}
