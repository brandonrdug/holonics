//! **A receiver's face and its code.**
//!
//! `z_t(a) = ⟨E(a), R r̂(x^K_t) + b_R⟩ + c_a`, `p̂_t(a) = 2^(z_a)/Σ_b 2^(z_b)` at the open sites; the loud face's sharpness
//! `β = 2^16 + release(Σ_ℓ κ_ℓ λ_ℓ, 16) + b` where declared; a place's code `−log₂ p̂_t(u_t)` on `2^(−20)`
//!
//! Kind: gate, an open site. Kernels: `field_face*`, `field_tied_face*`, `field_loud_beta`, `field_gather_rows32` (`hnn/resident.rs`).
//! Lean: `HNN/TargetFace`, `HNN/BornFace`.
//! Atlas: `radix.log-chart-carry`, `tower.face-loud-sharpness`, `tower.field-one-end-room`, `tower.field-write-by-the-training-clock`.
//! Records: `2026-11-01_THE_PROBLEM_IS_ONE_FIELD…`, `2026-11-15_THE_FACE_READS…`. The derivations' history is in the records; the items below keep
//! their reasons.

#[allow(unused_imports)]
use crate::field::*;
use num_bigint::BigUint;
#[allow(unused_imports)]
use rayon::prelude::*;

impl Constitution {

    /// [definition; agent-inferred, November 1] **A score's term** (§14.11): `2^z` for `z` on
    /// `2^(−16)` bits, as its whole bits `a = ⌊z⌋` and its fraction's face `2^(f − 1)` on `2^(−62)`
    /// (in `[2^61, 2^62)`), so a term is `face · 2^(a − 61)` and keeps its own exponent.
    pub fn face(&self, z: i64) -> (i64, u128) {
        (z >> FACE_BITS, self.exponential.below_one((z & ((1 << FACE_BITS) - 1)) as i128 - (1i128 << FACE_BITS)))
    }

    /// [§16.44] The face a site's state `x_t` reads through the readout (the chart, the lift `R r̂ + b_R`, the encoding), at
    /// temperature one: what a blank's clock reads its expected duration from.
    pub(crate) fn face_of(&self, x: &[i64], reaches: &Reaches) -> Result<BlankRead> {
        let (d, l) = (&self.declaration, &self.layout);
        let dw = d.width;
        let (mut r, mut s) = (Vec::with_capacity(dw), Vec::with_capacity(d.lanes));
        lane_chart(x, d.lanes, &mut r, &mut s)?;
        let mut y = vec![0i64; dw];
        affine(&self.theta[l.read..l.read + dw * dw], reaches.read, dw, &r, Some(&self.theta[l.lift_bias..l.lift_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut y)?;
        let mut z = vec![0i64; d.alphabet];
        self.tied(&y, &mut z)?;
        Ok(BlankRead { read: r, scale: s, lift: y, face: self.tempered(&z, 1) })
    }

    /// [Brandon, November 15 02:06Z] **The readout's face of a state** `x_t`: [`Constitution::face_of`]'s face with the sharpness a loud face reads from
    /// the state's lanes' powers ([`Constitution::loud_beta`]); the same face on a field whose face does not read its sites' loudness. The readings of a
    /// place's code at its opening read it (a blank's clock keeps `face_of`).
    pub(crate) fn readout_face(&self, x: &[i64], reaches: &Reaches) -> Result<TowerFace> {
        let read = self.face_of(x, reaches)?;
        if !self.declaration.loud {
            return Ok(read.face);
        }
        let mut z = vec![0i64; self.declaration.alphabet];
        let beta = self.loud_beta(&read.scale)?.map(|(b, _)| b);
        self.tied_sharp(&read.lift, beta, &mut z)?;
        Ok(self.tempered(&z, 1))
    }

    /// Each unresolved site's face over the region (`None` at a resolved site).
    pub fn faces(&self, region: &Region) -> Result<Vec<Option<TowerFace>>> {
        Ok(self.pass(region, false)?.faces)
    }

    /// Each unresolved site's readout logits over the region, on `2^(−16)` bits (`None` at a
    /// resolved site): the face at `β = 1` is [`Constitution::tempered`] of them.
    pub fn logits(&self, region: &Region) -> Result<Vec<Option<Vec<i64>>>> {
        Ok(self.pass(region, false)?.logits)
    }

    /// [definition; agent-inferred, November 1] **A face tempered at `β`** (the pump, §4):
    /// `p(a) = 2^(β ℓ(a)) / Σ_b 2^(β ℓ(b))` from logits `ℓ` on `2^(−16)` bits, the masses
    /// `2^(β(ℓ(a) − peak))` on the exponential's `2^(−62)`; at `β = 1` it is the field's own face.
    pub fn tempered(&self, logits: &[i64], beta: u64) -> TowerFace {
        let peak = *logits.iter().max().unwrap_or(&0);
        let masses: Vec<u128> = logits.iter().map(|&zc| self.exponential.below_one((zc as i128 - peak as i128) * beta as i128)).collect();
        let total = masses.iter().sum();
        TowerFace { masses, total }
    }

    /// The region's code on `2^(−20)` bits, and the number of sites it read: `Σ −log₂ p̂_t(u_t)` over its unresolved
    /// sites before its port, and its port's coupling code (§16.24) over the port's places.
    pub fn code(&self, region: &Region) -> Result<(i64, usize)> {
        let faces = self.faces(region)?;
        let end = region.port.map_or(region.classes.len(), |p| p.start);
        let mut code = 0i64;
        let mut count = 0usize;
        for (face, &class) in faces.iter().zip(region.classes).take(end) {
            if let Some(face) = face {
                code += face.code(class);
                count += 1;
            }
        }
        if let Some(port) = region.port {
            code += port_code(&faces, &port)?;
            let stop = port.stop.unwrap_or(region.classes.len()).min(region.classes.len());
            count += (port.start..stop).filter(|&t| region.unresolved[t] && port.heard.is_none_or(|h| h[t])).count();
        }
        Ok((code, count))
    }

    /// [definition; agent-inferred, November 3, §16.26] **The face read through the encoding**: `z(a) = release(Σ_i E(a)_i
    /// y_i, 16) + c_a` for every class `a`, `E(a)` its row of the encoding on `2^(−16)` and `y` the lift on `2^(−16)`.
    pub(crate) fn tied(&self, y: &[i64], z: &mut [i64]) -> Result<()> {
        let (dw, l) = (self.declaration.width, &self.layout);
        for (a, slot) in z.iter_mut().enumerate() {
            let row = &self.theta[l.enc + a * dw..l.enc + (a + 1) * dw];
            let sum: i128 = row.iter().zip(y).map(|(&e, &v)| e as i128 * v as i128).sum();
            *slot = fit64(release(sum, STATE_BITS) as i128 + self.theta[l.read_bias + a] as i128)?;
        }
        Ok(())
    }

    /// [definition; Brandon, November 15 02:06Z] **A site's sharpness from its loudness** ([`Declaration::loud`]): `β = 2^16 +
    /// release(Σ_ℓ κ_ℓ λ_ℓ, 16) + b` on `2^(−16)`, `λ_ℓ` the logarithm on the face's grain of lane `ℓ`'s power `s_ℓ` (the scale the chart divided
    /// it by); `None` on a field whose face does not read its sites' loudness. The readout's face is the one receiver that reads it: a blank's
    /// clock and the opening read their faces at temperature one, each its own receiver (`agent-inferred`: the code's comparison is the
    /// readout's, and a clock's duration is not sharpened by the site it times).
    pub(crate) fn loud_beta(&self, scales: &[i128]) -> Result<Option<(i128, Vec<i64>)>> {
        if !self.declaration.loud {
            return Ok(None);
        }
        let l = &self.layout;
        let lambda: Vec<i64> = scales.iter().map(|&s| log2_grain(s.max(1) as u128)).collect();
        let kappa = &self.theta[l.loud..l.loud + lambda.len()];
        let sum: i128 = kappa.iter().zip(&lambda).map(|(&k, &v)| k as i128 * v as i128).sum();
        let beta = (1i128 << FACE_BITS) + release(sum, FACE_BITS) + self.theta[l.loud + lambda.len()] as i128;
        Ok(Some((beta, lambda)))
    }

    /// [definition; Brandon, November 15 02:06Z] **The return through a loud face's sharpness**, given `δβ` (on `β`'s grain): `δκ_ℓ = release(δβ
    /// λ_ℓ, 16)` and `δb = δβ` into the material's covector `g`, and `δλ_ℓ = release(δβ κ_ℓ, 16)` returned radially into the state the face read,
    /// written into `radial` (`D` words): `∂λ_ℓ/∂x_i = r̂_i / (W s_ℓ ln 2)` on the lane, `r̂` the chart on `2^(−16)`, `s_ℓ` the lane's power and `W`
    /// its width. The chart's own adjoint ([`lane_adjoint`]) keeps only the part off the ray; this is the part along it, which a face that reads
    /// the site's power owes.
    pub(crate) fn loud_return(&self, lambda: &[i64], dbeta: i128, read: &[i32], scales: &[i128], g: &mut [i128], radial: &mut Vec<i64>) -> Result<()> {
        let (l, dw, lanes) = (&self.layout, self.declaration.width, self.declaration.lanes);
        let lw = dw / lanes;
        radial.clear();
        radial.resize(dw, 0);
        for (lane, (&lam, &s)) in lambda.iter().zip(scales).enumerate() {
            g[l.loud + lane] += release(dbeta * lam as i128, FACE_BITS);
            if s == 0 {
                continue;
            }
            let dlam = release(dbeta * self.theta[l.loud + lane] as i128, FACE_BITS) as i128;
            let den = lw as i128 * s * ln2_face();
            for i in lane * lw..(lane + 1) * lw {
                radial[i] = fit64(div_nearest((dlam * read[i] as i128) << LN2_FACE_BITS, den))?;
            }
        }
        g[l.loud + lanes] += dbeta;
        Ok(())
    }

    /// The readout's face at a site with sharpness `β` ([`Constitution::loud_beta`]): `z(a) = release(β v_a, 16) + c_a`, `v_a = release(⟨E(a), y⟩, 16)`;
    /// with no sharpness, [`Constitution::tied`].
    pub(crate) fn tied_sharp(&self, y: &[i64], beta: Option<i128>, z: &mut [i64]) -> Result<()> {
        let Some(beta) = beta else { return self.tied(y, z) };
        let (dw, l) = (self.declaration.width, &self.layout);
        for (a, slot) in z.iter_mut().enumerate() {
            let row = &self.theta[l.enc + a * dw..l.enc + (a + 1) * dw];
            let sum: i128 = row.iter().zip(y).map(|(&e, &v)| e as i128 * v as i128).sum();
            let v = release(sum, STATE_BITS) as i128;
            *slot = fit64(release(beta * v, FACE_BITS) as i128 + self.theta[l.read_bias + a] as i128)?;
        }
        Ok(())
    }

    /// Each region's faces, read in parallel.
    pub fn read_faces(&self, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>> {
        regions.par_iter().map(|r| self.faces(r)).collect()
    }
}

impl Constitution {

    /// [measurement; theory, November 13, P57 item 2 (G132)] **The readout's face from a chart** `r̂` (`D` words on `2^(−16)`): the lift
    /// `R r̂ + b_R`, the encoding and the face at temperature one, as [`Constitution::face_of`] reads a state after its chart. A reading.
    pub fn face_of_read(&self, read: &[i32]) -> Result<TowerFace> {
        if self.declaration.loud {
            return refuse("a face whose sharpness is its site's loudness is read from a chart and its lanes' powers (face_of_chart)");
        }
        self.face_of_chart(read, &[])
    }

    /// [Brandon, November 15 02:06Z] **The readout's face from a chart and its lanes' powers**: as [`Constitution::face_of_read`], with the sharpness the
    /// powers give where the face reads its sites' loudness ([`Constitution::loud_beta`]); the powers are not read on a field whose face does not. A
    /// reading.
    pub fn face_of_chart(&self, read: &[i32], scales: &[i128]) -> Result<TowerFace> {
        let (d, l) = (&self.declaration, &self.layout);
        let dw = d.width;
        if read.len() != dw || (d.loud && scales.len() != d.lanes) {
            return refuse("a chart that is not one word a coordinate, or a loud face's powers that are not one a lane");
        }
        let mut y = vec![0i64; dw];
        affine(&self.theta[l.read..l.read + dw * dw], self.reaches().read, dw, read, Some(&self.theta[l.lift_bias..l.lift_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut y)?;
        let mut z = vec![0i64; d.alphabet];
        let beta = self.loud_beta(scales)?.map(|(b, _)| b);
        self.tied_sharp(&y, beta, &mut z)?;
        Ok(self.tempered(&z, 1))
    }
}

/// A port's coupling code on `2^(−20)` bits from a region's faces (§16.24).
pub(crate) fn port_code(faces: &[Option<TowerFace>], port: &Port) -> Result<i64> {
    Ok(port_reading(&port_faces(faces, port)?, port)?.1)
}

/// A port's places' faces, each `(masses, total)`: every place must carry one, but a port at its boundary or on its letters
/// may hold resolved places, which carry none and are read as `(∅, 0)` (§16.47, [`boundary_reading`], [`letters_reading`]).
pub(crate) fn port_faces<'f>(faces: &'f [Option<TowerFace>], port: &Port) -> Result<Vec<(&'f [u128], u128)>> {
    let stop = port.stop.unwrap_or(faces.len()).min(faces.len());
    faces[port.start..]
        .iter()
        .enumerate()
        .map(|(k, f)| match f {
            _ if port.start + k >= stop || port.heard.is_some_and(|h| !h[port.start + k]) => Ok((&[][..], 0)),
            Some(f) => Ok((f.masses.as_slice(), f.total)),
            None if port.boundary || port.letters => Ok((&[][..], 0)),
            None => refuse("a port's place without a face"),
        })
        .collect()
}

/// The regions' code on `2^(−20)` bits: the weighed code of the sites before the ports (§16.23, [`crate::field::weighed_code`])
/// and the ports' coupling codes (§16.24).
pub(crate) fn code_of(c: &Compared, spans: &[(usize, u64, u64)]) -> i64 {
    weighed_code(&c.pairs, spans) + c.coupled
}

/// [definition; §16.47] The octave of a distance `d ≥ 1` from the question: `⌊log₂ d⌋`, so octave `j` holds `[2^j, 2^(j+1))`.
/// [definition; agent-inferred, November 6, the unified-theory reading of 07:21] **One end, one draw, conditioned on the room**
/// ([`Constitution::sample_runs`] with `one_end`): `room`'s faces at the release's first read, place by place, and `u` on `2^(−32)`; the
/// length is the places before the first whose void mass passes `u M(R)`, `M(R)` the largest void mass over the room (the
/// running maximum's last value), read exactly as `m_∅(t) T_R 2^32 > u m_R T_t` on 256-bit products; the room's extent where
/// none passes (none where no place carries void mass).
pub fn one_end_length(room: &[Option<&TowerFace>], void: usize, u: u128) -> usize {
    let wide = crate::field::wide_mul;
    let Some(top) = room.iter().flatten().copied().reduce(|a, b| if wide(b.masses[void], a.total) > wide(a.masses[void], b.total) { b } else { a }) else { return room.len() };
    room.iter().position(|f| f.is_some_and(|f| wide(f.masses[void] << 32, top.total) > wide(u * top.masses[void], f.total))).unwrap_or(room.len())
}

// The items this object owns that stood in the October tower until C5 (#603), each as it stood.

/// One cell's face: each class's mass `2^(z_a − z_max)` on `2^(−62)`, and their sum.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TowerFace {
    pub masses: Vec<u128>,
    pub total: u128,
}

impl TowerFace {
    /// The class's code, `−log₂ p̂(a)`, on `2^(−20)` bits.
    pub fn code(&self, class: usize) -> i64 {
        face_code(self.masses[class], self.total)
    }

    /// The comparison's descent covector against `target`, `p̂ − [· = target]` on `2^(−24)`: the
    /// one law the reverse scan reads ([`covector`]), handed to an exterior reading.
    pub fn covector(&self, target: usize) -> Vec<i64> {
        covector(self, target)
    }
}

/// A class's code read off its mass and the face's total, `−log₂(mass/total)` on `2^(−20)` bits
/// ([`TowerFace::code`]). Its domain is a positive total and a mass no greater than it, which every
/// face the tower forms satisfies; a face a realization returns is admitted to it before it is read
/// ([`realization::PassRead::admitted`]).
pub fn face_code(mass: u128, total: u128) -> i64 {
    let p = (mass << UNIT_BITS) / total;
    -(log2_face(p.max(1), READ_BITS) as i64)
}

impl Default for TowerFace {
    fn default() -> Self {
        Self { masses: Vec::new(), total: 1 }
    }
}

/// The exact comparison of two sections' codes: does `new` code strictly fewer bits than `old`?
/// `Π p_new > Π p_old`, over the products of their faces' numerators and denominators.
///
/// [definition; agent-inferred, October 27] **The certificate decided by partition.** The products
/// are compared through their logarithms first: each numerator and denominator `v` is read on
/// `2^(−CERTIFICATE_DIGITS)` ([`log2_reading`]), whose reading lies within `CERTIFICATE_SLACK`
/// grains of `log₂ v`. When the two sides' summed readings differ by more than every reading's
/// slack together, the sign of the difference is the sign of `log₂ Π p_new − log₂ Π p_old`, and so
/// the answer of the exact comparison; only inside that band are the products formed
/// ([`fewer_bits_exact`]). The answer is always the exact comparison's: the readings partition the
/// sections into those they decide and those the products decide. The readings are an integer sum,
/// so any partition of the faces sums them to the same bits. Measured October 25, the products
/// took 0.5 s a section at 320 streams and bounded the card's pass. The readings hold for positive
/// values only: a zero mass or total (never a face's, whose masses are at least one; Epime's review
/// of October 27 named the witness `[(0, 3)]` against `[(0, 2)]`) is decided by the products.
pub fn fewer_bits(old: &[(u128, u128)], new: &[(u128, u128)]) -> bool {
    if old.iter().chain(new).any(|&(m, t)| m == 0 || t == 0) {
        return fewer_bits_exact(old, new);
    }
    let side = |faces: &[(u128, u128)]| -> i128 { faces.par_iter().map(|&(m, t)| log2_reading(m) - log2_reading(t)).sum() };
    let difference = side(new) - side(old);
    let slack = CERTIFICATE_SLACK * 2 * (old.len() + new.len()) as i128;
    if difference > slack {
        return checked(true, old, new);
    }
    if difference < -slack {
        return checked(false, old, new);
    }
    fewer_bits_exact(old, new)
}

/// [definition; agent-inferred, November 2, the field's §16.23] **The certificate on a weighed code**: does `new` code
/// strictly fewer bits than `old` when each region's code is weighed by its state's `m/K` (the order-averaged joint
/// code)? `spans` gives each region's open sites (its run of consecutive pairs) and its `(m, K)`. Where every weight is
/// one it is [`fewer_bits`], the products. Otherwise the products cannot be formed (a rational power of a product), so
/// it is decided by partition alone: each region's readings are summed exactly, the difference
/// `ΔW = Σ_r (m_r/K_r) Σ_(i∈r) (log₂ p_new − log₂ p_old)` and its slack `Σ_r (m_r/K_r) · CERTIFICATE_SLACK · 2 · 2|r|`
/// are exact rationals of the readings, and the sign of `ΔW` decides once it passes the slack. The readings are read
/// at `CERTIFICATE_DIGITS` and, where the slack holds the difference, again at [`WEIGHED_DIGITS`], the readings' own
/// floor (their mantissa is released at `2^(−62)`); a difference still inside the slack there is a tie at that floor,
/// and a tie codes no fewer bits.
pub fn fewer_bits_weighed(old: &[(u128, u128)], new: &[(u128, u128)], spans: &[(usize, u64, u64)]) -> bool {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    if spans.iter().all(|&(_, m, k)| m == k) {
        return fewer_bits(old, new);
    }
    if old.iter().chain(new).any(|&(m, t)| m == 0 || t == 0) {
        return false;
    }
    for digits in [CERTIFICATE_DIGITS, WEIGHED_DIGITS] {
        let (mut difference, mut slack) = (BigRational::from_integer(BigInt::from(0)), BigRational::from_integer(BigInt::from(0)));
        let mut at = 0usize;
        for &(count, m, k) in spans {
            let range = at..at + count;
            at += count;
            let side = |faces: &[(u128, u128)]| -> i128 { faces[range.clone()].par_iter().map(|&(mm, t)| log2_reading_at(mm, digits) - log2_reading_at(t, digits)).sum() };
            let w = BigRational::new(BigInt::from(m), BigInt::from(k));
            difference += &w * &BigRational::from_integer(BigInt::from(side(new) - side(old)));
            slack += &w * &BigRational::from_integer(BigInt::from(CERTIFICATE_SLACK * 2 * 2 * count as i128));
        }
        if difference > slack {
            return true;
        }
        if difference < -slack {
            return false;
        }
    }
    false
}

/// The weighed certificate's finer readings: the readings' own floor (a mantissa released at `2^(−62)` holds a
/// reading within one grain and `2^(−60)` of `log₂ v`, so three grains at `2^(−60)`).
pub const WEIGHED_DIGITS: u32 = UNIT_BITS - 2;

/// [definition; agent-inferred, November 2, the field's §16.23] **A weighed code** on `2^(−20)` bits: each region's
/// code `Σ_(i∈r) −log₂ p_i` read at `m_r/K_r`, released once a region to the nearest (half away from zero), summed.
pub fn weighed_code(pairs: &[(u128, u128)], spans: &[(usize, u64, u64)]) -> i64 {
    let mut at = 0usize;
    let mut sum = 0i64;
    for &(count, m, k) in spans {
        let code: i64 = pairs[at..at + count].par_iter().map(|&(mm, t)| face_code(mm, t)).sum();
        at += count;
        sum += if m == k { code } else { div_nearest(code as i128 * m as i128, k as i128) as i64 };
    }
    sum
}

/// A decision the readings made. Built with the `certificate-check` feature, it is compared with the
/// products and a disagreement stops the run: the acceptance read that the partition decides as the
/// products do on every call of a whole pass. Without the feature it is the decision.
pub fn checked(decided: bool, old: &[(u128, u128)], new: &[(u128, u128)]) -> bool {
    #[cfg(feature = "certificate-check")]
    assert_eq!(decided, fewer_bits_exact(old, new), "the certificate's readings decided against its products");
    let _ = (old, new);
    decided
}

/// The fractional digits of the certificate's logarithmic readings.
pub const CERTIFICATE_DIGITS: u32 = 32;

/// How far a reading may lie from `log₂ v`, in grains of `2^(−CERTIFICATE_DIGITS)`. With `μ` the
/// mantissa, `d_k` the digits and `ε_k ≥ 0` the logarithm each release at `2^(−62)` takes off
/// (`ε_k < 2^(−61)`, the mantissa staying in `[1, 2)`), the squarings unroll to
/// `log₂ μ = Σ_(k≤K) 2^(−k) d_k + 2^(−K) log₂ μ_K + Σ_(k≤K) 2^(−k) ε_k`, so a reading lies below
/// `log₂ v` by less than one grain and `2^(−60)` (the entry release included), never above it;
/// three grains hold that with room.
pub const CERTIFICATE_SLACK: i128 = 3;

/// The products themselves: `Π m_new · Π t_old > Π m_old · Π t_new`.
pub fn fewer_bits_exact(old: &[(u128, u128)], new: &[(u128, u128)]) -> bool {
    // The halves of a long product are formed together: an exact product is the same in any
    // grouping.
    fn product(v: &[u128]) -> BigUint {
        match v.len() {
            0 => BigUint::from(1u8),
            1 => BigUint::from(v[0]),
            n if n < 1 << 12 => product(&v[..n / 2]) * product(&v[n / 2..]),
            n => {
                let (a, b) = rayon::join(|| product(&v[..n / 2]), || product(&v[n / 2..]));
                a * b
            }
        }
    }
    let (om, ot): (Vec<u128>, Vec<u128>) = old.iter().cloned().unzip();
    let (nm, nt): (Vec<u128>, Vec<u128>) = new.iter().cloned().unzip();
    let ((pnm, pot), (pom, pnt)) = rayon::join(|| rayon::join(|| product(&nm), || product(&ot)), || rayon::join(|| product(&om), || product(&nt)));
    pnm * pot > pom * pnt
}
