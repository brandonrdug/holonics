//! The engine's face (C5 of #603: cut from `field.rs` by object, each item's text as it stood but for its visibility).

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use crate::inherited::tower::{affine, covector, deposit_step, div_nearest, exp_series, face_code, fewer_bits_weighed, fit32, fit64, half_turn, on_step_grain, outer_sum, ratio_adjoint, ratio_to_power, reach, refuse, release, toward, transposed, weighed_code, Result, TowerError, TowerFace, FACE_BITS, FIRST_RATE, MATERIAL_BITS, MOVE_BITS, SECOND_RATE};
#[allow(unused_imports)]
use crate::inherited::keyed_modes::{ln2_face, log2_face, Exponential};
#[allow(unused_imports)]
use rayon::prelude::*;

impl Field {

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

    /// Each unresolved site's face over the region (`None` at a resolved site).
    pub fn faces(&self, region: &Region) -> Result<Vec<Option<TowerFace>>> {
        Ok(self.pass(region, false)?.faces)
    }

    /// Each unresolved site's readout logits over the region, on `2^(−16)` bits (`None` at a
    /// resolved site): the face at `β = 1` is [`Field::tempered`] of them.
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

    /// Each region's faces, read in parallel.
    pub fn read_faces(&self, regions: &[Region]) -> Result<Vec<Vec<Option<TowerFace>>>> {
        regions.par_iter().map(|r| self.faces(r)).collect()
    }
}

impl Field {

    /// [measurement; theory, November 13, P57 item 2 (G132)] **The readout's face from a chart** `r̂` (`D` words on `2^(−16)`): the lift
    /// `R r̂ + b_R`, the encoding and the face at temperature one, as [`Field::face_of`] reads a state after its chart. A reading.
    pub fn face_of_read(&self, read: &[i32]) -> Result<TowerFace> {
        let (d, l) = (&self.declaration, &self.layout);
        let dw = d.width;
        if read.len() != dw {
            return refuse("a chart that is not one word a coordinate");
        }
        let mut y = vec![0i64; dw];
        affine(&self.theta[l.read..l.read + dw * dw], self.reaches().read, dw, read, Some(&self.theta[l.lift_bias..l.lift_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut y)?;
        let mut z = vec![0i64; d.alphabet];
        self.tied(&y, &mut z)?;
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

/// The regions' code on `2^(−20)` bits: the weighed code of the sites before the ports (§16.23, [`crate::inherited::tower::weighed_code`])
/// and the ports' coupling codes (§16.24).
pub(crate) fn code_of(c: &Compared, spans: &[(usize, u64, u64)]) -> i64 {
    weighed_code(&c.pairs, spans) + c.coupled
}

/// [definition; §16.47] The octave of a distance `d ≥ 1` from the question: `⌊log₂ d⌋`, so octave `j` holds `[2^j, 2^(j+1))`.
/// [definition; agent-inferred, November 6, the unified-theory reading of 07:21] **One end, one draw, conditioned on the room**
/// ([`Field::sample_runs`] with `one_end`): `room`'s faces at the release's first read, place by place, and `u` on `2^(−32)`; the
/// length is the places before the first whose void mass passes `u M(R)`, `M(R)` the largest void mass over the room (the
/// running maximum's last value), read exactly as `m_∅(t) T_R 2^32 > u m_R T_t` on 256-bit products; the room's extent where
/// none passes (none where no place carries void mass).
pub fn one_end_length(room: &[Option<&TowerFace>], void: usize, u: u128) -> usize {
    let wide = crate::inherited::context::wide_mul;
    let Some(top) = room.iter().flatten().copied().reduce(|a, b| if wide(b.masses[void], a.total) > wide(a.masses[void], b.total) { b } else { a }) else { return room.len() };
    room.iter().position(|f| f.is_some_and(|f| wide(f.masses[void] << 32, top.total) > wide(u * top.masses[void], f.total))).unwrap_or(room.len())
}
