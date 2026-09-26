//! **The receiving phases and the read at the receiver's grain.**
//!
//! [definition] A receiver reads the front crossing its ring (design (a), `receive`; "Exact
//! charts", the receiving face). [`ReceivingPhases`] names the receiving ring `R`, its first epoch
//! `e_0 = min_(g∈𝒮) dist(g, R)`, its aperture `A` (so `e_last = e_0 + A − 1` and the word evaluates
//! `e_max = e_0 + A` junction steps) and its grain `L_R = ⌈1/ε_bits⌉`, derived from the receiver's
//! declared code tolerance `ε_bits` per cell (R2 M2). It refuses `A` beyond the rank of the
//! receiving ring's observability over the word, and reports that rank (review C7).
//!
//! ```text
//! f_j = R · P_R^(τ_R) (v_R(e_j) + h_R)        complex logits over |A| classes, realified [Re, Im, …]
//! Re f_c = n_c + k_c/L_R + ε_c,  ε_c ∈ [0, 1/L_R)   the grain cell (carry, phase class) and the fibre
//! φ^H_c = Im f_c / 2                             each class's phase, in turns
//! ```
//!
//! [definition; agent-inferred] **The standing read** (Decision 26). The face reads the receiving
//! parametron's bound harmonic coordinate `h_R` beside the change: a constitution coordinate
//! (`hnn::constitution`, at the receiving locus on its lattice, initially zero), changed only by
//! deposition, in the fixed space of the ring's rotation, `P_R h_R = h_R` ([`Ring::harmonic`]). So
//! `f = R P_R^(τ_R) v_R + R h_R`: the second term persists when the word opens at zero change, and
//! does not ride the path's attenuation or the ring's phase class (the located failure's missing
//! constant). Its return is the harmonic projection of the pulled-back covector,
//! `∂ℓ/∂h_R = Π Rᵀ Σ_j ∂ℓ/∂f_j` ([`standing_return`]): for a harmonic variation `δ`,
//! `⟨∇_f, R δ⟩ = ⟨Π Rᵀ ∇_f, δ⟩`, since `Π δ = δ` and `Π` is symmetric. Its deposit is the factor step
//! at the locus's statistic, which accumulates the **face's curvature along the fixed space**
//! ([`standing_energy`]): per read, `tr(Π Rᵀ 𝒥 R Π)` with `𝒥` the scored face's Gauss–Newton
//! curvature in the realified logits, `diag(p̃) − p̃p̃ᵀ` on the real rows (the odometer chart the
//! covector's magnitude part `p̃ − q` is read in; the `ln 2` between bits and nats is a declared
//! factor, never evaluated, and leaving it out only overstates the curvature) and `¼` at the
//! target's imaginary row (the phase excess `½Δ²` with `Δ = φ^T − Im f_t / 2`). [agent-inferred] The
//! covector descends the face, so the step `η_x G / h_x'` is preconditioned by the face's own
//! curvature, its trace over the fixed space bounding the largest eigenvalue there; the read's
//! Frobenius energy `‖R Π‖²_F` is the squared chart's curvature instead, which overstates the face's
//! by about `1/max_c p̃_c`, and under it the coordinate stayed below its lattice (measured: it moved
//! at 1 of the standing real cut's first 24 deposits). The face's common-shift fibre still applies
//! to `R h_R`.
//!
//! [definition] **Exact inside, grain only at the face.** The logits are exact rationals. The grain
//! reading returns the carry `n_c`, the phase class `k_c ∈ ℤ/L_R` and the fibre `ε_c`, the
//! receiver's unresolved remainder, which is returned and never rounded (guard 15). The normalized
//! face `p̂ ∝ 2^(n + k/L_R)` lives in `ℚ(θ_R)`, `θ_R^(L_R) = 2`, and is built from the cells by the
//! ratio module's carried power (addition 4); this module stops at the cells.
//!
//! | Lean | Rust |
//! |---|---|
//! | `HNN/Ratio.face_constant_on_fibre` (the face reads only `(n, k)`) | [`GrainCell`] |
//! | `HNN/Ratio.grain_of_tolerance` (`L_R = ⌈1/ε_bits⌉`) | [`ReceivingPhases::declare`] |
//! | `receiver::reception::ReceiverFace::read` with `C_S = R P_R^(τ_R) Π_R` | [`ReceivingPhases::read`] |
//! | `HNN/StandingRead.{standing_read_at_zero_change, harmonic_read_rotation_invariant, standing_read_pullback, standing_read_common_shift}` (Decision 26) | [`ReceivingPhases::read`], [`standing_return`], [`standing_energy`] |
//! | `HNN/Ratio.grain_of_tolerance` with Decision 26's margin | [`ReceivingPhases::margin`] |

use std::ops::Range;

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::hnn::HnnError;
use crate::hnn::field::{ConstitutionRead, Current, Field, ReceiverDeclaration, Ring};
use crate::hnn::propagation::Operands;
use crate::hnn::ratio::code_margin;
use crate::hnn::realization::{apply_rows, indexed};
use crate::hnn::word::Word;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, integer_dot, integral};
use crate::ratio::{Rat, integer};

/// [definition] **One exponent read at a grain**: `value = carry + phase/grain + fibre`, with
/// `phase ∈ ℤ/grain` and `fibre ∈ [0, 1/grain)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrainCell {
    pub carry: BigInt,
    pub phase: u64,
    pub fibre: Rat,
}

impl GrainCell {
    /// Read `value` at `grain ≥ 1`, exactly: nothing is rounded, the remainder is the fibre.
    ///
    /// [definition; agent-inferred] Two integer divisions with remainder of `value = p/q`
    /// (`q > 0`): `p = n q + r` with `0 ≤ r < q`, then `L r = k q + s` with `0 ≤ s < q`, so the
    /// carry is `n`, the phase class `k` and the fibre `s/(L q)`, normalized once. These are the
    /// floor readings `n = ⌊value⌋`, `k = ⌊L(value − n)⌋`, `ε = (L(value − n) − k)/L` exactly.
    pub fn of(value: &Rat, grain: u64) -> Self {
        let (numerator, denominator) = (value.numer(), value.denom());
        // A reduced ratio carries a positive denominator, so the truncated remainder is
        // corrected once for a negative numerator.
        let (mut carry, mut remainder) = (numerator / denominator, numerator % denominator);
        if remainder.is_negative() {
            carry -= 1;
            remainder += denominator;
        }
        let scaled = remainder * BigInt::from(grain);
        let (phase, residue) = (&scaled / denominator, &scaled % denominator);
        let fibre = Rat::new(residue, denominator * BigInt::from(grain));
        Self {
            carry,
            phase: phase.to_u64().expect("a phase class lies in ℤ/grain"),
            fibre,
        }
    }

    /// The cell's representative `carry + phase/grain`: the point every value of the cell reads as.
    pub fn representative(&self, grain: u64) -> Rat {
        Rat::from_integer(self.carry.clone())
            + Rat::new(BigInt::from(self.phase), BigInt::from(grain))
    }
}

/// [definition] **One receiving read**: the exact realified logits `f`, each class's grain cell of
/// `Re f_c`, and each class's phase `φ^H_c = Im f_c / 2` in turns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceivingRead {
    pub logits: Vec<Rat>,
    pub cells: Vec<GrainCell>,
    pub phases: Vec<Rat>,
}

/// [definition] **The receiving phases** of one admitted receiver. See the module header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceivingPhases {
    ring: usize,
    first_epoch: usize,
    aperture: usize,
    grain: u64,
    margin: u64,
    tolerance: Rat,
    rank: usize,
}

impl ReceivingPhases {
    /// **Declare an admitted receiver's phases** at the medium `(Θ, λ)`: its first epoch from the
    /// source rings, its grain from its code tolerance, and its observability rank over the word,
    /// refusing an aperture beyond it.
    pub fn declare(
        field: &Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
        receiver: &ReceiverDeclaration,
    ) -> Result<Self, HnnError> {
        if receiver.ring >= field.rings().len() {
            return Err(HnnError::RingOutside {
                ring: receiver.ring,
                rings: field.rings().len(),
            });
        }
        if receiver.tolerance <= Rat::zero() {
            return Err(HnnError::Tolerance {
                tolerance: receiver.tolerance.clone(),
            });
        }
        if receiver.aperture == 0 {
            return Err(HnnError::Observability {
                aperture: 0,
                rank: 0,
            });
        }
        let first_epoch = field
            .first_epoch(receiver.ring)
            .ok_or(HnnError::Unreached {
                ring: receiver.ring,
            })?;
        let grain = receiver
            .tolerance
            .recip()
            .ceil()
            .to_integer()
            .to_u64()
            .ok_or(HnnError::Tolerance {
                tolerance: receiver.tolerance.clone(),
            })?;
        let mut phases = Self {
            ring: receiver.ring,
            first_epoch,
            aperture: receiver.aperture,
            grain,
            margin: code_margin(field.alphabet(), grain),
            tolerance: receiver.tolerance.clone(),
            rank: 0,
        };
        phases.rank = phases.observability(field, constitution, current)?;
        if phases.aperture > phases.rank {
            return Err(HnnError::Observability {
                aperture: phases.aperture,
                rank: phases.rank,
            });
        }
        Ok(phases)
    }

    /// **The receiving ring's observability rank over the word**: the rank of the exact law's linear
    /// map from the source rings' open storage to the anchors `(v_R(e_0), …, v_R(e_last))`, one
    /// word per source coordinate. [agent-inferred] The rank is the medium's, read under the exact
    /// law ([`Operands::exact_at_cut`]): the executed word carries its transients on a lattice and
    /// is linear only up to its released remainders, so a rank read through it would count the
    /// splits, not the medium.
    pub fn observability(
        &self,
        field: &Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
    ) -> Result<usize, HnnError> {
        let operands = Operands::exact_at_cut(field, constitution, current)?;
        let mut columns: Vec<Vec<Rat>> = Vec::new();
        for &source in field.sources() {
            for coordinate in 0..field.ring(source).width() {
                let mut storage: Vec<Vec<Rat>> = field
                    .rings()
                    .iter()
                    .map(|ring| vec![Rat::zero(); ring.width()])
                    .collect();
                storage[source][coordinate] = integer(1);
                let mut word = Word::on_operands(field, operands.clone(), storage)?;
                columns.push(word.forward(self)?.concat());
            }
        }
        let rows = columns.first().map_or(0, Vec::len);
        let matrix = ExactRatMatrix::shaped(
            rows,
            columns.len(),
            (0..rows)
                .map(|row| columns.iter().map(|column| column[row].clone()).collect())
                .collect(),
        )?;
        Ok(matrix.rank()?)
    }

    pub fn ring(&self) -> usize {
        self.ring
    }

    /// `e_0`.
    pub fn first_epoch(&self) -> usize {
        self.first_epoch
    }

    /// `A`.
    pub fn aperture(&self) -> usize {
        self.aperture
    }

    /// `e_last = e_0 + A − 1`.
    pub fn last_epoch(&self) -> usize {
        self.first_epoch + self.aperture - 1
    }

    /// `e_max = e_0 + A`: the junction steps the word evaluates.
    pub fn junction_steps(&self) -> usize {
        self.first_epoch + self.aperture
    }

    /// The receiving epochs `e_0 … e_last`.
    pub fn epochs(&self) -> Range<usize> {
        self.first_epoch..self.first_epoch + self.aperture
    }

    /// `L_R = ⌈1/ε_bits⌉`.
    pub fn grain(&self) -> u64 {
        self.grain
    }

    /// **The declared margin `m`** of the receiver's target code face `χ_R(T) = m·e_t` (Decision
    /// 26; [`crate::hnn::ratio::code_margin`] at `|A|` and `L_R`, the field's [`Field::margins`]).
    pub fn margin(&self) -> u64 {
        self.margin
    }

    /// The declared code tolerance `ε_bits`.
    pub fn tolerance(&self) -> &Rat {
        &self.tolerance
    }

    /// **The observability rank reported at declaration**: a reading at the declaring medium
    /// `(Θ, λ)` only. A later class configuration (the rings' phases after ingest, the sheet
    /// classes after deposits) can have a lower rank; nothing re-reads it, and no law consumes it
    /// past the declaration's refusal of a wider aperture.
    pub fn rank(&self) -> usize {
        self.rank
    }

    /// **The read at one receiving epoch**: `f = R · P_R^(τ_R)(v_R + h_R)` (module header, the
    /// standing read), each class's real logit read at the grain with its fibre, and its imaginary
    /// logit halved into turns.
    pub fn read(
        &self,
        field: &Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
        anchor: &[Rat],
    ) -> Result<ReceivingRead, HnnError> {
        let ring = field.ring(self.ring);
        if anchor.len() != ring.width() {
            return Err(HnnError::Shape {
                what: "receiving anchor",
                expected: ring.width(),
                found: anchor.len(),
            });
        }
        let map = constitution
            .receiving_map(self.ring)
            .ok_or(HnnError::MissingReceivingMap { ring: self.ring })?;
        if map.rows() != 2 * field.alphabet() || map.columns() != ring.width() {
            return Err(HnnError::Shape {
                what: "receiving map R",
                expected: 2 * field.alphabet() * ring.width(),
                found: map.rows() * map.columns(),
            });
        }
        // The operand the map reads: the change and the bound harmonic coordinate, rotated
        // together (`P h = h`, so the rotation reads the standing unchanged).
        let operand = match constitution.harmonic(self.ring) {
            Some(standing) if standing.len() == anchor.len() => add(anchor, standing),
            Some(standing) => {
                return Err(HnnError::Shape {
                    what: "the receiving ring's harmonic coordinate",
                    expected: anchor.len(),
                    found: standing.len(),
                });
            }
            None => anchor.to_vec(),
        };
        // The map's rows, then the classes' grain cells, each read alone, run together
        // (`hnn::realization`); the map has `2|A|` rows, so the classes pair them exactly.
        let logits = apply_rows(map, &ring.rotate(&operand, &current.lift()[self.ring]))?;
        let classes = logits.len() / 2;
        let cells = indexed(classes, |class| {
            Ok::<_, HnnError>(GrainCell::of(&logits[2 * class], self.grain))
        })?;
        let phases = logits.chunks(2).map(|pair| &pair[1] / integer(2)).collect();
        Ok(ReceivingRead {
            logits,
            cells,
            phases,
        })
    }
}

/// **The standing read's return** (module header): `Π Rᵀ Σ_j ∇_j`, the harmonic projection of the
/// logit gradients pulled back through the receiving map, a vector of the ring's width in the fixed
/// space of its rotation. Read on the orbits' columns of `R`: with `c_(O,p) = Σ_(i∈O) R[·, 2i+p]`, each
/// node of orbit `O` in part `p` reads `Σ_j ⟨c_(O,p), ∇_j⟩ / |O|`, which is `Π Rᵀ Σ_j ∇_j` exactly
/// (the orbit's mean of `(Rᵀ∇)[2i+p] = ⟨R[·, 2i+p], ∇⟩`). Each gradient is read once in the
/// integral chart.
pub fn standing_return(
    ring: &Ring,
    map: &ExactRatMatrix,
    gradients: &[&[Rat]],
) -> Result<Vec<Rat>, HnnError> {
    let width = ring.width();
    if map.columns() != width {
        return Err(HnnError::Shape {
            what: "receiving map R against its ring's width",
            expected: width,
            found: map.columns(),
        });
    }
    let charts: Vec<_> = gradients
        .iter()
        .map(|gradient| {
            if gradient.len() == map.rows() {
                Ok(integral(gradient))
            } else {
                Err(HnnError::Shape {
                    what: "a logit gradient against the receiving map's rows",
                    expected: map.rows(),
                    found: gradient.len(),
                })
            }
        })
        .collect::<Result<_, _>>()?;
    let mut returned = vec![Rat::zero(); width];
    for orbit in ring.orbits() {
        let size = BigInt::from(orbit.len());
        for part in 0..2 {
            let (column, denominator) = integral(&orbit_column(map, &orbit, part)?);
            let mut coordinate = Rat::zero();
            for (values, scale) in &charts {
                coordinate += Rat::new(integer_dot(&column, values), &denominator * scale);
            }
            coordinate /= Rat::from_integer(size.clone());
            for &node in &orbit {
                returned[2 * node + part] = coordinate.clone();
            }
        }
    }
    Ok(returned)
}

/// **The face's curvature along the fixed space** (module header), summed over the window's reads:
/// per read `j`, given by its logit gradient `∇_j` and its target `t_j` (the odometer masses are
/// `p̃_c = ∇_j[2c] + [c = t_j]`, since the magnitude part of `∇_j` is `p̃ − q`),
///
/// ```text
/// tr(Π Rᵀ 𝒥_j R Π) = Σ_(O,p) ( Σ_c p̃_c c_(O,p)[2c]² − (Σ_c p̃_c c_(O,p)[2c])² + ¼ c_(O,p)[2t_j + 1]² ) / |O|
/// ```
///
/// with `c_(O,p) = Σ_(i∈O) R[·, 2i+p]` (the fixed space's orthonormal basis is `u_(O,p)/√|O|`, and
/// `R u_(O,p) = c_(O,p)`). Each read's masses are read once in the integral chart. Refused at a
/// gradient of the wrong length or a target outside the classes.
pub fn standing_energy(
    ring: &Ring,
    map: &ExactRatMatrix,
    reads: &[(&[Rat], usize)],
) -> Result<Rat, HnnError> {
    let classes = map.rows() / 2;
    let masses = reads
        .iter()
        .map(|(gradient, target)| {
            if gradient.len() != map.rows() {
                return Err(HnnError::Shape {
                    what: "a logit gradient against the receiving map's rows",
                    expected: map.rows(),
                    found: gradient.len(),
                });
            }
            if *target >= classes {
                return Err(HnnError::CellOutside {
                    code: *target,
                    alphabet: classes,
                });
            }
            let masses: Vec<Rat> = (0..classes)
                .map(|c| {
                    let mass = &gradient[2 * c];
                    if c == *target {
                        mass + Rat::one()
                    } else {
                        mass.clone()
                    }
                })
                .collect();
            Ok((integral(&masses), *target))
        })
        .collect::<Result<Vec<_>, HnnError>>()?;
    let mut energy = Rat::zero();
    for orbit in ring.orbits() {
        let size = Rat::from_integer(BigInt::from(orbit.len()));
        for part in 0..2 {
            let column = orbit_column(map, &orbit, part)?;
            let real: Vec<Rat> = (0..classes).map(|c| column[2 * c].clone()).collect();
            let (values, scale) = integral(&real);
            let squares: Vec<BigInt> = values.iter().map(|x| x * x).collect();
            for ((mass, denominator), target) in &masses {
                let second = Rat::new(integer_dot(mass, &squares), denominator * &scale * &scale);
                let first = Rat::new(integer_dot(mass, &values), denominator * &scale);
                let phase = &column[2 * target + 1];
                energy += (second - &first * &first
                    + phase * phase / Rat::from_integer(BigInt::from(4)))
                    / &size;
            }
        }
    }
    Ok(energy)
}

/// `c_(O,p) = Σ_(i∈O) R[·, 2i+p]`: the receiving map read on one orbit's indicator in one part.
fn orbit_column(map: &ExactRatMatrix, orbit: &[usize], part: usize) -> Result<Vec<Rat>, HnnError> {
    (0..map.rows())
        .map(|row| {
            let mut sum = Rat::zero();
            for &node in orbit {
                sum += map.get(row, 2 * node + part)?;
            }
            Ok(sum)
        })
        .collect()
}
