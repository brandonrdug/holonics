//! Causality forces holomorphy, and holomorphy locks the two faces of a response to each other.
//!
//! ## The deposit this closes
//!
//! `research/records/2026-08-05_THE_RECEIVER_QUOTIENTS_THE_SPECTRUM_CAUSALITY_LOCKS_ITS_FACES.md`
//! §5 states the chain in its `[proved-standard]` continuum form:
//!
//! > Causality — a response cannot precede its stimulus — implies that the complex susceptibility
//! > `χ(ω)` is holomorphic in the upper half plane, which implies the **Kramers–Kronig relations**:
//! > its real and imaginary parts are Hilbert transforms of each other,
//! >
//! > ```text
//! > Re chi(w) = (1/pi) P integral  Im chi(w') / (w' - w)  dw' .
//! > ```
//!
//! §8 retains it as a `[conjecture]` with a falsifier — *"Compute both faces independently over a
//! declared aperture and test the Hilbert transform relation exactly"* — and the record closes
//! `[open] No engine construction is scheduled by this record.` This module is that construction.
//! It is the **instrument**, not a measurement of any receiver: §8's conjecture is about the
//! continuing body's own response and remains untouched here.
//!
//! ## What is exact, and in which domain
//!
//! The continuum relation above is an integral over the whole line against a kernel with a pole.
//! Neither the line nor the pole survives onto a finite exact lattice, and the honest result of
//! trying to carry them over is the first thing this module states:
//!
//! **The pairing is exactly rational in the domain where the response lives, at every lattice
//! size. It is exactly rational in the spectral domain at exactly one lattice size, `N = 4`.**
//!
//! Both halves are theorems, not implementation limits.
//!
//! The first half is the algebraic content of Kramers–Kronig, and it is a **pointwise sign flip**.
//! Write `σ[n] = sgn(n)` for the lattice signature. Multiplication by `σ` in the response domain is
//! exactly what the Hilbert convolution is the spectral image of: up to the transform's
//! normalization, the singular kernel `1/(π(ω'-ω))` is the Fourier transform of `σ` and nothing
//! else. So the relation that costs an improper integral on one side costs a negation on the other.
//!
//! The second half is **Niven's theorem** (Niven, *Irrational Numbers*, Carus Mathematical
//! Monographs 11, MAA 1956, Corollary 3.12): for `θ` a rational multiple of `π`, the
//! only rational values of `cos θ` are `0, ±1/2, ±1` and the only rational values of `sin θ` and
//! `tan θ` are `0, ±1`. On the `N`-point circular lattice both spectral faces of a response are
//! rational for every rational response exactly when every `sin(2πk/N)` and `cos(2πk/N)` is
//! rational, that is exactly when `N ∈ {1, 2, 4}`; and the circular Hilbert kernel
//! `(2/N)·cot(πm/N)` is rational at exactly those same `N`. So "given one spectral face, return the
//! other" at a general spectral resolution is **outside the exact rational carrier**, not merely
//! unbuilt. [`FourPointSpectralReflection`] is therefore aperture-complete by a theorem.
//!
//! ## The law
//!
//! > **Law (the discrete face lock).** Let `h` be a response on the symmetric exact lattice
//! > `n ∈ [-M, M]` with the stimulus at `n = 0`. Its two faces are
//! >
//! > ```text
//! >   h_e[n] = (h[n] + h[-n]) / 2      the DISPERSIVE face   (even; carries Re χ)
//! >   h_o[n] = (h[n] - h[-n]) / 2      the ABSORPTIVE face   (odd;  carries Im χ)
//! > ```
//! >
//! > and `h = h_e + h_o` exactly, on every response. With `σ[n] = sgn(n)`,
//! >
//! > ```text
//! >   h_o = σ · h_e   on every index         <=>   h[n] = 0 for every n < 0
//! >   h_e = σ · h_o   on every index n != 0  <=>   h[n] = 0 for every n < 0
//! > ```
//! >
//! > The residual of the first reading is exactly `h[n]` at `n < 0` and exactly `-h[-n]` at
//! > `n > 0`; of the second, exactly `h[n]` at `n < 0` and exactly `h[-n]` at `n > 0`. **The
//! > residual at a lattice point is the acausal value at that point, or its mirror.** It is never a
//! > norm and never a fit.
//! >
//! > **Falsifier.** If a response with a nonzero pre-stimulus value ever locks, or a response whose
//! > pre-stimulus values are all zero ever fails to lock, this law is false.
//!
//! Both halves are run. `the_lock_holds_exactly_when_the_response_is_causal` decides the
//! biconditional by exhaustion over all 1,024 responses on the five-point lattice with values in
//! `{-1, 0, 1, 2}` — 64 causal, 960 acausal — and no response in either class disagrees.
//!
//! ## Where the principal value went
//!
//! **No principal value is taken anywhere in this module, and none is needed.** The singular term of
//! the continuum kernel is `ω' = ω`, and its exact lattice image is `n = 0` — the unique fixed point
//! of the reflection `n ↦ -n`, where `σ[0] = 0`. The construction therefore does not *omit* the
//! singular term by a symmetry argument; the signature annihilates that coordinate structurally, and
//! what a symmetric omission would have discarded is retained and returned as a
//! [`SubtractionConstant`].
//!
//! That retention is the module's second real return. The pairing is **asymmetric**:
//!
//! - dispersive `->` absorptive is exact at every index, including the fixed point;
//! - absorptive `->` dispersive is exact at every index **except** the fixed point, where it is
//!   blind, and the datum it cannot supply is exactly the instantaneous response `h[0]`.
//!
//! This is not a defect introduced by discretization. It is the discrete form of the fact that an
//! unsubtracted dispersion relation does not determine `Re χ`: the physical statement needs the
//! high-frequency limit `χ_∞` supplied separately, and a *subtracted* dispersion relation is what
//! carries it. Here the subtraction constant is exhibited exactly, with its address.
//!
//! And because the kernel of a reflection is a kernel in the receiver sense, it gets occupied. The
//! record's §1 and §9 say what to return when it does — *"the honest return is not the rank but an
//! exhibited colliding pair … a metamer is a stronger falsifier than a number"* — so
//! [`CausalResponse::instantaneous_metamer`] builds the collision: two distinct causal responses
//! with **identical absorptive faces** and different dispersive faces.
//!
//! ## The face names are a theorem, not an analogy
//!
//! Calling the even face dispersive and the odd face absorptive would be decoration if it rested on
//! a Fourier argument taken on faith. It does not. On the unit circle `z^{-1} = z̄`, so for any
//! **rational point of the unit circle** — a dense set, exactly parametrized by
//! [`RationalCirclePoint::from_slope`] — the transfer function
//!
//! ```text
//!   chi(z) = sum_n h[n] z^(-n)
//! ```
//!
//! has both parts in `Q`, computed by exact Gaussian-rational powering with no transcendental
//! anywhere. `the_time_faces_carry_the_transfer_faces_at_every_rational_circle_point` measures that
//! `Im χ` of the even face is exactly zero, `Re χ` of the odd face is exactly zero, and the two
//! decompositions agree at every tested point. The names are earned.
//!
//! ## Holomorphy, stated exactly
//!
//! [`HolomorphyWitness`] is the algebraic form of *"causality implies holomorphic in a half plane"*.
//! `χ(z) = Σ_n h[n] z^{-n}` is a Laurent polynomial; a nonzero pre-stimulus value `h[-m]` is the
//! coefficient of `z^{+m}`, a pole at infinity. So a response is causal exactly when its transfer
//! function has no advanced part, exactly when it extends holomorphically to the exterior chart
//! including `∞`, where its value is the instantaneous response `h[0]`. That is a statement about a
//! Laurent polynomial and it is decided by inspecting coefficients — no half-plane, no contour, no
//! limit.
//!
//! ## Cost, both implementations
//!
//! `CLAUDE.md` §8: *"Where an independent implementation exists, state both costs."* The four-point
//! spectrum is computed here by folding onto `Z/4` and taking the four-point transform: `O(M)`
//! exact rational additions and no multiplication at all. The same four rationals are reachable by
//! evaluating [`CausalResponse::transfer_faces_at`] at the four Gaussian points `1, i, -1, -i`,
//! which costs `O(M)` exact rational **multiplications** — strictly the dearer of the two, by the
//! multiplication. `the_fold_and_the_direct_evaluation_are_independent_routes_to_one_spectrum`
//! grades them against each other. The reflection itself costs `O(M)` negations and no
//! multiplication; the general transfer evaluation costs `O(M)` Gaussian-rational multiplications,
//! each four `Rat` products.
//!
//! ## What this does not establish
//!
//! - **It is not the continuum Kramers–Kronig relation.** No integral is evaluated, no limit is
//!   taken, no refinement is scheduled, and no convergence of the lattice statement to the
//!   continuum one is claimed or tested. The lattice statement is a finite biconditional between a
//!   support condition and a pointwise sign identity, and that is its whole content.
//! - **It says nothing about a susceptibility.** `χ` here is a Laurent polynomial with exact
//!   rational coefficients. There is no resonance, no pole off the origin, no line shape, no
//!   Lorentzian, and no analytic continuation. §5's identification of spectroscopy with
//!   singularity structure is `[interpretation]` in the record and is untouched by this module.
//! - **The spectral relation at `N > 4` is not implemented and is not implementable here.** See the
//!   Niven argument above. A body wanting it must declare an algebraic carrier — the real
//!   cyclotomic field `Q(ζ_N)⁺` — which this module does not. The live certified exact-enclosure
//!   carrier at `crates/holonic-engine/src/exact_value.rs` does not supply one either: its
//!   `AlgebraicRoot` names one real root of one integer polynomial by a Sturm-certified isolating
//!   interval, which is an enclosure of an algebraic number and not arithmetic in a number field.
//! - **The four-point organ tests the FOLDED response, not the response.** Folding `Z` onto `Z/4`
//!   aliases, so a response with a nonzero value at `n = -2` folds into the causal arc and the
//!   four-point relation locks on material that is not causal.
//!   `the_four_point_aperture_is_measured_and_not_asserted` exhibits exactly that violation rather
//!   than asserting the aperture, per `CLAUDE.md` §8. [`CausalResponse::within_four_point_aperture`]
//!   is the declared aperture and it is checkable.
//! - **No receiver is measured.** The record's `[conjecture]` asks whether the continuing body's own
//!   declared response is causal in the required sense. Nothing here answers that; this module is
//!   the apparatus that would.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use relational_geometry::Rat;

const RESPONSE_SCHEMA: &str = "holonic-engine.causal-response.v1";
const FACE_SCHEMA: &str = "holonic-engine.causal-response-face.v1";
const REFLECTION_SCHEMA: &str = "holonic-engine.causal-face-reflection.v1";
const LOCK_SCHEMA: &str = "holonic-engine.causality-lock.v1";
const WITNESS_SCHEMA: &str = "holonic-engine.causal-holomorphy-witness.v1";
const TRANSFER_SCHEMA: &str = "holonic-engine.causal-transfer-faces.v1";
const FOUR_POINT_SCHEMA: &str = "holonic-engine.four-point-spectral-reflection.v1";

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum CausalReflectionError {
    #[error(
        "a lattice with no pre-stimulus region cannot decide causality; the half extent must be \
         at least one"
    )]
    LatticeExtentZero,
    #[error("a lattice grain must be strictly positive")]
    SampleStepNotPositive,
    #[error("a lattice of half extent {half_extent} carries {declared} points, not {supplied}")]
    LatticeWidthMismatch {
        half_extent: u32,
        declared: usize,
        supplied: usize,
    },
    #[error("a declared {parity:?} face is violated at index {index} by exactly {violation}")]
    FaceParityViolated {
        parity: FaceParity,
        index: i64,
        /// `f[index] - ε·f[-index]` for the declared parity's mirror sign `ε`. The exact violation,
        /// not a pair of magnitudes.
        violation: Box<Rat>,
    },
    #[error("the reflection of a {expected:?} face was compared against a {supplied:?} face")]
    FaceParityMismatch {
        expected: FaceParity,
        supplied: FaceParity,
    },
    #[error(
        "two faces on different lattices name different responses and their residual means nothing"
    )]
    LatticesDiffer,
    #[error("the declared point misses the unit circle by exactly {deviation}")]
    NotOnTheUnitCircle {
        /// `x² + y² - 1`, exactly.
        deviation: Box<Rat>,
    },
}

// ---------------------------------------------------------------------------------------------
// the lattice signature

/// `σ[n] = sgn(n)`: the exact lattice image of the Hilbert kernel.
///
/// The single fixed point `σ[0] = 0` is where the continuum kernel's pole sits. Nothing is omitted
/// there by a symmetry argument; the signature annihilates the coordinate, and what it annihilates
/// is returned as a [`SubtractionConstant`].
const fn lattice_signature(index: i64) -> i8 {
    if index > 0 {
        1
    } else if index < 0 {
        -1
    } else {
        0
    }
}

fn signed(value: &Rat, signature: i8) -> Rat {
    match signature {
        1 => value.clone(),
        -1 => -value.clone(),
        _ => Rat::zero(),
    }
}

fn halved(value: Rat) -> Rat {
    value / Rat::from_integer(BigInt::from(2))
}

// ---------------------------------------------------------------------------------------------
// the two faces

/// Which face of a response this is, named both by its lattice parity and by its spectral role.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum FaceParity {
    /// `f[-n] = f[n]`. The response's dispersive face; it carries `Re χ` and nothing else.
    Dispersive,
    /// `f[-n] = -f[n]`. The response's absorptive face; it carries `Im χ` and nothing else.
    Absorptive,
}

impl FaceParity {
    /// The parity the lattice signature sends this one to. `σ` is odd, so it flips parity.
    pub const fn reflected(self) -> Self {
        match self {
            Self::Dispersive => Self::Absorptive,
            Self::Absorptive => Self::Dispersive,
        }
    }

    /// `+1` for the even face, `-1` for the odd face: the sign in `f[-n] = ε f[n]`.
    pub const fn mirror_sign(self) -> i8 {
        match self {
            Self::Dispersive => 1,
            Self::Absorptive => -1,
        }
    }
}

/// One face of a response on a symmetric exact lattice, with its parity guaranteed.
///
/// Construction refuses a value family that violates the declared parity, so
/// [`ExactResponseFace::reflect`] returning the opposite parity is a theorem about this carrier and
/// not a claim the caller has to be trusted on.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactResponseFace {
    pub schema: String,
    pub parity: FaceParity,
    half_extent: u32,
    sample_step: Rat,
    /// Index `n` is stored at `n + half_extent`.
    values: Vec<Rat>,
}

impl ExactResponseFace {
    pub fn new(
        parity: FaceParity,
        half_extent: u32,
        sample_step: Rat,
        values: Vec<Rat>,
    ) -> Result<Self, CausalReflectionError> {
        if half_extent == 0 {
            return Err(CausalReflectionError::LatticeExtentZero);
        }
        if !sample_step.is_positive() {
            return Err(CausalReflectionError::SampleStepNotPositive);
        }
        let width = 2 * half_extent as usize + 1;
        if values.len() != width {
            return Err(CausalReflectionError::LatticeWidthMismatch {
                half_extent,
                declared: width,
                supplied: values.len(),
            });
        }
        let face = Self {
            schema: FACE_SCHEMA.to_owned(),
            parity,
            half_extent,
            sample_step,
            values,
        };
        let extent = face.half_extent as i64;
        for index in 1..=extent {
            let violation = face.value(index) - signed(&face.value(-index), parity.mirror_sign());
            if !violation.is_zero() {
                return Err(CausalReflectionError::FaceParityViolated {
                    parity,
                    index,
                    violation: Box::new(violation),
                });
            }
        }
        if parity == FaceParity::Absorptive && !face.value(0).is_zero() {
            return Err(CausalReflectionError::FaceParityViolated {
                parity,
                index: 0,
                violation: Box::new(face.value(0)),
            });
        }
        Ok(face)
    }

    pub const fn half_extent(&self) -> u32 {
        self.half_extent
    }

    pub const fn sample_step(&self) -> &Rat {
        &self.sample_step
    }

    /// The lattice indices, in order, from the earliest pre-stimulus point to the latest.
    pub fn indices(&self) -> impl Iterator<Item = i64> + use<> {
        let extent = self.half_extent as i64;
        -extent..=extent
    }

    /// The exact value at a lattice index. Zero outside the lattice, which is the value a finite
    /// declaration carries there.
    pub fn value(&self, index: i64) -> Rat {
        let extent = self.half_extent as i64;
        if index < -extent || index > extent {
            return Rat::zero();
        }
        self.values[(index + extent) as usize].clone()
    }

    pub fn values(&self) -> &[Rat] {
        &self.values
    }

    pub fn is_zero(&self) -> bool {
        self.values.iter().all(Rat::is_zero)
    }

    /// The indices, away from the reflection's fixed point, where this face does not vanish.
    ///
    /// A face supported only at the fixed point cannot exercise the pairing: the signature
    /// annihilates it and both readings hold for it whatever the response was.
    pub fn moving_support(&self) -> Vec<i64> {
        self.indices()
            .filter(|index| *index != 0 && !self.value(*index).is_zero())
            .collect()
    }

    /// **The discrete Hilbert-transform pairing.** Multiply by the lattice signature and return the
    /// other face.
    ///
    /// This is the whole transform: `O(M)` negations, no multiplication, no kernel, no sum, no
    /// principal value. The parity of the return is opposite to this face's because `σ` is odd.
    pub fn reflect(&self) -> Self {
        let values = self
            .indices()
            .map(|index| signed(&self.value(index), lattice_signature(index)))
            .collect();
        Self {
            schema: FACE_SCHEMA.to_owned(),
            parity: self.parity.reflected(),
            half_extent: self.half_extent,
            sample_step: self.sample_step.clone(),
            values,
        }
    }

    /// Derive the other face from this one and compare it, point by point, against a measured face.
    ///
    /// The return carries the exact residual at **every** lattice index, including the zeros, so the
    /// aperture is inspectable. Nothing is summed, normed, averaged or fitted.
    pub fn reflect_and_compare(
        &self,
        measured_other_face: &Self,
    ) -> Result<FaceReflection, CausalReflectionError> {
        if self.half_extent != measured_other_face.half_extent
            || self.sample_step != measured_other_face.sample_step
        {
            return Err(CausalReflectionError::LatticesDiffer);
        }
        let expected = self.parity.reflected();
        if measured_other_face.parity != expected {
            return Err(CausalReflectionError::FaceParityMismatch {
                expected,
                supplied: measured_other_face.parity,
            });
        }

        let derived = self.reflect();
        let mut residuals = Vec::with_capacity(2 * self.half_extent as usize + 1);
        let mut standing_indices = Vec::new();
        let mut blind_residuals = Vec::new();
        for index in self.indices() {
            let derived_value = derived.value(index);
            let measured_value = measured_other_face.value(index);
            let residual = &measured_value - &derived_value;
            let blind = lattice_signature(index) == 0;
            if blind {
                blind_residuals.push(FaceResidual {
                    index,
                    derived: derived_value.clone(),
                    measured: measured_value.clone(),
                    residual: residual.clone(),
                });
            } else if !residual.is_zero() {
                standing_indices.push(index);
            }
            residuals.push(FaceResidual {
                index,
                derived: derived_value,
                measured: measured_value,
                residual,
            });
        }

        Ok(FaceReflection {
            schema: REFLECTION_SCHEMA.to_owned(),
            source_parity: self.parity,
            derived,
            measured: measured_other_face.clone(),
            residuals,
            standing_indices,
            blind_residuals,
        })
    }
}

// ---------------------------------------------------------------------------------------------
// the response

/// A real linear response on a finite symmetric exact lattice, with the stimulus at index zero.
///
/// The lattice is `n ∈ [-M, M]` at an exact grain. Indices below zero are **before the stimulus**;
/// [`CausalResponse::is_causal`] is the structural statement that the response vanishes on all of
/// them, decided by exact equality with zero. There is no tolerance and no threshold in this file.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalResponse {
    pub schema: String,
    half_extent: u32,
    sample_step: Rat,
    /// Index `n` is stored at `n + half_extent`.
    values: Vec<Rat>,
}

impl CausalResponse {
    pub fn new(
        half_extent: u32,
        sample_step: Rat,
        values: Vec<Rat>,
    ) -> Result<Self, CausalReflectionError> {
        if half_extent == 0 {
            return Err(CausalReflectionError::LatticeExtentZero);
        }
        if !sample_step.is_positive() {
            return Err(CausalReflectionError::SampleStepNotPositive);
        }
        let width = 2 * half_extent as usize + 1;
        if values.len() != width {
            return Err(CausalReflectionError::LatticeWidthMismatch {
                half_extent,
                declared: width,
                supplied: values.len(),
            });
        }
        Ok(Self {
            schema: RESPONSE_SCHEMA.to_owned(),
            half_extent,
            sample_step,
            values,
        })
    }

    /// A response that vanishes before the stimulus, declared by its values at `n = 0 ..= M`.
    ///
    /// Causal by construction, so it is not usable on its own to *decide* the law — the acausal
    /// half of every falsifier is declared through [`CausalResponse::new`].
    pub fn from_retarded_values(
        half_extent: u32,
        sample_step: Rat,
        retarded: &[Rat],
    ) -> Result<Self, CausalReflectionError> {
        let width = half_extent as usize + 1;
        if retarded.len() != width {
            return Err(CausalReflectionError::LatticeWidthMismatch {
                half_extent,
                declared: width,
                supplied: retarded.len(),
            });
        }
        let mut values = vec![Rat::zero(); half_extent as usize];
        values.extend_from_slice(retarded);
        Self::new(half_extent, sample_step, values)
    }

    pub const fn half_extent(&self) -> u32 {
        self.half_extent
    }

    pub const fn sample_step(&self) -> &Rat {
        &self.sample_step
    }

    pub fn indices(&self) -> impl Iterator<Item = i64> + use<> {
        let extent = self.half_extent as i64;
        -extent..=extent
    }

    pub fn value(&self, index: i64) -> Rat {
        let extent = self.half_extent as i64;
        if index < -extent || index > extent {
            return Rat::zero();
        }
        self.values[(index + extent) as usize].clone()
    }

    pub fn values(&self) -> &[Rat] {
        &self.values
    }

    /// The response at the stimulus instant. This is the datum the absorptive face cannot supply.
    pub fn instantaneous_value(&self) -> Rat {
        self.value(0)
    }

    /// **Structural causality:** the response vanishes at every index before the stimulus.
    ///
    /// Decided by exact equality with zero on the pre-stimulus indices. No tolerance, no epsilon,
    /// no energy fraction, no leading-edge estimate.
    pub fn is_causal(&self) -> bool {
        self.advanced_support().is_empty()
    }

    /// The pre-stimulus indices where the response does not vanish: the witness for acausality.
    ///
    /// Empty exactly when [`CausalResponse::is_causal`]. A returned nonempty list is the exhibited
    /// artifact, not a flag.
    pub fn advanced_support(&self) -> Vec<i64> {
        let extent = self.half_extent as i64;
        (-extent..0)
            .filter(|index| !self.value(*index).is_zero())
            .collect()
    }

    /// Whether this response can distinguish the law from its negation.
    ///
    /// A response supported only at the reflection's fixed point has a zero absorptive face and a
    /// dispersive face the signature annihilates, so **both readings lock for it regardless**. Such
    /// material is incapable of exercising the pairing and a fixture built from it proves nothing.
    pub fn exercises_the_pairing(&self) -> bool {
        self.indices()
            .any(|index| index != 0 && !self.value(index).is_zero())
    }

    /// `h_e[n] = (h[n] + h[-n]) / 2`. Even, and it carries `Re χ`.
    pub fn dispersive_face(&self) -> ExactResponseFace {
        let values = self
            .indices()
            .map(|index| halved(self.value(index) + self.value(-index)))
            .collect();
        ExactResponseFace {
            schema: FACE_SCHEMA.to_owned(),
            parity: FaceParity::Dispersive,
            half_extent: self.half_extent,
            sample_step: self.sample_step.clone(),
            values,
        }
    }

    /// `h_o[n] = (h[n] - h[-n]) / 2`. Odd, and it carries `Im χ`.
    pub fn absorptive_face(&self) -> ExactResponseFace {
        let values = self
            .indices()
            .map(|index| halved(self.value(index) - self.value(-index)))
            .collect();
        ExactResponseFace {
            schema: FACE_SCHEMA.to_owned(),
            parity: FaceParity::Absorptive,
            half_extent: self.half_extent,
            sample_step: self.sample_step.clone(),
            values,
        }
    }

    /// Rebuild a response from its two faces: `h = h_e + h_o`, exactly.
    pub fn from_faces(
        dispersive: &ExactResponseFace,
        absorptive: &ExactResponseFace,
    ) -> Result<Self, CausalReflectionError> {
        if dispersive.half_extent != absorptive.half_extent
            || dispersive.sample_step != absorptive.sample_step
        {
            return Err(CausalReflectionError::LatticesDiffer);
        }
        if dispersive.parity != FaceParity::Dispersive {
            return Err(CausalReflectionError::FaceParityMismatch {
                expected: FaceParity::Dispersive,
                supplied: dispersive.parity,
            });
        }
        if absorptive.parity != FaceParity::Absorptive {
            return Err(CausalReflectionError::FaceParityMismatch {
                expected: FaceParity::Absorptive,
                supplied: absorptive.parity,
            });
        }
        let values = dispersive
            .indices()
            .map(|index| dispersive.value(index) + absorptive.value(index))
            .collect();
        Self::new(
            dispersive.half_extent,
            dispersive.sample_step.clone(),
            values,
        )
    }

    /// A distinct response with an **identical absorptive face**: the occupied kernel, exhibited.
    ///
    /// The reflection is blind at its fixed point, so the absorptive face carries no information
    /// about `h[0]`. Two responses differing only there are indistinguishable to it. This returns
    /// that collision as an object rather than reporting a rank; the record's §9 asks for exactly
    /// that. `None` when the replacement is the value already standing, since a collision needs two
    /// distinct responses.
    pub fn instantaneous_metamer(&self, replacement: Rat) -> Option<Self> {
        if replacement == self.instantaneous_value() {
            return None;
        }
        let mut values = self.values.clone();
        values[self.half_extent as usize] = replacement;
        Some(Self {
            schema: RESPONSE_SCHEMA.to_owned(),
            half_extent: self.half_extent,
            sample_step: self.sample_step.clone(),
            values,
        })
    }

    /// The algebraic form of *causality implies holomorphy*: the transfer Laurent polynomial's
    /// advanced part.
    pub fn holomorphy_witness(&self) -> HolomorphyWitness {
        let extent = self.half_extent as i64;
        let advanced_coefficients = (1..=extent)
            .filter_map(|power| {
                let coefficient = self.value(-power);
                (!coefficient.is_zero()).then_some((power as u32, coefficient))
            })
            .collect();
        let retarded_degree = (0..=extent)
            .rev()
            .find(|power| !self.value(*power).is_zero())
            .map(|power| power as u32);
        HolomorphyWitness {
            schema: WITNESS_SCHEMA.to_owned(),
            advanced_coefficients,
            retarded_degree,
            value_at_infinity: self.instantaneous_value(),
        }
    }

    /// `χ(z) = Σ_n h[n] z^(-n)` at an exact rational point of the unit circle, both faces in `Q`.
    ///
    /// `|z| = 1` exactly, so `z^{-1} = z̄` and the whole evaluation is Gaussian-rational
    /// multiplication. No transcendental appears.
    pub fn transfer_faces_at(&self, point: &RationalCirclePoint) -> ExactTransferFaces {
        let mut dispersive = Rat::zero();
        let mut absorptive = Rat::zero();
        for index in self.indices() {
            let coefficient = self.value(index);
            if coefficient.is_zero() {
                continue;
            }
            let (real, imaginary) = point.power(-index);
            dispersive += &coefficient * real;
            absorptive += &coefficient * imaginary;
        }
        ExactTransferFaces {
            schema: TRANSFER_SCHEMA.to_owned(),
            point: point.clone(),
            dispersive,
            absorptive,
        }
    }

    /// `fold[j] = Σ_{n ≡ j (mod 4)} h[n]`, exactly.
    ///
    /// The four-point spectral lattice cannot see more than this: `z^{-n}` at `z ∈ {1, i, -1, -i}`
    /// depends on `n` only through `n mod 4`. Folding is therefore not a lossy convenience, it is
    /// what that receiver's aperture *is*.
    pub fn folded_to_four(&self) -> [Rat; 4] {
        let mut folded = [Rat::zero(), Rat::zero(), Rat::zero(), Rat::zero()];
        for index in self.indices() {
            let slot = index.rem_euclid(4) as usize;
            folded[slot] += self.value(index);
        }
        folded
    }

    /// The declared aperture of the four-point spectral organ: support inside one period.
    ///
    /// Outside it, folding aliases and the organ tests the causality of the folded response instead
    /// of the response. It appears to return and it is answering a different question.
    pub fn within_four_point_aperture(&self) -> bool {
        self.indices()
            .all(|index| (-1..=2).contains(&index) || self.value(index).is_zero())
    }

    /// The deposit's own formula, exactly, on the complete rational spectral aperture.
    pub fn four_point_spectral_reflection(&self) -> FourPointSpectralReflection {
        FourPointSpectralReflection::of_fold(self.folded_to_four())
    }
}

// ---------------------------------------------------------------------------------------------
// what a reflection returns

/// The exact residual at one lattice point. Never a norm, never a fit.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FaceResidual {
    pub index: i64,
    /// The value the reflection derived from the other face.
    pub derived: Rat,
    /// The value the measured face carries.
    pub measured: Rat,
    /// `measured - derived`. For a causal response this is zero away from the fixed point, and
    /// where it is not, it is exactly the acausal value at that point or its mirror.
    pub residual: Rat,
}

/// One derived face compared, point by point, against a measured one.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FaceReflection {
    pub schema: String,
    pub source_parity: FaceParity,
    pub derived: ExactResponseFace,
    pub measured: ExactResponseFace,
    /// Every lattice index, in order, including the zeros. The aperture stays inspectable.
    pub residuals: Vec<FaceResidual>,
    /// Indices away from the fixed point where the residual does not vanish.
    pub standing_indices: Vec<i64>,
    /// The fixed points of `n ↦ -n`, where the signature annihilates the coordinate. Retained
    /// rather than omitted: for the absorptive reading this residual is the subtraction constant.
    pub blind_residuals: Vec<FaceResidual>,
}

impl FaceReflection {
    /// The two faces lock: every residual away from the reflection's fixed point is exactly zero.
    pub fn locks(&self) -> bool {
        self.standing_indices.is_empty()
    }

    pub fn residual_at(&self, index: i64) -> Rat {
        self.residuals
            .iter()
            .find(|residual| residual.index == index)
            .map(|residual| residual.residual.clone())
            .unwrap_or_else(Rat::zero)
    }

    /// The standing residuals with their addresses: the returned obstruction.
    pub fn standing_residuals(&self) -> Vec<(i64, Rat)> {
        self.standing_indices
            .iter()
            .map(|index| (*index, self.residual_at(*index)))
            .collect()
    }
}

/// A datum the reflection annihilated, retained with its address.
///
/// The discrete form of the constant an unsubtracted dispersion relation cannot supply.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SubtractionConstant {
    /// A fixed point of the lattice reflection `n ↦ -n`.
    pub index: i64,
    /// The dispersive-face value there. The absorptive face carries no information about it.
    pub value: Rat,
}

/// Both readings of one response, with the retained subtraction constants.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalityLock {
    pub schema: String,
    /// Decided structurally on the response, independently of either reflection.
    pub structurally_causal: bool,
    pub advanced_support: Vec<i64>,
    /// Exact at every index, including the fixed point.
    pub dispersive_to_absorptive: FaceReflection,
    /// Exact at every index except the fixed point, where it is blind.
    pub absorptive_to_dispersive: FaceReflection,
    pub subtraction_constants: Vec<SubtractionConstant>,
    /// False when the response is supported only at the reflection's fixed point, where both
    /// readings hold whatever the response was.
    pub exercised: bool,
}

impl CausalityLock {
    /// Both readings lock.
    ///
    /// The law is that this equals [`CausalityLock::structurally_causal`], on every response.
    pub fn locks(&self) -> bool {
        self.dispersive_to_absorptive.locks() && self.absorptive_to_dispersive.locks()
    }

    /// The law, decided on this response: the reflection agrees with the structural reading.
    pub fn law_holds(&self) -> bool {
        self.locks() == self.structurally_causal
    }
}

/// Derive each face from the other and compare both against the measured faces.
pub fn causality_lock(response: &CausalResponse) -> Result<CausalityLock, CausalReflectionError> {
    let dispersive = response.dispersive_face();
    let absorptive = response.absorptive_face();
    let forward = dispersive.reflect_and_compare(&absorptive)?;
    let backward = absorptive.reflect_and_compare(&dispersive)?;
    let subtraction_constants = backward
        .blind_residuals
        .iter()
        .map(|residual| SubtractionConstant {
            index: residual.index,
            value: residual.measured.clone(),
        })
        .collect();
    Ok(CausalityLock {
        schema: LOCK_SCHEMA.to_owned(),
        structurally_causal: response.is_causal(),
        advanced_support: response.advanced_support(),
        dispersive_to_absorptive: forward,
        absorptive_to_dispersive: backward,
        subtraction_constants,
        exercised: response.exercises_the_pairing(),
    })
}

// ---------------------------------------------------------------------------------------------
// holomorphy, algebraically

/// The transfer Laurent polynomial's obstruction to extending over the exterior chart.
///
/// `χ(z) = Σ_n h[n] z^{-n}`. A nonzero pre-stimulus value `h[-m]` is the coefficient of `z^{+m}`,
/// a pole at infinity. The response is causal exactly when this list is empty, exactly when `χ`
/// extends holomorphically over `z = ∞`, where its value is the instantaneous response.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HolomorphyWitness {
    pub schema: String,
    /// `(m, h[-m])` for each nonzero coefficient of `z^{+m}`, `m ≥ 1`.
    pub advanced_coefficients: Vec<(u32, Rat)>,
    /// The largest `n ≥ 0` at which the response does not vanish. `None` for a response that
    /// vanishes on the whole retarded half.
    pub retarded_degree: Option<u32>,
    /// `χ(∞) = h[0]`, defined exactly when the advanced part is empty.
    pub value_at_infinity: Rat,
}

impl HolomorphyWitness {
    /// `χ` extends holomorphically to the exterior chart including `∞`.
    pub fn extends_over_infinity(&self) -> bool {
        self.advanced_coefficients.is_empty()
    }

    /// The order of the pole at infinity: the largest advanced power present.
    pub fn pole_order_at_infinity(&self) -> u32 {
        self.advanced_coefficients
            .iter()
            .map(|(power, _)| *power)
            .max()
            .unwrap_or(0)
    }
}

// ---------------------------------------------------------------------------------------------
// the exact rational spectral face

/// An exact rational point of the unit circle: `x² + y² = 1` with `x, y ∈ Q`.
///
/// These are dense in the circle and exactly parametrized by [`RationalCirclePoint::from_slope`],
/// the Cayley/Pythagorean parametrization. Because `|z| = 1` holds exactly, `z^{-1} = z̄` and every
/// power of `z` is a Gaussian rational — which is what puts both spectral faces of a rational
/// response in `Q` with no transcendental anywhere.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RationalCirclePoint {
    x: Rat,
    y: Rat,
}

impl RationalCirclePoint {
    /// Refuses any pair not exactly on the circle. An approximate point would make every face
    /// approximate.
    pub fn new(x: Rat, y: Rat) -> Result<Self, CausalReflectionError> {
        let deviation = &x * &x + &y * &y - Rat::one();
        if !deviation.is_zero() {
            return Err(CausalReflectionError::NotOnTheUnitCircle {
                deviation: Box::new(deviation),
            });
        }
        Ok(Self { x, y })
    }

    /// `z(s) = ((1 - s²) + 2s i) / (1 + s²)`, exact for every rational `s`.
    ///
    /// This is the stereographic parametrization from `-1`; it reaches every rational circle point
    /// except `-1` itself, which [`RationalCirclePoint::new`] takes directly.
    pub fn from_slope(slope: &Rat) -> Self {
        let square = slope * slope;
        let denominator = Rat::one() + &square;
        Self {
            x: (Rat::one() - &square) / &denominator,
            y: (Rat::from_integer(BigInt::from(2)) * slope) / &denominator,
        }
    }

    pub const fn real(&self) -> &Rat {
        &self.x
    }

    pub const fn imaginary(&self) -> &Rat {
        &self.y
    }

    /// The complex conjugate, which on this circle is also the inverse.
    pub fn conjugate(&self) -> Self {
        Self {
            x: self.x.clone(),
            y: -self.y.clone(),
        }
    }

    /// `z^exponent` as an exact Gaussian rational, by binary powering. Negative exponents use
    /// `z^{-1} = z̄`, which is exact because the point is exactly on the circle.
    pub fn power(&self, exponent: i64) -> (Rat, Rat) {
        let (mut base_real, mut base_imaginary) = if exponent >= 0 {
            (self.x.clone(), self.y.clone())
        } else {
            (self.x.clone(), -self.y.clone())
        };
        let mut remaining = exponent.unsigned_abs();
        let (mut real, mut imaginary) = (Rat::one(), Rat::zero());
        while remaining > 0 {
            if remaining & 1 == 1 {
                let product = complex_product(&real, &imaginary, &base_real, &base_imaginary);
                real = product.0;
                imaginary = product.1;
            }
            let squared = complex_product(&base_real, &base_imaginary, &base_real, &base_imaginary);
            base_real = squared.0;
            base_imaginary = squared.1;
            remaining >>= 1;
        }
        (real, imaginary)
    }
}

fn complex_product(
    left_real: &Rat,
    left_imaginary: &Rat,
    right_real: &Rat,
    right_imaginary: &Rat,
) -> (Rat, Rat) {
    (
        left_real * right_real - left_imaginary * right_imaginary,
        left_real * right_imaginary + left_imaginary * right_real,
    )
}

/// The two faces of `χ` at one exact rational point of the unit circle.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactTransferFaces {
    pub schema: String,
    pub point: RationalCirclePoint,
    /// `Re χ(z)`, exactly. Carried entirely by the response's dispersive face.
    pub dispersive: Rat,
    /// `Im χ(z)`, exactly. Carried entirely by the response's absorptive face.
    pub absorptive: Rat,
}

// ---------------------------------------------------------------------------------------------
// the complete rational spectral aperture

/// The deposit's formula, exactly, on the four-point spectral lattice `z ∈ {1, i, -1, -i}`.
///
/// This is the **whole** rational spectral aperture. By Niven's theorem both spectral faces of
/// every rational response are rational exactly when `N ∈ {1, 2, 4}`, and the circular Hilbert
/// kernel `(2/N)cot(πm/N)` is rational at exactly those `N`; at `N = 4` it is `[0, 1/2, 0, -1/2]`
/// and the relation collapses to a three-point stencil:
///
/// ```text
///   Im chi[k] =  ( Re chi[k+1] - Re chi[k-1] ) / 2
///   Re chi[k] = -( Im chi[k+1] - Im chi[k-1] ) / 2  +  h_e[0]  +  h_e[2] (-1)^k
/// ```
///
/// The second line is a **subtracted** dispersion relation and the two constants are exactly the
/// two fixed points of `n ↦ -n` on `Z/4`. Both directions are exact for a folded-causal response
/// and both fail for a folded-acausal one, with residual `±2·fold[3]`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FourPointSpectralReflection {
    pub schema: String,
    /// `fold[j] = Σ_{n ≡ j (mod 4)} h[n]`.
    pub folded: [Rat; 4],
    /// `Re χ` at `z = 1, i, -1, -i`.
    pub dispersive: [Rat; 4],
    /// `Im χ` at the same four points.
    pub absorptive: [Rat; 4],
    pub derived_absorptive: [Rat; 4],
    pub absorptive_residual: [Rat; 4],
    pub derived_dispersive: [Rat; 4],
    pub dispersive_residual: [Rat; 4],
    /// `(h_e[0], h_e[2])` on the folded lattice: the data the absorptive face cannot supply.
    pub subtraction_constants: [Rat; 2],
    /// `fold[3]`, the pre-stimulus arc after folding. Zero exactly when the folded response is
    /// causal on `Z/4`.
    pub folded_advanced: Rat,
}

impl FourPointSpectralReflection {
    fn of_fold(folded: [Rat; 4]) -> Self {
        // `w = e^(-2πi/4) = -i`, so `w^m` cycles through `1, -i, -1, i`.
        const REAL: [i8; 4] = [1, 0, -1, 0];
        const IMAGINARY: [i8; 4] = [0, -1, 0, 1];

        let dispersive: [Rat; 4] = std::array::from_fn(|k| {
            (0..4).fold(Rat::zero(), |sum, n| {
                sum + signed(&folded[n], REAL[(n * k) % 4])
            })
        });
        let absorptive: [Rat; 4] = std::array::from_fn(|k| {
            (0..4).fold(Rat::zero(), |sum, n| {
                sum + signed(&folded[n], IMAGINARY[(n * k) % 4])
            })
        });

        let derived_absorptive: [Rat; 4] = std::array::from_fn(|k| {
            halved(dispersive[(k + 1) % 4].clone() - &dispersive[(k + 3) % 4])
        });
        let absorptive_residual: [Rat; 4] =
            std::array::from_fn(|k| &absorptive[k] - &derived_absorptive[k]);

        // The two fixed points of `n ↦ -n` on `Z/4`, where `h_e` equals the fold itself.
        let subtraction_constants = [folded[0].clone(), folded[2].clone()];
        let derived_dispersive: [Rat; 4] = std::array::from_fn(|k| {
            let alternating = if k % 2 == 0 {
                subtraction_constants[1].clone()
            } else {
                -subtraction_constants[1].clone()
            };
            -halved(absorptive[(k + 1) % 4].clone() - &absorptive[(k + 3) % 4])
                + &subtraction_constants[0]
                + alternating
        });
        let dispersive_residual: [Rat; 4] =
            std::array::from_fn(|k| &dispersive[k] - &derived_dispersive[k]);

        Self {
            schema: FOUR_POINT_SCHEMA.to_owned(),
            folded_advanced: folded[3].clone(),
            folded,
            dispersive,
            absorptive,
            derived_absorptive,
            absorptive_residual,
            derived_dispersive,
            dispersive_residual,
            subtraction_constants,
        }
    }

    /// Both spectral directions reproduce the measured faces exactly.
    ///
    /// The law is that this equals `folded_advanced == 0` — the causality of the **folded**
    /// response, which is a strictly weaker statement than the causality of the response.
    pub fn locks(&self) -> bool {
        self.absorptive_residual.iter().all(Rat::is_zero)
            && self.dispersive_residual.iter().all(Rat::is_zero)
    }

    /// True when both spectral faces are identically zero, which no relation between them can test.
    pub fn is_vacuous(&self) -> bool {
        self.dispersive.iter().all(Rat::is_zero) && self.absorptive.iter().all(Rat::is_zero)
    }
}

// ---------------------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use relational_geometry::{integer, rat};

    fn grain() -> Rat {
        rat(1, 3)
    }

    fn response(half_extent: u32, values: &[(i64, i64)]) -> CausalResponse {
        CausalResponse::new(
            half_extent,
            grain(),
            values
                .iter()
                .map(|(numerator, denominator)| rat(*numerator, *denominator))
                .collect(),
        )
        .expect("a lawful response declaration")
    }

    // --- the fixture family -------------------------------------------------------------------
    //
    // Every fixture states, in its own name, whether it is causal and whether it can exercise the
    // pairing. The guard test `every_fixture_declares_what_it_can_exercise` holds them to it.

    /// `M = 3`. Causal, with a genuinely two-sided retarded tail: `h = [0,0,0, 5/2, -3, 7/4, 1]`.
    fn causal_tail() -> CausalResponse {
        response(
            3,
            &[(0, 1), (0, 1), (0, 1), (5, 2), (-3, 1), (7, 4), (1, 1)],
        )
    }

    /// `M = 3`. Causal and instantaneous-free: `h[0] = 0`, so the subtraction constant is zero and
    /// the absorptive reading is *not* blind on this material. Retained as the control that shows
    /// the blindness in [`causal_tail`] is a property of the response, not of the reflection.
    fn causal_without_instantaneous() -> CausalResponse {
        response(
            3,
            &[(0, 1), (0, 1), (0, 1), (0, 1), (4, 1), (-1, 3), (2, 1)],
        )
    }

    /// `M = 3`. **Not** causal: one nonzero value at `n = -2`.
    fn advanced_leak() -> CausalResponse {
        response(
            3,
            &[(0, 1), (9, 5), (0, 1), (5, 2), (-3, 1), (7, 4), (1, 1)],
        )
    }

    /// `M = 3`. Not causal, and **even**: `h[-n] = h[n]`. The symmetric-fixture trap named in the
    /// brief — its absorptive face is identically zero, and it must still be refused.
    fn even_response() -> CausalResponse {
        response(
            3,
            &[(2, 1), (-1, 1), (3, 1), (5, 1), (3, 1), (-1, 1), (2, 1)],
        )
    }

    /// `M = 3`. Not causal, and **odd**: its dispersive face is identically zero.
    fn odd_response() -> CausalResponse {
        response(
            3,
            &[(-2, 1), (1, 1), (-3, 1), (0, 1), (3, 1), (-1, 1), (2, 1)],
        )
    }

    /// `M = 2`. Causal and supported only at the stimulus. **Cannot exercise the pairing:** both
    /// readings lock for it whatever the response was, so it can never distinguish the law.
    fn instantaneous_only() -> CausalResponse {
        response(2, &[(0, 1), (0, 1), (11, 2), (0, 1), (0, 1)])
    }

    /// `M = 1`. The smallest lattice that has a pre-stimulus region at all. Causal.
    fn minimal_causal() -> CausalResponse {
        response(1, &[(0, 1), (3, 1), (-7, 2)])
    }

    fn every_fixture() -> Vec<(&'static str, CausalResponse)> {
        vec![
            ("causal_tail", causal_tail()),
            (
                "causal_without_instantaneous",
                causal_without_instantaneous(),
            ),
            ("advanced_leak", advanced_leak()),
            ("even_response", even_response()),
            ("odd_response", odd_response()),
            ("instantaneous_only", instantaneous_only()),
            ("minimal_causal", minimal_causal()),
        ]
    }

    fn rational_circle_points() -> Vec<RationalCirclePoint> {
        let mut points: Vec<RationalCirclePoint> = [
            (0, 1),
            (1, 1),
            (-1, 1),
            (1, 2),
            (-3, 5),
            (2, 1),
            (7, 3),
            (1, 7),
        ]
        .into_iter()
        .map(|(numerator, denominator)| {
            RationalCirclePoint::from_slope(&rat(numerator, denominator))
        })
        .collect();
        // The one rational circle point the stereographic chart from -1 cannot reach.
        points.push(
            RationalCirclePoint::new(integer(-1), Rat::zero()).expect("(-1, 0) is on the circle"),
        );
        points
    }

    // --- the fixture guard --------------------------------------------------------------------

    /// The material must be able to vary the property. A fixture whose faces are annihilated by the
    /// signature, or which cannot be acausal, proves nothing about the law.
    #[test]
    fn every_fixture_declares_what_it_can_exercise() {
        for (name, fixture) in every_fixture() {
            let dispersive = fixture.dispersive_face();
            let absorptive = fixture.absorptive_face();
            assert_eq!(
                fixture.exercises_the_pairing(),
                name != "instantaneous_only",
                "{name}: the declared exercisability is wrong"
            );
            if fixture.exercises_the_pairing() {
                assert!(
                    !dispersive.moving_support().is_empty()
                        || !absorptive.moving_support().is_empty(),
                    "{name}: both faces vanish away from the fixed point"
                );
            }
        }

        // And the family must populate both classes, or the biconditional is only ever tested on
        // one side.
        let causal = every_fixture()
            .iter()
            .filter(|(_, fixture)| fixture.is_causal())
            .count();
        let acausal = every_fixture().len() - causal;
        assert!(causal >= 3, "too few causal fixtures: {causal}");
        assert!(acausal >= 3, "too few acausal fixtures: {acausal}");

        // The symmetric and antisymmetric traps really are the degenerate shapes they claim to be.
        assert!(
            even_response().absorptive_face().is_zero(),
            "the even fixture must have a vanishing absorptive face"
        );
        assert!(
            odd_response().dispersive_face().is_zero(),
            "the odd fixture must have a vanishing dispersive face"
        );
        assert!(
            !even_response().is_causal() && !odd_response().is_causal(),
            "a nonzero response with a mirror symmetry cannot be causal"
        );
    }

    // --- the faces ----------------------------------------------------------------------------

    #[test]
    fn the_two_faces_recompose_the_response_exactly() {
        for (name, fixture) in every_fixture() {
            let dispersive = fixture.dispersive_face();
            let absorptive = fixture.absorptive_face();
            let rebuilt =
                CausalResponse::from_faces(&dispersive, &absorptive).expect("two lawful faces");
            for index in fixture.indices() {
                assert_eq!(
                    rebuilt.value(index),
                    fixture.value(index),
                    "{name}: h_e + h_o != h at {index}"
                );
            }
            // And the decomposition is not trivial on the fixtures that must exercise it.
            if name == "causal_tail" || name == "advanced_leak" {
                assert!(!dispersive.is_zero(), "{name}: a vacuous dispersive face");
                assert!(!absorptive.is_zero(), "{name}: a vacuous absorptive face");
            }
        }
    }

    #[test]
    fn a_face_declaration_that_violates_its_parity_is_refused() {
        // f[-1] = 1, f[0] = 0, f[1] = 2. As an even face the violation at index 1 is 2 - 1 = 1;
        // as an odd face it is 2 - (-1) = 3. The refusal carries the exact violation, not a flag.
        let lopsided = vec![integer(1), integer(0), integer(2)];
        assert_eq!(
            ExactResponseFace::new(FaceParity::Dispersive, 1, grain(), lopsided.clone()),
            Err(CausalReflectionError::FaceParityViolated {
                parity: FaceParity::Dispersive,
                index: 1,
                violation: Box::new(integer(1))
            })
        );
        assert_eq!(
            ExactResponseFace::new(FaceParity::Absorptive, 1, grain(), lopsided),
            Err(CausalReflectionError::FaceParityViolated {
                parity: FaceParity::Absorptive,
                index: 1,
                violation: Box::new(integer(3))
            })
        );
        // An odd face with a nonzero value at the fixed point is not odd, even though its mirror
        // symmetry is perfect.
        assert_eq!(
            ExactResponseFace::new(
                FaceParity::Absorptive,
                1,
                grain(),
                vec![integer(-3), integer(5), integer(3)]
            ),
            Err(CausalReflectionError::FaceParityViolated {
                parity: FaceParity::Absorptive,
                index: 0,
                violation: Box::new(integer(5))
            })
        );
        // The same values, with the fixed point cleared, are a lawful odd face.
        assert!(
            ExactResponseFace::new(
                FaceParity::Absorptive,
                1,
                grain(),
                vec![integer(-3), integer(0), integer(3)]
            )
            .is_ok()
        );
    }

    #[test]
    fn the_reflection_flips_the_parity_it_carries() {
        for (name, fixture) in every_fixture() {
            let dispersive = fixture.dispersive_face();
            let absorptive = fixture.absorptive_face();
            let from_even = dispersive.reflect();
            let from_odd = absorptive.reflect();
            assert_eq!(from_even.parity, FaceParity::Absorptive, "{name}");
            assert_eq!(from_odd.parity, FaceParity::Dispersive, "{name}");
            // The returned values genuinely satisfy the parity they now declare.
            ExactResponseFace::new(
                from_even.parity,
                from_even.half_extent(),
                from_even.sample_step().clone(),
                from_even.values().to_vec(),
            )
            .unwrap_or_else(|error| panic!("{name}: the reflected face is not odd: {error}"));
            ExactResponseFace::new(
                from_odd.parity,
                from_odd.half_extent(),
                from_odd.sample_step().clone(),
                from_odd.values().to_vec(),
            )
            .unwrap_or_else(|error| panic!("{name}: the reflected face is not even: {error}"));
        }
    }

    // --- the law ------------------------------------------------------------------------------

    #[test]
    fn a_causal_response_locks_both_faces_exactly() {
        for (name, fixture) in every_fixture() {
            if !fixture.is_causal() {
                continue;
            }
            let lock = causality_lock(&fixture).expect("a lawful lock");
            assert!(lock.locks(), "{name}: a causal response failed to lock");
            assert!(lock.law_holds(), "{name}");
            assert!(
                lock.advanced_support.is_empty(),
                "{name}: a causal response has an advanced support"
            );
            for reflection in [
                &lock.dispersive_to_absorptive,
                &lock.absorptive_to_dispersive,
            ] {
                for residual in &reflection.residuals {
                    if lattice_signature(residual.index) == 0 {
                        continue;
                    }
                    assert!(
                        residual.residual.is_zero(),
                        "{name}: residual {} at index {}",
                        residual.residual,
                        residual.index
                    );
                }
            }
            // The dispersive reading is exact at the fixed point too; only the absorptive is blind.
            assert!(
                lock.dispersive_to_absorptive.residual_at(0).is_zero(),
                "{name}: h_o[0] is zero on every response, so this residual cannot stand"
            );
        }
    }

    #[test]
    fn an_acausal_response_fails_the_reflection_and_the_residual_is_the_acausal_value() {
        for (name, fixture) in every_fixture() {
            if fixture.is_causal() {
                continue;
            }
            let lock = causality_lock(&fixture).expect("a lawful lock");
            assert!(!lock.locks(), "{name}: an acausal response locked");
            assert!(lock.law_holds(), "{name}");
            assert!(!lock.advanced_support.is_empty(), "{name}");

            // The residual is not a magnitude. It is the acausal value itself, at its own address.
            let forward = &lock.dispersive_to_absorptive;
            let backward = &lock.absorptive_to_dispersive;
            for index in fixture.indices() {
                if index < 0 {
                    assert_eq!(
                        forward.residual_at(index),
                        fixture.value(index),
                        "{name}: the dispersive reading's residual at {index}"
                    );
                    assert_eq!(
                        backward.residual_at(index),
                        fixture.value(index),
                        "{name}: the absorptive reading's residual at {index}"
                    );
                } else if index > 0 {
                    assert_eq!(
                        forward.residual_at(index),
                        -fixture.value(-index),
                        "{name}: the dispersive reading's mirrored residual at {index}"
                    );
                    assert_eq!(
                        backward.residual_at(index),
                        fixture.value(-index),
                        "{name}: the absorptive reading's mirrored residual at {index}"
                    );
                }
            }

            // And at least one of them stands, exhibited with its address.
            let standing = forward.standing_residuals();
            assert!(!standing.is_empty(), "{name}: nothing stood");
            assert!(
                standing.iter().all(|(_, residual)| !residual.is_zero()),
                "{name}: a standing residual was zero"
            );
        }
    }

    /// The falsifier, decided by exhaustion rather than by example.
    ///
    /// Every response on the five-point lattice with values in `{-1, 0, 1, 2}` — 1,024 of them — is
    /// run and the biconditional is checked on each. Both classes are populated, and the count of
    /// each is asserted so that a mutation collapsing one class cannot pass silently.
    #[test]
    fn the_lock_holds_exactly_when_the_response_is_causal() {
        let alphabet = [integer(-1), Rat::zero(), integer(1), integer(2)];
        let mut causal = 0usize;
        let mut acausal = 0usize;
        let mut exercised = 0usize;
        let mut standing_seen = 0usize;

        for code in 0..alphabet.len().pow(5) {
            let mut remaining = code;
            let values: Vec<Rat> = (0..5)
                .map(|_| {
                    let digit = remaining % alphabet.len();
                    remaining /= alphabet.len();
                    alphabet[digit].clone()
                })
                .collect();
            let fixture = CausalResponse::new(2, grain(), values).expect("a lawful declaration");
            let lock = causality_lock(&fixture).expect("a lawful lock");

            assert!(
                lock.law_holds(),
                "the biconditional failed on {:?}: causal {}, locks {}",
                fixture.values(),
                lock.structurally_causal,
                lock.locks()
            );
            if fixture.is_causal() {
                causal += 1;
            } else {
                acausal += 1;
                standing_seen += lock.dispersive_to_absorptive.standing_indices.len();
            }
            if fixture.exercises_the_pairing() {
                exercised += 1;
            }
        }

        assert_eq!(causal + acausal, 1_024);
        assert_eq!(
            causal, 64,
            "responses vanishing at both pre-stimulus indices"
        );
        assert_eq!(acausal, 960);
        assert_eq!(
            exercised, 1_020,
            "only the four fixed-point-only declarations are vacuous"
        );
        assert!(
            standing_seen > 0,
            "no residual ever stood, so the acausal half proved nothing"
        );
    }

    // --- the blindness, and the kernel it leaves ----------------------------------------------

    #[test]
    fn the_reflection_is_blind_exactly_at_the_lattice_origin() {
        let fixture = causal_tail();
        let lock = causality_lock(&fixture).expect("a lawful lock");

        assert_eq!(lock.subtraction_constants.len(), 1);
        let constant = &lock.subtraction_constants[0];
        assert_eq!(constant.index, 0, "the reflection has one fixed point");
        assert_eq!(
            constant.value,
            fixture.instantaneous_value(),
            "the annihilated datum is the instantaneous response"
        );
        assert_eq!(constant.value, rat(5, 2));
        assert!(
            !constant.value.is_zero(),
            "a zero subtraction constant would make this test vacuous"
        );

        // The blindness is one-sided: the dispersive reading recovers the fixed point exactly.
        assert!(lock.dispersive_to_absorptive.residual_at(0).is_zero());
        assert_eq!(lock.absorptive_to_dispersive.residual_at(0), rat(5, 2));

        // And it is a property of the material, not of the law: a response with no instantaneous
        // value has a zero subtraction constant and nothing is lost.
        let clean = causal_without_instantaneous();
        let clean_lock = causality_lock(&clean).expect("a lawful lock");
        assert!(clean_lock.subtraction_constants[0].value.is_zero());
        assert!(clean_lock.absorptive_to_dispersive.residual_at(0).is_zero());
        assert!(clean_lock.locks());
    }

    /// The kernel is occupied, and the return is the colliding pair rather than its rank.
    #[test]
    fn the_absorptive_face_admits_an_exhibited_metamer() {
        let left = causal_tail();
        let right = left
            .instantaneous_metamer(rat(-19, 7))
            .expect("a distinct instantaneous value");

        assert_ne!(left, right, "the pair must be two distinct responses");
        assert!(
            right.is_causal(),
            "the collision is inside the causal class"
        );
        assert_eq!(
            left.absorptive_face(),
            right.absorptive_face(),
            "the absorptive face cannot separate the pair"
        );
        assert_ne!(
            left.dispersive_face(),
            right.dispersive_face(),
            "the dispersive face separates it, so the pair is genuinely distinct"
        );
        assert_eq!(
            left.dispersive_face().value(0) - right.dispersive_face().value(0),
            rat(5, 2) - rat(-19, 7),
            "and the separation is exactly the difference of the subtraction constants"
        );
        assert!(
            !(rat(5, 2) - rat(-19, 7)).is_zero(),
            "a zero separation would make the collision vacuous"
        );

        // Both members lock, so the collision is not a defect the law could have caught.
        assert!(causality_lock(&left).unwrap().locks());
        assert!(causality_lock(&right).unwrap().locks());

        // A metamer needs two distinct members.
        assert!(left.instantaneous_metamer(rat(5, 2)).is_none());
    }

    // --- holomorphy ---------------------------------------------------------------------------

    #[test]
    fn the_transfer_polynomial_extends_over_infinity_exactly_when_the_response_is_causal() {
        for (name, fixture) in every_fixture() {
            let witness = fixture.holomorphy_witness();
            assert_eq!(
                witness.extends_over_infinity(),
                fixture.is_causal(),
                "{name}: holomorphy and causality disagreed"
            );
            if fixture.is_causal() {
                assert_eq!(witness.pole_order_at_infinity(), 0, "{name}");
            } else {
                assert!(witness.pole_order_at_infinity() > 0, "{name}");
                assert!(!witness.advanced_coefficients.is_empty(), "{name}");
            }
        }

        // The advanced coefficients are the actual pre-stimulus values, at their actual powers.
        let leak = advanced_leak();
        let witness = leak.holomorphy_witness();
        assert_eq!(witness.advanced_coefficients, vec![(2u32, rat(9, 5))]);
        assert_eq!(witness.pole_order_at_infinity(), 2);
        assert_eq!(witness.retarded_degree, Some(3));
        assert_eq!(witness.value_at_infinity, rat(5, 2));
    }

    // --- the spectral faces, exactly ----------------------------------------------------------

    #[test]
    fn a_rational_circle_point_is_refused_unless_it_is_exactly_on_the_circle() {
        assert_eq!(
            RationalCirclePoint::new(rat(1, 2), rat(1, 2)),
            Err(CausalReflectionError::NotOnTheUnitCircle {
                deviation: Box::new(rat(-1, 2))
            }),
            "the refusal carries the exact miss, not a flag"
        );
        assert!(RationalCirclePoint::new(rat(3, 5), rat(4, 5)).is_ok());
        for point in rational_circle_points() {
            assert_eq!(
                point.real() * point.real() + point.imaginary() * point.imaginary(),
                Rat::one(),
                "the parametrization left the circle"
            );
        }
        // The parametrization is not constant: the tested points are genuinely distinct.
        let points = rational_circle_points();
        assert!(
            points
                .iter()
                .any(|point| point != &points[0] && !point.imaginary().is_zero()),
            "the point family is degenerate"
        );
    }

    /// The names are a theorem. The even face carries `Re χ` and nothing else; the odd face carries
    /// `Im χ` and nothing else; and both are exact rationals at every rational circle point.
    #[test]
    fn the_time_faces_carry_the_transfer_faces_at_every_rational_circle_point() {
        let mut nonzero_dispersive = 0usize;
        let mut nonzero_absorptive = 0usize;

        for (name, fixture) in every_fixture() {
            let dispersive = fixture.dispersive_face();
            let absorptive = fixture.absorptive_face();
            let as_even = CausalResponse::new(
                fixture.half_extent(),
                fixture.sample_step().clone(),
                dispersive.values().to_vec(),
            )
            .expect("the even face is a response");
            let as_odd = CausalResponse::new(
                fixture.half_extent(),
                fixture.sample_step().clone(),
                absorptive.values().to_vec(),
            )
            .expect("the odd face is a response");

            for point in rational_circle_points() {
                let whole = fixture.transfer_faces_at(&point);
                let even = as_even.transfer_faces_at(&point);
                let odd = as_odd.transfer_faces_at(&point);

                assert!(
                    even.absorptive.is_zero(),
                    "{name}: the even face contributed to Im chi"
                );
                assert!(
                    odd.dispersive.is_zero(),
                    "{name}: the odd face contributed to Re chi"
                );
                assert_eq!(
                    whole.dispersive, even.dispersive,
                    "{name}: Re chi is not the even face's transform"
                );
                assert_eq!(
                    whole.absorptive, odd.absorptive,
                    "{name}: Im chi is not the odd face's transform"
                );
                if !whole.dispersive.is_zero() {
                    nonzero_dispersive += 1;
                }
                if !whole.absorptive.is_zero() {
                    nonzero_absorptive += 1;
                }
            }
        }

        assert!(nonzero_dispersive > 0, "every Re chi vanished");
        assert!(nonzero_absorptive > 0, "every Im chi vanished");
    }

    /// The control that must NOT distinguish. Crossing symmetry `χ(z̄) = conj χ(z)` is a
    /// consequence of the response being real and holds for acausal responses too, so it is
    /// strictly weaker than causality and cannot be mistaken for it.
    #[test]
    fn crossing_symmetry_holds_for_every_real_response_and_cannot_detect_causality() {
        let mut distinguishing = 0usize;
        for (name, fixture) in every_fixture() {
            for point in rational_circle_points() {
                let forward = fixture.transfer_faces_at(&point);
                let conjugated = fixture.transfer_faces_at(&point.conjugate());
                assert_eq!(forward.dispersive, conjugated.dispersive, "{name}");
                assert_eq!(forward.absorptive, -conjugated.absorptive.clone(), "{name}");
                if forward.absorptive != conjugated.absorptive {
                    distinguishing += 1;
                }
            }
        }
        assert!(
            distinguishing > 0,
            "the conjugate point never differed, so the symmetry was tested on nothing"
        );
    }

    // --- the four-point spectral relation -----------------------------------------------------

    #[test]
    fn the_four_point_spectral_relation_is_the_deposits_formula_and_is_exact() {
        // h0 = 5/2, h1 = -3, h2 = 7/4 inside the aperture; h[-1] = 0.
        let fixture = response(2, &[(0, 1), (0, 1), (5, 2), (-3, 1), (7, 4)]);
        assert!(fixture.is_causal() && fixture.within_four_point_aperture());
        let spectral = fixture.four_point_spectral_reflection();

        // Hand figures. D = [h0+h1+h2, h0-h2, h0-h1+h2, h0-h2]; A = [0, -h1, 0, h1].
        assert_eq!(
            spectral.dispersive,
            [rat(5, 4), rat(3, 4), rat(29, 4), rat(3, 4)]
        );
        assert_eq!(
            spectral.absorptive,
            [Rat::zero(), integer(3), Rat::zero(), integer(-3)]
        );
        assert!(!spectral.is_vacuous(), "a vacuous spectrum tests nothing");

        assert_eq!(spectral.derived_absorptive, spectral.absorptive);
        assert_eq!(spectral.derived_dispersive, spectral.dispersive);
        assert!(spectral.absorptive_residual.iter().all(Rat::is_zero));
        assert!(spectral.dispersive_residual.iter().all(Rat::is_zero));
        assert!(spectral.locks());
        assert!(spectral.folded_advanced.is_zero());

        // The subtracted direction genuinely needs its constants: they are nonzero here, and the
        // three-point stencil alone would miss them.
        assert_eq!(spectral.subtraction_constants, [rat(5, 2), rat(7, 4)]);
        assert!(
            spectral
                .subtraction_constants
                .iter()
                .all(|constant| !constant.is_zero())
        );
        let unsubtracted: [Rat; 4] = std::array::from_fn(|k| {
            halved(spectral.absorptive[(k + 3) % 4].clone() - &spectral.absorptive[(k + 1) % 4])
        });
        assert_ne!(
            unsubtracted, spectral.dispersive,
            "an unsubtracted dispersion relation must NOT reproduce Re chi"
        );
    }

    #[test]
    fn the_four_point_relation_fails_exactly_when_the_folded_arc_is_occupied() {
        for (numerator, denominator) in [(1, 1), (-2, 3), (9, 5)] {
            let leak = rat(numerator, denominator);
            let fixture = CausalResponse::new(
                2,
                grain(),
                vec![Rat::zero(), leak.clone(), rat(5, 2), integer(-3), rat(7, 4)],
            )
            .expect("a lawful declaration");
            assert!(!fixture.is_causal());
            assert!(fixture.within_four_point_aperture());

            let spectral = fixture.four_point_spectral_reflection();
            assert_eq!(spectral.folded_advanced, leak);
            assert!(!spectral.locks(), "an occupied arc locked");

            // The residual is exactly ±2·fold[3], at the two frequencies the stencil reaches.
            let doubled = integer(2) * &leak;
            assert_eq!(
                spectral.absorptive_residual,
                [Rat::zero(), doubled.clone(), Rat::zero(), -doubled.clone()]
            );
            assert_eq!(
                spectral.dispersive_residual,
                [doubled.clone(), Rat::zero(), -doubled.clone(), Rat::zero()]
            );
            assert!(!doubled.is_zero(), "a zero leak would make this vacuous");
        }
    }

    /// The biconditional for the spectral organ, decided by exhaustion inside its aperture.
    #[test]
    fn the_four_point_lock_holds_exactly_when_the_folded_arc_is_empty() {
        let alphabet = [integer(-1), Rat::zero(), integer(3)];
        let mut occupied = 0usize;
        let mut empty = 0usize;
        for code in 0..alphabet.len().pow(4) {
            let mut remaining = code;
            let values: Vec<Rat> = (0..4)
                .map(|_| {
                    let digit = remaining % alphabet.len();
                    remaining /= alphabet.len();
                    alphabet[digit].clone()
                })
                .collect();
            // Lattice indices -1, 0, 1, 2: exactly one period, so folding is injective.
            let fixture = CausalResponse::new(
                2,
                grain(),
                vec![
                    Rat::zero(),
                    values[0].clone(),
                    values[1].clone(),
                    values[2].clone(),
                    values[3].clone(),
                ],
            )
            .expect("a lawful declaration");
            let spectral = fixture.four_point_spectral_reflection();
            assert_eq!(
                spectral.locks(),
                spectral.folded_advanced.is_zero(),
                "the spectral biconditional failed on {:?}",
                fixture.values()
            );
            assert_eq!(
                spectral.locks(),
                fixture.is_causal(),
                "inside the aperture the folded reading is the response's own reading: {:?}",
                fixture.values()
            );
            if spectral.folded_advanced.is_zero() {
                empty += 1;
            } else {
                occupied += 1;
            }
        }
        assert_eq!(empty, 27);
        assert_eq!(occupied, 54);
    }

    /// The aperture is measured, not asserted. Conducted past it the organ **appears to return**:
    /// every residual is zero on material that is not causal.
    #[test]
    fn the_four_point_aperture_is_measured_and_not_asserted() {
        // A single nonzero value at n = -2, which folds onto the causal arc slot 2.
        let outside = response(2, &[(6, 1), (0, 1), (5, 2), (-3, 1), (7, 4)]);
        assert!(!outside.is_causal(), "n = -2 is before the stimulus");
        assert!(
            !outside.within_four_point_aperture(),
            "the declared aperture must exclude it"
        );

        let spectral = outside.four_point_spectral_reflection();
        assert!(
            spectral.locks(),
            "this fixture exists to exhibit an aperture violation that passes every check"
        );
        assert!(
            spectral.folded_advanced.is_zero(),
            "the leak aliased into slot 2"
        );
        assert!(!spectral.is_vacuous());

        // The response-domain law, which has no aperture limit, refuses it.
        let lock = causality_lock(&outside).expect("a lawful lock");
        assert!(!lock.locks(), "the lattice reading must still refuse it");
        assert_eq!(lock.advanced_support, vec![-2]);
        assert_eq!(lock.dispersive_to_absorptive.residual_at(-2), integer(6));
    }

    /// Two independent implementations of the same four rationals, graded against each other.
    ///
    /// Folding then transforming costs `O(M)` additions and no multiplication; evaluating the
    /// transfer function at the four Gaussian points costs `O(M)` Gaussian-rational
    /// multiplications. The cheaper one is the fold.
    #[test]
    fn the_fold_and_the_direct_evaluation_are_independent_routes_to_one_spectrum() {
        let gaussian_points = [
            RationalCirclePoint::new(integer(1), Rat::zero()).unwrap(),
            RationalCirclePoint::new(Rat::zero(), integer(1)).unwrap(),
            RationalCirclePoint::new(integer(-1), Rat::zero()).unwrap(),
            RationalCirclePoint::new(Rat::zero(), integer(-1)).unwrap(),
        ];
        for (name, fixture) in every_fixture() {
            let spectral = fixture.four_point_spectral_reflection();
            for (k, point) in gaussian_points.iter().enumerate() {
                let direct = fixture.transfer_faces_at(point);
                assert_eq!(
                    direct.dispersive, spectral.dispersive[k],
                    "{name}: Re chi disagreed at k = {k}"
                );
                assert_eq!(
                    direct.absorptive, spectral.absorptive[k],
                    "{name}: Im chi disagreed at k = {k}"
                );
            }
        }
        // And the routes are compared on material where they return something.
        let spectral = causal_tail().four_point_spectral_reflection();
        assert!(!spectral.is_vacuous());
    }

    // --- gauges and refusals ------------------------------------------------------------------

    /// The grain is a receiver gauge on the declaration. It appears in every carrier and moves
    /// nothing in the law, which is why the law is about the lattice and not about the sampling.
    #[test]
    fn the_lattice_grain_moves_nothing_in_the_law() {
        for (name, fixture) in every_fixture() {
            let reference = causality_lock(&fixture).expect("a lawful lock");
            for (numerator, denominator) in [(1, 1), (7, 2), (1, 1000), (99, 7)] {
                let regrained = CausalResponse::new(
                    fixture.half_extent(),
                    rat(numerator, denominator),
                    fixture.values().to_vec(),
                )
                .expect("a lawful declaration");
                let lock = causality_lock(&regrained).expect("a lawful lock");
                assert_eq!(lock.locks(), reference.locks(), "{name}");
                assert_eq!(
                    lock.dispersive_to_absorptive.standing_residuals(),
                    reference.dispersive_to_absorptive.standing_residuals(),
                    "{name}: the grain moved a residual"
                );
                assert_eq!(
                    lock.subtraction_constants, reference.subtraction_constants,
                    "{name}"
                );
            }
        }
    }

    #[test]
    fn faces_on_different_lattices_cannot_be_compared() {
        let narrow = minimal_causal();
        let wide = causal_tail();
        assert_eq!(
            narrow
                .dispersive_face()
                .reflect_and_compare(&wide.absorptive_face()),
            Err(CausalReflectionError::LatticesDiffer)
        );

        let regrained =
            CausalResponse::new(narrow.half_extent(), integer(5), narrow.values().to_vec())
                .unwrap();
        assert_eq!(
            narrow
                .dispersive_face()
                .reflect_and_compare(&regrained.absorptive_face()),
            Err(CausalReflectionError::LatticesDiffer)
        );

        // And comparing a derived face against a face of the wrong parity is refused.
        assert!(matches!(
            narrow
                .dispersive_face()
                .reflect_and_compare(&narrow.dispersive_face()),
            Err(CausalReflectionError::FaceParityMismatch {
                expected: FaceParity::Absorptive,
                supplied: FaceParity::Dispersive
            })
        ));
    }

    #[test]
    fn unlawful_declarations_are_refused() {
        assert_eq!(
            CausalResponse::new(0, grain(), vec![integer(1)]),
            Err(CausalReflectionError::LatticeExtentZero)
        );
        assert_eq!(
            CausalResponse::new(1, Rat::zero(), vec![integer(1); 3]),
            Err(CausalReflectionError::SampleStepNotPositive)
        );
        assert_eq!(
            CausalResponse::new(1, integer(-2), vec![integer(1); 3]),
            Err(CausalReflectionError::SampleStepNotPositive)
        );
        assert!(matches!(
            CausalResponse::new(2, grain(), vec![integer(1); 4]),
            Err(CausalReflectionError::LatticeWidthMismatch {
                half_extent: 2,
                declared: 5,
                supplied: 4
            })
        ));
        assert!(matches!(
            CausalResponse::from_retarded_values(2, grain(), &[integer(1), integer(1)]),
            Err(CausalReflectionError::LatticeWidthMismatch { .. })
        ));
        assert!(matches!(
            ExactResponseFace::new(FaceParity::Dispersive, 0, grain(), vec![integer(0)]),
            Err(CausalReflectionError::LatticeExtentZero)
        ));
        assert!(matches!(
            CausalResponse::from_faces(
                &causal_tail().absorptive_face(),
                &causal_tail().absorptive_face()
            ),
            Err(CausalReflectionError::FaceParityMismatch { .. })
        ));
    }

    #[test]
    fn the_retarded_constructor_declares_a_causal_response() {
        let built = CausalResponse::from_retarded_values(
            3,
            grain(),
            &[rat(5, 2), integer(-3), rat(7, 4), integer(1)],
        )
        .expect("a lawful declaration");
        assert_eq!(built, causal_tail());
        assert!(built.is_causal());
        assert!(causality_lock(&built).unwrap().locks());
    }

    // --- provably nonzero controls ------------------------------------------------------------

    /// `CLAUDE.md` §8: a law that returns zero proves nothing about itself. Every population this
    /// module can return is exercised here on material that forces it to be non-empty.
    #[test]
    fn nonzero_controls() {
        let causal = causal_tail();
        let acausal = advanced_leak();

        // The faces themselves.
        assert!(!causal.dispersive_face().is_zero());
        assert!(!causal.absorptive_face().is_zero());
        assert!(!causal.dispersive_face().moving_support().is_empty());
        assert!(!causal.absorptive_face().moving_support().is_empty());

        // The derived face is not a copy of the source face: the transform does something.
        let derived = causal.dispersive_face().reflect();
        assert_ne!(
            derived.values(),
            causal.dispersive_face().values(),
            "the signature left the face unchanged, so it transformed nothing"
        );
        assert_eq!(derived, causal.absorptive_face());

        // The lock's populations.
        let lock = causality_lock(&acausal).expect("a lawful lock");
        assert!(!lock.advanced_support.is_empty());
        assert!(!lock.dispersive_to_absorptive.standing_indices.is_empty());
        assert!(!lock.absorptive_to_dispersive.standing_indices.is_empty());
        assert!(!lock.blind_free());
        assert!(
            lock.dispersive_to_absorptive
                .standing_residuals()
                .iter()
                .any(|(_, residual)| !residual.is_zero())
        );
        assert!(!lock.subtraction_constants[0].value.is_zero());

        // The holomorphy witness.
        assert!(
            !acausal
                .holomorphy_witness()
                .advanced_coefficients
                .is_empty()
        );
        assert!(acausal.holomorphy_witness().pole_order_at_infinity() > 0);

        // The spectral faces at a point that is neither real nor a Gaussian unit.
        let point = RationalCirclePoint::from_slope(&rat(1, 2));
        let faces = causal.transfer_faces_at(&point);
        assert!(!faces.dispersive.is_zero(), "Re chi vanished");
        assert!(!faces.absorptive.is_zero(), "Im chi vanished");
        assert_ne!(point.real(), &Rat::zero());
        assert_ne!(point.imaginary(), &Rat::zero());

        // The four-point spectrum.
        let spectral = causal.four_point_spectral_reflection();
        assert!(!spectral.is_vacuous());
        assert!(spectral.folded.iter().any(|value| !value.is_zero()));
    }

    impl CausalityLock {
        /// A helper for the nonzero control: some fixed-point residual stands.
        fn blind_free(&self) -> bool {
            self.absorptive_to_dispersive
                .blind_residuals
                .iter()
                .all(|residual| residual.residual.is_zero())
        }
    }
}
