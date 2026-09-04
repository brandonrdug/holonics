import ElementaryHolonics.Millennium.NavierStokesFiniteFourierHeat

/-!
# Infinite Fourier heat transport on the periodic Hilbert carrier

**[definition]** This module replaces the predecessor's declared finite mode population by Mathlib's genuine
Fourier Hilbert basis for `L²((ℝ / ℤ)³)`.  Its coefficient carrier is Mathlib's
`ℓ²((Fin 3 → ℤ), ℂ)` representation, and the Sobolev carrier retains the complete weighted
coefficient summability witness.

**[proved-derived]** The diagonal heat multiplier defines an infinite `L²` semigroup for nonnegative viscosity and
time.  It is nonexpanding, and at every strictly positive viscous time it enters the first
inhomogeneous periodic Sobolev carrier with an explicit squared-norm estimate.

**[open]** These are linear heat/Stokes precursor statements only.  No nonlinear Navier--Stokes
local solution, fixed point, Galerkin limit, or continuation theorem is asserted.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal lp
open MeasureTheory

namespace Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat

open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat

/- Mathlib's multivariate Fourier basis uses probability Haar measure on each unit circle. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- [definition] The actual scalar `L²` carrier on the probability-Haar three-torus. -/
abbrev PeriodicL2 := Lp ℂ 2 (volume : Measure SpatialTorus)

/-- [definition] The complete Fourier coefficient carrier supplied by Mathlib's Hilbert basis. -/
abbrev PeriodicFourierL2 := ℓ²(SpatialFrequency, ℂ)

/-- [definition] Mathlib's Fourier Hilbert representation of the genuine periodic `L²` carrier. -/
def periodicFourierRepresentation : PeriodicL2 ≃ₗᵢ[ℂ] PeriodicFourierL2 :=
  UnitAddTorus.mFourierBasis.repr

/-- [proved-derived] The Hilbert-coordinate reading is exactly Mathlib's torus Fourier
coefficient, not a separately authored sequence chart. -/
theorem periodicFourierRepresentation_apply (field : PeriodicL2) (k : SpatialFrequency) :
    periodicFourierRepresentation field k = UnitAddTorus.mFourierCoeff field k := by
  exact UnitAddTorus.mFourierBasis_repr field k

/-- [definition] Squared inhomogeneous Sobolev weight of natural order `order`.  The Laplace
eigenvalue is the exact unit-torus eigenvalue already used by the finite heat owner. -/
def periodicSobolevWeight (order : ℕ) (k : SpatialFrequency) : ℝ :=
  (1 + torusStokesEigenvalue k) ^ order

/-- [proved-derived] Every inhomogeneous Sobolev weight is nonnegative. -/
theorem periodicSobolevWeight_nonneg (order : ℕ) (k : SpatialFrequency) :
    0 ≤ periodicSobolevWeight order k := by
  exact pow_nonneg (add_nonneg zero_le_one (torusStokesEigenvalue_nonneg k)) _

/-- [definition] A Fourier `ℓ²` population has periodic Sobolev order `order` exactly when its
complete weighted squared-coefficient population is summable. -/
def HasPeriodicSobolevCoefficients
    (order : ℕ) (coeff : PeriodicFourierL2) : Prop :=
  Summable fun k ↦ periodicSobolevWeight order k * ‖coeff k‖ ^ 2

/-- [definition] An honest weighted `ℓ²` periodic Sobolev coefficient carrier. -/
def PeriodicSobolevCoefficients (order : ℕ) :=
  {coeff : PeriodicFourierL2 // HasPeriodicSobolevCoefficients order coeff}

/-- [definition] The corresponding periodic Sobolev field carrier, bound through the actual
Fourier Hilbert representation. -/
def PeriodicSobolevField (order : ℕ) :=
  {field : PeriodicL2 //
    HasPeriodicSobolevCoefficients order (periodicFourierRepresentation field)}

private theorem periodicFourierL2_summable_sq (coeff : PeriodicFourierL2) :
    Summable fun k ↦ ‖coeff k‖ ^ 2 := by
  have h := (lp.memℓp coeff).summable
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa using h

private theorem periodicFourierL2_tsum_sq (coeff : PeriodicFourierL2) :
    (∑' k, ‖coeff k‖ ^ 2) = ‖coeff‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) coeff
  simpa using h.symm

/-- [proved-derived] Order zero is exactly the underlying Fourier `ℓ²` carrier. -/
theorem hasPeriodicSobolevCoefficients_zero (coeff : PeriodicFourierL2) :
    HasPeriodicSobolevCoefficients 0 coeff := by
  simpa [HasPeriodicSobolevCoefficients, periodicSobolevWeight] using
    periodicFourierL2_summable_sq coeff

private theorem norm_heatStokesMultiplier_mul_sq_le
    (nu t : ℝ≥0) (k : SpatialFrequency) (z : ℂ) :
    ‖(heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) * z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  obtain ⟨hm0, hm1⟩ := heatStokesMultiplier_mem_unitInterval
    nu.coe_nonneg t.coe_nonneg k
  have hm_sq :
      heatStokesMultiplier (nu : ℝ) (t : ℝ) k *
          heatStokesMultiplier (nu : ℝ) (t : ℝ) k ≤ 1 := by
    nlinarith
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm0]
  rw [pow_two, pow_two]
  calc
    (heatStokesMultiplier (nu : ℝ) (t : ℝ) k * ‖z‖) *
        (heatStokesMultiplier (nu : ℝ) (t : ℝ) k * ‖z‖) =
        (heatStokesMultiplier (nu : ℝ) (t : ℝ) k *
          heatStokesMultiplier (nu : ℝ) (t : ℝ) k) * (‖z‖ * ‖z‖) := by ring
    _ ≤ 1 * (‖z‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_right hm_sq (mul_self_nonneg _)
    _ = ‖z‖ * ‖z‖ := one_mul _

/-- [definition] Infinite diagonal heat action on the complete Fourier `ℓ²` population.
Nonnegative-real parameters make the diagonal multiplier contractive, which is the witness that
the returned coefficient function remains in `ℓ²`. -/
def infiniteHeatCoefficientEvolution
    (nu t : ℝ≥0) (coeff : PeriodicFourierL2) : PeriodicFourierL2 :=
  ⟨fun k ↦ (heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) * coeff k, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    refine Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_)
      (periodicFourierL2_summable_sq coeff)
    simpa only [Real.rpow_two] using
      norm_heatStokesMultiplier_mul_sq_le nu t k (coeff k)⟩

@[simp]
theorem infiniteHeatCoefficientEvolution_apply
    (nu t : ℝ≥0) (coeff : PeriodicFourierL2) (k : SpatialFrequency) :
    infiniteHeatCoefficientEvolution nu t coeff k =
      (heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) * coeff k := rfl

/-- [proved-derived] The infinite diagonal coefficient action starts at the identity. -/
@[simp]
theorem infiniteHeatCoefficientEvolution_zero_time
    (nu : ℝ≥0) (coeff : PeriodicFourierL2) :
    infiniteHeatCoefficientEvolution nu 0 coeff = coeff := by
  apply lp.ext
  funext k
  simp

/-- [proved-derived] The infinite diagonal coefficient action composes exactly in elapsed time. -/
theorem infiniteHeatCoefficientEvolution_add
    (nu s t : ℝ≥0) (coeff : PeriodicFourierL2) :
    infiniteHeatCoefficientEvolution nu (s + t) coeff =
      infiniteHeatCoefficientEvolution nu s
        (infiniteHeatCoefficientEvolution nu t coeff) := by
  apply lp.ext
  funext k
  simp only [infiniteHeatCoefficientEvolution_apply, NNReal.coe_add,
    heatStokesMultiplier_add]
  rw [Complex.ofReal_mul]
  ring

/-- [proved-derived] The infinite Fourier heat action is nonexpanding on `ℓ²`. -/
theorem norm_infiniteHeatCoefficientEvolution_le
    (nu t : ℝ≥0) (coeff : PeriodicFourierL2) :
    ‖infiniteHeatCoefficientEvolution nu t coeff‖ ≤ ‖coeff‖ := by
  apply lp.norm_le_of_forall_sum_le
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (norm_nonneg coeff)
  intro modes
  calc
    ∑ k ∈ modes, ‖infiniteHeatCoefficientEvolution nu t coeff k‖ ^
        (2 : ℝ≥0∞).toReal ≤
        ∑ k ∈ modes, ‖coeff k‖ ^ (2 : ℝ≥0∞).toReal := by
          apply Finset.sum_le_sum
          intro k _hk
          norm_num only [ENNReal.toReal_ofNat]
          simpa only [infiniteHeatCoefficientEvolution_apply, Real.rpow_two] using
            norm_heatStokesMultiplier_mul_sq_le nu t k (coeff k)
    _ ≤ ‖coeff‖ ^ (2 : ℝ≥0∞).toReal :=
      lp.sum_rpow_le_norm_rpow
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal) coeff modes

/-- [definition] Infinite periodic heat evolution obtained by conjugating the complete diagonal
coefficient action through Mathlib's Fourier Hilbert isometry. -/
def infinitePeriodicHeatEvolution
    (nu t : ℝ≥0) (field : PeriodicL2) : PeriodicL2 :=
  periodicFourierRepresentation.symm
    (infiniteHeatCoefficientEvolution nu t (periodicFourierRepresentation field))

/-- [proved-derived] The actual torus Fourier coefficients of the infinite evolution are the
finite owner's multiplier applied modewise. -/
theorem periodicFourierRepresentation_infinitePeriodicHeatEvolution
    (nu t : ℝ≥0) (field : PeriodicL2) :
    periodicFourierRepresentation (infinitePeriodicHeatEvolution nu t field) =
      infiniteHeatCoefficientEvolution nu t (periodicFourierRepresentation field) := by
  exact periodicFourierRepresentation.apply_symm_apply _

/-- [proved-derived] Infinite periodic heat transport is an exact semigroup on the actual torus
`L²` carrier. -/
theorem infinitePeriodicHeatEvolution_add
    (nu s t : ℝ≥0) (field : PeriodicL2) :
    infinitePeriodicHeatEvolution nu (s + t) field =
      infinitePeriodicHeatEvolution nu s (infinitePeriodicHeatEvolution nu t field) := by
  apply periodicFourierRepresentation.injective
  rw [periodicFourierRepresentation_infinitePeriodicHeatEvolution,
    infiniteHeatCoefficientEvolution_add,
    periodicFourierRepresentation_infinitePeriodicHeatEvolution,
    periodicFourierRepresentation_infinitePeriodicHeatEvolution]

/-- [proved-derived] Infinite periodic heat transport is nonexpanding in the actual torus `L²`
norm. -/
theorem norm_infinitePeriodicHeatEvolution_le
    (nu t : ℝ≥0) (field : PeriodicL2) :
    ‖infinitePeriodicHeatEvolution nu t field‖ ≤ ‖field‖ := by
  simpa [infinitePeriodicHeatEvolution] using
    norm_infiniteHeatCoefficientEvolution_le nu t
      (periodicFourierRepresentation field)

/-! ## One-order Sobolev smoothing at positive viscous time -/

/-- [proved-derived] The elementary exponential bound controlling one inhomogeneous Sobolev
weight.  Its constant is explicit and finite whenever `nu * t > 0`. -/
theorem periodicSobolevWeight_one_mul_heat_sq_le
    {nu t : ℝ} (hviscous : 0 < nu * t) (k : SpatialFrequency) :
    periodicSobolevWeight 1 k * (heatStokesMultiplier nu t k) ^ 2 ≤
      1 + (2 * (nu * t))⁻¹ := by
  let lambda := torusStokesEigenvalue k
  let a := 2 * (nu * t)
  have hlambda : 0 ≤ lambda := torusStokesEigenvalue_nonneg k
  have ha : 0 < a := mul_pos (by norm_num) hviscous
  let x := a * lambda
  have hx0 : 0 ≤ x := mul_nonneg ha.le hlambda
  have hxexp : x * Real.exp (-x) ≤ 1 := by
    have hx_le_exp : x ≤ Real.exp x :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp x)
    have := mul_le_mul_of_nonneg_right hx_le_exp (Real.exp_pos (-x)).le
    simpa [← Real.exp_add] using this
  have hexp_le_one : Real.exp (-x) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx0)
  have hlambda_exp : lambda * Real.exp (-x) ≤ a⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ ha).2
    calc
      (lambda * Real.exp (-x)) * a = x * Real.exp (-x) := by
        dsimp [x]
        ring
      _ ≤ 1 := hxexp
  have hmultiplier_sq :
      (heatStokesMultiplier nu t k) ^ 2 = Real.exp (-x) := by
    rw [heatStokesMultiplier, pow_two, ← Real.exp_add]
    congr 1
    dsimp [x, a, lambda]
    ring
  rw [hmultiplier_sq]
  change (1 + lambda) ^ 1 * Real.exp (-x) ≤ 1 + a⁻¹
  rw [pow_one]
  calc
    (1 + lambda) * Real.exp (-x) =
        Real.exp (-x) + lambda * Real.exp (-x) := by ring
    _ ≤ 1 + a⁻¹ := add_le_add hexp_le_one hlambda_exp

/-- [proved-derived] Every positive viscous time sends arbitrary Fourier `ℓ²` data into the
first periodic Sobolev coefficient carrier. -/
theorem infiniteHeatCoefficientEvolution_hasPeriodicSobolev_one
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (coeff : PeriodicFourierL2) :
    HasPeriodicSobolevCoefficients 1
      (infiniteHeatCoefficientEvolution nu t coeff) := by
  let C : ℝ := 1 + (2 * ((nu : ℝ) * (t : ℝ)))⁻¹
  have hsource : Summable (fun k ↦ C * ‖coeff k‖ ^ 2) :=
    (periodicFourierL2_summable_sq coeff).mul_left C
  unfold HasPeriodicSobolevCoefficients
  refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_) hsource
  · exact mul_nonneg (periodicSobolevWeight_nonneg 1 k) (sq_nonneg _)
  · have hmode := periodicSobolevWeight_one_mul_heat_sq_le hviscous k
    calc
      periodicSobolevWeight 1 k *
          ‖infiniteHeatCoefficientEvolution nu t coeff k‖ ^ 2 =
          (periodicSobolevWeight 1 k *
            (heatStokesMultiplier (nu : ℝ) (t : ℝ) k) ^ 2) *
              ‖coeff k‖ ^ 2 := by
            have hm0 : 0 ≤ heatStokesMultiplier (nu : ℝ) (t : ℝ) k :=
              (Real.exp_pos _).le
            simp only [infiniteHeatCoefficientEvolution_apply, norm_mul,
              Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_nonneg hm0]
            ring
      _ ≤ C * ‖coeff k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hmode (sq_nonneg _)

/-- [proved-derived] Explicit one-order smoothing estimate.  The left side is the complete
weighted squared Fourier population; the right side is the original `ℓ²` norm squared. -/
theorem tsum_periodicSobolevWeight_one_infiniteHeat_le
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (coeff : PeriodicFourierL2) :
    (∑' k, periodicSobolevWeight 1 k *
        ‖infiniteHeatCoefficientEvolution nu t coeff k‖ ^ 2) ≤
      (1 + (2 * ((nu : ℝ) * (t : ℝ)))⁻¹) * ‖coeff‖ ^ 2 := by
  let C : ℝ := 1 + (2 * ((nu : ℝ) * (t : ℝ)))⁻¹
  have hsmooth :=
    infiniteHeatCoefficientEvolution_hasPeriodicSobolev_one nu t hviscous coeff
  have hsource : Summable (fun k ↦ C * ‖coeff k‖ ^ 2) :=
    (periodicFourierL2_summable_sq coeff).mul_left C
  have hpoint : ∀ k,
      periodicSobolevWeight 1 k *
          ‖infiniteHeatCoefficientEvolution nu t coeff k‖ ^ 2 ≤
        C * ‖coeff k‖ ^ 2 := by
    intro k
    have hmode := periodicSobolevWeight_one_mul_heat_sq_le hviscous k
    calc
      periodicSobolevWeight 1 k *
          ‖infiniteHeatCoefficientEvolution nu t coeff k‖ ^ 2 =
          (periodicSobolevWeight 1 k *
            (heatStokesMultiplier (nu : ℝ) (t : ℝ) k) ^ 2) *
              ‖coeff k‖ ^ 2 := by
            have hm0 : 0 ≤ heatStokesMultiplier (nu : ℝ) (t : ℝ) k :=
              (Real.exp_pos _).le
            simp only [infiniteHeatCoefficientEvolution_apply, norm_mul,
              Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_nonneg hm0]
            ring
      _ ≤ C * ‖coeff k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hmode (sq_nonneg _)
  calc
    (∑' k, periodicSobolevWeight 1 k *
        ‖infiniteHeatCoefficientEvolution nu t coeff k‖ ^ 2) ≤
        ∑' k, C * ‖coeff k‖ ^ 2 :=
      hsmooth.tsum_le_tsum hpoint hsource
    _ = C * (∑' k, ‖coeff k‖ ^ 2) :=
      (periodicFourierL2_summable_sq coeff).tsum_mul_left C
    _ = C * ‖coeff‖ ^ 2 := by rw [periodicFourierL2_tsum_sq]

/-- [definition] The heat return packaged in the first periodic Sobolev coefficient carrier. -/
def infiniteHeatIntoPeriodicSobolevOne
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (coeff : PeriodicFourierL2) : PeriodicSobolevCoefficients 1 :=
  ⟨infiniteHeatCoefficientEvolution nu t coeff,
    infiniteHeatCoefficientEvolution_hasPeriodicSobolev_one nu t hviscous coeff⟩

/-- [definition] The actual periodic `L²` field after positive-time heat transport, packaged
with its complete first-order weighted Fourier witness. -/
def infinitePeriodicHeatIntoSobolevOne
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (field : PeriodicL2) : PeriodicSobolevField 1 :=
  ⟨infinitePeriodicHeatEvolution nu t field, by
    rw [periodicFourierRepresentation_infinitePeriodicHeatEvolution]
    exact infiniteHeatCoefficientEvolution_hasPeriodicSobolev_one nu t hviscous
      (periodicFourierRepresentation field)⟩

#print axioms periodicFourierRepresentation_apply
#print axioms hasPeriodicSobolevCoefficients_zero
#print axioms infiniteHeatCoefficientEvolution_add
#print axioms norm_infiniteHeatCoefficientEvolution_le
#print axioms infinitePeriodicHeatEvolution_add
#print axioms norm_infinitePeriodicHeatEvolution_le
#print axioms periodicSobolevWeight_one_mul_heat_sq_le
#print axioms infiniteHeatCoefficientEvolution_hasPeriodicSobolev_one
#print axioms tsum_periodicSobolevWeight_one_infiniteHeat_le

end Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
