import ElementaryHolonics.Millennium.NavierStokesWeightedMildCoefficientEquation

/-!
# The exact modal pressure carried by the weighted mild fixed point

**[proved-derived]** The unprojected `H³` divergence convolution and its Leray face differ by
an exact frequency gradient.  At every nonzero mode this owner returns the unique scalar
coefficient producing that gradient, and fixes the zero-mode pressure gauge to zero.

The coefficient inherits Fourier conjugate symmetry from a real weighted path.  Combining its
gradient multiplier with the already returned coefficientwise mild ODE restores the unprojected
Fourier momentum identity.  These are coefficient-level statements only: no spatial pressure
field, convergence of a pressure Fourier series, or classical pressure regularity is asserted.
-/

noncomputable section

open Function Set
open scoped ComplexConjugate NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedPressureCoefficient

open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedMildCoefficientEquation
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The scalar Leray-complement coefficient -/

/-- The Fourier gradient multiplier `2π i k` applied to one scalar coefficient. -/
def pressureFrequencyGradient
    (k : SpatialFrequency) (pressure : ℂ) : ComplexVector :=
  fun component ↦
    (2 * (Real.pi : ℂ) * Complex.I * (k component : ℂ)) * pressure

@[simp]
theorem pressureFrequencyGradient_zero (pressure : ℂ) :
    pressureFrequencyGradient 0 pressure = 0 := by
  funext component
  simp [pressureFrequencyGradient]

/-- The zero-gauge scalar coefficient whose gradient is the Leray complement of `mode`. -/
def pressureCoefficientOfMode
    (k : SpatialFrequency) (mode : ComplexVector) : ℂ :=
  if k = 0 then 0
  else
    Complex.I * complexDot (complexFrequencyVector k) mode /
      ((2 * (Real.pi : ℂ)) * (frequencySquared k : ℂ))

@[simp]
theorem pressureCoefficientOfMode_zero (mode : ComplexVector) :
    pressureCoefficientOfMode 0 mode = 0 := by
  simp [pressureCoefficientOfMode]

/-- The modal pressure gradient is exactly `Pₖ mode - mode`, including the fixed zero gauge. -/
theorem pressureFrequencyGradient_pressureCoefficientOfMode
    (k : SpatialFrequency) (mode : ComplexVector) :
    pressureFrequencyGradient k (pressureCoefficientOfMode k mode) =
      lerayProjectMode k mode - mode := by
  by_cases hk : k = 0
  · subst k
    simp
  · have hfrequencyReal : frequencySquared k ≠ 0 :=
      (frequencySquared_pos hk).ne'
    have hfrequency : (frequencySquared k : ℂ) ≠ 0 := by
      exact_mod_cast hfrequencyReal
    have htwoPiReal : 2 * Real.pi ≠ 0 :=
      mul_ne_zero (by norm_num) Real.pi_ne_zero
    have htwoPi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      exact_mod_cast htwoPiReal
    rw [lerayProjectMode, if_neg hk]
    funext component
    simp only [pressureFrequencyGradient, pressureCoefficientOfMode, if_neg hk,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, complexFrequencyVector]
    field_simp [hfrequency, htwoPi]
    rw [Complex.I_sq]
    ring

/-- Negating the frequency and conjugating the vector mode conjugates its zero-gauge pressure
coefficient. -/
theorem pressureCoefficientOfMode_neg_conj
    (k : SpatialFrequency) (mode : ComplexVector) :
    pressureCoefficientOfMode (-k) (fun component ↦ conj (mode component)) =
      conj (pressureCoefficientOfMode k mode) := by
  by_cases hk : k = 0
  · subst k
    simp
  · have hneg : -k ≠ 0 := neg_ne_zero.mpr hk
    rw [pressureCoefficientOfMode, if_neg hneg,
      pressureCoefficientOfMode, if_neg hk,
      complexDot_frequencyNeg_conj, frequencySquared_neg,
      map_div₀, map_mul, Complex.conj_I]
    simp only [map_mul, Complex.conj_ofNat, Complex.conj_ofReal]
    ring

/-! ## The actual weighted-path pressure coefficient -/

/-- The complete unprojected divergence-form quadratic vector at one weighted path face and
one Fourier mode. -/
def weightedUnprojectedDivergenceMode
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (t : ℝ) (k : SpatialFrequency) : ComplexVector :=
  fun component ↦
    (h3DivergenceConvolution
      (unweightedVectorThree (weightedPathExtension hT path t))
      (unweightedVectorThree (weightedPathExtension hT path t)) component).1 k

@[simp]
theorem weightedUnprojectedDivergenceMode_apply
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (t : ℝ) (k : SpatialFrequency) (component : Fin 3) :
    weightedUnprojectedDivergenceMode hT path t k component =
      (h3DivergenceConvolution
        (unweightedVectorThree (weightedPathExtension hT path t))
        (unweightedVectorThree (weightedPathExtension hT path t)) component).1 k :=
  rfl

/-- The exact zero-gauge pressure coefficient selected from the actual weighted-path quadratic
source. -/
def weightedPressureCoefficient
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (t : ℝ) (k : SpatialFrequency) : ℂ :=
  pressureCoefficientOfMode k (weightedUnprojectedDivergenceMode hT path t k)

@[simp]
theorem weightedPressureCoefficient_zero
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) (t : ℝ) :
    weightedPressureCoefficient hT path t 0 = 0 := by
  simp [weightedPressureCoefficient]

/-- The selected pressure coefficient returns exactly the actual Leray complement. -/
theorem pressureFrequencyGradient_weightedPressureCoefficient
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (t : ℝ) (k : SpatialFrequency) :
    pressureFrequencyGradient k (weightedPressureCoefficient hT path t k) =
      lerayProjectMode k (weightedUnprojectedDivergenceMode hT path t k) -
        weightedUnprojectedDivergenceMode hT path t k := by
  exact pressureFrequencyGradient_pressureCoefficientOfMode k _

/-- The actual unprojected quadratic mode is conjugate symmetric along every Fourier-real path. -/
theorem weightedUnprojectedDivergenceMode_neg_eq_conj
    {T : ℝ} (hT : 0 ≤ T) {path : WeightedH3Path T}
    (hpath : IsWeightedFourierRealPath path) (t : ℝ) (k : SpatialFrequency) :
    weightedUnprojectedDivergenceMode hT path t (-k) =
      fun component ↦ conj (weightedUnprojectedDivergenceMode hT path t k component) := by
  funext component
  exact h3DivergenceConvolution_neg_eq_conj
    (unweightedVectorThree (weightedPathExtension hT path t))
    (unweightedVectorThree (weightedPathExtension hT path t))
    (hpath.extension hT t) (hpath.extension hT t) component k

/-- Therefore the zero-gauge pressure coefficients have exact Fourier conjugate symmetry. -/
theorem weightedPressureCoefficient_neg_eq_conj
    {T : ℝ} (hT : 0 ≤ T) {path : WeightedH3Path T}
    (hpath : IsWeightedFourierRealPath path) (t : ℝ) (k : SpatialFrequency) :
    weightedPressureCoefficient hT path t (-k) =
      conj (weightedPressureCoefficient hT path t k) := by
  rw [weightedPressureCoefficient, weightedPressureCoefficient,
    weightedUnprojectedDivergenceMode_neg_eq_conj hT hpath t k]
  exact pressureCoefficientOfMode_neg_conj k _

/-! ## The unprojected coefficientwise momentum identity -/

/-- **Exact unprojected Fourier momentum equation.**  The modal derivative of a mild fixed point
is viscous diagonal decay minus the complete unprojected divergence convolution and minus the
zero-gauge pressure gradient coefficient. -/
theorem fixedPoint_weightedMildMap_unprojectedMomentum_hasDerivAt
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3) (path : WeightedH3Path T)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) path)
    (component : Fin 3) (k : SpatialFrequency) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun tau : ℝ ↦
        (weightedSobolevCoefficients 3
          (weightedPathExtension hT path tau component)).1 k)
      (((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
          (weightedSobolevCoefficients 3
            (weightedPathExtension hT path t component)).1 k -
        weightedUnprojectedDivergenceMode hT path t k component -
        pressureFrequencyGradient k
          (weightedPressureCoefficient hT path t k) component) t := by
  have hode := fixedPoint_weightedMildMap_physicalCoefficient_hasDerivAt
    nu hnu hT initial path hfixed component k ht
  have hprojected :
      (lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree (weightedPathExtension hT path t))
        (unweightedVectorThree (weightedPathExtension hT path t)) component).1 k =
      lerayProjectMode k (weightedUnprojectedDivergenceMode hT path t k) component := by
    exact congrFun
      (vectorCoefficientAt_lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree (weightedPathExtension hT path t))
        (unweightedVectorThree (weightedPathExtension hT path t)) k) component
  have hgradient := congrFun
    (pressureFrequencyGradient_weightedPressureCoefficient hT path t k) component
  apply hode.congr_deriv
  simp only [Pi.sub_apply] at hgradient
  rw [hprojected, hgradient]
  ring

section Audit

#print axioms pressureFrequencyGradient
#print axioms pressureFrequencyGradient_zero
#print axioms pressureCoefficientOfMode
#print axioms pressureCoefficientOfMode_zero
#print axioms pressureFrequencyGradient_pressureCoefficientOfMode
#print axioms pressureCoefficientOfMode_neg_conj
#print axioms weightedUnprojectedDivergenceMode
#print axioms weightedUnprojectedDivergenceMode_apply
#print axioms weightedPressureCoefficient
#print axioms weightedPressureCoefficient_zero
#print axioms pressureFrequencyGradient_weightedPressureCoefficient
#print axioms weightedUnprojectedDivergenceMode_neg_eq_conj
#print axioms weightedPressureCoefficient_neg_eq_conj
#print axioms fixedPoint_weightedMildMap_unprojectedMomentum_hasDerivAt

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedPressureCoefficient
