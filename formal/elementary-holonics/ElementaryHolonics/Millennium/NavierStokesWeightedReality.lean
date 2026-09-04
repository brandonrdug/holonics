import ElementaryHolonics.Millennium.NavierStokesSmoothSliceWeightedH3
import ElementaryHolonics.Millennium.NavierStokesWeightedDuhamelBound

/-!
# Fourier reality on the native weighted restart carrier

The weighted restart argument is constructed over complex Hilbert spaces, while a velocity is a
real field.  This owner records the missing exact incidence: after removing the positive Sobolev
weight, the coefficient at `-k` is the complex conjugate of the coefficient at `k`.  It proves that
the actual Fourier population of every smooth real periodic slice has this property and that the
native heat and Leray--Duhamel passages preserve it.

Reality is imposed on the unweighted coefficients carried by a native weighted state.  Thus the
predicate speaks directly about the physical Fourier population and is independent of which
positive Sobolev order is used to realize that population.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ComplexConjugate ContDiff ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedReality

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH2ToH3HeatSmoothing
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound
open Soma.Holonics.Millennium.NavierStokesWeightedHeatSemigroup
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/- `mFourierCoeff` in the torus owners uses normalized Haar probability measure. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## The exact native reality incidence -/

/-- A native weighted vector state represents a real Fourier field when its actual unweighted
coefficient population has exact conjugate symmetry under `k ↔ -k`. -/
def IsWeightedFourierReal
    (order : ℕ) (state : PeriodicVectorWeightedSobolev order) : Prop :=
  ∀ component k,
    (weightedSobolevCoefficients order (state component)).1 (-k) =
      conj ((weightedSobolevCoefficients order (state component)).1 k)

/-- Because the Sobolev weight is positive and even, physical unweighted reality is equivalent to
the same exact conjugate symmetry on the coefficients stored by the native Hilbert carrier. -/
theorem isWeightedFourierReal_iff_native
    (order : ℕ) (state : PeriodicVectorWeightedSobolev order) :
    IsWeightedFourierReal order state ↔
      ∀ component k, state component (-k) = conj (state component k) := by
  constructor
  · intro hstate component k
    have hreconstructNeg := congrArg (fun scalar : PeriodicWeightedSobolev order ↦ scalar (-k))
      (coefficientWeightedRealization_weightedSobolevCoefficients
        order (state component))
    have hreconstruct := congrArg (fun scalar : PeriodicWeightedSobolev order ↦ scalar k)
      (coefficientWeightedRealization_weightedSobolevCoefficients
        order (state component))
    change coefficientWeightedRealization order
        (weightedSobolevCoefficients order (state component)) (-k) =
      state component (-k) at hreconstructNeg
    change coefficientWeightedRealization order
        (weightedSobolevCoefficients order (state component)) k =
      state component k at hreconstruct
    rw [coefficientWeightedRealization_apply,
      show periodicSobolevWeight order (-k) = periodicSobolevWeight order k by
        simp [periodicSobolevWeight, torusStokesEigenvalue, frequencySquared]] at hreconstructNeg
    rw [coefficientWeightedRealization_apply] at hreconstruct
    calc
      state component (-k) =
          (Real.sqrt (periodicSobolevWeight order k) : ℂ) *
            (weightedSobolevCoefficients order (state component)).1 (-k) :=
        hreconstructNeg.symm
      _ = (Real.sqrt (periodicSobolevWeight order k) : ℂ) *
          conj ((weightedSobolevCoefficients order (state component)).1 k) := by
        rw [hstate component k]
      _ = conj ((Real.sqrt (periodicSobolevWeight order k) : ℂ) *
          (weightedSobolevCoefficients order (state component)).1 k) := by
        simp
      _ = conj (state component k) := by rw [hreconstruct]
  · intro hstate component k
    change
      ((((Real.sqrt (periodicSobolevWeight order (-k)))⁻¹ : ℝ) : ℂ) *
          state component (-k)) =
        conj (((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) *
          state component k))
    rw [show periodicSobolevWeight order (-k) = periodicSobolevWeight order k by
      simp [periodicSobolevWeight, torusStokesEigenvalue, frequencySquared],
      hstate component k]
    simp

@[simp]
theorem frequencySquared_neg (k : SpatialFrequency) :
    frequencySquared (-k) = frequencySquared k := by
  simp [frequencySquared]

@[simp]
theorem torusStokesEigenvalue_neg (k : SpatialFrequency) :
    torusStokesEigenvalue (-k) = torusStokesEigenvalue k := by
  simp [torusStokesEigenvalue]

@[simp]
theorem periodicSobolevWeight_neg (order : ℕ) (k : SpatialFrequency) :
    periodicSobolevWeight order (-k) = periodicSobolevWeight order k := by
  simp [periodicSobolevWeight]

@[simp]
theorem heatStokesMultiplier_neg (nu t : ℝ) (k : SpatialFrequency) :
    heatStokesMultiplier nu t (-k) = heatStokesMultiplier nu t k := by
  simp [heatStokesMultiplier]

/-- The zero population is real at every Sobolev order. -/
theorem isWeightedFourierReal_zero (order : ℕ) :
    IsWeightedFourierReal order (0 : PeriodicVectorWeightedSobolev order) := by
  intro component k
  change
    ((((Real.sqrt (periodicSobolevWeight order (-k)))⁻¹ : ℝ) : ℂ) * 0) =
      conj (((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) * 0))
  simp

/-- Fourier-real native states are closed under addition. -/
theorem IsWeightedFourierReal.add
    {order : ℕ} {left right : PeriodicVectorWeightedSobolev order}
    (hleft : IsWeightedFourierReal order left)
    (hright : IsWeightedFourierReal order right) :
    IsWeightedFourierReal order (left + right) := by
  rw [isWeightedFourierReal_iff_native] at hleft hright ⊢
  intro component k
  simp only [Pi.add_apply, lp.coeFn_add, map_add]
  rw [hleft component k, hright component k]

/-- Fourier-real native states are closed under negation. -/
theorem IsWeightedFourierReal.neg
    {order : ℕ} {state : PeriodicVectorWeightedSobolev order}
    (hstate : IsWeightedFourierReal order state) :
    IsWeightedFourierReal order (-state) := by
  rw [isWeightedFourierReal_iff_native] at hstate ⊢
  intro component k
  simp only [Pi.neg_apply, lp.coeFn_neg, map_neg]
  rw [hstate component k]

/-- Fourier-real native states are closed under subtraction. -/
theorem IsWeightedFourierReal.sub
    {order : ℕ} {left right : PeriodicVectorWeightedSobolev order}
    (hleft : IsWeightedFourierReal order left)
    (hright : IsWeightedFourierReal order right) :
    IsWeightedFourierReal order (left - right) := by
  simpa only [sub_eq_add_neg] using hleft.add hright.neg

/-- Continuous evaluation of one native component at one addressed frequency. -/
def nativeWeightedCoefficient
    (order : ℕ) (component : Fin 3) (k : SpatialFrequency) :
    PeriodicVectorWeightedSobolev order →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun state ↦ state component k
      map_add' := by
        intro left right
        rfl
      map_smul' := by
        intro scalar state
        rfl }
    1 (fun state ↦ by
      calc
        ‖state component k‖ ≤ ‖state component‖ :=
          lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) _ _
        _ ≤ ‖state‖ := norm_le_pi_norm state component
        _ = 1 * ‖state‖ := by ring)

@[simp]
theorem nativeWeightedCoefficient_apply
    (order : ℕ) (component : Fin 3) (k : SpatialFrequency)
    (state : PeriodicVectorWeightedSobolev order) :
    nativeWeightedCoefficient order component k state = state component k :=
  rfl

/-- Fourier reality is a closed incidence in the complete native weighted Hilbert carrier. -/
theorem isClosed_setOf_isWeightedFourierReal (order : ℕ) :
    IsClosed {state : PeriodicVectorWeightedSobolev order |
      IsWeightedFourierReal order state} := by
  have hclosed : IsClosed (⋂ component : Fin 3, ⋂ k : SpatialFrequency,
      {state : PeriodicVectorWeightedSobolev order |
        nativeWeightedCoefficient order component (-k) state =
          conj (nativeWeightedCoefficient order component k state)}) := by
    apply isClosed_iInter
    intro component
    apply isClosed_iInter
    intro k
    exact isClosed_eq
      (nativeWeightedCoefficient order component (-k)).continuous
      (Complex.continuous_conj.comp
        (nativeWeightedCoefficient order component k).continuous)
  convert hclosed using 1
  ext state
  simp only [Set.mem_setOf_eq, Set.mem_iInter, nativeWeightedCoefficient_apply]
  exact isWeightedFourierReal_iff_native order state

/-- The Bochner interval integral of a pointwise Fourier-real native path is Fourier real.  This
is the exact return needed after pointwise Duhamel-integrand preservation. -/
theorem isWeightedFourierReal_intervalIntegral
    (order : ℕ) (path : ℝ → PeriodicVectorWeightedSobolev order)
    {a b : ℝ} (hpath : IntervalIntegrable path volume a b)
    (hreal : ∀ s, IsWeightedFourierReal order (path s)) :
    IsWeightedFourierReal order (∫ s in a..b, path s) := by
  rw [isWeightedFourierReal_iff_native]
  intro component k
  let negativeCoefficient := nativeWeightedCoefficient order component (-k)
  let positiveCoefficient := nativeWeightedCoefficient order component k
  have hnegative := negativeCoefficient.intervalIntegral_comp_comm hpath
  have hpositive := positiveCoefficient.intervalIntegral_comp_comm hpath
  have hpositiveIntegrable : IntervalIntegrable
      (fun s ↦ positiveCoefficient (path s)) volume a b :=
    ⟨positiveCoefficient.integrable_comp hpath.1,
      positiveCoefficient.integrable_comp hpath.2⟩
  have hconjugate := Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm
    hpositiveIntegrable
  change negativeCoefficient (∫ s in a..b, path s) =
    conj (positiveCoefficient (∫ s in a..b, path s))
  calc
    negativeCoefficient (∫ s in a..b, path s) =
        ∫ s in a..b, negativeCoefficient (path s) := hnegative.symm
    _ = ∫ s in a..b, conj (positiveCoefficient (path s)) := by
      apply intervalIntegral.integral_congr
      intro s _hs
      exact (isWeightedFourierReal_iff_native order (path s)).1 (hreal s) component k
    _ = conj (∫ s in a..b, positiveCoefficient (path s)) := hconjugate
    _ = conj (positiveCoefficient (∫ s in a..b, path s)) := by rw [hpositive]

/-! ## Actual real slices -/

/-- A complex scalar torus field fixed pointwise by conjugation has conjugate-symmetric Fourier
coefficients. -/
theorem mFourierCoeff_neg_eq_conj_of_pointwise
    (field : UnitAddTorus (Fin 3) → ℂ)
    (hreal : ∀ q, conj (field q) = field q)
    (k : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff field (-k) =
      conj (UnitAddTorus.mFourierCoeff field k) := by
  unfold UnitAddTorus.mFourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with q
  simp [UnitAddTorus.mFourier_neg, hreal q]

/-- Every coefficient population obtained from a real one-periodic Euclidean vector field has
the exact `-k`/conjugation incidence. -/
theorem vectorSpatialFourierCoeff_neg_eq_conj
    (field : Space → Space) (hcontinuous : Continuous field)
    (hperiodic : IsOnePeriodic field) (k : SpatialFrequency) (component : Fin 3) :
    vectorSpatialFourierCoeff field hcontinuous hperiodic (-k) component =
      conj
        (vectorSpatialFourierCoeff field hcontinuous hperiodic k component) := by
  rw [vectorSpatialFourierCoeff_apply, vectorSpatialFourierCoeff_apply]
  unfold torusSpatialFourierCoeff
  apply mFourierCoeff_neg_eq_conj_of_pointwise
  intro q
  simp [complexVelocityComponent, periodicTorusLift, periodicTorusLiftFunction]

/-- The actual native weighted `H³` state constructed from a smooth real periodic slice is real. -/
theorem isWeightedFourierReal_smoothSliceVectorWeightedH3
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u) :
    IsWeightedFourierReal 3 (smoothSliceVectorWeightedH3 u hu hperiodic) := by
  intro component k
  rw [unweighted_smoothSliceVectorWeightedH3_apply,
    unweighted_smoothSliceVectorWeightedH3_apply]
  exact vectorSpatialFourierCoeff_neg_eq_conj
    u hu.continuous hperiodic k component

/-- Every actual interior slice of an admitted open periodic solution enters the native restart
carrier with exact Fourier reality. -/
theorem openPeriodicSolutionOn_isWeightedFourierReal_slice
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    IsWeightedFourierReal 3
      (smoothSliceVectorWeightedH3 (fun x ↦ velocity x t)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution ht)
        (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩)) :=
  isWeightedFourierReal_smoothSliceVectorWeightedH3
    (fun x ↦ velocity x t)
    (openPeriodicSolutionOn_velocitySlice_contDiff solution ht)
    (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩)

/-! ## Heat transport -/

/-- Unweighting same-order native heat gives exactly the same real heat multiplier applied to the
unweighted source coefficient. -/
theorem unweighted_periodicWeightedHeat_apply
    (order : ℕ) (nu t : ℝ≥0) (state : PeriodicWeightedSobolev order)
    (k : SpatialFrequency) :
    (weightedSobolevCoefficients order
        (periodicWeightedHeat order nu t state)).1 k =
      (heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) *
        (weightedSobolevCoefficients order state).1 k := by
  change
    ((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) *
        ((heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) * state k)) =
      (heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) *
        ((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) * state k)
  ring

/-- Same-order native heat preserves exact Fourier reality. -/
theorem IsWeightedFourierReal.periodicVectorWeightedHeat
    {order : ℕ} {state : PeriodicVectorWeightedSobolev order}
    (hstate : IsWeightedFourierReal order state) (nu t : ℝ≥0) :
    IsWeightedFourierReal order (periodicVectorWeightedHeat order nu t state) := by
  intro component k
  change
    (weightedSobolevCoefficients order
        (periodicWeightedHeat order nu t (state component))).1 (-k) =
      conj ((weightedSobolevCoefficients order
        (periodicWeightedHeat order nu t (state component))).1 k)
  rw [unweighted_periodicWeightedHeat_apply,
    unweighted_periodicWeightedHeat_apply, heatStokesMultiplier_neg,
    hstate component k]
  simp

/-- Unweighting the one-derivative heat return likewise exposes the same heat multiplier and the
order-two physical source coefficient. -/
theorem unweighted_periodicWeightedHeatTwoToThree_apply
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ))
    (state : PeriodicWeightedSobolev 2) (k : SpatialFrequency) :
    (weightedSobolevCoefficients 3
        (periodicWeightedHeatTwoToThree nu t hviscous state)).1 k =
      (heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) *
        (weightedSobolevCoefficients 2 state).1 k := by
  change
    (weightedSobolevCoefficients 3
      (coefficientWeightedRealization 3
        (infiniteHeatPeriodicSobolevTwoIntoThree nu t hviscous
          (weightedSobolevCoefficients 2 state)))).1 k = _
  rw [weightedSobolevCoefficients_coefficientWeightedRealization]
  rfl

/-- The positive-time one-derivative heat return preserves Fourier reality across the change of
native Sobolev carrier. -/
theorem IsWeightedFourierReal.periodicVectorWeightedHeatTwoToThree
    {state : PeriodicVectorWeightedSobolev 2}
    (hstate : IsWeightedFourierReal 2 state)
    (nu t : ℝ≥0) (hviscous : 0 < (nu : ℝ) * (t : ℝ)) :
    IsWeightedFourierReal 3
      (periodicVectorWeightedHeatTwoToThree nu t hviscous state) := by
  intro component k
  change
    (weightedSobolevCoefficients 3
        (periodicWeightedHeatTwoToThree nu t hviscous (state component))).1 (-k) =
      conj ((weightedSobolevCoefficients 3
        (periodicWeightedHeatTwoToThree nu t hviscous (state component))).1 k)
  rw [unweighted_periodicWeightedHeatTwoToThree_apply,
    unweighted_periodicWeightedHeatTwoToThree_apply,
    heatStokesMultiplier_neg, hstate component k]
  simp

/-! ## Exact reindexing of the Leray divergence convolution -/

/-- Convolution of two conjugate-symmetric populations is conjugate-symmetric.  The proof keeps
the complete lattice population and reindexes it by the exact negation equivalence. -/
theorem tsum_convolution_neg_eq_conj
    (left right : SpatialFrequency → ℂ)
    (hleft : ∀ k, left (-k) = conj (left k))
    (hright : ∀ k, right (-k) = conj (right k))
    (k : SpatialFrequency) :
    (∑' p, left p * right (-k - p)) =
      conj (∑' p, left p * right (k - p)) := by
  calc
    (∑' p, left p * right (-k - p)) =
        ∑' q, left (-q) * right (-k - (-q)) := by
      rw [← (Equiv.neg SpatialFrequency).tsum_eq]
      rfl
    _ = ∑' q, conj (left q * right (k - q)) := by
      apply tsum_congr
      intro q
      rw [hleft q]
      have hfrequency : -k - -q = -(k - q) := by
        ext coordinate
        change -(k coordinate) - -(q coordinate) = -(k coordinate - q coordinate)
        ring
      rw [hfrequency, hright (k - q), map_mul]
    _ = conj (∑' q, left q * right (k - q)) := by
      rw [Complex.conj_tsum]

/-- The Fourier derivative symbol has exactly the same negation/conjugation incidence as a real
derivative. -/
theorem derivativeSymbol_neg_eq_conj (k : SpatialFrequency) (coordinate : Fin 3) :
    2 * (Real.pi : ℂ) * Complex.I * ((-k) coordinate : ℂ) =
      conj (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) := by
  have hcast : conj (k coordinate : ℂ) = (k coordinate : ℂ) := by
    rw [← Complex.ofReal_intCast, Complex.conj_ofReal]
  rw [map_mul, map_mul, map_mul, Complex.conj_ofNat,
    Complex.conj_ofReal, Complex.conj_I, hcast]
  simp only [Pi.neg_apply, Int.cast_neg]
  ring

/-- Before projection, the full divergence-form population preserves Fourier reality in every
output component. -/
theorem h3DivergenceConvolution_neg_eq_conj
    (advecting transported : PeriodicVectorSobolevThree)
    (hadvecting : ∀ component k,
      (advecting component).1 (-k) = conj ((advecting component).1 k))
    (htransported : ∀ component k,
      (transported component).1 (-k) = conj ((transported component).1 k))
    (output : Fin 3) (k : SpatialFrequency) :
    (h3DivergenceConvolution advecting transported output).1 (-k) =
      conj ((h3DivergenceConvolution advecting transported output).1 k) := by
  rw [h3DivergenceConvolution_apply, h3DivergenceConvolution_apply, map_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [tsum_convolution_neg_eq_conj
    (fun p ↦ (advecting coordinate).1 p)
    (fun p ↦ (transported output).1 p)
    (hadvecting coordinate) (htransported output) k,
    derivativeSymbol_neg_eq_conj, map_mul]
  simp only [map_mul]

/-- The embedded real frequency vector changes sign under frequency negation. -/
@[simp]
theorem complexFrequencyVector_neg (k : SpatialFrequency) :
    complexFrequencyVector (-k) = -complexFrequencyVector k := by
  funext component
  simp [complexFrequencyVector]

/-- Pairing a negated real frequency with a conjugated mode is the negative conjugate pairing. -/
theorem complexDot_frequencyNeg_conj
    (k : SpatialFrequency) (mode : ComplexVector) :
    complexDot (complexFrequencyVector (-k)) (fun component ↦ conj (mode component)) =
      -conj (complexDot (complexFrequencyVector k) mode) := by
  simp only [complexDot, dotProduct, complexFrequencyVector, Pi.neg_apply, Int.cast_neg,
    map_sum, map_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro component _
  simp

/-- The real-even Leray matrix commutes exactly with Fourier reality. -/
theorem lerayProjectMode_neg_conj
    (k : SpatialFrequency) (mode : ComplexVector) :
    lerayProjectMode (-k) (fun component ↦ conj (mode component)) =
      fun component ↦ conj (lerayProjectMode k mode component) := by
  by_cases hk : k = 0
  · subst k
    simp
  · have hneg : -k ≠ 0 := neg_ne_zero.mpr hk
    rw [lerayProjectMode, if_neg hneg, lerayProjectMode, if_neg hk]
    funext output
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul]
    rw [complexDot_frequencyNeg_conj, frequencySquared_neg]
    simp [complexFrequencyVector]
    ring

/-- Leray projection of the complete divergence population remains Fourier real. -/
theorem lerayProjectedH3DivergenceConvolution_neg_eq_conj
    (advecting transported : PeriodicVectorSobolevThree)
    (hadvecting : ∀ component k,
      (advecting component).1 (-k) = conj ((advecting component).1 k))
    (htransported : ∀ component k,
      (transported component).1 (-k) = conj ((transported component).1 k))
    (output : Fin 3) (k : SpatialFrequency) :
    (lerayProjectedH3DivergenceConvolution advecting transported output).1 (-k) =
      conj ((lerayProjectedH3DivergenceConvolution advecting transported output).1 k) := by
  change
    lerayProjectMode (-k)
        (fun component ↦
          (h3DivergenceConvolution advecting transported component).1 (-k)) output =
      conj (lerayProjectMode k
        (fun component ↦
          (h3DivergenceConvolution advecting transported component).1 k) output)
  have hmode :
      (fun component ↦
        (h3DivergenceConvolution advecting transported component).1 (-k)) =
      fun component ↦
        conj ((h3DivergenceConvolution advecting transported component).1 k) := by
    funext component
    exact h3DivergenceConvolution_neg_eq_conj
      advecting transported hadvecting htransported component k
  rw [hmode, lerayProjectMode_neg_conj]

/-! ## Native Leray and Duhamel preservation -/

/-- Removing the output weight from the native Leray passage returns exactly the complete
coefficient-level Leray population used to construct it. -/
theorem unweighted_weightedLerayDivergenceConvolution_apply
    (advecting transported : PeriodicVectorWeightedSobolev 3)
    (output : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients 2
        (weightedLerayDivergenceConvolution advecting transported output)).1 k =
      (lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree advecting)
        (unweightedVectorThree transported) output).1 k := by
  change
    (weightedSobolevCoefficients 2
      (coefficientWeightedRealization 2
        (lerayProjectedH3DivergenceConvolution
          (unweightedVectorThree advecting)
          (unweightedVectorThree transported) output))).1 k = _
  rw [weightedSobolevCoefficients_coefficientWeightedRealization]

/-- The exact complete native Leray divergence convolution preserves Fourier reality in both
incoming arguments. -/
theorem IsWeightedFourierReal.weightedLerayDivergenceConvolution
    {advecting transported : PeriodicVectorWeightedSobolev 3}
    (hadvecting : IsWeightedFourierReal 3 advecting)
    (htransported : IsWeightedFourierReal 3 transported) :
    IsWeightedFourierReal 2
      (weightedLerayDivergenceConvolution advecting transported) := by
  intro output k
  rw [unweighted_weightedLerayDivergenceConvolution_apply,
    unweighted_weightedLerayDivergenceConvolution_apply]
  apply lerayProjectedH3DivergenceConvolution_neg_eq_conj
  · intro component q
    exact hadvecting component q
  · intro component q
    exact htransported component q

/-- In particular, the native quadratic Leray source of a real state is real. -/
theorem IsWeightedFourierReal.weightedLerayQuadratic
    {state : PeriodicVectorWeightedSobolev 3}
    (hstate : IsWeightedFourierReal 3 state) :
    IsWeightedFourierReal 2 (weightedLerayQuadratic state) := by
  rw [weightedLerayQuadratic_apply]
  exact hstate.weightedLerayDivergenceConvolution hstate

/-- The endpoint-totalized positive-time Duhamel integrand preserves exact Fourier reality for
every real input path.  The strict branch composes the real quadratic source with one-derivative
heat; the terminal and exterior branch is the real zero population. -/
theorem isWeightedFourierReal_weightedDuhamelIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (u : ℝ → PeriodicVectorWeightedSobolev 3)
    (hu : ∀ s, IsWeightedFourierReal 3 (u s)) (s : ℝ) :
    IsWeightedFourierReal 3 (weightedDuhamelIntegrand nu hnu t u s) := by
  by_cases hs : s < t
  · rw [weightedDuhamelIntegrand_of_lt nu hnu t u hs]
    exact (hu s).weightedLerayQuadratic.periodicVectorWeightedHeatTwoToThree
      nu (positiveElapsed t s hs) (mul_pos hnu (sub_pos.mpr hs))
  · rw [weightedDuhamelIntegrand_of_not_lt nu hnu t u hs]
    exact isWeightedFourierReal_zero 3

section Audit

#print axioms vectorSpatialFourierCoeff_neg_eq_conj
#print axioms isWeightedFourierReal_smoothSliceVectorWeightedH3
#print axioms openPeriodicSolutionOn_isWeightedFourierReal_slice
#print axioms isClosed_setOf_isWeightedFourierReal
#print axioms isWeightedFourierReal_intervalIntegral
#print axioms IsWeightedFourierReal.periodicVectorWeightedHeat
#print axioms IsWeightedFourierReal.periodicVectorWeightedHeatTwoToThree
#print axioms IsWeightedFourierReal.weightedLerayDivergenceConvolution
#print axioms isWeightedFourierReal_weightedDuhamelIntegrand

end Audit


end Soma.Holonics.Millennium.NavierStokesWeightedReality
