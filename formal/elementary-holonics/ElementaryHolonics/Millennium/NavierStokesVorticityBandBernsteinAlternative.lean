import ElementaryHolonics.Millennium.NavierStokesDissipationHodgeEnstrophy
import ElementaryHolonics.Millennium.NavierStokesCoordinateJacobianTailDecay
import ElementaryHolonics.Millennium.NavierStokesVorticityCanonicalCriticalBridge
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

/-!
# Finite-band Bernstein and the exact amplitude alternative

**[proved-derived; formal-checked]** A finite torus Fourier population obeys the exact
coefficient `L²` Bernstein estimate: its pointwise norm is at most the square root of its mode
count times the square root of its coefficient-square mass.  For an actual periodic vorticity
slice, subtracting this finite band gives an exact low/high alternative at every receiver point.
Compactness supplies a point attaining the critical vorticity amplitude, so the same alternative
holds at the actual supremum.

This module does not identify the algebraic high remainder with a heat-decayed population.  Such
an identification requires an actual backward mild/heat passage and retains the nonlinear
Duhamel source; the finite-band theorem alone supplies no amplitude-to-time law.
-/

noncomputable section

open ContDiff MeasureTheory Real Set
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesVorticityBandBernsteinAlternative

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianMatrixBridge
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
open Soma.Holonics.Millennium.NavierStokesDissipationHodgeEnstrophy
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTranslationDissipation
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalCriticalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

/- Keep the probability-Haar chart used by the Fourier source owners. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Finite-band coefficient `L²` Bernstein -/

/-- **[proved-derived; formal-checked]** The pointwise norm of any finite torus synthesis is
bounded by square-root mode count times its exact coefficient `L²` mass. -/
theorem norm_finiteFourierSynthesis_le_sqrt_card_mul_sqrt_sum_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (coeff : SpatialFrequency → E) (modes : Finset SpatialFrequency)
    (q : SpatialTorus) :
    ‖finiteFourierSynthesis coeff modes q‖ ≤
      Real.sqrt (modes.card : ℝ) *
        Real.sqrt (∑ k ∈ modes, ‖coeff k‖ ^ 2) := by
  let coefficientNorm : SpatialFrequency → ℝ := fun k ↦ ‖coeff k‖
  have htriangle :
      ‖finiteFourierSynthesis coeff modes q‖ ≤
        ∑ k ∈ modes, coefficientNorm k := by
    simpa [coefficientNorm] using
      norm_finiteFourierSynthesis_le_sum_norm coeff modes q
  have hsumNonneg : 0 ≤ ∑ k ∈ modes, coefficientNorm k :=
    Finset.sum_nonneg fun k _hk ↦ norm_nonneg _
  have hsquare :
      (∑ k ∈ modes, coefficientNorm k) ^ 2 ≤
        (modes.card : ℝ) * ∑ k ∈ modes, coefficientNorm k ^ 2 := by
    exact sq_sum_le_card_mul_sum_sq
  calc
    ‖finiteFourierSynthesis coeff modes q‖ ≤
        ∑ k ∈ modes, coefficientNorm k := htriangle
    _ = Real.sqrt ((∑ k ∈ modes, coefficientNorm k) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsumNonneg]
    _ ≤ Real.sqrt
        ((modes.card : ℝ) * ∑ k ∈ modes, coefficientNorm k ^ 2) :=
      Real.sqrt_le_sqrt hsquare
    _ = Real.sqrt (modes.card : ℝ) *
        Real.sqrt (∑ k ∈ modes, coefficientNorm k ^ 2) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg modes.card)]
    _ = Real.sqrt (modes.card : ℝ) *
        Real.sqrt (∑ k ∈ modes, ‖coeff k‖ ^ 2) := by
      rfl

/-- The actual vorticity-band specialization retains the literal coefficient population. -/
theorem norm_openPeriodicVorticityBandProjector_le_sqrt_card_mul_sqrt_sum_sq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) (q : SpatialTorus) :
    ‖openPeriodicVorticityBandProjector solution t modes q‖ ≤
      Real.sqrt (modes.card : ℝ) *
        Real.sqrt (∑ k ∈ modes,
          ‖openPeriodicVorticityFourierMode solution t k‖ ^ 2) :=
  norm_finiteFourierSynthesis_le_sqrt_card_mul_sqrt_sum_sq _ _ _

/-- The cube specialization exposes the exact `(2 radius + 1)^3` population. -/
theorem norm_openPeriodicVorticityCubeProjector_le_sqrt_modeCount_mul_sqrt_sum_sq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) (q : SpatialTorus) :
    ‖openPeriodicVorticityBandProjector solution t (frequencyCube radius) q‖ ≤
      Real.sqrt (((2 * radius + 1) ^ 3 : ℕ) : ℝ) *
        Real.sqrt (∑ k ∈ frequencyCube radius,
          ‖openPeriodicVorticityFourierMode solution t k‖ ^ 2) := by
  simpa [card_frequencyCube] using
    norm_openPeriodicVorticityBandProjector_le_sqrt_card_mul_sqrt_sum_sq
      solution t (frequencyCube radius) q

/-! ## Parseval/enstrophy payment for the low branch -/

/-- The complete componentwise coefficient-square population of actual vorticity.  This is the
Hilbert `L²` population; it is deliberately distinct from the coordinate-sup norm used by finite
vector synthesis. -/
def openPeriodicVorticityCoefficientSquareMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) : ℝ :=
  ∑ component : Fin 3, ∑' k : SpatialFrequency,
    ‖openPeriodicVorticityFourierMode solution t k component‖ ^ 2

/-- The coordinate-sup square of a complex three-vector is bounded by its Hilbert coordinate
square population. -/
theorem norm_complexVector_sq_le_sum_norm_sq (v : ComplexVector) :
    ‖v‖ ^ 2 ≤ ∑ component : Fin 3, ‖v component‖ ^ 2 := by
  have hsum : 0 ≤ ∑ component : Fin 3, ‖v component‖ ^ 2 :=
    Finset.sum_nonneg fun component _ ↦ sq_nonneg ‖v component‖
  have hnorm : ‖v‖ ≤ Real.sqrt (∑ component : Fin 3, ‖v component‖ ^ 2) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro component
    rw [← Real.sqrt_sq (norm_nonneg (v component))]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum
      (fun component' _ ↦ sq_nonneg ‖v component'‖) (Finset.mem_univ component))
  nlinarith [norm_nonneg v, Real.sqrt_nonneg
    (∑ component : Fin 3, ‖v component‖ ^ 2), Real.sq_sqrt hsum]

/-- **[proved-derived; formal-checked]** Componentwise torus Parseval identifies the complete
actual-vorticity coefficient-square population with twice the periodic enstrophy. -/
theorem openPeriodicVorticityCoefficientSquareMass_eq_two_enstrophy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    openPeriodicVorticityCoefficientSquareMass solution t =
      2 * periodicEnstrophy velocity t.1 := by
  let omega : InitialVelocity := fun x ↦ vorticityField velocity x t.1
  let homega : ContDiff ℝ ∞ omega :=
    openPeriodicSolutionOn_vorticitySlice_contDiff solution t
  let hperiodic : IsOnePeriodic omega :=
    openPeriodicSolutionOn_vorticityField_isOnePeriodic solution t.2
  have hparseval (component : Fin 3) :
      (∑' k : SpatialFrequency,
          ‖openPeriodicVorticityFourierMode solution t k component‖ ^ 2) =
        ∫ q : SpatialTorus,
          ‖smoothSliceComponentLift omega homega hperiodic component q‖ ^ 2 := by
    calc
      (∑' k : SpatialFrequency,
          ‖openPeriodicVorticityFourierMode solution t k component‖ ^ 2) =
          ∑' k : SpatialFrequency,
            ‖openPeriodicVorticityComponentFourierL2 solution t component k‖ ^ 2 := by
        apply tsum_congr
        intro k
        rw [openPeriodicVorticityComponentFourierL2_apply]
      _ = ∫ q : SpatialTorus,
          ‖smoothSliceComponentLift omega homega hperiodic component q‖ ^ 2 := by
        unfold openPeriodicVorticityComponentFourierL2
        exact (hasSum_sq_smoothSliceFourierL2
          omega homega hperiodic component).tsum_eq
  have hintegrable (component : Fin 3) : Integrable (fun q : SpatialTorus ↦
      ‖smoothSliceComponentLift omega homega hperiodic component q‖ ^ 2) :=
    continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          ‖smoothSliceComponentLift omega homega hperiodic component q‖ ^ 2
        continuous_toFun := by fun_prop }
  calc
    openPeriodicVorticityCoefficientSquareMass solution t =
        ∑ component : Fin 3, ∫ q : SpatialTorus,
          ‖smoothSliceComponentLift omega homega hperiodic component q‖ ^ 2 := by
      unfold openPeriodicVorticityCoefficientSquareMass
      apply Finset.sum_congr rfl
      intro component _hcomponent
      exact hparseval component
    _ = ∫ q : SpatialTorus, ∑ component : Fin 3,
          ‖smoothSliceComponentLift omega homega hperiodic component q‖ ^ 2 := by
      rw [integral_finsetSum Finset.univ]
      exact fun component _hcomponent ↦ hintegrable component
    _ = ∫ q : SpatialTorus, ‖torusVorticityEvolution solution t q‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with q
      rw [EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_congr rfl
      intro component _hcomponent
      simp [smoothSliceComponentLift, periodicTorusLift,
        periodicTorusLiftFunction, complexVelocityComponent, omega,
        torusVorticityEvolution, torusVorticityWorldTube,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = 2 * periodicEnstrophy velocity t.1 :=
      integral_norm_sq_torusVorticityEvolution_eq_two_enstrophy solution t

/-- Every finite actual-vorticity coefficient-square population is paid exactly by enstrophy. -/
theorem sum_sq_openPeriodicVorticityFourierMode_le_two_enstrophy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) :
    (∑ k ∈ modes, ‖openPeriodicVorticityFourierMode solution t k‖ ^ 2) ≤
      2 * periodicEnstrophy velocity t.1 := by
  have hsummable (component : Fin 3) : Summable (fun k : SpatialFrequency ↦
      ‖openPeriodicVorticityFourierMode solution t k component‖ ^ 2) := by
    have hcomponent : Summable (fun k : SpatialFrequency ↦
        ‖openPeriodicVorticityComponentFourierL2 solution t component k‖ ^ 2) := by
      unfold openPeriodicVorticityComponentFourierL2
      exact (hasSum_sq_smoothSliceFourierL2
        (fun x ↦ vorticityField velocity x t.1)
        (openPeriodicSolutionOn_vorticitySlice_contDiff solution t)
        (openPeriodicSolutionOn_vorticityField_isOnePeriodic solution t.2)
        component).summable
    simpa only [openPeriodicVorticityComponentFourierL2_apply] using hcomponent
  calc
    (∑ k ∈ modes, ‖openPeriodicVorticityFourierMode solution t k‖ ^ 2) ≤
        ∑ k ∈ modes, ∑ component : Fin 3,
          ‖openPeriodicVorticityFourierMode solution t k component‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k _hk
      exact norm_complexVector_sq_le_sum_norm_sq _
    _ = ∑ component : Fin 3, ∑ k ∈ modes,
          ‖openPeriodicVorticityFourierMode solution t k component‖ ^ 2 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ component : Fin 3, ∑' k : SpatialFrequency,
          ‖openPeriodicVorticityFourierMode solution t k component‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro component _hcomponent
      exact (hsummable component).sum_le_tsum modes
        (fun k _hk ↦ sq_nonneg ‖openPeriodicVorticityFourierMode solution t k component‖)
    _ = 2 * periodicEnstrophy velocity t.1 :=
      openPeriodicVorticityCoefficientSquareMass_eq_two_enstrophy solution t

/-- The low band obeys the exact square-root mode-count/enstrophy estimate. -/
theorem norm_openPeriodicVorticityBandProjector_le_sqrt_card_mul_sqrt_two_enstrophy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) (q : SpatialTorus) :
    ‖openPeriodicVorticityBandProjector solution t modes q‖ ≤
      Real.sqrt (modes.card : ℝ) *
        Real.sqrt (2 * periodicEnstrophy velocity t.1) := by
  refine (norm_openPeriodicVorticityBandProjector_le_sqrt_card_mul_sqrt_sum_sq
    solution t modes q).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt
      (sum_sq_openPeriodicVorticityFourierMode_le_two_enstrophy solution t modes))
    (Real.sqrt_nonneg _)

/-! ## Exact low/high alternative -/

/-- [definition] The exact remainder after subtracting a declared finite vorticity band. -/
def openPeriodicVorticityFrequencyRemainder
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) :
    C(SpatialTorus, ComplexVector) :=
  complexTorusVorticitySlice solution t -
    openPeriodicVorticityBandProjector solution t modes

/-- Curling a complex Jacobian costs at most the six signed source entries, hence at most six
times the entrywise supremum norm. -/
theorem norm_complexCurlFromJacobian_le_six_mul_norm
    (J : ComplexJacobianArray) :
    ‖complexCurlFromJacobian J‖ ≤ 6 * ‖J‖ := by
  refine (norm_complexVector_le_complexVectorL1 _).trans
    ((complexVectorL1_complexCurlFromJacobian_le J).trans ?_)
  unfold complexCurlEntryMass
  have h21 : ‖J 2 1‖ ≤ ‖J‖ :=
    (norm_le_pi_norm (J 2) 1).trans (norm_le_pi_norm J 2)
  have h12 : ‖J 1 2‖ ≤ ‖J‖ :=
    (norm_le_pi_norm (J 1) 2).trans (norm_le_pi_norm J 1)
  have h02 : ‖J 0 2‖ ≤ ‖J‖ :=
    (norm_le_pi_norm (J 0) 2).trans (norm_le_pi_norm J 0)
  have h20 : ‖J 2 0‖ ≤ ‖J‖ :=
    (norm_le_pi_norm (J 2) 0).trans (norm_le_pi_norm J 2)
  have h10 : ‖J 1 0‖ ≤ ‖J‖ :=
    (norm_le_pi_norm (J 1) 0).trans (norm_le_pi_norm J 1)
  have h01 : ‖J 0 1‖ ≤ ‖J‖ :=
    (norm_le_pi_norm (J 0) 1).trans (norm_le_pi_norm J 0)
  linarith

/-- The actual complex vorticity is literally the curl of the actual descended Jacobian array. -/
theorem complexTorusVorticitySlice_eq_complexCurl_jacobianArraySlice
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (q : SpatialTorus) :
    complexTorusVorticitySlice solution t q =
      complexCurlFromJacobian
        (openPeriodicTorusJacobianArraySlice solution t q) := by
  obtain ⟨x, rfl⟩ := euclideanToSpatialTorus_surjective q
  ext component
  fin_cases component <;>
    simp [complexTorusVorticitySlice, complexifySpace,
      complexCurlFromJacobian, vorticityField, vorticityAt,
      velocityJacobianAt, curlFromJacobian, jacobianMatrix_apply,
      spatialBasisVector]

/-- Curl commutes with the exact finite synthesis, so the vorticity band is the curl of the
matching Jacobian band. -/
theorem openPeriodicVorticityBandProjector_eq_complexCurl_jacobianBandProjector
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) (q : SpatialTorus) :
    openPeriodicVorticityBandProjector solution t modes q =
      complexCurlFromJacobian
        (openPeriodicJacobianBandProjector solution t modes q) := by
  ext component
  fin_cases component <;>
    simp [openPeriodicVorticityBandProjector,
      openPeriodicJacobianBandProjector, finiteFourierSynthesis,
      complexCurlFromJacobian, openPeriodicVorticityFourierMode_eq_complexCurl] <;>
    simp_rw [mul_sub] <;> rw [Finset.sum_sub_distrib]

/-- The exact vorticity remainder is the curl of the already reconstructed complementary
Jacobian tail. -/
theorem openPeriodicVorticityFrequencyRemainder_eq_complexCurl_jacobianArrayTail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) (q : SpatialTorus) :
    openPeriodicVorticityFrequencyRemainder solution t modes q =
      complexCurlFromJacobian
        (openPeriodicJacobianArrayFourierTail solution t modes q : ComplexMatrix3) := by
  unfold openPeriodicVorticityFrequencyRemainder
  change complexTorusVorticitySlice solution t q -
      openPeriodicVorticityBandProjector solution t modes q = _
  rw [complexTorusVorticitySlice_eq_complexCurl_jacobianArraySlice,
    openPeriodicVorticityBandProjector_eq_complexCurl_jacobianBandProjector,
    openPeriodicTorusJacobianArraySlice_eq_band_add_arrayTail
      solution t modes q]
  ext component
  fin_cases component <;>
    simp [complexCurlFromJacobian, Pi.add_apply, Pi.sub_apply] <;> ring

/-- Pointwise high-vorticity remainder is bounded by six times the exact nine-face Jacobian
coefficient-tail mass. -/
theorem norm_openPeriodicVorticityFrequencyRemainder_le_six_mul_jacobianTailMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) (q : SpatialTorus) :
    ‖openPeriodicVorticityFrequencyRemainder solution t modes q‖ ≤
      6 * openPeriodicJacobianCoefficientTailMass solution t modes := by
  rw [openPeriodicVorticityFrequencyRemainder_eq_complexCurl_jacobianArrayTail]
  exact (norm_complexCurlFromJacobian_le_six_mul_norm _).trans
    (mul_le_mul_of_nonneg_left
      (norm_openPeriodicJacobianArrayFourierTail_le solution t modes q) (by norm_num))

/-- **[proved-derived; formal-checked]** The high branch has an explicit strict-interior `H³`
price.  The decay is precisely the already proved Jacobian coefficient-tail scale; no terminal
uniformity or heat evolution is added. -/
theorem norm_openPeriodicVorticityFrequencyRemainder_frequencyCube_le_H3Tail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) (q : SpatialTorus) :
    ‖openPeriodicVorticityFrequencyRemainder solution t
        (frequencyCube radius) q‖ ≤
      6 * ((2 * Real.pi) *
        Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
          ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
            (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
            (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖) := by
  exact
    (norm_openPeriodicVorticityFrequencyRemainder_le_six_mul_jacobianTailMass
      solution t (frequencyCube radius) q).trans
      (mul_le_mul_of_nonneg_left
        (openPeriodicJacobianCoefficientTailMass_frequencyCube_le
          solution t radius) (by norm_num))

/-- The remainder has exactly the complementary Fourier coefficients.  Thus the second branch
of the alternative is spectrally high relative to `modes`, even though no pointwise infinite-tail
reconstruction or heat evolution is inferred from that fact. -/
theorem mFourierCoeff_openPeriodicVorticityFrequencyRemainder
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) (k : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (openPeriodicVorticityFrequencyRemainder solution t modes) k =
      if k ∈ modes then 0 else openPeriodicVorticityFourierMode solution t k := by
  unfold openPeriodicVorticityFrequencyRemainder
  rw [UnitAddTorus.mFourierCoeff]
  change (∫ q : SpatialTorus,
      UnitAddTorus.mFourier (-k) q •
        (complexTorusVorticitySlice solution t q -
          openPeriodicVorticityBandProjector solution t modes q)) = _
  simp_rw [smul_sub]
  rw [integral_sub]
  · rw [← UnitAddTorus.mFourierCoeff,
      ← UnitAddTorus.mFourierCoeff,
      ← openPeriodicVorticityFourierMode_eq_mFourierCoeff,
      mFourierCoeff_openPeriodicVorticityBandProjector]
    split <;> simp_all
  · exact continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          UnitAddTorus.mFourier (-k) q • complexTorusVorticitySlice solution t q
        continuous_toFun := by fun_prop }
  · exact continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          UnitAddTorus.mFourier (-k) q •
            openPeriodicVorticityBandProjector solution t modes q
        continuous_toFun := by fun_prop }

theorem complexTorusVorticitySlice_eq_band_add_frequencyRemainder
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) :
    complexTorusVorticitySlice solution t =
      openPeriodicVorticityBandProjector solution t modes +
        openPeriodicVorticityFrequencyRemainder solution t modes := by
  unfold openPeriodicVorticityFrequencyRemainder
  abel

/-- **[proved-derived; formal-checked]** At any receiver carrying amplitude `level`, either the
finite band or its exact remainder carries at least half that amplitude. -/
theorem half_level_le_band_or_half_level_le_frequencyRemainder
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) (q : SpatialTorus)
    {level : ℝ} (hlevel : level ≤ ‖complexTorusVorticitySlice solution t q‖) :
    level / 2 ≤ ‖openPeriodicVorticityBandProjector solution t modes q‖ ∨
      level / 2 ≤ ‖openPeriodicVorticityFrequencyRemainder solution t modes q‖ := by
  have hdecomposition := DFunLike.congr_fun
    (complexTorusVorticitySlice_eq_band_add_frequencyRemainder
      solution t modes) q
  have htriangle :
      ‖complexTorusVorticitySlice solution t q‖ ≤
        ‖openPeriodicVorticityBandProjector solution t modes q‖ +
          ‖openPeriodicVorticityFrequencyRemainder solution t modes q‖ := by
    rw [hdecomposition]
    exact norm_add_le _ _
  by_cases hlow :
      level / 2 ≤ ‖openPeriodicVorticityBandProjector solution t modes q‖
  · exact Or.inl hlow
  · right
    have hlowStrict :
        ‖openPeriodicVorticityBandProjector solution t modes q‖ < level / 2 :=
      lt_of_not_ge hlow
    nlinarith

/-- The low branch is discharged by the exact finite-band Bernstein receiver. -/
theorem half_level_le_bernstein_or_half_level_le_frequencyRemainder
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) (q : SpatialTorus)
    {level : ℝ} (hlevel : level ≤ ‖complexTorusVorticitySlice solution t q‖) :
    level / 2 ≤ Real.sqrt (modes.card : ℝ) *
        Real.sqrt (∑ k ∈ modes,
          ‖openPeriodicVorticityFourierMode solution t k‖ ^ 2) ∨
      level / 2 ≤ ‖openPeriodicVorticityFrequencyRemainder solution t modes q‖ := by
  rcases half_level_le_band_or_half_level_le_frequencyRemainder
      solution t modes q hlevel with hlow | hhigh
  · left
    exact hlow.trans
      (norm_openPeriodicVorticityBandProjector_le_sqrt_card_mul_sqrt_sum_sq
        solution t modes q)
  · exact Or.inr hhigh

/-! ## Alternative at an actual critical-amplitude point -/

/-- **[proved-derived; formal-checked]** Compactness of the spatial torus realizes the norm of
the actual vorticity slice at a receiver point. -/
theorem exists_norm_torusVorticityEvolution_eq_criticalVorticityRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    ∃ q : SpatialTorus,
      ‖torusVorticityEvolution solution t q‖ =
        criticalVorticityRate solution t.1 := by
  obtain ⟨q, _hq, hmax⟩ := isCompact_univ.exists_isMaxOn
    univ_nonempty
    (torusVorticityEvolution solution t).continuous.norm.continuousOn
  refine ⟨q, ?_⟩
  rw [criticalVorticityRate_eq solution t.2]
  apply le_antisymm
  · exact (torusVorticityEvolution solution t).norm_coe_le_norm q
  · apply (ContinuousMap.norm_le _
      (norm_nonneg (torusVorticityEvolution solution t q))).2
    intro q'
    exact hmax (mem_univ q')

/-- **[proved-derived; formal-checked]** At a point attaining the actual Euclidean critical
vorticity amplitude, either the declared finite band has enough coefficient `L²` mass or the exact
high remainder carries the missing amplitude.  The factor `sqrt 3` is the exact chart comparison
between the Euclidean norm and the coordinate-sup complex Fourier receiver used by this project. -/
theorem exists_criticalVorticityRate_le_bernstein_or_frequencyRemainder
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) :
    ∃ q : SpatialTorus,
      criticalVorticityRate solution t.1 / 2 ≤
          Real.sqrt 3 *
            (Real.sqrt (modes.card : ℝ) *
              Real.sqrt (∑ k ∈ modes,
                ‖openPeriodicVorticityFourierMode solution t k‖ ^ 2)) ∨
        criticalVorticityRate solution t.1 / 2 ≤
          Real.sqrt 3 *
            ‖openPeriodicVorticityFrequencyRemainder solution t modes q‖ := by
  obtain ⟨q, hq⟩ :=
    exists_norm_torusVorticityEvolution_eq_criticalVorticityRate solution t
  refine ⟨q, ?_⟩
  have hchart : criticalVorticityRate solution t.1 ≤
      Real.sqrt 3 * ‖complexTorusVorticitySlice solution t q‖ := by
    rw [← hq]
    exact norm_space_le_sqrt_three_mul_norm_complexifySpace _
  have hdecomposition := DFunLike.congr_fun
    (complexTorusVorticitySlice_eq_band_add_frequencyRemainder
      solution t modes) q
  have htriangle :
      ‖complexTorusVorticitySlice solution t q‖ ≤
        ‖openPeriodicVorticityBandProjector solution t modes q‖ +
          ‖openPeriodicVorticityFrequencyRemainder solution t modes q‖ := by
    rw [hdecomposition]
    exact norm_add_le _ _
  have hsqrt : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have htotal : criticalVorticityRate solution t.1 ≤
      Real.sqrt 3 * ‖openPeriodicVorticityBandProjector solution t modes q‖ +
        Real.sqrt 3 *
          ‖openPeriodicVorticityFrequencyRemainder solution t modes q‖ := by
    calc
      criticalVorticityRate solution t.1 ≤
          Real.sqrt 3 * ‖complexTorusVorticitySlice solution t q‖ := hchart
      _ ≤ Real.sqrt 3 *
          (‖openPeriodicVorticityBandProjector solution t modes q‖ +
            ‖openPeriodicVorticityFrequencyRemainder solution t modes q‖) :=
        mul_le_mul_of_nonneg_left htriangle hsqrt
      _ = _ := mul_add _ _ _
  by_cases hlow : criticalVorticityRate solution t.1 / 2 ≤
      Real.sqrt 3 * ‖openPeriodicVorticityBandProjector solution t modes q‖
  · left
    exact hlow.trans (mul_le_mul_of_nonneg_left
      (norm_openPeriodicVorticityBandProjector_le_sqrt_card_mul_sqrt_sum_sq
        solution t modes q) hsqrt)
  · right
    have hlowStrict :
        Real.sqrt 3 * ‖openPeriodicVorticityBandProjector solution t modes q‖ <
          criticalVorticityRate solution t.1 / 2 := lt_of_not_ge hlow
    nlinarith

/-- **[proved-derived; formal-checked]** Exact enstrophy/high-frequency dichotomy.  The low
branch has been squared after Parseval: if the high remainder does not carry half the amplitude
(up to the unavoidable `sqrt 3` chart factor), then `M² ≤ 24 · card · enstrophy`. -/
theorem exists_criticalVorticityRate_sq_le_card_mul_enstrophy_or_high
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) :
    ∃ q : SpatialTorus,
      criticalVorticityRate solution t.1 ^ 2 ≤
          24 * (modes.card : ℝ) * periodicEnstrophy velocity t.1 ∨
        criticalVorticityRate solution t.1 / 2 ≤
          Real.sqrt 3 *
            ‖openPeriodicVorticityFrequencyRemainder solution t modes q‖ := by
  obtain ⟨q, hlow | hhigh⟩ :=
    exists_criticalVorticityRate_le_bernstein_or_frequencyRemainder
      solution t modes
  · refine ⟨q, Or.inl ?_⟩
    have hmass :=
      sum_sq_openPeriodicVorticityFourierMode_le_two_enstrophy solution t modes
    have hlowEnstrophy : criticalVorticityRate solution t.1 / 2 ≤
        Real.sqrt 3 *
          (Real.sqrt (modes.card : ℝ) *
            Real.sqrt (2 * periodicEnstrophy velocity t.1)) := by
      exact hlow.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmass)
          (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    have hE : 0 ≤ 2 * periodicEnstrophy velocity t.1 := by
      rw [← openPeriodicVorticityCoefficientSquareMass_eq_two_enstrophy solution t]
      unfold openPeriodicVorticityCoefficientSquareMass
      exact Finset.sum_nonneg fun component _hcomponent ↦
        tsum_nonneg fun k ↦ sq_nonneg _
    have hleft : 0 ≤ criticalVorticityRate solution t.1 / 2 :=
      div_nonneg (criticalVorticityRate_nonneg solution t.1) (by norm_num)
    have hright : 0 ≤ Real.sqrt 3 *
        (Real.sqrt (modes.card : ℝ) *
          Real.sqrt (2 * periodicEnstrophy velocity t.1)) := by positivity
    have hsquare := (sq_le_sq₀ hleft hright).2 hlowEnstrophy
    rw [div_pow, mul_pow, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sq_sqrt (Nat.cast_nonneg modes.card), Real.sq_sqrt hE] at hsquare
    norm_num at hsquare ⊢
    nlinarith
  · exact ⟨q, Or.inr hhigh⟩

/-- Cube form of the same exact dichotomy, exposing the literal `(2 radius + 1)^3` mode count. -/
theorem exists_criticalVorticityRate_sq_le_cubeCount_mul_enstrophy_or_high
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) :
    ∃ q : SpatialTorus,
      criticalVorticityRate solution t.1 ^ 2 ≤
          24 * (((2 * radius + 1) ^ 3 : ℕ) : ℝ) *
            periodicEnstrophy velocity t.1 ∨
        criticalVorticityRate solution t.1 / 2 ≤
          Real.sqrt 3 *
            ‖openPeriodicVorticityFrequencyRemainder solution t
              (frequencyCube radius) q‖ := by
  simpa [card_frequencyCube] using
    exists_criticalVorticityRate_sq_le_card_mul_enstrophy_or_high
      solution t (frequencyCube radius)

/-- **[proved-derived; formal-checked]** Strongest current strict-interior amplitude/scale
tradeoff from the exact low branch and the existing weighted-`H³` coefficient tail.  The second
branch carries the explicit `sqrt (jacobianTailScale radius)` decay, but its `H³` norm has no
terminal-uniform bound here. -/
theorem exists_criticalVorticityRate_sq_le_cubeCount_mul_enstrophy_or_H3Tail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) :
    ∃ q : SpatialTorus,
      criticalVorticityRate solution t.1 ^ 2 ≤
          24 * (((2 * radius + 1) ^ 3 : ℕ) : ℝ) *
            periodicEnstrophy velocity t.1 ∨
        criticalVorticityRate solution t.1 / 2 ≤
          Real.sqrt 3 *
            (6 * ((2 * Real.pi) *
              Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
                ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
                  (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
                  (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖)) := by
  obtain ⟨q, hlow | hhigh⟩ :=
    exists_criticalVorticityRate_sq_le_cubeCount_mul_enstrophy_or_high
      solution t radius
  · exact ⟨q, Or.inl hlow⟩
  · refine ⟨q, Or.inr (hhigh.trans ?_)⟩
    exact mul_le_mul_of_nonneg_left
      (norm_openPeriodicVorticityFrequencyRemainder_frequencyCube_le_H3Tail
        solution t radius q) (Real.sqrt_nonneg 3)

#print axioms norm_finiteFourierSynthesis_le_sqrt_card_mul_sqrt_sum_sq
#print axioms openPeriodicVorticityCoefficientSquareMass_eq_two_enstrophy
#print axioms exists_criticalVorticityRate_sq_le_cubeCount_mul_enstrophy_or_high
#print axioms norm_openPeriodicVorticityFrequencyRemainder_frequencyCube_le_H3Tail
#print axioms exists_criticalVorticityRate_sq_le_cubeCount_mul_enstrophy_or_H3Tail
#print axioms exists_criticalVorticityRate_le_bernstein_or_frequencyRemainder

end Soma.Holonics.Millennium.NavierStokesVorticityBandBernsteinAlternative
