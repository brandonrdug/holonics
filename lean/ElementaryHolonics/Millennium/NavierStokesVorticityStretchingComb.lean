import ElementaryHolonics.Millennium.NavierStokesCriticalVorticityRate
import ElementaryHolonics.Millennium.NavierStokesFrequencyComb
import ElementaryHolonics.Millennium.NavierStokesIntegralEnstrophy
import ElementaryHolonics.Millennium.NavierStokesVorticityThreeStrands

/-!
# From the vorticity stretching strand to the logarithmic frequency comb

This module joins three existing owners without replacing any of them:

* the exact periodic vorticity-energy balance;
* the pointwise operator-norm control of vortex stretching;
* the balanced low/middle/high scalar frequency comb.

The primary field remains the actual vorticity.  Enstrophy is only the scalar receiver obtained by
integrating its squared norm.  A concrete augmented order-three derivative receiver is installed
so the logarithmic law is no longer phrased in terms of an arbitrary `H`.

Two analytic attachments remain visible.  The Fourier/Hodge owner must realize the three band
bounds for the actual periodic velocity Jacobian, and the differentiated Navier--Stokes equation
must prove the order-three production estimate.  Neither attachment is replaced by an assumption
of the final logarithmic differential inequality.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Real Set
open scoped BigOperators Interval Laplacian

namespace Soma.Holonics.Millennium.NavierStokesVorticityStretchingComb

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalContinuation
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesFrequencyComb
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityThreeStrands

/-! ## The actual order-three receiver -/

/-- Sum of the squared operator norms of spatial derivatives of orders zero through three, each
integrated over one periodic cube.  This is a concrete order-three derivative receiver; no theorem
in this module claims norm equivalence with a library Sobolev-space construction. -/
def periodicH3DerivativeEnergy (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 4,
    ∫ x in unitCube,
      ‖iteratedFDeriv ℝ n (fun y => velocity y t) x‖ ^ 2

/-- The logarithmic chart is kept uniformly away from zero by adjoining `exp 1`. -/
def periodicLogH3Receiver (velocity : VelocityField) (t : ℝ) : ℝ :=
  Real.exp 1 + periodicH3DerivativeEnergy velocity t

/-- Every derivative-square population in the order-three receiver is integrable on an interior
slice of an open smooth solution. -/
theorem openPeriodicSolutionOn_h3Derivative_integrable
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (order : ℕ) :
    IntegrableOn
      (fun x => ‖iteratedFDeriv ℝ order (fun y => velocity y t) x‖ ^ 2)
      unitCube := by
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hsmooth : ContDiff ℝ ∞ (fun x => velocity x t) := by
    rw [← contDiffOn_univ]
    exact solution.velocitySmooth.comp
      (contDiffOn_id.prodMk contDiffOn_const) (by
        intro x _hx
        exact ⟨Set.mem_univ x, ht.1.le, ht.2⟩)
  have hcontinuous : Continuous
      (fun x => ‖iteratedFDeriv ℝ order (fun y => velocity y t) x‖ ^ 2) :=
    (hsmooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.pow 2
  exact hcontinuous.continuousOn.integrableOn_compact hcubeCompact

/-- The finite sum of derivative-square populations is nonnegative. -/
theorem periodicH3DerivativeEnergy_nonneg (velocity : VelocityField) (t : ℝ) :
    0 ≤ periodicH3DerivativeEnergy velocity t := by
  unfold periodicH3DerivativeEnergy
  apply Finset.sum_nonneg
  intro order _horder
  apply integral_nonneg_of_ae
  filter_upwards with x
  exact sq_nonneg _

/-- The augmented order-three receiver dominates its logarithmic base point. -/
theorem exp_one_le_periodicLogH3Receiver (velocity : VelocityField) (t : ℝ) :
    Real.exp 1 ≤ periodicLogH3Receiver velocity t := by
  unfold periodicLogH3Receiver
  exact le_add_of_nonneg_right (periodicH3DerivativeEnergy_nonneg velocity t)

/-- In particular the continuation receiver is at least one. -/
theorem one_le_periodicLogH3Receiver (velocity : VelocityField) (t : ℝ) :
    1 ≤ periodicLogH3Receiver velocity t :=
  (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans
    (exp_one_le_periodicLogH3Receiver velocity t)

/-- The chosen augmentation makes the natural logarithm at least one. -/
theorem one_le_log_periodicLogH3Receiver (velocity : VelocityField) (t : ℝ) :
    1 ≤ Real.log (periodicLogH3Receiver velocity t) := by
  calc
    1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (periodicLogH3Receiver velocity t) :=
      Real.log_le_log (Real.exp_pos 1)
        (exp_one_le_periodicLogH3Receiver velocity t)

/-! ## The exact integrated stretching bound on an open lifespan -/

/-- A spatial operator-norm envelope bounds the complete signed stretching integral by twice the
envelope times the enstrophy receiver.  The proof restricts the open world-tube only to an
addressed compact slab beyond the queried time. -/
theorem openPeriodicSolutionOn_vortexStretching_le_jacobianEnvelope
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t K : ℝ} (ht : t ∈ Ioo 0 T)
    (hK : ∀ x ∈ unitCube,
      ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ K) :
    periodicVortexStretching velocity t ≤
      2 * K * periodicEnstrophy velocity t := by
  let S : ℝ := (t + T) / 2
  have hSpos : 0 < S := by
    dsimp [S]
    linarith [ht.1, ht.2]
  have htS : t < S := by
    dsimp [S]
    linarith [ht.2]
  have hST : S < T := by
    dsimp [S]
    linarith [ht.2]
  let closed := solution.toClosedInterior hSpos hST
  exact periodicSolutionOn_vortexStretching_le_two_mul_jacobianBound_mul_enstrophy
    closed ht.1 htS K hK

/-! ## Low, middle, and high frequency testimony -/

/-- Time-indexed analytic testimony that the actual spatial Jacobian envelope is assembled from
three frequency bands.  `low`, `middle`, and `high` remain explicit so a future Fourier/Hodge
owner must fill each band rather than postulate the final logarithmic estimate. -/
structure OpenH3FrequencyComb
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (a : ℝ) (jacobian low middle high : ℝ → ℝ) : Prop where
  jacobian_envelope : ∀ t ∈ Ico a T, ∀ x ∈ unitCube,
    ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ jacobian t
  threeBands : ∀ t ∈ Ico a T,
    ThreeBandCombBound
      (jacobian t) (low t) (middle t) (high t) 1
      (criticalVorticityRate solution t) (periodicLogH3Receiver velocity t)
      (shellDepth (periodicLogH3Receiver velocity t))

/-- The explicit dyadic balance bounds the actual Jacobian envelope by its unit low-frequency
face, one critical-vorticity payment per middle shell, and the balanced high tail. -/
theorem OpenH3FrequencyComb.jacobian_le_balancedBands
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {jacobian low middle high : ℝ → ℝ}
    (comb : OpenH3FrequencyComb solution a jacobian low middle high)
    {t : ℝ} (ht : t ∈ Ico a T) :
    jacobian t ≤
      2 + (Real.logb 2 (periodicLogH3Receiver velocity t) + 1) *
        criticalVorticityRate solution t := by
  exact (comb.threeBands t ht).logarithmic_bound_of_low_le_one
    (one_le_periodicLogH3Receiver velocity t)

/-- A fixed base-conversion constant sufficient to turn the dyadic logarithm and the two unit
faces into the natural-logarithm chart used by logarithmic Grönwall. -/
def combLogConstant : ℝ := 3 + (Real.log 2)⁻¹

theorem combLogConstant_nonneg : 0 ≤ combLogConstant := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold combLogConstant
  positivity

/-- The balanced comb in natural-logarithm form.  The low-frequency constant and dyadic
base-change are both retained in `combLogConstant`; the time-varying coefficient is exactly the
augmented genuine torus-vorticity receiver. -/
theorem OpenH3FrequencyComb.jacobian_le_logarithmicH3
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {jacobian low middle high : ℝ → ℝ}
    (comb : OpenH3FrequencyComb solution a jacobian low middle high)
    {t : ℝ} (ht : t ∈ Ico a T) :
    jacobian t ≤
      combLogConstant * augmentedCriticalVorticityRate solution t *
        Real.log (periodicLogH3Receiver velocity t) := by
  let H : ℝ := periodicLogH3Receiver velocity t
  let critical : ℝ := criticalVorticityRate solution t
  let q : ℝ := (Real.log 2)⁻¹
  have hraw := comb.jacobian_le_balancedBands ht
  have hcritical : 0 ≤ critical := criticalVorticityRate_nonneg solution t
  have hlog : 1 ≤ Real.log H := one_le_log_periodicLogH3Receiver velocity t
  have hq : 0 ≤ q := by
    dsimp [q]
    exact inv_nonneg.mpr (Real.log_pos (by norm_num)).le
  have hlogb : Real.logb 2 H + 1 ≤ (q + 1) * Real.log H := by
    rw [Real.logb, div_eq_mul_inv]
    dsimp [q]
    nlinarith
  have hmiddle :
      (Real.logb 2 H + 1) * critical ≤
        ((q + 1) * Real.log H) * critical :=
    mul_le_mul_of_nonneg_right hlogb hcritical
  have hconstant : 2 ≤ (q + 3) * Real.log H := by
    have hthree : (3 : ℝ) ≤ q + 3 := by linarith
    have hthreeLog : (3 : ℝ) * 1 ≤ (q + 3) * Real.log H :=
      mul_le_mul hthree hlog (by norm_num) (by linarith)
    norm_num at hthreeLog
    exact (by norm_num : (2 : ℝ) ≤ 3).trans hthreeLog
  have hcriticalTerm :
      ((q + 1) * Real.log H) * critical ≤
        ((q + 3) * Real.log H) * critical := by
    apply mul_le_mul_of_nonneg_right _ hcritical
    apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ Real.log H)
    linarith
  have hfinal :
      jacobian t ≤ (q + 3) * (1 + critical) * Real.log H := by
    calc
      jacobian t ≤ 2 + (Real.logb 2 H + 1) * critical := hraw
      _ ≤ 2 + ((q + 1) * Real.log H) * critical :=
        add_le_add (le_refl 2) hmiddle
      _ ≤ (q + 3) * Real.log H +
            ((q + 3) * Real.log H) * critical :=
        add_le_add hconstant hcriticalTerm
      _ = (q + 3) * (1 + critical) * Real.log H := by ring
  simpa [combLogConstant, augmentedCriticalVorticityRate, H, critical, q, add_comm]
    using hfinal

/-- Substitution of the balanced frequency comb into the integrated stretching estimate.  This is
the strongest field-level stretching return available from the present owners. -/
theorem OpenH3FrequencyComb.vortexStretching_le_logarithmicH3
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {jacobian low middle high : ℝ → ℝ}
    (comb : OpenH3FrequencyComb solution a jacobian low middle high)
    (ha : 0 < a) {t : ℝ} (ht : t ∈ Ico a T) :
    periodicVortexStretching velocity t ≤
      2 * (combLogConstant * augmentedCriticalVorticityRate solution t *
        Real.log (periodicLogH3Receiver velocity t)) *
          periodicEnstrophy velocity t := by
  have htInterior : t ∈ Ioo 0 T := ⟨lt_of_lt_of_le ha ht.1, ht.2⟩
  have hstretch := openPeriodicSolutionOn_vortexStretching_le_jacobianEnvelope
    solution htInterior (comb.jacobian_envelope t ht)
  have hjacobian := comb.jacobian_le_logarithmicH3 ht
  have henergy : 0 ≤ 2 * periodicEnstrophy velocity t :=
    mul_nonneg (by norm_num) (periodicEnstrophy_nonneg_receiver velocity t)
  calc
    periodicVortexStretching velocity t ≤
        2 * jacobian t * periodicEnstrophy velocity t := hstretch
    _ = jacobian t * (2 * periodicEnstrophy velocity t) := by ring
    _ ≤ (combLogConstant * augmentedCriticalVorticityRate solution t *
          Real.log (periodicLogH3Receiver velocity t)) *
        (2 * periodicEnstrophy velocity t) :=
      mul_le_mul_of_nonneg_right hjacobian henergy
    _ = 2 * (combLogConstant * augmentedCriticalVorticityRate solution t *
          Real.log (periodicLogH3Receiver velocity t)) *
        periodicEnstrophy velocity t := by ring

/-- Returning through the exact unforced three-strand identity, transport has already cancelled,
diffusion is nonpositive for nonnegative viscosity, and the comb-controlled stretching term bounds
the actual enstrophy derivative. -/
theorem OpenH3FrequencyComb.unforced_deriv_enstrophy_le_logarithmicH3
    {T a nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure}
    {jacobian low middle high : ℝ → ℝ}
    (comb : OpenH3FrequencyComb solution a jacobian low middle high)
    (ha : 0 < a) (hnu : 0 ≤ nu) {t : ℝ} (ht : t ∈ Ico a T) :
    deriv (periodicEnstrophy velocity) t ≤
      2 * (combLogConstant * augmentedCriticalVorticityRate solution t *
        Real.log (periodicLogH3Receiver velocity t)) *
          periodicEnstrophy velocity t := by
  have htInterior : t ∈ Ioo 0 T := ⟨lt_of_lt_of_le ha ht.1, ht.2⟩
  let S : ℝ := (t + T) / 2
  have hSpos : 0 < S := by
    dsimp [S]
    linarith [htInterior.1, htInterior.2]
  have htS : t < S := by
    dsimp [S]
    linarith [htInterior.2]
  have hST : S < T := by
    dsimp [S]
    linarith [htInterior.2]
  let closed := solution.toClosedInterior hSpos hST
  have hidentity := periodicSolutionOn_unforced_deriv_enstrophy_eq
    closed htInterior.1 htS
  have hdissipation := periodicSolutionOn_viscousVorticityDissipation_nonneg
    closed htInterior.1 htS hnu
  have hstretching := comb.vortexStretching_le_logarithmicH3 ha ht
  rw [hidentity]
  linarith

/-! ## The resulting order-three logarithmic differential law -/

/-- The coefficient produced by an order-three commutator constant and the balanced comb. -/
def h3CombCriticalRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (productionConstant : ℝ)
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : ℝ) : ℝ :=
  scaledAugmentedCriticalVorticityRate
    (productionConstant * combLogConstant) solution t

theorem h3CombAnalyticConstant_nonneg
    {productionConstant : ℝ} (hproductionConstant : 0 ≤ productionConstant) :
    0 ≤ productionConstant * combLogConstant :=
  mul_nonneg hproductionConstant combLogConstant_nonneg

/-- A differentiated order-three energy estimate against the actual Jacobian envelope, followed
by the explicit three-band comb, yields the logarithmic differential inequality.  The premise is
the standard local commutator-production estimate `H₃' ≤ C ‖∇u‖∞ H₃`, not the final
critical-vorticity inequality returned by the theorem. -/
theorem OpenH3FrequencyComb.h3Rate_le_logarithmic
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {jacobian low middle high H3Rate : ℝ → ℝ}
    (comb : OpenH3FrequencyComb solution a jacobian low middle high)
    {productionConstant : ℝ} (hproductionConstant : 0 ≤ productionConstant)
    {t : ℝ} (ht : t ∈ Ico a T)
    (hproduction : H3Rate t ≤ productionConstant * jacobian t *
      periodicLogH3Receiver velocity t) :
    H3Rate t ≤
      h3CombCriticalRate productionConstant solution t *
        periodicLogH3Receiver velocity t *
          Real.log (periodicLogH3Receiver velocity t) := by
  have hjacobian := comb.jacobian_le_logarithmicH3 ht
  have hreceiver : 0 ≤ periodicLogH3Receiver velocity t :=
    (one_le_periodicLogH3Receiver velocity t).trans' zero_le_one
  have hscaled :
      productionConstant * jacobian t * periodicLogH3Receiver velocity t ≤
        productionConstant *
            (combLogConstant * augmentedCriticalVorticityRate solution t *
              Real.log (periodicLogH3Receiver velocity t)) *
          periodicLogH3Receiver velocity t := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hjacobian hproductionConstant) hreceiver
  unfold h3CombCriticalRate
  unfold scaledAugmentedCriticalVorticityRate
  calc
    H3Rate t ≤ productionConstant * jacobian t *
        periodicLogH3Receiver velocity t := hproduction
    _ ≤ productionConstant *
          (combLogConstant * augmentedCriticalVorticityRate solution t *
            Real.log (periodicLogH3Receiver velocity t)) *
        periodicLogH3Receiver velocity t := hscaled
    _ = (productionConstant * combLogConstant *
          augmentedCriticalVorticityRate solution t) *
        periodicLogH3Receiver velocity t *
          Real.log (periodicLogH3Receiver velocity t) := by ring

/-- The actual order-three receiver and the decomposed low/middle/high plus commutator inputs form
the `LifespanLogarithmicHighOrderLaw` consumed by the continuation factorization. -/
def lifespanLogarithmicH3LawOfFrequencyComb
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {jacobian low middle high H3Rate : ℝ → ℝ}
    (ha : 0 < a) (haT : a < T)
    (comb : OpenH3FrequencyComb solution a jacobian low middle high)
    (productionConstant : ℝ) (hproductionConstant : 0 ≤ productionConstant)
    (hderiv : ∀ t ∈ Ico a T,
      HasDerivAt (periodicLogH3Receiver velocity) (H3Rate t) t)
    (hproduction : ∀ t ∈ Ico a T,
      H3Rate t ≤ productionConstant * jacobian t *
        periodicLogH3Receiver velocity t) :
    LifespanLogarithmicHighOrderLaw T a
      (periodicLogH3Receiver velocity) H3Rate
      (scaledAugmentedCriticalVorticityRate
        (productionConstant * combLogConstant) solution) :=
  lifespanLogarithmicLawOfScaledAugmentedCriticalVorticity
    (productionConstant * combLogConstant) solution ha haT hderiv
    (fun t _ht => one_le_periodicLogH3Receiver velocity t) (by
      intro t ht
      simpa [h3CombCriticalRate] using
        comb.h3Rate_le_logarithmic hproductionConstant ht (hproduction t ht))

section Audit

#print axioms openPeriodicSolutionOn_h3Derivative_integrable
#print axioms openPeriodicSolutionOn_vortexStretching_le_jacobianEnvelope
#print axioms OpenH3FrequencyComb.jacobian_le_logarithmicH3
#print axioms OpenH3FrequencyComb.vortexStretching_le_logarithmicH3
#print axioms OpenH3FrequencyComb.unforced_deriv_enstrophy_le_logarithmicH3
#print axioms OpenH3FrequencyComb.h3Rate_le_logarithmic
#print axioms h3CombAnalyticConstant_nonneg
#print axioms lifespanLogarithmicH3LawOfFrequencyComb

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityStretchingComb
