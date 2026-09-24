import ElementaryHolonics.Millennium.NavierStokesIncoherentSource
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import ElementaryHolonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration

/-!
# A source-backed periodic transverse shear

The field `A sin (2π x₀) e₁` is a concrete periodic divergence-free shear.  Its velocity is
parallel to `e₁`, while its only spatial dependence is in `x₀`; hence its actual spatial
advection `Du(u)` is zero.  This is a source class for testing the coherence-defect route: it
has no nonlinear Fourier source, but viscosity still imposes the scalar heat law
`A' = -ν (2π)² A`.

The scalar residual is derived from the actual spatial function, including its Laplacian.
The explicit decaying amplitude constructs a complete unforced `PeriodicSolution`, and its
restriction instantiates the actual coherence-defect receiver with zero defect.
-/

noncomputable section

open ContDiff Set Filter Topology MeasureTheory
open scoped BigOperators Laplacian

namespace Soma.Holonics.Millennium.NavierStokesShearAnsatz

open InnerProductSpace

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesIncoherentSource
open Soma.Holonics.Millennium.NavierStokesShellStepCost
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy

/-! ## The explicit shear -/

def shearVelocity (amplitude : ℝ) : InitialVelocity :=
  fun x ↦ (amplitude * Real.sin (2 * Real.pi * x 0)) •
    EuclideanSpace.single (1 : Fin 3) 1

/-- The amplitude is retained by a concrete spatial receiver. -/
theorem shearVelocity_amplitude_receiver (amplitude : ℝ) :
    shearVelocity amplitude (EuclideanSpace.single 0 (1 / 4)) 1 = amplitude := by
  simp [shearVelocity, show 2 * Real.pi * (4 : ℝ)⁻¹ = Real.pi / 2 by ring]

theorem shearVelocity_contDiff (amplitude : ℝ) :
    ContDiff ℝ ∞ (shearVelocity amplitude) := by
  have hcoord : ContDiff ℝ ∞ (fun x : Space ↦ x 0) := by
    simpa only [id_eq] using ((contDiff_piLp 2).mp (contDiff_id (𝕜 := ℝ)) 0)
  exact (contDiff_const.mul ((contDiff_const.mul hcoord).sin)).smul
      contDiff_const

/-- A one-coordinate source has the literal one-dimensional second derivative as its Laplacian.
The incoming coordinate directions are retained through the multilinear chain rule. -/
theorem laplacian_firstCoordinate (g : ℝ → Space) (hg : ContDiff ℝ 2 g) (x : Space) :
    Δ (fun y : Space ↦ g (y 0)) x = iteratedDeriv 2 g (x 0) := by
  have hfun : (fun y : Space ↦ g (y 0)) = g ∘ (EuclideanSpace.proj (0 : Fin 3)) := rfl
  rw [hfun, laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  have hchain := (EuclideanSpace.proj (0 : Fin 3)).iteratedFDeriv_comp_right hg x
    (i := 2) (by norm_num)
  simp_rw [hchain, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  simp [EuclideanSpace.basisFun_apply, Fin.prod_univ_succ]

/-- The sine shear's viscous eigenrelation is derived from its actual spatial function. -/
theorem laplacian_shearVelocity (amplitude : ℝ) :
    Δ (shearVelocity amplitude) = (-(2 * Real.pi) ^ 2) • shearVelocity amplitude := by
  let g : ℝ → Space := fun r ↦ (amplitude * Real.sin (2 * Real.pi * r)) •
    EuclideanSpace.single (1 : Fin 3) 1
  have hg : ContDiff ℝ 2 g := by dsimp [g]; fun_prop
  funext x
  have hl := laplacian_firstCoordinate g hg x
  change Δ (fun y : Space ↦ g (y 0)) x = _
  rw [hl]
  unfold g
  rw [iteratedDeriv_smul_const (by fun_prop),
    iteratedDeriv_const_mul amplitude (by fun_prop),
    iteratedDeriv_comp_const_mul Real.contDiff_sin]
  simp [iteratedDeriv_succ, Real.deriv_sin, Real.deriv_cos, shearVelocity, smul_smul,
    mul_assoc, mul_comm, mul_left_comm]

theorem shearVelocity_isOnePeriodic (amplitude : ℝ) :
    IsOnePeriodic (shearVelocity amplitude) := by
  intro x i
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [shearVelocity, Real.sin_add, add_comm, mul_add]

theorem shearVelocity_invariant_along_transverse
    (amplitude : ℝ) (x : Space) (s : ℝ) :
    shearVelocity amplitude (x + s • EuclideanSpace.single (1 : Fin 3) 1) =
      shearVelocity amplitude x := by
  ext j
  fin_cases j <;> simp [shearVelocity]

theorem fderiv_shearVelocity_apply_transverse
    (amplitude : ℝ) (x : Space) :
    fderiv ℝ (shearVelocity amplitude) x
      (EuclideanSpace.single (1 : Fin 3) 1) = 0 := by
  have hline : HasDerivAt
      (fun s : ℝ ↦ shearVelocity amplitude
        (x + s • EuclideanSpace.single (1 : Fin 3) 1)) 0 0 := by
    have hfun : (fun s : ℝ ↦ shearVelocity amplitude
        (x + s • EuclideanSpace.single (1 : Fin 3) 1)) =
        (fun _ : ℝ ↦ shearVelocity amplitude x) := by
      funext s
      exact shearVelocity_invariant_along_transverse amplitude x s
    rw [hfun]
    exact hasDerivAt_const _ _
  have hbase : HasFDerivAt (shearVelocity amplitude)
      (fderiv ℝ (shearVelocity amplitude) x) x :=
    (((shearVelocity_contDiff amplitude).differentiable (by simp)).differentiableAt).hasFDerivAt
  have hpath : HasDerivAt
      (fun s : ℝ ↦ x + s • EuclideanSpace.single (1 : Fin 3) 1)
      (EuclideanSpace.single (1 : Fin 3) 1) 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) 0).smul_const
      (EuclideanSpace.single (1 : Fin 3) 1) |>.const_add x
  have hbase' : HasFDerivAt (shearVelocity amplitude)
      (fderiv ℝ (shearVelocity amplitude) x)
      (x + (0 : ℝ) • EuclideanSpace.single (1 : Fin 3) 1) := by
    simpa using hbase
  have hcomp := hbase'.comp_hasDerivAt 0 hpath
  have hderiv :
      (fderiv ℝ (shearVelocity amplitude) x)
          (EuclideanSpace.single (1 : Fin 3) 1) =
        deriv (fun s : ℝ ↦ shearVelocity amplitude
          (x + s • EuclideanSpace.single (1 : Fin 3) 1)) 0 := by
    simpa [Function.comp_def] using hcomp.deriv.symm
  exact hderiv.trans hline.deriv

theorem shearVelocity_actualAdvectionField (amplitude : ℝ) :
    actualAdvectionField (shearVelocity amplitude) = 0 := by
  funext x
  rw [actualAdvectionField]
  rw [show shearVelocity amplitude x =
      (amplitude * Real.sin (2 * Real.pi * x 0)) •
        EuclideanSpace.single (1 : Fin 3) 1 by rfl,
    map_smul, fderiv_shearVelocity_apply_transverse]
  simp

/-- The shear's Jacobian is the transverse rank-one map, so its actual trace vanishes. -/
theorem shearVelocity_divergence (amplitude : ℝ) (x : Space) :
    divergence (shearVelocity amplitude) x = 0 := by
  have hs := (((hasDerivAt_id (x 0)).const_mul (2 * Real.pi)).sin).const_mul amplitude
  have hv := hs.smul_const (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : Space)
  let proj : Space →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 3)
  have hcomp := hv.hasFDerivAt.comp x proj.hasFDerivAt
  have hderiv := hcomp.fderiv
  change fderiv ℝ (shearVelocity amplitude) x = _ at hderiv
  rw [divergence, hderiv]
  change LinearMap.trace ℝ Space
    ((EuclideanSpace.proj (0 : Fin 3)).toLinearMap.smulRight _) = 0
  rw [LinearMap.trace_smulRight]
  simp

theorem shearPressure_gradient (constant : ℝ) (x : Space) :
    gradient (fun _ : Space ↦ constant) x = 0 := by
  change gradient (Function.const Space constant) x = 0
  exact gradient_const x constant

/-! ## Fourier and coherence consequences -/

theorem shearVelocity_fourierActualAdvection_zero
    (amplitude : ℝ) (hu : ContDiff ℝ ∞ (shearVelocity amplitude))
    (hp : IsOnePeriodic (shearVelocity amplitude)) (k : SpatialFrequency) :
    vectorSpatialFourierCoeff (actualAdvectionField (shearVelocity amplitude))
        (actualAdvectionField_contDiff hu).continuous
        (actualAdvectionField_isOnePeriodic hp) k = 0 := by
  funext component
  unfold vectorSpatialFourierCoeff UnitAddTorus.mFourierCoeff
  apply congrFun ?_ component
  apply integral_eq_zero_of_ae
  filter_upwards [] with q
  have hactual : ∀ x, actualAdvectionField (shearVelocity amplitude) x = 0 := by
    exact congrFun (shearVelocity_actualAdvectionField amplitude)
  have hcz : complexifySpace (0 : Space) = 0 := by
    ext j
    simp [complexifySpace]
  simp only [NavierStokesTorusVorticity.periodicTorusLift]
  change (UnitAddTorus.mFourier (-k) q) •
    complexifySpace (actualAdvectionField (shearVelocity amplitude)
      (NavierStokesTorusVorticity.euclideanRepresentative q)) = 0
  rw [hactual, hcz, smul_zero]

/-- The actual source receiver vanishes for any scalar amplitude of the transverse shear. -/
theorem openActualAdvectionMode_zero_of_shear
    {T nu A : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : Ioo 0 T} (ht : ∀ x, velocity x t.1 = shearVelocity A x)
    (k : SpatialFrequency) : openActualAdvectionMode solution t k = 0 := by
  unfold openActualAdvectionMode
  have hfield : (fun x ↦ velocity x t.1) = shearVelocity A := funext ht
  have hactual : ∀ x, actualAdvectionField (fun x ↦ velocity x t.1) x = 0 := by
    intro x
    rw [hfield]
    exact congrFun (shearVelocity_actualAdvectionField A) x
  unfold vectorSpatialFourierCoeff UnitAddTorus.mFourierCoeff
  funext component
  apply congrFun ?_ component
  apply integral_eq_zero_of_ae
  filter_upwards [] with q
  change (UnitAddTorus.mFourier (-k) q) •
    complexifySpace (actualAdvectionField (fun x ↦ velocity x t.1)
      (NavierStokesTorusVorticity.euclideanRepresentative q)) = 0
  have hcz : complexifySpace (0 : Space) = 0 := by
    ext j
    simp [complexifySpace]
  rw [hactual, hcz, smul_zero]

theorem shearVelocity_vorticityNonlinearMode_zero
    {T nu A : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : Ioo 0 T} (ht : ∀ x, velocity x t.1 = shearVelocity A x)
    (k : SpatialFrequency) :
    vorticityNonlinearMode solution t k = 0 := by
  rw [vorticityNonlinearMode,
    NavierStokesOpenAdvectionCarrierIntegration.openAdvectionMode_eq_openActualAdvectionMode,
    openActualAdvectionMode_zero_of_shear solution ht k]
  simp [frequencyCurlMultiplier]

theorem shearVelocity_coherenceDefectAt_zero
    {T nu A : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : Ioo 0 T} (ht : ∀ x, velocity x t.1 = shearVelocity A x)
    (k : SpatialFrequency) :
    CoherenceDefectAt solution t 0 k := by
  intro output
  rw [openActualAdvectionMode_zero_of_shear solution ht k]
  have hnonneg : 0 ≤ ∑' p, ‖feedTerm solution t k p output‖ ^ 2 :=
    tsum_nonneg fun p ↦ sq_nonneg ‖feedTerm solution t k p output‖
  simpa using hnonneg

/-! ## The amplitude diffusion law and its no-growth consequence -/

def shearAmplitudeLaw (nu : ℝ) (amplitude : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, HasDerivAt amplitude (-nu * (2 * Real.pi) ^ 2 * amplitude t) t

theorem shearAmplitudeLaw_solution (nu : ℝ) (A₀ : ℝ) :
    shearAmplitudeLaw nu (fun t ↦ A₀ * Real.exp (-nu * (2 * Real.pi) ^ 2 * t)) := by
  intro t
  have hinner : HasDerivAt
      (fun s : ℝ ↦ -nu * (2 * Real.pi) ^ 2 * s)
      (-nu * (2 * Real.pi) ^ 2) t := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id t).const_mul (-nu * (2 * Real.pi) ^ 2)
  have hexp := hinner.exp
  have hscaled := hexp.const_mul A₀
  simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled

theorem shearAmplitudeLaw_solution_norm_le
    {nu A₀ t : ℝ} (hnu : 0 ≤ nu) (ht : 0 ≤ t) :
    ‖A₀ * Real.exp (-nu * (2 * Real.pi) ^ 2 * t)‖ ≤ ‖A₀‖ := by
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-nu * (2 * Real.pi) ^ 2 * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hfactor : 0 ≤ nu * (2 * Real.pi) ^ 2 * t :=
      mul_nonneg (mul_nonneg hnu (sq_nonneg _)) ht
    nlinarith
  nlinarith [abs_nonneg A₀, mul_le_mul_of_nonneg_left he (abs_nonneg A₀)]

/-! ## The actual momentum residual -/

def shearVelocityField (amplitude : ℝ → ℝ) : VelocityField :=
  fun x t ↦ shearVelocity (amplitude t) x

def shearMomentumResidual (nu : ℝ) (amplitude : ℝ → ℝ) (x : Space) (t : ℝ) : Space :=
  deriv (shearVelocityField amplitude x) t
    + actualAdvectionField (shearVelocity (amplitude t)) x
    - nu • Δ (shearVelocity (amplitude t)) x

theorem hasDerivAt_shearVelocityField
    {amplitude : ℝ → ℝ} {A' t : ℝ} (hA : HasDerivAt amplitude A' t) (x : Space) :
    HasDerivAt (shearVelocityField amplitude x) (shearVelocity A' x) t := by
  have hs := hA.mul_const (Real.sin (2 * Real.pi * x 0))
  have hv := hs.smul_const
    (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : Space)
  change HasDerivAt (fun s : ℝ ↦
      (amplitude s * Real.sin (2 * Real.pi * x 0)) •
        EuclideanSpace.single (1 : Fin 3) 1) _ t
  exact hv

theorem deriv_shearVelocityField
    {amplitude : ℝ → ℝ} {A' t : ℝ} (hA : HasDerivAt amplitude A' t) (x : Space) :
    deriv (shearVelocityField amplitude x) t = shearVelocity A' x :=
  (hasDerivAt_shearVelocityField hA x).deriv

theorem shearMomentumResidual_eq_scalar_shear
    {nu : ℝ} {amplitude : ℝ → ℝ} {A' t : ℝ} (x : Space)
    (hA : HasDerivAt amplitude A' t) :
    shearMomentumResidual nu amplitude x t =
      shearVelocity (A' + nu * (2 * Real.pi) ^ 2 * amplitude t) x := by
  unfold shearMomentumResidual
  rw [deriv_shearVelocityField hA, shearVelocity_actualAdvectionField,
    Pi.zero_apply, add_zero, congrFun (laplacian_shearVelocity (amplitude t)) x]
  unfold shearVelocity
  simp only [Pi.smul_apply, smul_smul, sub_eq_add_neg]
  ext j
  fin_cases j <;> simp [smul_eq_mul]
  ring

theorem shearMomentumResidual_zero_of_shearAmplitudeLaw
    {nu : ℝ} {amplitude : ℝ → ℝ} {t : ℝ} (x : Space)
    (hlaw : shearAmplitudeLaw nu amplitude) :
    shearMomentumResidual nu amplitude x t = 0 := by
  rw [shearMomentumResidual_eq_scalar_shear x (hlaw t)]
  unfold shearVelocity
  simp

/-- Vanishing of the complete unforced zero-pressure shear residual requires exactly the heat
amplitude law. A desired growing amplitude cannot be freely assigned to this source class. -/
theorem shearMomentumResidual_zero_iff
    {nu : ℝ} {amplitude : ℝ → ℝ} {A' t : ℝ} (hA : HasDerivAt amplitude A' t) :
    (∀ x, shearMomentumResidual nu amplitude x t = 0) ↔
      A' = -nu * (2 * Real.pi) ^ 2 * amplitude t := by
  constructor
  · intro h
    have hvalue := congrArg (fun v : Space ↦ v 1)
      (h (EuclideanSpace.single 0 (1 / 4)))
    rw [shearMomentumResidual_eq_scalar_shear _ hA, shearVelocity_amplitude_receiver] at hvalue
    change A' + nu * (2 * Real.pi) ^ 2 * amplitude t = 0 at hvalue
    linarith
  · intro h x
    rw [shearMomentumResidual_eq_scalar_shear _ hA, h]
    simp [shearVelocity, neg_mul]

/-- A concrete unforced periodic source realizes the decaying shear, including its one-sided
initial derivative and joint smoothness. This supplies the control's actual source carrier. -/
theorem decayingShearSolution (nu A₀ : ℝ) :
    PeriodicSolution nu (shearVelocity A₀) (0 : VelocityField)
      (shearVelocityField (fun t ↦ A₀ * Real.exp (-nu * (2 * Real.pi) ^ 2 * t)))
      (0 : PressureField) where
  momentum x t ht := by
    let a : ℝ → ℝ := fun r ↦ A₀ * Real.exp (-nu * (2 * Real.pi) ^ 2 * r)
    have hlaw : shearAmplitudeLaw nu a := shearAmplitudeLaw_solution nu A₀
    have hd := hasDerivAt_shearVelocityField (hlaw t) x
    have hwithin : derivWithin (shearVelocityField a x) (Ici 0) t =
        deriv (shearVelocityField a x) t :=
      (hd.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Ici 0).uniqueDiffWithinAt ht)).trans
        hd.deriv.symm
    have hr := shearMomentumResidual_zero_of_shearAmplitudeLaw (t := t) x hlaw
    change derivWithin (shearVelocityField a x) (Ici 0) t +
        fderiv ℝ (shearVelocity (a t)) x (shearVelocity (a t) x) =
      nu • Δ (shearVelocity (a t)) x - gradient (fun _ : Space ↦ (0 : ℝ)) x + 0
    rw [hwithin]
    simpa [shearMomentumResidual, actualAdvectionField] using eq_of_sub_eq_zero hr
  incompressible x t _ht := shearVelocity_divergence _ x
  initial x := by simp [shearVelocityField, shearVelocity]
  velocitySmooth := by
    have hcoord0 : ContDiff ℝ ∞ (fun x : Space ↦ x 0) := by
      simpa only [id_eq] using ((contDiff_piLp 2).mp (contDiff_id (𝕜 := ℝ)) 0)
    have hcoord : ContDiff ℝ ∞ (fun z : Space × ℝ ↦ z.1 0) :=
      hcoord0.comp contDiff_fst
    have ha : ContDiff ℝ ∞ (fun z : Space × ℝ ↦ A₀ * Real.exp (-nu * (2 * Real.pi) ^ 2 * z.2)) := by
      fun_prop
    have hs : ContDiff ℝ ∞ (fun z : Space × ℝ ↦
        (A₀ * Real.exp (-nu * (2 * Real.pi) ^ 2 * z.2) *
          Real.sin (2 * Real.pi * z.1 0)) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) :=
      (ha.mul ((contDiff_const.mul hcoord).sin)).smul contDiff_const
    exact hs.contDiffOn
  pressureSmooth := contDiffOn_const
  velocityPeriodic t _ht := shearVelocity_isOnePeriodic _
  pressurePeriodic := by intro t _ht x i; rfl

theorem decayingShear_coherenceDefect_zero
    {T : ℝ} (hT : 0 < T) (nu A₀ : ℝ) (t : Ioo 0 T) (k : SpatialFrequency) :
    CoherenceDefectAt (NavierStokesOpenLifespan.PeriodicSolution.toOpenPeriodicSolutionOn
      (decayingShearSolution nu A₀) hT) t 0 k :=
  shearVelocity_coherenceDefectAt_zero
    (NavierStokesOpenLifespan.PeriodicSolution.toOpenPeriodicSolutionOn
      (decayingShearSolution nu A₀) hT)
    (A := A₀ * Real.exp (-nu * (2 * Real.pi) ^ 2 * t.1)) (fun _x ↦ rfl) k

section Audit

#print axioms shearVelocity_contDiff
#print axioms laplacian_shearVelocity
#print axioms shearVelocity_isOnePeriodic
#print axioms shearVelocity_actualAdvectionField
#print axioms shearVelocity_fourierActualAdvection_zero
#print axioms shearVelocity_vorticityNonlinearMode_zero
#print axioms shearVelocity_coherenceDefectAt_zero
#print axioms shearAmplitudeLaw_solution
#print axioms shearAmplitudeLaw_solution_norm_le
#print axioms deriv_shearVelocityField
#print axioms shearMomentumResidual_eq_scalar_shear
#print axioms shearMomentumResidual_zero_of_shearAmplitudeLaw
#print axioms shearMomentumResidual_zero_iff
#print axioms decayingShearSolution
#print axioms decayingShear_coherenceDefect_zero

end Audit

end Soma.Holonics.Millennium.NavierStokesShearAnsatz
