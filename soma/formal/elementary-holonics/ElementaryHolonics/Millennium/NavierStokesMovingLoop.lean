import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import ElementaryHolonics.Millennium.NavierStokesHodge
import ElementaryHolonics.Millennium.NavierStokesKelvin
import ElementaryHolonics.Millennium.NavierStokesMaterialDerivative

/-!
# Moving material loops and exact pressure periods

The first part of this module closes the pressure face of the genuine curve-integral receiver.
For a differentiable scalar pressure and a differentiable parameterized curve, the integral of
the lowered pressure gradient is exactly the endpoint difference.  It consequently vanishes on
closed curves.  A second theorem attaches this result to Mathlib's actual `curveIntegral`; its
integrability hypothesis is retained explicitly so totalization cannot manufacture a zero.

The later material-loop construction will use the same interval presentation to differentiate a
two-parameter moving circulation before rebasing the result to `curveIntegral`.
-/

noncomputable section

open Set InnerProductSpace MeasureTheory
open scoped Interval Laplacian

namespace Soma.Holonics.Millennium.NavierStokesMovingLoop

open Soma.Holonics.Millennium.NavierStokes

/-- The Euclidean lowering of a spatial pressure gradient, as the one-form integrated along a
curve.  Unlike the alternating-map presentation used by `extDeriv`, this is the direct one-form
type expected by Mathlib's curve integral. -/
def pressureGradientOneForm (pressure : Space → ℝ) : Space → Space →L[ℝ] ℝ :=
  fun x ↦ innerSL ℝ (gradient pressure x)

/-- The derivative of pressure read along a differentiable curve is the lowered pressure
gradient paired with the curve velocity. -/
theorem hasDerivAt_pressure_comp_curve
    (pressure : Space → ℝ) (curve : ℝ → Space) (s : ℝ)
    (hpressure : DifferentiableAt ℝ pressure (curve s))
    (hcurve : DifferentiableAt ℝ curve s) :
    HasDerivAt (fun σ ↦ pressure (curve σ))
      (pressureGradientOneForm pressure (curve s) (deriv curve s)) s := by
  have hcomp := hpressure.hasFDerivAt.comp_hasDerivAt s hcurve.hasDerivAt
  apply hcomp.congr_deriv
  change fderiv ℝ pressure (curve s) (deriv curve s) =
    inner ℝ (gradient pressure (curve s)) (deriv curve s)
  exact inner_gradient_left.symm

/-- **Exact pressure transport along an interval.**  The pressure-gradient integral along every
admitted differentiable parameterization is exactly its endpoint pressure difference.  The
integrability witness is explicit, so the totalized interval integral cannot silently hide a
non-integrable integrand. -/
theorem intervalIntegral_pressureGradient_eq_endpointDifference
    (pressure : Space → ℝ) (curve : ℝ → Space) (a b : ℝ)
    (hpressure : ∀ s ∈ uIcc a b, DifferentiableAt ℝ pressure (curve s))
    (hcurve : ∀ s ∈ uIcc a b, DifferentiableAt ℝ curve s)
    (hintegrable : IntervalIntegrable
      (fun s ↦ pressureGradientOneForm pressure (curve s) (deriv curve s)) volume a b) :
    ∫ s in a..b, pressureGradientOneForm pressure (curve s) (deriv curve s) =
      pressure (curve b) - pressure (curve a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro s hs
    exact hasDerivAt_pressure_comp_curve pressure curve s (hpressure s hs) (hcurve s hs)
  · exact hintegrable

/-- The exact pressure period vanishes for a closed interval parameterization. -/
theorem intervalIntegral_pressureGradient_eq_zero_of_closed
    (pressure : Space → ℝ) (curve : ℝ → Space) (a b : ℝ)
    (hpressure : ∀ s ∈ uIcc a b, DifferentiableAt ℝ pressure (curve s))
    (hcurve : ∀ s ∈ uIcc a b, DifferentiableAt ℝ curve s)
    (hintegrable : IntervalIntegrable
      (fun s ↦ pressureGradientOneForm pressure (curve s) (deriv curve s)) volume a b)
    (hclosed : curve b = curve a) :
    ∫ s in a..b, pressureGradientOneForm pressure (curve s) (deriv curve s) = 0 := by
  rw [intervalIntegral_pressureGradient_eq_endpointDifference pressure curve a b hpressure hcurve
    hintegrable, hclosed, sub_self]

section CurveIntegral

variable {a b : Space}

/-- **Exact pressure transport through Mathlib's genuine curve integral.**

Only interior differentiability of `Path.extend` is required, because extension is generally
nondifferentiable at an endpoint when the curve has nonzero endpoint velocity.  Endpoint limits
come from the path's continuity. -/
theorem curveIntegral_pressureGradient_eq_endpointDifference
    (pressure : Space → ℝ) (path : Path a b)
    (hpressure : Differentiable ℝ pressure)
    (hpath : ∀ s ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ path.extend s)
    (hintegrable : IntervalIntegrable
      (fun s ↦ pressureGradientOneForm pressure (path.extend s) (deriv path.extend s))
      volume 0 1) :
    ∫ᶜ x in path, pressureGradientOneForm pressure x = pressure b - pressure a := by
  rw [curveIntegral_eq_intervalIntegral_deriv]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
  · intro s hs
    exact hasDerivAt_pressure_comp_curve pressure path.extend s
      (hpressure (path.extend s)) (hpath s hs)
  · exact hintegrable
  · have hcont : Continuous (fun s ↦ pressure (path.extend s)) :=
      hpressure.continuous.comp path.continuous_extend
    have hzero := hcont.continuousAt.tendsto.mono_left
      (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from inf_le_left)
    simpa using hzero
  · have hcont : Continuous (fun s ↦ pressure (path.extend s)) :=
      hpressure.continuous.comp path.continuous_extend
    have hone := hcont.continuousAt.tendsto.mono_left
      (show nhdsWithin (1 : ℝ) (Iio 1) ≤ nhds 1 from inf_le_left)
    simpa using hone

/-- Every admitted closed path has zero pressure-gradient curve integral. -/
theorem curveIntegral_pressureGradient_eq_zero
    (pressure : Space → ℝ) (base : Space) (loop : Path base base)
    (hpressure : Differentiable ℝ pressure)
    (hloop : ∀ s ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ loop.extend s)
    (hintegrable : IntervalIntegrable
      (fun s ↦ pressureGradientOneForm pressure (loop.extend s) (deriv loop.extend s))
      volume 0 1) :
    ∫ᶜ x in loop, pressureGradientOneForm pressure x = 0 := by
  rw [curveIntegral_pressureGradient_eq_endpointDifference pressure loop hpressure hloop
    hintegrable, sub_self]

end CurveIntegral

/-! ## A two-parameter material loop -/

open Soma.Holonics.Millennium.NavierStokesMaterialDerivative
open Soma.Holonics.Millennium.NavierStokesVorticity

/-- A smooth material loop presented by position and tangent populations.

`mixedTransport` is the explicit mixed-partial receipt: differentiating the tangent in material
time gives the spatial velocity derivative applied to that tangent.  A later constructor may
derive this field from a globally `C²` two-parameter map.  Keeping it explicit here records exactly
the commutation needed by the moving-integral theorem and does not hide it behind the word
"smooth". -/
structure SmoothMaterialLoop (velocity : VelocityField) where
  position : ℝ → ℝ → Space
  tangent : ℝ → ℝ → Space
  closed : ∀ t, position t 1 = position t 0
  parameterized : ∀ t, 0 < t → ∀ s,
    HasDerivAt (position t) (tangent t s) s
  carried : ∀ t, 0 < t → ∀ s,
    HasDerivAt (fun τ ↦ position τ s) (velocity (position t s) t) t
  mixedTransport : ∀ t, 0 < t → ∀ s,
    HasDerivAt (fun τ ↦ tangent τ s)
      (fderiv ℝ (fun x ↦ velocity x t) (position t s) (tangent t s)) t

/-- The velocity/tangent integrand whose parameter integral is material circulation. -/
def movingCirculationIntegrand (velocity : VelocityField)
    (loop : SmoothMaterialLoop velocity) (t s : ℝ) : ℝ :=
  inner ℝ (velocity (loop.position t s) t) (loop.tangent t s)

/-- Circulation of velocity along the two-parameter material loop. -/
def movingCirculation (velocity : VelocityField)
    (loop : SmoothMaterialLoop velocity) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, movingCirculationIntegrand velocity loop t s

/-- The actual closed `Path` carried by a positive-time material-loop slice. -/
def SmoothMaterialLoop.pathAt {velocity : VelocityField}
    (loop : SmoothMaterialLoop velocity) (t : ℝ) (ht : 0 < t) :
    Path (loop.position t 0) (loop.position t 0) :=
  Path.ofLine
    ((show Differentiable ℝ (loop.position t) from
      fun s ↦ (loop.parameterized t ht s).differentiableAt).continuous.continuousOn)
    rfl (loop.closed t)

/-- On the unit parameter interval, `pathAt` retains the original material-loop position. -/
theorem SmoothMaterialLoop.pathAt_extend_eq {velocity : VelocityField}
    (loop : SmoothMaterialLoop velocity) (t : ℝ) (ht : 0 < t)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (loop.pathAt t ht).extend s = loop.position t s := by
  rw [Path.extend_apply _ hs]
  rfl

/-- The interval presentation of material circulation is exactly Mathlib's genuine curve
integral along the constructed closed path. -/
theorem movingCirculation_eq_curveIntegral {velocity : VelocityField}
    (loop : SmoothMaterialLoop velocity) (t : ℝ) (ht : 0 < t) :
    movingCirculation velocity loop t =
      ∫ᶜ x in loop.pathAt t ht,
        Soma.Holonics.Millennium.NavierStokesKelvin.velocityOneForm velocity t x := by
  rw [movingCirculation, curveIntegral_def]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le zero_le_one] at hs
  have heq : EqOn (loop.pathAt t ht).extend (loop.position t) (Icc (0 : ℝ) 1) :=
    fun σ hσ ↦ loop.pathAt_extend_eq t ht hσ
  rw [curveIntegralFun_def, heq hs, derivWithin_congr heq (heq hs)]
  have htangent : HasDerivWithinAt (loop.position t) (loop.tangent t s)
      (Icc (0 : ℝ) 1) s :=
    (loop.parameterized t ht s).hasDerivWithinAt
  rw [htangent.derivWithin (uniqueDiffOn_Icc_zero_one s hs)]
  rfl

/-- The material acceleration paired with the retained loop tangent. -/
def movingMomentumIntegrand (ν : ℝ) (force velocity : VelocityField)
    (pressure : PressureField) (loop : SmoothMaterialLoop velocity) (t s : ℝ) : ℝ :=
  inner ℝ (momentumReturn ν force velocity pressure (loop.position t s) t)
    (loop.tangent t s)

/-- The moving-edge term before its closed-loop cancellation. -/
def movingGeometricIntegrand (velocity : VelocityField)
    (loop : SmoothMaterialLoop velocity) (t s : ℝ) : ℝ :=
  inner ℝ (velocity (loop.position t s) t)
    (fderiv ℝ (fun x ↦ velocity x t) (loop.position t s) (loop.tangent t s))

/-- The viscous return paired with the loop tangent. -/
def movingViscousIntegrand (ν : ℝ) (velocity : VelocityField)
    (loop : SmoothMaterialLoop velocity) (t s : ℝ) : ℝ :=
  inner ℝ (ν • Δ (fun x ↦ velocity x t) (loop.position t s)) (loop.tangent t s)

/-- The pressure-gradient return paired with the loop tangent. -/
def movingPressureIntegrand (pressure : PressureField) {velocity : VelocityField}
    (loop : SmoothMaterialLoop velocity) (t s : ℝ) : ℝ :=
  inner ℝ (gradient (fun x ↦ pressure x t) (loop.position t s)) (loop.tangent t s)

/-- The forcing return paired with the loop tangent. -/
def movingForceIntegrand (force : VelocityField) {velocity : VelocityField}
    (loop : SmoothMaterialLoop velocity) (t s : ℝ) : ℝ :=
  inner ℝ (force (loop.position t s) t) (loop.tangent t s)

/-- The derivative of velocity observed along any admitted material trajectory is the actual
Navier--Stokes momentum return. -/
theorem smoothSolution_hasDerivAt_velocityAlongMaterialPoint
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (position : ℝ → Space) {t : ℝ} (ht : 0 < t)
    (hposition : HasDerivAt position (velocity (position t) t) t) :
    HasDerivAt (fun τ ↦ velocity (position τ) τ)
      (momentumReturn ν force velocity pressure (position t) t) t := by
  have hvelocity := smoothSolution_velocityUncurry_differentiableAt solution (position t) ht
  have hpair : HasDerivAt (fun τ ↦ (position τ, τ))
      (velocity (position t) t, 1) t := hposition.prodMk (hasDerivAt_id t)
  have hcomposition := hvelocity.hasFDerivAt.comp_hasDerivAt_of_eq t hpair (by simp)
  apply hcomposition.congr_deriv
  rw [jointVelocityDerivative_materialDirection hvelocity]
  have hhalf : Set.Ici (0 : ℝ) ∈ nhds t :=
    Filter.mem_of_superset (Ioi_mem_nhds ht) Set.Ioi_subset_Ici_self
  rw [← derivWithin_of_mem_nhds hhalf]
  simpa [momentumReturn] using solution.momentum (position t) t (le_of_lt ht)

/-- Pointwise first variation of the moving circulation integrand.  Material acceleration and
moving-edge geometry remain distinct in the return. -/
theorem hasDerivAt_movingCirculationIntegrand
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (loop : SmoothMaterialLoop velocity) {t : ℝ} (ht : 0 < t) (s : ℝ) :
    HasDerivAt (fun τ ↦ movingCirculationIntegrand velocity loop τ s)
      (movingMomentumIntegrand ν force velocity pressure loop t s +
        movingGeometricIntegrand velocity loop t s) t := by
  have hcurrent := smoothSolution_hasDerivAt_velocityAlongMaterialPoint solution
    (fun τ ↦ loop.position τ s) ht (loop.carried t ht s)
  have htangent := loop.mixedTransport t ht s
  have hinner := hcurrent.inner ℝ htangent
  simpa [movingCirculationIntegrand, movingMomentumIntegrand, movingGeometricIntegrand,
    add_comm] using hinner

/-- The geometric first-variation integrand is the parameter derivative of kinetic energy. -/
theorem hasDerivAt_half_normSq_velocityAlongLoop
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (loop : SmoothMaterialLoop velocity) {t : ℝ} (ht : 0 < t) (s : ℝ) :
    HasDerivAt
      (fun σ ↦ (2 : ℝ)⁻¹ *
        inner ℝ (velocity (loop.position t σ) t) (velocity (loop.position t σ) t))
      (movingGeometricIntegrand velocity loop t s) s := by
  have hvelocity := smoothSolution_velocitySlice_differentiableAt solution
    (loop.position t s) t ht
  have hcurrent := hvelocity.hasFDerivAt.comp_hasDerivAt s (loop.parameterized t ht s)
  have hnorm := (hcurrent.inner ℝ hcurrent).const_mul (2 : ℝ)⁻¹
  convert hnorm using 1 <;> try rfl
  change inner ℝ (velocity (loop.position t s) t)
      (fderiv ℝ (fun x ↦ velocity x t) (loop.position t s) (loop.tangent t s)) =
    (2 : ℝ)⁻¹ *
      (inner ℝ (velocity (loop.position t s) t)
          (fderiv ℝ (fun x ↦ velocity x t) (loop.position t s) (loop.tangent t s)) +
        inner ℝ (fderiv ℝ (fun x ↦ velocity x t) (loop.position t s)
          (loop.tangent t s)) (velocity (loop.position t s) t))
  rw [real_inner_comm
    (velocity (loop.position t s) t)
    (fderiv ℝ (fun x ↦ velocity x t) (loop.position t s) (loop.tangent t s))]
  ring

/-- The complete moving-edge contribution vanishes around a closed smooth material loop. -/
theorem intervalIntegral_movingGeometricIntegrand_eq_zero
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (loop : SmoothMaterialLoop velocity) {t : ℝ} (ht : 0 < t)
    (hintegrable : IntervalIntegrable
      (movingGeometricIntegrand velocity loop t) volume 0 1) :
    ∫ s in (0 : ℝ)..1, movingGeometricIntegrand velocity loop t s = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _hs ↦ hasDerivAt_half_normSq_velocityAlongLoop solution loop ht s) hintegrable]
  rw [loop.closed t]
  simp

/-- The pressure-gradient population has zero period around an admitted material loop. -/
theorem intervalIntegral_movingPressureIntegrand_eq_zero
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (loop : SmoothMaterialLoop velocity) {t : ℝ} (ht : 0 < t)
    (hintegrable : IntervalIntegrable
      (movingPressureIntegrand pressure loop t) volume 0 1) :
    ∫ s in (0 : ℝ)..1, movingPressureIntegrand pressure loop t s = 0 := by
  have hpressure : ∀ s : ℝ,
      DifferentiableAt ℝ (fun x ↦ pressure x t) (loop.position t s) := by
    intro s
    exact (spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime pressure
      (loop.position t s) t solution.pressureSmooth ht).differentiableAt (by simp)
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun σ ↦ pressure (loop.position t σ) t)
        (movingPressureIntegrand pressure loop t s) s := by
    intro s
    have hcomp := hasDerivAt_pressure_comp_curve (fun x ↦ pressure x t)
      (loop.position t) s (hpressure s) (loop.parameterized t ht s).differentiableAt
    simpa [movingPressureIntegrand, pressureGradientOneForm,
      (loop.parameterized t ht s).deriv] using hcomp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _hs ↦ hderiv s) hintegrable]
  rw [loop.closed t]
  simp

/-- **Differentiated moving-loop circulation.**

The hypotheses following `ht` are exactly Mathlib's dominated parametric-integral admission
receipts.  The pointwise derivative itself is not assumed: it is derived above from the material
transport laws and the actual Navier--Stokes momentum equation. -/
theorem hasDerivAt_movingCirculation_eq_momentum
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (loop : SmoothMaterialLoop velocity) {t : ℝ} (ht : 0 < t)
    (timeSet : Set ℝ) (htimeSet : timeSet ∈ nhds t)
    (htimePositive : ∀ τ ∈ timeSet, 0 < τ)
    (hFmeas : ∀ᶠ τ in nhds t, AEStronglyMeasurable
      (movingCirculationIntegrand velocity loop τ) (volume.restrict (Ι (0 : ℝ) 1)))
    (hFint : IntervalIntegrable (movingCirculationIntegrand velocity loop t) volume 0 1)
    (hF'meas : AEStronglyMeasurable
      (fun s ↦ movingMomentumIntegrand ν force velocity pressure loop t s +
        movingGeometricIntegrand velocity loop t s) (volume.restrict (Ι (0 : ℝ) 1)))
    (bound : ℝ → ℝ)
    (hbound : ∀ᵐ s ∂volume, s ∈ Ι (0 : ℝ) 1 →
      ∀ τ ∈ timeSet,
        ‖movingMomentumIntegrand ν force velocity pressure loop τ s +
          movingGeometricIntegrand velocity loop τ s‖ ≤ bound s)
    (hboundIntegrable : IntervalIntegrable bound volume 0 1)
    (hgeometricIntegrable : IntervalIntegrable
      (movingGeometricIntegrand velocity loop t) volume 0 1) :
    HasDerivAt (movingCirculation velocity loop)
      (∫ s in (0 : ℝ)..1,
        movingMomentumIntegrand ν force velocity pressure loop t s) t := by
  have hparam := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    htimeSet hFmeas hFint hF'meas hbound hboundIntegrable
    (Filter.Eventually.of_forall fun s _hs τ hτ ↦
      hasDerivAt_movingCirculationIntegrand solution loop (htimePositive τ hτ) s)
  have hsplit :
      ∫ s in (0 : ℝ)..1,
          (movingMomentumIntegrand ν force velocity pressure loop t s +
            movingGeometricIntegrand velocity loop t s) =
        ∫ s in (0 : ℝ)..1,
          movingMomentumIntegrand ν force velocity pressure loop t s := by
    have hmomentum : IntervalIntegrable
        (movingMomentumIntegrand ν force velocity pressure loop t) volume 0 1 := by
      simpa only [add_sub_cancel_right] using hparam.1.sub hgeometricIntegrable
    rw [intervalIntegral.integral_add hmomentum hgeometricIntegrable,
      intervalIntegral_movingGeometricIntegrand_eq_zero solution loop ht hgeometricIntegrable,
      add_zero]
  simpa only [movingCirculation] using hsplit ▸ hparam.2

/-- After the exact pressure period is removed, the momentum period is precisely viscosity plus
forcing.  All three component integrability receipts are retained explicitly. -/
theorem intervalIntegral_movingMomentum_eq_viscous_add_force
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (loop : SmoothMaterialLoop velocity) {t : ℝ} (ht : 0 < t)
    (hviscous : IntervalIntegrable (movingViscousIntegrand ν velocity loop t) volume 0 1)
    (hpressure : IntervalIntegrable (movingPressureIntegrand pressure loop t) volume 0 1)
    (hforce : IntervalIntegrable (movingForceIntegrand force loop t) volume 0 1) :
    ∫ s in (0 : ℝ)..1, movingMomentumIntegrand ν force velocity pressure loop t s =
      (∫ s in (0 : ℝ)..1, movingViscousIntegrand ν velocity loop t s) +
        ∫ s in (0 : ℝ)..1, movingForceIntegrand force loop t s := by
  have hpoint : movingMomentumIntegrand ν force velocity pressure loop t =
      fun s ↦ movingViscousIntegrand ν velocity loop t s -
        movingPressureIntegrand pressure loop t s + movingForceIntegrand force loop t s := by
    funext s
    simp [movingMomentumIntegrand, movingViscousIntegrand, movingPressureIntegrand,
      movingForceIntegrand, momentumReturn, inner_sub_left, inner_add_left]
  rw [hpoint, intervalIntegral.integral_add (hviscous.sub hpressure) hforce,
    intervalIntegral.integral_sub hviscous hpressure,
    intervalIntegral_movingPressureIntegrand_eq_zero solution loop ht hpressure]
  ring

/-- The differentiated circulation theorem in its pressure-free Navier--Stokes form. -/
theorem HasDerivAt.movingCirculation_eq_viscous_add_force
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : SmoothSolution ν u₀ force velocity pressure}
    {loop : SmoothMaterialLoop velocity} {t : ℝ} (ht : 0 < t)
    (hderiv : HasDerivAt (movingCirculation velocity loop)
      (∫ s in (0 : ℝ)..1,
        movingMomentumIntegrand ν force velocity pressure loop t s) t)
    (hviscous : IntervalIntegrable (movingViscousIntegrand ν velocity loop t) volume 0 1)
    (hpressure : IntervalIntegrable (movingPressureIntegrand pressure loop t) volume 0 1)
    (hforce : IntervalIntegrable (movingForceIntegrand force loop t) volume 0 1) :
    HasDerivAt (movingCirculation velocity loop)
      ((∫ s in (0 : ℝ)..1, movingViscousIntegrand ν velocity loop t s) +
        ∫ s in (0 : ℝ)..1, movingForceIntegrand force loop t s) t := by
  apply hderiv.congr_deriv
  exact intervalIntegral_movingMomentum_eq_viscous_add_force solution loop ht
    hviscous hpressure hforce

section Audit

#print axioms hasDerivAt_pressure_comp_curve
#print axioms intervalIntegral_pressureGradient_eq_endpointDifference
#print axioms intervalIntegral_pressureGradient_eq_zero_of_closed
#print axioms curveIntegral_pressureGradient_eq_endpointDifference
#print axioms curveIntegral_pressureGradient_eq_zero
#print axioms movingCirculation_eq_curveIntegral
#print axioms smoothSolution_hasDerivAt_velocityAlongMaterialPoint
#print axioms hasDerivAt_movingCirculationIntegrand
#print axioms intervalIntegral_movingGeometricIntegrand_eq_zero
#print axioms intervalIntegral_movingPressureIntegrand_eq_zero
#print axioms hasDerivAt_movingCirculation_eq_momentum
#print axioms intervalIntegral_movingMomentum_eq_viscous_add_force
#print axioms HasDerivAt.movingCirculation_eq_viscous_add_force

end Audit

end Soma.Holonics.Millennium.NavierStokesMovingLoop
