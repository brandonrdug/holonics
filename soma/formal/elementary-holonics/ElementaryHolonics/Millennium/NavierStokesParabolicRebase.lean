import ElementaryHolonics.Millennium.NavierStokesScaling
import ElementaryHolonics.Millennium.NavierStokesVorticity
import Mathlib.Analysis.Calculus.Deriv.CompMul

/-!
# The Navier--Stokes parabolic rebase is an exact constitutive transport

**[proved-derived]** `NavierStokesScaling.lean` records the standard rational scaling weights but
explicitly does not derive them from the PDE.  This file constructs the missing source passage.
Velocity, pressure, force, and initial data are transported together under

```text
uλ(x,t) = λ u(λx,λ²t),   pλ(x,t) = λ² p(λx,λ²t),
fλ(x,t) = λ³ f(λx,λ²t),  u₀λ(x) = λ u₀(λx).
```

The returned theorem is not exponent bookkeeping: the actual time derivative, spatial derivative,
advection, divergence, pressure gradient, and Laplacian receivers commute with this transport, and
the momentum equation returns multiplied by the common oriented factor `λ³`.
-/

noncomputable section

open ContDiff InnerProductSpace Set
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesParabolicRebase

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesVorticity

/-! ## The addressed rebase maps -/

/-- The spatial chart transition `x ↦ λx` as a continuous linear map. -/
def parabolicSpaceMap (scale : ℝ) : Space →L[ℝ] Space :=
  scale • ContinuousLinearMap.id ℝ Space

@[simp]
theorem parabolicSpaceMap_apply (scale : ℝ) (x : Space) :
    parabolicSpaceMap scale x = scale • x := by
  simp [parabolicSpaceMap]

/-- Initial data transported through the parabolic chart. -/
def parabolicInitialVelocity (scale : ℝ) (initial : InitialVelocity) : InitialVelocity :=
  fun x ↦ scale • initial (scale • x)

/-- Velocity transported through space, time, and its vector amplitude. -/
def parabolicVelocity (scale : ℝ) (velocity : VelocityField) : VelocityField :=
  fun x t ↦ scale • velocity (scale • x) (scale ^ 2 * t)

/-- Pressure carries the quadratic parabolic weight. -/
def parabolicPressure (scale : ℝ) (pressure : PressureField) : PressureField :=
  fun x t ↦ scale ^ 2 * pressure (scale • x) (scale ^ 2 * t)

/-- Force carries the cubic parabolic weight. -/
def parabolicForce (scale : ℝ) (force : VelocityField) : VelocityField :=
  fun x t ↦ scale ^ 3 • force (scale • x) (scale ^ 2 * t)

/-! ## Exact first-order transport -/

/-- The ordinary positive-time jet of velocity carries the common cubic PDE weight. -/
theorem deriv_parabolicVelocity
    (scale : ℝ) (velocity : VelocityField) (x : Space) (t : ℝ) :
    deriv (parabolicVelocity scale velocity x) t =
      scale ^ 3 • deriv (velocity (scale • x)) (scale ^ 2 * t) := by
  unfold parabolicVelocity
  change deriv (scale • fun s ↦ velocity (scale • x) (scale ^ 2 * s)) t = _
  rw [deriv_const_smul']
  rw [deriv_comp_mul_left]
  rw [smul_smul]
  ring_nf

/-- The spatial derivative of velocity carries weight two. -/
theorem fderiv_parabolicVelocity
    (scale : ℝ) (velocity : VelocityField) (x : Space) (t : ℝ) :
    fderiv ℝ (fun y ↦ parabolicVelocity scale velocity y t) x =
      scale ^ 2 • fderiv ℝ (fun y ↦ velocity y (scale ^ 2 * t)) (scale • x) := by
  unfold parabolicVelocity
  rw [show (fun y ↦ scale • velocity (scale • y) (scale ^ 2 * t)) =
      scale • (fun y ↦ velocity (scale • y) (scale ^ 2 * t)) by rfl]
  rw [congrFun (fderiv_const_smul_of_field scale) x]
  simp only [Pi.smul_apply]
  have hcomp :
      fderiv ℝ (fun y ↦ velocity (scale • y) (scale ^ 2 * t)) x =
        scale • fderiv ℝ (fun y ↦ velocity y (scale ^ 2 * t)) (scale • x) := by
    simpa only using
      (fderiv_comp_smul (f := fun y ↦ velocity y (scale ^ 2 * t))
        (x := x) scale)
  rw [hcomp]
  rw [smul_smul]
  ring_nf

/-- The nonlinear advection occurrence also carries weight three. -/
theorem advection_parabolicVelocity
    (scale : ℝ) (velocity : VelocityField) (x : Space) (t : ℝ) :
    fderiv ℝ (fun y ↦ parabolicVelocity scale velocity y t) x
        (parabolicVelocity scale velocity x t) =
      scale ^ 3 •
        fderiv ℝ (fun y ↦ velocity y (scale ^ 2 * t)) (scale • x)
          (velocity (scale • x) (scale ^ 2 * t)) := by
  rw [fderiv_parabolicVelocity]
  unfold parabolicVelocity
  simp only [ContinuousLinearMap.smul_apply]
  rw [map_smul, smul_smul]
  rw [show scale ^ 2 * scale = scale ^ 3 by ring]

/-- Divergence carries weight two under the spatial-amplitude rebase. -/
theorem divergence_parabolicVelocity
    (scale : ℝ) (velocity : VelocityField) (x : Space) (t : ℝ) :
    divergence (fun y ↦ parabolicVelocity scale velocity y t) x =
      scale ^ 2 *
        divergence (fun y ↦ velocity y (scale ^ 2 * t)) (scale • x) := by
  unfold divergence
  rw [fderiv_parabolicVelocity]
  simp

/-- The pressure gradient carries the common cubic PDE weight. -/
theorem gradient_parabolicPressure
    (scale : ℝ) (pressure : PressureField) (x : Space) (t : ℝ) :
    gradient (fun y ↦ parabolicPressure scale pressure y t) x =
      scale ^ 3 •
        gradient (fun y ↦ pressure y (scale ^ 2 * t)) (scale • x) := by
  unfold gradient parabolicPressure
  rw [show (fun y ↦ scale ^ 2 * pressure (scale • y) (scale ^ 2 * t)) =
      scale ^ 2 • (fun y ↦ pressure (scale • y) (scale ^ 2 * t)) by
    funext y
    simp]
  rw [congrFun (fderiv_const_smul_of_field (scale ^ 2)) x]
  simp only [Pi.smul_apply]
  have hcomp :
      fderiv ℝ (fun y ↦ pressure (scale • y) (scale ^ 2 * t)) x =
        scale • fderiv ℝ (fun y ↦ pressure y (scale ^ 2 * t)) (scale • x) := by
    simpa only using
      (fderiv_comp_smul (f := fun y ↦ pressure y (scale ^ 2 * t))
        (x := x) scale)
  rw [hcomp]
  simp only [map_smul, smul_smul]
  ring_nf

/-! ## Exact second-order transport -/

/-- The second spatial derivative sees the two incoming chart directions and therefore carries
two copies of the scale. -/
theorem iteratedFDeriv_two_comp_parabolicSpaceMap
    (scale : ℝ) (field : Space → Space) (hfield : ContDiff ℝ 2 field)
    (x first second : Space) :
    iteratedFDeriv ℝ 2 (fun y ↦ field (scale • y)) x ![first, second] =
      scale ^ 2 • iteratedFDeriv ℝ 2 field (scale • x) ![first, second] := by
  have htransport :=
    (parabolicSpaceMap scale).iteratedFDeriv_comp_right hfield x
      (i := 2) (by norm_num)
  have happly := congrArg
    (fun derivative : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ Space) Space ↦
      derivative ![first, second]) htransport
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at happly
  simp only [parabolicSpaceMap_apply] at happly
  change
    iteratedFDeriv ℝ 2 (fun y ↦ field (scale • y)) x ![first, second] =
      iteratedFDeriv ℝ 2 field (scale • x)
        (fun i ↦ scale • ![first, second] i) at happly
  rw [ContinuousMultilinearMap.map_smul_univ] at happly
  simpa [Fin.prod_univ_two, pow_two] using happly

/-- Precomposition by the spatial dilation gives the Laplacian its quadratic chart weight. -/
theorem laplacian_comp_parabolicSpaceMap
    (scale : ℝ) (field : Space → Space) (hfield : ContDiff ℝ 2 field) (x : Space) :
    Δ (fun y ↦ field (scale • y)) x =
      scale ^ 2 • Δ field (scale • x) := by
  rw [congrFun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis
      (fun y ↦ field (scale • y))) x]
  rw [congrFun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis field) (scale • x)]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  exact iteratedFDeriv_two_comp_parabolicSpaceMap scale field hfield x
    ((stdOrthonormalBasis ℝ Space) coordinate)
    ((stdOrthonormalBasis ℝ Space) coordinate)

/-- Viscous diffusion carries the same cubic weight as time transport, advection, pressure, and
force: one amplitude copy and two spatial chart copies. -/
theorem laplacian_parabolicVelocity
    (scale : ℝ) (velocity : VelocityField) (x : Space) (t : ℝ)
    (hsmooth : ContDiff ℝ 2 (fun y ↦ velocity y (scale ^ 2 * t))) :
    Δ (fun y ↦ parabolicVelocity scale velocity y t) x =
      scale ^ 3 • Δ (fun y ↦ velocity y (scale ^ 2 * t)) (scale • x) := by
  let field : Space → Space := fun y ↦ velocity y (scale ^ 2 * t)
  have hcomp : ContDiffAt ℝ 2 (fun y ↦ field (scale • y)) x := by
    have hglobal : ContDiff ℝ 2 (field ∘ parabolicSpaceMap scale) :=
      hsmooth.comp_continuousLinearMap
    simpa [field, Function.comp_def] using hglobal.contDiffAt
  change Δ (scale • fun y ↦ field (scale • y)) x = _
  rw [laplacian_smul scale hcomp]
  rw [laplacian_comp_parabolicSpaceMap scale field hsmooth x]
  rw [smul_smul]
  congr 1
  ring

/-! ## The constitutive law -/

/-- The Navier--Stokes momentum equation is equivariant under the complete parabolic rebase.  Each
term is transported from its actual differential definition, and only then are the five copies of
the common cubic factor identified. -/
theorem parabolicVelocity_momentum
    (nu scale : ℝ) (force velocity : VelocityField) (pressure : PressureField)
    (x : Space) (t : ℝ)
    (hsmooth : ContDiff ℝ 2 (fun y ↦ velocity y (scale ^ 2 * t)))
    (hmomentum :
      deriv (velocity (scale • x)) (scale ^ 2 * t) +
          fderiv ℝ (fun y ↦ velocity y (scale ^ 2 * t)) (scale • x)
            (velocity (scale • x) (scale ^ 2 * t)) =
        nu • Δ (fun y ↦ velocity y (scale ^ 2 * t)) (scale • x) -
          gradient (fun y ↦ pressure y (scale ^ 2 * t)) (scale • x) +
          force (scale • x) (scale ^ 2 * t)) :
    deriv (parabolicVelocity scale velocity x) t +
          fderiv ℝ (fun y ↦ parabolicVelocity scale velocity y t) x
            (parabolicVelocity scale velocity x t) =
        nu • Δ (fun y ↦ parabolicVelocity scale velocity y t) x -
          gradient (fun y ↦ parabolicPressure scale pressure y t) x +
          parabolicForce scale force x t := by
  rw [deriv_parabolicVelocity, advection_parabolicVelocity,
    laplacian_parabolicVelocity scale velocity x t hsmooth,
    gradient_parabolicPressure]
  unfold parabolicForce
  have hscaled := congrArg (fun value : Space ↦ scale ^ 3 • value) hmomentum
  simpa [smul_add, smul_sub, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hscaled

/-! ## Attachment to the official source carrier -/

/-- The transported initial face is exact at time zero. -/
theorem parabolicVelocity_zero
    (scale : ℝ) (velocity : VelocityField) (x : Space) :
    parabolicVelocity scale velocity x 0 =
      parabolicInitialVelocity scale (fun y ↦ velocity y 0) x := by
  simp [parabolicVelocity, parabolicInitialVelocity]

/-- Every official smooth solution remains divergence-free after the parabolic transport. -/
theorem SmoothSolution.parabolicVelocity_incompressible
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution nu initial force velocity pressure)
    (scale : ℝ) (x : Space) (t : ℝ) (ht : 0 ≤ t) :
    divergence (fun y ↦ parabolicVelocity scale velocity y t) x = 0 := by
  rw [divergence_parabolicVelocity]
  rw [solution.incompressible (scale • x) (scale ^ 2 * t)
    (mul_nonneg (sq_nonneg scale) ht)]
  simp

/-- **[proved-derived; formal-checked]** At every strictly positive transported occurrence and
every nonzero scale, the official `SmoothSolution.momentum` field returns the complete parabolic
momentum equation.  This removes the "weights declared but not derived from the PDE" boundary of
`NavierStokesScaling.lean`. -/
theorem SmoothSolution.parabolicVelocity_momentum_positiveTime
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution nu initial force velocity pressure)
    (scale : ℝ) (hscale : scale ≠ 0) (x : Space) (t : ℝ) (ht : 0 < t) :
    deriv (parabolicVelocity scale velocity x) t +
          fderiv ℝ (fun y ↦ parabolicVelocity scale velocity y t) x
            (parabolicVelocity scale velocity x t) =
        nu • Δ (fun y ↦ parabolicVelocity scale velocity y t) x -
          gradient (fun y ↦ parabolicPressure scale pressure y t) x +
          parabolicForce scale force x t := by
  have hscaledTime : 0 < scale ^ 2 * t :=
    mul_pos (sq_pos_of_ne_zero hscale) ht
  have hmomentum := solution.momentum (scale • x) (scale ^ 2 * t) hscaledTime.le
  have hhalf : Set.Ici (0 : ℝ) ∈ nhds (scale ^ 2 * t) :=
    Filter.mem_of_superset (Ioi_mem_nhds hscaledTime) Set.Ioi_subset_Ici_self
  rw [derivWithin_of_mem_nhds hhalf] at hmomentum
  have hsmooth : ContDiff ℝ 2 (fun y ↦ velocity y (scale ^ 2 * t)) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact smoothSolution_velocitySlice_contDiffAtTwo solution y (scale ^ 2 * t) hscaledTime
  exact parabolicVelocity_momentum nu scale force velocity pressure x t hsmooth hmomentum

section Audit

#print axioms deriv_parabolicVelocity
#print axioms fderiv_parabolicVelocity
#print axioms advection_parabolicVelocity
#print axioms divergence_parabolicVelocity
#print axioms gradient_parabolicPressure
#print axioms iteratedFDeriv_two_comp_parabolicSpaceMap
#print axioms laplacian_comp_parabolicSpaceMap
#print axioms laplacian_parabolicVelocity
#print axioms parabolicVelocity_momentum
#print axioms SmoothSolution.parabolicVelocity_incompressible
#print axioms SmoothSolution.parabolicVelocity_momentum_positiveTime

end Audit

end Soma.Holonics.Millennium.NavierStokesParabolicRebase
