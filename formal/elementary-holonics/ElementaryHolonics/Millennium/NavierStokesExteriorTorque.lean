import ElementaryHolonics.Millennium.NavierStokesViscousSwirlBalance

/-!
# Angular momentum retains the exterior pressure torque

The pressure is an arbitrary Cartesian field. Its angular derivative is retained in the
actual trajectory equation and in the MFR1 physical reconstruction. No global rotational
symmetry or division by the radius is imposed. The scalar Laplacian receiver includes the
axial vorticity term coming from differentiating the position carrier.
-/

noncomputable section

open ContDiff Set InnerProductSpace
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesExteriorTorque

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesSwirlDiffusion
open Soma.Holonics.Millennium.NavierStokesViscousSwirlBalance
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesDynamicRescaling

def angularField (u : InitialVelocity) (x : Space) : ℝ :=
  cartesianAngularMomentum x (u x)

def pressureTorque (P : Space → ℝ) (x : Space) : ℝ :=
  cartesianAngularMomentum x (gradient P x)

def axialVorticity (u : InitialVelocity) (x : Space) : ℝ :=
  gradient (fun y ↦ u y 1) x 0 - gradient (fun y ↦ u y 0) x 1

def rotationGenerator (x : Space) : Space := assemble (-x 1) (x 0) 0

/-- Torque is the actual angular directional derivative, including at the axis. -/
theorem pressureTorque_eq_angular_derivative (P : Space → ℝ) (x : Space) :
    pressureTorque P x = fderiv ℝ P x (rotationGenerator x) := by
  have hc (i : Fin 3) :
      fderiv ℝ P x (EuclideanSpace.single i 1) = gradient P x i := by
    rw [← EuclideanSpace.inner_basisFun_real (Fin 3) (gradient P x : Space) i]
    simpa only [EuclideanSpace.basisFun_apply] using (inner_gradient_left :
      inner ℝ (gradient P x) (EuclideanSpace.basisFun (Fin 3) ℝ i) = _).symm
  simp [rotationGenerator, assemble, map_add, map_smul, hc, pressureTorque,
    cartesianAngularMomentum]
  ring

theorem pressureTorque_axisymmetric (P : MeridionalProfile) (x : Space)
    (hP : DifferentiableAt ℝ P (meridionalChart x)) :
    pressureTorque (fun y ↦ P (meridionalChart y)) x = 0 := by
  unfold pressureTorque cartesianAngularMomentum
  rw [gradient_axisymmetricPressure P x hP]
  simp only [assemble_zero, assemble_one]
  ring

/-- Agreement of Poisson sources leaves a harmonic difference in the local chart. It does
not assert that this difference is constant or has zero torque. -/
theorem pressure_difference_harmonic (P Q : Space → ℝ) (x : Space)
    (hP : ContDiffAt ℝ 2 P x) (hQ : ContDiffAt ℝ 2 Q x)
    (hsource : Δ P x = Δ Q x) : Δ (P - Q) x = 0 := by
  rw [hP.laplacian_sub hQ, hsource, sub_self]

/-- The centred pressure torque reconstructs with the actual square normalizer. -/
theorem rescaled_pressureTorque (length normalizer clock : ℝ → ℝ)
    (pressure : PressureField) (y : Space) (t : ℝ) :
    pressureTorque
      (fun z ↦ rescaledPressure (fun _ ↦ 0) length normalizer clock pressure z t) y =
      normalizer t ^ 2 * pressureTorque (fun z ↦ pressure z (clock t)) (length t • y) := by
  have hp : (fun z ↦ rescaledPressure (fun _ ↦ 0) length normalizer clock pressure z t) =
      NavierStokesRescalingSpace.spatialPullback (normalizer t ^ 2) (length t) 0
        (fun z ↦ pressure z (clock t)) := rfl
  rw [hp]
  unfold pressureTorque cartesianAngularMomentum
  rw [NavierStokesRescalingSpace.gradient_spatialPullback]
  simp only [zero_add, PiLp.smul_apply, smul_eq_mul]
  ring

theorem angularField_fderiv_apply (u : InitialVelocity) (x d : Space)
    (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (angularField u) x d =
      cartesianAngularMomentum d (u x) +
        cartesianAngularMomentum x (fderiv ℝ u x d) := by
  have h0 := (coordinateProjection 0).hasFDerivAt (x := x)
  have h1 := (coordinateProjection 1).hasFDerivAt (x := x)
  have hu0 := (coordinateProjection 0).hasFDerivAt.comp x hu.hasFDerivAt
  have hu1 := (coordinateProjection 1).hasFDerivAt.comp x hu.hasFDerivAt
  have h := (h0.mul hu1).sub (h1.mul hu0)
  change HasFDerivAt (angularField u) _ x at h
  rw [h.fderiv]
  simp [cartesianAngularMomentum, coordinateProjection]
  ring

/-- The position carrier contributes twice the axial vorticity to the scalar Laplacian. -/
theorem laplacian_angularField (u : InitialVelocity) (hu : ContDiff ℝ 2 u) (x : Space) :
    cartesianAngularMomentum x (Δ u x) =
      Δ (angularField u) x - 2 * axialVorticity u x := by
  have hc (i : Fin 3) : ContDiff ℝ 2 (fun y ↦ u y i) :=
    (coordinateProjection i).contDiff.comp hu
  have hl (i : Fin 3) : Δ (fun y ↦ u y i) x = (Δ u x) i := by
    simpa [Function.comp_def] using hu.contDiffAt.laplacian_CLM_comp_left
      (l := EuclideanSpace.proj i) (x := x)
  have hprod (i j : Fin 3) :
      Δ (fun y : Space ↦ y i * u y j) x =
        x i * (Δ u x) j + 2 * gradient (fun y ↦ u y j) x i := by
    have hd : fderiv ℝ (fun y : Space ↦ y i) x = coordinateProjection i :=
      (coordinateProjection i).fderiv
    rw [laplacian_product (fun y : Space ↦ y i) (fun y ↦ u y j)
      (coordinateProjection i).contDiff (hc j) x,
      laplacian_coordinate, hl, inner_gradient_left, hd]
    simp [coordinateProjection]
  have hdiff : Δ (angularField u) x =
      Δ (fun y : Space ↦ y 0 * u y 1) x - Δ (fun y : Space ↦ y 1 * u y 0) x := by
    exact (((coordinateProjection 0).contDiff.mul (hc 1)).contDiffAt.laplacian_sub
      ((coordinateProjection 1).contDiff.mul (hc 0)).contDiffAt)
  rw [hdiff, hprod, hprod]
  unfold cartesianAngularMomentum axialVorticity
  ring

def momentumResidual (U : ℝ → InitialVelocity) (P : ℝ → Space → ℝ)
    (alpha beta mu : ℝ → ℝ) (t : ℝ) (x : Space) : Space :=
  deriv (fun τ ↦ U τ x) t + fderiv ℝ (U t) x (U t x) +
    beta t • fderiv ℝ (U t) x x + alpha t • U t x +
    gradient (P t) x - mu t • Δ (U t) x

/-- The source-bound MFR1 equation, with arbitrary rescaled pressure. -/
theorem momentumResidual_of_physical_solution
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial (fun _ _ ↦ 0) velocity pressure)
    (alpha beta length normalizer clock : ℝ → ℝ) (t : ℝ)
    (ht : clock t ∈ Ioo 0 T)
    (hell : HasDerivAt length (-beta t * length t) t)
    (hq : HasDerivAt normalizer (-alpha t * normalizer t) t)
    (hclock : HasDerivAt clock (length t * normalizer t) t)
    (hellne : length t ≠ 0) (hqne : normalizer t ≠ 0) (x : Space) :
    momentumResidual
      (fun τ y ↦ rescaledVelocity (fun _ ↦ 0) length normalizer clock velocity y τ)
      (fun τ y ↦ rescaledPressure (fun _ ↦ 0) length normalizer clock pressure y τ)
      alpha beta (fun τ ↦ nu * normalizer τ / length τ) t x = 0 := by
  have h := Soma.Holonics.Millennium.NavierStokesDynamicRescaling.OpenSmoothSolutionOn.rescaled_momentum
    solution (fun _ ↦ 0) length normalizer clock x t 0
    (-beta t * length t) (-alpha t * normalizer t) ht (hasDerivAt_const t 0)
    hell hq hclock hqne hellne
  have hl : -beta t * length t / length t = -beta t := by field_simp
  have hn : -alpha t * normalizer t / normalizer t = -alpha t := by field_simp
  simp only [hl, hn, map_zero, smul_zero, add_zero] at h
  unfold momentumResidual
  rw [h]
  module

theorem joint_velocity_derivative (U : ℝ → InitialVelocity) (t : ℝ) (x d : Space)
    (hU : DifferentiableAt ℝ (fun q : ℝ × Space ↦ U q.1 q.2) (t, x)) :
    fderiv ℝ (fun q : ℝ × Space ↦ U q.1 q.2) (t, x) (1, d) =
      deriv (fun τ ↦ U τ x) t + fderiv ℝ (U t) x d := by
  have ht := hU.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id' t).prodMk (hasDerivAt_const t x))
  have hx := hU.hasFDerivAt.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
  change HasDerivAt (fun τ ↦ U τ x) _ t at ht
  change HasFDerivAt (U t) _ x at hx
  rw [ht.deriv, hx.fderiv]
  change _ = fderiv ℝ (fun q : ℝ × Space ↦ U q.1 q.2) (t, x) (1, 0) +
    fderiv ℝ (fun q : ℝ × Space ↦ U q.1 q.2) (t, x) (0, d)
  rw [← map_add]
  congr 1
  simp

/-- Actual Cartesian trajectories retain pressure torque even when a local velocity chart is
axisymmetric. The complete PDE residual remains an oriented source term. -/
theorem hasDerivAt_angularField (U : ℝ → InitialVelocity) (P : ℝ → Space → ℝ)
    (alpha beta mu : ℝ → ℝ) (path : ℝ → Space) (t : ℝ)
    (hU : DifferentiableAt ℝ (fun q : ℝ × Space ↦ U q.1 q.2) (t, path t))
    (hpath : HasDerivAt path (U t (path t) + beta t • path t) t) :
    HasDerivAt (fun τ ↦ angularField (U τ) (path τ))
      (cartesianAngularMomentum (path t) (momentumResidual U P alpha beta mu t (path t)) -
        pressureTorque (P t) (path t) +
        mu t * cartesianAngularMomentum (path t) (Δ (U t) (path t)) -
        (alpha t - beta t) * angularField (U t) (path t)) t := by
  let d := U t (path t) + beta t • path t
  have hp : HasDerivAt (fun τ ↦ (τ, path τ)) (1, d) t :=
    (hasDerivAt_id' t).prodMk hpath
  have hv := hU.hasFDerivAt.comp_hasDerivAt t hp
  change HasDerivAt (fun τ ↦ U τ (path τ)) _ t at hv
  rw [joint_velocity_derivative U t (path t) d hU] at hv
  have hx0 := (coordinateProjection 0).hasFDerivAt.comp_hasDerivAt t hpath
  have hx1 := (coordinateProjection 1).hasFDerivAt.comp_hasDerivAt t hpath
  have hu0 := (coordinateProjection 0).hasFDerivAt.comp_hasDerivAt t hv
  have hu1 := (coordinateProjection 1).hasFDerivAt.comp_hasDerivAt t hv
  have h := (hx0.mul hu1).sub (hx1.mul hu0)
  change HasDerivAt (fun τ ↦ angularField (U τ) (path τ)) _ t at h
  convert h using 1
  simp [angularField, pressureTorque, cartesianAngularMomentum, momentumResidual,
    coordinateProjection, d, map_add, map_smul]
  ring

/-- The exact PDE supplies the full source along its renormalized trajectory. -/
theorem hasDerivAt_angularField_of_momentum (U : ℝ → InitialVelocity) (P : ℝ → Space → ℝ)
    (alpha beta mu : ℝ → ℝ) (path : ℝ → Space) (t : ℝ)
    (hU : DifferentiableAt ℝ (fun q : ℝ × Space ↦ U q.1 q.2) (t, path t))
    (hs : ContDiff ℝ 2 (U t))
    (hpath : HasDerivAt path (U t (path t) + beta t • path t) t)
    (hPDE : momentumResidual U P alpha beta mu t (path t) = 0) :
    HasDerivAt (fun τ ↦ angularField (U τ) (path τ))
      (mu t * (Δ (angularField (U t)) (path t) - 2 * axialVorticity (U t) (path t)) -
        pressureTorque (P t) (path t) -
        (alpha t - beta t) * angularField (U t) (path t)) t := by
  have h := hasDerivAt_angularField U P alpha beta mu path t hU hpath
  rw [hPDE, laplacian_angularField (U t) hs (path t)] at h
  convert h using 1 <;> simp [cartesianAngularMomentum] <;> ring

/-- Reconstruction cancels the normalization current and keeps the exterior torque. -/
theorem physical_factor_with_torque (nu alpha beta D torque : ℝ)
    (length normalizer L : ℝ → ℝ) (t : ℝ)
    (hell : HasDerivAt length (-beta * length t) t)
    (hq : HasDerivAt normalizer (-alpha * normalizer t) t)
    (hellne : length t ≠ 0) (hqne : normalizer t ≠ 0)
    (hL : HasDerivAt L
      ((nu * normalizer t / length t) * D - torque - (alpha - beta) * L t) t) :
    HasDerivAt (fun τ ↦ (length τ / normalizer τ) * L τ)
      (nu * D - (length t / normalizer t) * torque) t := by
  have h := (hell.div hq hqne).mul hL
  convert h using 1 <;> first | rfl |
    (simp only [Pi.div_apply, Pi.mul_apply]; field_simp [hellne, hqne] <;> ring)

#print axioms laplacian_angularField
#print axioms pressureTorque_eq_angular_derivative
#print axioms rescaled_pressureTorque
#print axioms momentumResidual_of_physical_solution
#print axioms hasDerivAt_angularField
#print axioms hasDerivAt_angularField_of_momentum
#print axioms physical_factor_with_torque

end Soma.Holonics.Millennium.NavierStokesExteriorTorque
