import ElementaryHolonics.Millennium.NavierStokesMovingSwirlCirculation
import ElementaryHolonics.Millennium.NavierStokesSwirlDiffusion
import ElementaryHolonics.Millennium.NavierStokesDynamicRescaling

/-!
# The moving swirl law returns its actual Cartesian viscosity and physical scale

The joint profile constructs the velocity and its time derivative. The complete centred
Cartesian momentum residual is projected to angular momentum, where pressure cancels and
viscosity is the actual vector Laplacian. The physical factor is length/normalizer, in the
convention of MFR1. No existence or stability of the chosen profile is assumed to be proved.
-/

noncomputable section

open ContDiff Set InnerProductSpace
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesViscousSwirlBalance

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesSwirlCirculation
open Soma.Holonics.Millennium.NavierStokesMovingSwirlCirculation
open Soma.Holonics.Millennium.NavierStokesSwirlDiffusion
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesDynamicRescaling

def profileVelocity (V Omega W : SpacetimeProfile) (t : ℝ) : InitialVelocity :=
  axisymmetricVelocity (timeSlice V t) (timeSlice Omega t) (timeSlice W t)

theorem fixedPoint_time_hasDerivAt (f : SpacetimeProfile) (t : ℝ) (p : ℝ × ℝ)
    (hf : DifferentiableAt ℝ f (t, p)) :
    HasDerivAt (fun τ ↦ f (τ, p)) (timeDerivative f t p) t := by
  have hp : HasDerivAt (fun τ : ℝ ↦ (τ, p)) (1, (0, 0)) t :=
    (hasDerivAt_id' t).prodMk (hasDerivAt_const t p)
  exact hf.hasFDerivAt.comp_hasDerivAt t hp

theorem profileVelocity_time_hasDerivAt (V Omega W : SpacetimeProfile) (t : ℝ) (x : Space)
    (hV : DifferentiableAt ℝ V (t, meridionalChart x))
    (hOmega : DifferentiableAt ℝ Omega (t, meridionalChart x))
    (hW : DifferentiableAt ℝ W (t, meridionalChart x)) :
    HasDerivAt (fun τ ↦ profileVelocity V Omega W τ x)
      (assemble
        (x 0 * timeDerivative V t (meridionalChart x) - x 1 * timeDerivative Omega t (meridionalChart x))
        (x 1 * timeDerivative V t (meridionalChart x) + x 0 * timeDerivative Omega t (meridionalChart x))
        (timeDerivative W t (meridionalChart x))) t := by
  have hv := fixedPoint_time_hasDerivAt V t (meridionalChart x) hV
  have ho := fixedPoint_time_hasDerivAt Omega t (meridionalChart x) hOmega
  have hw := fixedPoint_time_hasDerivAt W t (meridionalChart x) hW
  exact ((((hv.const_mul (x 0)).sub (ho.const_mul (x 1))).smul_const
    (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : Space)).add
    (((hv.const_mul (x 1)).add (ho.const_mul (x 0))).smul_const
      (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : Space))).add
    (hw.smul_const (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : Space))

def centredMomentumResidual (V Omega W : SpacetimeProfile)
    (P : ℝ → MeridionalProfile) (alpha beta mu : ℝ → ℝ) (t : ℝ) (x : Space) : Space :=
  deriv (fun τ ↦ profileVelocity V Omega W τ x) t +
    (fderiv ℝ (profileVelocity V Omega W t) x (profileVelocity V Omega W t x) +
      beta t • fderiv ℝ (profileVelocity V Omega W t) x x +
      alpha t • profileVelocity V Omega W t x) +
    gradient (fun y ↦ P t (meridionalChart y)) x - mu t • Δ (profileVelocity V Omega W t) x

/-- MFR1's actual unforced physical solution pays the centred profile equation, with its
physical clock and reciprocal velocity normalizer retained. -/
theorem centredMomentumResidual_of_physical_solution
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial (fun _ _ ↦ 0) velocity pressure)
    (V Omega W : SpacetimeProfile) (P : ℝ → MeridionalProfile)
    (alpha beta length normalizer clock : ℝ → ℝ) (t : ℝ)
    (hU : ∀ y τ, rescaledVelocity (fun _ ↦ 0) length normalizer clock velocity y τ =
      profileVelocity V Omega W τ y)
    (hP : ∀ y τ, rescaledPressure (fun _ ↦ 0) length normalizer clock pressure y τ =
      P τ (meridionalChart y))
    (ht : clock t ∈ Ioo 0 T)
    (hell : HasDerivAt length (-beta t * length t) t)
    (hq : HasDerivAt normalizer (-alpha t * normalizer t) t)
    (hclock : HasDerivAt clock (length t * normalizer t) t)
    (hellne : length t ≠ 0) (hqne : normalizer t ≠ 0) (x : Space) :
    centredMomentumResidual V Omega W P alpha beta
      (fun τ ↦ nu * normalizer τ / length τ) t x = 0 := by
  have h := Soma.Holonics.Millennium.NavierStokesDynamicRescaling.OpenSmoothSolutionOn.rescaled_momentum
    solution (fun _ ↦ 0) length normalizer clock x t 0
    (-beta t * length t) (-alpha t * normalizer t) ht (hasDerivAt_const t 0)
    hell hq hclock hqne hellne
  dsimp only at h
  simp_rw [hU, hP] at h
  have htime : rescaledVelocity (fun _ ↦ 0) length normalizer clock velocity x =
      fun τ ↦ profileVelocity V Omega W τ x := funext (hU x)
  rw [htime] at h
  have hl : -beta t * length t / length t = -beta t := by field_simp
  have hq' : -alpha t * normalizer t / normalizer t = -alpha t := by field_simp
  simp only [hl, hq', map_zero, smul_zero, add_zero] at h
  change deriv (fun τ ↦ profileVelocity V Omega W τ x) t +
    fderiv ℝ (profileVelocity V Omega W t) x (profileVelocity V Omega W t x) =
      (nu * normalizer t / length t) • Δ (profileVelocity V Omega W t) x -
      gradient (fun y ↦ P t (meridionalChart y)) x +
      (-beta t) • fderiv ℝ (profileVelocity V Omega W t) x x +
      (-alpha t) • profileVelocity V Omega W t x at h
  unfold centredMomentumResidual
  change deriv (fun τ ↦ profileVelocity V Omega W τ x) t +
    (fderiv ℝ (profileVelocity V Omega W t) x (profileVelocity V Omega W t x) +
      beta t • fderiv ℝ (profileVelocity V Omega W t) x x +
      alpha t • profileVelocity V Omega W t x) +
    gradient (fun y ↦ P t (meridionalChart y)) x -
      (nu * normalizer t / length t) • Δ (profileVelocity V Omega W t) x = 0
  calc
    _ = (deriv (fun τ ↦ profileVelocity V Omega W τ x) t +
      fderiv ℝ (profileVelocity V Omega W t) x (profileVelocity V Omega W t x)) +
      beta t • fderiv ℝ (profileVelocity V Omega W t) x x +
      alpha t • profileVelocity V Omega W t x +
      gradient (fun y ↦ P t (meridionalChart y)) x -
      (nu * normalizer t / length t) • Δ (profileVelocity V Omega W t) x := by module
    _ = 0 := by
      rw [h]
      module

/-- The full Cartesian equation supplies the moving swirl source, including its viscosity. -/
theorem centredMomentumResidual_angular_projection (V Omega W : SpacetimeProfile)
    (P : ℝ → MeridionalProfile) (alpha beta mu : ℝ → ℝ) (t : ℝ) (x : Space)
    (hV : DifferentiableAt ℝ V (t, meridionalChart x))
    (hOmega : DifferentiableAt ℝ Omega (t, meridionalChart x))
    (hW : DifferentiableAt ℝ W (t, meridionalChart x))
    (hVs : ContDiff ℝ 2 (timeSlice V t)) (hOs : ContDiff ℝ 2 (timeSlice Omega t))
    (hWs : ContDiff ℝ 2 (timeSlice W t))
    (hP : DifferentiableAt ℝ (P t) (meridionalChart x)) :
    x 0 * centredMomentumResidual V Omega W P alpha beta mu t x 1 -
      x 1 * centredMomentumResidual V Omega W P alpha beta mu t x 0 =
      (meridionalChart x).1 * movingSwirlResidual Omega alpha beta
        (fun τ ↦ timeSlice V τ) (fun τ ↦ timeSlice W τ) t (meridionalChart x) -
      mu t * meridionalDiffusion (angularMomentum (timeSlice Omega t)) (meridionalChart x) := by
  have htime := profileVelocity_time_hasDerivAt V Omega W t x hV hOmega hW
  have hspace := normalizedMomentum_axisymmetricVelocity (alpha t) (beta t)
    (timeSlice V t) (timeSlice Omega t) (timeSlice W t) x
    (hVs.differentiable (by norm_num) _) (hOs.differentiable (by norm_num) _)
    (hWs.differentiable (by norm_num) _)
  have hpressure := gradient_axisymmetricPressure (P t) x hP
  have hvisc := cartesian_laplacian_angularMomentum (timeSlice V t) (timeSlice Omega t)
    (timeSlice W t) hVs hOs hWs x
  unfold centredMomentumResidual
  simp only [htime.deriv]
  simp only [profileVelocity, hspace, hpressure]
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    assemble_zero, assemble_one]
  unfold movingSwirlResidual timeSliceV timeSliceW
  simp only [profileVelocity] at hvisc
  simp only [meridionalChart] at hvisc ⊢
  linear_combination -mu t * hvisc

/-- An actual meridional trajectory inherits the viscous circulation law from the complete
Cartesian PDE. Its radius-squared coordinate is reconstructed without dividing at the axis. -/
theorem hasDerivAt_viscous_angularMomentum (V Omega W : SpacetimeProfile)
    (P : ℝ → MeridionalProfile) (alpha beta mu : ℝ → ℝ)
    (trajectory : ℝ → ℝ × ℝ) (t : ℝ)
    (hV : DifferentiableAt ℝ V (t, trajectory t))
    (hOmega : DifferentiableAt ℝ Omega (t, trajectory t))
    (hW : DifferentiableAt ℝ W (t, trajectory t))
    (hVs : ContDiff ℝ 2 (timeSlice V t)) (hOs : ContDiff ℝ 2 (timeSlice Omega t))
    (hWs : ContDiff ℝ 2 (timeSlice W t)) (hP : DifferentiableAt ℝ (P t) (trajectory t))
    (htrajectory : HasDerivAt trajectory
      (meridionalDrift (beta t) (timeSlice V t) (timeSlice W t) (trajectory t)) t)
    (hs : 0 ≤ (trajectory t).1)
    (hPDE : ∀ x, centredMomentumResidual V Omega W P alpha beta mu t x = 0) :
    HasDerivAt (fun τ ↦ (trajectory τ).1 * Omega (τ, trajectory τ))
      (mu t * meridionalDiffusion (angularMomentum (timeSlice Omega t)) (trajectory t) -
        (alpha t - beta t) * ((trajectory t).1 * Omega (t, trajectory t))) t := by
  let x : Space := assemble (Real.sqrt (trajectory t).1) 0 (trajectory t).2
  have hx : meridionalChart x = trajectory t := by
    ext <;> simp [x, meridionalChart, Real.sq_sqrt hs]
  have hprojection := centredMomentumResidual_angular_projection V Omega W P alpha beta mu t x
    (by simpa [hx] using hV) (by simpa [hx] using hOmega) (by simpa [hx] using hW)
    hVs hOs hWs (by simpa [hx] using hP)
  rw [hPDE x] at hprojection
  simp only [PiLp.zero_apply, mul_zero, sub_self, hx] at hprojection
  have h := hasDerivAt_movingAngularMomentum Omega alpha beta
    (fun τ ↦ timeSlice V τ) (fun τ ↦ timeSlice W τ) trajectory t hOmega htrajectory
  change HasDerivAt _ ((trajectory t).1 * movingSwirlResidual Omega alpha beta
    (fun τ ↦ timeSlice V τ) (fun τ ↦ timeSlice W τ) t (trajectory t) - _) t at h
  have hsource : (trajectory t).1 * movingSwirlResidual Omega alpha beta
      (fun τ ↦ timeSlice V τ) (fun τ ↦ timeSlice W τ) t (trajectory t) =
      mu t * meridionalDiffusion (angularMomentum (timeSlice Omega t)) (trajectory t) := by
    linarith
  rw [hsource] at h
  exact h

def cartesianAngularMomentum (position velocity : Space) : ℝ :=
  position 0 * velocity 1 - position 1 * velocity 0

/-- The physical angular momentum is reconstructed with length/normalizer, using the exact
MFR1 rescaled velocity. The normalizer is the reciprocal physical velocity amplitude. -/
theorem rescaled_angularMomentum_reconstruct (length normalizer clock : ℝ → ℝ)
    (velocity : VelocityField) (y : Space) (t : ℝ) (hq : normalizer t ≠ 0) :
    cartesianAngularMomentum (length t • y) (velocity (length t • y) (clock t)) =
      (length t / normalizer t) * cartesianAngularMomentum y
        (Soma.Holonics.Millennium.NavierStokesDynamicRescaling.rescaledVelocity
          (fun _ ↦ 0) length normalizer clock velocity y t) := by
  unfold cartesianAngularMomentum
    Soma.Holonics.Millennium.NavierStokesDynamicRescaling.rescaledVelocity
  simp only [PiLp.smul_apply, smul_eq_mul, zero_add]
  field_simp <;> ring

theorem physical_factor_hasDerivAt (nu alpha beta D : ℝ)
    (length normalizer L : ℝ → ℝ) (t : ℝ)
    (hell : HasDerivAt length (-beta * length t) t)
    (hq : HasDerivAt normalizer (-alpha * normalizer t) t)
    (hellne : length t ≠ 0) (hqne : normalizer t ≠ 0)
    (hL : HasDerivAt L ((nu * normalizer t / length t) * D - (alpha - beta) * L t) t) :
    HasDerivAt (fun τ ↦ (length τ / normalizer τ) * L τ) (nu * D) t := by
  have h := (hell.div hq hqne).mul hL
  convert h using 1 <;> first | rfl |
    (simp only [Pi.div_apply, Pi.mul_apply]; field_simp [hellne, hqne] <;> ring)

/-- In a regular centred MFR1 chart the normalizing current cancels after reconstruction.
The remaining source is the actual viscous angular-momentum diffusion. -/
theorem hasDerivAt_reconstructed_viscous_circulation (nu : ℝ)
    (V Omega W : SpacetimeProfile) (P : ℝ → MeridionalProfile)
    (alpha beta length normalizer : ℝ → ℝ) (trajectory : ℝ → ℝ × ℝ) (t : ℝ)
    (hV : DifferentiableAt ℝ V (t, trajectory t))
    (hOmega : DifferentiableAt ℝ Omega (t, trajectory t))
    (hW : DifferentiableAt ℝ W (t, trajectory t))
    (hVs : ContDiff ℝ 2 (timeSlice V t)) (hOs : ContDiff ℝ 2 (timeSlice Omega t))
    (hWs : ContDiff ℝ 2 (timeSlice W t)) (hP : DifferentiableAt ℝ (P t) (trajectory t))
    (htrajectory : HasDerivAt trajectory
      (meridionalDrift (beta t) (timeSlice V t) (timeSlice W t) (trajectory t)) t)
    (hs : 0 ≤ (trajectory t).1)
    (hPDE : ∀ x, centredMomentumResidual V Omega W P alpha beta
      (fun τ ↦ nu * normalizer τ / length τ) t x = 0)
    (hell : HasDerivAt length (-beta t * length t) t)
    (hq : HasDerivAt normalizer (-alpha t * normalizer t) t)
    (hellne : length t ≠ 0) (hqne : normalizer t ≠ 0) :
    HasDerivAt (fun τ ↦ (length τ / normalizer τ) *
      ((trajectory τ).1 * Omega (τ, trajectory τ)))
      (nu * meridionalDiffusion (angularMomentum (timeSlice Omega t)) (trajectory t)) t := by
  have h := hasDerivAt_viscous_angularMomentum V Omega W P alpha beta
    (fun τ ↦ nu * normalizer τ / length τ) trajectory t hV hOmega hW hVs hOs hWs hP
    htrajectory hs hPDE
  exact physical_factor_hasDerivAt nu (alpha t) (beta t)
    (meridionalDiffusion (angularMomentum (timeSlice Omega t)) (trajectory t))
    length normalizer (fun τ ↦ (trajectory τ).1 * Omega (τ, trajectory τ)) t hell hq hellne hqne h

#print axioms profileVelocity_time_hasDerivAt
#print axioms centredMomentumResidual_of_physical_solution
#print axioms centredMomentumResidual_angular_projection
#print axioms hasDerivAt_viscous_angularMomentum
#print axioms rescaled_angularMomentum_reconstruct
#print axioms physical_factor_hasDerivAt
#print axioms hasDerivAt_reconstructed_viscous_circulation

end Soma.Holonics.Millennium.NavierStokesViscousSwirlBalance
