import ElementaryHolonics.Millennium.NavierStokesAxisymmetricChart

/-!
# Axisymmetric angular momentum circulation

The meridional drift transports the actual angular momentum `s*Omega`, where `s` is the squared
radius in the meridional chart.  This owner composes the Cartesian axisymmetric chart and keeps
the axis (`s=0`) in the formulas; no division by radius, global orbit, or ODE existence premise
is introduced.
-/

noncomputable section

open ContDiff Set

namespace Soma.Holonics.Millennium.NavierStokesSwirlCirculation

open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart

/-- Actual angular momentum in the meridional `(s,z)` chart. -/
def angularMomentum (Omega : MeridionalProfile) : MeridionalProfile :=
  (fun p : ℝ × ℝ ↦ p.1) * Omega

/-- Meridional drift of the normalized axisymmetric flow. -/
def meridionalDrift (beta : ℝ) (V W : MeridionalProfile) (p : ℝ × ℝ) : ℝ × ℝ :=
  (2 * p.1 * (V p + beta), W p + beta * p.2)

theorem angularMomentum_fderiv_apply
    (alpha beta : ℝ) (V Omega W : MeridionalProfile) (p : ℝ × ℝ)
  (hOmega : DifferentiableAt ℝ Omega p) :
    fderiv ℝ (angularMomentum Omega) p (meridionalDrift beta V W p) +
        (alpha - beta) * angularMomentum Omega p =
      p.1 * swirlMomentum alpha beta V Omega W p := by
  have hprod := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).mul hOmega.hasFDerivAt
  unfold angularMomentum
  rw [hprod.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  rw [profile_fderiv_apply Omega p (meridionalDrift beta V W p).1
    (meridionalDrift beta V W p).2]
  simp [angularMomentum, meridionalDrift, swirlMomentum]
  ring

theorem hasDerivAt_angularMomentum_along_meridionalDrift
    (alpha beta : ℝ) (V Omega W : MeridionalProfile)
    (trajectory : ℝ → ℝ × ℝ) (t : ℝ)
    (hOmega : DifferentiableAt ℝ Omega (trajectory t))
    (htrajectory : HasDerivAt trajectory
      (meridionalDrift beta V W (trajectory t)) t) :
    HasDerivAt (fun τ ↦ angularMomentum Omega (trajectory τ))
      ((trajectory t).1 * swirlMomentum alpha beta V Omega W (trajectory t) -
        (alpha - beta) * angularMomentum Omega (trajectory t)) t := by
  have hprod := (hasFDerivAt_fst (𝕜 := ℝ) (p := trajectory t)).mul
    hOmega.hasFDerivAt
  have hcomp := hprod.comp_hasDerivAt t htrajectory
  have hidentity := angularMomentum_fderiv_apply alpha beta V Omega W
    (trajectory t) hOmega
  have hidentity' := hidentity
  rw [show angularMomentum Omega = (fun q : ℝ × ℝ ↦ q.1) * Omega by rfl,
    hprod.fderiv] at hidentity'
  have hderiv :
      ((trajectory t).1 • fderiv ℝ Omega (trajectory t) +
        Omega (trajectory t) • ContinuousLinearMap.fst ℝ ℝ ℝ)
          (meridionalDrift beta V W (trajectory t)) =
        (trajectory t).1 * swirlMomentum alpha beta V Omega W (trajectory t) -
          (alpha - beta) * ((fun q : ℝ × ℝ ↦ q.1) * Omega) (trajectory t) := by
    linarith [hidentity']
  rw [hderiv] at hcomp
  simpa [angularMomentum, Function.comp_def] using hcomp

theorem stationary_off_axis_swirl_forces_alpha_eq_beta
    (alpha beta : ℝ) (V Omega W : MeridionalProfile) (p : ℝ × ℝ)
    (hOmega : DifferentiableAt ℝ Omega p)
    (hs : p.1 ≠ 0) (hOmega_ne : Omega p ≠ 0)
    (hdrift : meridionalDrift beta V W p = 0)
    (hswirl : swirlMomentum alpha beta V Omega W p = 0) :
    alpha = beta := by
  have hidentity := angularMomentum_fderiv_apply alpha beta V Omega W p hOmega
  rw [hdrift, map_zero, hswirl, mul_zero] at hidentity
  have hprod : (alpha - beta) * angularMomentum Omega p = 0 := by simpa using hidentity
  have hnonzero : angularMomentum Omega p ≠ 0 := mul_ne_zero hs hOmega_ne
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hnonzero)

#print axioms angularMomentum_fderiv_apply
#print axioms hasDerivAt_angularMomentum_along_meridionalDrift
#print axioms stationary_off_axis_swirl_forces_alpha_eq_beta

end Soma.Holonics.Millennium.NavierStokesSwirlCirculation
