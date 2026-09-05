import ElementaryHolonics.Millennium.NavierStokesExteriorTorque
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Compact positive maxima for the Cartesian angular momentum

This owner extracts a genuine maximum from compact support of the Cartesian field
`x ↦ s * Omega (s,z)`, where `s = x₀² + x₁²`.  The resulting Fermat derivative is then read back
through the existing meridional chart, retaining the axis and avoiding any radius division.
-/

noncomputable section

open ContDiff Set Filter InnerProductSpace
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesCompactMaximum

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesExteriorTorque
open Soma.Holonics.Millennium.NavierStokesSwirlCirculation
open Soma.Holonics.Millennium.NavierStokesSwirlDiffusion

/-- The actual Cartesian angular-momentum scalar induced by a meridional swirl profile. -/
def cartesianAngularMomentumProfile (Omega : MeridionalProfile) : Space → ℝ :=
  fun x ↦ angularMomentum Omega (meridionalChart x)

theorem continuous_cartesianAngularMomentumProfile
    (Omega : MeridionalProfile) (hOmega : ContDiff ℝ 2 Omega) :
    Continuous (cartesianAngularMomentumProfile Omega) := by
  have hangular : Continuous (angularMomentum Omega) := by
    exact continuous_fst.mul hOmega.continuous
  exact hangular.comp meridionalChart_contDiff.continuous

/-- A positive compactly-supported Cartesian angular momentum has a positive global maximum whose
meridional profile derivative vanishes. -/
theorem exists_positive_compact_angularMomentum_max
    (Omega : MeridionalProfile) (hOmega : ContDiff ℝ 2 Omega)
    (hcompact : HasCompactSupport (cartesianAngularMomentumProfile Omega))
    (x0 : Space) (hx0 : 0 < cartesianAngularMomentumProfile Omega x0) :
    ∃ x : Space,
      cartesianAngularMomentumProfile Omega x0 ≤ cartesianAngularMomentumProfile Omega x ∧
      0 < cartesianAngularMomentumProfile Omega x ∧
      IsLocalMax (cartesianAngularMomentumProfile Omega) x ∧
      fderiv ℝ (angularMomentum Omega) (meridionalChart x) = 0 ∧
      0 < (meridionalChart x).1 := by
  let L : Space → ℝ := cartesianAngularMomentumProfile Omega
  have hL : Continuous L := continuous_cartesianAngularMomentumProfile Omega hOmega
  have hx0support : x0 ∈ Function.support L := Function.mem_support.mpr hx0.ne'
  have hx0tsupport : x0 ∈ tsupport L := subset_tsupport L hx0support
  have htscompact : IsCompact (tsupport L) := hcompact.isCompact
  have htsnonempty : (tsupport L).Nonempty := ⟨x0, hx0tsupport⟩
  obtain ⟨x, hxtsupport, hmax⟩ :=
    htscompact.exists_isMaxOn htsnonempty hL.continuousOn
  have hmax' : ∀ y, L y ≤ L x := by
    intro y
    by_cases hy : y ∈ tsupport L
    · exact (isMaxOn_iff.mp hmax) y hy
    · rw [image_eq_zero_of_notMem_tsupport hy]
      exact (le_of_lt hx0).trans ((isMaxOn_iff.mp hmax) x0 hx0tsupport)
  have hlocal : IsLocalMax L x := Filter.Eventually.of_forall hmax'
  have hpositive : 0 < L x := lt_of_lt_of_le hx0 ((isMaxOn_iff.mp hmax) x0 hx0tsupport)
  have hspositive : 0 < (meridionalChart x).1 := by
    have hsnonnegative : 0 ≤ (meridionalChart x).1 := by
      simp [meridionalChart]
      positivity
    by_contra hs
    have hszero : (meridionalChart x).1 = 0 := le_antisymm (le_of_not_gt hs) hsnonnegative
    have hLzero : L x = 0 := by
      simp [L, cartesianAngularMomentumProfile, angularMomentum, hszero]
    linarith
  have hLderiv : fderiv ℝ L x = 0 := hlocal.fderiv_eq_zero
  have hOmegaDiff : DifferentiableAt ℝ (angularMomentum Omega) (meridionalChart x) := by
    have hOmega' : DifferentiableAt ℝ Omega (meridionalChart x) :=
      (hOmega.differentiable (by norm_num)) (meridionalChart x)
    exact (hasFDerivAt_fst (𝕜 := ℝ)).mul hOmega'.hasFDerivAt |>.differentiableAt
  have hrad := congrArg (fun D : Space →L[ℝ] ℝ =>
      D (assemble (x 0) (x 1) 0)) hLderiv
  have haxial := congrArg (fun D : Space →L[ℝ] ℝ =>
      D (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) hLderiv
  have hradzero : radialDerivative (angularMomentum Omega) (meridionalChart x) = 0 := by
    rw [show L = (fun y ↦ angularMomentum Omega (meridionalChart y)) from rfl,
      profileLift_fderiv_apply (angularMomentum Omega) x (assemble (x 0) (x 1) 0)
        hOmegaDiff] at hrad
    simp [assemble] at hrad
    rcases hrad with hzero | hrad
    · exfalso
      have hspos' : 0 < x 0 ^ 2 + x 1 ^ 2 := by
        simpa [meridionalChart] using hspositive
      nlinarith [hspos']
    · exact hrad
  have haxialzero : axialDerivative (angularMomentum Omega) (meridionalChart x) = 0 := by
    rw [show L = (fun y ↦ angularMomentum Omega (meridionalChart y)) from rfl,
      profileLift_fderiv_apply (angularMomentum Omega) x
        (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) hOmegaDiff] at haxial
    simp at haxial
    exact haxial
  have hprofilezero : fderiv ℝ (angularMomentum Omega) (meridionalChart x) = 0 := by
    apply ContinuousLinearMap.ext
    rintro ⟨a, b⟩
    simp only [profile_fderiv_apply]
    rw [hradzero, haxialzero]
    simp
  exact ⟨x, hmax' x0, hpositive, hlocal, hprofilezero, hspositive⟩

#print axioms exists_positive_compact_angularMomentum_max

end Soma.Holonics.Millennium.NavierStokesCompactMaximum
