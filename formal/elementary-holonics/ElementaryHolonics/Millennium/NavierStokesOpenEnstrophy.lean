import ElementaryHolonics.Millennium.NavierStokesOpenLifespan
import ElementaryHolonics.Millennium.NavierStokesIntegralEnstrophy

/-!
# Enstrophy transport on a genuine open Navier--Stokes lifespan

This module attaches the time-dependent integrating-factor estimates to
`OpenPeriodicSolutionOn T`, whose time population is `Ico 0 T`.  Each requested time lies in a
strictly interior closed slab, so the proof reuses the closed-slab analysis through
`OpenPeriodicSolutionOn.toClosedInterior` without asserting any field value or smoothness at `T`.

The accumulated-control receipt is uniform over every `t < T`: a continuous spatial-Jacobian
envelope with uniformly bounded accumulated integral and nonpositive curl-forcing work bounds the
periodic enstrophy by one explicit constant throughout `Ico a T`.

This is only a Jacobian-to-enstrophy estimate.  It is not the Beale--Kato--Majda vorticity
criterion, does not control a continuation norm, and does not construct or assume an extension
past `T`.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Real Set
open scoped Interval Laplacian

namespace Soma.Holonics.Millennium.NavierStokesOpenLifespan

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux

/-! ## Compact interior attachment -/

/-- The exact time-dependent Duhamel--Grönwall estimate on an interior interval of an open
lifespan.  The auxiliary closed carrier ends strictly between `b` and `T`; it therefore adds no
terminal-face hypothesis at `T`. -/
theorem OpenPeriodicSolutionOn.enstrophy_le_timeDependentGronwallBound
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (hnu : 0 ≤ nu)
    (K F : ℝ → ℝ) (hKcontinuous : Continuous K) (hFcontinuous : Continuous F)
    (hK : ∀ t ∈ Icc a b, ∀ x ∈ unitCube,
      ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ K t)
    (hforce : ∀ t ∈ Icc a b,
      periodicCurlForcingWork force velocity t ≤ F t) :
    ∀ t ∈ Icc a b,
      periodicEnstrophy velocity t ≤
        timeDependentGronwallBound a (periodicEnstrophy velocity a)
          (fun s => 2 * K s) F t := by
  let S : ℝ := (b + T) / 2
  have hbS : b < S := by
    dsimp [S]
    linarith
  have hST : S < T := by
    dsimp [S]
    linarith
  have hS : 0 < S := (lt_of_lt_of_le ha hab).trans hbS
  exact periodicSolutionOn_enstrophy_le_timeDependentGronwallBound
    (solution.toClosedInterior hS hST) ha hab hbS hnu K F
      hKcontinuous hFcontinuous hK hforce

/-- With nonpositive curl-forcing work, the actual accumulated Jacobian envelope controls
enstrophy on every compact interval strictly inside the open lifespan. -/
theorem OpenPeriodicSolutionOn.enstrophy_le_exp_integral_jacobian
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (hnu : 0 ≤ nu)
    (K : ℝ → ℝ) (hKcontinuous : Continuous K)
    (hK : ∀ t ∈ Icc a b, ∀ x ∈ unitCube,
      ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ K t)
    (hforce : ∀ t ∈ Icc a b,
      periodicCurlForcingWork force velocity t ≤ 0) :
    ∀ t ∈ Icc a b,
      periodicEnstrophy velocity t ≤
        periodicEnstrophy velocity a *
          Real.exp (∫ s in a..t, 2 * K s) := by
  intro t ht
  have h := solution.enstrophy_le_timeDependentGronwallBound
    ha hab hbT hnu K (fun _ => 0) hKcontinuous continuous_const
      hK hforce t ht
  simpa [timeDependentGronwallBound, cumulativeRate, mul_comm] using h

/-- A uniform accumulated-Jacobian budget gives one enstrophy bound throughout an interior
compact interval of the open lifespan. -/
theorem OpenPeriodicSolutionOn.enstrophy_le_of_integral_jacobian_budget
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {a b M : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (hnu : 0 ≤ nu)
    (K : ℝ → ℝ) (hKcontinuous : Continuous K)
    (hK : ∀ t ∈ Icc a b, ∀ x ∈ unitCube,
      ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ K t)
    (hforce : ∀ t ∈ Icc a b,
      periodicCurlForcingWork force velocity t ≤ 0)
    (hbudget : ∀ t ∈ Icc a b, (∫ s in a..t, 2 * K s) ≤ M) :
    ∀ t ∈ Icc a b,
      periodicEnstrophy velocity t ≤
        periodicEnstrophy velocity a * Real.exp M := by
  intro t ht
  have hbound := solution.enstrophy_le_exp_integral_jacobian
    ha hab hbT hnu K hKcontinuous hK hforce t ht
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (hbudget t ht))
    (periodicEnstrophy_nonneg_receiver velocity a))

/-! ## A lifespan-wide accumulated-control receiver -/

/-- Input testimony for one accumulated Jacobian control on the entire tail `Ico a T`.

The continuous envelope is stronger than bare time integrability, but is exactly the regularity
currently required by the integrating-factor owner.  The budget is uniform as `t ↑ T`. -/
structure OpenAccumulatedJacobianControl
    (T nu : ℝ) (force velocity : VelocityField) (a M : ℝ) (K : ℝ → ℝ) : Prop where
  base_pos : 0 < a
  base_lt_terminal : a < T
  viscosity_nonneg : 0 ≤ nu
  envelope_continuous : Continuous K
  jacobian_envelope : ∀ t ∈ Ico a T, ∀ x ∈ unitCube,
    ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ K t
  curlForcing_nonpos : ∀ t ∈ Ico a T,
    periodicCurlForcingWork force velocity t ≤ 0
  accumulated_budget : ∀ t ∈ Ico a T,
    (∫ s in a..t, 2 * K s) ≤ M

/-- The receiver question that one constant bounds periodic enstrophy at every point of the
half-open tail. -/
def UniformOpenEnstrophyBound
    (T a : ℝ) (velocity : VelocityField) (bound : ℝ) : Prop :=
  ∀ t ∈ Ico a T, periodicEnstrophy velocity t ≤ bound

/-- A lifespan-wide accumulated Jacobian receipt returns the explicit uniform enstrophy bound
`E(a) exp(M)` at every time strictly below `T`. -/
theorem OpenAccumulatedJacobianControl.uniformOpenEnstrophyBound
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {a M : ℝ} {K : ℝ → ℝ}
    (control : OpenAccumulatedJacobianControl T nu force velocity a M K)
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    UniformOpenEnstrophyBound T a velocity
      (periodicEnstrophy velocity a * Real.exp M) := by
  intro t ht
  exact solution.enstrophy_le_of_integral_jacobian_budget
    control.base_pos ht.1 ht.2 control.viscosity_nonneg K
      control.envelope_continuous
      (fun s hs x hx => control.jacobian_envelope s
        ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩ x hx)
      (fun s hs => control.curlForcing_nonpos s
        ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩)
      (fun s hs => control.accumulated_budget s
        ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩)
      t ⟨ht.1, le_rfl⟩

/-- The explicit pointwise uniform receipt also yields boundedness of the complete enstrophy image
over the open tail. -/
theorem UniformOpenEnstrophyBound.bddAbove_image
    {T a bound : ℝ} {velocity : VelocityField}
    (h : UniformOpenEnstrophyBound T a velocity bound) :
    BddAbove (periodicEnstrophy velocity '' Ico a T) := by
  refine ⟨bound, ?_⟩
  rintro y ⟨t, ht, rfl⟩
  exact h t ht

section Audit

#print axioms OpenPeriodicSolutionOn.enstrophy_le_timeDependentGronwallBound
#print axioms OpenPeriodicSolutionOn.enstrophy_le_exp_integral_jacobian
#print axioms OpenAccumulatedJacobianControl.uniformOpenEnstrophyBound
#print axioms UniformOpenEnstrophyBound.bddAbove_image

end Audit

end Soma.Holonics.Millennium.NavierStokesOpenLifespan
