import ElementaryHolonics.Millennium.NavierStokesAxisymmetricChart
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import ElementaryHolonics.Millennium.NavierStokesCoreVectorPotential
import ElementaryHolonics.Millennium.NavierStokesPeriodicLocalExistence

/-!
# A smooth periodic completion of an actual local potential

Integer translates of a core supported in radius less than one half are locally separated.
Their finite sum is locally one smooth translate. Cutting off the potential, then taking its
curl, preserves incompressibility and the complete velocity germ on the inner ball.
-/

noncomputable section
open ContDiff Set Metric Function Filter
open scoped BigOperators Topology

namespace Soma.Holonics.Millennium.NavierStokesPeriodicCore
open Soma.Holonics.Millennium.NavierStokes

abbrev LatticePoint := Fin 3 → ℤ

def latticeShift (n : LatticePoint) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i ↦ (n i : ℝ))

@[simp] theorem latticeShift_apply (n : LatticePoint) (i : Fin 3) :
    latticeShift n i = (n i : ℝ) := rfl

@[simp] theorem latticeShift_zero : latticeShift 0 = 0 := by ext i; simp

theorem lattice_separation {n m : LatticePoint} (hne : n ≠ m) :
    1 ≤ dist (latticeShift n) (latticeShift m) := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ m i := by
    by_contra h
    apply hne
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  have hint := Int.one_le_abs (sub_ne_zero.mpr hi)
  have hreal : (1 : ℝ) ≤ |(n i : ℝ) - (m i : ℝ)| := by exact_mod_cast hint
  calc
    1 ≤ |(latticeShift n - latticeShift m) i| := by simpa using hreal
    _ ≤ ‖latticeShift n - latticeShift m‖ := by
      simpa [Real.norm_eq_abs] using
        (PiLp.norm_apply_le (p := 2) (latticeShift n - latticeShift m) i)
    _ = dist (latticeShift n) (latticeShift m) := (dist_eq_norm _ _).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def periodize (f : Space → E) (x : Space) : E :=
  ∑ᶠ n : LatticePoint, f (x - latticeShift n)

theorem periodize_periodic (f : Space → E) (i : Fin 3) :
    Function.Periodic (periodize f) (EuclideanSpace.single i 1) := by
  intro x
  let e : LatticePoint ≃ LatticePoint :=
    { toFun := fun n j ↦ if j = i then n j - 1 else n j
      invFun := fun n j ↦ if j = i then n j + 1 else n j
      left_inv := by intro n; funext j; by_cases h : j = i <;> simp [h]
      right_inv := by intro n; funext j; by_cases h : j = i <;> simp [h] }
  change (∑ᶠ n : LatticePoint, f (x + EuclideanSpace.single i 1 - latticeShift n)) =
    ∑ᶠ n : LatticePoint, f (x - latticeShift n)
  refine finsum_eq_of_bijective e e.bijective (fun n ↦ ?_)
  congr 1
  ext j
  by_cases h : j = i
  · subst j; simp [e]; ring
  · simp [e, h]

/-- At most one lattice centre can be within half a unit of a point. -/
theorem exists_distinguished_centre (x : Space) :
    ∃ n : LatticePoint, ∀ m, m ≠ n → 1 / 2 ≤ dist x (latticeShift m) := by
  by_cases h : ∃ n : LatticePoint, dist x (latticeShift n) < 1 / 2
  · obtain ⟨n, hn⟩ := h
    refine ⟨n, fun m hmn ↦ ?_⟩
    have hsep := lattice_separation hmn
    have htri := dist_triangle (latticeShift m) x (latticeShift n)
    rw [dist_comm (latticeShift m) x] at htri
    linarith
  · exact ⟨0, fun m _ ↦ le_of_not_gt (fun hm ↦ h ⟨m, hm⟩)⟩

/-- Smoothness is proved from a local single-translate formula, without any convergence port. -/
theorem periodize_contDiff (f : Space → E) (hf : ContDiff ℝ ∞ f) {r : ℝ}
    (hr : r < 1 / 2) (hsupport : support f ⊆ closedBall (0 : Space) r) :
    ContDiff ℝ ∞ (periodize f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨n, hn⟩ := exists_distinguished_centre x
  have heq : periodize f =ᶠ[𝓝 x] fun y ↦ f (y - latticeShift n) := by
    filter_upwards [Metric.ball_mem_nhds x (sub_pos.mpr hr)] with y hy
    apply finsum_eq_single
    intro m hmn
    apply notMem_support.mp
    intro hfm
    have hb : dist y (latticeShift m) ≤ r := by
      simpa [mem_closedBall, dist_eq_norm] using hsupport hfm
    have hxy : dist x y < 1 / 2 - r := by simpa [mem_ball, dist_comm] using hy
    have htri := dist_triangle x y (latticeShift m)
    have hfar := hn m hmn
    linarith
  exact (hf.comp (contDiff_id.sub contDiff_const)).contDiffAt.congr_of_eventuallyEq heq

theorem periodize_eq_core_of_mem_ball {f : Space → E} {r : ℝ}
    (hsupport : support f ⊆ closedBall (0 : Space) r)
    {x : Space} (hx : x ∈ ball (0 : Space) (1 - r)) : periodize f x = f x := by
  have h : periodize f x = f (x - latticeShift 0) := by
    apply finsum_eq_single
    intro n hn
    apply notMem_support.mp
    intro hfn
    have hsmall : dist x 0 < 1 - r := hx
    have hcore : dist x (latticeShift n) ≤ r := by
      simpa [mem_closedBall, dist_eq_norm] using hsupport hfn
    have hsep := lattice_separation hn
    rw [latticeShift_zero] at hsep
    have htri := dist_triangle (latticeShift n) x 0
    rw [dist_comm (latticeShift n) x] at htri
    linarith
  simpa using h

def localCore (f : Space → E) (b : ContDiffBump (0 : Space)) : Space → E :=
  fun x ↦ b x • f x

theorem localCore_contDiff (f : Space → E) (b : ContDiffBump (0 : Space))
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (localCore f b) := b.contDiff.smul hf

theorem localCore_support (f : Space → E) (b : ContDiffBump (0 : Space)) :
    support (localCore f b) ⊆ closedBall (0 : Space) b.rOut := by
  intro x hx
  have hb : b x ≠ 0 := by intro h; exact hx (by simp [localCore, h])
  exact ball_subset_closedBall (by simpa [← b.support_eq] using hb)

def completedPotential (f : Space → E) (b : ContDiffBump (0 : Space)) : Space → E :=
  periodize (localCore f b)

/-- The declared physical aperture used by the finite-core construction. -/
def physicalCoreBump (ell : ℝ) (hell : 0 < ell) : ContDiffBump (0 : Space) where
  rIn := ell / 8
  rOut := ell / 4
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

theorem physicalCoreBump_separated (ell : ℝ) (hell : 0 < ell) (hsmall : ell < 2) :
    (physicalCoreBump ell hell).rOut < 1 / 2 := by
  change ell / 4 < 1 / 2
  linarith

theorem completedPotential_contDiff (f : Space → E) (b : ContDiffBump (0 : Space))
    (hf : ContDiff ℝ ∞ f) (hb : b.rOut < 1 / 2) :
    ContDiff ℝ ∞ (completedPotential f b) :=
  periodize_contDiff _ (localCore_contDiff f b hf) hb (localCore_support f b)

theorem completedPotential_periodic (f : Space → E) (b : ContDiffBump (0 : Space)) :
    IsOnePeriodic (completedPotential f b) := fun x i ↦ periodize_periodic _ i x

theorem completedPotential_eq_on_core (f : Space → E) (b : ContDiffBump (0 : Space))
    (hb : b.rOut < 1 / 2) {x : Space} (hx : x ∈ ball (0 : Space) b.rIn) :
    completedPotential f b x = f x := by
  have hsmall : x ∈ ball (0 : Space) (1 - b.rOut) := by
    have h := b.rIn_lt_rOut
    change dist x 0 < _ at hx ⊢
    linarith
  rw [completedPotential, periodize_eq_core_of_mem_ball (localCore_support f b) hsmall]
  simp [localCore, b.one_of_mem_closedBall (ball_subset_closedBall hx)]

#print axioms periodize_contDiff
#print axioms completedPotential_eq_on_core

open Soma.Holonics.Millennium.NavierStokesCoreVectorPotential
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicLocalExistence

def completedVelocity (f : InitialVelocity) (b : ContDiffBump (0 : Space)) : InitialVelocity :=
  coreCurl (completedPotential f b)

/-- The constructed global velocity supplies the actual local-existence data contract. -/
theorem completedVelocity_initial_condition (f : InitialVelocity) (b : ContDiffBump (0 : Space))
    (hf : ContDiff ℝ ∞ f) (hb : b.rOut < 1 / 2) :
    InitialVelocityConditionPeriodic (completedVelocity f b) where
  divergenceFree := divergence_coreCurl_eq_zero _
    ((completedPotential_contDiff f b hf hb).of_le (WithTop.coe_le_coe.mpr le_top))
  smooth := coreCurl_contDiff _ (completedPotential_contDiff f b hf hb)
  periodic := coreCurl_isOnePeriodic _ (completedPotential_periodic f b)

/-- The entire original velocity germ is preserved, not just a chosen finite list of jets. -/
theorem completedVelocity_eq_on_core (f : InitialVelocity) (b : ContDiffBump (0 : Space))
    (hb : b.rOut < 1 / 2) {x : Space} (hx : x ∈ ball (0 : Space) b.rIn) :
    completedVelocity f b x = coreCurl f x := by
  have heq : completedPotential f b =ᶠ[𝓝 x] f := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact completedPotential_eq_on_core f b hb hy
  unfold completedVelocity coreCurl NavierStokesVorticity.vorticityAt
    NavierStokesVorticity.velocityJacobianAt
  rw [heq.fderiv_eq]

/-- The actual smooth periodic source has a positive local Navier--Stokes lifespan, with its
own global pressure. This does not identify that pressure with a local radial comparison. -/
theorem completedVelocity_periodic_local_existence (f : InitialVelocity)
    (b : ContDiffBump (0 : Space)) (hf : ContDiff ℝ ∞ f) (hb : b.rOut < 1 / 2)
    (nu : ℝ) (hnu : 0 < nu) :
    ∃ T velocity pressure, 0 < T ∧
      OpenPeriodicSolutionOn T nu (completedVelocity f b) (fun _ _ ↦ 0) velocity pressure :=
  periodicLocalExistence nu hnu _ (completedVelocity_initial_condition f b hf hb)

#print axioms completedVelocity_initial_condition
#print axioms completedVelocity_eq_on_core
#print axioms completedVelocity_periodic_local_existence
end Soma.Holonics.Millennium.NavierStokesPeriodicCore
