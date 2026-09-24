import Holonics.Mathematics.AnalyticNavigation
import Holonics.Foundation.Holon
import Holonics.Computation.HolonicRecurrentEcology

/-!
# Analytic navigation as a receiving recurrence

This owner binds the local analytic Newton step to the existing Holon and first-arrival carriers.
The `Option` value is an explicit refusal/termination face: an absent value stays absent, while a
present value is advanced only inside the declared source domain and away from a zero derivative.
No convergence or global basin claim is made.
-/

noncomputable section

namespace Holonics.Mathematics.AnalyticReceiving

open Set
open Holonics
open Holonics.Mathematics.AnalyticNavigation
open Holonics.Computation.HolonicRecurrentEcology

def admittedNewtonStep (lambda : ℂ) (f : ℂ → ℂ) (domain : Set ℂ) : Option ℂ → Option ℂ := by
  classical
  intro value
  cases value with
  | none => exact none
  | some z => exact if z ∈ domain ∧ deriv f z ≠ 0 then some (newtonMap lambda f z) else none

def analyticNewtonHolon (lambda : ℂ) (f : ℂ → ℂ) (domain : Set ℂ) :
    Holon (Option ℂ) (Option ℂ) (Option ℂ) :=
  Holon.ofEvolution id (admittedNewtonStep lambda f domain) id

def firstArrivalPopulation (lambda : ℂ) (f : ℂ → ℂ) (domain : Set ℂ) (receiving : Set (Option ℂ)) :
    ℕ → Set (Option ℂ) :=
  FirstArrival.population (admittedNewtonStep lambda f domain) receiving

def clockedFirstArrivalPopulation (lambda : ℂ) (f : ℂ → ℂ) (domain : Set ℂ)
    (regions : ℕ → Set (Option ℂ)) : ℕ → Set (Option ℂ × ℕ) :=
  FirstArrival.population
    (ClockedFirstArrival.step (fun _ => admittedNewtonStep lambda f domain))
    (ClockedFirstArrival.receiving regions)

theorem admittedNewtonStep_some_iff {lambda : ℂ} {f : ℂ → ℂ} {domain : Set ℂ}
    {z y : ℂ} (hz : z ∈ domain) (hderiv : deriv f z ≠ 0) :
    admittedNewtonStep lambda f domain (some z) = some y ↔
      deriv f z * (y - z) + lambda * f z = 0 := by
  classical
  rw [show admittedNewtonStep lambda f domain (some z) = some (newtonMap lambda f z) by
    simp [admittedNewtonStep, hz, hderiv]]
  simp only [Option.some.injEq]
  constructor
  · intro h
    unfold newtonMap at h
    field_simp [hderiv] at h ⊢
    linear_combination (-1) * h
  · intro h
    have hy : newtonMap lambda f z = y := by
      unfold newtonMap
      field_simp [hderiv] at h ⊢
      ring_nf at h ⊢
      linear_combination (-1) * h
    exact hy

theorem absent_step_absorbing {lambda : ℂ} {f : ℂ → ℂ} {domain : Set ℂ} :
    admittedNewtonStep lambda f domain none = none := rfl

/-! ## Changing charts and moving receiving regions -/

def changingConjugateStep {X Y : Type*} (equiv : ℕ → X ≃ Y) (transport : ℕ → X → X) (n : ℕ) :
    Y → Y :=
  equiv (n + 1) ∘ transport n ∘ (equiv n).symm

theorem changing_evolution_conjugate {X Y : Type*} (equiv : ℕ → X ≃ Y)
    (transport : ℕ → X → X) (k n : ℕ) (x : X) :
    ClockedFirstArrival.evolution (X := Y) (changingConjugateStep equiv transport) k n (equiv k x) =
      equiv (k + n) (ClockedFirstArrival.evolution transport k n x) := by
  induction n with
  | zero => simp [ClockedFirstArrival.evolution]
  | succ n ih =>
      simp only [ClockedFirstArrival.evolution, changingConjugateStep, Function.comp_apply,
        Equiv.symm_apply_apply]
      rw [ih]
      simp [ClockedFirstArrival.evolution, Nat.add_assoc]

theorem changing_firstArrival_membership_equiv {X Y : Type*} (equiv : ℕ → X ≃ Y)
    (regions : ℕ → Set X) (n : ℕ) (y : Y) :
    y ∈ equiv n '' regions n ↔ (equiv n).symm y ∈ regions n := by
  simp

theorem changing_firstArrival_population_conjugate {X Y : Type*} (equiv : ℕ → X ≃ Y)
    (transport : ℕ → X → X) (regions : ℕ → Set X) (k n : ℕ) (x : X) :
    (equiv k x, k) ∈
        FirstArrival.population
          (ClockedFirstArrival.step (changingConjugateStep equiv transport))
          (ClockedFirstArrival.receiving (fun n => equiv n '' regions n)) n ↔
      (x, k) ∈
        FirstArrival.population (ClockedFirstArrival.step transport)
          (ClockedFirstArrival.receiving regions) n := by
  rw [ClockedFirstArrival.mem_population_iff, ClockedFirstArrival.mem_population_iff]
  constructor
  · rintro ⟨hit, prior⟩
    refine ⟨?_, ?_⟩
    · rw [changing_firstArrival_membership_equiv] at hit
      simpa [changing_evolution_conjugate] using hit
    · intro j hj hreturn
      apply prior j hj
      rw [changing_firstArrival_membership_equiv]
      simpa [changing_evolution_conjugate] using hreturn
  · rintro ⟨hit, prior⟩
    refine ⟨?_, ?_⟩
    · rw [changing_firstArrival_membership_equiv]
      simpa [changing_evolution_conjugate] using hit
    · intro j hj hreturn
      apply prior j hj
      rw [changing_firstArrival_membership_equiv] at hreturn
      simpa [changing_evolution_conjugate] using hreturn

end Holonics.Mathematics.AnalyticReceiving

section Audit
open Holonics.Mathematics.AnalyticReceiving
#print axioms admittedNewtonStep_some_iff
#print axioms changing_evolution_conjugate
#print axioms changing_firstArrival_membership_equiv
#print axioms changing_firstArrival_population_conjugate
end Audit
