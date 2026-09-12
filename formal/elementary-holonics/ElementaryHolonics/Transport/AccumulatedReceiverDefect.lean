import ElementaryHolonics.Transport.ChangingReceiver
import Mathlib.Analysis.ODE.DiscreteGronwall
import Mathlib.Tactic

/-!
# Accumulated receiver defects

This owner records the finite affine propagation of a receiver-relative approximation defect.
The Lipschitz and one-step hypotheses are supplied by the two compared transports; the resulting
bound is an exterior receiver of their actual trajectories, not a native certainty gate.
-/

namespace Soma.Holonics.Transport.AccumulatedReceiverDefect

open Soma.Holonics.Transport.ChangingReceiver
open scoped BigOperators

/-! ## The finite affine budget -/

def budget (L ε : ℕ → ℝ) (e₀ : ℝ) : ℕ → ℝ
  | 0 => e₀
  | n + 1 => L n * budget L ε e₀ n + ε n

def expansion (L ε : ℕ → ℝ) (e₀ : ℝ) (n : ℕ) : ℝ :=
  e₀ * ∏ j ∈ Finset.Ico 0 n, L j +
    ∑ k ∈ Finset.Ico 0 n, ε k * ∏ j ∈ Finset.Ico (k + 1) n, L j

/-! ## A trajectory comparison through a changing receiver -/

theorem distance_step_le
    {State : Type*} [NormedAddCommGroup State]
    (F G : ℕ → State → State) (fine coarse : ℕ → State)
    (L ε : ℕ → ℝ)
    (fine_step : ∀ n, fine (n + 1) = F n (fine n))
    (coarse_step : ∀ n, coarse (n + 1) = G n (coarse n))
    (lipschitz : ∀ n x y, ‖F n x - F n y‖ ≤ L n * ‖x - y‖)
    (one_step : ∀ n, ‖F n (coarse n) - G n (coarse n)‖ ≤ ε n) (n : ℕ) :
    ‖fine (n + 1) - coarse (n + 1)‖ ≤
      L n * ‖fine n - coarse n‖ + ε n := by
  rw [fine_step n, coarse_step n]
  calc
    ‖F n (fine n) - G n (coarse n)‖ ≤
        ‖F n (fine n) - F n (coarse n)‖ +
          ‖F n (coarse n) - G n (coarse n)‖ := by
            rw [show F n (fine n) - G n (coarse n) =
              (F n (fine n) - F n (coarse n)) +
                (F n (coarse n) - G n (coarse n)) by abel]
            exact norm_add_le _ _
    _ ≤ L n * ‖fine n - coarse n‖ + ε n :=
      add_le_add (lipschitz n _ _) (one_step n)

theorem distance_le_budget
    {State : Type*} [NormedAddCommGroup State]
    (F G : ℕ → State → State) (fine coarse : ℕ → State)
    (L ε : ℕ → ℝ) (e₀ : ℝ)
    (initial : ‖fine 0 - coarse 0‖ ≤ e₀)
    (fine_step : ∀ n, fine (n + 1) = F n (fine n))
    (coarse_step : ∀ n, coarse (n + 1) = G n (coarse n))
    (L_nonneg : ∀ n, 0 ≤ L n) (ε_nonneg : ∀ n, 0 ≤ ε n)
    (lipschitz : ∀ n x y, ‖F n x - F n y‖ ≤ L n * ‖x - y‖)
    (one_step : ∀ n, ‖F n (coarse n) - G n (coarse n)‖ ≤ ε n) :
    ∀ n, ‖fine n - coarse n‖ ≤ expansion L ε e₀ n := by
  intro n
  have h := discrete_gronwall_prod_general
      (u := fun n => ‖fine n - coarse n‖)
      (c := L) (b := ε) (n₀ := 0)
      (hu := fun k hk => by
        simpa using
          (distance_step_le F G fine coarse L ε fine_step coarse_step lipschitz one_step k))
      (hc := fun k hk => L_nonneg k)
      (n := n) (Nat.zero_le n)
  have hprod : 0 ≤ ∏ j ∈ Finset.Ico 0 n, L j :=
    Finset.prod_nonneg (fun j hj => L_nonneg j)
  simpa [expansion] using h.trans (add_le_add
    (mul_le_mul_of_nonneg_right initial hprod) le_rfl)

section Audit

#print axioms distance_step_le
#print axioms distance_le_budget

end Audit

end Soma.Holonics.Transport.AccumulatedReceiverDefect
