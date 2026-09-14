import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Composite terms from finite affine return

[proved-derived] Reduction commutes with iteration. A coprime slope permutes
`ZMod d`, so zero has a positive return clock bounded by `d`. Together with
strict integer growth this proves the first bound of Reyes, arXiv:2508.18305,
without factoring the root. The proof also permits `b = 0` and does not require
`a` and `b` to be coprime. The general certificate permits a composite divisor.
-/

namespace Soma.Holonics.Mathematics.AffineOrbitDivisor

open Function

def affineMap (a b : ℕ) (d : ℕ) : ZMod d → ZMod d := fun x ↦ a * x + b

def natAffine (a b : ℕ) : ℕ → ℕ := fun x ↦ a * x + b

/-- A fixed injective action on a finite state space has a bounded positive
return clock at every state. An arbitrary changing sequence of actions does
not satisfy this fixed-action hypothesis. -/
theorem finite_injective_return {Q : Type*} [Fintype Q]
    (f : Q → Q) (hf : Injective f) (x : Q) :
    ∃ n : ℕ, 0 < n ∧ n ≤ Fintype.card Q ∧ f^[n] x = x := by
  have hper : x ∈ periodicPts f := hf.mem_periodicPts x
  exact ⟨minimalPeriod f x, minimalPeriod_pos_of_mem_periodicPts hper,
    minimalPeriod_le_card, isPeriodicPt_minimalPeriod f x⟩

theorem natAffine_mod_iterate {a b d x : ℕ} (n : ℕ) :
    ((natAffine a b)^[n] x : ZMod d) =
      (affineMap a b d)^[n] (x : ZMod d) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
      congr 1
      simp [affineMap, natAffine]

theorem affineMap_injective {a b d : ℕ} (hcop : Nat.Coprime a d) :
    Injective (affineMap a b d) := by
  intro x y h
  have hm : (a : ZMod d) * x = (a : ZMod d) * y := by
    simpa [affineMap, add_left_inj] using h
  have hu : IsUnit (a : ZMod d) := (ZMod.isUnit_iff_coprime a d).2 hcop
  exact hu.mul_left_cancel hm

theorem affineMap_periodic_return {a b d : ℕ} (hd : 0 < d) (hcop : Nat.Coprime a d) :
    ∃ n : ℕ, 0 < n ∧ n ≤ d ∧ (affineMap a b d)^[n] 0 = 0 := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  simpa using finite_injective_return (affineMap a b d) (affineMap_injective hcop) 0

theorem natAffine_iterate_strict_growth {a b z : ℕ} (ha : 1 < a) (hz : 0 < z) :
    ∀ n, 0 < n → z < (natAffine a b)^[n] z := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero =>
          simpa [Function.iterate_succ_apply', natAffine] using
            (show z < a * z + b from (lt_mul_of_one_lt_left hz ha).trans_le (Nat.le_add_right _ _))
      | succ n =>
          have hprev := ih (by omega)
          have hpos : 0 < (natAffine a b)^[n + 1] z := Nat.zero_lt_of_lt (lt_of_lt_of_le hz hprev.le)
          calc
            z < (natAffine a b)^[n + 1] z := hprev
            _ < a * (natAffine a b)^[n + 1] z + b := by
              exact (lt_mul_of_one_lt_left hpos ha).trans_le (Nat.le_add_right _ _)
            _ = (natAffine a b)^[n + 2] z := by simp [Function.iterate_succ_apply', natAffine]

/-- A modular return and a retained growth bound certify a proper divisor;
the divisor need not be prime and the multiplier need not be a unit here. -/
theorem natAffine_proper_divisor_certificate {a b z d n : ℕ}
    (ha : 1 < a) (hd : 1 < d) (hdz : d ≤ z) (hn : 0 < n)
    (hreturn : (affineMap a b d)^[n] (z : ZMod d) = 0) :
    ¬Nat.Prime ((natAffine a b)^[n] z) := by
  have hz : 0 < z := lt_of_lt_of_le (lt_trans Nat.zero_lt_one hd) hdz
  have hmod : ((natAffine a b)^[n] z : ZMod d) = 0 := by
    rw [natAffine_mod_iterate]
    exact hreturn
  have hdvd : d ∣ (natAffine a b)^[n] z :=
    (ZMod.natCast_eq_zero_iff _ _).mp hmod
  have hg := natAffine_iterate_strict_growth (b := b) ha hz n hn
  intro hp
  rcases hp.eq_one_or_self_of_dvd _ hdvd with hone | heq <;> omega

theorem natAffine_proper_divisor_return {a b z : ℕ} (ha : 1 < a) (hz : 1 < z)
    (hcop : Nat.Coprime a z) :
    ∃ n : ℕ, 0 < n ∧ n ≤ z ∧ ¬Nat.Prime ((natAffine a b)^[n] z) := by
  have hper := affineMap_periodic_return (a := a) (b := b) (d := z) (lt_trans Nat.zero_lt_one hz) hcop
  obtain ⟨n, hn, hnz, hreturn⟩ := hper
  letI : NeZero z := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hz)⟩
  refine ⟨n, hn, hnz, ?_⟩
  apply natAffine_proper_divisor_certificate ha hz (le_refl z) hn
  simpa using hreturn

end Soma.Holonics.Mathematics.AffineOrbitDivisor
