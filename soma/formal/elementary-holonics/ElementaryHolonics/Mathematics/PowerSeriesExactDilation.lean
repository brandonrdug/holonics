import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Exact power-series dilation

Substitution `X ↦ X^k` is the exact scale chart used by the Jacobi/Tunnell
line.  This file records its coefficient receiver explicitly: the target
coefficient at `n` has one predecessor at `n/k` when `k ∣ n`, and has an empty
predecessor fibre otherwise.  No decimal scale, approximation, or limit is
involved.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.PowerSeriesExactDilation

open PowerSeries

/-- The exact dilation ring receiver `X ↦ X^k`, for a nonzero scale. -/
def exactDilateHom (k : ℕ) (hk : k ≠ 0) :
    PowerSeries ℤ →+* PowerSeries ℤ :=
  (PowerSeries.substAlgHom (PowerSeries.HasSubst.X_pow hk)).toRingHom

def exactDilate (k : ℕ) (hk : k ≠ 0)
    (F : PowerSeries ℤ) : PowerSeries ℤ :=
  exactDilateHom k hk F

@[simp] theorem exactDilate_zero (k : ℕ) (hk : k ≠ 0) :
    exactDilate k hk (0 : PowerSeries ℤ) = 0 :=
  map_zero (exactDilateHom k hk)

@[simp] theorem exactDilate_one (k : ℕ) (hk : k ≠ 0) :
    exactDilate k hk (1 : PowerSeries ℤ) = 1 :=
  map_one (exactDilateHom k hk)

@[simp] theorem exactDilate_add (k : ℕ) (hk : k ≠ 0)
    (F G : PowerSeries ℤ) :
    exactDilate k hk (F + G) =
      exactDilate k hk F + exactDilate k hk G :=
  map_add (exactDilateHom k hk) F G

@[simp] theorem exactDilate_sub (k : ℕ) (hk : k ≠ 0)
    (F G : PowerSeries ℤ) :
    exactDilate k hk (F - G) =
      exactDilate k hk F - exactDilate k hk G :=
  map_sub (exactDilateHom k hk) F G

@[simp] theorem exactDilate_mul (k : ℕ) (hk : k ≠ 0)
    (F G : PowerSeries ℤ) :
    exactDilate k hk (F * G) =
      exactDilate k hk F * exactDilate k hk G :=
  map_mul (exactDilateHom k hk) F G

@[simp] theorem exactDilate_pow (k : ℕ) (hk : k ≠ 0)
    (F : PowerSeries ℤ) (r : ℕ) :
    exactDilate k hk (F ^ r) = exactDilate k hk F ^ r :=
  map_pow (exactDilateHom k hk) F r

/-- **EXACT DILATION FIBRE.**  A target coefficient has the unique source
address `n/k` precisely when `k` divides `n`; otherwise its predecessor
population is empty. -/
theorem coeff_exactDilate (k : ℕ) (hk : k ≠ 0)
    (F : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (exactDilate k hk F) =
      if k ∣ n then PowerSeries.coeff (n / k) F else 0 := by
  have hsubst : exactDilate k hk F =
      PowerSeries.subst ((PowerSeries.X : PowerSeries ℤ) ^ k) F := by
    simpa [exactDilate, exactDilateHom] using
      congrFun (PowerSeries.coe_substAlgHom
        (PowerSeries.HasSubst.X_pow hk)) F
  rw [hsubst]
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.X_pow hk)]
  by_cases hdiv : k ∣ n
  · rw [if_pos hdiv]
    obtain ⟨j, rfl⟩ := hdiv
    rw [finsum_eq_single _ j]
    · simp [← pow_mul,
        Nat.mul_div_cancel_left j (Nat.pos_of_ne_zero hk)]
    · intro r hr
      have hne : k * j ≠ k * r := by
        intro h
        exact hr (mul_left_cancel₀ hk h).symm
      simp [← pow_mul, PowerSeries.coeff_X_pow, hne]
  · rw [if_neg hdiv]
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    have hne : n ≠ k * j := by
      intro h
      apply hdiv
      exact ⟨j, h⟩
    simp [← pow_mul, PowerSeries.coeff_X_pow, hne]

theorem coeff_exactDilate_of_dvd
    (k : ℕ) (hk : k ≠ 0) (F : PowerSeries ℤ) {n : ℕ}
    (hdiv : k ∣ n) :
    PowerSeries.coeff n (exactDilate k hk F) =
      PowerSeries.coeff (n / k) F := by
  rw [coeff_exactDilate, if_pos hdiv]

theorem coeff_exactDilate_of_not_dvd
    (k : ℕ) (hk : k ≠ 0) (F : PowerSeries ℤ) {n : ℕ}
    (hdiv : ¬ k ∣ n) :
    PowerSeries.coeff n (exactDilate k hk F) = 0 := by
  rw [coeff_exactDilate, if_neg hdiv]

#print axioms coeff_exactDilate

end Soma.Holonics.Mathematics.PowerSeriesExactDilation
