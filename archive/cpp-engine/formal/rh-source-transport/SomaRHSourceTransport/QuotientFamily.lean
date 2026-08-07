import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

/-!
# Quotient-family re-indexing

For a positive receiver `m` and one old divisor `n ∣ m`, the quotient
`k = m / n` is the relative axis between them.  Descendants of `n` are
`n * ℓ`.  At scale `x`, writing `s = m / x`, the geometric receiver band

`y < (n * ℓ) / x ≤ 1`

becomes

`y * k / s < ℓ ≤ k / s`.

The analytic continuation uses this re-indexing to separate geometric
variables `(s, k, ℓ)` from the arithmetic coefficient
`cω (ℓ * n) / cω n`.  The finite lemmas below certify only the exact integer
incidence on which that separation rests.  They contain no floating-point
arithmetic and make no claim about the remaining uniform kernel inequality.
-/

namespace Soma.RHSourceTransport

/--
An integer cell lies below the exact rational seam `yNum / yDen` at scale
`x`.  This is the cross-multiplied form of `n / x < yNum / yDen`.
-/
def belowSeam (yNum yDen x n : ℕ) : Prop :=
  yDen * n < yNum * x

/--
An integer cell lies in the positive receiver band above the exact rational
seam and no later than the finite scale.
-/
def positiveBand (yNum yDen x n : ℕ) : Prop :=
  yNum * x < yDen * n ∧ n ≤ x

theorem divisor_has_quotient
    {n m : ℕ} (hdiv : n ∣ m) :
    n * (m / n) = m := by
  exact Nat.mul_div_cancel' hdiv

theorem quotient_recovers_divisor
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hdiv : n ∣ m) :
    m / (m / n) = n := by
  obtain ⟨k, rfl⟩ := hdiv
  have hk : 0 < k := Nat.pos_of_mul_pos_left hm
  rw [Nat.mul_div_right k hn, Nat.mul_div_cancel n hk]

theorem descendant_through_quotient
    {n m k ell : ℕ}
    (hk : m = n * k)
    (hk_pos : 0 < k) :
    n * ell = m * ell / k := by
  subst m
  calc
    n * ell = (n * ell * k) / k := by
      symm
      exact Nat.mul_div_cancel (n * ell) hk_pos
    _ = (n * k) * ell / k := by
      congr 1
      ac_rfl

/--
For `m = n * k`, the old-cell seam test may be read entirely in the
receiver-relative quotient frame.  This is the exact integer form of
`s / k < y`, with `s = m / x`; there is no floating-point quotient.
-/
theorem belowSeam_iff_quotient
    {yNum yDen x n m k : ℕ}
    (hm : m = n * k)
    (hk : 0 < k) :
    belowSeam yNum yDen x n ↔
      yDen * m < yNum * x * k := by
  subst m
  unfold belowSeam
  constructor
  · intro h
    have h' := (Nat.mul_lt_mul_right hk).2 h
    convert h' using 1
    all_goals ring
  · intro h
    apply (Nat.mul_lt_mul_right hk).1
    convert h using 1
    all_goals ring

/--
The descendant band of `n * ell`, when observed from a receiver
`m = n * k`, is exactly the quotient-family band

`yNum * x * k < yDen * m * ell` and `m * ell ≤ x * k`.

This is the cross-multiplied, discrete form of
`y * k / s < ell ≤ k / s`.  It is the geometric re-indexing used by the
quotient congestion law.
-/
theorem positiveBand_iff_quotientBand
    {yNum yDen x n m k ell : ℕ}
    (hm : m = n * k)
    (hk : 0 < k) :
    positiveBand yNum yDen x (n * ell) ↔
      yNum * x * k < yDen * m * ell ∧
      m * ell ≤ x * k := by
  subst m
  unfold positiveBand
  constructor
  · rintro ⟨hseam, hscale⟩
    constructor
    · have h' := (Nat.mul_lt_mul_right hk).2 hseam
      convert h' using 1
      all_goals ring
    · have h' := Nat.mul_le_mul_right k hscale
      convert h' using 1
      all_goals ring
  · rintro ⟨hseam, hscale⟩
    constructor
    · apply (Nat.mul_lt_mul_right hk).1
      convert hseam using 1
      all_goals ring
    · apply (Nat.mul_le_mul_right_iff hk).1
      convert hscale using 1
      all_goals ring

end Soma.RHSourceTransport
