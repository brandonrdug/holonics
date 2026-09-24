import ElementaryHolonics.Millennium.MinusFourth
import ElementaryHolonics.Millennium.Descent
import Mathlib.Tactic

/-!
# RankZero: the four half-turns are the whole population, and one is not a congruent number

The discharge.  `Descent.lean` carried `TheFourHalfTurnsAreTheWholePopulation` — every rational
point of `y² = x³ − x` is the identity or one of the three half-turns — as a named-open
proposition, noting its classical proof is Fermat's descent.  `MinusFourth.lean` climbed the
descent.  This file builds the bridge and discharges the proposition as a **theorem**: the first
complete rank computation in this tree, `E(ℚ) ≅ (ℤ/2)²`, rank zero, kernel-checked — and with
it, **one is not a congruent number**: no rational right triangle has area one, also a theorem
below.

The bridge, verified exactly on 292 rational points before encoding: a point `(x, y)` with
`y ≠ 0` yields `X = (x²+1)/(2y)` and `Y = (x⁴−6x²+1)/(4y²)` with `X⁴ − 1 = Y²` — the identity's
whole content is `(x²+1)⁴ − (x⁴−6x²+1)² = 16(x³−x)²`, the curve equation entering
quadratically.  `Y ≠ 0` because `x⁴ − 6x² + 1 = 0` would make `(x² − 3)² = 8` with eight not a
rational square.  Clearing `X`'s denominator lands an integer solution of the minus form —
`num⁴ − den⁴ = (Y·den²)²`, the rational `Y·den²` forced integral because its square is — and
the descent refuses it.  So every affine point has `y = 0`, the cubic factors the abscissa into
`{0, 1, −1}`, and the population is exactly the four half-turns.  The triangle face rides the
same refusal through `x = c²/4, y = c(a² − b²)/8`, whose curve membership is the exact identity
`(a² − b²)² = c⁴ − 16` under `ab = 2`, `a² + b² = c²`.

In the dialect: the realized population of the congruent-number curve **is** its torsion table,
proved by navigation's own mechanism — a route that would realize a fifth point cannot close,
because closing it would found an infinite strictly-descending chain on well-founded terrain.

Classical citations: Fermat's right-triangle theorem (c. 1640); the congruent-number
correspondence as in Koblitz, *Introduction to Elliptic Curves and Modular Forms* (1984),
Chapter I.

Every `theorem` is discharged and none depends on `sorryAx`.  **Boundary**: rank zero for this
one curve and the non-congruence of one; nothing about other congruent numbers, ranks in
general, or the Birch–Swinnerton-Dyer conjecture — whose rank-zero prediction for this curve
this result is *consistent with*, not evidence for.
-/

namespace Soma.Holonics.Millennium.RankZero

open Soma.Holonics.Millennium

/-- Eight is not a rational square — the arithmetic that keeps the bridge's `Y` nonzero. -/
theorem theEightIsNotASquare : ¬ IsSquare (8 : ℚ) := by
  rw [show (8 : ℚ) = ((8 : ℕ) : ℚ) by norm_num, Rat.isSquare_natCast_iff]
  rintro ⟨r, hr⟩
  have h1 : r < 4 := by nlinarith
  interval_cases r <;> omega

/-- **The quartic guard never vanishes rationally**: `x⁴ − 6x² + 1 = 0` would make
`(x² − 3)² = 8`. -/
theorem theQuarticGuardNeverVanishes (x : ℚ) : x ^ 4 - 6 * x ^ 2 + 1 ≠ 0 := by
  intro h
  refine theEightIsNotASquare ⟨x ^ 2 - 3, ?_⟩
  linear_combination -h

/-- **The cleared bridge identity**: on the curve,
`(x²+1)⁴ − 16y⁴ = (x⁴−6x²+1)²` — the curve equation entering quadratically. -/
theorem theClearedBridgeIdentity {x y : ℚ} (hcurve : y ^ 2 = x ^ 3 - x) :
    (x ^ 2 + 1) ^ 4 - 16 * y ^ 4 = (x ^ 4 - 6 * x ^ 2 + 1) ^ 2 := by
  linear_combination (-16 * (x ^ 3 - x + y ^ 2)) * hcurve

/-- A rational whose self-product is an integer has unit denominator — the square's denominator
is the square of the denominator, so a unit denominator descends. -/
theorem theIntegralSquareForcesIntegrality {q : ℚ} {n : ℤ} (h : q * q = (n : ℚ)) :
    q.den = 1 := by
  have hden : q.den * q.den = 1 := by
    have h1 : (q * q).den = 1 := by rw [h]; exact Rat.den_intCast n
    rwa [Rat.mul_self_den] at h1
  have h2 : q.den ∣ 1 := ⟨q.den, hden.symm⟩
  have h3 : q.den ≤ 1 := Nat.le_of_dvd one_pos h2
  have h4 : q.den ≠ 0 := q.den_nz
  omega

/-- **A point off the half-turns founds a forbidden descent**: no rational point of
`y² = x³ − x` has a nonzero ordinate.  The bridge lands the minus form; the descent refuses
it. -/
theorem theCurveHasNoPointOffTheHalfTurns {x y : ℚ} (hy : y ≠ 0)
    (hcurve : y ^ 2 = x ^ 3 - x) : False := by
  have h2y : (2 : ℚ) * y ≠ 0 := by simpa using hy
  set X : ℚ := (x ^ 2 + 1) / (2 * y) with hX
  set Y : ℚ := (x ^ 4 - 6 * x ^ 2 + 1) / (4 * y ^ 2) with hY
  have hXY : X ^ 4 - 1 = Y ^ 2 := by
    rw [hX, hY]
    have h16 : (16 : ℚ) * y ^ 4 ≠ 0 := by positivity
    field_simp
    linear_combination (-256 * (x ^ 3 - x + y ^ 2)) * hcurve
  have hY0 : Y ≠ 0 := by
    rw [hY]
    exact div_ne_zero (theQuarticGuardNeverVanishes x) (by positivity)
  -- clear the denominator of `X`
  have hden0 : ((X.den : ℚ)) ≠ 0 := by
    exact_mod_cast X.den_nz
  have hnum : X * (X.den : ℚ) = (X.num : ℚ) := Rat.mul_den_eq_num X
  have h1 : (X.num : ℚ) ^ 4 - (X.den : ℚ) ^ 4 = (Y * (X.den : ℚ) ^ 2) ^ 2 := by
    rw [← hnum]
    linear_combination ((X.den : ℚ)) ^ 4 * hXY
  -- the square is an integer, so its root is
  have hCsq : (Y * (X.den : ℚ) ^ 2) * (Y * (X.den : ℚ) ^ 2)
      = ((X.num ^ 4 - (X.den : ℤ) ^ 4 : ℤ) : ℚ) := by
    push_cast
    linear_combination -h1
  have hCden : (Y * (X.den : ℚ) ^ 2).den = 1 := theIntegralSquareForcesIntegrality hCsq
  have hC0 : Y * (X.den : ℚ) ^ 2 ≠ 0 := mul_ne_zero hY0 (by positivity)
  have hCint : ((Y * (X.den : ℚ) ^ 2).num : ℚ) = Y * (X.den : ℚ) ^ 2 := by
    conv_rhs => rw [← Rat.num_div_den (Y * (X.den : ℚ) ^ 2)]
    rw [hCden]
    simp
  -- the integer minus-form solution
  have hZ : X.num ^ 4 - (X.den : ℤ) ^ 4 = (Y * (X.den : ℚ) ^ 2).num ^ 2 := by
    have h := hCsq
    rw [← hCint] at h
    have h' : X.num ^ 4 - (X.den : ℤ) ^ 4
        = (Y * (X.den : ℚ) ^ 2).num * (Y * (X.den : ℚ) ^ 2).num := by exact_mod_cast h.symm
    rw [← pow_two] at h'
    exact h'
  have hbZ : ((X.den : ℤ)) ≠ 0 := by exact_mod_cast X.den_nz
  have hcZ : (Y * (X.den : ℚ) ^ 2).num ≠ 0 := Rat.num_ne_zero.mpr hC0
  exact MinusFourth.theMinusFourthHasNoSolution hbZ hcZ hZ

/-- **The vanishing ordinate factors the abscissa**: `y = 0` on the curve forces
`x ∈ {0, 1, −1}`. -/
theorem theVanishingOrdinateFactorsTheAbscissa {x : ℚ} (h : (0 : ℚ) ^ 2 = x ^ 3 - x) :
    x = 0 ∨ x = 1 ∨ x = -1 := by
  have h0 : x * ((x - 1) * (x + 1)) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact Or.inl h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (by linarith))

/-- **THE DISCHARGE: the four half-turns are the whole population.**  `Descent.lean`'s
named-open proposition, now a theorem — the congruent-number curve has rank zero, its rational
points exactly the computed Klein four-group. -/
theorem theFourHalfTurnsAreTheWholePopulationHolds :
    Descent.TheFourHalfTurnsAreTheWholePopulation := by
  intro P
  cases P with
  | zero => exact Or.inl rfl
  | @some x y h =>
    have heq : y ^ 2 = x ^ 3 - x := by
      have h1 := ((WeierstrassCurve.Affine.nonsingular_iff x y).mp h).1
      rw [WeierstrassCurve.Affine.equation_iff] at h1
      simp only [Descent.E] at h1
      linarith [h1]
    by_cases hy : y = 0
    · subst hy
      rcases theVanishingOrdinateFactorsTheAbscissa (by linarith [heq]) with hx | hx | hx
      · subst hx; exact Or.inr (Or.inl rfl)
      · subst hx; exact Or.inr (Or.inr (Or.inl rfl))
      · subst hx; exact Or.inr (Or.inr (Or.inr rfl))
    · exact (theCurveHasNoPointOffTheHalfTurns hy heq).elim

/-- **One is not a congruent number**: no rational right triangle has area one — legs `a, b`
with `ab = 2` and hypotenuse `c` cannot exist.  Equal squared legs would make two a rational
square; unequal legs land on the curve at `x = c²/4, y = c(a²−b²)/8` through the exact identity
`(a²−b²)² = c⁴ − 16`, and the curve has no such point. -/
theorem theOneIsNotACongruentNumber (a b c : ℚ) (hab : a * b = 2)
    (hpyth : a ^ 2 + b ^ 2 = c ^ 2) : False := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab
  have hb0 : b ≠ 0 := by rintro rfl; simp at hab
  have hc0 : c ≠ 0 := by
    rintro rfl
    nlinarith [sq_pos_of_ne_zero ha0, sq_nonneg b, hpyth]
  by_cases habs : a ^ 2 = b ^ 2
  · -- equal squared legs force `a² = 2`
    have hab2 : a ^ 2 * b ^ 2 = 4 := by nlinarith [hab]
    have ha2 : a ^ 2 * a ^ 2 = 4 := by rw [habs] at hab2 ⊢; linarith [hab2]
    have h2 : (a ^ 2 - 2) * (a ^ 2 + 2) = 0 := by linear_combination ha2
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact Descent.notSquareTwo ⟨a, by nlinarith [h3]⟩
    · nlinarith [sq_nonneg a]
  · -- unequal legs land on the curve
    have hy0 : c * (a ^ 2 - b ^ 2) / 8 ≠ 0 := by
      apply div_ne_zero _ (by norm_num)
      exact mul_ne_zero hc0 (sub_ne_zero.mpr habs)
    refine theCurveHasNoPointOffTheHalfTurns (x := c ^ 2 / 4) hy0 ?_
    have hkey : (a ^ 2 - b ^ 2) ^ 2 = c ^ 4 - 16 := by
      linear_combination (a ^ 2 + b ^ 2 + c ^ 2) * hpyth - (4 * a * b + 8) * hab
    field_simp
    linear_combination 64 * hkey

end Soma.Holonics.Millennium.RankZero
