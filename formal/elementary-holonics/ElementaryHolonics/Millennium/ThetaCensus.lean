import ElementaryHolonics.Millennium.RankZero
import ElementaryHolonics.Millennium.DistantWindings
import Mathlib.Tactic

/-!
# ThetaCensus: the two sides of the Birch–Swinnerton-Dyer question meet at one

Tunnell's theorem (1983, through Waldspurger) converts the analytic side of the
congruent-number problem into finite lattice censuses: for odd squarefree `n`, the central
value `L(E_n, 1)` vanishes exactly when
`#{n = 2x² + y² + 32z²} = ½·#{n = 2x² + y² + 8z²}`, and — unconditionally — when the two
counts **differ**, the central value is nonzero, so by Coates–Wiles (1977, complex
multiplication) the curve has rank zero.  The analytic side of the first congruent-number
instance is therefore a theta census: a sphere-packing-species count of lattice points, the
coefficient of the theta series the L-value is assembled from.

This file closes the loop at `n = 1`, all of it exact:

* `theThickCensusIsComplete` / `theThinCensusIsComplete` — the two solution populations are
  enumerated whole: each is exactly `{(0, ±1, 0)}`, forced by the squares' sizes;
* `theTunnellComparisonRefusesEquality` — the counts are `2` against `2`, and two is not
  half of two: the equality that would make the central value vanish **fails**;
* `theAnalyticAndRealizedSidesAgreeAtOne` — the count inequality stands beside the
  kernel-checked realized statement `RankZero.theOneIsNotACongruentNumber`: the analytic
  chain (cited: Tunnell–Waldspurger, then Coates–Wiles) lands on exactly the statement the
  descent proved.  **The first Birch–Swinnerton-Dyer instance in this tree with both sides
  exact — the realized side by Fermat's descent, the analytic side by a lattice census —
  and they agree.**

The two bridges are classical and cited, never proved here: Tunnell (*Inventiones* 72,
1983), riding Waldspurger's theorem; Coates–Wiles (*Inventiones* 39, 1977).  Every
`theorem` below is discharged and none depends on `sorryAx`.  **Boundary**: the counts and
the agreement are theorems; the implication between them is imported literature; nothing
about `L`-functions as analytic objects, other `n`, or the conjecture itself is claimed.
-/

namespace Soma.Holonics.Millennium.ThetaCensus

/-- The thick theta form's solutions at one. -/
def thickSolutions : Finset (ℤ × ℤ × ℤ) := {(0, 1, 0), (0, -1, 0)}

/-- The thin theta form's solutions at one. -/
def thinSolutions : Finset (ℤ × ℤ × ℤ) := {(0, 1, 0), (0, -1, 0)}

/-- A nonzero integer square is at least one — the size bound that closes both censuses. -/
private lemma sq_ge_one {x : ℤ} (hx : x ≠ 0) : 1 ≤ x ^ 2 := by
  rcases lt_or_gt_of_ne hx with h | h
  · nlinarith
  · nlinarith

/-- **The thick census is complete**: `2x² + y² + 32z² = 1` has exactly the two solutions
`(0, ±1, 0)`. -/
theorem theThickCensusIsComplete (x y z : ℤ) :
    2 * x ^ 2 + y ^ 2 + 32 * z ^ 2 = 1 ↔ (x, y, z) ∈ thickSolutions := by
  constructor
  · intro h
    have hx : x = 0 := by
      by_contra hx0
      have := sq_ge_one hx0
      nlinarith [sq_nonneg y, sq_nonneg z]
    have hz : z = 0 := by
      by_contra hz0
      have := sq_ge_one hz0
      nlinarith [sq_nonneg y, sq_nonneg x]
    subst hx; subst hz
    have hy : y ^ 2 = 1 := by linarith
    have hfac : (y - 1) * (y + 1) = 0 := by linear_combination hy
    rcases mul_eq_zero.mp hfac with h1 | h1
    · have : y = 1 := by linarith
      subst this
      simp [thickSolutions]
    · have : y = -1 := by linarith
      subst this
      simp [thickSolutions]
  · intro h
    rcases Finset.mem_insert.mp h with h1 | h1
    · rw [Prod.ext_iff] at h1
      obtain ⟨hx, hyz⟩ := h1
      rw [Prod.ext_iff] at hyz
      obtain ⟨hy, hz⟩ := hyz
      subst hx; subst hy; subst hz
      norm_num
    · have h1' := Finset.mem_singleton.mp h1
      rw [Prod.ext_iff] at h1'
      obtain ⟨hx, hyz⟩ := h1'
      rw [Prod.ext_iff] at hyz
      obtain ⟨hy, hz⟩ := hyz
      subst hx; subst hy; subst hz
      norm_num

/-- **The thin census is complete**: `2x² + y² + 8z² = 1` has exactly the two solutions
`(0, ±1, 0)`. -/
theorem theThinCensusIsComplete (x y z : ℤ) :
    2 * x ^ 2 + y ^ 2 + 8 * z ^ 2 = 1 ↔ (x, y, z) ∈ thinSolutions := by
  constructor
  · intro h
    have hx : x = 0 := by
      by_contra hx0
      have := sq_ge_one hx0
      nlinarith [sq_nonneg y, sq_nonneg z]
    have hz : z = 0 := by
      by_contra hz0
      have := sq_ge_one hz0
      nlinarith [sq_nonneg y, sq_nonneg x]
    subst hx; subst hz
    have hy : y ^ 2 = 1 := by linarith
    have hfac : (y - 1) * (y + 1) = 0 := by linear_combination hy
    rcases mul_eq_zero.mp hfac with h1 | h1
    · have : y = 1 := by linarith
      subst this
      simp [thinSolutions]
    · have : y = -1 := by linarith
      subst this
      simp [thinSolutions]
  · intro h
    rcases Finset.mem_insert.mp h with h1 | h1
    · rw [Prod.ext_iff] at h1
      obtain ⟨hx, hyz⟩ := h1
      rw [Prod.ext_iff] at hyz
      obtain ⟨hy, hz⟩ := hyz
      subst hx; subst hy; subst hz
      norm_num
    · have h1' := Finset.mem_singleton.mp h1
      rw [Prod.ext_iff] at h1'
      obtain ⟨hx, hyz⟩ := h1'
      rw [Prod.ext_iff] at hyz
      obtain ⟨hy, hz⟩ := hyz
      subst hx; subst hy; subst hz
      norm_num

/-- **The Tunnell comparison refuses equality**: the thick count is not half the thin count
— the condition under which the central value would vanish fails at one. -/
theorem theTunnellComparisonRefusesEquality :
    thickSolutions.card = 2 ∧ thinSolutions.card = 2 ∧
      thickSolutions.card ≠ thinSolutions.card / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **THE TWO SIDES AGREE AT ONE.**  The analytic side's census refuses the vanishing
condition (this file), and the realized side refuses the triangle (Fermat's descent,
kernel-checked in `RankZero.lean`).  The cited chain — count inequality ⟹ nonvanishing
central value (Tunnell–Waldspurger) ⟹ rank zero (Coates–Wiles) — lands on exactly the
theorem the descent proved independently. -/
theorem theAnalyticAndRealizedSidesAgreeAtOne :
    (thickSolutions.card ≠ thinSolutions.card / 2) ∧
      (∀ a b c : ℚ, a * b = 2 → a ^ 2 + b ^ 2 = c ^ 2 → False) :=
  ⟨by decide, fun a b c hab hpyth => RankZero.theOneIsNotACongruentNumber a b c hab hpyth⟩

/-! ## The laboratory continues: three and five -/

private lemma abs_le_one_of_sq_le_one {x : ℤ} (h : x ^ 2 ≤ 1) : -1 ≤ x ∧ x ≤ 1 := by
  constructor <;> nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 2)]

/-- **The censuses differ at three**: each form represents three in exactly the four ways
`(±1, ±1, 0)`, and four is not half of four — the vanishing condition fails, the cited
chain reads rank zero, and three is classically not a congruent number. -/
theorem theCensusesDifferAtThree :
    (∀ x y z : ℤ, 2 * x ^ 2 + y ^ 2 + 32 * z ^ 2 = 3 ↔
      (z = 0 ∧ (x = 1 ∨ x = -1) ∧ (y = 1 ∨ y = -1))) ∧
    (∀ x y z : ℤ, 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2 = 3 ↔
      (z = 0 ∧ (x = 1 ∨ x = -1) ∧ (y = 1 ∨ y = -1))) ∧
    ¬ ((4 : ℤ) = 4 / 2) := by
  refine ⟨?_, ?_, by norm_num⟩ <;>
  · intro x y z
    constructor
    · intro h
      have hz : z = 0 := by
        by_contra hz0
        have := sq_ge_one hz0
        nlinarith [sq_nonneg x, sq_nonneg y]
      subst hz
      have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg y]
      obtain ⟨hxl, hxr⟩ := abs_le_one_of_sq_le_one hx2
      have hy2 : y ^ 2 ≤ 3 := by nlinarith [sq_nonneg x]
      have hyl : -1 ≤ y ∧ y ≤ 1 := by
        constructor <;> nlinarith [sq_nonneg (y + 2), sq_nonneg (y - 2)]
      obtain ⟨hyl', hyr'⟩ := hyl
      interval_cases x <;> interval_cases y <;> simp_all
    · rintro ⟨rfl, hx | hx, hy | hy⟩ <;> subst hx <;> subst hy <;> norm_num

/-- **The censuses vanish together at five, and the realized side supplies the infinite
chain.**  Neither form represents five at all, so the vanishing condition holds — the cited
chain reads a vanishing central value, the signature of positive rank — and this tree's
realized side answers with the kernel-checked infinite-order point `(−4, 6)` on
`y² = x³ − 25x`.  At one the census refuses and the descent proves emptiness; at five the
census vanishes and the walk proves an infinite chain: **the two sides move together, in
opposite directions, across the first two instances — both sides exact in this tree.** -/
theorem theVanishingCensusMeetsTheInfiniteChainAtFive :
    (∀ x y z : ℤ, 2 * x ^ 2 + y ^ 2 + 32 * z ^ 2 ≠ 5) ∧
    (∀ x y z : ℤ, 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2 ≠ 5) ∧
    RankOne.ThePointHasInfiniteOrder := by
  refine ⟨?_, ?_, DistantWindings.thePointHasInfiniteOrderHolds⟩ <;>
  · intro x y z h
    have hz : z = 0 := by
      by_contra hz0
      have := sq_ge_one hz0
      nlinarith [sq_nonneg x, sq_nonneg y]
    subst hz
    have hx1 : -1 ≤ x ∧ x ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg y, sq_nonneg (x + 2), sq_nonneg (x - 2)]
    have hy2 : -2 ≤ y ∧ y ≤ 2 := by
      constructor <;> nlinarith [sq_nonneg x, sq_nonneg (y + 3), sq_nonneg (y - 3)]
    obtain ⟨hxa, hxb⟩ := hx1
    obtain ⟨hya, hyb⟩ := hy2
    interval_cases x <;> interval_cases y <;> norm_num at h

end Soma.Holonics.Millennium.ThetaCensus
