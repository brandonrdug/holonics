import ElementaryHolonics.Millennium.BirchSwinnertonDyer
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The parity face of the posed Birch–Swinnerton-Dyer conjecture

The functional equation at its own centre forces `L(1) = 0` whenever the sign is `−1`
(`theOddSignForcesCentralVanishing`).  Read through the analytic order this is the unconditional
statement that the analytic rank is at least one at odd sign, and through the rank clause it is
the parity law of the posed conjecture: at algebraic rank zero the sign is even, and at odd sign
there is a rational point of infinite order.  Nothing here constructs the datum; every theorem is
a theorem of the pose.
-/

noncomputable section

namespace Soma.Holonics.Millennium.BirchSwinnertonDyerParity

open Soma.Holonics.Millennium.BirchSwinnertonDyer

variable {n : ℕ}

/-- **Analytic rank zero is exactly a nonvanishing central value.** -/
theorem analyticRank_eq_zero_iff (W : LDatum n) : analyticRank W = 0 ↔ W.L 1 ≠ 0 := by
  unfold analyticRank
  rw [analyticOrderAt_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd (Differentiable.analyticAt W.analytic 1) h
    · exact h
  · intro h
    exact Or.inr h

/-- **The odd sign forces analytic rank at least one**, unconditionally. -/
theorem theOddSignForcesAnalyticRankAtLeastOne (W : LDatum n) (hw : W.sign = -1) :
    1 ≤ analyticRank W := by
  unfold analyticRank
  have hne : analyticOrderAt W.L 1 ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨Differentiable.analyticAt W.analytic 1, theOddSignForcesCentralVanishing W hw⟩
  exact Order.one_le_iff_ne_zero.mpr hne

/-- Algebraic rank at least zero holds for every twist: the empty family is independent. -/
theorem algebraicRankAtLeast_zero (n : ℕ) : AlgebraicRankAtLeast n 0 :=
  ⟨fun i ↦ Fin.elim0 i, fun _ _ i ↦ Fin.elim0 i⟩

/-- **Under the rank clause, algebraic rank zero forces the even sign.** -/
theorem theRankZeroForcesEvenSign (W : LDatum n) (hclause : TheRankClause n W)
    (h0 : AlgebraicRankIs n 0) : W.sign = 1 := by
  rcases W.sign_pm with h | h
  · exact h
  · exfalso
    have hrank : analyticRank W = 0 := by simpa using (hclause 0).mpr h0
    exact (analyticRank_eq_zero_iff W).mp hrank (theOddSignForcesCentralVanishing W h)

/-- **Under the rank clause, the odd sign forces a rational point of infinite order.** -/
theorem theOddSignForcesAlgebraicRankAtLeastOne (W : LDatum n) (hclause : TheRankClause n W)
    (hw : W.sign = -1) : AlgebraicRankAtLeast n 1 := by
  by_contra hno
  have h0 : AlgebraicRankIs n 0 := ⟨algebraicRankAtLeast_zero n, hno⟩
  exact absurd (theRankZeroForcesEvenSign W hclause h0) (by rw [hw]; norm_num)

/-- **The parity law of the pose**: under the rank clause, either the sign is even or there is a
point of infinite order. -/
theorem theParityLaw (W : LDatum n) (hclause : TheRankClause n W) :
    W.sign = 1 ∨ AlgebraicRankAtLeast n 1 := by
  rcases W.sign_pm with h | h
  · exact Or.inl h
  · exact Or.inr (theOddSignForcesAlgebraicRankAtLeastOne W hclause h)

section Audit

#print axioms theOddSignForcesAnalyticRankAtLeastOne
#print axioms theRankZeroForcesEvenSign
#print axioms theParityLaw

end Audit

end Soma.Holonics.Millennium.BirchSwinnertonDyerParity
