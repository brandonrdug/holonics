import ElementaryHolonics.Millennium.BirchSwinnertonDyerSignLaw

/-!
# Under the rank clause, the sign is the parity of the algebraic rank

The sign law reads the functional-equation sign as the parity of the analytic rank.  The rank
clause identifies the analytic rank with the algebraic rank.  Together: under the rank clause the
sign is `(−1)^r` where `r` is the algebraic rank, so sign `+1` is exactly even algebraic rank and
sign `−1` is exactly odd algebraic rank.  This is the full parity conjecture of the pose, with the
rank clause as its only hypothesis.
-/

noncomputable section

namespace Soma.Holonics.Millennium.BirchSwinnertonDyerAlgebraicParity

open Soma.Holonics.Millennium.BirchSwinnertonDyer
open Soma.Holonics.Millennium.BirchSwinnertonDyerParity
open Soma.Holonics.Millennium.BirchSwinnertonDyerSignLaw

variable {n : ℕ}

/-- **The sign is the parity of the algebraic rank.** -/
theorem sign_eq_neg_one_pow_algebraicRank (W : LDatum n) (hclause : TheRankClause n W) {r : ℕ}
    (hr : AlgebraicRankIs n r) : (W.sign : ℂ) = (-1) ^ r :=
  theSignIsTheParityOfTheAnalyticRank W ((hclause r).mpr hr)

theorem even_algebraicRank_of_sign_one (W : LDatum n) (hclause : TheRankClause n W)
    (hw : W.sign = 1) {r : ℕ} (hr : AlgebraicRankIs n r) : Even r :=
  even_analyticRank_of_sign_one W hw ((hclause r).mpr hr)

theorem odd_algebraicRank_of_sign_neg_one (W : LDatum n) (hclause : TheRankClause n W)
    (hw : W.sign = -1) {r : ℕ} (hr : AlgebraicRankIs n r) : Odd r :=
  odd_analyticRank_of_sign_neg_one W hw ((hclause r).mpr hr)

/-- **The parity conjecture of the pose.** Under the rank clause, sign `+1` is exactly even
algebraic rank. -/
theorem sign_one_iff_even_algebraicRank (W : LDatum n) (hclause : TheRankClause n W) {r : ℕ}
    (hr : AlgebraicRankIs n r) : W.sign = 1 ↔ Even r := by
  constructor
  · intro hw
    exact even_algebraicRank_of_sign_one W hclause hw hr
  · intro he
    rcases W.sign_pm with h | h
    · exact h
    · exact absurd he (Nat.not_even_iff_odd.mpr (odd_algebraicRank_of_sign_neg_one W hclause h hr))

theorem sign_neg_one_iff_odd_algebraicRank (W : LDatum n) (hclause : TheRankClause n W) {r : ℕ}
    (hr : AlgebraicRankIs n r) : W.sign = -1 ↔ Odd r := by
  constructor
  · intro hw
    exact odd_algebraicRank_of_sign_neg_one W hclause hw hr
  · intro ho
    rcases W.sign_pm with h | h
    · exact absurd ho (Nat.not_odd_iff_even.mpr (even_algebraicRank_of_sign_one W hclause h hr))
    · exact h

end Soma.Holonics.Millennium.BirchSwinnertonDyerAlgebraicParity
