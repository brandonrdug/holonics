import ElementaryHolonics.Millennium.BirchSwinnertonDyerAlgebraicParity

/-!
# Finiteness of the analytic rank from a single nonvanishing value

The continued `L`-function is entire, so by the identity theorem its order at the centre is
infinite exactly when it vanishes identically.  A single nonvanishing value therefore makes the
analytic rank a natural number, and the sign law then applies without hypothesis on the order.
-/

noncomputable section

namespace Soma.Holonics.Millennium.BirchSwinnertonDyerFiniteRank

open Soma.Holonics.Millennium.BirchSwinnertonDyer
open Soma.Holonics.Millennium.BirchSwinnertonDyerParity
open Soma.Holonics.Millennium.BirchSwinnertonDyerSignLaw

variable {n : ℕ}

/-- **The identity theorem at the centre.** The analytic rank is infinite exactly when `L`
vanishes identically. -/
theorem analyticRank_eq_top_iff (W : LDatum n) : analyticRank W = ⊤ ↔ W.L = 0 :=
  AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (z := (1 : ℂ)) (fun z₀ => W.analytic.analyticAt z₀)

/-- The analytic rank is finite exactly when `L` has a nonvanishing value. -/
theorem analyticRank_ne_top_iff (W : LDatum n) : analyticRank W ≠ ⊤ ↔ ∃ s, W.L s ≠ 0 := by
  rw [Ne, analyticRank_eq_top_iff, funext_iff]
  push Not
  rfl

/-- **Finite rank from one nonvanishing value.** -/
theorem exists_analyticRank_eq (W : LDatum n) (h : ∃ s, W.L s ≠ 0) :
    ∃ m : ℕ, analyticRank W = m := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp ((analyticRank_ne_top_iff W).mpr h)
  exact ⟨m, hm.symm⟩

/-- **The sign law without an order hypothesis.** From one nonvanishing value, the rank is a
natural number and the sign is its parity. -/
theorem exists_analyticRank_eq_and_sign (W : LDatum n) (h : ∃ s, W.L s ≠ 0) :
    ∃ m : ℕ, analyticRank W = m ∧ (W.sign : ℂ) = (-1) ^ m := by
  obtain ⟨m, hm⟩ := exists_analyticRank_eq W h
  exact ⟨m, hm, theSignIsTheParityOfTheAnalyticRank W hm⟩

end Soma.Holonics.Millennium.BirchSwinnertonDyerFiniteRank
