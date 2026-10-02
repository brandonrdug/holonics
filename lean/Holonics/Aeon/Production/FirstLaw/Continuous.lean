import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

/-! [agent-inferred] This existing law block has an independent consumer.
Its canonical namespace and every statement/proof are preserved exactly;
the aggregate owner imports it once. Import factoring excludes unrelated
constitutions/witnesses at the fixed one-core, 17-second, 2^32-byte RSS gate. -/

noncomputable section

namespace Holonics.Aeon.Production.FirstLaw

open scoped BigOperators
open Finset

section Continuous

variable {Index : Type*} [Fintype Index]

/-- [proved-derived; formal-checked] **The first law in the continuous chart.** Along
differentiable curves `p`, `q` with `q > 0`,
`d/dλ (−Σ pᵢ log qᵢ) = −Σ dpᵢ log qᵢ − Σ pᵢ dqᵢ/qᵢ`: the exchange rate plus the deposition rate. -/
theorem hasDerivAt_crossEntropy {p q : ℝ → Index → ℝ} {dp dq : Index → ℝ} {t : ℝ}
    (hp : ∀ i, HasDerivAt (fun s => p s i) (dp i) t)
    (hq : ∀ i, HasDerivAt (fun s => q s i) (dq i) t) (hpos : ∀ i, 0 < q t i) :
    HasDerivAt (fun s => -∑ i, p s i * Real.log (q s i))
      (-∑ i, dp i * Real.log (q t i) + -∑ i, p t i * (dq i / q t i)) t := by
  have hsum : HasDerivAt (fun s => ∑ i, p s i * Real.log (q s i))
      (∑ i, (dp i * Real.log (q t i) + p t i * (dq i / q t i))) t := by
    apply HasDerivAt.fun_sum
    intro i _
    exact (hp i).mul ((hq i).log (hpos i).ne')
  rw [sum_add_distrib] at hsum
  rw [show ∀ a b : ℝ, -a + -b = -(a + b) from fun a b => by ring]
  exact hsum.fun_neg

/-- [proved-derived; formal-checked] **Integrated over a clock interval**, the exchange and
deposition rates return the boundary difference of cross-entropy. -/
theorem first_law_integral {p q dp dq : ℝ → Index → ℝ} {a b : ℝ}
    (hp : ∀ t ∈ Set.uIcc a b, ∀ i, HasDerivAt (fun s => p s i) (dp t i) t)
    (hq : ∀ t ∈ Set.uIcc a b, ∀ i, HasDerivAt (fun s => q s i) (dq t i) t)
    (hpos : ∀ t ∈ Set.uIcc a b, ∀ i, 0 < q t i)
    (hint : IntervalIntegrable (fun t => -∑ i, dp t i * Real.log (q t i) +
      -∑ i, p t i * (dq t i / q t i)) MeasureTheory.volume a b) :
    ∫ t in a..b, (-∑ i, dp t i * Real.log (q t i) + -∑ i, p t i * (dq t i / q t i)) =
      (-∑ i, p b i * Real.log (q b i)) - (-∑ i, p a i * Real.log (q a i)) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_crossEntropy (hp t ht) (hq t ht) (hpos t ht)) hint

end Continuous

end Holonics.Aeon.Production.FirstLaw
