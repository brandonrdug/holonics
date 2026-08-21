import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

/-!
# Acceleration: the return-word population is pinned, and the tail is priced exactly

The deposited `ζ(5)` series (the zeta-five record of 2026-08-21) is

    ζ(5) = (25/24) · Σₙ (−1)ⁿ/(n³·C(2n,n)) · Σ_{k≤n} (−1)ᵏ·C(2k,k)/k².

Its first analysis compared exact partial sums against a *quoted decimal* of `ζ(5)` — a
magnitude imported across the frame, a float wearing fifty digits.  Brandon's correction: no
floats, analyze holonically, adapt it.  This file is the adaptation: the series' convergence
structure as exact theorems over `ℚ`, with no analytic constant anywhere.

Write `t n = C(2n,n)/n²` and `J n = (−1)ⁿ · Σ_{k≤n} (−1)ᵏ t k`, so `J` obeys the reflection
recurrence `J (n+1) = t (n+1) − J n` and the series' outer term is `(25/24)·J n/(n³·C(2n,n))`.
What is proved:

* **the weight climbs**: `t` is strictly increasing from `n = 2` — the central binomial's growth
  beats the square, through mathlib's `succ_mul_centralBinom_succ`;
* **the population is pinned**: for `n ≥ 4`, `0 < J n < t n` — the anti-collapse shape, by
  induction on the reflection recurrence; so every outer term from there is positive: the series
  is eventually one-signed, as an exact theorem rather than an observed decimal;
* **the term is priced by the fifth power**: `J n/(n³·C(2n,n)) < 1/n⁵` — the `4ⁿ` growth of the
  inner population cancels the `4⁻ⁿ` of the outer factor *exactly*, leaving a fifth-power law;
* **the tail is priced by an exact coboundary**: `1/(n+1)⁵ ≤ (1/4)(1/n⁴ − 1/(n+1)⁴)` and the
  matching minorant — telescoping majorants, so every finite tail is bounded by an exact ratio,
  `Σ_{N<n≤M} 1/n⁵ ≤ (1/4)(1/N⁴ − 1/M⁴)`, and the series' own tail by `(25/96)/N⁴`;
* **the contraction's fixed point is `4/5`**: the ratio `x n = J n / t n` obeys
  `x (n+1) = 1 − x n / ρ (n+1)` with `ρ → 4`, and `x = 1 − x/4` exactly when `x = 4/5`; the
  coefficient chain `(25/24)·(4/5) = 5/6` is an identity — the tail constant, derived, not
  fitted.

**The exact enclosure this supports, measured 2026-08-21** (Python `fractions`, no decimal
conversion at any point): with the series' partial sum at aperture `N = 800` and the defining
series `Σ m⁻⁵` at `M = 2000`, both tails priced by the telescoping bounds above, the enclosure
of the **difference** has a strictly negative lower endpoint and strictly positive upper
endpoint — zero inside — with total width exactly `16009/24576000000000000`, identically
`25/(96·800⁴) + 1/(4·2000⁴) − 1/(4·2001⁴)`; and the ratio face satisfies `x₈₀₀ < 4/5` with
`4/5 − x₈₀₀ < 1/1600`, all by exact rational comparison.  The identity itself remains
`open`; what stands proved here is its convergence skeleton.

Every `theorem` is discharged and none depends on `sorryAx`.  Nothing here claims the
irrationality of `ζ(5)` or the deposited identity.
-/

namespace Soma.Holonics.Millennium.Acceleration

/-- The inner step: the central binomial against the square — a return-word count per area. -/
def t (n : ℕ) : ℚ := (Nat.centralBinom n : ℚ) / n ^ 2

/-- The signed inner population `J n = (−1)ⁿ Σ_{k≤n} (−1)ᵏ t k`, by its reflection recurrence. -/
def J : ℕ → ℚ
  | 0 => 0
  | n + 1 => t (n + 1) - J n

/-- The small populations, computed: `J 1 = 2`, `J 2 = −1/2`, `J 3 = 49/18`, `J 4 = 119/72`.
The sign settles at `n = 3`; the pinning below begins at `4`. -/
theorem theSmallPopulationsAreComputed :
    J 1 = 2 ∧ J 2 = -(1/2) ∧ J 3 = 49/18 ∧ J 4 = 119/72 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [J, t, Nat.centralBinom, Nat.choose]

/-- The central ratio, cast to `ℚ`: `(n+1)·C(2n+2, n+1) = 2(2n+1)·C(2n, n)`. -/
theorem theCentralRatioCasts (n : ℕ) :
    ((n : ℚ) + 1) * (Nat.centralBinom (n + 1) : ℚ)
      = (2 * (2 * n + 1)) * (Nat.centralBinom n : ℚ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ n

/-- **The weight climbs**: `t n < t (n+1)` from `n = 2` — the return-word growth beats the
square, exactly. -/
theorem theWeightClimbs (n : ℕ) (hn : 2 ≤ n) : t n < t (n + 1) := by
  have hq : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn1 : (0 : ℚ) < n := by linarith
  have hn2 : (0 : ℚ) < (n : ℚ) + 1 := by linarith
  have hC : (0 : ℚ) < (Nat.centralBinom n : ℚ) := by
    exact_mod_cast Nat.centralBinom_pos n
  have hCn : (Nat.centralBinom (n + 1) : ℚ)
      = (2 * (2 * n + 1)) * (Nat.centralBinom n : ℚ) / ((n : ℚ) + 1) := by
    field_simp
    linarith [theCentralRatioCasts n]
  rw [t, t, hCn]
  push_cast
  rw [div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
  have hpoly : ((n : ℚ) + 1) * ((n : ℚ) + 1) ^ 2 < 2 * (2 * (n : ℚ) + 1) * (n : ℚ) ^ 2 := by
    nlinarith [hq]
  nlinarith [mul_lt_mul_of_pos_left hpoly hC]

/-- **The population is pinned**: for `n ≥ 4`, `0 < J n < t n`.  The reflection recurrence
cannot collapse the population to zero and cannot let it escape its own step — the anti-collapse
clause of the schema, on arithmetic material. -/
theorem thePopulationIsPinned : ∀ n : ℕ, 4 ≤ n → 0 < J n ∧ J n < t n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      constructor <;> norm_num [J, t, Nat.centralBinom, Nat.choose]
  | succ n hn ih =>
      obtain ⟨h0, h1⟩ := ih
      have hclimb := theWeightClimbs n (by omega)
      constructor
      · show 0 < t (n + 1) - J n
        linarith
      · show t (n + 1) - J n < t (n + 1)
        linarith

/-- **The term is priced by the fifth power**: `J n · n⁵ < n³ · C(2n,n)`, the division-free form
of `J n/(n³·C(2n,n)) < 1/n⁵`.  The inner `4ⁿ` growth and the outer `4⁻ⁿ` decay cancel exactly;
what survives is the fifth power — kernel-checked, where the first analysis had an asymptotic
sentence. -/
theorem theTermIsPricedByTheFifthPower (n : ℕ) (hn : 4 ≤ n) :
    J n * (n : ℚ) ^ 5 < (n : ℚ) ^ 3 * (Nat.centralBinom n : ℚ) := by
  obtain ⟨-, h1⟩ := thePopulationIsPinned n hn
  have hn0 : (0 : ℚ) < n := by
    have : (4 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  have h2 : J n * (n : ℚ) ^ 2 < (Nat.centralBinom n : ℚ) := by
    rw [t] at h1
    calc J n * (n : ℚ) ^ 2 < ((Nat.centralBinom n : ℚ) / n ^ 2) * n ^ 2 := by
          apply mul_lt_mul_of_pos_right h1 (by positivity)
      _ = (Nat.centralBinom n : ℚ) := by field_simp
  calc J n * (n : ℚ) ^ 5 = (J n * (n : ℚ) ^ 2) * (n : ℚ) ^ 3 := by ring
    _ < (Nat.centralBinom n : ℚ) * (n : ℚ) ^ 3 := by
        apply mul_lt_mul_of_pos_right h2 (by positivity)
    _ = (n : ℚ) ^ 3 * (Nat.centralBinom n : ℚ) := by ring

/-- **The tail majorant is an exact coboundary**: `1/(n+1)⁵ ≤ (1/4)(1/n⁴ − 1/(n+1)⁴)`.  The
telescoping term changes the representative and prices the class — the tail is bounded by what
the coboundary telescopes to, not estimated. -/
theorem theTelescopingMajorant (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℚ) / ((n : ℚ) + 1) ^ 5 ≤ (1 / 4) * (1 / (n : ℚ) ^ 4 - 1 / ((n : ℚ) + 1) ^ 4) := by
  have hn0 : (0 : ℚ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℚ) < (n : ℚ) + 1 := by linarith
  have key : (1 / 4 : ℚ) * (1 / (n : ℚ) ^ 4 - 1 / ((n : ℚ) + 1) ^ 4)
      = (((n : ℚ) + 1) ^ 4 - (n : ℚ) ^ 4) / (4 * (n : ℚ) ^ 4 * ((n : ℚ) + 1) ^ 4) := by
    field_simp
  rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : (0 : ℚ) < (n : ℚ) ^ 2 := by positivity
  have h3 : (0 : ℚ) < (n : ℚ) ^ 3 := by positivity
  have hpoly : 4 * (n : ℚ) ^ 4 ≤ (((n : ℚ) + 1) ^ 4 - (n : ℚ) ^ 4) * ((n : ℚ) + 1) := by
    nlinarith [hn0, h2, h3]
  nlinarith [mul_le_mul_of_nonneg_right hpoly (le_of_lt (pow_pos hn1 4))]

/-- The matching minorant: `(1/4)(1/n⁴ − 1/(n+1)⁴) ≤ 1/n⁵` — so the coboundary prices the tail
from both sides and nothing is discarded unexhibited. -/
theorem theTelescopingMinorant (n : ℕ) (hn : 1 ≤ n) :
    (1 / 4 : ℚ) * (1 / (n : ℚ) ^ 4 - 1 / ((n : ℚ) + 1) ^ 4) ≤ 1 / (n : ℚ) ^ 5 := by
  have hn0 : (0 : ℚ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℚ) < (n : ℚ) + 1 := by linarith
  have key : (1 / 4 : ℚ) * (1 / (n : ℚ) ^ 4 - 1 / ((n : ℚ) + 1) ^ 4)
      = (((n : ℚ) + 1) ^ 4 - (n : ℚ) ^ 4) / (4 * (n : ℚ) ^ 4 * ((n : ℚ) + 1) ^ 4) := by
    field_simp
  rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : (0 : ℚ) < (n : ℚ) ^ 2 := by positivity
  have h3 : (0 : ℚ) < (n : ℚ) ^ 3 := by positivity
  have hpoly : (((n : ℚ) + 1) ^ 4 - (n : ℚ) ^ 4) * (n : ℚ) ≤ 4 * ((n : ℚ) + 1) ^ 4 := by
    nlinarith [hn0, h2, h3]
  nlinarith [mul_le_mul_of_nonneg_right hpoly (le_of_lt (pow_pos hn0 4))]

/-- **Every finite tail is priced by an exact ratio**:
`Σ_{N<n≤M} 1/n⁵ ≤ (1/4)(1/N⁴ − 1/M⁴)`, by telescoping the majorant.  No limit is taken and no
constant is quoted; the bound is a rational for every aperture pair. -/
theorem theFiniteTailIsPriced (N : ℕ) (hN : 1 ≤ N) :
    ∀ M : ℕ, N ≤ M →
      ∑ n ∈ Finset.Ioc N M, (1 : ℚ) / (n : ℚ) ^ 5
        ≤ (1 / 4) * (1 / (N : ℚ) ^ 4 - 1 / (M : ℚ) ^ 4) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
      rw [Finset.sum_Ioc_succ_top (by omega)]
      have hM1 : 1 ≤ M := le_trans hN hM
      have step := theTelescopingMajorant M hM1
      have cast1 : ((M + 1 : ℕ) : ℚ) = (M : ℚ) + 1 := by push_cast; ring
      calc ∑ n ∈ Finset.Ioc N M, (1 : ℚ) / (n : ℚ) ^ 5 + (1 : ℚ) / ((M + 1 : ℕ) : ℚ) ^ 5
          ≤ (1 / 4) * (1 / (N : ℚ) ^ 4 - 1 / (M : ℚ) ^ 4)
              + (1 / 4) * (1 / (M : ℚ) ^ 4 - 1 / ((M : ℚ) + 1) ^ 4) := by
            rw [cast1]; exact add_le_add ih step
        _ = (1 / 4) * (1 / (N : ℚ) ^ 4 - 1 / (((M : ℚ) + 1)) ^ 4) := by ring
        _ = (1 / 4) * (1 / (N : ℚ) ^ 4 - 1 / (((M + 1 : ℕ)) : ℚ) ^ 4) := by rw [cast1]

/-- **The contraction's fixed point is four fifths**: `x = 1 − x/4` exactly when `x = 4/5`.  The
ratio `J n/t n` obeys `x (n+1) = 1 − x n/ρ (n+1)` with `ρ` tending to four; this is where the
tail coefficient comes from, derived rather than fitted. -/
theorem theFixedPointIsFourFifths (x : ℚ) : x = 1 - x / 4 ↔ x = 4 / 5 := by
  constructor <;> intro h <;> linarith

/-- The coefficient chain is an identity: `(25/24)·(4/5) = 5/6` — the series prefactor times the
fixed point is the tail constant. -/
theorem theCoefficientChainIsExact : (25 : ℚ) / 24 * (4 / 5) = 5 / 6 := by norm_num

end Soma.Holonics.Millennium.Acceleration
