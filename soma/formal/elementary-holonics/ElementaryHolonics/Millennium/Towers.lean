import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-!
# The two gap scales, in exact charts

```text
√p · log p = log (p^{√p})          so   exp(√p log p) = p^{√p}
(log p)²   = log (p^{log p})       so   exp((log p)²) = p^{log p}
```

Both are logarithms of a tower, and `log²p ≪ √p log p` is just `log p ≪ √p` in the exponent.  **But
the two exponents decompose exactly in completely different charts, and that is why they behave
differently.**

**The `√p log p` chart is Diophantine.**  `√p` is irrational, so it has no arithmetic decomposition;
what it has is a continued fraction, whose convergents are exact rationals.  The determinant
identity `h_{n+1}k_n − h_n k_{n+1} = (−1)^n` — proved here by integer induction, no analysis — makes
consecutive convergents differ by

```text
Δ_n = (−1)^n / (k_n · k_{n+1})
```

an **alternating unit fraction** whose modulus is the product of consecutive denominators.  The
telescoping sum gives the tower as an exact product of rational powers:

```text
p^{√p} = p^{h₀/k₀} · ∏_n p^{(−1)^n /(k_n k_{n+1})}
√2 = 1 + 1/2 − 1/10 + 1/60 − 1/348 + 1/2030 − 1/11830 + …
2^{√2} = 2 · 2^{1/2} · 2^{−1/10} · 2^{1/60} · 2^{−1/348} · …
```

Every exponent exact, the signs alternating, and the moduli `k_n k_{n+1}` computed by an integer
recurrence.

**The `(log p)²` chart is arithmetic, and carries no irrationality at all.**  The logarithm's exact
decomposition is over the divisor lattice — mathlib's `vonMangoldt_sum`, `Σ_{d|n} Λ(d) = log n` — and
its square has the same shape one order up:

```text
Λ₂ = μ ∗ log²        Σ_{d|n} Λ₂(d) = (log n)²
```

proved below.  (`Λ₂` is the second von Mangoldt function; Selberg's identity
`Λ₂ = Λ·log + Λ∗Λ` is a further fact and is not proved here.)

**So the Cramér scale decomposes over divisors and the Riemann scale over convergents.**  One is a
sum over the multiplicative structure of `p`; the other is an alternating sum with growing moduli
that knows nothing about factorization.  Nothing here is a claim about any conjecture.
-/

namespace Soma.Holonics.Millennium.Towers

open ArithmeticFunction

/-! ## The `√p log p` chart: exact rational exponents from convergents -/

variable (a : ℕ → ℤ)

/-- Convergent numerators. -/
def hh : ℕ → ℤ
  | 0 => a 0
  | 1 => a 1 * a 0 + 1
  | (n + 2) => a (n + 2) * hh (n + 1) + hh n

/-- Convergent denominators. -/
def kk : ℕ → ℤ
  | 0 => 1
  | 1 => a 1
  | (n + 2) => a (n + 2) * kk (n + 1) + kk n

/-- **The convergent determinant alternates.**  `h_{n+1}k_n − h_n k_{n+1} = (−1)^n` — the whole
content of the continued-fraction chart, and it is an integer identity with no analysis. -/
theorem theConvergentDeterminantAlternates (n : ℕ) :
    hh a (n + 1) * kk a n - hh a n * kk a (n + 1) = (-1) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hh, kk]; ring
  | one => simp [hh, kk]; ring
  | more n _ ih2 =>
    show hh a (n + 2 + 1) * kk a (n + 2) - hh a (n + 2) * kk a (n + 2 + 1) = (-1) ^ (n + 2)
    have hrec1 : hh a (n + 2 + 1) = a (n + 3) * hh a (n + 2) + hh a (n + 1) := rfl
    have hrec2 : kk a (n + 2 + 1) = a (n + 3) * kk a (n + 2) + kk a (n + 1) := rfl
    rw [hrec1, hrec2,
      show (a (n + 3) * hh a (n + 2) + hh a (n + 1)) * kk a (n + 2)
        - hh a (n + 2) * (a (n + 3) * kk a (n + 2) + kk a (n + 1))
        = -(hh a (n + 2) * kk a (n + 1) - hh a (n + 1) * kk a (n + 2)) by ring, ih2]
    ring

/-- **So consecutive convergents differ by an exact rational with alternating sign and modulus
`k_n k_{n+1}`.**

`Δ_n = (−1)^n / (k_n k_{n+1})`.  Summing the differences telescopes to the value, so a tower
`p^x` factors as `p^{h_0/k_0} · ∏ p^{Δ_n}` — every factor an exact rational power, the signs
alternating, the moduli the products of consecutive denominators. -/
theorem theConvergentDifferenceIsAnAlternatingUnitFraction (n : ℕ)
    (h0 : (kk a n : ℚ) ≠ 0) (h1 : (kk a (n + 1) : ℚ) ≠ 0) :
    (hh a (n + 1) : ℚ) / (kk a (n + 1) : ℚ) - (hh a n : ℚ) / (kk a n : ℚ)
      = (-1) ^ n / ((kk a n : ℚ) * (kk a (n + 1) : ℚ)) := by
  have hd := theConvergentDeterminantAlternates a n
  field_simp
  have : ((hh a (n + 1) * kk a n - hh a n * kk a (n + 1) : ℤ) : ℚ) = ((-1 : ℤ) ^ n : ℤ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hd
  push_cast at this ⊢
  linarith [this]

/-! ## The `(log p)²` chart: exact, over the divisor lattice, with no irrationality at all -/

/-- The **second von Mangoldt function**, `Λ₂ = μ ∗ log²`, so that its divisor sum is `log²`. -/
noncomputable def logSq : ArithmeticFunction ℝ := ⟨fun n => (Real.log n) ^ 2, by simp⟩

noncomputable def vonMangoldtTwo : ArithmeticFunction ℝ :=
  (↑ArithmeticFunction.moebius : ArithmeticFunction ℝ) * logSq

/-- **The divisor sum of the second von Mangoldt function is the square of the logarithm.**

`Σ_{d|n} Λ₂(d) = (log n)²` — the exact decomposition of the Cramér scale over the divisor lattice,
with no irrationality anywhere.  The first-order case is mathlib's `vonMangoldt_sum`,
`Σ_{d|n} Λ(d) = log n`. -/
theorem theDivisorSumOfTheSecondIsTheLogSquared (n : ℕ) :
    ∑ d ∈ n.divisors, vonMangoldtTwo d = (Real.log n) ^ 2 := by
  have h : (↑ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vonMangoldtTwo = logSq := by
    unfold vonMangoldtTwo
    rw [← mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul]
  have h2 : ((↑ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vonMangoldtTwo) n = logSq n := by
    rw [h]
  rw [ArithmeticFunction.coe_zeta_mul_apply] at h2
  simpa [logSq] using h2


end Soma.Holonics.Millennium.Towers
