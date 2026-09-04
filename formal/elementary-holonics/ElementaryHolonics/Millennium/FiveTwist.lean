import ElementaryHolonics.Millennium.BirchSwinnertonDyer
import ElementaryHolonics.Millennium.GaussCoefficient

/-!
# FiveTwist: the trace of the twist is the character times the trace

**The opening deed of the rank-one campaign at five.**  The curve `y² = x³ − 25x` is
the quadratic twist by five of `y² = x³ − x`, and its point counts obey the twist law

```text
a_p(E₅) = χ_p(5) · a_p(E₁)     for every prime  p ∤ 10,
```

proved by the substitution `x ↦ 5x` inside the quadratic character sum — one bijection
of `𝔽_p`, no modularity input.  This pins the coefficient stream of the five-twist to
the already-identified stream at one, so the analytic datum at five is the
character-twisted transplant of the witness at one; its functional-equation sign `−1`
is the remaining analytic face.
-/

namespace Soma.Holonics.Millennium.FiveTwist

open Finset
open Soma.Holonics.Millennium.BirchSwinnertonDyer

variable {p : ℕ} [Fact p.Prime]

/-- The square-count expansion of the trace, for every twist. -/
theorem trace_eq_neg_charSum (n : ℕ) (hp2 : p ≠ 2) :
    traceOfFrobenius n p
      = -∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - (n : ZMod p) ^ 2 * x) := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  unfold traceOfFrobenius affineCount
  have hcard : ∀ x : ZMod p,
      ((univ.filter fun y : ZMod p => y ^ 2 = x ^ 3 - ((n : ℕ) : ZMod p) ^ 2 * x).card : ℤ)
      = quadraticChar (ZMod p) (x ^ 3 - (n : ZMod p) ^ 2 * x) + 1 := by
    intro x
    have h := quadraticChar_card_sqrts hchar (x ^ 3 - (n : ZMod p) ^ 2 * x)
    rw [← h]
    congr 1
    rw [Set.toFinset_setOf]
  push_cast
  rw [Finset.sum_congr rfl fun x _ => hcard x, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, ZMod.card]
  push_cast
  ring

/-- **The twist law**: for `p ∤ 10`, the trace at five is the quadratic character of
five times the trace at one — the substitution `x ↦ 5x` inside the character sum. -/
theorem theTraceTwistLaw (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    traceOfFrobenius 5 p = quadraticChar (ZMod p) 5 * traceOfFrobenius 1 p := by
  have h5 : ((5 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    rcases (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by norm_num)).mp hdvd with h
    exact hp5 h
  rw [trace_eq_neg_charSum 5 hp2, trace_eq_neg_charSum 1 hp2]
  have hsub : ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - ((5 : ℕ) : ZMod p) ^ 2 * x)
      = quadraticChar (ZMod p) 5 *
        ∑ u : ZMod p, quadraticChar (ZMod p) (u ^ 3 - ((1 : ℕ) : ZMod p) ^ 2 * u) := by
    rw [Finset.mul_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft₀ ((5 : ℕ) : ZMod p) h5)
      (fun x => quadraticChar (ZMod p) (x ^ 3 - ((5 : ℕ) : ZMod p) ^ 2 * x))]
    refine Finset.sum_congr rfl fun u _ => ?_
    show quadraticChar (ZMod p) ((((5 : ℕ) : ZMod p) * u) ^ 3
        - ((5 : ℕ) : ZMod p) ^ 2 * (((5 : ℕ) : ZMod p) * u)) = _
    have hfac : (((5 : ℕ) : ZMod p) * u) ^ 3 - ((5 : ℕ) : ZMod p) ^ 2 * (((5 : ℕ) : ZMod p) * u)
        = ((5 : ℕ) : ZMod p) ^ 2 * (((5 : ℕ) : ZMod p) * (u ^ 3 - ((1 : ℕ) : ZMod p) ^ 2 * u)) := by
      push_cast
      ring
    rw [hfac, map_mul, quadraticChar_sq_one' h5, one_mul, map_mul]
    push_cast
    ring
  rw [hsub]
  ring

/-- The twist law, measured at the first sighted prime beyond the bad set:
`a₁₃(E₅) = −6 = (5|13)·a₁₃(E₁)`. -/
theorem theTwistInstanceAtThirteen : traceOfFrobenius 5 13 = -6 := by decide

/-- The blind frames stay blind under twisting: `a₃(E₅) = 0`. -/
theorem theTwistInstanceAtThree : traceOfFrobenius 5 3 = 0 := by decide

/-- The residue-one prime seventeen is a square-class fixed point: `(5|17) = −1` sends
`a₁₇ = 2` to `−2`. -/
theorem theTwistInstanceAtSeventeen : traceOfFrobenius 5 17 = -2 := by decide

end Soma.Holonics.Millennium.FiveTwist
