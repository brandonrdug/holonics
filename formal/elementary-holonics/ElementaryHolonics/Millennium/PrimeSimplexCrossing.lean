import ElementaryHolonics.Millennium.PrimeSimplexPeeling
import Mathlib.Data.Nat.Choose.Sum

/-!
# Many staircases crossing: the shells of the prime simplex intersect with polarity

`PrimeSimplexPeeling` is one staircase: one prime `q` peels one shell,
`M_{≥q}(N) = M_{>q}(N) − M_{>q}(N/q)`.  Here the shells of any finite set of primes `S` are
peeled together.  Two shells `q, q′` cross at `N/(qq′)`; the incoming polarity of each is `−1`,
the crossing carries their product `+1` — two flips restore the flow — and a crossing of `|T|`
shells carries `(−1)^{|T|} = μ(∏T)`.  The complete statement is the Legendre identity

```
    M(N) = Σ_{T ⊆ S} (−1)^{|T|} · M_{avoid S}(N / ∏T),
```

with `M_{avoid S}` the Möbius sum over numbers coprime to every prime of `S`: the outgoing traffic
after every shell of `S` has been peeled, read at every crossing `N/∏T`.  Summing the polarities
alone over every crossing pattern of a nonempty `S` returns `0` — the crossings fully cancel,
which is `Σ_{d ∣ n} μ(d) = 0` on the Boolean lattice `2^S`: Möbius inversion, the inverse of the
unitriangular incidence matrix `ζ` of the divisor lattice.  This is the crossing-word algebra of
`TABLET_THE_TURN` (`(ℤ/2)^{|S|}` graded by symmetric difference) acting on the Möbius sums.

Every theorem below is discharged with no `sorryAx`.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

namespace Soma.Holonics.Millennium.PrimeSimplexCrossing

open Soma.Holonics.Millennium.PrimeSimplexPeeling
open Soma.Holonics.Millennium.PrimeSimplex

/-- [definition] `n` avoids every prime of `S`. -/
def Avoids (S : Finset ℕ) (n : ℕ) : Prop := ∀ p ∈ S, ¬ p ∣ n

noncomputable instance (S : Finset ℕ) (n : ℕ) : Decidable (Avoids S n) := Classical.dec _

/-- [definition] The Möbius sum over `n ≤ N` avoiding every prime of `S`: the outgoing traffic
after the shells of `S` are peeled. -/
noncomputable def avoiding (S : Finset ℕ) (N : ℕ) : ℤ :=
  ∑ n ∈ Ioc 0 N, if Avoids S n then μ n else 0

theorem avoiding_succ (S : Finset ℕ) (n : ℕ) :
    avoiding S (n + 1) = avoiding S n + if Avoids S (n + 1) then μ (n + 1) else 0 := by
  unfold avoiding
  rw [sum_Ioc_succ_top (Nat.zero_le _)]

theorem avoids_insert_iff_of_not_dvd {S : Finset ℕ} {q n : ℕ} (hqn : ¬ q ∣ n) :
    Avoids (insert q S) n ↔ Avoids S n := by
  constructor
  · intro h p hp
    exact h p (mem_insert_of_mem hp)
  · intro h p hp
    rcases mem_insert.mp hp with rfl | hpS
    · exact hqn
    · exact h p hpS

theorem not_avoids_insert_of_dvd {S : Finset ℕ} {q n : ℕ} (hqn : q ∣ n) :
    ¬ Avoids (insert q S) n := by
  intro h
  exact h q (mem_insert_self q S) hqn

/-- Multiplying by a prime outside `S` does not change avoidance of `S`. -/
theorem avoids_mul_left_iff {S : Finset ℕ} {q m : ℕ} (hq : q.Prime)
    (hS : ∀ p ∈ S, p.Prime) (hqS : q ∉ S) :
    Avoids S (q * m) ↔ Avoids S m := by
  constructor
  · intro h p hp hpm
    exact h p hp (Dvd.dvd.mul_left hpm q)
  · intro h p hp hpqm
    rcases (Nat.Prime.dvd_mul (hS p hp)).mp hpqm with hpq | hpm
    · have : p = q := (Nat.prime_dvd_prime_iff_eq (hS p hp) hq).mp hpq
      exact hqS (this ▸ hp)
    · exact h p hp hpm

/-- [proved-derived; formal-checked] **One shell against a set of shells**: for a prime `q ∉ S`,
`M_{avoid S}(N) = M_{avoid S∪{q}}(N) − M_{avoid S∪{q}}(N/q)`. -/
theorem avoiding_eq_insert_sub {S : Finset ℕ} {q : ℕ} (hq : q.Prime)
    (hS : ∀ p ∈ S, p.Prime) (hqS : q ∉ S) (N : ℕ) :
    avoiding S N = avoiding (insert q S) N - avoiding (insert q S) (N / q) := by
  induction N with
  | zero => simp [avoiding]
  | succ n ih =>
    rw [avoiding_succ, ih]
    by_cases hdvd : q ∣ n + 1
    · have hk1 : (n + 1) / q = n / q + 1 := by rw [Nat.succ_div, if_pos hdvd]
      obtain ⟨k, hk⟩ := hdvd
      have hk' : k = n / q + 1 := by
        rw [← hk1, hk, Nat.mul_div_cancel_left k hq.pos]
      have hnot : ¬ Avoids (insert q S) (n + 1) := not_avoids_insert_of_dvd ⟨k, hk⟩
      rw [hk1, avoiding_succ (insert q S) n, if_neg hnot, add_zero,
        avoiding_succ (insert q S) (n / q)]
      rw [hk, hk', moebius_prime_mul hq]
      by_cases hqm : q ∣ n / q + 1
      · rw [if_pos hqm, if_neg (not_avoids_insert_of_dvd hqm)]
        simp
      · rw [if_neg hqm]
        by_cases h : Avoids (insert q S) (n / q + 1)
        · rw [if_pos h, if_pos ((avoids_mul_left_iff hq hS hqS).mpr
            ((avoids_insert_iff_of_not_dvd hqm).mp h))]
          ring
        · rw [if_neg h, if_neg (fun hf => h ((avoids_insert_iff_of_not_dvd hqm).mpr
            ((avoids_mul_left_iff hq hS hqS).mp hf)))]
          ring
    · have h1 : (n + 1) / q = n / q := by rw [Nat.succ_div, if_neg hdvd, add_zero]
      rw [h1, avoiding_succ (insert q S) n]
      by_cases h : Avoids (insert q S) (n + 1)
      · rw [if_pos h, if_pos ((avoids_insert_iff_of_not_dvd hdvd).mp h)]
        ring
      · rw [if_neg h, if_neg (fun hf => h ((avoids_insert_iff_of_not_dvd hdvd).mpr hf))]
        ring

/-- [proved-derived; formal-checked] With no shell peeled, the sum is the Mertens function. -/
theorem avoiding_empty (N : ℕ) : avoiding ∅ N = mertens N := by
  unfold avoiding mertens
  apply sum_congr rfl
  intro n _
  have h : Avoids ∅ n := fun p hp => absurd hp (notMem_empty p)
  rw [if_pos h]

/-- [proved-derived; formal-checked] **Many staircases crossing — the Legendre identity.**  For
a finite set of primes `S`, `M(N) = Σ_{T ⊆ S} (−1)^{|T|} · M_{avoid S}(N / ∏T)`: every crossing
pattern `T` of the shells carries the polarity `(−1)^{|T|}` and reads the outgoing traffic at
`N/∏T`. -/
theorem legendre {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    mertens N = ∑ T ∈ S.powerset, (-1 : ℤ) ^ T.card * avoiding S (N / ∏ p ∈ T, p) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [avoiding_empty]
  | insert q S hqS ih =>
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hS p (mem_insert_of_mem hp)
    have hq : q.Prime := hS q (mem_insert_self q S)
    rw [ih hS']
    rw [sum_powerset_insert hqS]
    have hshell : ∀ T ∈ S.powerset,
        (-1 : ℤ) ^ T.card * avoiding S (N / ∏ p ∈ T, p) =
          (-1 : ℤ) ^ T.card * avoiding (insert q S) (N / ∏ p ∈ T, p)
            + (-1 : ℤ) ^ (insert q T).card * avoiding (insert q S) (N / ∏ p ∈ insert q T, p) := by
      intro T hT
      have hqT : q ∉ T := fun hqT => hqS ((mem_powerset.mp hT) hqT)
      rw [avoiding_eq_insert_sub hq hS' hqS, card_insert_of_notMem hqT, prod_insert hqT,
        mul_comm q, ← Nat.div_div_eq_div_mul, pow_succ]
      ring
    rw [sum_congr rfl hshell, sum_add_distrib]

/-- [proved-derived; formal-checked] **The crossings fully cancel**: summing the polarities alone
over every crossing pattern of a nonempty set of shells returns `0` — Möbius inversion on the
Boolean lattice, `Σ_{d ∣ n} μ(d) = 0` for `n > 1`. -/
theorem crossings_cancel {S : Finset ℕ} (hS : S.Nonempty) :
    ∑ T ∈ S.powerset, (-1 : ℤ) ^ T.card = 0 :=
  sum_powerset_neg_one_pow_card_of_nonempty hS

section Audit

#print axioms avoiding_eq_insert_sub
#print axioms legendre
#print axioms crossings_cancel

end Audit

end Soma.Holonics.Millennium.PrimeSimplexCrossing
