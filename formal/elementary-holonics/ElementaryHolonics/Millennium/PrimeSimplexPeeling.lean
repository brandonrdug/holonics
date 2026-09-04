import ElementaryHolonics.Millennium.PrimeSimplex

/-!
# The prime simplex peels prime by prime: the shift holds at every vertex

`PrimeSimplex.mertens_eq_oddSum_sub` is the shell at the least vertex `2`:
`M(N) = M_{odd}(N) − M_{odd}(N/2)`.  The complex is shifted at **every** vertex, and the same
identity holds at every prime `q` for the `q`-rough Möbius sums

```
    M_{≥q}(N) = Σ_{n ≤ N, every prime factor ≥ q} μ(n),
    M_{>q}(N) = Σ_{n ≤ N, every prime factor > q} μ(n),

    M_{≥q}(N) = M_{>q}(N) − M_{>q}(N / q)        (q prime).
```

This is Buchstab's identity for `μ`; iterated over consecutive primes it is the Legendre sieve,
and it is the local-to-global transport of the prime simplex in algebraic form: each prime peels
one shell, carrying the sum at `N` to the sum at `N/q` with the polarity `μ(qm) = −μ(m)`.  The
top-octave identity is the case `q = 2` (`roughFrom_two`, `roughAbove_two`).

Every theorem below is discharged with no `sorryAx`.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

namespace Soma.Holonics.Millennium.PrimeSimplexPeeling

/-- [definition] Every prime factor of `n` is at least `q`. -/
def RoughFrom (q n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → q ≤ p

/-- [definition] Every prime factor of `n` exceeds `q`. -/
def RoughAbove (q n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → q < p

noncomputable instance (q n : ℕ) : Decidable (RoughFrom q n) := Classical.dec _

noncomputable instance (q n : ℕ) : Decidable (RoughAbove q n) := Classical.dec _

/-- [definition] The `q`-rough Möbius sum `M_{≥q}(N)`. -/
noncomputable def roughFrom (q N : ℕ) : ℤ :=
  ∑ n ∈ Ioc 0 N, if RoughFrom q n then μ n else 0

/-- [definition] The strictly `q`-rough Möbius sum `M_{>q}(N)`. -/
noncomputable def roughAbove (q N : ℕ) : ℤ :=
  ∑ n ∈ Ioc 0 N, if RoughAbove q n then μ n else 0

theorem roughFrom_succ (q n : ℕ) :
    roughFrom q (n + 1) = roughFrom q n + if RoughFrom q (n + 1) then μ (n + 1) else 0 := by
  unfold roughFrom
  rw [sum_Ioc_succ_top (Nat.zero_le _)]

theorem roughAbove_succ (q n : ℕ) :
    roughAbove q (n + 1) = roughAbove q n + if RoughAbove q (n + 1) then μ (n + 1) else 0 := by
  unfold roughAbove
  rw [sum_Ioc_succ_top (Nat.zero_le _)]

/-- Not divisible by `q`: rough from `q` is the same as rough above `q`. -/
theorem roughFrom_iff_roughAbove_of_not_dvd {q n : ℕ} (_hq : q.Prime) (hn : ¬ q ∣ n) :
    RoughFrom q n ↔ RoughAbove q n := by
  constructor
  · intro h p hp hpn
    rcases lt_or_eq_of_le (h p hp hpn) with hlt | heq
    · exact hlt
    · exact absurd (heq ▸ hpn) hn
  · intro h p hp hpn
    exact le_of_lt (h p hp hpn)

/-- Divisible by `q`: rough from `q` of `q·m` is rough from `q` of `m`. -/
theorem roughFrom_mul_left_iff {q m : ℕ} (hq : q.Prime) :
    RoughFrom q (q * m) ↔ RoughFrom q m := by
  constructor
  · intro h p hp hpm
    exact h p hp (Dvd.dvd.mul_left hpm q)
  · intro h p hp hpqm
    rcases (Nat.Prime.dvd_mul hp).mp hpqm with hpq | hpm
    · exact le_of_eq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpq).symm
    · exact h p hp hpm

/-- A multiple of `q` is never rough above `q`. -/
theorem not_roughAbove_of_dvd {q n : ℕ} (hq : q.Prime) (hn : q ∣ n) : ¬ RoughAbove q n := by
  intro h
  exact lt_irrefl q (h q hq hn)

/-- [proved-derived; formal-checked] `μ(q·m) = −μ(m)` when `q ∤ m`, and `0` when `q ∣ m`. -/
theorem moebius_prime_mul {q m : ℕ} (hq : q.Prime) :
    μ (q * m) = if q ∣ m then 0 else -μ m := by
  split_ifs with hqm
  · apply moebius_eq_zero_of_not_squarefree
    intro hsq
    obtain ⟨k, rfl⟩ := hqm
    have h2 : q * q ∣ q * (q * k) := ⟨k, by ring⟩
    exact hq.ne_one (Nat.isUnit_iff.mp (hsq q h2))
  · have hc : Nat.Coprime q m := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqm
    rw [isMultiplicative_moebius.map_mul_of_coprime hc, moebius_apply_prime hq]
    ring

/-- [proved-derived; formal-checked] **The shell at every prime**: for prime `q`,
`M_{≥q}(N) = M_{>q}(N) − M_{>q}(N/q)`.  Buchstab's identity for the Möbius function; the
local-to-global transport of the prime simplex, one prime at a time. -/
theorem roughFrom_eq_roughAbove_sub {q : ℕ} (hq : q.Prime) (N : ℕ) :
    roughFrom q N = roughAbove q N - roughAbove q (N / q) := by
  induction N with
  | zero => simp [roughFrom, roughAbove]
  | succ n ih =>
    rw [roughFrom_succ, ih]
    by_cases hdvd : q ∣ n + 1
    · have hk1 : (n + 1) / q = n / q + 1 := by rw [Nat.succ_div, if_pos hdvd]
      obtain ⟨k, hk⟩ := hdvd
      have hk' : k = n / q + 1 := by
        rw [← hk1, hk, Nat.mul_div_cancel_left k hq.pos]
      have hnot : ¬ RoughAbove q (n + 1) := not_roughAbove_of_dvd hq ⟨k, hk⟩
      rw [hk1, roughAbove_succ q n, if_neg hnot, add_zero, roughAbove_succ q (n / q)]
      rw [hk, hk', moebius_prime_mul hq]
      by_cases hqm : q ∣ n / q + 1
      · rw [if_pos hqm, if_neg (not_roughAbove_of_dvd hq hqm)]
        simp
      · rw [if_neg hqm]
        by_cases h : RoughAbove q (n / q + 1)
        · rw [if_pos h, if_pos ((roughFrom_mul_left_iff hq).mpr
            ((roughFrom_iff_roughAbove_of_not_dvd hq hqm).mpr h))]
          ring
        · rw [if_neg h, if_neg (fun hf => h ((roughFrom_iff_roughAbove_of_not_dvd hq hqm).mp
            ((roughFrom_mul_left_iff hq).mp hf)))]
          ring
    · have h1 : (n + 1) / q = n / q := by rw [Nat.succ_div, if_neg hdvd, add_zero]
      rw [h1, roughAbove_succ q n]
      by_cases h : RoughAbove q (n + 1)
      · rw [if_pos h, if_pos ((roughFrom_iff_roughAbove_of_not_dvd hq hdvd).mpr h)]
        ring
      · rw [if_neg h, if_neg (fun hf => h ((roughFrom_iff_roughAbove_of_not_dvd hq hdvd).mp hf))]
        ring

/-- [proved-derived; formal-checked] At the least vertex the rough sum is the Mertens function. -/
theorem roughFrom_two (N : ℕ) : roughFrom 2 N = Soma.Holonics.Millennium.PrimeSimplex.mertens N := by
  unfold roughFrom Soma.Holonics.Millennium.PrimeSimplex.mertens
  apply sum_congr rfl
  intro n _
  have h : RoughFrom 2 n := fun p hp _ => hp.two_le
  rw [if_pos h]

/-- [proved-derived; formal-checked] Above the least vertex, rough means odd. -/
theorem roughAbove_two (N : ℕ) : roughAbove 2 N = Soma.Holonics.Millennium.PrimeSimplex.oddSum N := by
  unfold roughAbove Soma.Holonics.Millennium.PrimeSimplex.oddSum
  apply sum_congr rfl
  intro n hn
  have hn0 : 0 < n := (mem_Ioc.mp hn).1
  have hiff : RoughAbove 2 n ↔ Odd n := by
    constructor
    · intro h
      rw [← Nat.not_even_iff_odd]
      intro heven
      have : 2 < 2 := h 2 Nat.prime_two (even_iff_two_dvd.mp heven)
      exact lt_irrefl _ this
    · intro hodd p hp hpn
      rcases lt_or_eq_of_le hp.two_le with hlt | heq
      · exact hlt
      · exfalso
        rw [← heq] at hpn
        exact hodd.not_two_dvd_nat hpn
  by_cases h : RoughAbove 2 n
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun ho => h (hiff.mpr ho))]

/-- [proved-derived; formal-checked] The top-octave identity of `PrimeSimplex` is the `q = 2`
shell. -/
theorem mertens_shell_two (N : ℕ) :
    Soma.Holonics.Millennium.PrimeSimplex.mertens N =
      Soma.Holonics.Millennium.PrimeSimplex.oddSum N -
        Soma.Holonics.Millennium.PrimeSimplex.oddSum (N / 2) := by
  rw [← roughFrom_two, roughFrom_eq_roughAbove_sub Nat.prime_two, roughAbove_two, roughAbove_two]

section Audit

#print axioms roughFrom_eq_roughAbove_sub
#print axioms mertens_shell_two

end Audit

end Soma.Holonics.Millennium.PrimeSimplexPeeling
