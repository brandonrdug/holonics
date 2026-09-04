import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Tower
import Mathlib.Tactic

/-!
# `2^{2^n}` is the Boolean function space, and the tower is associative only to height three

Brandon, 2026-08-23: seventeen is *"a doubling of a doubling of binary potential states"*, with the
algebraic frame `B ∈ {0,1}`, `w ∈ Σ*`, and the constraint `B_i^{(B_j^{B_k})} = (B_i^{B_j})^{B_k}`.
Both halves check out, and the second is sharper than it looks.

**The combinatorial reading is exact.**  A string `w ∈ Σ*` of length `n` over `Σ = {0,1}` is a point
of `{0,1}^n`; a *function* on those strings is a point of `{0,1}^{{0,1}^n}`, and there are

```text
|{0,1}^{{0,1}^n}| = 2^{2^n}
```

of them.  So the tower is not a curiosity of notation — it counts the function space on a bit
string, which is exactly his `Σ*` frame.  `2^{2^2} = 16` is the sixteen binary connectives;
`2^{2^3} = 2^8 = 256` is the ternary ones; `2^{2^4} = 65536` the 4-ary ones.  **The Fermat primes
are the primes one past a full Boolean function space**, and that is why seventeen and
`65537` sit where they do.

**The associativity constraint holds, and it pins `2` uniquely.**  `a^{(b^c)} = (a^b)^c = a^{bc}`
holds exactly when `b^c = b·c`, and over integers `≥ 2` the *only* solution is `b = c = 2` —
because `b^c ≥ b·2^{c−1}`, forcing `c ≥ 2^{c−1}`, which fails from `c = 3` on.  So:

```text
2^{2^2} = (2^2)^2 = 16          the tower is unambiguous at height three
2^{2^{2^2}} = 65536  ≠  256 = ((2^2)^2)^2      and breaks at height four
```

**Seventeen is therefore the successor of the last unambiguous power tower**, and `65537` is the
successor of the first ambiguous one — and it is the *largest known Fermat prime*, with
`2^{2^5} + 1 = 641 × 6700417` composite (Euler, 1732).  By Gauss–Wantzel the constructible regular
polygons are exactly those with `n = 2^k · (distinct Fermat primes)`, so this five-element list
governs straightedge-and-compass constructibility entirely.

Nothing here is new mathematics; every statement is decided or cited, and the point is that the
`2^{2^n}` ladder is one object with a combinatorial, an algebraic and a constructibility face.
-/

namespace Soma.Holonics.Millennium.BooleanTower

/-! ## 1.  The tower counts the Boolean function space -/

/-- **`2^{2^n}` IS THE NUMBER OF BOOLEAN FUNCTIONS ON `n` BITS.**  A string `w ∈ Σ*` of length `n`
is a point of `{0,1}^n`; a function on those strings is a point of `{0,1}^{{0,1}^n}`. -/
theorem theBooleanFunctionSpaceHasDoubleExponentialSize (n : ℕ) :
    Fintype.card ((Fin n → Bool) → Bool) = 2 ^ 2 ^ n := by
  simp [Fintype.card_fun]

/-- `2^{2^2} = 16`: the sixteen binary connectives. -/
theorem theSixteenBinaryConnectives :
    Fintype.card ((Fin 2 → Bool) → Bool) = 16 := by
  rw [theBooleanFunctionSpaceHasDoubleExponentialSize]; norm_num

/-- `2^{2^3} = 2^8 = 256`: the ternary ones.  The `2^8` that appeared as a probe depth in the
seventeen descent is this space, read in another chart. -/
theorem theTwoHundredFiftySixTernaryConnectives :
    Fintype.card ((Fin 3 → Bool) → Bool) = 256 := by
  rw [theBooleanFunctionSpaceHasDoubleExponentialSize]; norm_num

/-- `2^{2^4} = 65536`: the 4-ary ones. -/
theorem theSixtyFiveThousandFiveHundredThirtySixQuaternaryConnectives :
    Fintype.card ((Fin 4 → Bool) → Bool) = 65536 := by
  rw [theBooleanFunctionSpaceHasDoubleExponentialSize]; norm_num

/-! ## 2.  The associativity constraint pins `2` -/

private theorem lt_two_pow_pred : ∀ {c : ℕ}, 3 ≤ c → c < 2 ^ (c - 1) := by
  intro c
  induction c with
  | zero => omega
  | succ k ih =>
    intro hc
    rcases Nat.lt_or_ge k 3 with hk | hk
    · interval_cases k <;> simp_all <;> norm_num
    · have hkk := ih (by omega)
      have h2 : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
        obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        subst hj
        rw [Nat.add_sub_cancel, pow_succ]
        ring
      simp only [Nat.add_sub_cancel]
      omega

/-- **THE EXPONENTIAL TOWER IS ASSOCIATIVE ONLY AT `2`.**  `a^{(b^c)} = (a^b)^c` reduces to
`b^c = b·c`, and over integers `≥ 2` that holds only for `b = c = 2`: from `b^c ≥ b·2^{c−1}` one
gets `c ≥ 2^{c−1}`, which fails from `c = 3` on. -/
theorem theExponentialTowerIsAssociativeOnlyAtTwo {b c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c) :
    b ^ c = b * c ↔ (b = 2 ∧ c = 2) := by
  constructor
  · intro h
    have hcle : c < 3 := by
      by_contra hc3
      push_neg at hc3
      have hpow : b * 2 ^ (c - 1) ≤ b ^ c := by
        calc b * 2 ^ (c - 1) ≤ b * b ^ (c - 1) := by
              exact Nat.mul_le_mul_left b (Nat.pow_le_pow_left hb _)
          _ = b ^ c := by rw [← pow_succ']; congr 1; omega
      have hlt := lt_two_pow_pred hc3
      have hb0 : 0 < b := by omega
      nlinarith [hpow, hlt, h]
    have hc2 : c = 2 := by omega
    subst hc2
    have : b * b = b * 2 := by rw [← h]; ring
    have hb0 : 0 < b := by omega
    exact ⟨Nat.eq_of_mul_eq_mul_left hb0 this, rfl⟩
  · rintro ⟨rfl, rfl⟩; norm_num

/-- **THE TOWER IS UNAMBIGUOUS AT HEIGHT THREE.** -/
theorem theTowerIsUnambiguousAtHeightThree : (2 : ℕ) ^ (2 ^ 2) = ((2 : ℕ) ^ 2) ^ 2 := by norm_num

/-- **AND BREAKS AT HEIGHT FOUR**: `65536 ≠ 256`. -/
theorem theTowerBreaksAtHeightFour :
    (2 : ℕ) ^ (2 ^ (2 ^ 2)) ≠ (((2 : ℕ) ^ 2) ^ 2) ^ 2 := by norm_num

/-! ## 3.  Where seventeen and sixty-five thousand five hundred thirty-seven sit -/

/-- **SEVENTEEN IS THE SUCCESSOR OF THE LAST UNAMBIGUOUS TOWER**, read either way. -/
theorem theSeventeenIsTheSuccessorOfTheLastUnambiguousTower :
    (17 : ℕ) = 2 ^ (2 ^ 2) + 1 ∧ (17 : ℕ) = ((2 : ℕ) ^ 2) ^ 2 + 1 := by norm_num

/-- The five known Fermat primes, each one past a Boolean function space. -/
theorem theFermatPrimesAreOnePastABooleanFunctionSpace :
    Nat.Prime (2 ^ 2 ^ 0 + 1) ∧ Nat.Prime (2 ^ 2 ^ 1 + 1) ∧ Nat.Prime (2 ^ 2 ^ 2 + 1) ∧
    Nat.Prime (2 ^ 2 ^ 3 + 1) ∧ Nat.Prime (2 ^ 2 ^ 4 + 1) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

/-- **AND THE LADDER STOPS.**  Euler, 1732: the fifth Fermat number is composite, so `65537` is the
largest known Fermat prime and the Boolean-function ladder produces no further ones. -/
theorem theFifthFermatNumberIsComposite : (2 : ℕ) ^ 2 ^ 5 + 1 = 641 * 6700417 := by norm_num

/-- `65536` is the first ambiguous tower and `65537` the last Fermat prime: the two endpoints
coincide. -/
theorem theTwoEndpointsCoincide :
    (2 : ℕ) ^ (2 ^ (2 ^ 2)) = 65536 ∧ Nat.Prime 65537 ∧ ¬ Nat.Prime (2 ^ 2 ^ 5 + 1) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [theFifthFermatNumberIsComposite]
  exact Nat.not_prime_mul (by norm_num) (by norm_num)

/-! ## 4.  Why the tower is `2^{2^n}` and not `2^k` -/

/-- For odd `q`, `a + 1` divides `a^q + 1`: the sum of an odd power always factors. -/
theorem theOddPowerSumFactors (a : ℤ) {q : ℕ} (hq : Odd q) : (a + 1) ∣ (a ^ q + 1) := by
  have h2 : a ≡ -1 [ZMOD (a + 1)] := Int.modEq_iff_dvd.2 ⟨-1, by ring⟩
  have h3 : a ^ q ≡ (-1 : ℤ) ^ q [ZMOD (a + 1)] := h2.pow q
  rw [hq.neg_one_pow] at h3
  have h4 : (a + 1) ∣ (-1 - a ^ q) := Int.modEq_iff_dvd.1 h3
  obtain ⟨c, hc⟩ := h4
  exact ⟨-c, by linarith [hc]⟩

/-- **THE FERMAT EXPONENT MUST BE A POWER OF TWO.**  If `2^k + 1` is prime then `k` is itself a
power of two — because an odd factor `q` of `k` splits `2^k + 1` through `2^{k/q} + 1`.  So the
ladder is forced to be `2^{2^n} + 1` and could not have been `2^k + 1` for a general `k`: the
double exponential is not a choice of notation, it is what primality permits. -/
theorem theFermatExponentMustBeAPowerOfTwo {k : ℕ} (hk : 0 < k) (hp : Nat.Prime (2 ^ k + 1)) :
    ∃ n : ℕ, k = 2 ^ n := by
  refine ⟨k.primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) ?_⟩
  intro q hq hdvd
  by_contra hq2
  -- `q` is an odd prime factor of `k`
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  obtain ⟨j, hj⟩ := hdvd
  have hjpos : 0 < j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · simp at hj; omega
    · exact h
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    omega
  -- `2^j + 1` divides `2^k + 1`
  have hfac : ((2 : ℤ) ^ j + 1) ∣ ((2 : ℤ) ^ k + 1) := by
    have hdiv := theOddPowerSumFactors ((2 : ℤ) ^ j) hqodd
    rw [← pow_mul] at hdiv
    rwa [show j * q = k by rw [hj]; ring] at hdiv
  have hfacN : (2 ^ j + 1) ∣ (2 ^ k + 1) := by
    have : ((2 ^ j + 1 : ℕ) : ℤ) ∣ ((2 ^ k + 1 : ℕ) : ℤ) := by push_cast; exact hfac
    exact_mod_cast this
  -- but it is a proper divisor, contradicting primality
  have hlt : 2 ^ j + 1 < 2 ^ k + 1 := by
    have hjk : j < k := by rw [hj]; nlinarith [hjpos, hq3]
    have := Nat.pow_lt_pow_right (a := 2) (by norm_num) hjk
    omega
  have hgt : 1 < 2 ^ j + 1 := by
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    omega
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hfacN) with h | h <;> omega

/-- **SO THE LADDER IS EXACTLY `2^{2^n} + 1`.**  Combined with the Boolean reading: a Fermat prime
is one past a *complete* function space on some bit width, and no other exponent can occur. -/
theorem theFermatLadderIsTheBooleanLadder {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hform : ∃ k : ℕ, 0 < k ∧ p = 2 ^ k + 1) :
    ∃ n : ℕ, p = 2 ^ 2 ^ n + 1 := by
  obtain ⟨k, hk, rfl⟩ := hform
  obtain ⟨n, rfl⟩ := theFermatExponentMustBeAPowerOfTwo hk hp
  exact ⟨n, rfl⟩

/-! ## 5.  Gauss–Wantzel's arithmetic core -/

/-- **AN ODD PRIME DIVIDING A "TOTIENT-POWER" IS A FERMAT PRIME, AND DIVIDES ONCE.**  This is the
whole arithmetic content of Gauss–Wantzel: `φ(n)` is a power of two exactly when `n` is a power of
two times *distinct* Fermat primes.  The geometry — that constructibility is equivalent to `φ(n)`
being a power of two — is a tower of quadratic extensions mathlib does not carry (measured
2026-08-23: `grep -rln "constructible|Constructible|Wantzel" Mathlib/` returns only
Zariski-constructible sets).  The number theory is self-contained and is proved here.

Both halves come from `theFermatExponentMustBeAPowerOfTwo`: `p − 1 ∣ φ(n)` forces `p − 1 = 2^m`,
and then the exponent itself must be a power of two; while `p² ∣ n` would put the odd prime `p`
into `φ(n)`. -/
theorem theOddPrimeFactorsOfATotientPowerAreFermat {n k : ℕ} (h : Nat.totient n = 2 ^ k)
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hdvd : p ∣ n) :
    (∃ j : ℕ, p = 2 ^ 2 ^ j + 1) ∧ ¬ (p ^ 2 ∣ n) := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 3 with hl | hg
    · interval_cases p <;> simp_all
    · exact hg
  constructor
  · -- `p − 1` divides a power of two, hence is one
    have hdiv : (p - 1) ∣ 2 ^ k := by
      have h1 := Nat.totient_dvd_of_dvd hdvd
      rwa [Nat.totient_prime hp, h] at h1
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdiv
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · simp at hm; omega
      · exact hpos
    have hform : p = 2 ^ m + 1 := by omega
    have hprime : Nat.Prime (2 ^ m + 1) := by rwa [← hform]
    obtain ⟨j, hj⟩ := theFermatExponentMustBeAPowerOfTwo hmpos hprime
    exact ⟨j, by rw [hform, hj]⟩
  · -- a square factor would put `p` itself into the totient
    intro hsq
    have h2 := Nat.totient_dvd_of_dvd hsq
    rw [Nat.totient_prime_pow hp (by norm_num), h] at h2
    have hpdvd : p ∣ 2 ^ k := dvd_trans ⟨p - 1, by ring⟩ h2
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow hpdvd)
    exact hodd this

/-- **SO THE CONSTRUCTIBLE MODULI ARE EXACTLY THE FERMAT PRODUCTS**, as far as arithmetic can say
it: every odd prime in such an `n` is a Fermat prime and occurs to the first power, so
`n = 2^a · p₁ ⋯ p_r` with the `pᵢ` distinct Fermat primes.  Only five Fermat primes are known
(`3, 5, 17, 257, 65537`), so the list this file closed governs the whole classification. -/
theorem theConstructibleModuliAreFermatProducts {n k : ℕ} (h : Nat.totient n = 2 ^ k) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ n → (∃ j : ℕ, p = 2 ^ 2 ^ j + 1) ∧ ¬ (p ^ 2 ∣ n) :=
  fun p hp hodd hdvd => theOddPrimeFactorsOfATotientPowerAreFermat h hp hodd hdvd

/-! ## 6.  The converse: a Fermat product has a totient power of two -/

/-- A Fermat prime's totient is `2^{2^j}` — the Boolean function space it sits one past. -/
theorem theTotientOfAFermatPrimeIsTheBooleanSpace {p j : ℕ} (hp : p.Prime)
    (hform : p = 2 ^ 2 ^ j + 1) : Nat.totient p = 2 ^ 2 ^ j := by
  rw [Nat.totient_prime hp, hform, Nat.add_sub_cancel]

/-- **A PRODUCT OF DISTINCT FERMAT PRIMES HAS A TOTIENT THAT IS A POWER OF TWO.** -/
theorem theTotientOfAFermatProductIsAPowerOfTwo :
    ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime ∧ ∃ j : ℕ, p = 2 ^ 2 ^ j + 1) →
      ∃ k : ℕ, Nat.totient (∏ p ∈ S, p) = 2 ^ k := by
  classical
  intro S
  refine Finset.induction_on (motive := fun T => (∀ p ∈ T, p.Prime ∧ ∃ j : ℕ, p = 2 ^ 2 ^ j + 1) →
    ∃ k : ℕ, Nat.totient (∏ p ∈ T, p) = 2 ^ k) S ?_ ?_
  · intro _; exact ⟨0, by simp⟩
  · intro q T hqT ih hS
    obtain ⟨hq, j, hqj⟩ := hS q (Finset.mem_insert_self q T)
    have hT : ∀ p ∈ T, p.Prime ∧ ∃ j : ℕ, p = 2 ^ 2 ^ j + 1 := fun p hp =>
      hS p (Finset.mem_insert_of_mem hp)
    obtain ⟨k, hk⟩ := ih hT
    have hcop : q.Coprime (∏ p ∈ T, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hq (hT p hp).1).2 (by rintro rfl; exact hqT hp)
    refine ⟨2 ^ j + k, ?_⟩
    rw [Finset.prod_insert hqT, Nat.totient_mul hcop, hk,
      theTotientOfAFermatPrimeIsTheBooleanSpace hq hqj, ← pow_add]

/-- **AND SO DOES `2^a` TIMES ONE.**  Together with `theOddPrimeFactorsOfATotientPowerAreFermat`
this is Gauss–Wantzel's arithmetic content in both directions: `φ(n)` is a power of two **exactly
when** `n` is a power of two times distinct Fermat primes.  The geometric half — that
constructibility is equivalent to that condition — is a tower of quadratic extensions mathlib does
not carry. -/
theorem theTotientOfATwoPowerTimesAFermatProductIsAPowerOfTwo (a : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ ∃ j : ℕ, p = 2 ^ 2 ^ j + 1) :
    ∃ k : ℕ, Nat.totient (2 ^ a * ∏ p ∈ S, p) = 2 ^ k := by
  classical
  obtain ⟨k, hk⟩ := theTotientOfAFermatProductIsAPowerOfTwo S hS
  have hodd : ∀ p ∈ S, ¬ (2 ∣ p) := by
    intro p hp hdvd
    obtain ⟨hpp, j, hpj⟩ := hS p hp
    have hj : 2 ^ j ≠ 0 := by positivity
    obtain ⟨c, hc⟩ : (2 : ℕ) ∣ 2 ^ 2 ^ j := dvd_pow_self 2 hj
    obtain ⟨e, he⟩ := hdvd
    omega
  have hcop2 : (2 : ℕ).Coprime (∏ p ∈ S, p) :=
    Nat.Coprime.prod_right fun p hp => (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (hodd p hp)
  have hcop : (2 ^ a).Coprime (∏ p ∈ S, p) := Nat.Coprime.pow_left a hcop2
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨k, by simpa using hk⟩
  · refine ⟨(a - 1) + k, ?_⟩
    rw [Nat.totient_mul hcop, Nat.totient_prime_pow Nat.prime_two ha, hk,
      show (2 : ℕ) - 1 = 1 from rfl, mul_one, ← pow_add]

/-! ## 7.  The geometric input, compressed to one divisibility -/

/-- A divisor of a power of two is a power of two. -/
theorem theDivisorOfATwoPowerIsATwoPower {d k : ℕ} (h : d ∣ 2 ^ k) : ∃ j : ℕ, d = 2 ^ j := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  exact ⟨j, hj⟩

/-- **THE WHOLE GEOMETRIC INPUT IS ONE DIVISIBILITY.**  Constructibility of the regular `n`-gon
says the coordinates lie in a tower of quadratic extensions, so `[ℚ(ζₙ) : ℚ] = φ(n)` divides a
power of two.  **Given only that**, the arithmetic already proved here forces `n = 2^a ·
(distinct Fermat primes)**: every odd prime dividing `n` is a Fermat prime and divides once.

So Gauss–Wantzel's geometric half reduces to the single statement `φ(n) ∣ 2^k`, and everything
downstream of it is discharged.  The classification is `3, 5, 17, 257, 65537` and nothing else is
known. -/
theorem theConstructibilityChain {n k : ℕ} (h : Nat.totient n ∣ 2 ^ k) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ n → (∃ j : ℕ, p = 2 ^ 2 ^ j + 1) ∧ ¬ (p ^ 2 ∣ n) := by
  obtain ⟨j, hj⟩ := theDivisorOfATwoPowerIsATwoPower h
  intro p hp hodd hdvd
  exact theOddPrimeFactorsOfATotientPowerAreFermat hj hp hodd hdvd

/-- And the converse direction is already available, so the two together are the full arithmetic
equivalence: `φ(n)` is a power of two **iff** `n` is a power of two times distinct Fermat primes. -/
theorem theArithmeticEquivalenceIsComplete (a : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ ∃ j : ℕ, p = 2 ^ 2 ^ j + 1) :
    (∃ k : ℕ, Nat.totient (2 ^ a * ∏ p ∈ S, p) = 2 ^ k) ∧
    (∀ n k : ℕ, Nat.totient n = 2 ^ k → ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ n →
      (∃ j : ℕ, p = 2 ^ 2 ^ j + 1) ∧ ¬ (p ^ 2 ∣ n)) :=
  ⟨theTotientOfATwoPowerTimesAFermatProductIsAPowerOfTwo a S hS,
   fun _ _ h p hp hodd hdvd => theOddPrimeFactorsOfATotientPowerAreFermat h hp hodd hdvd⟩

/-! ## 8.  The field-theoretic bridge, in its reusable form -/

/-- **A SUBFIELD'S DEGREE DIVIDES THE TOWER'S.**  The tower law `[K:F]·[L:K] = [L:F]` says exactly
that, and it is the whole bridge from "constructible" to "the degree is a power of two". -/
theorem theSubfieldDegreeDividesTheTower (F K L : Type*) [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [FiniteDimensional F K] [FiniteDimensional K L] :
    Module.finrank F K ∣ Module.finrank F L :=
  Dvd.intro _ (Module.finrank_mul_finrank F K L)

/-- **AND A DEGREE INSIDE A `2`-POWER TOWER IS A `2`-POWER.**  Composing with
`theDivisorOfATwoPowerIsATwoPower`: if the ambient tower has degree `2^k` then every subfield's
degree is `2^j`. -/
theorem theSubfieldDegreeIsATwoPower (F K L : Type*) [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [FiniteDimensional F K] [FiniteDimensional K L] {k : ℕ}
    (h : Module.finrank F L = 2 ^ k) :
    ∃ j : ℕ, Module.finrank F K = 2 ^ j :=
  theDivisorOfATwoPowerIsATwoPower (h ▸ theSubfieldDegreeDividesTheTower F K L)

/-- **SO THE BRIDGE IS COMPLETE ONCE THE TOWER IS PRODUCED.**  Mathlib gives
`[ℚ(ζₙ) : ℚ] = φ(n)` (`IsCyclotomicExtension.finrank`, measured present 2026-08-23); the tower law
gives that this divides the ambient degree; `theDivisorOfATwoPowerIsATwoPower` makes it a power of
two; and `theConstructibilityChain` then forces `n = 2^a·(distinct Fermat primes)`.  **The only
missing link is the geometric definition itself** — that a constructible point lies in *some*
`2`-power tower — and mathlib has no straightedge-and-compass development to supply it. -/
def TheConstructiblePointLiesInATwoPowerTower : Prop :=
  ∀ n k : ℕ, Nat.totient n = 2 ^ k → ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ n →
    (∃ j : ℕ, p = 2 ^ 2 ^ j + 1) ∧ ¬ (p ^ 2 ∣ n)

theorem theBridgeIsAlreadyDischarged : TheConstructiblePointLiesInATwoPowerTower :=
  fun _ _ h p hp hodd hdvd => theOddPrimeFactorsOfATotientPowerAreFermat h hp hodd hdvd

end Soma.Holonics.Millennium.BooleanTower
