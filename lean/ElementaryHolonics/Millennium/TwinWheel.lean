import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

/-!
# The twin slot is a letter of the wheel word, and the cut law is exact

The primorial wheel of `research/records/2026-07-17_THE_WHEEL_RECURS_THE_ZERO_WAVE_CARRIES_THE_PRIME_CURRENT.md`
is the coprime population `{r : gcd(r, M) = 1}` read as a cyclic gap word `W_M`, recursively built
by COPY/CUT/JOIN: entering a new prime `q` copies the old support `q` times, cuts the one lift
divisible by `q`, and joins the two gaps that met there.

A **twin slot** is a letter `2` in that word — a residue `r` with `r` and `r + 2` both surviving.
The cut law for those letters is exact and this file proves it: each `2`-letter has two endpoints,
a cut destroys it exactly when the cut lands on one of them, the two endpoints lie in distinct
copies, and a join can never *create* a `2` because it produces a gap of at least `4`.  Hence

```text
twinSlots (M · q) = (q − 2) · twinSlots M ,      twinSlots 6 = 1
twinSlots (primorial up to y) = ∏_{5 ≤ p ≤ y} (p − 2)
```

Measured against the wheels themselves before it was proved: `1, 3, 15, 135, 1485` at
`M = 6, 30, 210, 2310, 30030`.

**What this settles and what it does not.**  It settles that the sieve *never runs out of
admissible twin positions* — the count is a product of positive factors and grows without bound,
so no finite stage of the wheel refuses the twin pattern.  In the receiver language that is the
statement that the twin pair is never a collapsed pair of the wheel family at any horizon.  It
does **not** settle the twin prime conjecture, which is the separate claim that admissibility
survives to actuality; the wheel is the collapsed population and the conjecture is its separator
question.  `TwinPrimeConjecture` below is a named `Prop` with real quantifiers, discharged nowhere.

The local ratio `p(p − 2)/(p − 1)²` that falls out of the cut law is exactly the Hardy–Littlewood
singular-series factor, and it is derived here from the wheel rather than assumed.
-/

namespace Soma.Holonics.Millennium.TwinWheel

open Finset

set_option maxRecDepth 4000

instance instDecidableIsUnitZMod (n : ℕ) [NeZero n] : DecidablePred (IsUnit : ZMod n → Prop) :=
  fun _ => decidable_of_iff _ isUnit_iff_exists_inv.symm

/-- The `h`-slots of the wheel at horizon `M`: residues at which both `r` and `r + h` survive
every cut.  For `h = 2` these are exactly the `2`-letters of the cyclic gap word `W_M`. -/
def gapSlots (h : ℕ) (M : ℕ) [NeZero M] : ℕ :=
  (univ.filter (fun r : ZMod M => IsUnit r ∧ IsUnit (r + (h : ZMod M)))).card

/-- The twin slots: the `2`-letters of `W_M`. -/
abbrev twinSlots (M : ℕ) [NeZero M] : ℕ := gapSlots 2 M

/-- A total form with a junk value at `0`, so product statements need no instance threading. -/
noncomputable def gapCount (h M : ℕ) : ℕ := if hM : M = 0 then 0 else @gapSlots h M ⟨hM⟩

@[simp] theorem gapCount_eq (h M : ℕ) [NeZero M] : gapCount h M = gapSlots h M := by
  rw [gapCount, dif_neg (NeZero.ne M)]

/-! ## 1.  A ring equivalence moves units, so the wheel factors -/

theorem theEquivalenceMovesUnits {A B : Type*} [CommMonoid A] [CommMonoid B] (e : A ≃* B)
    (a : A) : IsUnit (e a) ↔ IsUnit a := by
  simp only [isUnit_iff_exists_inv]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨e.symm b, e.injective (by rw [map_mul, MulEquiv.apply_symm_apply, hb, map_one])⟩
  · rintro ⟨b, hb⟩
    exact ⟨e b, by rw [← map_mul, hb, map_one]⟩

/-- **THE COPY/CUT/JOIN LAW IS MULTIPLICATIVITY.**  Entering a coprime horizon multiplies the slot
population, because the Chinese remainder equivalence carries `r ↦ r + h` to itself componentwise
and carries units to units. -/
theorem theGapSlotsAreMultiplicative {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)] (h : ℕ)
    (hc : m.Coprime n) :
    gapSlots h (m * n) = gapSlots h m * gapSlots h n := by
  classical
  set e := ZMod.chineseRemainder hc with he
  have hcast : ∀ r : ZMod (m * n),
      e (r + (h : ZMod (m * n))) = (((e r).1 + (h : ZMod m)), ((e r).2 + (h : ZMod n))) := by
    intro r
    rw [map_add, map_natCast]
    rfl
  have key : ∀ r : ZMod (m * n),
      (IsUnit r ∧ IsUnit (r + (h : ZMod (m * n)))) ↔
        ((IsUnit (e r).1 ∧ IsUnit ((e r).1 + (h : ZMod m))) ∧
         (IsUnit (e r).2 ∧ IsUnit ((e r).2 + (h : ZMod n)))) := by
    intro r
    have hu : IsUnit r ↔ (IsUnit (e r).1 ∧ IsUnit (e r).2) := by
      rw [← theEquivalenceMovesUnits e.toMulEquiv r, Prod.isUnit_iff]; rfl
    have hv : IsUnit (r + (h : ZMod (m * n))) ↔
        (IsUnit ((e r).1 + (h : ZMod m)) ∧ IsUnit ((e r).2 + (h : ZMod n))) := by
      rw [← theEquivalenceMovesUnits e.toMulEquiv (r + (h : ZMod (m * n))), Prod.isUnit_iff]
      rw [show (e.toMulEquiv (r + (h : ZMod (m * n)))) = e (r + (h : ZMod (m * n))) from rfl,
        hcast r]
    rw [hu, hv]; tauto
  have hcard :
      (univ.filter (fun r : ZMod (m * n) => IsUnit r ∧ IsUnit (r + (h : ZMod (m * n))))).card =
      (univ.filter (fun z : ZMod m × ZMod n =>
          (IsUnit z.1 ∧ IsUnit (z.1 + (h : ZMod m))) ∧
          (IsUnit z.2 ∧ IsUnit (z.2 + (h : ZMod n))))).card := by
    refine Finset.card_equiv e.toEquiv ?_
    intro r; simp only [mem_filter, mem_univ, true_and]
    exact key r
  rw [gapSlots, hcard, gapSlots, gapSlots, ← Finset.card_product]
  congr 1
  ext z
  simp only [mem_filter, mem_univ, true_and, Finset.mem_product]

theorem theTwinSlotsAreMultiplicative {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (h : m.Coprime n) :
    twinSlots (m * n) = twinSlots m * twinSlots n :=
  theGapSlotsAreMultiplicative 2 h

/-! ## 2.  The count at one place -/

/-- **THE CUT REMOVES EXACTLY TWO LETTERS AT A PRIME THAT DOES NOT DIVIDE THE GAP.**  In `ZMod p`
the survivors are the nonzero residues, and an `h`-slot fails exactly at `r = 0` and `r = −h`,
which are distinct because `p ∤ h`.  So the wheel loses two positions and keeps `p − 2`. -/
theorem theGapSlotCountAtAPrimeMissingTheGap {p h : ℕ} (hp : p.Prime) (hdvd : ¬ (p ∣ h)) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    gapSlots h p = p - 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  classical
  have hh : ((h : ℕ) : ZMod p) ≠ 0 := fun hz => hdvd ((CharP.cast_eq_zero_iff (ZMod p) p h).1 hz)
  have hne : (0 : ZMod p) ≠ -(h : ZMod p) := by
    intro hz
    exact hh (by linear_combination hz)
  have hfil : (univ.filter (fun r : ZMod p => IsUnit r ∧ IsUnit (r + (h : ZMod p))))
      = univ \ ({0, -(h : ZMod p)} : Finset (ZMod p)) := by
    ext r
    simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_insert, mem_singleton, not_or]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rintro rfl; exact not_isUnit_zero h1
      · rintro rfl
        rw [neg_add_cancel] at h2
        exact not_isUnit_zero h2
    · rintro ⟨h1, h2⟩
      refine ⟨isUnit_iff_ne_zero.2 h1, isUnit_iff_ne_zero.2 ?_⟩
      intro hz; exact h2 (by linear_combination hz)
  rw [gapSlots, hfil, Finset.card_univ_diff, ZMod.card,
    Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

/-- **AND EXACTLY ONE LETTER AT A PRIME THAT DIVIDES THE GAP.**  There `r` and `r + h` are the
same residue, so the two lost positions coincide and the wheel keeps `p − 1`.  This is why an
admissible pattern's density is a product of `(p − 2)/p` off the gap and `(p − 1)/p` on it. -/
theorem theGapSlotCountAtAPrimeDividingTheGap {p h : ℕ} (hp : p.Prime) (hdvd : p ∣ h) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    gapSlots h p = p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  classical
  have hh : ((h : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p h).2 hdvd
  have hfil : (univ.filter (fun r : ZMod p => IsUnit r ∧ IsUnit (r + (h : ZMod p))))
      = univ \ ({0} : Finset (ZMod p)) := by
    ext r
    simp only [hh, add_zero, mem_filter, mem_univ, true_and, mem_sdiff, mem_singleton, and_self]
    exact isUnit_iff_ne_zero
  rw [gapSlots, hfil, Finset.card_univ_diff, ZMod.card, Finset.card_singleton]

/-- The twin case: `p ∤ 2` is `p ≠ 2`. -/
theorem theTwinSlotCountAtAnOddPrime {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    twinSlots p = p - 2 := by
  refine theGapSlotCountAtAPrimeMissingTheGap hp ?_
  intro hd
  exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)

/-- At the place `2` the wheel keeps one letter: the odd residues, and `r + 2` is odd with `r`. -/
theorem theTwinSlotCountAtTwo : twinSlots 2 = 1 := by decide

/-- At the place `3` only one letter survives — `3 − 2 = 1`. -/
theorem theTwinSlotCountAtThree : twinSlots 3 = 1 := by decide

/-! ## 3.  The measured wheels, now derived -/

theorem theWheelAtSix : twinSlots (2 * 3) = 1 := by decide

theorem theWheelAtThirty : twinSlots (2 * 3 * 5) = 3 := by
  have h : (2 * 3 : ℕ).Coprime 5 :=
    Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 (by decide))
  have hm := theTwinSlotsAreMultiplicative (m := 2 * 3) (n := 5) h
  rw [theTwinSlotCountAtAnOddPrime (p := 5) (by norm_num) (by norm_num),
    theWheelAtSix] at hm
  exact hm

theorem theWheelAtTwoHundredTen : twinSlots (2 * 3 * 5 * 7) = 15 := by
  have h : (2 * 3 * 5 : ℕ).Coprime 7 :=
    Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 (by decide))
  have hm := theTwinSlotsAreMultiplicative (m := 2 * 3 * 5) (n := 7) h
  rw [theTwinSlotCountAtAnOddPrime (p := 7) (by norm_num) (by norm_num),
    theWheelAtThirty] at hm
  exact hm

/-- **THE CUT LAW, IN GENERAL FORM.**  Entering a new odd prime `q` copies the wheel `q` times and
removes exactly two letters per copy — the copy whose left endpoint is cut and the copy whose right
endpoint is cut, distinct because `q` is odd.  A join can never create a `2`, because joining two
gaps of a wheel past `6` produces a gap of at least `4`.  Hence `d(M·q) = (q − 2)·d(M)`, and the
primorial twin population is `∏_{5 ≤ p ≤ y} (p − 2)`.  Measured on the wheels before it was proved:
`1, 3, 15, 135, 1485` at `M = 6, 30, 210, 2310, 30030`. -/
theorem theCutLawRemovesTwoLettersPerCopy {M q : ℕ} [NeZero M] [NeZero q] [NeZero (M * q)]
    (hq : q.Prime) (hq2 : q ≠ 2) (h : M.Coprime q) :
    twinSlots (M * q) = (q - 2) * twinSlots M := by
  rw [theTwinSlotsAreMultiplicative h, theTwinSlotCountAtAnOddPrime hq hq2, Nat.mul_comm]

/-! ## 4.  The wheel never refuses the twin pattern -/

/-- **THE ADMISSIBLE TWIN POPULATION IS UNBOUNDED.**  Adjoining a prime `p` to the horizon `6`
multiplies the twin population by `p − 2`, and there are arbitrarily large primes, so no finite
sieve horizon refuses the twin pattern.  The wheel is a *collapsed population*, never a
separator. -/
theorem theAdmissibleTwinPopulationIsUnbounded (N : ℕ) :
    ∃ M : ℕ, ∃ _ : NeZero M, N < twinSlots M := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 7)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have hcop : (6 : ℕ).Coprime p := by
    have h3 : ¬ (p ∣ 6) := by
      intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
    exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 h3)
  haveI : NeZero (6 * p) := ⟨Nat.mul_ne_zero (by norm_num) hp.ne_zero⟩
  refine ⟨6 * p, inferInstance, ?_⟩
  have hm := theTwinSlotsAreMultiplicative (m := 6) (n := p) hcop
  rw [theTwinSlotCountAtAnOddPrime hp hp2] at hm
  rw [hm, theWheelAtSix]
  omega

/-- **NO HORIZON EVER CLOSES A TWIN SLOT COMPLETELY.** -/
theorem theWheelAlwaysCarriesATwinSlot {M : ℕ} [NeZero M] (h : 0 < twinSlots M) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hcop : M.Coprime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : NeZero (M * q) := ⟨Nat.mul_ne_zero (NeZero.ne M) hq.ne_zero⟩
    0 < twinSlots (M * q) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : NeZero (M * q) := ⟨Nat.mul_ne_zero (NeZero.ne M) hq.ne_zero⟩
  have hm := theTwinSlotsAreMultiplicative (m := M) (n := q) hcop
  rw [theTwinSlotCountAtAnOddPrime hq hq2] at hm
  rw [hm]
  have h3 : 3 ≤ q := by have := hq.two_le; omega
  exact Nat.mul_pos h (by omega)

/-! ## 5.  The singular series factor is the wheel ratio -/

/-- **THE HARDY–LITTLEWOOD LOCAL FACTOR IS THE WHEEL'S OWN RATIO.**  The twin density at the place
`p` is `(p − 2)/p`; the square of the single-prime density is `((p − 1)/p)²`; their quotient is
`p(p − 2)/(p − 1)²`, the factor of the twin-prime singular series.  Derived from the cut law, not
imported. -/
theorem theSingularSeriesFactorIsTheWheelRatio {p : ℕ} (hp : 2 < p) :
    ((p : ℚ) - 2) / p / (((p : ℚ) - 1) / p) ^ 2 = (p : ℚ) * ((p : ℚ) - 2) / ((p : ℚ) - 1) ^ 2 := by
  have hq : (2 : ℚ) < p := by exact_mod_cast hp
  have h0 : (p : ℚ) ≠ 0 := by intro h; rw [h] at hq; linarith
  have h1 : (p : ℚ) - 1 ≠ 0 := by intro h; nlinarith
  field_simp

/-! ## 6.  The primorial product, and the singular series -/

theorem theGapCountIsMultiplicative {m n : ℕ} (h : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hc : m.Coprime n) : gapCount h (m * n) = gapCount h m * gapCount h n := by
  haveI : NeZero m := ⟨hm⟩
  haveI : NeZero n := ⟨hn⟩
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero hm hn⟩
  simp only [gapCount_eq]
  exact theGapSlotsAreMultiplicative h hc

theorem theTwinCountAtTheEmptyHorizon : gapCount 2 1 = 1 := by
  rw [gapCount, dif_neg one_ne_zero]
  rfl

/-- **THE PRIMORIAL TWIN POPULATION IS `∏ (p − 2)`.**  The `Finset.prod` form of the cut law: over
any finite set of odd primes the wheel's twin-slot count is the product of `p − 2`. -/
theorem theTwinSlotProductOverAPrimorial :
    ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime ∧ p ≠ 2) →
      gapCount 2 (∏ p ∈ S, p) = ∏ p ∈ S, (p - 2) := by
  classical
  intro S
  refine Finset.induction_on (motive := fun T => (∀ p ∈ T, p.Prime ∧ p ≠ 2) →
    gapCount 2 (∏ p ∈ T, p) = ∏ p ∈ T, (p - 2)) S ?_ ?_
  · intro _; simpa using theTwinCountAtTheEmptyHorizon
  · intro q T hqT ih hS
    have hq := hS q (mem_insert_self q T)
    have hT : ∀ p ∈ T, p.Prime ∧ p ≠ 2 := fun p hp => hS p (mem_insert_of_mem hp)
    have hprodne : (∏ p ∈ T, p) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun p hp => (hT p hp).1.ne_zero
    have hcop : q.Coprime (∏ p ∈ T, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hq.1 (hT p hp).1).2 (by rintro rfl; exact hqT hp)
    rw [Finset.prod_insert hqT, Finset.prod_insert hqT,
      theGapCountIsMultiplicative 2 hq.1.ne_zero hprodne hcop, ih hT]
    congr 1
    haveI : NeZero q := ⟨hq.1.ne_zero⟩
    rw [gapCount_eq]
    exact theTwinSlotCountAtAnOddPrime hq.1 hq.2

/-- Euler's function on the same horizon. -/
theorem theTotientOfAPrimorial :
    ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime ∧ p ≠ 2) →
      (∏ p ∈ S, p).totient = ∏ p ∈ S, (p - 1) := by
  classical
  intro S
  refine Finset.induction_on (motive := fun T => (∀ p ∈ T, p.Prime ∧ p ≠ 2) →
    (∏ p ∈ T, p).totient = ∏ p ∈ T, (p - 1)) S ?_ ?_
  · intro _; simp
  · intro q T hqT ih hS
    have hq := hS q (mem_insert_self q T)
    have hT : ∀ p ∈ T, p.Prime ∧ p ≠ 2 := fun p hp => hS p (mem_insert_of_mem hp)
    have hcop : q.Coprime (∏ p ∈ T, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hq.1 (hT p hp).1).2 (by rintro rfl; exact hqT hp)
    rw [Finset.prod_insert hqT, Finset.prod_insert hqT, Nat.totient_mul hcop, ih hT,
      Nat.totient_prime hq.1]

/-- **THE SINGULAR SERIES PARTIAL PRODUCT IS THE WHEEL'S OWN DENSITY.**  The twin-slot density
against the square of the prime density, over any finite set of odd primes, is exactly the
partial product `∏ p(p − 2)/(p − 1)²` of the twin-prime singular series — derived from the cut
law, not imported from an analytic heuristic. -/
theorem theSingularSeriesPartialProductIsTheWheelDensity (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) :
    ((gapCount 2 (∏ p ∈ S, p) : ℚ) * (∏ p ∈ S, (p : ℚ))) /
        (((∏ p ∈ S, p).totient : ℚ)) ^ 2
      = ∏ p ∈ S, ((p : ℚ) * ((p : ℚ) - 2) / ((p : ℚ) - 1) ^ 2) := by
  classical
  rw [theTwinSlotProductOverAPrimorial S hS, theTotientOfAPrimorial S hS]
  have h2 : ((∏ p ∈ S, (p - 2) : ℕ) : ℚ) = ∏ p ∈ S, ((p : ℚ) - 2) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp3 : 2 ≤ p := (hS p hp).1.two_le
    push_cast [Nat.cast_sub hp3]
    ring
  have h1 : ((∏ p ∈ S, (p - 1) : ℕ) : ℚ) = ∏ p ∈ S, ((p : ℚ) - 1) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp1 : 1 ≤ p := (hS p hp).1.one_lt.le.trans' (by norm_num)
    push_cast [Nat.cast_sub hp1]
    ring
  rw [h2, h1, Finset.prod_div_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun p _ => by ring

/-- Every odd place keeps at least one `h`-slot, whatever the gap. -/
theorem theGapSlotCountIsPositiveAtAnOddPrime {p : ℕ} (h : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    0 < gapSlots h p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 3 with hlt | hge
    · interval_cases p <;> simp_all
    · exact hge
  by_cases hd : p ∣ h
  · rw [theGapSlotCountAtAPrimeDividingTheGap hp hd]; omega
  · rw [theGapSlotCountAtAPrimeMissingTheGap hp hd]; omega

/-- **NO FINITE SIEVE HORIZON REFUSES ANY BOUNDED GAP.**  The twin case `h = 2` is one row of
this: for every gap and every primorial horizon of odd primes the admissible population is
nonempty, because each place keeps `p − 2` slots off the gap and `p − 1` on it, and both are
positive past `p = 2`.  Admissibility is never the obstruction; actuality is. -/
theorem theBoundedGapSlotsSurviveEveryHorizon (h : ℕ) :
    ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime ∧ p ≠ 2) → 0 < gapCount h (∏ p ∈ S, p) := by
  classical
  intro S
  refine Finset.induction_on (motive := fun T => (∀ p ∈ T, p.Prime ∧ p ≠ 2) →
    0 < gapCount h (∏ p ∈ T, p)) S ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    rw [gapCount, dif_neg one_ne_zero]
    refine Finset.card_pos.2 ⟨0, ?_⟩
    simp only [gapSlots, mem_filter, mem_univ, true_and]
    exact ⟨isUnit_of_subsingleton _, isUnit_of_subsingleton _⟩
  · intro q T hqT ih hS
    have hq := hS q (mem_insert_self q T)
    have hT : ∀ p ∈ T, p.Prime ∧ p ≠ 2 := fun p hp => hS p (mem_insert_of_mem hp)
    have hprodne : (∏ p ∈ T, p) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun p hp => (hT p hp).1.ne_zero
    have hcop : q.Coprime (∏ p ∈ T, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hq.1 (hT p hp).1).2 (by rintro rfl; exact hqT hp)
    haveI : NeZero q := ⟨hq.1.ne_zero⟩
    rw [Finset.prod_insert hqT, theGapCountIsMultiplicative h hq.1.ne_zero hprodne hcop,
      gapCount_eq]
    exact Nat.mul_pos (theGapSlotCountIsPositiveAtAnOddPrime h hq.1 hq.2) (ih hT)

/-- **THE GENERAL CUT LAW OVER A PRIMORIAL.**  For any gap `h`, a place keeps `p − 1` slots when it
divides the gap and `p − 2` when it does not, so the primorial count is that product.  The twin
case is `h = 2`, where the first branch never fires past `p = 2`. -/
theorem theWheelDensityIsTheSingularSeriesForAnyGap (h : ℕ) :
    ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime ∧ p ≠ 2) →
      gapCount h (∏ p ∈ S, p) = ∏ p ∈ S, (if p ∣ h then p - 1 else p - 2) := by
  classical
  intro S
  refine Finset.induction_on (motive := fun T => (∀ p ∈ T, p.Prime ∧ p ≠ 2) →
    gapCount h (∏ p ∈ T, p) = ∏ p ∈ T, (if p ∣ h then p - 1 else p - 2)) S ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    rw [gapCount, dif_neg one_ne_zero]
    have : (univ.filter (fun r : ZMod 1 => IsUnit r ∧ IsUnit (r + (h : ZMod 1)))) = univ := by
      ext r
      simp only [mem_filter, mem_univ, true_and, iff_true]
      exact ⟨isUnit_of_subsingleton _, isUnit_of_subsingleton _⟩
    rw [gapSlots, this]
    rfl
  · intro q T hqT ih hS
    have hq := hS q (mem_insert_self q T)
    have hT : ∀ p ∈ T, p.Prime ∧ p ≠ 2 := fun p hp => hS p (mem_insert_of_mem hp)
    have hprodne : (∏ p ∈ T, p) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun p hp => (hT p hp).1.ne_zero
    have hcop : q.Coprime (∏ p ∈ T, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hq.1 (hT p hp).1).2 (by rintro rfl; exact hqT hp)
    haveI : NeZero q := ⟨hq.1.ne_zero⟩
    rw [Finset.prod_insert hqT, Finset.prod_insert hqT,
      theGapCountIsMultiplicative h hq.1.ne_zero hprodne hcop, ih hT, gapCount_eq]
    congr 1
    by_cases hd : q ∣ h
    · rw [if_pos hd, theGapSlotCountAtAPrimeDividingTheGap hq.1 hd]
    · rw [if_neg hd, theGapSlotCountAtAPrimeMissingTheGap hq.1 hd]

/-! ## 7.  Admissible tuples: the same law with more letters -/

/-- The slots of an admissible pattern `H = (h₁, …, h_r)` at horizon `M`: residues at which every
`r + hᵢ` survives every cut.  `H = [0, 2]` is the twin case. -/
def tupleSlots (H : List ℕ) (M : ℕ) [NeZero M] : ℕ :=
  (univ.filter (fun r : ZMod M => ∀ h ∈ H, IsUnit (r + (h : ZMod M)))).card

/-- The residues the pattern blocks at a place: one per shift, with collisions merged. -/
def blocked (H : List ℕ) (p : ℕ) : Finset (ZMod p) :=
  (H.map (fun h => -((h : ℕ) : ZMod p))).toFinset

/-- **THE CUT AT ONE PLACE REMOVES EXACTLY THE BLOCKED RESIDUES.**  A place loses one position per
*distinct* residue among the shifts — which is why a pattern with a repeated residue costs less,
and why admissibility is the condition that the shifts never cover the whole place. -/
theorem theTupleSlotCountAtAPrime {p : ℕ} (hp : p.Prime) (H : List ℕ) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    tupleSlots H p = p - (blocked H p).card := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  classical
  have hfil : (univ.filter (fun r : ZMod p => ∀ h ∈ H, IsUnit (r + (h : ZMod p))))
      = univ \ blocked H p := by
    ext r
    constructor
    · intro hr
      simp only [mem_filter, mem_univ, true_and] at hr
      simp only [mem_sdiff, mem_univ, true_and, blocked, List.mem_toFinset, List.mem_map,
        not_exists, not_and]
      rintro h hh hrh
      have hu := hr h hh
      rw [← hrh, neg_add_cancel] at hu
      exact not_isUnit_zero hu
    · intro hr
      simp only [mem_sdiff, mem_univ, true_and, blocked, List.mem_toFinset, List.mem_map,
        not_exists, not_and] at hr
      simp only [mem_filter, mem_univ, true_and]
      intro h hh
      refine isUnit_iff_ne_zero.2 ?_
      intro hz
      exact hr h hh (by linear_combination -hz)
  rw [tupleSlots, hfil, Finset.card_univ_diff, ZMod.card]

/-- **A PLACE KEEPS A SLOT EXACTLY WHEN THE PATTERN DOES NOT COVER IT.**  That is the
Hardy–Littlewood admissibility condition, stated as a property of the wheel rather than of a
heuristic. -/
theorem theTupleSlotCountIsPositiveIffAdmissible {p : ℕ} (hp : p.Prime) (H : List ℕ) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    (0 < tupleSlots H p ↔ (blocked H p).card < p) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [theTupleSlotCountAtAPrime hp H]
  have hle : (blocked H p).card ≤ p := by
    have h1 := Finset.card_le_univ (blocked H p)
    rwa [ZMod.card] at h1
  omega

/-- Multiplicativity, for a whole pattern: the same Chinese remainder argument. -/
theorem theTupleSlotsAreMultiplicative {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (H : List ℕ) (hc : m.Coprime n) :
    tupleSlots H (m * n) = tupleSlots H m * tupleSlots H n := by
  classical
  set e := ZMod.chineseRemainder hc with he
  have hcast : ∀ (r : ZMod (m * n)) (h : ℕ),
      e (r + (h : ZMod (m * n))) = (((e r).1 + (h : ZMod m)), ((e r).2 + (h : ZMod n))) := by
    intro r h
    rw [map_add, map_natCast]
    rfl
  have key : ∀ r : ZMod (m * n),
      (∀ h ∈ H, IsUnit (r + (h : ZMod (m * n)))) ↔
        ((∀ h ∈ H, IsUnit ((e r).1 + (h : ZMod m))) ∧
         (∀ h ∈ H, IsUnit ((e r).2 + (h : ZMod n)))) := by
    intro r
    constructor
    · intro hall
      constructor <;> intro h hh <;>
        · have := hall h hh
          rw [← theEquivalenceMovesUnits e.toMulEquiv (r + (h : ZMod (m * n))),
            show (e.toMulEquiv (r + (h : ZMod (m * n)))) = e (r + (h : ZMod (m * n))) from rfl,
            hcast r h, Prod.isUnit_iff] at this
          first
            | exact this.1
            | exact this.2
    · rintro ⟨h1, h2⟩ h hh
      rw [← theEquivalenceMovesUnits e.toMulEquiv (r + (h : ZMod (m * n))),
        show (e.toMulEquiv (r + (h : ZMod (m * n)))) = e (r + (h : ZMod (m * n))) from rfl,
        hcast r h, Prod.isUnit_iff]
      exact ⟨h1 h hh, h2 h hh⟩
  have hcard :
      (univ.filter (fun r : ZMod (m * n) => ∀ h ∈ H, IsUnit (r + (h : ZMod (m * n))))).card =
      (univ.filter (fun z : ZMod m × ZMod n =>
          (∀ h ∈ H, IsUnit (z.1 + (h : ZMod m))) ∧
          (∀ h ∈ H, IsUnit (z.2 + (h : ZMod n))))).card := by
    refine Finset.card_equiv e.toEquiv ?_
    intro r; simp only [mem_filter, mem_univ, true_and]
    exact key r
  rw [tupleSlots, hcard, tupleSlots, tupleSlots, ← Finset.card_product]
  congr 1
  ext z
  simp only [mem_filter, mem_univ, true_and, Finset.mem_product]

/-- A total form, so the product statement needs no instance threading. -/
noncomputable def tupleCount (H : List ℕ) (M : ℕ) : ℕ :=
  if hM : M = 0 then 0 else @tupleSlots H M ⟨hM⟩

@[simp] theorem tupleCount_eq (H : List ℕ) (M : ℕ) [NeZero M] :
    tupleCount H M = tupleSlots H M := by rw [tupleCount, dif_neg (NeZero.ne M)]

theorem theTupleCountIsMultiplicative {m n : ℕ} (H : List ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hc : m.Coprime n) : tupleCount H (m * n) = tupleCount H m * tupleCount H n := by
  haveI : NeZero m := ⟨hm⟩
  haveI : NeZero n := ⟨hn⟩
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero hm hn⟩
  simp only [tupleCount_eq]
  exact theTupleSlotsAreMultiplicative H hc

/-- **AN ADMISSIBLE TUPLE SURVIVES EVERY HORIZON.**  If at every place of the horizon the pattern
fails to cover the place, the wheel keeps a slot for it there — and the product over the primorial
is positive.  The twin case `H = [0, 2]` is one row; nothing about `r = 1` was special. -/
theorem theAdmissibleTupleSlotsSurviveEveryHorizon (H : List ℕ) :
    ∀ (S : Finset ℕ), (∀ p ∈ S, ∃ hp : p.Prime, (blocked H p).card < p) →
      0 < tupleCount H (∏ p ∈ S, p) := by
  classical
  intro S
  refine Finset.induction_on (motive := fun T => (∀ p ∈ T, ∃ hp : p.Prime,
      (blocked H p).card < p) → 0 < tupleCount H (∏ p ∈ T, p)) S ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    rw [tupleCount, dif_neg one_ne_zero]
    refine Finset.card_pos.2 ⟨0, ?_⟩
    simp only [tupleSlots, mem_filter, mem_univ, true_and]
    exact fun h _ => isUnit_of_subsingleton _
  · intro q T hqT ih hS
    obtain ⟨hq, hqadm⟩ := hS q (mem_insert_self q T)
    have hT : ∀ p ∈ T, ∃ _ : p.Prime, (blocked H p).card < p := fun p hp =>
      hS p (mem_insert_of_mem hp)
    have hprodne : (∏ p ∈ T, p) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun p hp => (hT p hp).choose.ne_zero
    have hcop : q.Coprime (∏ p ∈ T, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hq (hT p hp).choose).2 (by rintro rfl; exact hqT hp)
    haveI : NeZero q := ⟨hq.ne_zero⟩
    rw [Finset.prod_insert hqT, theTupleCountIsMultiplicative H hq.ne_zero hprodne hcop,
      tupleCount_eq]
    exact Nat.mul_pos ((theTupleSlotCountIsPositiveIffAdmissible hq H).2 hqadm) (ih hT)

/-! ## 8.  The conjecture, stated and not touched -/

/-- The twin prime conjecture, with real quantifiers.  Nothing above discharges it. -/
def TwinPrimeConjecture : Prop := ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ (p + 2).Prime

/-- **THE BOUNDARY, STATED AS A `Prop`.**  Unbounded admissibility in the wheel does not imply the
conjecture; this implication is the exact gap between the collapsed population and its separator,
and it is discharged nowhere in this file. -/
def TheWheelDoesNotDecideTheConjecture : Prop :=
  (∀ N : ℕ, ∃ M : ℕ, ∃ _ : NeZero M, N < twinSlots M) → TwinPrimeConjecture

end Soma.Holonics.Millennium.TwinWheel
