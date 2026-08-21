import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Tactic

/-!
# The place ledger: the height is a product of local factors, and the fiber it collapses is counted

The arithmetic-intersection ledger of `P¹` over `ℤ`, written out where every term is a rational
number and nothing is a limit.

A rational `x` is a point of `P¹(ℚ)`, hence a section of `P¹_ℤ → Spec ℤ`.  Its **height** is the
intersection of that section with a hyperplane, and Arakelov's compactification says that number is
a sum of local contributions: one per finite fibre `X_p`, and one at the adjoined fibre at infinity.
Over `ℚ` the whole ledger is rational and can be exhibited term by term:

```text
archFactor x  =  max 1 |x|                    the fibre at infinity
finiteFactor x =  x.den  =  ∏_p p^{v_p(den)}   the finite fibres, one per prime
archFactor x · finiteFactor x  =  max |x.num| x.den  =  the height
```

That identity is `theLedgerMultipliesToTheHeight`, and it is exact in `ℚ`.  Its companion is the
**product formula**, stated here as a product of rational factors equal to `1` — never through a
logarithm, and with no real number anywhere in the file:

```text
|x| · ∏_{p ∈ places x} p^{−v_p(x)}  =  1
```

The valuation is not imported; it is *defined* from `Nat.factorization` as
`ledger x p = v_p(num) − v_p(den)`, and `theLedgerIsThePAdicValuation` proves that definition
agrees with mathlib's `padicValRat` at every prime.  So the ledger is the object, and the `p`-adic
valuation is a name for one of its coordinates.

**What the ledger is for.**  The height is a compression of `x`: it is a single natural number, and
its fibres are infinite.  Three readings below make the collapse and its remainder exact rather
than gestural.

* **The collapse is an involution.**  `theHeightIsInvariantUnderInversion` — `height x⁻¹ = height
  x` for every `x` — while `theInversionNegatesTheLedger` gives `ledger x⁻¹ p = −ledger x p`.
  So inversion moves all the mass from the archimedean fibre to the finite ones and back, and the
  height cannot see it.  `12` and `1/12` are the exhibited witness: same height `12`, archimedean
  factor `12` against `1`, finite factor `1` against `12`.
* **The finite half loses nothing.**  `theFiniteLedgerDeterminesTheRationalUpToSign`: two nonzero
  rationals with the same ledger differ at most by sign, and `theEqualLedgersForceEqualHeights` is
  the direction that makes the ledger a refinement of the height rather than an unrelated
  invariant.  Stripped of vocabulary the first is unique factorization — `ℚ⁺` is free abelian on
  the primes — and it is stated here for its *placement* rather than its difficulty: it says the
  archimedean coordinate is the unique lossy one, because every finite coordinate is recoverable
  and the sign is exactly what the ledger drops.
* **The retained fiber is counted.**  For `H ≥ 2` the set of rationals of height `H` is carried by
  the finite set `heightPairs H` of coprime pairs (`theHeightPairCarriesItsHeight`,
  `theRationalLandsInItsOwnHeightPairs`, `theHeightPairMapIsInjective` — together: the map
  `(a,b) ↦ a/b` is a bijection from `heightPairs H` onto the height-`H` fiber).  Its cardinality is
  `4·φ(H)` for every `H ≥ 2` — `theHeightFiberIsFourTimesTheTotient`, proved by exhibiting the
  four-branch bijection `k ↦ (k,H), (−k,H), (H,k), (−H,k)` — with eleven independent kernel
  evaluations at `H = 2 … 12` standing as the control on the definition.  So the fiber the
  compression retains is not merely infinite in aggregate: at each level it is an exactly counted
  finite set, and `4·φ(H)` is not a quantity this file declares.  `H = 1` is the exception and is
  not smoothed: that fiber is `{0, 1, −1}`, of size `3`, and
  `theUnitHeightFiberIsZeroAndTheTwoRootsOfUnity` proves the identification (Kronecker's theorem
  over `ℚ`, in the one case where it is elementary).

The last section is a **calibration control and is graded as one**, not as a discovery.  For every
`n > 0`,

```text
∏_{d | n, d > 1} Φ_d(1)  =  n
```

which is `∏_{ζⁿ = 1, ζ ≠ 1} (1 − ζ) = n` — the archimedean Green product over the `n`-torsion of
`𝔾_m`, in the one chart where its value is an integer.  It holds for *every* `n` with no arithmetic
input whatever, so under the tautology rule it carries no evidence about any particular arithmetic
object; its only honest use is that an organ computing archimedean local heights must return `n` on
the torsion orbit or it is wrong.  `theTorsionProductHasTheFiniteLedgerOfItsOrder` then reads its
prime factorization off the divisor lattice, joining it to the finite ledger above.

**Imported and not proved here**, cited so the statements are read at their true height:
Arakelov's compactification of an arithmetic surface by fibres at infinity (Arakelov 1974);
the arithmetic Riemann–Roch theorem, the arithmetic Hodge index theorem for arithmetic surfaces,
and the `δ` invariant (Faltings 1984); that the Arakelov pairing is a Néron pairing, so
`(D.D) = −ĥ([D])` (Hriljac 1985); the local decomposition of the canonical height into local
symbols, which is the ledger itself (Néron 1965); arithmetic Chow groups in arbitrary dimension
(Gillet–Soulé 1990) and their open positivity conjectures (Gillet–Soulé 1994), proved in
codimension one (Moriwaki 1996) and extended to adelic line bundles (Yuan–Zhang 2017); and
Ostrowski's theorem, that every nontrivial absolute value on `ℚ` is equivalent to the real one or
to a `p`-adic one, which is why `places x` together with the archimedean factor is the *complete*
place family and not a chosen subfamily.  Mathlib carries Ostrowski at
`Mathlib/NumberTheory/Ostrowski.lean` (`equiv_real_or_padic`); it is stated over `ℝ`, nothing below
invokes it, and no statement in this file mentions a real number.

**Boundary — what this file does not claim.**  It does not claim any Arakelov object, arithmetic
surface, Néron–Tate height, Green function or arithmetic intersection number; none is defined here
and none is defined in mathlib.  It does not claim the elliptic identity
`∏_{P ∈ E[n], P ≠ 0} G(0,P) = n` (de Jong, *On the Arakelov theory of elliptic curves*, Thm 4.2),
which needs real analysis and is not formalized; what is proved below is the `𝔾_m` cyclotomic
shadow of that identity over `ℤ`, which is a different and much weaker statement.  It does not
connect `archFactor · finiteFactor` to mathlib's `Height.mulHeight₁`, which is `ℝ`-valued and is
nowhere computed for a rational — measured 2026-08-21, `grep -rn "mulHeight₁" Mathlib | grep -c "ℚ"`
→ `0`.  That bridge is a real, absent, upstreamable mathlib theorem and is not attempted here.  It does not claim that Arakelov theory
is the shared organ of the Riemann, Hodge and BSD route charts — the survey that produced this deed
found *against* that reading, since the arithmetic Hodge index theorem is a theorem and proves none
of the three, and the coupling at the word "archimedean" is a name match rather than a computation.
And it does not touch any Millennium statement: no variety, cycle, curve or `L`-function appears.

**Measured 2026-08-21**, each command with its exact scope, and each measuring those names over
that scope only:
`grep -rlin "arakelov" soma/formal/ crates/ papers/ blueprint/ canon/`, excluding this file → 0
files;
`grep -rn "canonicalHeight\|NeronTate\|neronTate" <mathlib>/Mathlib/` → 0 hits;
`grep -rin "arakelov" <mathlib>/Mathlib/` → 0 hits;
`grep -rn "greenFunction\|GreenFunction" <mathlib>/Mathlib/` → 0 hits;
`grep -rin "arithmetic intersection\|arithmeticChow" <mathlib>/Mathlib/` → 0 hits;
`grep -c "ℚ\|padic" <mathlib>/Mathlib/NumberTheory/NumberField/FinitePlaces.lean` → 0, i.e.
mathlib nowhere identifies `FinitePlace ℚ` with the primes, which is why the place family below is
declared rather than imported.  Each command measures those names over that scope only and is not a
claim that no related content exists under another name.

The `4·φ(H)` counts and the cyclotomic products were **re-verified by exact enumeration before
being written down** (integer arithmetic, no floats): the coprime-pair count matches `4·φ(H)` for
every `H` in `2 … 200` with zero mismatches and `H = 1` returns `3`; and
`∏_{d | n, d > 1} Φ_d(1) = n` was recomputed from the recursive integer definition of the
cyclotomic polynomials for every `n` in `1 … 80` with zero mismatches.  Neither enumeration is
load-bearing for a proof below; both are the check that the statements written down are the
statements measured.

Twelve height-fiber cardinalities are discharged by kernel evaluation (`decide`); everything else
is proved by ordinary rewriting, a finite case split and one exhibited bijection.  Every `theorem`
here is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.PlaceLedger

open Finset

/-! ## 1. The two factors of one rational

The archimedean factor and the finite factor, and the height as their product.  Nothing here is a
limit: `archFactor` is a `max` of two rationals and `finiteFactor` is a denominator. -/

/-- The factor at the fibre at infinity: `max 1 |x|`. -/
def archFactor (x : ℚ) : ℚ := max 1 |x|

/-- The factor carried by all the finite fibres together: the denominator. -/
def finiteFactor (x : ℚ) : ℚ := (x.den : ℚ)

/-- The height of `x` read as a point of `P¹(ℚ)`: `max |num| den`, in lowest terms. -/
def height (x : ℚ) : ℕ := max x.num.natAbs x.den

theorem theArchimedeanFactorIsNeverBelowOne (x : ℚ) : 1 ≤ archFactor x := le_max_left _ _

theorem theFiniteFactorIsPositive (x : ℚ) : 0 < finiteFactor x := by
  simpa [finiteFactor] using (Nat.cast_pos (α := ℚ)).mpr x.pos

/-- Clearing the denominator turns the archimedean absolute value into the numerator. -/
theorem theAbsoluteValueTimesTheDenominatorIsTheNumerator (x : ℚ) :
    |x| * (x.den : ℚ) = (x.num.natAbs : ℚ) := by
  have hd : (0 : ℚ) ≤ (x.den : ℚ) := by positivity
  calc |x| * (x.den : ℚ) = |x * (x.den : ℚ)| := by rw [abs_mul, abs_of_nonneg hd]
    _ = |((x.num : ℚ))| := by rw [Rat.mul_den_eq_num]
    _ = (x.num.natAbs : ℚ) := by rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp

/-- **The ledger multiplies to the height.**  The archimedean factor times the finite factor is
`max |num| den` — the height of `x` as a point of `P¹` over `ℤ`, with every term rational. -/
theorem theLedgerMultipliesToTheHeight (x : ℚ) :
    archFactor x * finiteFactor x = (height x : ℚ) := by
  have hd : (0 : ℚ) ≤ (x.den : ℚ) := by positivity
  rw [archFactor, finiteFactor, max_mul_of_nonneg _ _ hd, one_mul,
    theAbsoluteValueTimesTheDenominatorIsTheNumerator, height]
  push_cast
  exact max_comm _ _

/-! ## 2. The finite factor is a product over the finite places -/

/-- A positive natural is the product of its prime powers, cast into `ℚ`. -/
theorem theNaturalIsTheProductOverItsFinitePlaces {n : ℕ} (hn : n ≠ 0) :
    (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
  have h := Nat.factorization_prod_pow_eq_self hn
  rw [Finsupp.prod, Nat.support_factorization] at h
  exact_mod_cast h.symm

/-- **The finite factor is the product over the finite fibres**, one factor per prime dividing the
denominator. -/
theorem theFiniteFactorIsTheProductOverTheFinitePlaces (x : ℚ) :
    finiteFactor x = ∏ p ∈ x.den.primeFactors, (p : ℚ) ^ x.den.factorization p :=
  theNaturalIsTheProductOverItsFinitePlaces x.den_nz

/-! ## 3. The ledger and the product formula -/

/-- The finite ledger of `x`: the exponent of `p` in the numerator minus its exponent in the
denominator.  Defined from `Nat.factorization`, not imported. -/
def ledger (x : ℚ) (p : ℕ) : ℤ :=
  (x.num.natAbs.factorization p : ℤ) - (x.den.factorization p : ℤ)

/-- The finite places at which `x` is not a unit. -/
def places (x : ℚ) : Finset ℕ := (x.num.natAbs * x.den).primeFactors

/-- The local factor of `x` at the finite place `p`, as a rational: `p^{−v_p(x)}`. -/
def localFactor (p : ℕ) (x : ℚ) : ℚ := (p : ℚ) ^ (-(ledger x p))

/-- **The declared ledger is the `p`-adic valuation.**  So `ledger` is the object and `padicValRat`
is a name for one of its coordinates; neither is an extra hypothesis on the other. -/
theorem theLedgerIsThePAdicValuation {p : ℕ} (hp : p.Prime) (x : ℚ) :
    ledger x p = padicValRat p x := by
  simp [ledger, padicValRat, padicValInt, Nat.factorization_def _ hp]

/-- A prime that is not a prime factor contributes nothing to the factorization. -/
theorem theFactorizationVanishesOffThePrimeFactors {n p : ℕ} (hp : p ∉ n.primeFactors) :
    n.factorization p = 0 :=
  Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])

theorem theLedgerVanishesOffThePlaces {x : ℚ} (hx : x ≠ 0) {p : ℕ} (hp : p ∉ places x) :
    ledger x p = 0 := by
  have hn : x.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hx)
  rw [places, Nat.primeFactors_mul hn x.den_nz, Finset.mem_union] at hp
  push_neg at hp
  obtain ⟨h1, h2⟩ := hp
  rw [ledger, theFactorizationVanishesOffThePrimeFactors h1,
    theFactorizationVanishesOffThePrimeFactors h2]
  simp

/-- **The product formula, exactly, as a product of rationals equal to one.**  No logarithm and no
real number: the archimedean factor times every local factor is `1`. -/
theorem theProductOverEveryPlaceIsOne {x : ℚ} (hx : x ≠ 0) :
    |x| * ∏ p ∈ places x, localFactor p x = 1 := by
  have hn : x.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hx)
  have hdisj : Disjoint x.num.natAbs.primeFactors x.den.primeFactors :=
    Nat.Coprime.disjoint_primeFactors x.reduced
  have hplaces : places x = x.num.natAbs.primeFactors ∪ x.den.primeFactors := by
    rw [places, Nat.primeFactors_mul hn x.den_nz]
  have hnumside : ∏ p ∈ x.num.natAbs.primeFactors, localFactor p x = ((x.num.natAbs : ℚ))⁻¹ := by
    rw [theNaturalIsTheProductOverItsFinitePlaces hn, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpd : x.den.factorization p = 0 :=
      theFactorizationVanishesOffThePrimeFactors (Finset.disjoint_left.mp hdisj hp)
    rw [localFactor, ledger, hpd]
    push_cast
    rw [sub_zero, zpow_neg, zpow_natCast]
  have hdenside : ∏ p ∈ x.den.primeFactors, localFactor p x = (x.den : ℚ) := by
    rw [theNaturalIsTheProductOverItsFinitePlaces x.den_nz]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpn : x.num.natAbs.factorization p = 0 :=
      theFactorizationVanishesOffThePrimeFactors (Finset.disjoint_right.mp hdisj hp)
    rw [localFactor, ledger, hpn]
    push_cast
    rw [zero_sub, neg_neg, zpow_natCast]
  have hnq : ((x.num.natAbs : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [hplaces, Finset.prod_union hdisj, hnumside, hdenside, ← mul_assoc,
    mul_comm (|x|) (((x.num.natAbs : ℚ))⁻¹), mul_assoc,
    theAbsoluteValueTimesTheDenominatorIsTheNumerator, inv_mul_cancel₀ hnq]

/-! ## 4. The finite half of the ledger loses nothing -/

/-- At every prime at most one of the numerator and the denominator contributes, so the ledger's
positive and negative parts are the two factorizations. -/
theorem theLedgerSplitsIntoItsTwoParts (x : ℚ) (p : ℕ) :
    (x.num.natAbs.factorization p : ℤ) = max (ledger x p) 0 ∧
      (x.den.factorization p : ℤ) = max (-(ledger x p)) 0 := by
  have key : x.num.natAbs.factorization p = 0 ∨ x.den.factorization p = 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    have hd1 : p ∣ x.num.natAbs := Nat.dvd_of_factorization_pos h1
    have hd2 : p ∣ x.den := Nat.dvd_of_factorization_pos h2
    have hp1 : p ∣ 1 := x.reduced ▸ Nat.dvd_gcd hd1 hd2
    have hp : p.Prime := Nat.prime_of_mem_primeFactors
      (Nat.support_factorization (n := x.num.natAbs) ▸ Finsupp.mem_support_iff.mpr h1)
    exact hp.one_lt.ne' (Nat.dvd_one.mp hp1)
  rw [ledger]
  omega

/-- **The finite ledger determines the rational up to sign.**  Two nonzero rationals with the same
ledger differ at most by the sign the ledger drops.  Stripped of vocabulary this is unique
factorization; its content is where it sits — the archimedean coordinate is the only lossy one. -/
theorem theFiniteLedgerDeterminesTheRationalUpToSign {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ledger x = ledger y) : x = y ∨ x = -y := by
  have hxn : x.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hx)
  have hyn : y.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hy)
  have hpt : ∀ p : ℕ, ledger x p = ledger y p := fun p => by rw [h]
  have hnumfac : x.num.natAbs.factorization = y.num.natAbs.factorization := by
    refine Finsupp.ext fun p => ?_
    have h1 := (theLedgerSplitsIntoItsTwoParts x p).1
    have h2 := (theLedgerSplitsIntoItsTwoParts y p).1
    have := hpt p
    omega
  have hdenfac : x.den.factorization = y.den.factorization := by
    refine Finsupp.ext fun p => ?_
    have h1 := (theLedgerSplitsIntoItsTwoParts x p).2
    have h2 := (theLedgerSplitsIntoItsTwoParts y p).2
    have := hpt p
    omega
  have hnum : x.num.natAbs = y.num.natAbs := Nat.factorization_inj hxn hyn hnumfac
  have hden : x.den = y.den := Nat.factorization_inj x.den_nz y.den_nz hdenfac
  rcases Int.natAbs_eq_natAbs_iff.mp hnum with hnn | hnn
  · exact Or.inl (Rat.ext hnn hden)
  · refine Or.inr (Rat.ext ?_ ?_) <;> simp [hnn, hden]

/-! ## 5. The collapse: inversion moves the mass and the height cannot see it -/

theorem theInverseNumeratorIsTheDenominator {x : ℚ} (hx : x ≠ 0) : x⁻¹.num.natAbs = x.den := by
  rw [Rat.num_inv, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero (Rat.num_ne_zero.mpr hx)]
  simp

/-- **The height is invariant under inversion.**  It is a `max` of the two coordinates that
inversion exchanges. -/
theorem theHeightIsInvariantUnderInversion (x : ℚ) : height x⁻¹ = height x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [height, height, theInverseNumeratorIsTheDenominator hx, Rat.den_inv_of_ne_zero hx]
    exact max_comm _ _

/-- **Inversion negates the ledger.**  So the whole mass moves from the archimedean fibre to the
finite ones, coordinate by coordinate, while the height above stays put. -/
theorem theInversionNegatesTheLedger {x : ℚ} (hx : x ≠ 0) (p : ℕ) :
    ledger x⁻¹ p = -ledger x p := by
  rw [ledger, ledger, theInverseNumeratorIsTheDenominator hx, Rat.den_inv_of_ne_zero hx]
  ring

theorem theHeightIsInvariantUnderNegation (x : ℚ) : height (-x) = height x := by
  simp [height]

/-- **The ledger refines the height, and never disagrees with it.**  Equal ledgers force equal
heights — the direction that makes the ledger a genuine refinement rather than an unrelated
invariant, and the one a wrong ledger would break. -/
theorem theEqualLedgersForceEqualHeights {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ledger x = ledger y) : height x = height y := by
  rcases theFiniteLedgerDeterminesTheRationalUpToSign hx hy h with rfl | rfl
  · rfl
  · exact theHeightIsInvariantUnderNegation y

/-- **The collapsed pair, exhibited.**  `12` and `1/12` have the same height and opposite ledgers:
`12` carries all its mass at the fibre at infinity, `1/12` all of it at `2` and `3`.  The
compressed reading cannot tell them apart; the ledger separates them at every coordinate. -/
theorem theTwelveAndItsInverseAreACollapsedPair :
    height (1 / 12 : ℚ) = height (12 : ℚ) ∧
      archFactor (1 / 12 : ℚ) ≠ archFactor (12 : ℚ) ∧
      finiteFactor (1 / 12 : ℚ) ≠ finiteFactor (12 : ℚ) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [height, archFactor, finiteFactor]

/-! ## 6. The height-one fiber -/

/-- **The multiplicative-height-one locus over `ℚ` is `{0} ∪ μ(ℚ)`.**  Kronecker's theorem in the
one case where it is elementary, and the exception to the count below: this fiber has three members,
not `4·φ(1)`. -/
theorem theUnitHeightFiberIsZeroAndTheTwoRootsOfUnity (x : ℚ) :
    height x = 1 ↔ x = 0 ∨ x = 1 ∨ x = -1 := by
  constructor
  · intro h
    rw [height] at h
    have hpos : 1 ≤ x.den := x.pos
    have hden : x.den = 1 := by omega
    have hnum : x.num.natAbs ≤ 1 := by omega
    have hx : (x.num : ℚ) = x := (Rat.den_eq_one_iff x).mp hden
    have : x.num = 0 ∨ x.num = 1 ∨ x.num = -1 := by omega
    rcases this with h0 | h1 | h2
    · exact Or.inl (by rw [← hx, h0]; norm_num)
    · exact Or.inr (Or.inl (by rw [← hx, h1]; norm_num))
    · exact Or.inr (Or.inr (by rw [← hx, h2]; norm_num))
  · rintro (rfl | rfl | rfl) <;> norm_num [height]

/-! ## 7. The retained fiber of the height compression, counted

For `H ≥ 2` the height-`H` fiber is carried by a finite set of coprime integer pairs.  The first
three theorems say the carrying is a bijection; the cardinalities are then kernel-evaluated at
eleven heights and proved in general. -/

/-- The coprime integer pairs of height `H`. -/
def heightPairs (H : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(H : ℤ)) (H : ℤ)) ×ˢ (Finset.Icc (1 : ℤ) (H : ℤ))).filter
    (fun ab => Int.gcd ab.1 ab.2 = 1 ∧ max ab.1.natAbs ab.2.natAbs = H)

/-- The pair `(a, b)` read as the rational `a / b`. -/
def toRat (ab : ℤ × ℤ) : ℚ := (ab.1 : ℚ) / (ab.2 : ℚ)

theorem theHeightPairIsAlreadyInLowestTerms {H : ℕ} {ab : ℤ × ℤ} (hab : ab ∈ heightPairs H) :
    (toRat ab).num = ab.1 ∧ ((toRat ab).den : ℤ) = ab.2 := by
  rw [heightPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hab
  obtain ⟨⟨_, hb⟩, hg, _⟩ := hab
  have hb0 : (0 : ℤ) < ab.2 := lt_of_lt_of_le zero_lt_one hb.1
  exact ⟨Rat.num_div_eq_of_coprime hb0 hg, Rat.den_div_eq_of_coprime hb0 hg⟩

/-- **A pair of height `H` names a rational of height `H`.** -/
theorem theHeightPairCarriesItsHeight {H : ℕ} {ab : ℤ × ℤ} (hab : ab ∈ heightPairs H) :
    height (toRat ab) = H := by
  obtain ⟨hn, hd⟩ := theHeightPairIsAlreadyInLowestTerms hab
  rw [heightPairs, Finset.mem_filter] at hab
  obtain ⟨_, _, hmax⟩ := hab
  rw [height, hn, ← hmax]
  congr 1
  omega

/-- **Every rational lands in the pair set of its own height**, so the carrying is onto. -/
theorem theRationalLandsInItsOwnHeightPairs (x : ℚ) :
    (x.num, (x.den : ℤ)) ∈ heightPairs (height x) := by
  have hd : (1 : ℤ) ≤ (x.den : ℤ) := by exact_mod_cast x.pos
  rw [heightPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  refine ⟨⟨⟨?_, ?_⟩, hd, ?_⟩, x.reduced, rfl⟩
  · have : x.num.natAbs ≤ height x := le_max_left _ _
    omega
  · have : x.num.natAbs ≤ height x := le_max_left _ _
    omega
  · show ((x.den : ℤ)) ≤ ((height x : ℕ) : ℤ)
    have : x.den ≤ height x := le_max_right _ _
    exact_mod_cast this

/-- **The carrying is injective**, so `heightPairs H` is exactly the height-`H` fiber and its
cardinality below is the fiber's. -/
theorem theHeightPairMapIsInjective (H : ℕ) : Set.InjOn toRat (heightPairs H) := by
  intro a ha b hb hab
  obtain ⟨ha1, ha2⟩ := theHeightPairIsAlreadyInLowestTerms ha
  obtain ⟨hb1, hb2⟩ := theHeightPairIsAlreadyInLowestTerms hb
  have h1 : a.1 = b.1 := by rw [← ha1, ← hb1, hab]
  have h2 : a.2 = b.2 := by rw [← ha2, ← hb2, hab]
  exact Prod.ext h1 h2

/-- **The height fiber is four times the totient**, kernel-evaluated at `H = 2 … 12`.  The count is
not a quantity this file declares: it is read off an exhaustive enumeration of coprime pairs and
compared against `Nat.totient`, which is defined independently. -/
theorem theSmallHeightFibersAreFourTimesTheTotient :
    (heightPairs 2).card = 4 * Nat.totient 2 ∧
      (heightPairs 3).card = 4 * Nat.totient 3 ∧
      (heightPairs 4).card = 4 * Nat.totient 4 ∧
      (heightPairs 5).card = 4 * Nat.totient 5 ∧
      (heightPairs 6).card = 4 * Nat.totient 6 ∧
      (heightPairs 7).card = 4 * Nat.totient 7 ∧
      (heightPairs 8).card = 4 * Nat.totient 8 ∧
      (heightPairs 9).card = 4 * Nat.totient 9 ∧
      (heightPairs 10).card = 4 * Nat.totient 10 ∧
      (heightPairs 11).card = 4 * Nat.totient 11 ∧
      (heightPairs 12).card = 4 * Nat.totient 12 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The count fails at `H = 1`, and the failure is stated rather than smoothed.**  The unit fiber
has three members, `4·φ(1) = 4`. -/
theorem theUnitFiberIsThreeAndNotFourTimesTheTotient :
    (heightPairs 1).card = 3 ∧ (heightPairs 1).card ≠ 4 * Nat.totient 1 := by
  constructor <;> decide

/-- Membership in `heightPairs H` for `H ≥ 2`, split by which coordinate attains the height.  The
two branches are exclusive: coprimality forbids both coordinates reaching `H` at once. -/
theorem theHeightPairSplitsByWhichCoordinateAttainsTheHeight {H : ℕ} (hH : 2 ≤ H) (a b : ℤ) :
    (a, b) ∈ heightPairs H ↔
      ((b = (H : ℤ) ∧ a.natAbs < H ∧ Nat.gcd H a.natAbs = 1) ∨
       (a.natAbs = H ∧ 1 ≤ b ∧ b.natAbs < H ∧ Nat.gcd H b.natAbs = 1)) := by
  rw [heightPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  simp only [Int.gcd]
  constructor
  · rintro ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, hg, hm⟩
    rcases max_cases a.natAbs b.natAbs with ⟨he, _⟩ | ⟨he, _⟩
    · right
      refine ⟨by omega, hb1, ?_, ?_⟩
      · by_contra hc
        have hbH : b.natAbs = H := by omega
        have : Nat.gcd a.natAbs b.natAbs = H := by
          rw [hbH, show a.natAbs = H by omega, Nat.gcd_self]
        omega
      · rw [show H = a.natAbs by omega]; exact hg
    · left
      refine ⟨by omega, ?_, ?_⟩
      · by_contra hc
        have haH : a.natAbs = H := by omega
        have : Nat.gcd a.natAbs b.natAbs = H := by
          rw [haH, show b.natAbs = H by omega, Nat.gcd_self]
        omega
      · rw [show H = b.natAbs by omega, Nat.gcd_comm]; exact hg
  · rintro (⟨hb, ha, hg⟩ | ⟨ha, hb1, hb, hg⟩)
    · subst hb
      refine ⟨⟨⟨by omega, by omega⟩, by omega, le_refl _⟩, ?_, ?_⟩
      · rw [Nat.gcd_comm] at hg; simpa using hg
      · simp; omega
    · refine ⟨⟨⟨by omega, by omega⟩, hb1, by omega⟩, ?_, ?_⟩
      · rw [← ha] at hg; exact hg
      · omega

/-- **The height fiber is four times the totient, for every `H ≥ 2`.**  The bijection is exhibited:
the four branches send `k` coprime to `H` and below it to `(k, H)`, `(−k, H)`, `(H, k)`, `(−H, k)`,
and every pair of height `H` is one of those.  So the fiber the height compression retains is not
merely infinite in aggregate — at each level it is an exactly counted finite set, and `4·φ(H)` is
not a quantity this file declares.  The eleven kernel evaluations above are the independent control
on the definition; a single mismatch at any `H` would refute this theorem. -/
theorem theHeightFiberIsFourTimesTheTotient {H : ℕ} (hH : 2 ≤ H) :
    (heightPairs H).card = 4 * Nat.totient H := by
  classical
  have hH0 : H ≠ 0 := by omega
  have htot : Nat.totient H = ((range H).filter H.Coprime).card := rfl
  have hTcard : (((range H).filter H.Coprime) ×ˢ (range 4)).card = 4 * Nat.totient H := by
    rw [Finset.card_product, Finset.card_range, htot]; ring
  have hmemT : ∀ k : ℕ, k ∈ (range H).filter H.Coprime ↔ (k < H ∧ Nat.gcd H k = 1) := by
    intro k; simp [Nat.Coprime]
  rw [← hTcard]
  refine Finset.card_nbij'
    (fun ab => if ab.2 = (H : ℤ) then (ab.1.natAbs, if 0 ≤ ab.1 then 0 else 1)
               else (ab.2.natAbs, if 0 ≤ ab.1 then 2 else 3))
    (fun kt => if kt.2 = 0 then ((kt.1 : ℤ), (H : ℤ))
               else if kt.2 = 1 then (-(kt.1 : ℤ), (H : ℤ))
               else if kt.2 = 2 then ((H : ℤ), (kt.1 : ℤ))
               else (-(H : ℤ), (kt.1 : ℤ))) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_coe] at hab ⊢
    rcases (theHeightPairSplitsByWhichCoordinateAttainsTheHeight hH a b).mp hab with
      ⟨hb, ha, hg⟩ | ⟨ha, hb1, hb, hg⟩
    · simp only [hb, Finset.mem_product, hmemT, Finset.mem_range, if_pos]
      exact ⟨⟨ha, hg⟩, by split_ifs <;> omega⟩
    · have hbne : b ≠ (H : ℤ) := by omega
      simp only [if_neg hbne, Finset.mem_product, hmemT, Finset.mem_range]
      exact ⟨⟨hb, hg⟩, by split_ifs <;> omega⟩
  · rintro ⟨k, t⟩ hkt
    simp only [Finset.mem_coe, Finset.mem_product, hmemT, Finset.mem_range] at hkt ⊢
    obtain ⟨⟨hk, hg⟩, ht⟩ := hkt
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hg; omega
      · omega
    have hk1' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk1
    interval_cases t
    · show ((k : ℤ), (H : ℤ)) ∈ heightPairs H
      rw [theHeightPairSplitsByWhichCoordinateAttainsTheHeight hH]
      exact Or.inl ⟨rfl, by simpa using hk, by simpa using hg⟩
    · show (-(k : ℤ), (H : ℤ)) ∈ heightPairs H
      rw [theHeightPairSplitsByWhichCoordinateAttainsTheHeight hH]
      exact Or.inl ⟨rfl, by simpa using hk, by simpa using hg⟩
    · show ((H : ℤ), (k : ℤ)) ∈ heightPairs H
      rw [theHeightPairSplitsByWhichCoordinateAttainsTheHeight hH]
      exact Or.inr ⟨by simp, hk1', by simpa using hk, by simpa using hg⟩
    · show (-(H : ℤ), (k : ℤ)) ∈ heightPairs H
      rw [theHeightPairSplitsByWhichCoordinateAttainsTheHeight hH]
      exact Or.inr ⟨by simp, hk1', by simpa using hk, by simpa using hg⟩
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_coe] at hab
    rcases (theHeightPairSplitsByWhichCoordinateAttainsTheHeight hH a b).mp hab with
      ⟨hb, ha, hg⟩ | ⟨ha, hb1, hb, hg⟩
    · subst hb
      by_cases hs : 0 ≤ a
      · have hv : ((a.natAbs : ℤ)) = a := Int.natAbs_of_nonneg hs
        simp [hs, hv]
      · have hv : ((a.natAbs : ℤ)) = -a := Int.ofNat_natAbs_of_nonpos (by omega)
        simp [hs, hv]
    · have hbne : b ≠ (H : ℤ) := by omega
      have hbb : ((b.natAbs : ℤ)) = b := Int.natAbs_of_nonneg (by omega)
      by_cases hs : 0 ≤ a
      · have hv : a = (H : ℤ) := by omega
        simp [hbne, hbb, hv]
      · have hv : a = -(H : ℤ) := by omega
        simp [hbne, hbb, hv, hH0]
  · rintro ⟨k, t⟩ hkt
    simp only [Finset.mem_coe, Finset.mem_product, hmemT, Finset.mem_range] at hkt
    obtain ⟨⟨hk, hg⟩, ht⟩ := hkt
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hg; omega
      · omega
    have hk0 : k ≠ 0 := by omega
    have hkH : ((k : ℤ)) ≠ (H : ℤ) := by omega
    have hkpos : (0 : ℤ) ≤ (k : ℤ) := by omega
    interval_cases t
    · simp [hkpos]
    · simp [hk0]
    · simp [hkH]
    · simp [hkH, hH0]

/-! ## 8. The archimedean torsion product, in the one chart where it is an integer

This section is a **calibration control**.  The identity below holds for every `n` with no
arithmetic input, so it carries no evidence about any particular arithmetic object; its use is that
an organ computing archimedean local heights must return `n` on the torsion orbit or it is wrong. -/

/-- **`∏_{ζⁿ = 1, ζ ≠ 1} (1 − ζ) = n`, over `ℤ`.**  The archimedean Green product over the
`n`-torsion of `𝔾_m`, evaluated in the chart where every factor is a cyclotomic value at `1`.
Immediate from `Polynomial.prod_cyclotomic_eq_geom_sum` evaluated at `1`. -/
theorem theTorsionProductOverTheDivisorLatticeIsTheOrder {n : ℕ} (hn : 0 < n) :
    ∏ d ∈ n.divisors.erase 1, (Polynomial.cyclotomic d ℤ).eval 1 = (n : ℤ) := by
  have h := Polynomial.prod_cyclotomic_eq_geom_sum hn ℤ
  apply_fun Polynomial.eval 1 at h
  rwa [Polynomial.eval_prod, Polynomial.eval_geom_sum, one_geom_sum] at h

/-- **The torsion product's prime factorization is the finite ledger of `n`.**  So the archimedean
value read here and the finite ledger of §3 are two charts of one integer, and the divisor lattice
is what carries the passage between them. -/
theorem theTorsionProductHasTheFiniteLedgerOfItsOrder {n : ℕ} (hn : 0 < n) :
    ∏ d ∈ n.divisors.erase 1, (Polynomial.cyclotomic d ℤ).eval 1
      = ∏ p ∈ n.primeFactors, (p : ℤ) ^ n.factorization p := by
  rw [theTorsionProductOverTheDivisorLatticeIsTheOrder hn]
  have h := Nat.factorization_prod_pow_eq_self hn.ne'
  rw [Finsupp.prod, Nat.support_factorization] at h
  exact_mod_cast h.symm

end Soma.Holonics.Millennium.PlaceLedger
