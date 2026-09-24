import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Tower
import Mathlib.FieldTheory.Relrank
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import ElementaryHolonics.Millennium.BooleanTower

/-!
# Straightedge and compass, written rather than noted absent

`BooleanTower` reduced the constructible-polygon classification to one link and then stopped on a
stated absence: *"mathlib has no straightedge-and-compass development at all"*, measured and true.
**A missing definition is not an obstruction; it is work.**  This file is the work.

The whole of ruler-and-compass is three intersection rules, and each is priced here exactly:

| step | price |
|---|---|
| line ∩ line | **nothing** — Cramer's rule is a field operation |
| line ∩ circle | **one square root** — the discriminant of one quadratic |
| circle ∩ circle | **nothing new** — subtracting the two equations cancels the quadratic part exactly, leaving the radical axis, so it *is* line ∩ circle |

So a construction is a chain of square-root adjunctions, and `theTowerHasTwoPowerDegree` says such
a chain has degree `2^j` over `ℚ` — the tower law, with each rung of degree at most two because
the adjoined element kills `X² − z²`.

The corpus's reading: **a compass is an aperture that admits exactly one square root per
contact.**  The discriminant is what it costs, and it is nonnegative for free — because a real
intersection was assumed, so `(2Ax+B)² = B² − 4AC` *exhibits* the nonnegativity rather than
requiring it as a hypothesis.  The obstruction to trisecting an angle is then not that the
construction is hard but that **three is not a power of two**: the tower can only double.

Over `ℂ` the same tower meets the cyclotomic degree and closes the classical necessity direction:
a constructible primitive `n`-th root of unity forces `φ(n) = 2^j`, whence `BooleanTower`'s
arithmetic chain forces `n = 2^a` times distinct Fermat primes.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section
open IntermediateField Module

namespace Soma.Holonics.Millennium.Constructible

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- A chain of square-root adjunctions starting at `ℚ`: at each step one adjoins an element whose
*square* already stands.  Over `ℝ` that is `√d` for `d ≥ 0` in the field; over `ℂ` it is any square
root at all.  One inductive serves both. -/
inductive QuadraticTower : IntermediateField ℚ L → Prop
  | base : QuadraticTower (⊥ : IntermediateField ℚ L)
  | step (K : IntermediateField ℚ L) (h : QuadraticTower K)
      (z : L) (hz : z ^ 2 ∈ K) : QuadraticTower ((K⟮z⟯).restrictScalars ℚ)

/-- An element whose square stands is integral over the standing field: it kills `X² − z²`. -/
theorem theSquareRootIsIntegral (K : IntermediateField ℚ L) (z : L) (hz : z ^ 2 ∈ K) :
    IsIntegral K z := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C ⟨z ^ 2, hz⟩, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub_C _ (by norm_num)
  · simp

/-- Its degree over that field is at most two. -/
theorem theSquareRootDegreeIsAtMostTwo (K : IntermediateField ℚ L) (z : L) (hz : z ^ 2 ∈ K) :
    finrank K (K⟮z⟯) ≤ 2 := by
  have hi := theSquareRootIsIntegral K z hz
  rw [IntermediateField.adjoin.finrank hi]
  have hmonic : (Polynomial.X ^ 2 - Polynomial.C (⟨z ^ 2, hz⟩ : K)).Monic :=
    Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hroot : Polynomial.aeval z (Polynomial.X ^ 2 - Polynomial.C (⟨z ^ 2, hz⟩ : K)) = 0 := by
    simp
  calc (minpoly K z).natDegree
      ≤ (Polynomial.X ^ 2 - Polynomial.C (⟨z ^ 2, hz⟩ : K)).natDegree :=
        Polynomial.natDegree_le_natDegree (minpoly.min K z hmonic hroot)
    _ = 2 := Polynomial.natDegree_X_pow_sub_C

/-- Every quadratic tower is finite over `ℚ` and its degree is a power of two. -/
theorem theTowerHasTwoPowerDegree {K : IntermediateField ℚ L} (h : QuadraticTower K) :
    FiniteDimensional ℚ K ∧ ∃ j : ℕ, finrank ℚ K = 2 ^ j := by
  induction h with
  | base =>
      refine ⟨?_, 0, ?_⟩
      · infer_instance
      · simp
  | step K hK z hz ih =>
      obtain ⟨hfd, j, hj⟩ := ih
      have hi := theSquareRootIsIntegral K z hz
      have hfin : FiniteDimensional K (K⟮z⟯) := IntermediateField.adjoin.finiteDimensional hi
      have hle := theSquareRootDegreeIsAtMostTwo K z hz
      have hpos : 0 < finrank K (K⟮z⟯) := finrank_pos
      have htower : finrank ℚ K * finrank K (K⟮z⟯)
          = finrank ℚ ((K⟮z⟯).restrictScalars ℚ) := Module.finrank_mul_finrank ℚ K (K⟮z⟯)
      have hfd' : FiniteDimensional ℚ ((K⟮z⟯).restrictScalars ℚ) :=
        FiniteDimensional.trans ℚ K (K⟮z⟯)
      refine ⟨hfd', ?_⟩
      interval_cases hr : finrank K (K⟮z⟯)
      · exact ⟨j, by rw [← htower, hj]; ring⟩
      · exact ⟨j + 1, by rw [← htower, hj]; ring⟩

/-! ## The three straightedge-and-compass steps -/

section Steps
variable (K : IntermediateField ℚ ℝ)

/-- Over `ℝ`, `√d` for `d ≥ 0` in `K` is exactly a tower step. -/
theorem theRealSqrtSquareStands {d : ℝ} (hd : d ∈ K) (hd0 : 0 ≤ d) : Real.sqrt d ^ 2 ∈ K := by
  rwa [Real.sq_sqrt hd0]

/-- `K` sits inside any square-root extension of itself. -/
theorem theBaseFieldSitsInside {d : ℝ} {k : ℝ} (hk : k ∈ K) : k ∈ K⟮Real.sqrt d⟯ := by
  have : (algebraMap K ℝ) ⟨k, hk⟩ ∈ K⟮Real.sqrt d⟯ := (K⟮Real.sqrt d⟯).algebraMap_mem _
  simpa using this

/-- The adjoined root is in it. -/
theorem theRootSitsInside (d : ℝ) : Real.sqrt d ∈ K⟮Real.sqrt d⟯ :=
  IntermediateField.mem_adjoin_simple_self _ _

/-- **EVERY ROOT OF A QUADRATIC OVER `K` LIES IN A SQUARE-ROOT EXTENSION OF `K`.**  This is the
entire algebraic content of "compass and straightedge buys one square root": the discriminant is
the adjoined element, and it is automatically nonnegative because a real root was assumed. -/
theorem theQuadraticRootLandsInASquareRootExtension
    {A B C x : ℝ} (hA : A ∈ K) (hB : B ∈ K) (hC : C ∈ K) (hA0 : A ≠ 0)
    (hx : A * x ^ 2 + B * x + C = 0) :
    ∃ d : ℝ, d ∈ K ∧ 0 ≤ d ∧ x ∈ K⟮Real.sqrt d⟯ := by
  set d : ℝ := B ^ 2 - 4 * (A * C) with hd
  have hsq : (2 * A * x + B) ^ 2 = d := by rw [hd]; linear_combination (4 * A) * hx
  have hd0 : (0:ℝ) ≤ d := by rw [← hsq]; positivity
  have hdmem : d ∈ K := by
    rw [hd]
    exact sub_mem (pow_mem hB 2) (mul_mem (by exact_mod_cast K.natCast_mem 4) (mul_mem hA hC))
  refine ⟨d, hdmem, hd0, ?_⟩
  have habs : Real.sqrt d = |2 * A * x + B| := by rw [← hsq, Real.sqrt_sq_eq_abs]
  have hAmem : A ∈ K⟮Real.sqrt d⟯ := theBaseFieldSitsInside K hA
  have hBmem : B ∈ K⟮Real.sqrt d⟯ := theBaseFieldSitsInside K hB
  have hroot : Real.sqrt d ∈ K⟮Real.sqrt d⟯ := theRootSitsInside K d
  have h2mem : (2:ℝ) * A ∈ K⟮Real.sqrt d⟯ :=
    mul_mem (by exact_mod_cast (K⟮Real.sqrt d⟯).natCast_mem 2) hAmem
  rcases abs_cases (2 * A * x + B) with ⟨he, _⟩ | ⟨he, _⟩
  · have hx' : x = (Real.sqrt d - B) / (2 * A) := by
      rw [habs, he]; field_simp; ring
    rw [hx']
    exact div_mem (sub_mem hroot hBmem) h2mem
  · have hx' : x = (-Real.sqrt d - B) / (2 * A) := by
      rw [habs, he]; field_simp; ring
    rw [hx']
    exact div_mem (sub_mem (neg_mem hroot) hBmem) h2mem

/-- **LINE ∩ LINE COSTS NOTHING.**  Cramer's rule is a field operation, so the intersection of two
`K`-lines has `K`-coordinates: the straightedge alone never leaves the field. -/
theorem theLineLineIntersectionStaysInTheField
    {a b c a' b' c' x y : ℝ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K)
    (ha' : a' ∈ K) (hb' : b' ∈ K) (hc' : c' ∈ K)
    (hdet : a * b' - a' * b ≠ 0)
    (h1 : a * x + b * y = c) (h2 : a' * x + b' * y = c') :
    x ∈ K ∧ y ∈ K := by
  have hxm : x * (a * b' - a' * b) = c * b' - c' * b := by linear_combination b' * h1 - b * h2
  have hym : y * (a * b' - a' * b) = a * c' - a' * c := by linear_combination a * h2 - a' * h1
  have hx : x = (c * b' - c' * b) / (a * b' - a' * b) := (eq_div_iff hdet).mpr hxm
  have hy : y = (a * c' - a' * c) / (a * b' - a' * b) := (eq_div_iff hdet).mpr hym
  refine ⟨hx ▸ div_mem (sub_mem (mul_mem hc hb') (mul_mem hc' hb))
      (sub_mem (mul_mem ha hb') (mul_mem ha' hb)),
    hy ▸ div_mem (sub_mem (mul_mem ha hc') (mul_mem ha' hc))
      (sub_mem (mul_mem ha hb') (mul_mem ha' hb))⟩

/-- **CIRCLE ∩ CIRCLE IS LINE ∩ CIRCLE.**  Subtracting the two circle equations cancels the
quadratic part exactly, so any common point of two circles lies on an explicit `K`-line — the
*radical axis*.  Pure algebra, no case split, and it is why the compass buys no more than the
straightedge-plus-one-root already bought. -/
theorem theCircleCircleReducesToALine
    {p₁ q₁ r₁ p₂ q₂ r₂ x y : ℝ}
    (h1 : (x - p₁) ^ 2 + (y - q₁) ^ 2 = r₁ ^ 2)
    (h2 : (x - p₂) ^ 2 + (y - q₂) ^ 2 = r₂ ^ 2) :
    (2 * (p₂ - p₁)) * x + (2 * (q₂ - q₁)) * y
      = (p₂ ^ 2 + q₂ ^ 2 - r₂ ^ 2) - (p₁ ^ 2 + q₁ ^ 2 - r₁ ^ 2) := by
  nlinarith [h1, h2]

/-- **LINE ∩ CIRCLE COSTS EXACTLY ONE SQUARE ROOT.**  Eliminating one coordinate turns the pair
into a single quadratic whose coefficients are in `K`, so both coordinates land in one square-root
extension.  The discriminant is the whole price of the compass. -/
theorem theLineCircleIntersectionCostsOneRoot
    {a b c p q r x y : ℝ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K)
    (hp : p ∈ K) (hq : q ∈ K) (hr : r ∈ K) (hb0 : b ≠ 0)
    (hline : a * x + b * y = c)
    (hcirc : (x - p) ^ 2 + (y - q) ^ 2 = r ^ 2) :
    ∃ d : ℝ, d ∈ K ∧ 0 ≤ d ∧ x ∈ K⟮Real.sqrt d⟯ ∧ y ∈ K⟮Real.sqrt d⟯ := by
  set A : ℝ := a ^ 2 + b ^ 2 with hAdef
  set B : ℝ := -2 * b ^ 2 * p - 2 * a * (c - q * b) with hBdef
  set C : ℝ := b ^ 2 * p ^ 2 + (c - q * b) ^ 2 - r ^ 2 * b ^ 2 with hCdef
  have hA0 : A ≠ 0 := by
    rw [hAdef]; positivity
  have hAmem : A ∈ K := by rw [hAdef]; exact add_mem (pow_mem ha 2) (pow_mem hb 2)
  have hBmem : B ∈ K := by
    rw [hBdef]
    refine sub_mem (mul_mem (mul_mem ?_ (pow_mem hb 2)) hp)
      (mul_mem (mul_mem ?_ ha) (sub_mem hc (mul_mem hq hb)))
    · exact neg_mem (by exact_mod_cast K.natCast_mem 2)
    · exact_mod_cast K.natCast_mem 2
  have hCmem : C ∈ K := by
    rw [hCdef]
    exact sub_mem (add_mem (mul_mem (pow_mem hb 2) (pow_mem hp 2))
      (pow_mem (sub_mem hc (mul_mem hq hb)) 2)) (mul_mem (pow_mem hr 2) (pow_mem hb 2))
  have hquad : A * x ^ 2 + B * x + C = 0 := by
    rw [hAdef, hBdef, hCdef]
    linear_combination b ^ 2 * hcirc - (c - a * x + b * y - 2 * b * q) * hline
  obtain ⟨d, hdmem, hd0, hxd⟩ :=
    theQuadraticRootLandsInASquareRootExtension K hAmem hBmem hCmem hA0 hquad
  refine ⟨d, hdmem, hd0, hxd, ?_⟩
  have hy : y = (c - a * x) / b := by field_simp; linarith [hline]
  rw [hy]
  exact div_mem (sub_mem (theBaseFieldSitsInside K hc)
    (mul_mem (theBaseFieldSitsInside K ha) hxd)) (theBaseFieldSitsInside K hb)

end Steps

/-! ## The definition, and the degree it forces -/

/-- An element is **constructible** when it is reachable from `ℚ` by a finite chain of square-root
adjunctions — which the three steps above show is exactly what straightedge and compass produce. -/
def IsConstructibleIn (x : L) : Prop := ∃ K : IntermediateField ℚ L, QuadraticTower K ∧ x ∈ K

/-- **A CONSTRUCTIBLE POINT LIES IN A TWO-POWER TOWER.**  The primitive that was missing. -/
theorem theConstructibleDegreeIsATwoPower {x : L} (h : IsConstructibleIn x) :
    ∃ j : ℕ, finrank ℚ ℚ⟮x⟯ = 2 ^ j := by
  obtain ⟨K, hK, hx⟩ := h
  obtain ⟨hfd, j, hj⟩ := theTowerHasTwoPowerDegree hK
  have hle : ℚ⟮x⟯ ≤ K := by
    rw [IntermediateField.adjoin_simple_le_iff]; exact hx
  have hdvd : finrank ℚ ℚ⟮x⟯ ∣ finrank ℚ K :=
    Dvd.intro _ (IntermediateField.finrank_bot_mul_relfinrank hle)
  rw [hj] at hdvd
  obtain ⟨j', _, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨j', hj'⟩

/-- Rationals are constructible. -/
theorem theRationalsAreConstructible (r : ℚ) : IsConstructibleIn (algebraMap ℚ L r) :=
  ⟨⊥, QuadraticTower.base, IntermediateField.algebraMap_mem ⊥ r⟩

/-! ## The cyclotomic bridge: constructibility forces a two-power totient -/

/-- The degree of a primitive `n`-th root over `ℚ` is `φ(n)` — the minimal polynomial is the
cyclotomic one, which is irreducible over `ℚ`. -/
theorem theCyclotomicDegreeIsTheTotient {n : ℕ} [NeZero n] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    finrank ℚ ℚ⟮ζ⟯ = n.totient := by
  have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hirr : Irreducible (Polynomial.cyclotomic n ℚ) := Polynomial.cyclotomic.irreducible_rat hpos
  have hmin : Polynomial.cyclotomic n ℚ = minpoly ℚ ζ :=
    hζ.minpoly_eq_cyclotomic_of_irreducible hirr
  have hint : IsIntegral ℚ ζ := (hζ.isIntegral hpos).tower_top
  rw [IntermediateField.adjoin.finrank hint, ← hmin, Polynomial.natDegree_cyclotomic]

/-- **GAUSS–WANTZEL, NECESSITY.**  If a primitive `n`-th root of unity is constructible then
`φ(n)` is a power of two.  Everything downstream — `n` is a power of two times distinct Fermat
primes — is already standing arithmetic. -/
theorem theConstructibleRootOfUnityForcesTwoPowerTotient {n : ℕ} [NeZero n] {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (h : IsConstructibleIn ζ) : ∃ j : ℕ, n.totient = 2 ^ j := by
  obtain ⟨j, hj⟩ := theConstructibleDegreeIsATwoPower h
  exact ⟨j, by rw [← theCyclotomicDegreeIsTheTotient hζ]; exact hj⟩

/-- **GAUSS–WANTZEL, THE NECESSITY DIRECTION, WHOLE.**  A constructible regular `n`-gon forces
`n = 2^a` times distinct Fermat primes.  The geometry is this file; the arithmetic is
`BooleanTower`; nothing is left over. -/
theorem theGaussWantzelNecessity {n : ℕ} [NeZero n] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    (h : IsConstructibleIn ζ) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ n → (∃ j : ℕ, p = 2 ^ 2 ^ j + 1) ∧ ¬ (p ^ 2 ∣ n) := by
  obtain ⟨k, hk⟩ := theConstructibleRootOfUnityForcesTwoPowerTotient hζ h
  exact fun p hp hodd hdvd =>
    BooleanTower.theOddPrimeFactorsOfATotientPowerAreFermat hk hp hodd hdvd

/-- **THE NINE-GON IS REFUSED**, and the refusal is the trisection of the angle: `φ(9) = 6`, and
six is not a power of two because it carries a factor of three.  **The tower can only double.** -/
theorem theNineGonIsRefused {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 9) : ¬ IsConstructibleIn ζ := by
  intro h
  obtain ⟨j, hj⟩ := theConstructibleRootOfUnityForcesTwoPowerTotient hζ h
  have h6 : Nat.totient 9 = 6 := by decide
  rw [h6] at hj
  have h3 : (3:ℕ) ∣ 2 ^ j := hj ▸ (by norm_num : (3:ℕ) ∣ 6)
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  norm_num at this

/-- **AND THE SEVENTEEN-GON PASSES**: `φ(17) = 2⁴`, the Boolean space of four inputs.  The same
seventeen that carries the descent obstruction is the one Gauss constructed. -/
theorem theSeventeenGonPassesTheTest : Nat.totient 17 = 2 ^ 4 := by decide

end Soma.Holonics.Millennium.Constructible
