import ElementaryHolonics.Millennium.FamilyPairing
import ElementaryHolonics.Millennium.FamilyDivisorRank

/-!
# UniversalBSD: the conjecture posed for **every** elliptic curve over `ℚ`

`BirchSwinnertonDyer.lean` poses the conjecture for the congruent-number twist at a
modulus.  This file poses it as the Millennium statement does — quantified over
**every** elliptic curve over `ℚ` — and proves the family pose is an instance.

* **`LDatumOn W M`** — the analytic datum attached to an integral Weierstrass curve
  `W` over `ℤ`: Dirichlet coefficients equal to the traces of Frobenius at the good
  primes, the Euler recursion, an entire continuation agreeing with the series, a
  conductor, a sign, and the completed functional equation `Λ(2−s) = w·Λ(s)`.
* **`RankAtLeastOn`, `RankIsOn`** — the algebraic rank of `W(ℚ)`, with no
  Mordell–Weil input, exactly as the family pose defines it.
* **`TheRankClauseOn`** — order of vanishing at the center equals the algebraic rank.
* **`TheBirchSwinnertonDyerRankConjecture`** — `∀ W, ∀ M, ∀ D : LDatumOn W M`, the
  rank clause.  This is the universally quantified statement.
* **`theFamilyPoseIsAnInstance`** — every family datum `LDatum n` is an `LDatumOn`
  for the integral model `y² = x³ − n²x`, with the same `L`, so the universal
  conjecture implies every family rank clause this tree has posed.
* **`theUniversalConjectureMakesEveryOddSignPrimeCongruent`** — the cash-out: under
  the universal statement, **every prime `p ≡ 5, 7 (mod 8)` is a congruent number**
  and its rank is exactly one.  The analytic half (central vanishing from the odd
  root number) and the descent half (rank at most one) are both theorems here; the
  conjecture supplies only the bridge between them.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.UniversalBSD

open Finset
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.BirchSwinnertonDyer

/-! ## 1. The rational model and its point counts -/

/-- The curve over `ℚ` cut out by an integral Weierstrass model. -/
def rationalModel (W : WeierstrassCurve ℤ) : WeierstrassCurve.Affine ℚ :=
  W.map (Int.castRingHom ℚ)

/-- The affine point count of an integral model reduced modulo `p`. -/
def affineCountOn (W : WeierstrassCurve ℤ) (p : ℕ) [NeZero p] : ℕ :=
  ∑ x : ZMod p, (univ.filter fun y : ZMod p =>
    y ^ 2 + (W.a₁ : ZMod p) * x * y + (W.a₃ : ZMod p) * y
      = x ^ 3 + (W.a₂ : ZMod p) * x ^ 2 + (W.a₄ : ZMod p) * x + (W.a₆ : ZMod p)).card

/-- The trace of Frobenius of an integral model: `a_p = p + 1 − #E(𝔽_p)`. -/
def traceOn (W : WeierstrassCurve ℤ) (p : ℕ) [NeZero p] : ℤ :=
  (p : ℤ) - affineCountOn W p

/-! ## 2. The algebraic rank of an arbitrary curve -/

/-- A point of finite order. -/
def IsTorsionOn (E : WeierstrassCurve.Affine ℚ) (P : E.Point) : Prop :=
  ∃ k : ℕ, 0 < k ∧ k • P = 0

/-- No nonzero integer combination is torsion. -/
def IndependentModTorsionOn (E : WeierstrassCurve.Affine ℚ) {r : ℕ}
    (Pts : Fin r → E.Point) : Prop :=
  ∀ c : Fin r → ℤ, IsTorsionOn E (∑ i, c i • Pts i) → ∀ i, c i = 0

/-- The rank of `E(ℚ)` is at least `r`. -/
def RankAtLeastOn (E : WeierstrassCurve.Affine ℚ) (r : ℕ) : Prop :=
  ∃ Pts : Fin r → E.Point, IndependentModTorsionOn E Pts

/-- The rank of `E(ℚ)` is exactly `r`. -/
def RankIsOn (E : WeierstrassCurve.Affine ℚ) (r : ℕ) : Prop :=
  RankAtLeastOn E r ∧ ¬ RankAtLeastOn E (r + 1)

/-! ## 3. The analytic datum of an arbitrary curve -/

/-- **The declared analytic datum for an integral Weierstrass model `W`**, with the
Euler laws holding away from the level `M`.  Classically such a datum exists for
every elliptic curve over `ℚ` by modularity; the pose declares it and the family
files construct one by hand through the theta/Poisson deed. -/
structure LDatumOn (W : WeierstrassCurve ℤ) (M : ℕ) where
  /-- The Dirichlet coefficients. -/
  coeff : ℕ → ℂ
  /-- Normalization. -/
  coeff_one : coeff 1 = 1
  /-- The coefficients are the traces of Frobenius at the good primes. -/
  coeff_prime : ∀ p : ℕ, ∀ hp : p.Prime, ¬ p ∣ M →
    coeff p = ((@traceOn W p ⟨hp.pos.ne'⟩ : ℤ) : ℂ)
  /-- Multiplicativity across coprime indices. -/
  coeff_mul : ∀ a b : ℕ, Nat.Coprime a b → coeff (a * b) = coeff a * coeff b
  /-- The Euler recursion at good prime powers. -/
  coeff_prime_pow : ∀ p k : ℕ, p.Prime → ¬ p ∣ M →
    coeff (p ^ (k + 2)) = coeff p * coeff (p ^ (k + 1)) - (p : ℂ) * coeff (p ^ k)
  /-- Bad prime powers carry the degenerate Euler factor. -/
  coeff_bad : ∀ p k : ℕ, p.Prime → p ∣ M → coeff (p ^ (k + 1)) = coeff p ^ (k + 1)
  /-- The analytic continuation. -/
  L : ℂ → ℂ
  /-- Entirety. -/
  analytic : Differentiable ℂ L
  /-- Agreement with the Dirichlet series on a right half-plane. -/
  agrees : ∀ s : ℂ, 3 < s.re → L s = LSeries coeff s
  /-- The conductor. -/
  conductor : ℕ
  conductor_pos : 0 < conductor
  /-- The sign of the functional equation. -/
  sign : ℤ
  sign_pm : sign = 1 ∨ sign = -1
  /-- The completed L-function. -/
  Lambda : ℂ → ℂ
  /-- The completed function is entire. -/
  Lambda_analytic : Differentiable ℂ Lambda
  /-- Away from the poles of `Γ`, the completed function is the classical product. -/
  Lambda_eq : ∀ s : ℂ, (∀ m : ℕ, s ≠ -(m : ℂ)) →
    Lambda s = BirchSwinnertonDyer.completed conductor L s
  /-- The completed functional equation. -/
  functional_equation : ∀ s : ℂ, Lambda (2 - s) = (sign : ℂ) * Lambda s

/-- **The rank clause for an arbitrary curve**: the order of vanishing of `L` at the
center of the functional equation equals the rank of `W(ℚ)`. -/
def TheRankClauseOn (W : WeierstrassCurve ℤ) (M : ℕ) (D : LDatumOn W M) : Prop :=
  ∀ r : ℕ, analyticOrderAt D.L 1 = (r : ℕ∞) ↔ RankIsOn (rationalModel W) r

/-- **THE BIRCH–SWINNERTON-DYER RANK CONJECTURE, UNIVERSALLY QUANTIFIED**: for every
integral Weierstrass model over `ℤ`, every level, and every analytic datum carried by
it, the order of vanishing at the center equals the rank of the rational points.  This
is the Millennium statement's rank clause with the quantifier it carries. -/
def TheBirchSwinnertonDyerRankConjecture : Prop :=
  ∀ (W : WeierstrassCurve ℤ) (M : ℕ) (D : LDatumOn W M), TheRankClauseOn W M D


/-! ## 4. The family is an instance -/

/-- The integral model of the congruent-number twist: `y² = x³ − n²x`. -/
def familyModel (n : ℕ) : WeierstrassCurve ℤ := ⟨0, 0, 0, -(n : ℤ) ^ 2, 0⟩

lemma rationalModel_familyModel (n : ℕ) :
    rationalModel (familyModel n) = FamilyFace.E ((n : ℚ)) := by
  unfold rationalModel familyModel FamilyFace.E WeierstrassCurve.map
  norm_num

lemma affineCountOn_familyModel (n p : ℕ) [NeZero p] :
    affineCountOn (familyModel n) p = BirchSwinnertonDyer.affineCount n p := by
  unfold affineCountOn BirchSwinnertonDyer.affineCount familyModel
  refine Finset.sum_congr rfl fun x _ => ?_
  refine congrArg Finset.card (Finset.filter_congr fun y _ => ?_)
  constructor
  · intro h
    push_cast at h ⊢
    linear_combination h
  · intro h
    push_cast at h ⊢
    linear_combination h

lemma traceOn_familyModel (n p : ℕ) [NeZero p] :
    traceOn (familyModel n) p = BirchSwinnertonDyer.traceOfFrobenius n p := by
  unfold traceOn BirchSwinnertonDyer.traceOfFrobenius
  rw [affineCountOn_familyModel]

/-- **THE FAMILY DATUM IS A UNIVERSAL DATUM**: every `LDatum n` this tree constructs
is an analytic datum for the integral model `y² = x³ − n²x` at level `2n`, carrying
the same continued `L`. -/
def ofFamilyDatum {n : ℕ} (D : LDatum n) : LDatumOn (familyModel n) (2 * n) where
  coeff := D.coeff
  coeff_one := D.coeff_one
  coeff_prime := fun p hp hpd => by
    haveI : NeZero p := ⟨hp.pos.ne'⟩
    rw [D.coeff_prime p hp hpd, traceOn_familyModel]
  coeff_mul := D.coeff_mul
  coeff_prime_pow := D.coeff_prime_pow
  coeff_bad := D.coeff_bad
  L := D.L
  analytic := D.analytic
  agrees := D.agrees
  conductor := D.conductor
  conductor_pos := D.conductor_pos
  sign := D.sign
  sign_pm := D.sign_pm
  Lambda := D.Lambda
  Lambda_analytic := D.Lambda_analytic
  Lambda_eq := D.Lambda_eq
  functional_equation := D.functional_equation

lemma rankAtLeastOn_familyModel (n r : ℕ) :
    RankAtLeastOn (rationalModel (familyModel n)) r ↔ AlgebraicRankAtLeast n r := by
  rw [rationalModel_familyModel]
  rfl

lemma rankIsOn_familyModel (n r : ℕ) :
    RankIsOn (rationalModel (familyModel n)) r ↔ AlgebraicRankIs n r := by
  unfold RankIsOn AlgebraicRankIs
  rw [rankAtLeastOn_familyModel, rankAtLeastOn_familyModel]

/-- **THE FAMILY POSE IS AN INSTANCE OF THE UNIVERSAL POSE**: the universal rank
conjecture implies every family rank clause this tree has posed. -/
theorem theFamilyPoseIsAnInstance (hBSD : TheBirchSwinnertonDyerRankConjecture)
    (n : ℕ) (D : LDatum n) : TheRankClause n D := by
  intro r
  have h := hBSD (familyModel n) (2 * n) (ofFamilyDatum D) r
  rw [rankIsOn_familyModel] at h
  exact h


/-! ## 5. The cash-out on the odd-sign locus -/

/-- **THE UNIVERSAL CONJECTURE MAKES EVERY ODD-SIGN PRIME A CONGRUENT NUMBER**:
under the Millennium rank clause quantified over every elliptic curve, at every
prime `p ≡ 5, 7 (mod 8)` the curve `y² = x³ − p²x` has a rational point of infinite
order and its rank is **exactly one**.

Both endpoints are theorems of this tree and neither consumes the conjecture: the
theta functional equation forces the root number to be `−1`, hence the central value
to vanish, hence the analytic rank to be positive; and the eight-cell descent forces
the algebraic rank to be at most one.  The conjecture supplies only the bridge. -/
theorem theUniversalConjectureMakesEveryOddSignPrimeCongruent
    (hBSD : TheBirchSwinnertonDyerRankConjecture)
    (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 5 ∨ p % 8 = 7) :
    AlgebraicRankIs p 1 := by
  have hp2 : p ≠ 2 := by rcases hp8 with h | h <;> omega
  have hclause : TheRankClause p (FamilyWitness.theWitnessAtEveryOddPrime p hp2) :=
    theFamilyPoseIsAnInstance hBSD p _
  exact (FamilyPairing.theConjectureIsSqueezedToASinglePointOnTheOddSignLocus
    p hp8 hclause).1

/-- **THE UNIVERSAL CONJECTURE FORCES ANALYTIC RANK ZERO AT EVERY `p ≡ 3 (mod 8)`**:
Genocchi's descent is the algebraic half as a theorem, so the clause pins the
analytic side with nothing else assumed. -/
theorem theUniversalConjectureForcesAnalyticRankZeroOnTheThreeModEightBranch
    (hBSD : TheBirchSwinnertonDyerRankConjecture)
    (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 3) (D : LDatum p) :
    analyticRank D = (0 : ℕ∞) :=
  (theFamilyPoseIsAnInstance hBSD p D 0).mpr
    (FamilyGenocchi.theGenocchiLawHoldsOnTheThreeModEightBranch hp8)

/-- **THE DIAL UNDER THE UNIVERSAL CONJECTURE**: the complete reading of the
congruent-number family at odd primes, with every algebraic endpoint a theorem of
this tree and the conjecture used only to transport them to the analytic side. -/
theorem theUniversalDialOnTheCongruentFamily
    (hBSD : TheBirchSwinnertonDyerRankConjecture)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (p % 8 = 3 → AlgebraicRankIs p 0 ∧
      analyticRank (FamilyWitness.theWitnessAtEveryOddPrime p hp2) = (0 : ℕ∞)) ∧
    ((p % 8 = 5 ∨ p % 8 = 7) → AlgebraicRankIs p 1 ∧
      analyticRank (FamilyWitness.theWitnessAtEveryOddPrime p hp2) = (1 : ℕ∞)) ∧
    (p % 8 = 1 → ¬ AlgebraicRankAtLeast p 3) := by
  refine ⟨fun h => ⟨FamilyGenocchi.theGenocchiLawHoldsOnTheThreeModEightBranch h,
      theUniversalConjectureForcesAnalyticRankZeroOnTheThreeModEightBranch hBSD p h _⟩,
    fun h => ?_,
    fun _ => FamilyOddDescent.theRankIsAtMostTwoAtEveryOddPrime hp2⟩
  have hIs : AlgebraicRankIs p 1 :=
    theUniversalConjectureMakesEveryOddSignPrimeCongruent hBSD p h
  exact ⟨hIs, (theFamilyPoseIsAnInstance hBSD p _ 1).mpr hIs⟩

end Soma.Holonics.Millennium.UniversalBSD

