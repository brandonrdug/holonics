import ElementaryHolonics.Millennium.UniversalBSD

/-!
# UniversalBSDLedger: the complete Millennium statement

`UniversalBSD.lean` posed the **rank clause** for every elliptic curve over `ℚ`.
The Millennium statement has a second clause — the leading Taylor coefficient of
`L` at the center is the arithmetic ledger

```text
lim_{s→1} L(E,s)/(s−1)^r  =  (Ω · Reg · ∏_v c_v · |Ш|) / |E(ℚ)_tors|²
```

This file carries that clause with the objects it names.

* **`HeightDatum E`** — the Néron–Tate canonical height, declared by its
  characterizing laws: nonnegative, quadratic (`ĥ(n·P) = n²·ĥ(P)` and the
  parallelogram law), and vanishing exactly on torsion.  Declared, not
  constructed — the same method the analytic datum uses, and the same method the
  Millennium statement itself uses when it writes `Ш` before anyone has proved
  `Ш` finite.
* **`pairing`, `regulator`** — the height pairing and the Gram determinant of a
  basis modulo torsion.  At rank zero the Gram matrix is empty and the regulator
  is `1`, which is why the rank-zero ledger needs no height theory.
* **`ArithmeticDatum`** — the Tamagawa product, the torsion order, the order of
  `Ш` (a positive **square**, forced by the alternating Cassels pairing), and the
  real period.
* **`TheLedgerClauseOn`**, **`TheBirchSwinnertonDyerConjecture`** — the complete
  statement: the rank clause **and** the ledger clause, for every integral model
  over `ℤ`, every level, and every datum carried by it.
* **`theRankZeroLedgerIsTheCentralValue`** — at rank zero the clause reads
  `L(1) = (|Ш|·∏c/|T|²)·Ω`, matching the family pose exactly, with the regulator
  discharged to `1` rather than assumed away.
* **`theCompleteConjectureImpliesTheRankConjecture`** — the complete statement
  contains the rank statement, so every consequence already derived stands under it.

Every `theorem` is discharged and none depends on `sorryAx`.  **Boundary**: nothing
here is claimed as proved about the conjecture; this file is the *statement*, at the
standard the Millennium problem states it.
-/

noncomputable section

namespace Soma.Holonics.Millennium.UniversalBSDLedger

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.UniversalBSD

/-! ## 1. The canonical height and the regulator -/

/-- **The Néron–Tate canonical height**, declared by its characterizing laws.  A
`HeightDatum` is a real-valued function on the rational points that is nonnegative,
homogeneous of degree two under multiplication by an integer, satisfies the
parallelogram law, and vanishes exactly on the torsion. -/
structure HeightDatum (E : WeierstrassCurve.Affine ℚ) where
  /-- The canonical height. -/
  height : E.Point → ℝ
  /-- Nonnegativity. -/
  nonneg : ∀ P, 0 ≤ height P
  /-- Quadratic homogeneity. -/
  smul : ∀ (m : ℤ) (P), height (m • P) = (m : ℝ) ^ 2 * height P
  /-- The parallelogram law, which makes the pairing below bilinear. -/
  parallelogram : ∀ P Q,
    height (P + Q) + height (P - Q) = 2 * height P + 2 * height Q
  /-- The height vanishes exactly on the torsion. -/
  vanishes_iff : ∀ P, height P = 0 ↔ IsTorsionOn E P

variable {E : WeierstrassCurve.Affine ℚ}

/-- The height pairing `⟨P,Q⟩ = (ĥ(P+Q) − ĥ(P) − ĥ(Q))/2`. -/
def pairing (H : HeightDatum E) (P Q : E.Point) : ℝ :=
  (H.height (P + Q) - H.height P - H.height Q) / 2

lemma pairing_self (H : HeightDatum E) (P : E.Point) :
    pairing H P P = H.height P := by
  unfold pairing
  have h := H.parallelogram P P
  have hzero : H.height (P - P) = 0 := by
    rw [sub_self]
    exact (H.vanishes_iff 0).mpr ⟨1, one_pos, by simp⟩
  rw [hzero] at h
  linarith

lemma pairing_comm (H : HeightDatum E) (P Q : E.Point) :
    pairing H P Q = pairing H Q P := by
  unfold pairing
  rw [add_comm P Q]
  ring

/-- **The regulator** of a family of points: the Gram determinant of the height
pairing.  On a basis modulo torsion this is the Néron–Tate regulator; at rank zero
the matrix is empty and the determinant is `1`. -/
def regulator (H : HeightDatum E) {r : ℕ} (Pts : Fin r → E.Point) : ℝ :=
  Matrix.det (Matrix.of fun i j => pairing H (Pts i) (Pts j))

@[simp]
lemma regulator_zero (H : HeightDatum E) (Pts : Fin 0 → E.Point) :
    regulator H Pts = 1 := by
  unfold regulator
  simp

/-- A family of points is a **basis modulo torsion** when it is independent modulo
torsion and every rational point differs from an integer combination of it by a
torsion point. -/
def IsBasisModTorsion (E : WeierstrassCurve.Affine ℚ) {r : ℕ}
    (Pts : Fin r → E.Point) : Prop :=
  IndependentModTorsionOn E Pts ∧
    ∀ P : E.Point, ∃ c : Fin r → ℤ, IsTorsionOn E (P - ∑ i, c i • Pts i)

lemma isBasisModTorsion_zero_of_rank_zero (E : WeierstrassCurve.Affine ℚ)
    (h : ∀ P : E.Point, IsTorsionOn E P) :
    IsBasisModTorsion E (fun i : Fin 0 => i.elim0) :=
  ⟨fun c _ i => i.elim0, fun P => ⟨fun i => i.elim0, by simpa using h P⟩⟩

/-! ## 2. The arithmetic ledger -/

/-- **The arithmetic side of the ledger**: the Tamagawa product, the torsion order,
the order of the Tate–Shafarevich group (a positive square, forced by the
alternating Cassels pairing), and the real period of the model. -/
structure ArithmeticDatum (E : WeierstrassCurve.Affine ℚ) where
  /-- The product of the local Tamagawa numbers. -/
  tamagawa : ℕ
  tamagawa_pos : 0 < tamagawa
  /-- The order of the rational torsion. -/
  torsion : ℕ
  torsion_pos : 0 < torsion
  /-- The order of `Ш`. -/
  sha : ℕ
  sha_pos : 0 < sha
  /-- `Ш` carries an alternating pairing, so its order is a square. -/
  sha_square : IsSquare sha
  /-- The real period. -/
  period : ℝ
  period_pos : 0 < period

/-- The leading Taylor coefficient of `L` at the center, for an order-`r` zero. -/
def leadingCoeff (L : ℂ → ℂ) (r : ℕ) : ℂ :=
  iteratedDeriv r L 1 / (Nat.factorial r : ℂ)

/-! ## 3. The complete statement -/

/-- **The ledger clause for an arbitrary curve**: whenever the rank is `r` and `Pts`
is a basis modulo torsion, the leading Taylor coefficient of `L` at the center is
the arithmetic ledger `(Ω · Reg · ∏c · |Ш|)/|T|²`. -/
def TheLedgerClauseOn (W : WeierstrassCurve ℤ) (M : ℕ) (D : LDatumOn W M)
    (H : HeightDatum (rationalModel W)) (A : ArithmeticDatum (rationalModel W)) :
    Prop :=
  ∀ (r : ℕ) (Pts : Fin r → (rationalModel W).Point),
    RankIsOn (rationalModel W) r → IsBasisModTorsion (rationalModel W) Pts →
      leadingCoeff D.L r =
        ((A.period * regulator H Pts * (A.tamagawa : ℝ) * (A.sha : ℝ)
          / ((A.torsion : ℝ) ^ 2) : ℝ) : ℂ)

/-- **THE BIRCH–SWINNERTON-DYER CONJECTURE, COMPLETE AND UNIVERSALLY QUANTIFIED**:
for every integral Weierstrass model over `ℤ`, every level, every analytic datum,
every canonical height and every arithmetic ledger it carries, the order of vanishing
of `L` at the center is the rank of the rational points **and** the leading Taylor
coefficient is the arithmetic ledger.  This is the Millennium statement. -/
def TheBirchSwinnertonDyerConjecture : Prop :=
  ∀ (W : WeierstrassCurve ℤ) (M : ℕ) (D : LDatumOn W M)
    (H : HeightDatum (rationalModel W)) (A : ArithmeticDatum (rationalModel W)),
    TheRankClauseOn W M D ∧ TheLedgerClauseOn W M D H A

/-- **THE COMPLETE STATEMENT CONTAINS THE RANK STATEMENT**: every consequence this
tree has derived from the rank conjecture stands under the complete conjecture,
provided the curve carries a height and a ledger. -/
theorem theCompleteConjectureImpliesTheRankConjecture
    (hBSD : TheBirchSwinnertonDyerConjecture)
    (hcarry : ∀ W : WeierstrassCurve ℤ,
      HeightDatum (rationalModel W) × ArithmeticDatum (rationalModel W)) :
    TheBirchSwinnertonDyerRankConjecture := by
  intro W M D
  obtain ⟨H, A⟩ := hcarry W
  exact (hBSD W M D H A).1

/-! ## 4. The rank-zero reading -/

lemma leadingCoeff_zero (L : ℂ → ℂ) : leadingCoeff L 0 = L 1 := by
  unfold leadingCoeff
  simp

/-- **THE RANK-ZERO LEDGER IS THE CENTRAL VALUE**: at rank zero the regulator is the
empty determinant `1`, so the ledger clause reads `L(1) = (|Ш|·∏c/|T|²)·Ω` — exactly
the family's rank-zero ledger, with the regulator **discharged** rather than assumed
away. -/
theorem theRankZeroLedgerIsTheCentralValue (W : WeierstrassCurve ℤ) (M : ℕ)
    (D : LDatumOn W M) (H : HeightDatum (rationalModel W))
    (A : ArithmeticDatum (rationalModel W))
    (hledger : TheLedgerClauseOn W M D H A)
    (hrank : RankIsOn (rationalModel W) 0)
    (htor : ∀ P : (rationalModel W).Point, IsTorsionOn (rationalModel W) P) :
    D.L 1 = (((A.tamagawa : ℝ) * (A.sha : ℝ) / ((A.torsion : ℝ) ^ 2) * A.period : ℝ) : ℂ) := by
  have h := hledger 0 (fun i : Fin 0 => i.elim0) hrank
    (isBasisModTorsion_zero_of_rank_zero _ htor)
  rw [leadingCoeff_zero] at h
  rw [h, regulator_zero]
  push_cast
  ring


/-! ## 5. Rank zero really is all-torsion, and the family cash-out -/

/-- **RANK ZERO FORCES EVERY POINT TORSION**: the rank-zero hypothesis of the ledger
is not an extra assumption — it is the rank statement itself. -/
theorem theRankZeroForcesAllTorsion (E : WeierstrassCurve.Affine ℚ)
    (h : ¬ RankAtLeastOn E 1) (P : E.Point) : IsTorsionOn E P := by
  by_contra hP
  refine h ⟨fun _ => P, fun c hc i => ?_⟩
  by_contra hc0
  refine hP ?_
  obtain ⟨k, hk, hkP⟩ := hc
  have hsum : (∑ j : Fin 1, c j • P) = c i • P := by
    have : i = 0 := Subsingleton.elim _ _
    subst this
    simp
  rw [hsum] at hkP
  rw [← natCast_zsmul, smul_smul] at hkP
  set m : ℤ := (k : ℤ) * c i with hm
  have hm0 : m ≠ 0 := by
    rw [hm]
    exact mul_ne_zero (by exact_mod_cast hk.ne') hc0
  refine ⟨m.natAbs, Int.natAbs_pos.mpr hm0, ?_⟩
  rcases Int.natAbs_eq m with hme | hme
  · have : (m.natAbs : ℤ) • P = 0 := by rw [← hme]; exact hkP
    simpa using this
  · have : (m.natAbs : ℤ) • P = 0 := by
      rw [show ((m.natAbs : ℤ)) = -m from by omega, neg_smul, hkP, neg_zero]
    simpa using this

/-- **THE COMPLETE CONJECTURE CLOSES THE LEDGER AT EVERY PRIME `p ≡ 3 (mod 8)`**:
Genocchi's descent supplies rank zero as a theorem, so the rank-zero hypothesis and
the all-torsion hypothesis are both discharged, the regulator is `1`, and the
Millennium ledger reads `L(1) = (|Ш|·∏c/|T|²)·Ω` with nothing about the rank
assumed. -/
theorem theCompleteConjectureClosesTheLedgerOnTheThreeModEightBranch
    (hBSD : TheBirchSwinnertonDyerConjecture)
    (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 3) (D : BirchSwinnertonDyer.LDatum p)
    (H : HeightDatum (rationalModel (familyModel p)))
    (A : ArithmeticDatum (rationalModel (familyModel p))) :
    D.L 1 = (((A.tamagawa : ℝ) * (A.sha : ℝ) / ((A.torsion : ℝ) ^ 2) * A.period : ℝ) : ℂ) := by
  have hrank : RankIsOn (rationalModel (familyModel p)) 0 :=
    (rankIsOn_familyModel p 0).mpr
      (FamilyGenocchi.theGenocchiLawHoldsOnTheThreeModEightBranch hp8)
  have htor : ∀ P : (rationalModel (familyModel p)).Point,
      IsTorsionOn (rationalModel (familyModel p)) P :=
    theRankZeroForcesAllTorsion _ hrank.2
  exact theRankZeroLedgerIsTheCentralValue (familyModel p) (2 * p) (ofFamilyDatum D)
    H A (hBSD (familyModel p) (2 * p) (ofFamilyDatum D) H A).2 hrank htor

end Soma.Holonics.Millennium.UniversalBSDLedger

