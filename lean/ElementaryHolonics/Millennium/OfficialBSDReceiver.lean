import ElementaryHolonics.Millennium.BirchSwinnertonDyer
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.GroupTheory.Torsion

/-!
# OfficialBSDReceiver: a parameter-free Birch--Swinnerton--Dyer finish line

[definition] This module repairs the repository receiver without asserting the
Birch--Swinnerton--Dyer conjecture.  A source is an actually elliptic
Weierstrass curve over `ℚ`.  Its analytic section is required to continue the
Hasse--Weil `L`-series already constructed from that curve by Mathlib.  Its
arithmetic section uses the actual rational-point group, its actual torsion
subgroup, and a Tate--Shafarevich group presented as the kernel of one
global-to-local cohomology homomorphism.

[definition] The parameter-free terminal proposition constructs one source
theory for every rational elliptic curve and only then concludes Sha finiteness,
rank equality, and the leading-coefficient ledger.  In particular, an empty
analytic-data family cannot inhabit the receiver, and finiteness of Sha is not a
field of the entering data.

[open] Mathlib does not yet construct the global/local cohomology realization,
Neron--Tate height, local Tamagawa product, real period, analytic continuation,
or their complete model-change transport for every rational elliptic curve.
Those are explicit source-construction obligations of this finish line, not
assumptions hidden inside the conjectural equalities.

[open] This closed repository receiver includes those source-construction
obligations.  Faithfulness of the cohomology, Tamagawa, period, and height
interfaces to their full classical constructions is a remaining formalization
boundary.  No theorem in this file claims equivalence to an independently
formalized Clay statement.
-/

noncomputable section

namespace Soma.Holonics.Millennium.OfficialBSDReceiver

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.BirchSwinnertonDyer

/-! ## 1. The non-vacuous source domain -/

/-- [definition] A rational elliptic curve is a rational Weierstrass model with
an actual proof that its discriminant is a unit.  A possibly singular raw model
cannot enter this source type. -/
structure RationalEllipticCurve where
  model : WeierstrassCurve ℚ
  elliptic : model.IsElliptic

attribute [instance] RationalEllipticCurve.elliptic

/-- [definition] Re-present the same rational elliptic curve through an
admissible Weierstrass variable change. -/
def RationalEllipticCurve.rebase (E : RationalEllipticCurve)
    (C : WeierstrassCurve.VariableChange ℚ) : RationalEllipticCurve where
  model := C • E.model
  elliptic := inferInstance

/-! ## 2. Source-determined analytic and arithmetic sections -/

/-- [definition] The analytic section is pinned to the curve-derived Mathlib
Hasse--Weil `L`-series on a right half-plane.  The continuation, conductor, and
functional equation must be constructed; there is no caller-supplied coefficient
ledger. -/
structure AnalyticDatum (E : RationalEllipticCurve) where
  L : ℂ → ℂ
  analytic : Differentiable ℂ L
  agreesWithHasseWeil : ∀ s : ℂ, 3 < s.re → L s = E.model.LSeries s
  conductor : ℕ
  conductor_pos : 0 < conductor
  sign : ℤ
  sign_pm : sign = 1 ∨ sign = -1
  completedL : ℂ → ℂ
  completed_analytic : Differentiable ℂ completedL
  completed_eq : ∀ s : ℂ, (∀ m : ℕ, s ≠ -(m : ℂ)) →
    completedL s = BirchSwinnertonDyer.completed conductor L s
  functional_equation : ∀ s : ℂ,
    completedL (2 - s) = (sign : ℂ) * completedL s

/-- [definition] The actual torsion subgroup of the rational-point group. -/
abbrev RationalTorsion (E : RationalEllipticCurve) : Type :=
  AddCommGroup.torsion E.model.toAffine.Point

/-- [definition] A rational point is torsion when one positive multiple is zero. -/
def IsTorsion (E : RationalEllipticCurve) (P : E.model.toAffine.Point) : Prop :=
  ∃ k : ℕ, 0 < k ∧ k • P = 0

/-- [definition] Independence in the Mordell--Weil group modulo its actual
torsion subgroup. -/
def IndependentModTorsion (E : RationalEllipticCurve) {r : ℕ}
    (Pts : Fin r → E.model.toAffine.Point) : Prop :=
  ∀ c : Fin r → ℤ, IsTorsion E (∑ i, c i • Pts i) → ∀ i, c i = 0

/-- [definition] The rational-point rank is at least `r`. -/
def RankAtLeast (E : RationalEllipticCurve) (r : ℕ) : Prop :=
  ∃ Pts : Fin r → E.model.toAffine.Point, IndependentModTorsion E Pts

/-- [definition] The rational-point rank is exactly `r`. -/
def RankIs (E : RationalEllipticCurve) (r : ℕ) : Prop :=
  RankAtLeast E r ∧ ¬ RankAtLeast E (r + 1)

/-- [definition] A basis of the rational points modulo torsion. -/
def IsBasisModTorsion (E : RationalEllipticCurve) {r : ℕ}
    (Pts : Fin r → E.model.toAffine.Point) : Prop :=
  IndependentModTorsion E Pts ∧
    ∀ P : E.model.toAffine.Point, ∃ c : Fin r → ℤ,
      IsTorsion E (P - ∑ i, c i • Pts i)

/-- [definition] The Neron--Tate height interface contains only its standard
characterizing laws and no analytic-rank or leading-ledger equality. -/
structure HeightDatum (E : RationalEllipticCurve) where
  height : E.model.toAffine.Point → ℝ
  nonneg : ∀ P, 0 ≤ height P
  smul : ∀ (m : ℤ) (P), height (m • P) = (m : ℝ) ^ 2 * height P
  parallelogram : ∀ P Q,
    height (P + Q) + height (P - Q) = 2 * height P + 2 * height Q
  vanishes_iff : ∀ P, height P = 0 ↔ IsTorsion E P

/-- [definition] The height pairing associated to a height interface. -/
def heightPairing {E : RationalEllipticCurve} (H : HeightDatum E)
    (P Q : E.model.toAffine.Point) : ℝ :=
  (H.height (P + Q) - H.height P - H.height Q) / 2

/-- [definition] The Neron--Tate regulator is the determinant of the height
pairing on an arithmetic basis. -/
def regulatorOn {E : RationalEllipticCurve} (H : HeightDatum E) {r : ℕ}
    (Pts : Fin r → E.model.toAffine.Point) : ℝ :=
  Matrix.det (Matrix.of fun i j => heightPairing H (Pts i) (Pts j))

/-- [definition] The leading Taylor coefficient at the central point. -/
def leadingCoefficient (L : ℂ → ℂ) (r : ℕ) : ℂ :=
  iteratedDeriv r L 1 / (Nat.factorial r : ℂ)

/-- [definition] The arithmetic source section contains no Sha order and no Sha
finiteness proof.  It presents the global and local degree-one cohomology groups
and their localization homomorphism, so Sha is subsequently formed as a kernel.
The remaining fields are the standard, nonconjectural arithmetic constructions
which the receiver requires to be produced from the curve. -/
structure ArithmeticDatum (E : RationalEllipticCurve) where
  mordellWeilRank : ℕ
  basis : Fin mordellWeilRank → E.model.toAffine.Point
  basis_mod_torsion :
    IsBasisModTorsion E basis
  rank_spec : ∀ r : ℕ,
    RankIs E r ↔ r = mordellWeilRank
  height : HeightDatum E
  regulator : ℝ
  regulator_eq : regulator =
    regulatorOn height basis
  regulator_pos : 0 < regulator
  localTamagawaProduct : ℕ
  localTamagawaProduct_pos : 0 < localTamagawaProduct
  realPeriod : ℝ
  realPeriod_pos : 0 < realPeriod
  torsion_finite : Finite (RationalTorsion E)
  globalH1 : Type
  localH1 : Type
  globalH1Group : AddCommGroup globalH1
  localH1Group : AddCommGroup localH1
  localization : globalH1 →+ localH1

attribute [instance] ArithmeticDatum.globalH1Group ArithmeticDatum.localH1Group

/-- [definition] The Tate--Shafarevich group is the actual kernel of the
global-to-local cohomology passage carried by the arithmetic source section. -/
abbrev TateShafarevichGroup {E : RationalEllipticCurve}
    (A : ArithmeticDatum E) : Type := A.localization.ker

/-- [definition] The arithmetic side of the leading-coefficient formula.  This
uses the cardinality of the actual Sha kernel and actual rational torsion
subgroup; Sha finiteness is deliberately not needed to form the expression and
is separately demanded by `CurveConclusion`. -/
def arithmeticLedger {E : RationalEllipticCurve} (A : ArithmeticDatum E) : ℝ :=
  A.realPeriod * A.regulator * (A.localTamagawaProduct : ℝ) *
      (Nat.card (TateShafarevichGroup A) : ℝ) /
    ((Nat.card (RationalTorsion E) : ℝ) ^ 2)

/-! ## 3. One source theory and its model-change laws -/

/-- [definition] A source theory constructs analytic and arithmetic sections for
every rational elliptic curve and transports their receiver faces across every
admissible Weierstrass re-presentation.  The Sha equivalence retains the group,
not merely its eventual order. -/
structure SourceTheory where
  analytic : (E : RationalEllipticCurve) → AnalyticDatum E
  arithmetic : (E : RationalEllipticCurve) → ArithmeticDatum E
  analytic_modelChange : ∀ (E : RationalEllipticCurve)
      (C : WeierstrassCurve.VariableChange ℚ),
    (analytic (E.rebase C)).L = (analytic E).L
  rank_modelChange : ∀ (E : RationalEllipticCurve)
      (C : WeierstrassCurve.VariableChange ℚ),
    (arithmetic (E.rebase C)).mordellWeilRank =
      (arithmetic E).mordellWeilRank
  sha_modelChange : ∀ (E : RationalEllipticCurve)
      (C : WeierstrassCurve.VariableChange ℚ),
    TateShafarevichGroup (arithmetic (E.rebase C)) ≃+
      TateShafarevichGroup (arithmetic E)
  ledger_modelChange : ∀ (E : RationalEllipticCurve)
      (C : WeierstrassCurve.VariableChange ℚ),
    arithmeticLedger (arithmetic (E.rebase C)) =
      arithmeticLedger (arithmetic E)

/-! ## 4. The terminal receiver -/

/-- [definition] The three conjectural conclusions for one curve.  Finiteness is
asserted of the Sha kernel itself, followed by analytic-rank equality and the
full leading-coefficient ledger at that rank. -/
def CurveConclusion (T : SourceTheory) (E : RationalEllipticCurve) : Prop :=
  let D := T.analytic E
  let A := T.arithmetic E
  Finite (TateShafarevichGroup A) ∧
    analyticOrderAt D.L 1 = (A.mordellWeilRank : ℕ∞) ∧
    leadingCoefficient D.L A.mordellWeilRank =
      (arithmeticLedger A : ℂ)

/-- [definition] The repaired parameter-free repository finish line.  It first
constructs a complete source theory, so the quantifier cannot become vacuous
through absent analytic data, and then returns `CurveConclusion` for every
rational elliptic curve. -/
def BSDSourceConstructionFinishLine : Prop :=
  ∃ T : SourceTheory, ∀ E : RationalEllipticCurve, CurveConclusion T E

/-! ## 5. Exact adapter to the existing family pose -/

/-- [proved-derived] Generic terminal adapter for the exact shape used by the
current `UniversalBSD.TheRankClauseOn`: once a legacy analytic function and
rank predicate are identified with this source, `CurveConclusion` returns the
complete rank biconditional.

[open] Instantiating this theorem with the current universal definitions is a
thin import-only bridge; its legacy import closure is presently blocked
elsewhere in the 4.33 station. -/
theorem rankClauseOn_of_curveConclusion (T : SourceTheory)
    (E : RationalEllipticCurve) (hE : CurveConclusion T E)
    (legacyL : ℂ → ℂ) (legacyRankIs : ℕ → Prop)
    (hL : legacyL = (T.analytic E).L)
    (hRank : ∀ r : ℕ, legacyRankIs r ↔ RankIs E r) :
    ∀ r : ℕ, analyticOrderAt legacyL 1 = (r : ℕ∞) ↔ legacyRankIs r := by
  let A := T.arithmetic E
  have horder : analyticOrderAt legacyL 1 = (A.mordellWeilRank : ℕ∞) := by
    rw [hL]
    exact hE.2.1
  intro r
  constructor
  · intro hr
    have hcast : (A.mordellWeilRank : ℕ∞) = (r : ℕ∞) := horder.symm.trans hr
    have hnat : A.mordellWeilRank = r := by exact_mod_cast hcast
    exact (hRank r).2 ((A.rank_spec r).2 hnat.symm)
  · intro hr
    have hnat : r = A.mordellWeilRank :=
      (A.rank_spec r).1 ((hRank r).1 hr)
    rw [horder, hnat]

/-- [definition] The exact identification required before a current family
analytic datum may consume a repaired source-theory conclusion. -/
structure FamilyAnalyticIdentification (T : SourceTheory)
    (E : RationalEllipticCurve) (n : ℕ)
    (D : BirchSwinnertonDyer.LDatum n) : Prop where
  model_eq : E.model = FamilyFace.E (n : ℚ)
  L_eq : D.L = (T.analytic E).L

/-- [proved-derived] The repaired rational-point rank predicate is literally the
current congruent-family predicate after the source model is identified. -/
lemma rankIs_iff_familyRankIs (E : RationalEllipticCurve) (n r : ℕ)
    (hmodel : E.model = FamilyFace.E (n : ℚ)) :
    RankIs E r ↔ BirchSwinnertonDyer.AlgebraicRankIs n r := by
  unfold RankIs RankAtLeast IndependentModTorsion IsTorsion
    BirchSwinnertonDyer.AlgebraicRankIs
    BirchSwinnertonDyer.AlgebraicRankAtLeast
    BirchSwinnertonDyer.IndependentModTorsion
    BirchSwinnertonDyer.IsTorsion
  rw [hmodel]

/-- [proved-derived] The current congruent-number family rank receiver consumes a
repaired curve conclusion only after the family model and its existing analytic
datum are identified with the source construction. -/
theorem familyRankClause_of_curveConclusion (T : SourceTheory)
    (E : RationalEllipticCurve) (hE : CurveConclusion T E)
    (n : ℕ) (D : BirchSwinnertonDyer.LDatum n)
    (I : FamilyAnalyticIdentification T E n D) :
    BirchSwinnertonDyer.TheRankClause n D := by
  exact rankClauseOn_of_curveConclusion T E hE D.L
    (BirchSwinnertonDyer.AlgebraicRankIs n) I.L_eq
    (fun r => (rankIs_iff_familyRankIs E n r I.model_eq).symm)

/-- [conditional] A proof of the parameter-free finish line specializes to the
current family rank receiver once the selected constructed source theory is
identified with that family model and datum. -/
theorem familyRankClause_of_finishLine
    (hBSD : BSDSourceConstructionFinishLine)
    (n : ℕ) (D : BirchSwinnertonDyer.LDatum n)
    (identify : ∀ T : SourceTheory,
      ∃ E : RationalEllipticCurve,
        FamilyAnalyticIdentification T E n D) :
    BirchSwinnertonDyer.TheRankClause n D := by
  obtain ⟨T, hall⟩ := hBSD
  obtain ⟨E, I⟩ := identify T
  exact familyRankClause_of_curveConclusion T E (hall E) n D I

section Audit

#print axioms rankClauseOn_of_curveConclusion
#print axioms rankIs_iff_familyRankIs
#print axioms familyRankClause_of_curveConclusion
#print axioms familyRankClause_of_finishLine

end Audit

end Soma.Holonics.Millennium.OfficialBSDReceiver
