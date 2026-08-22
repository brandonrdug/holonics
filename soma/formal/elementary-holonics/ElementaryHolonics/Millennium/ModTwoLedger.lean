import ElementaryHolonics.Millennium.FaceImageFive
import ElementaryHolonics.Millennium.ThetaCensus
import Mathlib.Tactic

/-!
# ModTwoLedger: the mod-two Birch–Swinnerton-Dyer programme's standing ledger

The goal ratified 2026-08-22 poses three components: the governance matrix (Selmer rank
as 𝔽₂ corank of a quadratic-character matrix), completed descents as Ш[2]-vanishing
certificates, and parity of the descent rank against the analytic sign.  This file is
the **ledger that joins what stands**: the first complete parity instance (five), the
agreement instance at one, and the character data at the two certificate twists that
the owed governance matrix must reproduce.

**What this file does not do**: it does not define the governance matrix — a matrix
family stated only at two instances would be a declaration table, which the grading
rule forbids; the matrix becomes an instrument when its corank law is proved
family-wise, and these entries are its adjudication fixtures, exactly as
`desktop_receiver` adjudicates a card against an independent computation.

Every `theorem` is discharged and none depends on `sorryAx`.  Nothing about the
Birch–Swinnerton-Dyer conjecture is claimed; the Tunnell/Waldspurger/Coates–Wiles and
Monsky readings are cited classical chains, `interpretation` throughout.
-/

namespace Soma.Holonics.Millennium.ModTwoLedger

/-- **THE PARITY INSTANCE AT FIVE, BOTH SIDES COMPLETE**: the theta censuses vanish
(the analytic face of an odd sign) **and** the descent image is exactly the realized
eight — four torsion classes times one direction, an odd descent exponent.  The first
instance of the programme's parity component where the analytic face and the descent
face are both finished computations in this tree. -/
theorem theParityInstanceAtFiveHasBothSidesComplete :
    ((∀ x y z : ℤ, 2 * x ^ 2 + y ^ 2 + 32 * z ^ 2 ≠ 5) ∧
     (∀ x y z : ℤ, 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2 ≠ 5)) ∧
    (∀ P : RankOne.E5.Point, ∃ d₁ d₂ : ℚ, FaceImageFive.RealizedFive d₁ d₂ ∧
      Descent.SqCls (RankOne.slotOne P) d₁ ∧
      Descent.SqCls (RankOne.slotTwo P) d₂) := by
  obtain ⟨h1, h2, -⟩ := ThetaCensus.theVanishingCensusMeetsTheInfiniteChainAtFive
  exact ⟨⟨h1, h2⟩, FaceImageFive.theFaceImageAtFiveIsTheRealizedEight⟩

/-- **THE AGREEMENT INSTANCE AT ONE**: the census refuses the vanishing condition (the
analytic face of a nonvanishing central value) and the realized side is empty — the
even-parity sibling, both faces already theorems. -/
theorem theParityInstanceAtOneStands :
    (ThetaCensus.thickSolutions.card ≠ ThetaCensus.thinSolutions.card / 2) ∧
    (∀ a b c : ℚ, a * b = 2 → a ^ 2 + b ^ 2 = c ^ 2 → False) :=
  ThetaCensus.theAnalyticAndRealizedSidesAgreeAtOne

/-- **THE CHARACTER DATA AT THE TWO CERTIFICATES**: the residue classes and
quadratic-residue facts that the owed governance matrix must consume — at thirty-four
(`= 2·17`): seventeen sits in the split class mod eight and two is a square mod
seventeen; at five: the prime sits in the class mod eight whose classical Selmer rank
is one.  Kernel-decided; these are the matrix's inputs at its two adjudication
fixtures, not the matrix. -/
theorem theCharacterDataAtTheTwoCertificates :
    (17 % 8 = 1 ∧ IsSquare (2 : ZMod 17)) ∧ (5 % 8 = 5 ∧ ¬ IsSquare (2 : ZMod 5)) := by
  refine ⟨⟨by norm_num, ⟨6, by decide⟩⟩, ⟨by norm_num, ?_⟩⟩
  rintro ⟨r, hr⟩
  revert hr
  revert r
  decide

end Soma.Holonics.Millennium.ModTwoLedger
