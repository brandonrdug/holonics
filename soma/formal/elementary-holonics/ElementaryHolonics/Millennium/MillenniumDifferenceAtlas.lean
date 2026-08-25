import ElementaryHolonics.Foundation.MeasuredDifferenceReceiver
import ElementaryHolonics.Millennium.BirchSwinnertonDyer
import ElementaryHolonics.Millennium.HodgeConjecture
import ElementaryHolonics.Millennium.MassGap
import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeHaarReceiver
import ElementaryHolonics.Millennium.Seam

/-!
# Difference residuals across the Millennium formal surfaces

**[proved-derived]** This file poses the measured-difference correction against the existing open
problem objects without pretending that one scalar solves them.

* The Riemann seam is the zero fibre of a real-part difference.
* A finite BSD rank comparison is the zero fibre of an integer difference, while the ledger is the
  zero fibre of a complex central-value difference.
* A Hodge class returns a generally non-scalar quotient difference modulo the algebraic span.
* A Yang--Mills gap is a positive lower bound on energy differences from the vacuum.
* The current Navier--Stokes coefficient obligation is a nonpositive excess difference on every
  coordinate face, scale, and Hodge entry.

These are exact reformulations and compositions of the named owners.  Their unresolved fibres are
unchanged: no open conjecture is proved by changing its receiver chart.
-/

noncomputable section

namespace Soma.Holonics.Millennium.MillenniumDifferenceAtlas

open Soma.Holonics.Foundation.MeasuredDifferenceReceiver

/-! ## Riemann: the seam is a zero-difference fibre -/

/-- Difference between the received real part and the reflection-fixed half. -/
def criticalSeamDifference (s : ℂ) : ℝ := s.re - 1 / 2

/-- The critical seam is exactly the zero fibre of that returned difference. -/
theorem criticalSeamDifference_eq_zero_iff_mem (s : ℂ) :
    criticalSeamDifference s = 0 ↔
      s ∈ Soma.Holonics.Millennium.Seam.theSelfConjugateSeam := by
  rw [criticalSeamDifference, sub_eq_zero]
  exact (Soma.Holonics.Millennium.Seam.mem_seam_iff s).symm

/-! ## BSD: rank and ledger comparisons retain their distinct carriers -/

open Soma.Holonics.Millennium.BirchSwinnertonDyer

/-- Signed difference after an analytic rank has been proved finite and represented in `ℕ`. -/
def finiteRankDifference (analyticCandidate algebraicCandidate : ℕ) : ℤ :=
  (analyticCandidate : ℤ) - (algebraicCandidate : ℤ)

theorem finiteRankDifference_eq_zero_iff
    (analyticCandidate algebraicCandidate : ℕ) :
    finiteRankDifference analyticCandidate algebraicCandidate = 0 ↔
      analyticCandidate = algebraicCandidate := by
  rw [finiteRankDifference, sub_eq_zero]
  exact Int.ofNat_inj

/-- Given an actual finite analytic-rank witness, the BSD rank clause is exactly the family of
zero signed-difference tests against every algebraic-rank candidate. -/
theorem rankClause_iff_zero_finiteRankDifferences {n analyticCandidate : ℕ}
    (W : LDatum n) (hfinite : analyticRank W = (analyticCandidate : ℕ∞)) :
    TheRankClause n W ↔
      ∀ algebraicCandidate : ℕ,
        finiteRankDifference analyticCandidate algebraicCandidate = 0 ↔
          AlgebraicRankIs n algebraicCandidate := by
  unfold TheRankClause
  simp only [hfinite, finiteRankDifference_eq_zero_iff]
  norm_cast

/-- Complex difference between the returned central value and one proposed BSD ledger value. -/
def bsdLedgerDifference {n : ℕ} (W : LDatum n)
    (sha tamagawa torsion : ℕ) : ℂ :=
  W.L 1 -
    (((sha * tamagawa : ℕ) : ℂ) / ((torsion : ℂ) ^ 2)) * (realPeriod n : ℂ)

theorem bsdLedgerDifference_eq_zero_iff {n : ℕ} (W : LDatum n)
    (sha tamagawa torsion : ℕ) :
    bsdLedgerDifference W sha tamagawa torsion = 0 ↔
      W.L 1 =
        (((sha * tamagawa : ℕ) : ℂ) / ((torsion : ℂ) ^ 2)) * (realPeriod n : ℂ) := by
  exact sub_eq_zero

/-- The rank-zero ledger clause is exactly the existence of a positive square obstruction order
whose complex ledger difference vanishes. -/
theorem ledgerClause_iff_zero_bsdLedgerDifference {n : ℕ} (W : LDatum n)
    (tamagawa torsion : ℕ) :
    TheLedgerClause n W tamagawa torsion ↔
      AlgebraicRankIs n 0 →
        ∃ sha : ℕ, 0 < sha ∧ IsSquare sha ∧
          bsdLedgerDifference W sha tamagawa torsion = 0 := by
  unfold TheLedgerClause
  simp only [bsdLedgerDifference_eq_zero_iff]

/-! ## Hodge: the difference lives in the quotient, not necessarily in a scalar chart -/

open Soma.Holonics.Millennium.HodgeConjecture

/-- The class remaining after quotienting by the rational algebraic cycle span. -/
def hodgeQuotientDifference (D : Datum) (cohomologyClass : D.Cohomology) :
    D.Cohomology ⧸ D.algebraicSpan :=
  Submodule.Quotient.mk cohomologyClass

/-- The quotient difference vanishes exactly when the class is already algebraic. -/
theorem hodgeQuotientDifference_eq_zero_iff (D : Datum)
    (cohomologyClass : D.Cohomology) :
    hodgeQuotientDifference D cohomologyClass = 0 ↔
      cohomologyClass ∈ D.algebraicSpan := by
  exact Submodule.Quotient.mk_eq_zero D.algebraicSpan

/-- An open Hodge class is precisely an admitted rational Hodge class with nonzero quotient
difference.  No scalar condensation is introduced. -/
theorem mem_openHodgeClasses_iff_nonzero_quotientDifference
    (Official : Datum → Prop) (D : Datum) (cohomologyClass : D.Cohomology) :
    (⟨D, cohomologyClass⟩ : Σ D : Datum, D.Cohomology) ∈
        OpenHodgeClasses Official ↔
      Official D ∧ cohomologyClass ∈ D.rationalHodgeClasses ∧
        hodgeQuotientDifference D cohomologyClass ≠ 0 := by
  simp only [OpenHodgeClasses, Set.mem_setOf_eq]
  rw [ne_eq, hodgeQuotientDifference_eq_zero_iff]

/-! ## Yang--Mills: mass is a lower bound on differences from the vacuum -/

open Soma.Holonics.Millennium.MillenniumCoupling
open Soma.Holonics.Millennium.MassGap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Difference of quadratic energy readings between two addressed states. -/
def energyDifference (F : ReceiverForm V) (source target : V) : ℝ :=
  F.B target target - F.B source source

/-- A zero-energy vacuum makes its outgoing energy difference equal the target reading. -/
theorem energyDifference_from_vacuum {F : ReceiverForm V} {vacuum : V}
    (hvacuum : F.B vacuum vacuum = 0) (target : V) :
    energyDifference F vacuum target = F.B target target := by
  rw [energyDifference, hvacuum, sub_zero]

/-- The coercive gap is exactly one positive lower bound on all unit-sphere energy differences
from the zero vacuum. -/
theorem gap_iff_positive_unit_energyDifferences (F : ReceiverForm V) :
    F.IsCoercive ↔
      ∃ gap : ℝ, 0 < gap ∧
        ∀ state ∈ Metric.sphere (0 : V) 1,
          gap ≤ energyDifference F 0 state := by
  rw [theGapIsThePositivityOfTheSphereInfimum]
  constructor
  · rintro ⟨gap, hgap, hlower⟩
    refine ⟨gap, hgap, ?_⟩
    intro state hstate
    have := hlower (F.B state state) ⟨state, hstate, rfl⟩
    simpa [energyDifference, ReceiverForm.B] using this
  · rintro ⟨gap, hgap, hlower⟩
    refine ⟨gap, hgap, ?_⟩
    rintro reading ⟨state, hstate, rfl⟩
    simpa [energyDifference, ReceiverForm.B] using hlower state hstate

/-! ## Navier--Stokes: the current frontier is an eight-face excess difference -/

open Soma.Holonics.CoordinateSubsetReceiver
open Soma.Holonics.CoordinateHaarReceiver
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeHaarReceiver
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeSubsetReceivers
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors

/-- Excess of one exact subset mass above the scale law presented to its receiver. -/
def dyadicHodgeSubsetMassExcess
    (face : CoordinateFace 3) (scale : ℕ) (component coordinate input : Fin 3)
    (constant : ℝ) : ℝ :=
  dyadicHodgeSubsetMass face scale component coordinate input -
    constant * coordinateSubsetScale (dyadicRadius scale : ℝ) face

/-- The named coefficient return is exactly nonnegativity of its constant plus nonpositivity of
the returned excess difference on all eight coordinate faces. -/
theorem dyadicHodgeSubsetMassReturn_iff_nonpositive_excess
    (scale : ℕ) (component coordinate input : Fin 3) (constant : ℝ) :
    DyadicHodgeSubsetMassReturn scale component coordinate input constant ↔
      0 ≤ constant ∧ ∀ face : CoordinateFace 3,
        dyadicHodgeSubsetMassExcess face scale component coordinate input constant ≤ 0 := by
  unfold DyadicHodgeSubsetMassReturn dyadicHodgeSubsetMassExcess
  simp only [sub_nonpos]

/-- The still-open uniform return is exactly the same excess law across all large scales and all
twenty-seven Hodge entries. -/
theorem uniformLargeScaleSubsetMassReturn_iff_nonpositive_excess
    (constant : ℝ) :
    UniformLargeScaleDyadicHodgeSubsetMassReturn constant ↔
      0 ≤ constant ∧ ∀ scale : ℕ, 3 ≤ scale →
        ∀ component coordinate input : Fin 3,
          ∀ face : CoordinateFace 3,
            dyadicHodgeSubsetMassExcess face scale component coordinate input constant ≤ 0 := by
  unfold UniformLargeScaleDyadicHodgeSubsetMassReturn
  constructor
  · rintro ⟨hconstant, hreturn⟩
    refine ⟨hconstant, ?_⟩
    intro scale hscale component coordinate input face
    exact (dyadicHodgeSubsetMassReturn_iff_nonpositive_excess
      scale component coordinate input constant).mp
        (hreturn scale hscale component coordinate input) |>.2 face
  · rintro ⟨hconstant, hexcess⟩
    refine ⟨hconstant, ?_⟩
    intro scale hscale component coordinate input
    exact (dyadicHodgeSubsetMassReturn_iff_nonpositive_excess
      scale component coordinate input constant).mpr
        ⟨hconstant, hexcess scale hscale component coordinate input⟩

section Audit

#print axioms criticalSeamDifference_eq_zero_iff_mem
#print axioms rankClause_iff_zero_finiteRankDifferences
#print axioms ledgerClause_iff_zero_bsdLedgerDifference
#print axioms hodgeQuotientDifference_eq_zero_iff
#print axioms mem_openHodgeClasses_iff_nonzero_quotientDifference
#print axioms gap_iff_positive_unit_energyDifferences
#print axioms dyadicHodgeSubsetMassReturn_iff_nonpositive_excess
#print axioms uniformLargeScaleSubsetMassReturn_iff_nonpositive_excess

end Audit

end Soma.Holonics.Millennium.MillenniumDifferenceAtlas
