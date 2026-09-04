import ElementaryHolonics.Millennium.FamilyCentralRatio
import ElementaryHolonics.Millennium.LatticeCount

/-!
# FamilyWaldspurgerGate: the canonical finite count and its exact remaining defect

`FamilyCentralRatio` reduced the positive-sign central-value problem to an equality
between an absolutely convergent Gaussian lattice sum and the square of an integer.
This file fixes the remaining sign convention for that integer.  It is the signed ternary
count from `LatticeCount`, evaluated on the proved-tight box and divided by the four
element reflection orbit.  If `A_p` counts the solutions with `32z²` and `B_p` counts
the solutions with `8z²`, then the chosen `(-1)^z` orientation is `2A_p - B_p`.
Replacing it by the opposite convention negates the branch count but does not change
the square occurring in the central ratio.

The output is an exact scalar defect.  Its vanishing implies the established BSD rank
clause on every prime `p ≡ 3 (mod 8)`.  No Waldspurger or Tunnell theorem is assumed:
proving that this defect vanishes is precisely the still-open analytic/arithmetic port.
-/

namespace Soma.Holonics.Millennium.FamilyWaldspurgerGate

open Complex
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.BirchSwinnertonDyer
open Soma.Holonics.Millennium.FamilyCentralRatio
open Soma.Holonics.Millennium.LatticeCount

/-- The complete signed ternary census in the `2A_p - B_p` orientation, evaluated on
the smallest box proved to contain every solution. -/
def canonicalSignedTernaryCount (p : ℕ) : ℤ :=
  SFr p (Nat.sqrt p)

/-- The orbit-normalized finite count in the chosen signed orientation.  Its square is
the orientation-independent quantity entering the central-ratio defect below. -/
def canonicalBranchCount (p : ℕ) : ℤ :=
  canonicalSignedTernaryCount p / 4

/-- The tight reducible census is exactly the structural census on the modulus-sized
box used by the family parity theorem. -/
theorem canonicalSignedTernaryCount_eq_structural (p : ℕ) :
    canonicalSignedTernaryCount p = SF p p := by
  have hsol : SolFr p (Nat.sqrt p) = SolFr p p :=
    theTightBoxSuffices (p := p) le_rfl (Nat.sqrt_le_self p)
  calc
    canonicalSignedTernaryCount p = SFr p (Nat.sqrt p) := rfl
    _ = SFr p p := by simp only [SFr, hsol]
    _ = SF p p := theReducibleCountIsTheStructuralCount p p

/-- On the three-mod-eight branch the canonical signed census is four times its
orbit-normalized count. -/
theorem canonicalSignedTernaryCount_eq_four_mul_count
    {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 3) :
    canonicalSignedTernaryCount p = 4 * canonicalBranchCount p := by
  have hodd : Odd p := ⟨p / 2, by omega⟩
  have hdStructural : (4 : ℤ) ∣ SF p p :=
    theSignOrbitsHaveSizeDivisibleByFour (Fact.out : p.Prime) hodd p
  have hd : (4 : ℤ) ∣ canonicalSignedTernaryCount p := by
    rw [canonicalSignedTernaryCount_eq_structural]
    exact hdStructural
  unfold canonicalBranchCount
  exact (Int.ediv_mul_cancel hd).symm.trans (mul_comm _ _)

/-- The canonical branch count is odd; nonvanishing is an orbit theorem, not an
analytic estimate. -/
theorem canonicalBranchCount_odd
    {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 3) :
    Odd (canonicalBranchCount p) := by
  obtain ⟨k, hk⟩ :=
    theCountIsOddOnTheThreeModEightBranch (Fact.out : p.Prime) hp8 (le_refl p)
  have hstruct := canonicalSignedTernaryCount_eq_structural p
  have hfour := canonicalSignedTernaryCount_eq_four_mul_count hp8
  refine ⟨k, ?_⟩
  omega

/-- The exact complex scalar left by the Waldspurger--Tunnell comparison after all
normalizations and the finite count have been fixed. -/
noncomputable def waldspurgerTunnellDefect (p : ℕ) [Fact p.Prime] : ℂ :=
  (4 : ℂ) * ((centralGaussianSum p : ℝ) : ℂ) -
    centralArchimedeanFactor p *
      ((((canonicalBranchCount p) ^ 2 : ℤ) : ℂ) *
        ((realPeriod p : ℝ) : ℂ))

/-- Vanishing of the named defect is exactly the canonical central-ratio identity. -/
theorem centralRatio_iff_waldspurgerTunnellDefect_eq_zero
    {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 3) :
    ((2 : ℂ) *
        (FamilyWitness.theWitnessAtEveryOddPrime p (by omega)).L 1
      = ((((canonicalBranchCount p) ^ 2 : ℤ) : ℂ) *
          ((realPeriod p : ℝ) : ℂ)))
      ↔ waldspurgerTunnellDefect p = 0 := by
  rw [centralRatio_iff_explicitLatticeIdentity hp8 (canonicalBranchCount p)]
  exact sub_eq_zero.symm

/-- A zero defect supplies the complete already-defined lattice-count datum. -/
def latticeCountDatumOfWaldspurgerTunnellDefectEqZero
    {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 3)
    (hzero : waldspurgerTunnellDefect p = 0) :
    FamilyRatio.LatticeCountDatum p
      (FamilyWitness.theWitnessAtEveryOddPrime p (by omega)) := by
  refine
    { count := canonicalBranchCount p
      count_odd := canonicalBranchCount_odd hp8
      period_ne_null := FamilyPeriod.theRealPeriodIsNotNull (Fact.out : p.Prime).pos
      central_ratio := ?_ }
  exact (centralRatio_iff_waldspurgerTunnellDefect_eq_zero hp8).mpr hzero

/-- The remaining scalar equality is sufficient for the BSD rank clause on the
whole positive-root-number prime branch. -/
theorem rankClause_of_waldspurgerTunnellDefect_eq_zero
    {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 3)
    (hzero : waldspurgerTunnellDefect p = 0) :
    TheRankClause p (FamilyWitness.theWitnessAtEveryOddPrime p (by omega)) :=
  FamilyRatio.theRankClauseHoldsOnTheThreeModEightBranch hp8
    (latticeCountDatumOfWaldspurgerTunnellDefectEqZero hp8 hzero)

set_option maxRecDepth 8000 in
example : canonicalBranchCount 3 = 1 := by
  native_decide

set_option maxRecDepth 40000 in
example : canonicalBranchCount 11 = -1 := by
  native_decide

set_option maxRecDepth 200000 in
example : canonicalBranchCount 43 = 3 := by
  native_decide

end Soma.Holonics.Millennium.FamilyWaldspurgerGate
