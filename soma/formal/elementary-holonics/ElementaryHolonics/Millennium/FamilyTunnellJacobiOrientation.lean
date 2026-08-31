import ElementaryHolonics.Millennium.FamilyTunnellHeckeThetaFactor

/-!
# The quarter-residue current is an oriented Jacobi population

The coefficient called `weightedQuarterSquareTheta 1` is not an anonymous
integer sum.  Every contributing coordinate has the unique form `4 * t + 1`.
This file retains that orientation parameter as an occurrence, proves that no
source is lost or duplicated by the regrading, and then returns equality of the
whole formal power series.

This is the exact occurrence-level input required by the quarter-character
specialization of the Jacobi triple product.  No analytic convergence,
rounding, or modular-form classification enters here.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiOrientation

open Finset
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaLift
open Soma.Holonics.Millennium.FamilyTunnellHeckeThetaFactor

/-- A residue-one integer is exactly one addressed orientation parameter. -/
def residueOneEquivInt : {x : ℤ // x % 4 = 1} ≃ ℤ where
  toFun x := x.1 / 4
  invFun t := ⟨4 * t + 1, by omega⟩
  left_inv x := by
    apply Subtype.ext
    change 4 * (x.1 / 4) + 1 = x.1
    have hdivision : x.1 % 4 + 4 * (x.1 / 4) = x.1 :=
      Int.emod_add_mul_ediv x.1 4
    omega
  right_inv t := by
    dsimp
    omega

theorem residueOne_reconstruct (x : {x : ℤ // x % 4 = 1}) :
    4 * residueOneEquivInt x + 1 = x.1 := by
  have h := residueOneEquivInt.symm_apply_apply x
  exact congrArg Subtype.val h

theorem intCast_zmod_four_eq_one_iff_emod (x : ℤ) :
    (x : ZMod 4) = 1 ↔ x % 4 = 1 := by
  have h0 : (0 : ℤ) ≤ 1 := by omega
  have h4 : (1 : ℤ) < 4 := by omega
  simpa [Int.emod_eq_of_lt h0 h4] using
    (ZMod.intCast_eq_intCast_iff' x (1 : ℤ) 4)

/-- The finite orientation population over the square coefficient `n`.  It is
defined as the image of the complete quarter-square population, so finiteness
does not impose an additional analytic cutoff. -/
def jacobiOrientationPopulation (n : ℕ) : Finset ℤ :=
  (quarterSquarePopulation 1 n).image fun x => x / 4

private theorem quarterSquareOne_reconstruct {n : ℕ} {x : ℤ}
    (hx : x ∈ quarterSquarePopulation 1 n) :
    4 * (x / 4) + 1 = x := by
  have hxResidueZMod := (Finset.mem_filter.mp hx).2.2
  have hxResidue : x % 4 = 1 :=
    (intCast_zmod_four_eq_one_iff_emod x).mp (by simpa using hxResidueZMod)
  have hdivision : x % 4 + 4 * (x / 4) = x :=
    Int.emod_add_mul_ediv x 4
  omega

private theorem orientationMap_injective_on (n : ℕ) {x y : ℤ}
    (hx : x ∈ quarterSquarePopulation 1 n)
    (hy : y ∈ quarterSquarePopulation 1 n)
    (hxy : x / 4 = y / 4) : x = y := by
  have hxResidueZMod := (Finset.mem_filter.mp hx).2.2
  have hyResidueZMod := (Finset.mem_filter.mp hy).2.2
  have hxResidue : x % 4 = 1 :=
    (intCast_zmod_four_eq_one_iff_emod x).mp (by simpa using hxResidueZMod)
  have hyResidue : y % 4 = 1 :=
    (intCast_zmod_four_eq_one_iff_emod y).mp (by simpa using hyResidueZMod)
  have hsubtype : (⟨x, hxResidue⟩ : {z : ℤ // z % 4 = 1}) =
      ⟨y, hyResidue⟩ :=
    residueOneEquivInt.injective hxy
  exact congrArg Subtype.val hsubtype

/-- Complete occurrence equivalence: residue-one square coordinates and their
Jacobi orientation parameters are the same population in two charts. -/
def quarterSquareOneEquivJacobiOrientation (n : ℕ) :
    {x // x ∈ quarterSquarePopulation 1 n} ≃
      {t // t ∈ jacobiOrientationPopulation n} :=
  Equiv.ofBijective
    (fun x => ⟨x.1 / 4, Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩)
    (by
      constructor
      · intro x y hxy
        apply Subtype.ext
        apply orientationMap_injective_on n x.2 y.2
        exact congrArg Subtype.val hxy
      · intro t
        rcases Finset.mem_image.mp t.2 with ⟨x, hx, hxt⟩
        refine ⟨⟨x, hx⟩, ?_⟩
        apply Subtype.ext
        exact hxt)

/-- The oriented lacunary Jacobi stream.  Its coefficient retains the signed
coordinate `4*t+1`, rather than collapsing the population to its cardinality. -/
def jacobiOrientedTheta : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    ∑ t ∈ jacobiOrientationPopulation n, (4 * t + 1)

@[simp] theorem coeff_jacobiOrientedTheta (n : ℕ) :
    PowerSeries.coeff n jacobiOrientedTheta =
      ∑ t ∈ jacobiOrientationPopulation n, (4 * t + 1) := by
  simp [jacobiOrientedTheta]

theorem sum_jacobiOrientation_eq_weightedQuarterSquare (n : ℕ) :
    (∑ t ∈ jacobiOrientationPopulation n, (4 * t + 1)) =
      ∑ x ∈ quarterSquarePopulation 1 n, x := by
  rw [jacobiOrientationPopulation, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    exact quarterSquareOne_reconstruct hx
  · intro x hx y hy hxy
    exact orientationMap_injective_on n hx hy hxy

/-- **THE WEIGHTED QUARTER-SQUARE STREAM IS THE ORIENTED JACOBI STREAM.** -/
theorem jacobiOrientedTheta_eq_weightedQuarterSquareTheta :
    jacobiOrientedTheta = weightedQuarterSquareTheta 1 := by
  apply PowerSeries.ext
  intro n
  simp [sum_jacobiOrientation_eq_weightedQuarterSquare]

#print axioms residueOneEquivInt
#print axioms quarterSquareOneEquivJacobiOrientation
#print axioms jacobiOrientedTheta_eq_weightedQuarterSquareTheta

end Soma.Holonics.Millennium.FamilyTunnellJacobiOrientation
