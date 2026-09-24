import ElementaryHolonics.Millennium.FamilyTunnellJacobiFourSquareLambert
import ElementaryHolonics.Millennium.FamilyTunnellJacobiUnitThetaReceiver

/-!
# The ambient odd theta returns the Jacobi four-square source

**[proved-derived; formal-checked]** The complete positive-unit Jacobi theta,
raised to the fourth power, reopens coefficientwise into every addressed
four-square residue shell.  At an odd address every inhabited shell lies in
the ambient odd-residue aperture, so the ambient theta coefficient is exactly
the corresponding coefficient of that fourth power.

This is the source-faithful bridge needed before a Lambert receiver may be
used.  It deliberately does not identify a projective direction modulo `p`
with an integral norm-`p` occurrence.  The remaining arithmetic obligation is
the prime coefficient of Jacobi's four-square identity:

`coeff p (unitSquareTheta 1 ^ 4) = coeff p jacobiFourSquareLambertSeries`.

The stronger unfiltered series equality suggested by those names is not the
right statement: the ambient series retains only odd norm addresses, whereas
the Lambert series also has even coefficients.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareSource

open Finset
open PowerSeries
open Soma.Holonics.Mathematics.JacobiUnitSpecialization
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaCensus
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaLift
open Soma.Holonics.Millennium.FamilyTunnellFourSquareThetaReceiver
open Soma.Holonics.Millennium.FamilyTunnellFourSquarePrimeCensus
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareLambert
open Soma.Holonics.Millennium.FamilyTunnellJacobiUnitThetaReceiver

/-- Summing the four independently addressed residue coordinates returns the
fourth power of the folded positive-unit square stream. -/
theorem sum_foldedCoordinateProduct_eq {R : Type*} [CommRing R]
    (a b c : R) :
    (∑ q : ResidueQuaternion, foldedCoordinateProduct a b c q) =
      (a + 2 * b + c) ^ 4 := by
  simp only [Fintype.sum_prod_type]
  let f : QuarterResidue → R := foldedQuarterVariable a b c
  have hsum : (∑ r : QuarterResidue, f r) = a + 2 * b + c := by
    simp [f, foldedQuarterVariable, foldQuarterResidue,
      Fin.sum_univ_four]
    ring
  change (∑ q₀, ∑ q₁, ∑ q₂, ∑ q₃,
    f q₀ * f q₁ * f q₂ * f q₃) = _
  rw [← hsum]
  simp only [pow_succ, pow_zero, one_mul, Finset.sum_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q₀ _
  apply Finset.sum_congr rfl
  intro q₁ _
  apply Finset.sum_congr rfl
  intro q₂ _
  apply Finset.sum_congr rfl
  intro q₃ _
  ring

/-- The complete positive-unit four-square theta before taking its odd
coefficient receiver. -/
def fullFourSquareTheta : PowerSeries ℤ :=
  unitSquareTheta (1 : ℤˣ) ^ 4

/-- The fourth power of the positive-unit Jacobi theta is the sum of all 256
addressed residue terms, with the `1/3` reconstruction fibre retained by each
folded term. -/
theorem fullFourSquareTheta_eq_sum_foldedResidueThetaTerm :
    fullFourSquareTheta =
      ∑ q : ResidueQuaternion, foldedResidueThetaTerm q := by
  unfold fullFourSquareTheta
  rw [unitSquareTheta_one_eq_foldedQuarterSquareTheta]
  calc
    (quarterSquareTheta 0 + 2 * quarterSquareTheta 1 +
        quarterSquareTheta 2) ^ 4 =
        ∑ q : ResidueQuaternion,
          foldedCoordinateProduct (quarterSquareTheta 0)
            (quarterSquareTheta 1) (quarterSquareTheta 2) q := by
      symm
      exact sum_foldedCoordinateProduct_eq _ _ _
    _ = ∑ q : ResidueQuaternion, foldedResidueThetaTerm q := by
      apply Finset.sum_congr rfl
      intro q _hq
      exact (foldedResidueThetaTerm_eq_coordinateProduct q).symm

/-- Every coefficient of the complete source is the sum of the exact
integral shells over all residue addresses. -/
theorem coeff_fullFourSquareTheta_eq_sum_exactShell_card (n : ℕ) :
    PowerSeries.coeff n fullFourSquareTheta =
      ∑ r : ResidueQuaternion,
        ((fourSquareResidueShell
          r.1 r.2.1 r.2.2.1 r.2.2.2 n).card : ℤ) := by
  rw [fullFourSquareTheta_eq_sum_foldedResidueThetaTerm, map_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  unfold foldedResidueThetaTerm
  rw [coeff_fourQuarterSquareTheta_eq_residueShell_card]
  exact_mod_cast foldedResidueShell_card_eq_exact r n

/-- **THE AMBIENT ODD THETA IS THE ODD COEFFICIENT FACE OF THE COMPLETE
JACOBI FOUR-SQUARE SOURCE.** -/
theorem coeff_ambientOddFourSquareTheta_eq_fullFourSquareTheta_of_odd
    {n : ℕ} (hn : Odd n) :
    PowerSeries.coeff n ambientOddFourSquareTheta =
      PowerSeries.coeff n fullFourSquareTheta := by
  rw [coeff_ambientOddFourSquareTheta_eq_sum_exactShell_card,
    coeff_fullFourSquareTheta_eq_sum_exactShell_card]
  rw [ambientOddResidues, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hodd : residueNormOdd r
  · simp [hodd]
  · rw [if_neg hodd]
    symm
    have hcard :
        (fourSquareResidueShell
          r.1 r.2.1 r.2.2.1 r.2.2.2 n).card = 0 := by
      apply Finset.card_eq_zero.mpr
      by_contra hne
      rcases Finset.nonempty_iff_ne_empty.mpr hne with ⟨q, hq⟩
      exact hodd (residueNormOdd_of_exactShell hn hq)
    exact_mod_cast hcard

/-- The exact remaining prime-coefficient source identity is sufficient to
close the integral Hamilton shell count. -/
theorem ambientHamiltonPopulation_card_prime_of_jacobi_source
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsource :
      PowerSeries.coeff p fullFourSquareTheta =
        PowerSeries.coeff p jacobiFourSquareLambertSeries) :
    ((ambientHamiltonPopulation p).card : ℤ) =
      8 * ((p : ℤ) + 1) := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  calc
    ((ambientHamiltonPopulation p).card : ℤ) =
        PowerSeries.coeff p ambientOddFourSquareTheta :=
      (coeff_ambientOddFourSquareTheta_eq_ambientHamiltonPopulation_card
        hp.pos hpodd).symm
    _ = PowerSeries.coeff p fullFourSquareTheta :=
      coeff_ambientOddFourSquareTheta_eq_fullFourSquareTheta_of_odd hpodd
    _ = PowerSeries.coeff p jacobiFourSquareLambertSeries := hsource
    _ = 8 * ((p : ℤ) + 1) :=
      coeff_jacobiFourSquareLambertSeries_prime hp hp2

#print axioms sum_foldedCoordinateProduct_eq
#print axioms fullFourSquareTheta_eq_sum_foldedResidueThetaTerm
#print axioms coeff_fullFourSquareTheta_eq_sum_exactShell_card
#print axioms coeff_ambientOddFourSquareTheta_eq_fullFourSquareTheta_of_odd
#print axioms ambientHamiltonPopulation_card_prime_of_jacobi_source

end Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareSource
