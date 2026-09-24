import ElementaryHolonics.Millennium.FamilyTunnellHopfImprimitiveCensus
import ElementaryHolonics.Millennium.FamilyTunnellJacobiGaussFactor
import ElementaryHolonics.Millennium.FamilyTunnellJacobiFourSquareSource
import ElementaryHolonics.Millennium.FamilyTunnellCubicResidueCensus

/-!
# The two theta source laws close the odd-prime Brandt census

**[proved-derived]** The quaternionic Hopf passage has already reconstructed every primitive
first-Brandt point with exactly four phase sources, and its imprimitive boundary has already been
identified with two Gaussian prime shells.  This file performs the remaining exact gluing algebra.

Only two source identities enter:

* the surviving Hopf theta current is eight copies of the Hecke coefficient stream;
* the complete integral norm-`p` Hamilton shell has `8(p+1)` occurrences.

From them the theta difference, complete source decomposition, four-phase reconstruction, and
Gaussian boundary census force the primitive Brandt population formula.  The Brandt eigen-defect
and the equivalent cubic-population defect then vanish.  No estimate, asymptotic passage, or
population identification is hidden in the proof.

The hypotheses are intentionally retained until their independent Jacobi product passages are
proved.  Consequently this file is an exact composition theorem and a firing obstruction: any
purported odd-prime closure must supply both named source laws (or an equally strong theorem), not
merely the already checked projective or Hopf fibre counts.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellPrimeThetaBalance

open PowerSeries
open Soma.Holonics.Millennium.HeckeTheta
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaCensus
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaLift
open Soma.Holonics.Millennium.FamilyTunnellHeckeThetaFactor
open Soma.Holonics.Millennium.FamilyTunnellHopfSourceCensus
open Soma.Holonics.Millennium.FamilyTunnellFourSquareThetaReceiver
open Soma.Holonics.Millennium.FamilyTunnellFourSquarePrimeCensus
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareLambert
open Soma.Holonics.Millennium.FamilyTunnellJacobiGaussFactor
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareSource
open Soma.Holonics.Millennium.FamilyTunnellHopfImprimitiveCensus
open Soma.Holonics.Millennium.FamilyTunnellPrimeSquareCensus
open Soma.Holonics.Millennium.FamilyTunnellBrandtPrimeResidual
open Soma.Holonics.Millennium.FamilyTunnellCubicResidueCensus

variable {p : ℕ} [Fact p.Prime]

/-- The exact coefficient balance before the primitive/imprimitive source partition. -/
theorem completeHopfSource_balance
    (hp2 : p ≠ 2)
    (hopfCurrentLaw : hopfHeckeThetaCurrent = 8 * heckeCoefficientSeries) :
    2 * ((firstHopfSourcePopulation p).card : ℤ) -
        ((ambientHamiltonPopulation p).card : ℤ) =
      8 * heckeCoeff p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hseries :
      2 * hopfResidueTheta - ambientOddFourSquareTheta =
        8 * heckeCoefficientSeries := by
    rw [hopfResidueTheta_difference, hopfCurrentLaw]
  have hcoefficient := congrArg (PowerSeries.coeff p) hseries
  have height : (8 : PowerSeries ℤ) = PowerSeries.C 8 := by norm_num
  rw [height, PowerSeries.coeff_C_mul] at hcoefficient
  simpa [two_mul, PowerSeries.coeff_C_mul,
    coeff_hopfResidueTheta_eq_firstHopfSourcePopulation_card hp2,
    coeff_ambientOddFourSquareTheta_eq_ambientHamiltonPopulation_card hp hpodd,
    coeff_heckeCoefficientSeries] using hcoefficient

/-- The completed positive-Jacobi/Gauss passage removes the Hopf-current hypothesis from the
prime source balance. -/
theorem completeHopfSource_balance_of_gauss (hp2 : p ≠ 2) :
    2 * ((firstHopfSourcePopulation p).card : ℤ) -
        ((ambientHamiltonPopulation p).card : ℤ) =
      8 * heckeCoeff p := by
  exact completeHopfSource_balance hp2
    hopfHeckeThetaCurrent_eq_eight_mul_heckeCoefficientSeries

/-- **THE TWO THETA SOURCE LAWS FORCE THE PRIMITIVE BRANDT CENSUS.** -/
theorem primitiveFirstPrimeSquarePopulation_card_of_theta_balances
    (hp2 : p ≠ 2)
    (hopfCurrentLaw : hopfHeckeThetaCurrent = 8 * heckeCoefficientSeries)
    (ambientFourSquareLaw :
      ((ambientHamiltonPopulation p).card : ℤ) = 8 * ((p : ℤ) + 1)) :
    ((primitiveFirstPrimeSquarePopulation (p := p)).card : ℤ) =
      (p : ℤ) + 1 + heckeCoeff p -
        2 * (quadraticChar (ZMod p) (-1) + 1) := by
  have hsource := completeHopfSource_balance hp2 hopfCurrentLaw
  have hpartitionNat :=
    firstHopfSourcePopulation_card_eq_primitive_add_imprimitive (p := p)
  have hpartition :
      ((firstHopfSourcePopulation p).card : ℤ) =
        ((primitiveFirstHopfSourcePopulation p).card : ℤ) +
          ((imprimitiveFirstHopfSourcePopulation (p := p)).card : ℤ) := by
    exact_mod_cast hpartitionNat
  have hprimitiveNat := primitiveHopfSourcePopulation_card_of_reconstruction
    hp2 (hopfReconstructionComplete hp2)
  have hprimitive :
      ((primitiveFirstHopfSourcePopulation p).card : ℤ) =
        4 * ((primitiveFirstPrimeSquarePopulation (p := p)).card : ℤ) := by
    exact_mod_cast hprimitiveNat
  have himprimitive := imprimitiveFirstHopfSourcePopulation_card_character
    (p := p) hp2
  rw [hpartition, hprimitive, himprimitive, ambientFourSquareLaw] at hsource
  linarith

/-- The same two source laws close the signed Brandt eigenvalue return. -/
theorem brandtPrimeSignedCensus_eq_heckeCoeff_of_theta_balances
    (hp2 : p ≠ 2)
    (hopfCurrentLaw : hopfHeckeThetaCurrent = 8 * heckeCoefficientSeries)
    (ambientFourSquareLaw :
      ((ambientHamiltonPopulation p).card : ℤ) = 8 * ((p : ℤ) + 1)) :
    brandtPrimeSignedCensus (p := p) = heckeCoeff p := by
  apply (brandtPrimeSignedCensus_eq_heckeCoeff_iff (p := p) hp2).mpr
  exact primitiveFirstPrimeSquarePopulation_card_of_theta_balances
    hp2 hopfCurrentLaw ambientFourSquareLaw

/-- The retained Brandt eigen-defect vanishes once the two source laws are inhabited. -/
theorem brandtPrimeEigenDefect_eq_zero_of_theta_balances
    (hp2 : p ≠ 2)
    (hopfCurrentLaw : hopfHeckeThetaCurrent = 8 * heckeCoefficientSeries)
    (ambientFourSquareLaw :
      ((ambientHamiltonPopulation p).card : ℤ) = 8 * ((p : ℤ) + 1)) :
    brandtPrimeEigenDefect (p := p) = 0 := by
  unfold brandtPrimeEigenDefect
  rw [brandtPrimeSignedCensus_eq_heckeCoeff_of_theta_balances
    hp2 hopfCurrentLaw ambientFourSquareLaw]
  ring

/-- The equivalent integral-sphere/cubic-nonresidue census is therefore also forced. -/
theorem primitive_cubic_census_of_theta_balances
    (hp2 : p ≠ 2)
    (hopfCurrentLaw : hopfHeckeThetaCurrent = 8 * heckeCoefficientSeries)
    (ambientFourSquareLaw :
      ((ambientHamiltonPopulation p).card : ℤ) = 8 * ((p : ℤ) + 1)) :
    ((primitiveFirstPrimeSquarePopulation (p := p)).card : ℤ) =
      2 * ((cubicNonresiduePopulation (p := p)).card : ℤ) +
        2 * (1 - quadraticChar (ZMod p) (-1)) := by
  apply (brandtPrimeEigenDefect_eq_zero_iff_cubic_census (p := p) hp2).mp
  exact brandtPrimeEigenDefect_eq_zero_of_theta_balances
    hp2 hopfCurrentLaw ambientFourSquareLaw

/-- The fully source-named composition: the Hopf/Gauss factor and the odd-prime Jacobi
four-square coefficient identity close the Brandt defect without first presenting either as an
anonymous cardinal hypothesis. -/
theorem brandtPrimeEigenDefect_eq_zero_of_jacobi_sources
    (hp2 : p ≠ 2)
    (hopfCurrentLaw : hopfHeckeThetaCurrent = 8 * heckeCoefficientSeries)
    (fourSquareSourceLaw :
      PowerSeries.coeff p fullFourSquareTheta =
        PowerSeries.coeff p jacobiFourSquareLambertSeries) :
    brandtPrimeEigenDefect (p := p) = 0 := by
  apply brandtPrimeEigenDefect_eq_zero_of_theta_balances hp2 hopfCurrentLaw
  exact ambientHamiltonPopulation_card_prime_of_jacobi_source
    (Fact.out : p.Prime) hp2 fourSquareSourceLaw

/-- **ONE SOURCE LAW REMAINS.**  The Gauss factor is now unconditional, so the odd-prime Jacobi
four-square coefficient identity alone closes the Brandt eigen-defect. -/
theorem brandtPrimeEigenDefect_eq_zero_of_jacobi_four_square
    (hp2 : p ≠ 2)
    (fourSquareSourceLaw :
      PowerSeries.coeff p fullFourSquareTheta =
        PowerSeries.coeff p jacobiFourSquareLambertSeries) :
    brandtPrimeEigenDefect (p := p) = 0 := by
  exact brandtPrimeEigenDefect_eq_zero_of_jacobi_sources hp2
    hopfHeckeThetaCurrent_eq_eight_mul_heckeCoefficientSeries
    fourSquareSourceLaw

/-- The same two named Jacobi source returns force the finite cubic receiver census. -/
theorem primitive_cubic_census_of_jacobi_sources
    (hp2 : p ≠ 2)
    (hopfCurrentLaw : hopfHeckeThetaCurrent = 8 * heckeCoefficientSeries)
    (fourSquareSourceLaw :
      PowerSeries.coeff p fullFourSquareTheta =
        PowerSeries.coeff p jacobiFourSquareLambertSeries) :
    ((primitiveFirstPrimeSquarePopulation (p := p)).card : ℤ) =
      2 * ((cubicNonresiduePopulation (p := p)).card : ℤ) +
        2 * (1 - quadraticChar (ZMod p) (-1)) := by
  apply (brandtPrimeEigenDefect_eq_zero_iff_cubic_census (p := p) hp2).mp
  exact brandtPrimeEigenDefect_eq_zero_of_jacobi_sources
    hp2 hopfCurrentLaw fourSquareSourceLaw

/-- The same single surviving source law returns the finite cubic census. -/
theorem primitive_cubic_census_of_jacobi_four_square
    (hp2 : p ≠ 2)
    (fourSquareSourceLaw :
      PowerSeries.coeff p fullFourSquareTheta =
        PowerSeries.coeff p jacobiFourSquareLambertSeries) :
    ((primitiveFirstPrimeSquarePopulation (p := p)).card : ℤ) =
      2 * ((cubicNonresiduePopulation (p := p)).card : ℤ) +
        2 * (1 - quadraticChar (ZMod p) (-1)) := by
  exact primitive_cubic_census_of_jacobi_sources hp2
    hopfHeckeThetaCurrent_eq_eight_mul_heckeCoefficientSeries
    fourSquareSourceLaw

#print axioms completeHopfSource_balance
#print axioms completeHopfSource_balance_of_gauss
#print axioms primitiveFirstPrimeSquarePopulation_card_of_theta_balances
#print axioms brandtPrimeSignedCensus_eq_heckeCoeff_of_theta_balances
#print axioms brandtPrimeEigenDefect_eq_zero_of_theta_balances
#print axioms primitive_cubic_census_of_theta_balances
#print axioms brandtPrimeEigenDefect_eq_zero_of_jacobi_sources
#print axioms brandtPrimeEigenDefect_eq_zero_of_jacobi_four_square
#print axioms primitive_cubic_census_of_jacobi_sources
#print axioms primitive_cubic_census_of_jacobi_four_square

end Soma.Holonics.Millennium.FamilyTunnellPrimeThetaBalance
