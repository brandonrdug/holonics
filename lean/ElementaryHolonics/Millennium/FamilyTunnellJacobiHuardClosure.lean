import ElementaryHolonics.Millennium.FamilyTunnellJacobiHuardParityReindexing
import ElementaryHolonics.Millennium.FamilyTunnellJacobiHuardEvaluation
import ElementaryHolonics.Millennium.FamilyTunnellPrimeThetaBalance

/-!
# Composition of the Huard source into the prime Brandt receiver

The exact parity carrier is now proved independently.  Consequently a proof
of the remaining cleared Huard source law immediately inhabits the complete
finite source, returns the level-two divisor convolution, reconstructs the
full Jacobi four-square identity, and kills the odd-prime Brandt defect.

This file is only the serial composition.  It neither assumes the Huard law
as an axiom nor hides it inside a structure field: every theorem below takes
that one source proposition explicitly until the finite source construction
supplies it.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiHuardClosure

open PowerSeries
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareLambert
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareSource
open Soma.Holonics.Millennium.FamilyTunnellJacobiQuarticProduct
open Soma.Holonics.Millennium.FamilyTunnellJacobiDivisorConvolutionReduction
open Soma.Holonics.Millennium.FamilyTunnellJacobiHuardLevelTwoSource
open Soma.Holonics.Millennium.FamilyTunnellJacobiHuardParityReindexing
open Soma.Holonics.Millennium.FamilyTunnellJacobiHuardEvaluation
open Soma.Holonics.Millennium.FamilyTunnellBrandtPrimeResidual
open Soma.Holonics.Millennium.FamilyTunnellPrimeThetaBalance

/-- The proved parity return joins any source proof of Huard's cleared
identity into the complete finite HOSW source object. -/
theorem finiteSource_of_huardLemmaOne
    (hhuard : HuardLemmaOneCleared) :
    HuardOuSpearmanWilliamsFiniteSource :=
  ⟨hhuard, huardParityReindexing⟩

/-- The remaining Huard source law therefore returns the exact uniform
level-two additive divisor convolution formula. -/
theorem doubledDivisorConvolutionFormula_of_huardLemmaOne
    (hhuard : HuardLemmaOneCleared) :
    DoubledDivisorConvolutionFormula :=
  doubledDivisorConvolutionFormula_of_finiteSource
    (finiteSource_of_huardLemmaOne hhuard)

/-- The same source law reconstructs the complete formal Jacobi identity. -/
theorem fullFourSquareTheta_eq_completedLambert_of_huardLemmaOne
    (hhuard : HuardLemmaOneCleared) :
    FamilyTunnellJacobiFourSquareSource.fullFourSquareTheta =
      completedJacobiFourSquareLambertSeries :=
  fullFourSquareTheta_eq_completedLambert_of_doubled
    (doubledDivisorConvolutionFormula_of_huardLemmaOne hhuard)

/-- Every positive shell returns its complete divisor current after the one
Huard source law is supplied. -/
theorem totalShellDivisorLaw_of_huardLemmaOne
    (hhuard : HuardLemmaOneCleared) :
    ∀ n : ℕ, 0 < n →
      ((totalFourSquareShell n).card : ℤ) = 8 * jacobiDivisorCurrent n :=
  totalShellDivisorLaw_of_finiteSource
    (finiteSource_of_huardLemmaOne hhuard)

/-- At every odd prime, the reconstructed Jacobi coefficient closes the
already constructed Hopf/Brandt square and annihilates its exact defect. -/
theorem brandtPrimeEigenDefect_eq_zero_of_huardLemmaOne
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hhuard : HuardLemmaOneCleared) :
    brandtPrimeEigenDefect (p := p) = 0 := by
  apply brandtPrimeEigenDefect_eq_zero_of_jacobi_four_square hp2
  calc
    PowerSeries.coeff p
        FamilyTunnellJacobiFourSquareSource.fullFourSquareTheta =
        PowerSeries.coeff p completedJacobiFourSquareLambertSeries :=
      congrArg (PowerSeries.coeff p)
        (fullFourSquareTheta_eq_completedLambert_of_huardLemmaOne hhuard)
    _ = 8 * jacobiDivisorCurrent p :=
      coeff_completedJacobiFourSquareLambertSeries_of_pos
        (Fact.out : p.Prime).pos
    _ = PowerSeries.coeff p jacobiFourSquareLambertSeries := by
      rw [coeff_jacobiFourSquareLambertSeries]

/-! ## Unconditional returns from the checked source -/

/-- The complete finite HOSW source is now inhabited by the checked Huard
source law and the checked parity reindexing. -/
theorem huardOuSpearmanWilliamsFiniteSource_proved :
    HuardOuSpearmanWilliamsFiniteSource :=
  finiteSource_of_huardLemmaOne huardLemmaOneCleared_proved

/-- The exact uniform level-two additive divisor-convolution formula. -/
theorem doubledDivisorConvolutionFormula_proved :
    DoubledDivisorConvolutionFormula :=
  doubledDivisorConvolutionFormula_of_huardLemmaOne
    huardLemmaOneCleared_proved

/-- The reconstructed full Jacobi four-square power-series identity. -/
theorem fullFourSquareTheta_eq_completedLambert_proved :
    FamilyTunnellJacobiFourSquareSource.fullFourSquareTheta =
      completedJacobiFourSquareLambertSeries :=
  fullFourSquareTheta_eq_completedLambert_of_huardLemmaOne
    huardLemmaOneCleared_proved

/-- Every positive four-square shell carries exactly eight copies of the
Jacobi divisor current. -/
theorem totalShellDivisorLaw_proved :
    ∀ n : ℕ, 0 < n →
      ((totalFourSquareShell n).card : ℤ) = 8 * jacobiDivisorCurrent n :=
  totalShellDivisorLaw_of_huardLemmaOne huardLemmaOneCleared_proved

/-- At every odd prime, the exact norm-one Brandt calibration defect
vanishes.  This is the base-point calibration, not yet the uniform Hecke
successor law at every coefficient address. -/
theorem brandtPrimeEigenDefect_eq_zero_proved
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    brandtPrimeEigenDefect (p := p) = 0 :=
  brandtPrimeEigenDefect_eq_zero_of_huardLemmaOne hp2
    huardLemmaOneCleared_proved

#print axioms finiteSource_of_huardLemmaOne
#print axioms doubledDivisorConvolutionFormula_of_huardLemmaOne
#print axioms fullFourSquareTheta_eq_completedLambert_of_huardLemmaOne
#print axioms totalShellDivisorLaw_of_huardLemmaOne
#print axioms brandtPrimeEigenDefect_eq_zero_of_huardLemmaOne
#print axioms huardOuSpearmanWilliamsFiniteSource_proved
#print axioms doubledDivisorConvolutionFormula_proved
#print axioms fullFourSquareTheta_eq_completedLambert_proved
#print axioms totalShellDivisorLaw_proved
#print axioms brandtPrimeEigenDefect_eq_zero_proved

end Soma.Holonics.Millennium.FamilyTunnellJacobiHuardClosure
