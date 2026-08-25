import ElementaryHolonics.Foundation.PrimeValuationRadixAtlas
import ElementaryHolonics.Millennium.PrimeIndex
import ElementaryHolonics.Millennium.CongruentSeventeen
import Mathlib.Tactic

/-!
# Exact radix faces, the seventeenth depth, and additive prime caustics

[definition] This file binds the general prime-valuation/radix owner to the two arithmetic
occurrences that motivated it.  The decimal occurrence is the exact population `42 * 10^17`; the
Birch--Swinnerton--Dyer occurrence is the pair of coefficients `(34, 2)` in the seventeen descent.
They use the same operation but occupy opposite faces of it:

* `42 * 10^17` removes seventeen whole radix-ten layers and returns residual `42`;
* `(34, 2)` removes one common radix-two layer and returns residual pair `(17, 1)`; and
* subtracting the two normalized BSD branch equations returns `v^2 - 17*u^2 = 1` exactly.

[proved-derived; formal-checked] The full prime face of `42 * 10^17` is
`2^18 * 3 * 5^17 * 7`, seventeen is `P 6`, and the earlier Hodge arithmetic returns
`412236000 = 2^5 * 3^3 * 5^3 * 11 * 347` exactly.  The prime `347` is an additive caustic: it is
absent from each incoming term and appears after their exact addition.  No rounded
`42 * 10^17` upper bound is asserted anywhere in this file.
-/

namespace Soma.Holonics.Millennium.PrimeRadixAtlas

open Soma.Holonics.Foundation.PrimeValuationRadixAtlas
open Soma.Holonics.Foundation.PrimeValuationRadixAtlas.ExactRadixChart
open Soma.Holonics.Millennium

/-! ## 1. The exact decimal occurrence -/

/-- [definition] The exact population whose decimal chart has depth seventeen. -/
def decimalPopulation : ℕ := 42 * 10 ^ 17

theorem theTwoValuationIsEighteen : primeValuation decimalPopulation 2 = 18 := by
  exact primeValuation_eq_of_pow_dvd_not_dvd
    (by norm_num) (by norm_num [decimalPopulation])
    (by norm_num [decimalPopulation]) (by norm_num [decimalPopulation])

theorem theThreeValuationIsOne : primeValuation decimalPopulation 3 = 1 := by
  exact primeValuation_eq_of_pow_dvd_not_dvd
    (by norm_num) (by norm_num [decimalPopulation])
    (by norm_num [decimalPopulation]) (by norm_num [decimalPopulation])

theorem theFiveValuationIsSeventeen : primeValuation decimalPopulation 5 = 17 := by
  exact primeValuation_eq_of_pow_dvd_not_dvd
    (by norm_num) (by norm_num [decimalPopulation])
    (by norm_num [decimalPopulation]) (by norm_num [decimalPopulation])

theorem theSevenValuationIsOne : primeValuation decimalPopulation 7 = 1 := by
  exact primeValuation_eq_of_pow_dvd_not_dvd
    (by norm_num) (by norm_num [decimalPopulation])
    (by norm_num [decimalPopulation]) (by norm_num [decimalPopulation])

/-- [proved-derived; formal-checked] The complete prime face; this is an equality of natural
populations, not scientific notation. -/
theorem theDecimalPopulationHasItsCompletePrimeFace :
    decimalPopulation = 2 ^ 18 * 3 * 5 ^ 17 * 7 := by
  norm_num [decimalPopulation]

/-- [proved-derived; formal-checked] Seventeen is the maximal radix-ten depth and `42` is the exact
terminal residual. -/
def theFortyTwoTimesTenToSeventeenChart : ExactRadixChart 10 decimalPopulation :=
  ExactRadixChart.ofPrimeWitness
    (p := 5) (depth := 17) (residual := 42)
    (by norm_num)
    (by norm_num [decimalPopulation])
    (by norm_num [decimalPopulation])
    (by norm_num)
    (by norm_num)
    theFiveValuationIsSeventeen

theorem theDecimalChartReturnsSeventeenAndFortyTwo :
    theFortyTwoTimesTenToSeventeenChart.depth = 17 ∧
      theFortyTwoTimesTenToSeventeenChart.residual = 42 := by
  exact ⟨rfl, rfl⟩

theorem theDecimalResidualRefusesAnotherTen :
    ¬ 10 ∣ theFortyTwoTimesTenToSeventeenChart.residual :=
  theFortyTwoTimesTenToSeventeenChart.theResidualIsTerminal

/-! ## 2. The BSD coefficient pair is the same exact normalization -/

theorem theThirtyFourTwoValuationIsOne : primeValuation 34 2 = 1 := by
  exact primeValuation_eq_of_pow_dvd_not_dvd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem theTwoTwoValuationIsOne : primeValuation 2 2 = 1 := by
  exact primeValuation_eq_of_pow_dvd_not_dvd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- [proved-derived; formal-checked] `34 = 2^1 * 17`, with maximal binary depth one. -/
def theThirtyFourBinaryChart : ExactRadixChart 2 34 :=
  ExactRadixChart.ofPrimeWitness
    (p := 2) (depth := 1) (residual := 17)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    theThirtyFourTwoValuationIsOne

/-- [proved-derived; formal-checked] `2 = 2^1 * 1`, with maximal binary depth one. -/
def theTwoBinaryChart : ExactRadixChart 2 2 :=
  ExactRadixChart.ofPrimeWitness
    (p := 2) (depth := 1) (residual := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    theTwoTwoValuationIsOne

theorem theBsdCoefficientPairReturnsSeventeenAndOne :
    theThirtyFourBinaryChart.residual = 17 ∧ theTwoBinaryChart.residual = 1 := by
  exact ⟨rfl, rfl⟩

/-- [proved-derived; formal-checked] After the common binary layer is removed, differencing the two
branch equations returns precisely the `(17,1)` residual pair. -/
theorem theBsdBranchDifferenceIsTheNormalizedResidual {X u v : ℤ}
    (h1 : X ^ 2 = 34 * u ^ 2 + 1) (h2 : X ^ 2 + 1 = 2 * v ^ 2) :
    v ^ 2 - (theThirtyFourBinaryChart.residual : ℤ) * u ^ 2 =
      (theTwoBinaryChart.residual : ℤ) := by
  simpa [theThirtyFourBinaryChart, theTwoBinaryChart] using
    CongruentSeventeen.thePellRelation h1 h2

/-- [proved-derived; formal-checked] The residual prime is the sixth indexed prime, hence the
seventh member of the zero-indexed prime basis. -/
theorem theBsdResidualIsTheSixthIndexedPrime :
    theThirtyFourBinaryChart.residual = PrimeIndex.P 6 := by
  rw [PrimeIndex.theSixthPrimeIsSeventeen]
  rfl

/-! ## 3. Addition creates an exact prime caustic -/

/-- [definition] The first exact coefficient population from the prior Hodge arithmetic. -/
def lowCoefficientFace : ℕ := 2 * 198000

/-- [definition] The second exact coefficient population from the prior Hodge arithmetic. -/
def mixedCoefficientFace : ℕ := 11 * 24 * 1560000

theorem theCoefficientReturnIsExact :
    lowCoefficientFace + mixedCoefficientFace = 412236000 := by
  norm_num [lowCoefficientFace, mixedCoefficientFace]

/-- [counterexample; formal-checked] The former `420000000` intermediate coefficient is a strict
enlargement of the returned sum, not another spelling of that occurrence. -/
theorem theRoundedIntermediateStrictlyEnlargesTheReturn :
    lowCoefficientFace + mixedCoefficientFace < 420000000 := by
  norm_num [lowCoefficientFace, mixedCoefficientFace]

theorem theLowCoefficientHasItsCompletePrimeFace :
    lowCoefficientFace = 2 ^ 5 * 3 ^ 2 * 5 ^ 3 * 11 := by
  norm_num [lowCoefficientFace]

theorem theMixedCoefficientHasItsCompletePrimeFace :
    mixedCoefficientFace = 2 ^ 9 * 3 ^ 2 * 5 ^ 4 * 11 * 13 := by
  norm_num [mixedCoefficientFace]

/-- [proved-derived; formal-checked] The second incoming face is exactly `1040` copies of the
first; their addition therefore returns `1041 = 3 * 347` copies of the common face. -/
theorem theCoefficientAdditionFactorsThroughItsExactCommonFace :
    mixedCoefficientFace = 1040 * lowCoefficientFace ∧
      lowCoefficientFace + mixedCoefficientFace = (3 * 347) * lowCoefficientFace := by
  constructor <;> norm_num [lowCoefficientFace, mixedCoefficientFace]

theorem theCoefficientReturnHasItsCompletePrimeFace :
    lowCoefficientFace + mixedCoefficientFace = 2 ^ 5 * 3 ^ 3 * 5 ^ 3 * 11 * 347 := by
  norm_num [lowCoefficientFace, mixedCoefficientFace]

theorem theLowFaceHasNoThreeFortySeven : primeValuation lowCoefficientFace 347 = 0 := by
  exact primeValuation_eq_of_pow_dvd_not_dvd
    (by norm_num) (by norm_num [lowCoefficientFace])
    (by norm_num) (by norm_num [lowCoefficientFace])

theorem theMixedFaceHasNoThreeFortySeven : primeValuation mixedCoefficientFace 347 = 0 := by
  exact primeValuation_eq_of_pow_dvd_not_dvd
    (by norm_num) (by norm_num [mixedCoefficientFace])
    (by norm_num) (by norm_num [mixedCoefficientFace])

theorem theReturnHasOneThreeFortySeven :
    primeValuation (lowCoefficientFace + mixedCoefficientFace) 347 = 1 := by
  exact primeValuation_eq_of_pow_dvd_not_dvd
    (by norm_num) (by norm_num [lowCoefficientFace, mixedCoefficientFace])
    (by norm_num [lowCoefficientFace, mixedCoefficientFace])
    (by norm_num [lowCoefficientFace, mixedCoefficientFace])

/-- [proved-derived; formal-checked] `347` is absent from both incident populations and appears in
their sum.  The caustic is the exact valuation jump `0 < 1`. -/
theorem theCoefficientAdditionCreatesTheThreeFortySevenCaustic :
    AdditivePrimeCaustic 347 lowCoefficientFace mixedCoefficientFace 0 := by
  refine
    { prime := by norm_num
      left_positive := by norm_num [lowCoefficientFace]
      right_positive := by norm_num [mixedCoefficientFace]
      left_entry := theLowFaceHasNoThreeFortySeven
      right_entry := theMixedFaceHasNoThreeFortySeven
      return_jump := ?_ }
  rw [theReturnHasOneThreeFortySeven]
  omega

end Soma.Holonics.Millennium.PrimeRadixAtlas

#print axioms Soma.Holonics.Millennium.PrimeRadixAtlas.theDecimalPopulationHasItsCompletePrimeFace
#print axioms Soma.Holonics.Millennium.PrimeRadixAtlas.theDecimalChartReturnsSeventeenAndFortyTwo
#print axioms Soma.Holonics.Millennium.PrimeRadixAtlas.theBsdBranchDifferenceIsTheNormalizedResidual
#print axioms Soma.Holonics.Millennium.PrimeRadixAtlas.theBsdResidualIsTheSixthIndexedPrime
#print axioms Soma.Holonics.Millennium.PrimeRadixAtlas.theRoundedIntermediateStrictlyEnlargesTheReturn
#print axioms Soma.Holonics.Millennium.PrimeRadixAtlas.theCoefficientAdditionFactorsThroughItsExactCommonFace
#print axioms Soma.Holonics.Millennium.PrimeRadixAtlas.theCoefficientReturnHasItsCompletePrimeFace
#print axioms Soma.Holonics.Millennium.PrimeRadixAtlas.theCoefficientAdditionCreatesTheThreeFortySevenCaustic
