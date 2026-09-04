import ElementaryHolonics.Millennium.FamilyTunnellBrandtTwoClassInterchange
import ElementaryHolonics.Millennium.FamilyTunnellJacobiHuardClosure

/-!
# The unconditional Jacobi calibration of a classified Brandt action

The two-class interchange theorem deliberately accepts a signed calibration.
This file removes that remaining algebraic input for the Tunnell source.  Once
an actual destination-classified neighbor census returns its four entries, its
common aperture, and the norm-one first-row fibre, the proved Jacobi/Huard
source forces the calibration to be `heckeCoeff p`.

The only remaining hypothesis in the terminal theorem is consequently the
geometric source return identifying the actual odd Tunnell neighbor population
with the classified two-class action.  No coefficientwise induction or finite
aperture check remains.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtCalibratedInterchange

open Soma.Holonics.Millennium.HeckeTheta
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector
open Soma.Holonics.Millennium.FamilyTunnellBrandtPrimeResidual
open Soma.Holonics.Millennium.FamilyTunnellBrandtTwoClassInterchange
open Soma.Holonics.Millennium.FamilyTunnellJacobiHuardClosure
open Soma.Holonics.Millennium.FamilyTunnellOddHeckeDoubleCount
open Soma.Holonics.Millennium.FamilyTunnellThetaCarrier

/-! ## The uncalibrated destination census -/

/-- The four destination fibres returned by a two-class neighbor
classification, before its signed eigenvalue is read. -/
structure TwoClassNeighborCensus where
  diagonalFirst : ℤ
  offDiagonalFirst : ℤ
  offDiagonalSecond : ℤ
  diagonalSecond : ℤ
  aperture : ℤ
  firstRow : diagonalFirst + offDiagonalFirst = aperture
  secondRow : offDiagonalSecond + diagonalSecond = aperture
  offDiagonalInterchange : offDiagonalFirst = offDiagonalSecond

/-- The raw signed return of a classified census on two coefficient fibres. -/
def TwoClassNeighborCensus.differenceReturn
    (C : TwoClassNeighborCensus) (r₁ r₂ : ℤ) : ℤ :=
  (C.diagonalFirst * r₁ + C.offDiagonalFirst * r₂) -
    (C.offDiagonalSecond * r₁ + C.diagonalSecond * r₂)

/-! ## Jacobi fixes the norm-one calibration -/

/-- The complete Huard/Jacobi theorem turns the actual norm-one first-row
return into the odd-prime Hecke calibration. -/
theorem normOneSignedCalibration_of_classified_census
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (C : TwoClassNeighborCensus)
    (haperture : C.aperture = (p : ℤ) + 1)
    (hnormOne :
      ((firstNormOneNeighborPopulation (p := p) hp2).card : ℤ) =
        2 * C.diagonalFirst) :
    C.diagonalFirst - C.offDiagonalFirst = heckeCoeff p := by
  have hdefect := brandtPrimeEigenDefect_eq_zero_proved (p := p) hp2
  have hsigned : brandtPrimeSignedCensus (p := p) = heckeCoeff p := by
    unfold brandtPrimeEigenDefect at hdefect
    linarith
  rw [brandtPrimeSignedCensus_eq_neighbor_population_sub_aperture
    (p := p) hp2, hnormOne] at hsigned
  have hrow := C.firstRow
  rw [haperture] at hrow
  linarith [hrow]

/-- A source-classified census is therefore an actual calibrated two-class
action, with no calibration hypothesis left to its caller. -/
def TwoClassNeighborCensus.toTunnellNeighborAction
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (C : TwoClassNeighborCensus)
    (haperture : C.aperture = (p : ℤ) + 1)
    (hnormOne :
      ((firstNormOneNeighborPopulation (p := p) hp2).card : ℤ) =
        2 * C.diagonalFirst) :
    TwoClassNeighborAction (heckeCoeff p) where
  diagonalFirst := C.diagonalFirst
  offDiagonalFirst := C.offDiagonalFirst
  offDiagonalSecond := C.offDiagonalSecond
  diagonalSecond := C.diagonalSecond
  aperture := C.aperture
  firstRow := C.firstRow
  secondRow := C.secondRow
  offDiagonalInterchange := C.offDiagonalInterchange
  normOneSignedCalibration :=
    normOneSignedCalibration_of_classified_census hp2 C haperture hnormOne

/-- The uncalibrated census already acts by the Hecke coefficient on every
pair once the source aperture and norm-one fibres have returned. -/
theorem TwoClassNeighborCensus.differenceReturn_eq_heckeCoeff_mul
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (C : TwoClassNeighborCensus)
    (haperture : C.aperture = (p : ℤ) + 1)
    (hnormOne :
      ((firstNormOneNeighborPopulation (p := p) hp2).card : ℤ) =
        2 * C.diagonalFirst)
    (r₁ r₂ : ℤ) :
    C.differenceReturn r₁ r₂ = heckeCoeff p * (r₁ - r₂) := by
  change
    (C.toTunnellNeighborAction hp2 haperture hnormOne).differenceReturn r₁ r₂ = _
  exact TwoClassNeighborAction.differenceReturn_eq_calibration_mul
    (C.toTunnellNeighborAction hp2 haperture hnormOne) r₁ r₂

/-! ## The exact terminal composition -/

/-- Once the actual destination-classified neighbor carrier is identified with
the already constructed odd Tunnell neighbor population, the uniform Hecke
eigen-current follows at every coefficient address. -/
theorem oddTunnellNeighborReturn_eq_heckeCoeff_mul_of_classified_source
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (C : TwoClassNeighborCensus)
    (haperture : C.aperture = (p : ℤ) + 1)
    (hnormOne :
      ((firstNormOneNeighborPopulation (p := p) hp2).card : ℤ) =
        2 * C.diagonalFirst)
    (hsource : ∀ n : ℕ,
      oddTunnellNeighborReturn (p := p) hp2 n =
        C.differenceReturn
          ((brandtFirstPopulation n).card : ℤ)
          ((brandtSecondPopulation n).card : ℤ)) :
    ∀ n : ℕ,
      oddTunnellNeighborReturn (p := p) hp2 n =
        heckeCoeff p * fullTunnellThetaCoefficient n := by
  intro n
  rw [hsource n,
    C.differenceReturn_eq_heckeCoeff_mul hp2 haperture hnormOne]
  rw [fullTunnellThetaCoefficient_eq_brandtDifference]

#print axioms normOneSignedCalibration_of_classified_census
#print axioms TwoClassNeighborCensus.differenceReturn_eq_heckeCoeff_mul
#print axioms oddTunnellNeighborReturn_eq_heckeCoeff_mul_of_classified_source

end Soma.Holonics.Millennium.FamilyTunnellBrandtCalibratedInterchange
