import ElementaryHolonics.Millennium.FamilyTunnellJacobiFourSquareSource

/-!
# The exact Jacobi four-square closure obstruction

The source receiver has already reopened the positive unit theta into the
complete integral four-square shells, while the Lambert receiver has already
returned the divisor current. This file records their exact difference and
the resulting odd-prime equivalence. It deliberately does not assert a
whole-series equality: the Lambert receiver has nonzero even coefficients.

The remaining fibre is therefore the classical Jacobi shell-count passage,
not a missing coefficient or a change of receiver:

`sum_r card (fourSquareResidueShell r n) =
  8 * sum_{d | n, 4 ∤ d} d`.

For an odd prime this specializes exactly to the Hamilton shell law
`card (ambientHamiltonPopulation p) = 8 * (p + 1)`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareClosure

open Finset
open PowerSeries
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaCensus
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaLift
open Soma.Holonics.Millennium.FamilyTunnellFourSquareThetaReceiver
open Soma.Holonics.Millennium.FamilyTunnellFourSquarePrimeCensus
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareLambert
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareSource

/-! ## The source/Lambert defect -/

/-- The coefficient defect is exactly the integral shell-count defect against
the retained Lambert divisor current. No source or receiver term is hidden
behind the displayed equality. -/
theorem coeff_fullFourSquareTheta_sub_lambert_eq_shellDivisorDefect (n : ℕ) :
    PowerSeries.coeff n fullFourSquareTheta -
        PowerSeries.coeff n jacobiFourSquareLambertSeries =
      (∑ r : ResidueQuaternion,
        ((fourSquareResidueShell
          r.1 r.2.1 r.2.2.1 r.2.2.2 n).card : ℤ)) -
        8 * jacobiDivisorCurrent n := by
  rw [coeff_fullFourSquareTheta_eq_sum_exactShell_card,
    coeff_jacobiFourSquareLambertSeries]

/-- Coefficientwise, the requested Jacobi passage is equivalent to the
explicit shell/divisor law. This is the shortest exact remaining fibre for
an arbitrary address. -/
theorem coeff_fullFourSquareTheta_eq_lambert_iff_shellDivisorLaw (n : ℕ) :
    PowerSeries.coeff n fullFourSquareTheta =
        PowerSeries.coeff n jacobiFourSquareLambertSeries ↔
      (∑ r : ResidueQuaternion,
        ((fourSquareResidueShell
          r.1 r.2.1 r.2.2.1 r.2.2.2 n).card : ℤ)) =
        8 * jacobiDivisorCurrent n := by
  rw [coeff_fullFourSquareTheta_eq_sum_exactShell_card,
    coeff_jacobiFourSquareLambertSeries]

/-! ## Odd addresses and the prime receiver -/

/-- At a positive odd address, the exact shell/divisor fibre can equivalently
be read through the ambient Hamilton carrier. -/
theorem coeff_fullFourSquareTheta_eq_lambert_iff_ambientHamiltonLaw_of_odd
    {n : ℕ} (hn : Odd n) :
    PowerSeries.coeff n fullFourSquareTheta =
        PowerSeries.coeff n jacobiFourSquareLambertSeries ↔
      ((ambientHamiltonPopulation n).card : ℤ) =
        8 * jacobiDivisorCurrent n := by
  have hnpos : 0 < n := by
    rcases hn with ⟨k, hk⟩
    omega
  have hambient :=
    coeff_ambientOddFourSquareTheta_eq_ambientHamiltonPopulation_card
      hnpos hn
  have hfull := coeff_ambientOddFourSquareTheta_eq_fullFourSquareTheta_of_odd hn
  constructor
  · intro h
    calc
      ((ambientHamiltonPopulation n).card : ℤ) =
          PowerSeries.coeff n ambientOddFourSquareTheta := hambient.symm
      _ = PowerSeries.coeff n fullFourSquareTheta := hfull
      _ = PowerSeries.coeff n jacobiFourSquareLambertSeries := h
      _ = 8 * jacobiDivisorCurrent n := by
        rw [coeff_jacobiFourSquareLambertSeries]
  · intro h
    calc
      PowerSeries.coeff n fullFourSquareTheta =
          PowerSeries.coeff n ambientOddFourSquareTheta := hfull.symm
      _ = ((ambientHamiltonPopulation n).card : ℤ) := hambient
      _ = 8 * jacobiDivisorCurrent n := h
      _ = PowerSeries.coeff n jacobiFourSquareLambertSeries := by
        rw [coeff_jacobiFourSquareLambertSeries]

/-- For an odd prime the surviving Jacobi four-square coefficient identity is
equivalent to the exact Hamilton shell count; the Lambert side has already
been evaluated as `8 * (p + 1)`. -/
theorem coeff_fullFourSquareTheta_eq_lambert_iff_oddPrimeHamiltonLaw
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    PowerSeries.coeff p fullFourSquareTheta =
        PowerSeries.coeff p jacobiFourSquareLambertSeries ↔
      ((ambientHamiltonPopulation p).card : ℤ) =
        8 * ((p : ℤ) + 1) := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hodd := coeff_fullFourSquareTheta_eq_lambert_iff_ambientHamiltonLaw_of_odd hpodd
  rw [hodd, jacobiDivisorCurrent_prime hp hp2]

#print axioms coeff_fullFourSquareTheta_sub_lambert_eq_shellDivisorDefect
#print axioms coeff_fullFourSquareTheta_eq_lambert_iff_shellDivisorLaw
#print axioms coeff_fullFourSquareTheta_eq_lambert_iff_ambientHamiltonLaw_of_odd
#print axioms coeff_fullFourSquareTheta_eq_lambert_iff_oddPrimeHamiltonLaw

end Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareClosure
