import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ClockedTriadNormalForm

/-!
# A uniform lower bound for the physical-H2 triad clock

**[proved-derived; formal-checked]** A nonzero integer spatial frequency has squared lattice
length at least one.  The intrinsic primitive-character calibration therefore gives a lower bound
for every nonzero torus Stokes eigenvalue.

A nontrivial closed transport address has at least two nonzero pins among its advecting,
transported, and receiving occurrences.  Consequently its three-pin Stokes clock is bounded below
by twice the viscosity-weighted primitive scale.  The excluded zero address is retained as the
exact radical of this estimate.

This owner introduces no reciprocal clock and makes no summability, service, packing, or closure
claim.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2TriadClockLowerBound

open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedTriadNormalForm
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The integer-lattice spectral floor -/

/-- A nonzero integer spatial frequency has squared Euclidean lattice length at least one. -/
theorem one_le_frequencySquared_of_ne_zero
    {frequency : SpatialFrequency} (hfrequency : frequency ≠ 0) :
    1 ≤ frequencySquared frequency := by
  obtain ⟨coordinate, hcoordinate⟩ := Function.ne_iff.mp hfrequency
  have habsInt : (1 : ℤ) ≤ |frequency coordinate| :=
    Int.one_le_abs hcoordinate
  have habsReal : (1 : ℝ) ≤ |(frequency coordinate : ℝ)| := by
    exact_mod_cast habsInt
  have hcomponent :
      (frequency coordinate : ℝ) ^ 2 ≤ frequencySquared frequency := by
    unfold frequencySquared
    exact Finset.single_le_sum (fun index _ ↦ sq_nonneg (frequency index : ℝ))
      (Finset.mem_univ coordinate)
  nlinarith [sq_abs (frequency coordinate : ℝ)]

/-- Every nonzero lattice character lies above the primitive-character Stokes scale. -/
theorem primitiveTorusStokesScale_le_torusStokesEigenvalue
    {frequency : SpatialFrequency} (hfrequency : frequency ≠ 0) :
    primitiveTorusStokesScale ≤ torusStokesEigenvalue frequency := by
  rw [torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared]
  have hscale : 0 ≤ primitiveTorusStokesScale :=
    le_of_lt primitiveTorusStokesScale_pos
  simpa using mul_le_mul_of_nonneg_left
    (one_le_frequencySquared_of_ne_zero hfrequency) hscale

/-! ## Two supported pins in every nonzero closed address -/

/-- Every nonzero complete transport address has at least two nonzero pins.  The alternatives
retain which two of the three addressed occurrences carry the support. -/
theorem completeTransportAddress_has_two_nonzero_pins
    (address : CompleteTransportAddress) (haddress : address ≠ (0, 0)) :
    (address.1 ≠ 0 ∧ address.2 ≠ 0) ∨
      (address.1 ≠ 0 ∧ completeTransportReceiver address ≠ 0) ∨
      (address.2 ≠ 0 ∧ completeTransportReceiver address ≠ 0) := by
  by_cases hfirst : address.1 = 0
  · have hsecond : address.2 ≠ 0 := by
      intro hsecond
      apply haddress
      exact Prod.ext hfirst hsecond
    have hreceiverEq : completeTransportReceiver address = -address.2 := by
      funext coordinate
      simp [completeTransportReceiver, hfirst]
    have hreceiver : completeTransportReceiver address ≠ 0 := by
      rw [hreceiverEq]
      exact neg_ne_zero.mpr hsecond
    exact Or.inr (Or.inr ⟨hsecond, hreceiver⟩)
  · by_cases hsecond : address.2 = 0
    · have hreceiverEq : completeTransportReceiver address = -address.1 := by
        funext coordinate
        simp [completeTransportReceiver, hsecond]
      have hreceiver : completeTransportReceiver address ≠ 0 := by
        rw [hreceiverEq]
        exact neg_ne_zero.mpr hfirst
      exact Or.inr (Or.inl ⟨hfirst, hreceiver⟩)
    · exact Or.inl ⟨hfirst, hsecond⟩

/-- The spectral sum of the three closed pins contains at least two primitive spectral units. -/
theorem two_mul_primitiveTorusStokesScale_le_closed_pin_sum
    (address : CompleteTransportAddress) (haddress : address ≠ (0, 0)) :
    2 * primitiveTorusStokesScale ≤
      torusStokesEigenvalue address.1 +
        torusStokesEigenvalue address.2 +
          torusStokesEigenvalue (completeTransportReceiver address) := by
  rcases completeTransportAddress_has_two_nonzero_pins address haddress with
    ⟨hfirst, hsecond⟩ | ⟨hfirst, hreceiver⟩ | ⟨hsecond, hreceiver⟩
  · linarith [primitiveTorusStokesScale_le_torusStokesEigenvalue hfirst,
      primitiveTorusStokesScale_le_torusStokesEigenvalue hsecond,
      torusStokesEigenvalue_nonneg (completeTransportReceiver address)]
  · linarith [primitiveTorusStokesScale_le_torusStokesEigenvalue hfirst,
      primitiveTorusStokesScale_le_torusStokesEigenvalue hreceiver,
      torusStokesEigenvalue_nonneg address.2]
  · linarith [primitiveTorusStokesScale_le_torusStokesEigenvalue hsecond,
      primitiveTorusStokesScale_le_torusStokesEigenvalue hreceiver,
      torusStokesEigenvalue_nonneg address.1]

/-- Uniform division-free lower bound for every nontrivial physical-H2 triad clock. -/
theorem two_mul_viscosity_mul_primitiveTorusStokesScale_le_physicalH2TriadStokesClock
    {nu : ℝ} (hnu : 0 ≤ nu) (address : CompleteTransportAddress)
    (haddress : address ≠ (0, 0)) :
    2 * nu * primitiveTorusStokesScale ≤
      physicalH2TriadStokesClock nu address := by
  have hpins := two_mul_primitiveTorusStokesScale_le_closed_pin_sum address haddress
  unfold physicalH2TriadStokesClock
  calc
    2 * nu * primitiveTorusStokesScale =
        nu * (2 * primitiveTorusStokesScale) := by ring
    _ ≤ nu * (torusStokesEigenvalue address.1 +
        torusStokesEigenvalue address.2 +
          torusStokesEigenvalue (completeTransportReceiver address)) :=
      mul_le_mul_of_nonneg_left hpins hnu

/-! ## The retained zero radical -/

/-- The trivial transport address carries exactly zero Stokes clock for every viscosity. -/
@[simp]
theorem physicalH2TriadStokesClock_zero_address (nu : ℝ) :
    physicalH2TriadStokesClock nu (0, 0) = 0 := by
  unfold physicalH2TriadStokesClock
  simp [completeTransportReceiver,
    torusStokesEigenvalue_eq_primitiveScale_mul_frequencySquared,
    frequencySquared]

/-! ## Kernel audit -/

#print axioms one_le_frequencySquared_of_ne_zero
#print axioms primitiveTorusStokesScale_le_torusStokesEigenvalue
#print axioms completeTransportAddress_has_two_nonzero_pins
#print axioms two_mul_primitiveTorusStokesScale_le_closed_pin_sum
#print axioms two_mul_viscosity_mul_primitiveTorusStokesScale_le_physicalH2TriadStokesClock
#print axioms physicalH2TriadStokesClock_zero_address

end Soma.Holonics.Millennium.NavierStokesPhysicalH2TriadClockLowerBound
