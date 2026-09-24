import ElementaryHolonics.Millennium.NavierStokesPhysicalH2CyclicSectorSwing

/-!
# Reorienting a physical H2 cyclic swing through its least pin

**[proved-derived; formal-checked]** A three-rotation physical `H2` orbit does not vanish, but
closed-triad divergence still moves every dangerous derivative onto a useful boundary.  When the
first pin is selected as the least-grade pin, the first cyclic face retains the high transported
derivative together with the small high/high multiplier difference.  The second face is exchanged
exactly onto the first pin, and the third face already differentiates at that first pin.  Thus the
two large high/low multiplier differences are paired with low-frequency derivative faces before
any norm is taken.

This is the signed local identity needed before a scale-local convolution estimate.  It makes no
population, time, or continuation claim.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2CyclicLowPinReorientation

open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CyclicSectorSwing
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurlMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-- Divergence freedom at the second pin exchanges its high transported derivative for the first
pin derivative, with the exact orientation sign retained. -/
theorem cyclicSecondTriadicFace_eq_neg_firstPinDerivativeFace
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (htransported :
      complexDot (complexFrequencyVector triad.transported) transportedMode = 0) :
    cyclicSecondTriadicFace triad advectingMode transportedMode receiverMode =
      -triadicEnergyFace triad.transported triad.advecting
        transportedMode advectingMode receiverMode := by
  have hcancel := exchanged_triadicEnergyFace_cancel triad.rotate
    transportedMode receiverMode advectingMode htransported
  exact eq_neg_of_add_eq_zero_left (by
    simpa [cyclicSecondTriadicFace] using hcancel)

/-- The third cyclic face already differentiates at the first pin. -/
theorem cyclicThirdTriadicFace_eq_firstPinDerivativeFace
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) :
    cyclicThirdTriadicFace triad advectingMode transportedMode receiverMode =
      triadicEnergyFace triad.receiver triad.advecting
        receiverMode advectingMode transportedMode := rfl

/-- **Least-pin cyclic reorientation.**  The high/high multiplier swing remains on the first
face.  Both high/low multiplier swings are transported onto faces whose derivative-frequency
occurrence is the first pin. -/
theorem cyclicPhysicalH2ExchangedTriadTransfer_eq_reoriented_firstPin
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hadvecting :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (htransported :
      complexDot (complexFrequencyVector triad.transported) transportedMode = 0)
    (hreceiver :
      complexDot (complexFrequencyVector triad.receiver) receiverMode = 0) :
    cyclicPhysicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode =
      (((torusStokesEigenvalue triad.transported -
          torusStokesEigenvalue triad.receiver) *
        (1 + torusStokesEigenvalue triad.transported +
          torusStokesEigenvalue triad.receiver) : ℝ) : ℂ) *
          triadicEnergyFace triad.advecting triad.transported
            advectingMode transportedMode receiverMode -
      (((torusStokesEigenvalue triad.receiver -
          torusStokesEigenvalue triad.advecting) *
        (1 + torusStokesEigenvalue triad.receiver +
          torusStokesEigenvalue triad.advecting) : ℝ) : ℂ) *
          triadicEnergyFace triad.transported triad.advecting
            transportedMode advectingMode receiverMode +
      (((torusStokesEigenvalue triad.advecting -
          torusStokesEigenvalue triad.transported) *
        (1 + torusStokesEigenvalue triad.advecting +
          torusStokesEigenvalue triad.transported) : ℝ) : ℂ) *
          triadicEnergyFace triad.receiver triad.advecting
            receiverMode advectingMode transportedMode := by
  rw [cyclicPhysicalH2ExchangedTriadTransfer_eq_three_factorized_swings triad
    advectingMode transportedMode receiverMode hadvecting htransported hreceiver,
    cyclicSecondTriadicFace_eq_neg_firstPinDerivativeFace triad
      advectingMode transportedMode receiverMode htransported,
    cyclicThirdTriadicFace_eq_firstPinDerivativeFace]
  unfold cyclicFirstTriadicFace
  ring

/-- Adding a common scalar to the three completed pin multipliers does not alter the reoriented
first-pin boundary.  This is the same coboundary law in the least-pin presentation. -/
theorem cyclicPhysicalH2ExchangedTriadTransfer_eq_firstPinRebasedCoboundary
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hadvecting :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (htransported :
      complexDot (complexFrequencyVector triad.transported) transportedMode = 0)
    (hreceiver :
      complexDot (complexFrequencyVector triad.receiver) receiverMode = 0) :
    cyclicPhysicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode =
      cyclicMultiplierCoboundary
        (fun frequency ↦ physicalH2CurlEnergyMultiplier frequency -
          physicalH2CurlEnergyMultiplier triad.advecting)
        triad advectingMode transportedMode receiverMode := by
  rw [cyclicPhysicalH2ExchangedTriadTransfer_eq_coboundary triad
    advectingMode transportedMode receiverMode hadvecting htransported hreceiver]
  have hcommon := cyclicMultiplierCoboundary_add_common
    (fun frequency ↦ physicalH2CurlEnergyMultiplier frequency -
      physicalH2CurlEnergyMultiplier triad.advecting)
    (physicalH2CurlEnergyMultiplier triad.advecting)
    triad advectingMode transportedMode receiverMode
  simpa only [sub_add_cancel] using hcommon

section Audit

#print axioms cyclicSecondTriadicFace_eq_neg_firstPinDerivativeFace
#print axioms cyclicPhysicalH2ExchangedTriadTransfer_eq_reoriented_firstPin
#print axioms cyclicPhysicalH2ExchangedTriadTransfer_eq_firstPinRebasedCoboundary

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2CyclicLowPinReorientation
