import ElementaryHolonics.Millennium.NavierStokesH2TriadShellLeverBound

/-!
# The H2 multiplier swing through a smooth dyadic boundary

**[proved-derived; formal-checked]**  The standing inhomogeneous `H2` curl-energy multiplier and
one smooth dyadic band are two distinct receiver factors.  Their product therefore crosses an
exchanged divergence-free triad by a discrete product rule: one term is the exact `H2` Stokes
swing retained by the transported band weight, and the other is the smooth-band boundary flux
retained by the receiver `H2` weight.

On two adjacent smooth bands covering one noninitial sharp shell, the transported weights add to
one while the boundary fluxes cancel.  The two localized occurrences consequently reconstruct
the full `H2` exchanged transfer exactly.  This is a finite signed composition; no norm, infinite
triad sum, or continuation estimate is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesH2DyadicMultiplierProductSwing

open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicTriadFluxCancellation
open Soma.Holonics.Millennium.NavierStokesSmoothSharpDyadicShellComparison
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Product-localized H2 transfer -/

/-- The complete exchanged transfer observed after multiplying the standing `H2` receiver by one
smooth dyadic band.  The two multiplier factors remain explicit in the definition. -/
def h2SmoothDyadicExchangedTriadTransfer
    (scale : ℕ) (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) : ℂ :=
  weightedExchangedTriadTransfer
    (fun frequency ↦
      (dyadicHodgeBandWeight scale frequency : ℂ) * h2CurlEnergyMultiplier frequency)
    triad advectingMode transportedMode receiverMode

/-- **Discrete multiplier product rule.**  After the common exchanged face is cancelled, the
product multiplier splits into the transported band weight times the intrinsic `H2` swing and
the receiver `H2` weight times the smooth-band boundary flux. -/
theorem h2SmoothDyadicExchangedTriadTransfer_eq_h2Swing_add_boundaryFlux
    (scale : ℕ) (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    h2SmoothDyadicExchangedTriadTransfer scale triad
        advectingMode transportedMode receiverMode =
      (dyadicHodgeBandWeight scale triad.transported : ℂ) *
          h2ExchangedTriadTransfer triad
            advectingMode transportedMode receiverMode +
        h2CurlEnergyMultiplier triad.receiver *
          smoothDyadicExchangedTriadTransfer scale triad
            advectingMode transportedMode receiverMode := by
  rw [h2SmoothDyadicExchangedTriadTransfer,
    weightedExchangedTriadTransfer_eq_difference_mul _ triad
      advectingMode transportedMode receiverMode hdivergence,
    h2ExchangedTriadTransfer,
    weightedExchangedTriadTransfer_eq_difference_mul _ triad
      advectingMode transportedMode receiverMode hdivergence,
    smoothDyadicExchangedTriadTransfer_eq_weight_difference_mul
      scale triad advectingMode transportedMode receiverMode hdivergence]
  ring

/-! ## Adjacent-band reconstruction -/

/-- Two adjacent smooth `H2`-localized transfers reconstruct the complete `H2` transfer whenever
both exchanged pins occupy the sharp shell covered by those bands.  The boundary-flux term is
internal circulation and vanishes before any norm receiver is applied. -/
theorem adjacent_h2SmoothDyadicExchangedTriadTransfers_eq_h2ExchangedTriadTransfer
    (scale : ℕ) (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (htransported : triad.transported ∈ dyadicFrequencyShell (scale + 1))
    (hreceiver : triad.receiver ∈ dyadicFrequencyShell (scale + 1)) :
    h2SmoothDyadicExchangedTriadTransfer scale triad
        advectingMode transportedMode receiverMode +
      h2SmoothDyadicExchangedTriadTransfer (scale + 1) triad
        advectingMode transportedMode receiverMode =
      h2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode := by
  rw [h2SmoothDyadicExchangedTriadTransfer_eq_h2Swing_add_boundaryFlux
      scale triad advectingMode transportedMode receiverMode hdivergence,
    h2SmoothDyadicExchangedTriadTransfer_eq_h2Swing_add_boundaryFlux
      (scale + 1) triad advectingMode transportedMode receiverMode hdivergence]
  have hweight :
      (dyadicHodgeBandWeight scale triad.transported : ℂ) +
          (dyadicHodgeBandWeight (scale + 1) triad.transported : ℂ) = 1 := by
    exact_mod_cast adjacent_dyadicHodgeBandWeights_add_eq_one_of_mem_sharp_shell
      scale htransported
  have hboundary :
      smoothDyadicExchangedTriadTransfer scale triad
          advectingMode transportedMode receiverMode +
        smoothDyadicExchangedTriadTransfer (scale + 1) triad
          advectingMode transportedMode receiverMode = 0 :=
    adjacent_smoothDyadicExchangedTriadTransfers_cancel_of_same_sharpShell
      scale triad advectingMode transportedMode receiverMode hdivergence
        htransported hreceiver
  calc
    (dyadicHodgeBandWeight scale triad.transported : ℂ) *
          h2ExchangedTriadTransfer triad
            advectingMode transportedMode receiverMode +
        h2CurlEnergyMultiplier triad.receiver *
          smoothDyadicExchangedTriadTransfer scale triad
            advectingMode transportedMode receiverMode +
      ((dyadicHodgeBandWeight (scale + 1) triad.transported : ℂ) *
          h2ExchangedTriadTransfer triad
            advectingMode transportedMode receiverMode +
        h2CurlEnergyMultiplier triad.receiver *
          smoothDyadicExchangedTriadTransfer (scale + 1) triad
            advectingMode transportedMode receiverMode) =
        ((dyadicHodgeBandWeight scale triad.transported : ℂ) +
            (dyadicHodgeBandWeight (scale + 1) triad.transported : ℂ)) *
          h2ExchangedTriadTransfer triad
            advectingMode transportedMode receiverMode +
        h2CurlEnergyMultiplier triad.receiver *
          (smoothDyadicExchangedTriadTransfer scale triad
              advectingMode transportedMode receiverMode +
            smoothDyadicExchangedTriadTransfer (scale + 1) triad
              advectingMode transportedMode receiverMode) := by ring
    _ = h2ExchangedTriadTransfer triad
          advectingMode transportedMode receiverMode := by
      rw [hweight, hboundary]
      ring

section Audit

#print axioms h2SmoothDyadicExchangedTriadTransfer_eq_h2Swing_add_boundaryFlux
#print axioms adjacent_h2SmoothDyadicExchangedTriadTransfers_eq_h2ExchangedTriadTransfer

end Audit

end Soma.Holonics.Millennium.NavierStokesH2DyadicMultiplierProductSwing
