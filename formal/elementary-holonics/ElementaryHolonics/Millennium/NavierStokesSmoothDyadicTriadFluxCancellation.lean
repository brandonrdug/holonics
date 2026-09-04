import ElementaryHolonics.Millennium.NavierStokesDyadicFlowCommutator
import ElementaryHolonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
import ElementaryHolonics.Millennium.NavierStokesSmoothSharpDyadicShellComparison

/-!
# Smooth dyadic triad flux cancellation

**[proved-derived; formal-checked]**  This finite owner records what the signed quadratic
interaction does before any norm is taken.  First, a frequency outside a doubled cube cannot be
the sum of two pins in the original cube.  Hence a nonzero smooth band at scale `j + 1` has at
least one parent outside the scale-`j` cube: high-band current has an explicit causal ancestor.

Second, the exchanged divergence-free triad faces survive a scalar multiplier only through the
difference between its values at the transported and receiving pins.  The two adjacent smooth
dyadic multipliers add to one on a sharp shell, so their combined exchanged work cancels exactly
when both pins lie in that shell.  Thus same-shell exchange is internal circulation; only a
multiplier mismatch can cross the scale boundary.

All statements are finite and algebraic.  They assert neither absolute summability nor a terminal
Navier--Stokes estimate.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesSmoothDyadicTriadFluxCancellation

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothSharpDyadicShellComparison
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Finite causal ancestry of a high output pin -/

/-- Two pins in a coordinate cube add to a pin in the exactly doubled cube. -/
theorem add_mem_frequencyCube_two_mul
    (radius : ℕ) {p q : SpatialFrequency}
    (hp : p ∈ frequencyCube radius) (hq : q ∈ frequencyCube radius) :
    p + q ∈ frequencyCube (2 * radius) := by
  rw [mem_frequencyCube_iff] at hp hq ⊢
  intro coordinate
  have hpCoordinate := hp coordinate
  have hqCoordinate := hq coordinate
  change -(((2 * radius : ℕ) : ℤ)) ≤ p coordinate + q coordinate ∧
    p coordinate + q coordinate ≤ ((2 * radius : ℕ) : ℤ)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  omega

/-- Contrapositive ancestry law: an output outside the doubled cube has a parent outside the
original cube. -/
theorem outside_two_mul_frequencyCube_forces_parent_outside
    (radius : ℕ) {p q k : SpatialFrequency}
    (houtput : p + q = k)
    (hk : k ∉ frequencyCube (2 * radius)) :
    p ∉ frequencyCube radius ∨ q ∉ frequencyCube radius := by
  by_contra hparents
  simp only [not_or, not_not] at hparents
  have hsum := add_mem_frequencyCube_two_mul radius hparents.1 hparents.2
  rw [houtput] at hsum
  exact hk hsum

/-- For the convolution address `q = k - p`, an output outside scale `j + 1` has at least one
parent outside scale `j`. -/
theorem dyadic_output_outside_forces_convolution_parent_outside
    (scale : ℕ) (k p : SpatialFrequency)
    (hk : k ∉ frequencyCube (dyadicRadius (scale + 1))) :
    p ∉ frequencyCube (dyadicRadius scale) ∨
      transportedFrequencyAt k p ∉ frequencyCube (dyadicRadius scale) := by
  apply outside_two_mul_frequencyCube_forces_parent_outside
    (radius := dyadicRadius scale)
    (p := p) (q := transportedFrequencyAt k p) (k := k)
  · exact advecting_add_transportedFrequencyAt k p
  · simpa [dyadicRadius, pow_succ, Nat.mul_comm] using hk

/-- **No spontaneous high smooth band.**  If the direct smooth band at scale `j + 1` sees the
output `k`, then in every convolution decomposition `k = p + (k-p)` at least one parent escapes
the scale-`j` cube. -/
theorem dyadicHodgeBandWeight_succ_ne_zero_forces_parent_outside
    (scale : ℕ) (k p : SpatialFrequency)
    (hweight : dyadicHodgeBandWeight (scale + 1) k ≠ 0) :
    p ∉ frequencyCube (dyadicRadius scale) ∨
      transportedFrequencyAt k p ∉ frequencyCube (dyadicRadius scale) := by
  apply dyadic_output_outside_forces_convolution_parent_outside scale k p
  intro hk
  apply hweight
  exact dyadicHodgeBandWeight_eq_zero_of_mem_inner (scale + 1)
    (by simpa [dyadicHodgeInnerCutoff] using hk)

/-! ## Signed exchanged transfer through multiplier boundaries -/

/-- The signed exchanged work of one addressed closed triad after a scalar multiplier is attached
to the transported/receiving pin. -/
def weightedExchangedTriadTransfer
    (multiplier : SpatialFrequency → ℂ)
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) : ℂ :=
  multiplier triad.transported *
      triadicEnergyFace triad.advecting triad.transported
        advectingMode transportedMode receiverMode +
    multiplier triad.receiver *
      triadicEnergyFace triad.advecting triad.receiver
        advectingMode receiverMode transportedMode

/-- **Exact multiplier-boundary flux law.**  Divergence freedom removes all common multiplier
weight.  Only the difference between the transported and receiving multiplier values survives. -/
theorem weightedExchangedTriadTransfer_eq_difference_mul
    (multiplier : SpatialFrequency → ℂ)
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    weightedExchangedTriadTransfer multiplier triad
        advectingMode transportedMode receiverMode =
      (multiplier triad.transported - multiplier triad.receiver) *
        triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode := by
  have hcancel := exchanged_triadicEnergyFace_cancel triad
    advectingMode transportedMode receiverMode hdivergence
  have hreceiver :
      triadicEnergyFace triad.advecting triad.receiver
          advectingMode receiverMode transportedMode =
        -triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode := by
    exact eq_neg_of_add_eq_zero_right hcancel
  unfold weightedExchangedTriadTransfer
  rw [hreceiver]
  ring

/-- The exchanged transfer observed by one direct smooth dyadic band. -/
def smoothDyadicExchangedTriadTransfer
    (scale : ℕ) (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) : ℂ :=
  weightedExchangedTriadTransfer
    (fun frequency ↦ (dyadicHodgeBandWeight scale frequency : ℂ))
    triad advectingMode transportedMode receiverMode

/-- One smooth dyadic band sees precisely its multiplier jump across the exchanged triad edge. -/
theorem smoothDyadicExchangedTriadTransfer_eq_weight_difference_mul
    (scale : ℕ) (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    smoothDyadicExchangedTriadTransfer scale triad
        advectingMode transportedMode receiverMode =
      ((dyadicHodgeBandWeight scale triad.transported : ℂ) -
          (dyadicHodgeBandWeight scale triad.receiver : ℂ)) *
        triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode := by
  exact weightedExchangedTriadTransfer_eq_difference_mul
    (fun frequency ↦ (dyadicHodgeBandWeight scale frequency : ℂ))
    triad advectingMode transportedMode receiverMode hdivergence

/-- **Adjacent same-shell cancellation.**  When the two exchanged pins occupy the same noninitial
sharp shell, the sum of the two adjacent smooth-band transfers is zero before norms. -/
theorem adjacent_smoothDyadicExchangedTriadTransfers_cancel_of_same_sharpShell
    (scale : ℕ) (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (htransported : triad.transported ∈ dyadicFrequencyShell (scale + 1))
    (hreceiver : triad.receiver ∈ dyadicFrequencyShell (scale + 1)) :
    smoothDyadicExchangedTriadTransfer scale triad
        advectingMode transportedMode receiverMode +
      smoothDyadicExchangedTriadTransfer (scale + 1) triad
        advectingMode transportedMode receiverMode = 0 := by
  rw [smoothDyadicExchangedTriadTransfer_eq_weight_difference_mul
      scale triad advectingMode transportedMode receiverMode hdivergence,
    smoothDyadicExchangedTriadTransfer_eq_weight_difference_mul
      (scale + 1) triad advectingMode transportedMode receiverMode hdivergence]
  have htransportedWeight :
      (dyadicHodgeBandWeight scale triad.transported : ℂ) +
          (dyadicHodgeBandWeight (scale + 1) triad.transported : ℂ) = 1 := by
    exact_mod_cast adjacent_dyadicHodgeBandWeights_add_eq_one_of_mem_sharp_shell
      scale htransported
  have hreceiverWeight :
      (dyadicHodgeBandWeight scale triad.receiver : ℂ) +
          (dyadicHodgeBandWeight (scale + 1) triad.receiver : ℂ) = 1 := by
    exact_mod_cast adjacent_dyadicHodgeBandWeights_add_eq_one_of_mem_sharp_shell
      scale hreceiver
  calc
    (((dyadicHodgeBandWeight scale triad.transported : ℂ) -
          (dyadicHodgeBandWeight scale triad.receiver : ℂ)) *
        triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode) +
      (((dyadicHodgeBandWeight (scale + 1) triad.transported : ℂ) -
          (dyadicHodgeBandWeight (scale + 1) triad.receiver : ℂ)) *
        triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode) =
        (((dyadicHodgeBandWeight scale triad.transported : ℂ) +
            (dyadicHodgeBandWeight (scale + 1) triad.transported : ℂ)) -
          ((dyadicHodgeBandWeight scale triad.receiver : ℂ) +
            (dyadicHodgeBandWeight (scale + 1) triad.receiver : ℂ))) *
          triadicEnergyFace triad.advecting triad.transported
            advectingMode transportedMode receiverMode := by ring
    _ = 0 := by rw [htransportedWeight, hreceiverWeight]; ring

/-! ## Actual open-solution transport specialization -/

/-- The preceding signed transfer instantiated with the actual velocity pin and the two actual
vorticity pins of an admitted open periodic solution.  This is the transport part of the genuine
vorticity nonlinearity; the stretching part remains a separate population. -/
def openPeriodicSmoothDyadicVorticityTransportTriadTransfer
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) (triad : AddressedClosedFourierTriad) : ℂ :=
  smoothDyadicExchangedTriadTransfer scale triad
    (openPeriodicVelocityFourierMode solution t triad.advecting)
    (openPeriodicVorticityFourierMode solution t triad.transported)
    (openPeriodicVorticityFourierMode solution t triad.receiver)

/-- The actual vorticity-transport population has the same adjacent same-shell cancellation.
What remains in the full vorticity source is the cross-boundary transport flux together with
vortex stretching. -/
theorem adjacent_openPeriodicSmoothDyadicVorticityTransportTriadTransfers_cancel
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) (triad : AddressedClosedFourierTriad)
    (htransported : triad.transported ∈ dyadicFrequencyShell (scale + 1))
    (hreceiver : triad.receiver ∈ dyadicFrequencyShell (scale + 1)) :
    openPeriodicSmoothDyadicVorticityTransportTriadTransfer
        solution t scale triad +
      openPeriodicSmoothDyadicVorticityTransportTriadTransfer
        solution t (scale + 1) triad = 0 := by
  exact adjacent_smoothDyadicExchangedTriadTransfers_cancel_of_same_sharpShell
    scale triad
    (openPeriodicVelocityFourierMode solution t triad.advecting)
    (openPeriodicVorticityFourierMode solution t triad.transported)
    (openPeriodicVorticityFourierMode solution t triad.receiver)
    (openPeriodicVelocityFourierMode_divergenceFree solution t triad.advecting)
    htransported hreceiver

/-! ## Cumulative finite scale flux -/

/-- The direct smooth-band weights telescope to the two retained low-pass boundary faces. -/
theorem sum_complex_dyadicHodgeBandWeight_eq_lowPass_boundary
    (depth : ℕ) (frequency : SpatialFrequency) :
    (∑ scale ∈ Finset.range depth,
        (dyadicHodgeBandWeight scale frequency : ℂ)) =
      (tensorValleePoussinWeight (dyadicHodgeParameter depth) frequency : ℂ) -
        (tensorValleePoussinWeight (dyadicHodgeParameter 0) frequency : ℂ) := by
  induction depth with
  | zero => simp
  | succ depth inductionHypothesis =>
      rw [Finset.sum_range_succ, inductionHypothesis]
      unfold dyadicHodgeBandWeight
      push_cast
      ring

/-- Summing finitely many signed smooth-band transfers leaves only the cumulative multiplier
jump between the transported and receiving pins. -/
theorem sum_smoothDyadicExchangedTriadTransfer_eq_cumulative_weight_difference
    (depth : ℕ) (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    (∑ scale ∈ Finset.range depth,
        smoothDyadicExchangedTriadTransfer scale triad
          advectingMode transportedMode receiverMode) =
      ((∑ scale ∈ Finset.range depth,
          (dyadicHodgeBandWeight scale triad.transported : ℂ)) -
        (∑ scale ∈ Finset.range depth,
          (dyadicHodgeBandWeight scale triad.receiver : ℂ))) *
        triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode := by
  induction depth with
  | zero => simp
  | succ depth inductionHypothesis =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        inductionHypothesis,
        smoothDyadicExchangedTriadTransfer_eq_weight_difference_mul
          depth triad advectingMode transportedMode receiverMode hdivergence]
      ring

/-- The cumulative signed scale transfer is a boundary flux: all intermediate smooth dyadic
faces telescope, leaving only the depth low-pass and the scale-zero low-pass at the two exchanged
pins. -/
theorem sum_smoothDyadicExchangedTriadTransfer_eq_lowPass_boundary_flux
    (depth : ℕ) (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    (∑ scale ∈ Finset.range depth,
        smoothDyadicExchangedTriadTransfer scale triad
          advectingMode transportedMode receiverMode) =
      (((tensorValleePoussinWeight (dyadicHodgeParameter depth) triad.transported : ℂ) -
          (tensorValleePoussinWeight (dyadicHodgeParameter 0) triad.transported : ℂ)) -
        ((tensorValleePoussinWeight (dyadicHodgeParameter depth) triad.receiver : ℂ) -
          (tensorValleePoussinWeight (dyadicHodgeParameter 0) triad.receiver : ℂ))) *
        triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode := by
  rw [sum_smoothDyadicExchangedTriadTransfer_eq_cumulative_weight_difference
      depth triad advectingMode transportedMode receiverMode hdivergence,
    sum_complex_dyadicHodgeBandWeight_eq_lowPass_boundary,
    sum_complex_dyadicHodgeBandWeight_eq_lowPass_boundary]

section Audit

#print axioms add_mem_frequencyCube_two_mul
#print axioms dyadicHodgeBandWeight_succ_ne_zero_forces_parent_outside
#print axioms weightedExchangedTriadTransfer_eq_difference_mul
#print axioms adjacent_smoothDyadicExchangedTriadTransfers_cancel_of_same_sharpShell
#print axioms adjacent_openPeriodicSmoothDyadicVorticityTransportTriadTransfers_cancel
#print axioms sum_smoothDyadicExchangedTriadTransfer_eq_cumulative_weight_difference
#print axioms sum_smoothDyadicExchangedTriadTransfer_eq_lowPass_boundary_flux

end Audit

end Soma.Holonics.Millennium.NavierStokesSmoothDyadicTriadFluxCancellation
