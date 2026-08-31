import ElementaryHolonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2CurlMultiplierSwing

/-!
# Finite physical H2 velocity-triad join

**[proved-derived; formal-checked]**  This owner returns the exact finite symmetric
velocity-triad representation of the completed physical `H2` multiplier.  The finite aperture
retains both independent transport-address pins and requires the receiving pin to inhabit the
same frequency cube.  It is therefore invariant under exchanging the transported and receiving
occurrences.

Before a norm is taken, that exchange negates the raw triadic advection face.  Reindexing the
finite population consequently identifies the transported-weighted population with the negative
of the receiver-weighted population.  The completed exchanged multiplier current is their
difference, so the raw receiver-weighted current is exactly negative one half of it.

The last theorem specializes the identity to the literal velocity Fourier modes of an admitted
open periodic solution.  No infinite convolution, cofinal limit, time estimate, or continuation
claim is made.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurlMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicTriadFluxCancellation
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Exchange-invariant finite address population -/

/-- The finite ordered transport population whose advecting, transported, and receiving pins
all lie in the same coordinate cube.  Address multiplicity and ordering are retained. -/
def physicalH2VelocityTriadAperture (radius : ℕ) :
    Finset CompleteTransportAddress :=
  (completeTransportOutputAperture radius).filter fun address ↦
    completeTransportReceiver address ∈ frequencyCube radius

theorem mem_physicalH2VelocityTriadAperture_iff
    (radius : ℕ) (address : CompleteTransportAddress) :
    address ∈ physicalH2VelocityTriadAperture radius ↔
      address.1 ∈ frequencyCube radius ∧
      address.2 ∈ frequencyCube radius ∧
      completeTransportReceiver address ∈ frequencyCube radius := by
  simp [physicalH2VelocityTriadAperture, completeTransportOutputAperture,
    and_assoc]

/-- Transport exchange preserves the complete three-pin cube population exactly. -/
theorem completeTransportExchange_mem_physicalH2VelocityTriadAperture_iff
    (radius : ℕ) (address : CompleteTransportAddress) :
    completeTransportExchange address ∈ physicalH2VelocityTriadAperture radius ↔
      address ∈ physicalH2VelocityTriadAperture radius := by
  rw [mem_physicalH2VelocityTriadAperture_iff,
    mem_physicalH2VelocityTriadAperture_iff]
  simp only [completeTransportExchange_first, completeTransportExchange_second,
    completeTransportReceiver_exchange]
  tauto

/-- Reindexing any finite receiver by transported/receiving exchange leaves its sum unchanged. -/
theorem sum_physicalH2VelocityTriadAperture_exchange
    {M : Type*} [AddCommMonoid M] (radius : ℕ)
    (face : CompleteTransportAddress → M) :
    (∑ address ∈ physicalH2VelocityTriadAperture radius,
        face (completeTransportExchange address)) =
      ∑ address ∈ physicalH2VelocityTriadAperture radius, face address := by
  exact Finset.sum_equiv completeTransportExchange
    (fun address ↦
      (completeTransportExchange_mem_physicalH2VelocityTriadAperture_iff
        radius address).symm)
    (fun _address _haddress ↦ rfl)

/-! ## Raw receiver-weighted velocity transport and completed exchange -/

/-- One raw velocity-advection face, weighted at the receiving pin by the completed physical
`H2` curl multiplier. -/
def receiverWeightedPhysicalH2VelocityAdvectionFace
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) : ℂ :=
  physicalH2CurlEnergyMultiplier (completeTransportReceiver address) *
    triadicEnergyFace address.1 address.2
      (velocityMode address.1)
      (velocityMode address.2)
      (velocityMode (completeTransportReceiver address))

/-- The corresponding transported-pin weight, kept as a separate caused occurrence until the
exchange passage joins it to the receiver-weighted population. -/
def transportedWeightedPhysicalH2VelocityAdvectionFace
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) : ℂ :=
  physicalH2CurlEnergyMultiplier address.2 *
    triadicEnergyFace address.1 address.2
      (velocityMode address.1)
      (velocityMode address.2)
      (velocityMode (completeTransportReceiver address))

/-- The literal completed physical exchanged transfer on the same ordered velocity-mode
population. -/
def physicalH2VelocityExchangedTriadFace
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress) : ℂ :=
  physicalH2ExchangedTriadTransfer (completeTransportTriad address)
    (velocityMode address.1)
    (velocityMode address.2)
    (velocityMode (completeTransportReceiver address))

/-- Exchange sends a receiver-weighted raw face to the negative transported-weighted face. -/
theorem receiverWeightedPhysicalH2VelocityAdvectionFace_exchange
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress)
    (hdivergence :
      complexDot (complexFrequencyVector address.1) (velocityMode address.1) = 0) :
    receiverWeightedPhysicalH2VelocityAdvectionFace velocityMode
        (completeTransportExchange address) =
      -transportedWeightedPhysicalH2VelocityAdvectionFace velocityMode address := by
  have hcancel := exchanged_triadicEnergyFace_cancel
    (completeTransportTriad address)
    (velocityMode address.1)
    (velocityMode address.2)
    (velocityMode (completeTransportReceiver address))
    hdivergence
  have hface :
      triadicEnergyFace address.1 (completeTransportReceiver address)
          (velocityMode address.1)
          (velocityMode (completeTransportReceiver address))
          (velocityMode address.2) =
        -triadicEnergyFace address.1 address.2
          (velocityMode address.1)
          (velocityMode address.2)
          (velocityMode (completeTransportReceiver address)) := by
    exact eq_neg_of_add_eq_zero_right (by
      simpa [completeTransportTriad] using hcancel)
  unfold receiverWeightedPhysicalH2VelocityAdvectionFace
    transportedWeightedPhysicalH2VelocityAdvectionFace
  simp only [completeTransportExchange_first, completeTransportExchange_second,
    completeTransportReceiver_exchange]
  rw [hface]
  ring

/-- Pointwise, the completed exchanged transfer is transported weight minus receiver weight. -/
theorem physicalH2VelocityExchangedTriadFace_eq_transported_sub_receiver
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress)
    (hdivergence :
      complexDot (complexFrequencyVector address.1) (velocityMode address.1) = 0) :
    physicalH2VelocityExchangedTriadFace velocityMode address =
      transportedWeightedPhysicalH2VelocityAdvectionFace velocityMode address -
        receiverWeightedPhysicalH2VelocityAdvectionFace velocityMode address := by
  unfold physicalH2VelocityExchangedTriadFace
    transportedWeightedPhysicalH2VelocityAdvectionFace
    receiverWeightedPhysicalH2VelocityAdvectionFace
  rw [physicalH2ExchangedTriadTransfer_eq_factorized
    (completeTransportTriad address)
    (velocityMode address.1)
    (velocityMode address.2)
    (velocityMode (completeTransportReceiver address)) hdivergence]
  simp only [completeTransportTriad]
  unfold physicalH2CurlEnergyMultiplier
  push_cast
  ring

/-! ## Exact finite current join -/

/-- The signed raw receiver-weighted velocity-advection current on the finite symmetric
population. -/
def finiteReceiverWeightedPhysicalH2VelocityAdvectionCurrent
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) : ℂ :=
  ∑ address ∈ physicalH2VelocityTriadAperture radius,
    receiverWeightedPhysicalH2VelocityAdvectionFace velocityMode address

/-- The finite sum of literal completed exchanged multiplier transfers on the same addressed
population. -/
def finitePhysicalH2VelocityExchangedTriadCurrent
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector) : ℂ :=
  ∑ address ∈ physicalH2VelocityTriadAperture radius,
    physicalH2VelocityExchangedTriadFace velocityMode address

/-- The transported-weighted finite population is the negative receiver-weighted population. -/
theorem finiteTransportedWeighted_eq_neg_finiteReceiverWeighted
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector)
    (hdivergence : ∀ frequency ∈ frequencyCube radius,
      complexDot (complexFrequencyVector frequency) (velocityMode frequency) = 0) :
    (∑ address ∈ physicalH2VelocityTriadAperture radius,
      transportedWeightedPhysicalH2VelocityAdvectionFace velocityMode address) =
      -finiteReceiverWeightedPhysicalH2VelocityAdvectionCurrent radius velocityMode := by
  have hreindex := sum_physicalH2VelocityTriadAperture_exchange radius
    (receiverWeightedPhysicalH2VelocityAdvectionFace velocityMode)
  unfold finiteReceiverWeightedPhysicalH2VelocityAdvectionCurrent
  rw [← hreindex]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro address haddress
  rw [receiverWeightedPhysicalH2VelocityAdvectionFace_exchange]
  · simp
  · exact hdivergence address.1
      ((mem_physicalH2VelocityTriadAperture_iff radius address).mp haddress).1

/-- **Exact finite completed-multiplier identity.**  Cancellation occurs before any norm:
the raw receiver-weighted velocity current is negative one half of the literal completed
physical exchanged-transfer population. -/
theorem finiteReceiverWeightedPhysicalH2VelocityAdvectionCurrent_eq_neg_half_exchanged
    (radius : ℕ) (velocityMode : SpatialFrequency → ComplexVector)
    (hdivergence : ∀ frequency ∈ frequencyCube radius,
      complexDot (complexFrequencyVector frequency) (velocityMode frequency) = 0) :
    finiteReceiverWeightedPhysicalH2VelocityAdvectionCurrent radius velocityMode =
      -(1 / 2 : ℂ) *
        finitePhysicalH2VelocityExchangedTriadCurrent radius velocityMode := by
  have htransport := finiteTransportedWeighted_eq_neg_finiteReceiverWeighted
    radius velocityMode hdivergence
  have hexchange :
      finitePhysicalH2VelocityExchangedTriadCurrent radius velocityMode =
        (∑ address ∈ physicalH2VelocityTriadAperture radius,
          transportedWeightedPhysicalH2VelocityAdvectionFace velocityMode address) -
        finiteReceiverWeightedPhysicalH2VelocityAdvectionCurrent radius velocityMode := by
    unfold finitePhysicalH2VelocityExchangedTriadCurrent
      finiteReceiverWeightedPhysicalH2VelocityAdvectionCurrent
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro address haddress
    exact physicalH2VelocityExchangedTriadFace_eq_transported_sub_receiver
      velocityMode address
      (hdivergence address.1
        ((mem_physicalH2VelocityTriadAperture_iff radius address).mp haddress).1)
  rw [hexchange, htransport]
  ring

/-! ## Literal open-periodic velocity specialization -/

/-- The raw finite current formed from the actual velocity Fourier modes of an admitted open
periodic solution. -/
def finiteOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) : ℂ :=
  finiteReceiverWeightedPhysicalH2VelocityAdvectionCurrent radius
    (openPeriodicVelocityFourierMode solution t)

/-- The corresponding literal finite completed exchanged-transfer current. -/
def finiteOpenPhysicalH2VelocityExchangedTriadCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) : ℂ :=
  finitePhysicalH2VelocityExchangedTriadCurrent radius
    (openPeriodicVelocityFourierMode solution t)

/-- The admitted solution discharges every divergence hypothesis, so the actual finite raw
velocity current is exactly negative one half of its completed physical multiplier swing. -/
theorem finiteOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent_eq_neg_half_exchanged
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (radius : ℕ) :
    finiteOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent solution t radius =
      -(1 / 2 : ℂ) *
        finiteOpenPhysicalH2VelocityExchangedTriadCurrent solution t radius := by
  exact finiteReceiverWeightedPhysicalH2VelocityAdvectionCurrent_eq_neg_half_exchanged
    radius (openPeriodicVelocityFourierMode solution t)
    (fun frequency _hfrequency ↦
      openPeriodicVelocityFourierMode_divergenceFree solution t frequency)

section Audit

#print axioms completeTransportExchange_mem_physicalH2VelocityTriadAperture_iff
#print axioms receiverWeightedPhysicalH2VelocityAdvectionFace_exchange
#print axioms physicalH2VelocityExchangedTriadFace_eq_transported_sub_receiver
#print axioms finiteReceiverWeightedPhysicalH2VelocityAdvectionCurrent_eq_neg_half_exchanged
#print axioms finiteOpenReceiverWeightedPhysicalH2VelocityAdvectionCurrent_eq_neg_half_exchanged

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin
