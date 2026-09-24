import ElementaryHolonics.Millennium.NavierStokesH2AdvectingLowGradeLeverBound
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin

/-!
# Least-grade lever for the completed physical H2 velocity swing

**[proved-derived; formal-checked]** The completed velocity multiplier carries both the
pantographic Stokes difference and the additional symmetric curl scale.  This owner transports
the existing least-dyadic-grade geometry into that completed chart without discarding either
factor.  On an advecting-low closed triad, the first factor is the low/high grade ratio times the
common high square; the second remains the exact sum of the two high Stokes coordinates, or its
explicit common-cube majorant.

The last theorem specializes the bound to the literal velocity Fourier modes of an admitted open
periodic solution.  No population sum, time estimate, or continuation claim is made.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityGradeLeverBound

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteDyadicTriadSectorPartition
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradeLeverBound
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurlMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityTriadJoin
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-- The completed physical velocity swing retains the least-grade ratio and its distinct
symmetric curl-scale occurrence. -/
theorem norm_physicalH2ExchangedTriadTransfer_le_advectingLowGradeRatio
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (_hsector : AdvectingLowSector triad) :
    ‖physicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode‖ ≤
      (primitiveTorusStokesScale *
        (6 * dyadicGradeLengthRatio (advectingGrade triad)
            (advectingLowHighGrade triad) *
          (dyadicRadius (advectingLowHighGrade triad) : ℝ) ^ 2) *
        (1 + torusStokesEigenvalue triad.transported +
          torusStokesEigenvalue triad.receiver)) *
        ‖triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode‖ := by
  have hbase := norm_physicalH2ExchangedTriadTransfer_le_six_mul_cubeRadii
    triad
    (dyadicRadius (advectingGrade triad))
    (dyadicRadius (advectingLowHighGrade triad))
    advectingMode transportedMode receiverMode hdivergence
    (frequencyDyadicGrade_mem triad.advecting)
    (transported_mem_advectingLowHighGradeCube triad)
    (receiver_mem_advectingLowHighGradeCube triad)
  calc
    ‖physicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode‖ ≤
      (primitiveTorusStokesScale *
        (6 * (dyadicRadius (advectingGrade triad) : ℝ) *
          (dyadicRadius (advectingLowHighGrade triad) : ℝ)) *
        (1 + torusStokesEigenvalue triad.transported +
          torusStokesEigenvalue triad.receiver)) *
        ‖triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode‖ := hbase
    _ = (primitiveTorusStokesScale *
        (6 * dyadicGradeLengthRatio (advectingGrade triad)
            (advectingLowHighGrade triad) *
          (dyadicRadius (advectingLowHighGrade triad) : ℝ) ^ 2) *
        (1 + torusStokesEigenvalue triad.transported +
          torusStokesEigenvalue triad.receiver)) *
        ‖triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode‖ := by
      rw [show
        6 * (dyadicRadius (advectingGrade triad) : ℝ) *
            (dyadicRadius (advectingLowHighGrade triad) : ℝ) =
          6 * ((dyadicRadius (advectingGrade triad) : ℝ) *
            (dyadicRadius (advectingLowHighGrade triad) : ℝ)) by ring,
        dyadicGrade_low_mul_high_eq_ratio_mul_high_sq]
      ring

/-- Fully aperture-bounded form.  The retained scale is a grade ratio times a high fourth-order
velocity multiplier, not the high square of the vorticity test factor alone. -/
theorem norm_physicalH2ExchangedTriadTransfer_le_explicit_advectingLowGradeRatio
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (_hsector : AdvectingLowSector triad) :
    ‖physicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode‖ ≤
      (primitiveTorusStokesScale *
        (6 * dyadicGradeLengthRatio (advectingGrade triad)
            (advectingLowHighGrade triad) *
          (dyadicRadius (advectingLowHighGrade triad) : ℝ) ^ 2) *
        (1 + primitiveTorusStokesScale *
          (6 * (dyadicRadius (advectingLowHighGrade triad) : ℝ) ^ 2))) *
        ‖triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode‖ := by
  have hbase := norm_physicalH2ExchangedTriadTransfer_le_explicit_cubeScale
    triad
    (dyadicRadius (advectingGrade triad))
    (dyadicRadius (advectingLowHighGrade triad))
    advectingMode transportedMode receiverMode hdivergence
    (frequencyDyadicGrade_mem triad.advecting)
    (transported_mem_advectingLowHighGradeCube triad)
    (receiver_mem_advectingLowHighGradeCube triad)
  calc
    ‖physicalH2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode‖ ≤
      (primitiveTorusStokesScale *
        (6 * (dyadicRadius (advectingGrade triad) : ℝ) *
          (dyadicRadius (advectingLowHighGrade triad) : ℝ)) *
        (1 + primitiveTorusStokesScale *
          (6 * (dyadicRadius (advectingLowHighGrade triad) : ℝ) ^ 2))) *
        ‖triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode‖ := hbase
    _ = (primitiveTorusStokesScale *
        (6 * dyadicGradeLengthRatio (advectingGrade triad)
            (advectingLowHighGrade triad) *
          (dyadicRadius (advectingLowHighGrade triad) : ℝ) ^ 2) *
        (1 + primitiveTorusStokesScale *
          (6 * (dyadicRadius (advectingLowHighGrade triad) : ℝ) ^ 2))) *
        ‖triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode‖ := by
      rw [show
        6 * (dyadicRadius (advectingGrade triad) : ℝ) *
            (dyadicRadius (advectingLowHighGrade triad) : ℝ) =
          6 * ((dyadicRadius (advectingGrade triad) : ℝ) *
            (dyadicRadius (advectingLowHighGrade triad) : ℝ)) by ring,
        dyadicGrade_low_mul_high_eq_ratio_mul_high_sq]
      ring

/-- Address specialization for any divergence-free velocity coefficient section. -/
theorem norm_physicalH2VelocityExchangedTriadFace_le_advectingLowGradeRatio
    (velocityMode : SpatialFrequency → ComplexVector)
    (address : CompleteTransportAddress)
    (hdivergence :
      complexDot (complexFrequencyVector address.1) (velocityMode address.1) = 0)
    (hsector : AdvectingLowSector (completeTransportTriad address)) :
    ‖physicalH2VelocityExchangedTriadFace velocityMode address‖ ≤
      (primitiveTorusStokesScale *
        (6 * dyadicGradeLengthRatio
            (advectingGrade (completeTransportTriad address))
            (advectingLowHighGrade (completeTransportTriad address)) *
          (dyadicRadius
            (advectingLowHighGrade (completeTransportTriad address)) : ℝ) ^ 2) *
        (1 + torusStokesEigenvalue address.2 +
          torusStokesEigenvalue (completeTransportReceiver address))) *
        ‖triadicEnergyFace address.1 address.2
          (velocityMode address.1) (velocityMode address.2)
          (velocityMode (completeTransportReceiver address))‖ := by
  exact norm_physicalH2ExchangedTriadTransfer_le_advectingLowGradeRatio
    (completeTransportTriad address)
    (velocityMode address.1)
    (velocityMode address.2)
    (velocityMode (completeTransportReceiver address))
    hdivergence hsector

/-- Literal open-solution specialization; divergence freedom is discharged by the admitted PDE
carrier, while every mode occurrence remains visible in the receiver. -/
theorem norm_openPhysicalH2VelocityExchangedTriadFace_le_advectingLowGradeRatio
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (address : CompleteTransportAddress)
    (hsector : AdvectingLowSector (completeTransportTriad address)) :
    ‖physicalH2VelocityExchangedTriadFace
        (openPeriodicVelocityFourierMode solution t) address‖ ≤
      (primitiveTorusStokesScale *
        (6 * dyadicGradeLengthRatio
            (advectingGrade (completeTransportTriad address))
            (advectingLowHighGrade (completeTransportTriad address)) *
          (dyadicRadius
            (advectingLowHighGrade (completeTransportTriad address)) : ℝ) ^ 2) *
        (1 + torusStokesEigenvalue address.2 +
          torusStokesEigenvalue (completeTransportReceiver address))) *
        ‖triadicEnergyFace address.1 address.2
          (openPeriodicVelocityFourierMode solution t address.1)
          (openPeriodicVelocityFourierMode solution t address.2)
          (openPeriodicVelocityFourierMode solution t
            (completeTransportReceiver address))‖ := by
  exact norm_physicalH2VelocityExchangedTriadFace_le_advectingLowGradeRatio
    (openPeriodicVelocityFourierMode solution t) address
    (openPeriodicVelocityFourierMode_divergenceFree solution t address.1) hsector

section Audit

#print axioms norm_physicalH2ExchangedTriadTransfer_le_advectingLowGradeRatio
#print axioms norm_physicalH2ExchangedTriadTransfer_le_explicit_advectingLowGradeRatio
#print axioms norm_physicalH2VelocityExchangedTriadFace_le_advectingLowGradeRatio
#print axioms norm_openPhysicalH2VelocityExchangedTriadFace_le_advectingLowGradeRatio

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityGradeLeverBound
