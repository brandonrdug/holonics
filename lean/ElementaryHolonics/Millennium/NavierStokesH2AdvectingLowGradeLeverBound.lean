import ElementaryHolonics.Millennium.NavierStokesPhysicalH2CurrentSectorJoin
import ElementaryHolonics.Millennium.NavierStokesH2TriadShellLeverBound

/-!
# Least-grade H2 lever on the complete advecting-low sector

**[proved-derived; formal-checked]** The least dyadic frequency grade is used directly: grade
zero is the unit low-frequency cube, and every positive grade is its corresponding sharp shell.
For an advecting-low closed triad, the common high aperture is the maximum of the transported and
receiver grades. Both high pins lie in that cube, while their actual grades remain distinct data
and closure forces them to be equal or adjacent.

The exact exchanged `H2` multiplier swing is then bounded by the retained low/high grade-length
ratio times the square of the common high aperture. This owner remains in the vorticity chart and
specializes pointwise to the actual exchanged transport face. It forms no population sum and
asserts no time or continuation consequence.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradeLeverBound

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCofinalOutputReceiverClosure
open Soma.Holonics.Millennium.NavierStokesCompleteDyadicTriadSectorPartition
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesH2TriadShellLeverBound
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurrentTriadJoin
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Direct least-grade length ratio -/

def dyadicGradeLengthRatio (lowGrade highGrade : ℕ) : ℝ :=
  (dyadicRadius lowGrade : ℝ) / (dyadicRadius highGrade : ℝ)

theorem dyadicGradeLengthRatio_eq_half_pow
    {lowGrade highGrade : ℕ} (hlowHigh : lowGrade ≤ highGrade) :
    dyadicGradeLengthRatio lowGrade highGrade =
      ((1 : ℝ) / 2) ^ (highGrade - lowGrade) := by
  have hgrade : highGrade = lowGrade + (highGrade - lowGrade) := by omega
  have hbase : (2 : ℝ) ^ lowGrade ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold dyadicGradeLengthRatio dyadicRadius
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [show (2 : ℝ) ^ highGrade =
      (2 : ℝ) ^ lowGrade * (2 : ℝ) ^ (highGrade - lowGrade) by
    calc
      (2 : ℝ) ^ highGrade =
          (2 : ℝ) ^ (lowGrade + (highGrade - lowGrade)) :=
        congrArg ((2 : ℝ) ^ ·) hgrade
      _ = _ := pow_add _ _ _]
  calc
    (2 : ℝ) ^ lowGrade /
        ((2 : ℝ) ^ lowGrade * (2 : ℝ) ^ (highGrade - lowGrade)) =
      1 / (2 : ℝ) ^ (highGrade - lowGrade) := by field_simp
    _ = ((1 : ℝ) / 2) ^ (highGrade - lowGrade) := by
      rw [div_pow]
      simp

theorem dyadicGradeLengthRatio_lt_one
    {lowGrade highGrade : ℕ} (hlowHigh : lowGrade < highGrade) :
    dyadicGradeLengthRatio lowGrade highGrade < 1 := by
  rw [dyadicGradeLengthRatio_eq_half_pow hlowHigh.le]
  have hdifference : 0 < highGrade - lowGrade := Nat.sub_pos_of_lt hlowHigh
  exact pow_lt_one₀ (by norm_num) (by norm_num) hdifference.ne'

theorem dyadicGrade_low_mul_high_eq_ratio_mul_high_sq
    (lowGrade highGrade : ℕ) :
    (dyadicRadius lowGrade : ℝ) * (dyadicRadius highGrade : ℝ) =
      dyadicGradeLengthRatio lowGrade highGrade *
        (dyadicRadius highGrade : ℝ) ^ 2 := by
  unfold dyadicGradeLengthRatio
  have hhighPositive : 0 < dyadicRadius highGrade := by
    unfold dyadicRadius
    positivity
  have hhighNonzero : (dyadicRadius highGrade : ℝ) ≠ 0 := by
    exact_mod_cast hhighPositive.ne'
  field_simp [hhighNonzero]

/-! ## Advecting-low least-grade geometry -/

def advectingLowHighGrade (triad : AddressedClosedFourierTriad) : ℕ :=
  max (transportedGrade triad) (receiverGrade triad)

theorem advectingLowSector_lowGrade_lt_highGrade
    {triad : AddressedClosedFourierTriad}
    (hsector : AdvectingLowSector triad) :
    advectingGrade triad < advectingLowHighGrade triad := by
  unfold advectingLowHighGrade
  exact lt_of_lt_of_le hsector.1 (Nat.le_max_left _ _)

theorem advectingLowSector_gradeRatio_lt_one
    {triad : AddressedClosedFourierTriad}
    (hsector : AdvectingLowSector triad) :
    dyadicGradeLengthRatio (advectingGrade triad)
        (advectingLowHighGrade triad) < 1 :=
  dyadicGradeLengthRatio_lt_one
    (advectingLowSector_lowGrade_lt_highGrade hsector)

theorem transported_mem_advectingLowHighGradeCube
    (triad : AddressedClosedFourierTriad) :
    triad.transported ∈
      frequencyCube (dyadicRadius (advectingLowHighGrade triad)) := by
  apply (frequencyDyadicGrade_le_iff_mem triad.transported
    (advectingLowHighGrade triad)).mp
  exact Nat.le_max_left _ _

theorem receiver_mem_advectingLowHighGradeCube
    (triad : AddressedClosedFourierTriad) :
    triad.receiver ∈
      frequencyCube (dyadicRadius (advectingLowHighGrade triad)) := by
  apply (frequencyDyadicGrade_le_iff_mem triad.receiver
    (advectingLowHighGrade triad)).mp
  exact Nat.le_max_right _ _

theorem advectingLowSector_highPins_mem_highGradeCube
    {triad : AddressedClosedFourierTriad}
    (_hsector : AdvectingLowSector triad) :
    triad.transported ∈
        frequencyCube (dyadicRadius (advectingLowHighGrade triad)) ∧
      triad.receiver ∈
        frequencyCube (dyadicRadius (advectingLowHighGrade triad)) :=
  ⟨transported_mem_advectingLowHighGradeCube triad,
    receiver_mem_advectingLowHighGradeCube triad⟩

theorem advectingLowSector_highGradeDifference_le_one
    {triad : AddressedClosedFourierTriad}
    (hsector : AdvectingLowSector triad) :
    transportedGrade triad ≤ receiverGrade triad + 1 ∧
      receiverGrade triad ≤ transportedGrade triad + 1 :=
  advectingLowSector_highGrades_proximate hsector

theorem advectingLowSector_lowGrade_zero_iff_lowFrequencyMode
    {triad : AddressedClosedFourierTriad}
    (_hsector : AdvectingLowSector triad) :
    advectingGrade triad = 0 ↔ triad.advecting ∈ lowFrequencyModes := by
  exact frequencyDyadicGrade_eq_zero_iff triad.advecting

/-! ## Pointwise vorticity-chart H2 lever -/

theorem norm_h2ExchangedTriadTransfer_le_advectingLowGradeRatio
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (_hsector : AdvectingLowSector triad) :
    ‖h2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode‖ ≤
      (primitiveTorusStokesScale *
        (6 * dyadicGradeLengthRatio (advectingGrade triad)
            (advectingLowHighGrade triad) *
          (dyadicRadius (advectingLowHighGrade triad) : ℝ) ^ 2)) *
        ‖triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode‖ := by
  have hbase := norm_h2ExchangedTriadTransfer_le_six_mul_cubeRadii
    triad
    (dyadicRadius (advectingGrade triad))
    (dyadicRadius (advectingLowHighGrade triad))
    advectingMode transportedMode receiverMode hdivergence
    (frequencyDyadicGrade_mem triad.advecting)
    (transported_mem_advectingLowHighGradeCube triad)
    (receiver_mem_advectingLowHighGradeCube triad)
  calc
    ‖h2ExchangedTriadTransfer triad
        advectingMode transportedMode receiverMode‖ ≤
      (primitiveTorusStokesScale *
        (6 * (dyadicRadius (advectingGrade triad) : ℝ) *
          (dyadicRadius (advectingLowHighGrade triad) : ℝ))) *
        ‖triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode‖ := hbase
    _ = (primitiveTorusStokesScale *
        (6 * dyadicGradeLengthRatio (advectingGrade triad)
            (advectingLowHighGrade triad) *
          (dyadicRadius (advectingLowHighGrade triad) : ℝ) ^ 2)) *
        ‖triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode‖ := by
      rw [show
        6 * (dyadicRadius (advectingGrade triad) : ℝ) *
            (dyadicRadius (advectingLowHighGrade triad) : ℝ) =
          6 * ((dyadicRadius (advectingGrade triad) : ℝ) *
            (dyadicRadius (advectingLowHighGrade triad) : ℝ)) by ring,
        dyadicGrade_low_mul_high_eq_ratio_mul_high_sq]
      ring

/-! ## Actual solution face -/

theorem norm_completePhysicalH2ExchangedTransportFace_le_advectingLowGradeRatio
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (address : CompleteTransportAddress)
    (hsector : AdvectingLowSector (completeTransportTriad address)) :
    ‖completePhysicalH2ExchangedTransportFace solution t address‖ ≤
      (primitiveTorusStokesScale *
        (6 * dyadicGradeLengthRatio
            (advectingGrade (completeTransportTriad address))
            (advectingLowHighGrade (completeTransportTriad address)) *
          (dyadicRadius
            (advectingLowHighGrade (completeTransportTriad address)) : ℝ) ^ 2)) *
        ‖completeOpenVorticityTransportFace solution t address‖ := by
  have hdivergence := openPeriodicVelocityFourierMode_divergenceFree
    solution t address.1
  change
    ‖h2ExchangedTriadTransfer (completeTransportTriad address)
      (openPeriodicVelocityFourierMode solution t address.1)
      (openPeriodicVorticityFourierMode solution t address.2)
      (openPeriodicVorticityFourierMode solution t
        (completeTransportReceiver address))‖ ≤ _
  exact norm_h2ExchangedTriadTransfer_le_advectingLowGradeRatio
    (completeTransportTriad address)
    (openPeriodicVelocityFourierMode solution t address.1)
    (openPeriodicVorticityFourierMode solution t address.2)
    (openPeriodicVorticityFourierMode solution t
      (completeTransportReceiver address))
    hdivergence hsector

theorem abs_re_completePhysicalH2ExchangedTransportFace_le_advectingLowGradeRatio
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (address : CompleteTransportAddress)
    (hsector : AdvectingLowSector (completeTransportTriad address)) :
    |(completePhysicalH2ExchangedTransportFace solution t address).re| ≤
      (primitiveTorusStokesScale *
        (6 * dyadicGradeLengthRatio
            (advectingGrade (completeTransportTriad address))
            (advectingLowHighGrade (completeTransportTriad address)) *
          (dyadicRadius
            (advectingLowHighGrade (completeTransportTriad address)) : ℝ) ^ 2)) *
        ‖completeOpenVorticityTransportFace solution t address‖ := by
  exact (Complex.abs_re_le_norm _).trans
    (norm_completePhysicalH2ExchangedTransportFace_le_advectingLowGradeRatio
      solution t address hsector)

section Audit

#print axioms dyadicGradeLengthRatio_eq_half_pow
#print axioms dyadicGradeLengthRatio_lt_one
#print axioms dyadicGrade_low_mul_high_eq_ratio_mul_high_sq
#print axioms advectingLowSector_lowGrade_lt_highGrade
#print axioms advectingLowSector_highPins_mem_highGradeCube
#print axioms advectingLowSector_highGradeDifference_le_one
#print axioms norm_h2ExchangedTriadTransfer_le_advectingLowGradeRatio
#print axioms norm_completePhysicalH2ExchangedTransportFace_le_advectingLowGradeRatio
#print axioms abs_re_completePhysicalH2ExchangedTransportFace_le_advectingLowGradeRatio

end Audit

end Soma.Holonics.Millennium.NavierStokesH2AdvectingLowGradeLeverBound
