import ElementaryHolonics.Millennium.NavierStokesH2TriadMultiplierSwing
import ElementaryHolonics.Millennium.NavierStokesDyadicShellProjectors
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionRemainderBound

/-!
# Scale-local bounds for the exact H2 triad multiplier swing

**[proved-derived; formal-checked]**  The predecessor keeps the exchanged H2 pair signed until
divergence freedom cancels its common storage weight.  This owner places a quantitative receiver
on the surviving multiplier lever, still before any sum of absolute triad coefficients is formed.

The general estimate uses the existing three-coordinate frequency length.  A sharper cube-local
estimate then reads the low advecting pin and the two high exchanged pins through their actual
coordinate apertures.  On a dyadic high--high--low triad the intrinsic Stokes lever therefore
costs one low length times one high length, rather than two high lengths.  Equal-radius exchanged
pins lie in the exact null fibre.

These are single-triad and finite-aperture inequalities.  They do not sum the infinite nonlinear
production current and do not establish a Navier--Stokes continuation theorem.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesH2TriadShellLeverBound

open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH2TriadMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.Turn

/-! ## Length receiver for the exact pairing swing -/

/-- The real frequency pairing is controlled by the already-founded three-coordinate absolute
lengths.  This receiver is deliberately taken before any population sum. -/
theorem abs_frequencyPairing_le_frequencyL1_mul_frequencyL1
    (left right : SpatialFrequency) :
    |frequencyPairing left right| ≤ frequencyL1 left * frequencyL1 right := by
  have htriangle :
      |(left 0 : ℝ) * (right 0 : ℝ) +
          (left 1 : ℝ) * (right 1 : ℝ) +
            (left 2 : ℝ) * (right 2 : ℝ)| ≤
        |(left 0 : ℝ) * (right 0 : ℝ)| +
          |(left 1 : ℝ) * (right 1 : ℝ)| +
            |(left 2 : ℝ) * (right 2 : ℝ)| := by
    calc
      |(left 0 : ℝ) * (right 0 : ℝ) +
          (left 1 : ℝ) * (right 1 : ℝ) +
            (left 2 : ℝ) * (right 2 : ℝ)| ≤
          |(left 0 : ℝ) * (right 0 : ℝ) +
            (left 1 : ℝ) * (right 1 : ℝ)| +
              |(left 2 : ℝ) * (right 2 : ℝ)| := abs_add_le _ _
      _ ≤ (|(left 0 : ℝ) * (right 0 : ℝ)| +
              |(left 1 : ℝ) * (right 1 : ℝ)|) +
            |(left 2 : ℝ) * (right 2 : ℝ)| := by
        linarith [abs_add_le ((left 0 : ℝ) * (right 0 : ℝ))
          ((left 1 : ℝ) * (right 1 : ℝ))]
      _ = |(left 0 : ℝ) * (right 0 : ℝ)| +
          |(left 1 : ℝ) * (right 1 : ℝ)| +
            |(left 2 : ℝ) * (right 2 : ℝ)| := by ring
  rw [show frequencyPairing left right =
      (left 0 : ℝ) * (right 0 : ℝ) +
        (left 1 : ℝ) * (right 1 : ℝ) +
          (left 2 : ℝ) * (right 2 : ℝ) by
    simp [frequencyPairing, Fin.sum_univ_succ, add_assoc]]
  refine htriangle.trans ?_
  rw [abs_mul, abs_mul, abs_mul]
  unfold frequencyL1
  nlinarith [abs_nonneg (left 0 : ℝ), abs_nonneg (left 1 : ℝ),
    abs_nonneg (left 2 : ℝ), abs_nonneg (right 0 : ℝ),
    abs_nonneg (right 1 : ℝ), abs_nonneg (right 2 : ℝ),
    mul_nonneg (abs_nonneg (left 0 : ℝ)) (abs_nonneg (right 1 : ℝ)),
    mul_nonneg (abs_nonneg (left 0 : ℝ)) (abs_nonneg (right 2 : ℝ)),
    mul_nonneg (abs_nonneg (left 1 : ℝ)) (abs_nonneg (right 0 : ℝ)),
    mul_nonneg (abs_nonneg (left 1 : ℝ)) (abs_nonneg (right 2 : ℝ)),
    mul_nonneg (abs_nonneg (left 2 : ℝ)) (abs_nonneg (right 0 : ℝ)),
    mul_nonneg (abs_nonneg (left 2 : ℝ)) (abs_nonneg (right 1 : ℝ))]

/-- The exact exchanged pairing lever costs one advecting frequency length and the sum of the two
exchanged lengths. -/
theorem abs_advectingPairingSwing_le_frequencyL1
    (triad : AddressedClosedFourierTriad) :
    |frequencyPairing triad.advecting triad.receiver -
        frequencyPairing triad.advecting triad.transported| ≤
      frequencyL1 triad.advecting *
        (frequencyL1 triad.receiver + frequencyL1 triad.transported) := by
  calc
    |frequencyPairing triad.advecting triad.receiver -
        frequencyPairing triad.advecting triad.transported| ≤
      |frequencyPairing triad.advecting triad.receiver| +
        |frequencyPairing triad.advecting triad.transported| := abs_sub _ _
    _ ≤ frequencyL1 triad.advecting * frequencyL1 triad.receiver +
        frequencyL1 triad.advecting * frequencyL1 triad.transported :=
      add_le_add
        (abs_frequencyPairing_le_frequencyL1_mul_frequencyL1 _ _)
        (abs_frequencyPairing_le_frequencyL1_mul_frequencyL1 _ _)
    _ = frequencyL1 triad.advecting *
        (frequencyL1 triad.receiver + frequencyL1 triad.transported) := by ring

/-- Intrinsic full-turn calibration converts the pairing bound into the H2 Stokes-coordinate
bound without selecting a numerical circle chart. -/
theorem abs_calibratedTorusStokesEigenvalue_difference_le_frequencyL1
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (triad : AddressedClosedFourierTriad) :
    |calibratedTorusStokesEigenvalue calibration triad.transported -
        calibratedTorusStokesEigenvalue calibration triad.receiver| ≤
      calibratedStokesScale calibration * frequencyL1 triad.advecting *
        (frequencyL1 triad.receiver + frequencyL1 triad.transported) := by
  have hscale : 0 ≤ calibratedStokesScale calibration := by
    unfold calibratedStokesScale
    exact sq_nonneg _
  rw [calibratedTorusStokesEigenvalue_transported_sub_receiver, abs_mul,
    abs_of_nonneg hscale]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (abs_advectingPairingSwing_le_frequencyL1 triad) hscale

/-- The same lever bound in the standing torus chart, expressed through the internally measured
primitive-character scale. -/
theorem abs_torusStokesEigenvalue_difference_le_frequencyL1
    (triad : AddressedClosedFourierTriad) :
    |torusStokesEigenvalue triad.transported -
        torusStokesEigenvalue triad.receiver| ≤
      primitiveTorusStokesScale * frequencyL1 triad.advecting *
        (frequencyL1 triad.receiver + frequencyL1 triad.transported) := by
  rw [torusStokesEigenvalue_transported_sub_receiver, abs_mul,
    abs_of_pos primitiveTorusStokesScale_pos]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (abs_advectingPairingSwing_le_frequencyL1 triad)
    primitiveTorusStokesScale_pos.le

/-! ## Sharp coordinate-cube and dyadic high--high--low bounds -/

/-- Membership in a genuine frequency cube bounds every real coordinate by its aperture radius. -/
theorem abs_frequency_coordinate_le_radius_of_mem_frequencyCube
    {radius : ℕ} {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube radius) (coordinate : Fin 3) :
    |(frequency coordinate : ℝ)| ≤ (radius : ℝ) := by
  have hcoordinate := (mem_frequencyCube_iff radius frequency).mp hfrequency coordinate
  have hlower : -(radius : ℝ) ≤ (frequency coordinate : ℝ) := by
    exact_mod_cast hcoordinate.1
  have hupper : (frequency coordinate : ℝ) ≤ (radius : ℝ) := by
    exact_mod_cast hcoordinate.2
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Two cube-local pins have pairing at most three times the product of their coordinate radii. -/
theorem abs_frequencyPairing_le_three_mul_cubeRadii
    {leftRadius rightRadius : ℕ} {left right : SpatialFrequency}
    (hleft : left ∈ frequencyCube leftRadius)
    (hright : right ∈ frequencyCube rightRadius) :
    |frequencyPairing left right| ≤
      3 * (leftRadius : ℝ) * (rightRadius : ℝ) := by
  have hterm : ∀ coordinate : Fin 3,
      |(left coordinate : ℝ) * (right coordinate : ℝ)| ≤
        (leftRadius : ℝ) * (rightRadius : ℝ) := by
    intro coordinate
    rw [abs_mul]
    exact mul_le_mul
      (abs_frequency_coordinate_le_radius_of_mem_frequencyCube hleft coordinate)
      (abs_frequency_coordinate_le_radius_of_mem_frequencyCube hright coordinate)
      (abs_nonneg _) (Nat.cast_nonneg _)
  rw [show frequencyPairing left right =
      (left 0 : ℝ) * (right 0 : ℝ) +
        (left 1 : ℝ) * (right 1 : ℝ) +
          (left 2 : ℝ) * (right 2 : ℝ) by
    simp [frequencyPairing, Fin.sum_univ_succ, add_assoc]]
  calc
    |(left 0 : ℝ) * (right 0 : ℝ) +
        (left 1 : ℝ) * (right 1 : ℝ) +
          (left 2 : ℝ) * (right 2 : ℝ)| ≤
      |(left 0 : ℝ) * (right 0 : ℝ)| +
        |(left 1 : ℝ) * (right 1 : ℝ)| +
          |(left 2 : ℝ) * (right 2 : ℝ)| := by
      calc
        |(left 0 : ℝ) * (right 0 : ℝ) +
            (left 1 : ℝ) * (right 1 : ℝ) +
              (left 2 : ℝ) * (right 2 : ℝ)| ≤
          |(left 0 : ℝ) * (right 0 : ℝ) +
            (left 1 : ℝ) * (right 1 : ℝ)| +
              |(left 2 : ℝ) * (right 2 : ℝ)| := abs_add_le _ _
        _ ≤ (|(left 0 : ℝ) * (right 0 : ℝ)| +
                |(left 1 : ℝ) * (right 1 : ℝ)|) +
              |(left 2 : ℝ) * (right 2 : ℝ)| := by
          linarith [abs_add_le ((left 0 : ℝ) * (right 0 : ℝ))
            ((left 1 : ℝ) * (right 1 : ℝ))]
        _ = _ := by ring
    _ ≤ 3 * (leftRadius : ℝ) * (rightRadius : ℝ) := by
      have h0 := hterm 0
      have h1 := hterm 1
      have h2 := hterm 2
      linarith

/-- With one low cube and two common high cubes, the exact exchanged lever is bounded by six low
times high coordinate lengths. -/
theorem abs_advectingPairingSwing_le_six_mul_cubeRadii
    (triad : AddressedClosedFourierTriad) (lowRadius highRadius : ℕ)
    (hadvecting : triad.advecting ∈ frequencyCube lowRadius)
    (htransported : triad.transported ∈ frequencyCube highRadius)
    (hreceiver : triad.receiver ∈ frequencyCube highRadius) :
    |frequencyPairing triad.advecting triad.receiver -
        frequencyPairing triad.advecting triad.transported| ≤
      6 * (lowRadius : ℝ) * (highRadius : ℝ) := by
  calc
    |frequencyPairing triad.advecting triad.receiver -
        frequencyPairing triad.advecting triad.transported| ≤
      |frequencyPairing triad.advecting triad.receiver| +
        |frequencyPairing triad.advecting triad.transported| := abs_sub _ _
    _ ≤ 3 * (lowRadius : ℝ) * (highRadius : ℝ) +
        3 * (lowRadius : ℝ) * (highRadius : ℝ) :=
      add_le_add
        (abs_frequencyPairing_le_three_mul_cubeRadii hadvecting hreceiver)
        (abs_frequencyPairing_le_three_mul_cubeRadii hadvecting htransported)
    _ = 6 * (lowRadius : ℝ) * (highRadius : ℝ) := by ring

/-- Calibrated Stokes difference for a cube-local high--high--low interaction. -/
theorem abs_calibratedTorusStokesEigenvalue_difference_le_six_mul_cubeRadii
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (triad : AddressedClosedFourierTriad) (lowRadius highRadius : ℕ)
    (hadvecting : triad.advecting ∈ frequencyCube lowRadius)
    (htransported : triad.transported ∈ frequencyCube highRadius)
    (hreceiver : triad.receiver ∈ frequencyCube highRadius) :
    |calibratedTorusStokesEigenvalue calibration triad.transported -
        calibratedTorusStokesEigenvalue calibration triad.receiver| ≤
      calibratedStokesScale calibration *
        (6 * (lowRadius : ℝ) * (highRadius : ℝ)) := by
  have hscale : 0 ≤ calibratedStokesScale calibration := by
    unfold calibratedStokesScale
    exact sq_nonneg _
  rw [calibratedTorusStokesEigenvalue_transported_sub_receiver, abs_mul,
    abs_of_nonneg hscale]
  exact mul_le_mul_of_nonneg_left
    (abs_advectingPairingSwing_le_six_mul_cubeRadii triad lowRadius highRadius
      hadvecting htransported hreceiver)
    hscale

/-- The same cube-local high--high--low bound for the actual standing torus Stokes operator. -/
theorem abs_torusStokesEigenvalue_difference_le_six_mul_cubeRadii
    (triad : AddressedClosedFourierTriad) (lowRadius highRadius : ℕ)
    (hadvecting : triad.advecting ∈ frequencyCube lowRadius)
    (htransported : triad.transported ∈ frequencyCube highRadius)
    (hreceiver : triad.receiver ∈ frequencyCube highRadius) :
    |torusStokesEigenvalue triad.transported -
        torusStokesEigenvalue triad.receiver| ≤
      primitiveTorusStokesScale *
        (6 * (lowRadius : ℝ) * (highRadius : ℝ)) := by
  rw [torusStokesEigenvalue_transported_sub_receiver, abs_mul,
    abs_of_pos primitiveTorusStokesScale_pos]
  exact mul_le_mul_of_nonneg_left
    (abs_advectingPairingSwing_le_six_mul_cubeRadii triad lowRadius highRadius
      hadvecting htransported hreceiver)
    primitiveTorusStokesScale_pos.le

/-- The sharp-shell receiver supplies the cube hypotheses automatically.  Scale separation is
retained explicitly as the high--high--low classification; the quantitative lever remembers both
dyadic lengths instead of collapsing them to the high scale. -/
theorem abs_calibratedTorusStokesEigenvalue_difference_le_of_highHighLowDyadic
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (triad : AddressedClosedFourierTriad) (lowLevel highLevel : ℕ)
    (_hseparated : lowLevel + 1 ≤ highLevel)
    (hadvecting : triad.advecting ∈ dyadicFrequencyShell lowLevel)
    (htransported : triad.transported ∈ dyadicFrequencyShell highLevel)
    (hreceiver : triad.receiver ∈ dyadicFrequencyShell highLevel) :
    |calibratedTorusStokesEigenvalue calibration triad.transported -
        calibratedTorusStokesEigenvalue calibration triad.receiver| ≤
      calibratedStokesScale calibration *
        (6 * (dyadicRadius (lowLevel + 1) : ℝ) *
          (dyadicRadius (highLevel + 1) : ℝ)) := by
  exact abs_calibratedTorusStokesEigenvalue_difference_le_six_mul_cubeRadii
    calibration triad (dyadicRadius (lowLevel + 1)) (dyadicRadius (highLevel + 1))
    ((mem_dyadicFrequencyShell_iff lowLevel triad.advecting).mp hadvecting).1
    ((mem_dyadicFrequencyShell_iff highLevel triad.transported).mp htransported).1
    ((mem_dyadicFrequencyShell_iff highLevel triad.receiver).mp hreceiver).1

/-- Actual standing-torus version of the high--high--low dyadic lever bound. -/
theorem abs_torusStokesEigenvalue_difference_le_of_highHighLowDyadic
    (triad : AddressedClosedFourierTriad) (lowLevel highLevel : ℕ)
    (_hseparated : lowLevel + 1 ≤ highLevel)
    (hadvecting : triad.advecting ∈ dyadicFrequencyShell lowLevel)
    (htransported : triad.transported ∈ dyadicFrequencyShell highLevel)
    (hreceiver : triad.receiver ∈ dyadicFrequencyShell highLevel) :
    |torusStokesEigenvalue triad.transported -
        torusStokesEigenvalue triad.receiver| ≤
      primitiveTorusStokesScale *
        (6 * (dyadicRadius (lowLevel + 1) : ℝ) *
          (dyadicRadius (highLevel + 1) : ℝ)) := by
  exact abs_torusStokesEigenvalue_difference_le_six_mul_cubeRadii
    triad (dyadicRadius (lowLevel + 1)) (dyadicRadius (highLevel + 1))
    ((mem_dyadicFrequencyShell_iff lowLevel triad.advecting).mp hadvecting).1
    ((mem_dyadicFrequencyShell_iff highLevel triad.transported).mp htransported).1
    ((mem_dyadicFrequencyShell_iff highLevel triad.receiver).mp hreceiver).1

/-! ## The retained dyadic gain -/

/-- Ratio of the low outer shell length to the high outer shell length.  This is a receiver face
of the two distinct lengths, not an identification of their shells. -/
def dyadicLowHighLengthRatio (lowLevel highLevel : ℕ) : ℝ :=
  (dyadicRadius (lowLevel + 1) : ℝ) /
    (dyadicRadius (highLevel + 1) : ℝ)

/-- Genuine high--high--low separation makes the retained length ratio strictly smaller than one. -/
theorem dyadicLowHighLengthRatio_lt_one
    {lowLevel highLevel : ℕ} (hseparated : lowLevel + 1 ≤ highLevel) :
    dyadicLowHighLengthRatio lowLevel highLevel < 1 := by
  have hexponents : lowLevel + 1 < highLevel + 1 := Nat.lt_succ_of_le hseparated
  have hradiiNat : dyadicRadius (lowLevel + 1) < dyadicRadius (highLevel + 1) := by
    unfold dyadicRadius
    exact Nat.pow_lt_pow_right (by norm_num) hexponents
  have hradiiReal :
      (dyadicRadius (lowLevel + 1) : ℝ) <
        (dyadicRadius (highLevel + 1) : ℝ) := by
    exact_mod_cast hradiiNat
  have hhighNat : 0 < dyadicRadius (highLevel + 1) := by
    unfold dyadicRadius
    exact pow_pos (by norm_num) _
  have hhighReal : 0 < (dyadicRadius (highLevel + 1) : ℝ) := by
    exact_mod_cast hhighNat
  exact (div_lt_one hhighReal).2 hradiiReal

/-- The low-times-high lever is exactly the high-square scale multiplied by the retained dyadic
length ratio.  This is the formal scale gain which would be lost by replacing both pins with the
high aperture before cancellation. -/
theorem dyadic_low_mul_high_eq_ratio_mul_high_sq
    (lowLevel highLevel : ℕ) :
    (dyadicRadius (lowLevel + 1) : ℝ) *
        (dyadicRadius (highLevel + 1) : ℝ) =
      dyadicLowHighLengthRatio lowLevel highLevel *
        (dyadicRadius (highLevel + 1) : ℝ) ^ 2 := by
  unfold dyadicLowHighLengthRatio
  have hhighNat : 0 < dyadicRadius (highLevel + 1) := by
    unfold dyadicRadius
    exact pow_pos (by norm_num) _
  have hhigh : (dyadicRadius (highLevel + 1) : ℝ) ≠ 0 := by
    exact_mod_cast hhighNat.ne'
  field_simp [hhigh]

/-! ## The norm receiver is applied only after exact exchanged cancellation -/

/-- After the exchanged signed pair has collapsed to its exact multiplier swing, its norm is
controlled by the intrinsic length lever times the still-oriented triadic face. -/
theorem norm_calibratedH2ExchangedTriadTransfer_le_frequencyL1
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    ‖calibratedH2ExchangedTriadTransfer calibration triad
        advectingMode transportedMode receiverMode‖ ≤
      (calibratedStokesScale calibration * frequencyL1 triad.advecting *
        (frequencyL1 triad.receiver + frequencyL1 triad.transported)) *
          ‖triadicEnergyFace triad.advecting triad.transported
            advectingMode transportedMode receiverMode‖ := by
  rw [calibratedH2ExchangedTriadTransfer_eq_stokesDifference_mul
    calibration triad advectingMode transportedMode receiverMode hdivergence,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (abs_calibratedTorusStokesEigenvalue_difference_le_frequencyL1 calibration triad)
    (norm_nonneg _)

/-- Actual standing-torus H2 transfer bound through the same exact pre-mass length lever. -/
theorem norm_h2ExchangedTriadTransfer_le_frequencyL1
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    ‖h2ExchangedTriadTransfer triad advectingMode transportedMode receiverMode‖ ≤
      (primitiveTorusStokesScale * frequencyL1 triad.advecting *
        (frequencyL1 triad.receiver + frequencyL1 triad.transported)) *
          ‖triadicEnergyFace triad.advecting triad.transported
            advectingMode transportedMode receiverMode‖ := by
  rw [h2ExchangedTriadTransfer_eq_stokesDifference_mul
    triad advectingMode transportedMode receiverMode hdivergence,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (abs_torusStokesEigenvalue_difference_le_frequencyL1 triad)
    (norm_nonneg _)

/-- Cube-local norm bound for the complete exchanged H2 transfer after cancellation. -/
theorem norm_calibratedH2ExchangedTriadTransfer_le_six_mul_cubeRadii
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (triad : AddressedClosedFourierTriad) (lowRadius highRadius : ℕ)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (hadvecting : triad.advecting ∈ frequencyCube lowRadius)
    (htransported : triad.transported ∈ frequencyCube highRadius)
    (hreceiver : triad.receiver ∈ frequencyCube highRadius) :
    ‖calibratedH2ExchangedTriadTransfer calibration triad
        advectingMode transportedMode receiverMode‖ ≤
      (calibratedStokesScale calibration *
        (6 * (lowRadius : ℝ) * (highRadius : ℝ))) *
          ‖triadicEnergyFace triad.advecting triad.transported
            advectingMode transportedMode receiverMode‖ := by
  rw [calibratedH2ExchangedTriadTransfer_eq_stokesDifference_mul
    calibration triad advectingMode transportedMode receiverMode hdivergence,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (abs_calibratedTorusStokesEigenvalue_difference_le_six_mul_cubeRadii
      calibration triad lowRadius highRadius hadvecting htransported hreceiver)
    (norm_nonneg _)

/-- Actual standing-torus cube-local transfer bound after exact exchanged cancellation. -/
theorem norm_h2ExchangedTriadTransfer_le_six_mul_cubeRadii
    (triad : AddressedClosedFourierTriad) (lowRadius highRadius : ℕ)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (hadvecting : triad.advecting ∈ frequencyCube lowRadius)
    (htransported : triad.transported ∈ frequencyCube highRadius)
    (hreceiver : triad.receiver ∈ frequencyCube highRadius) :
    ‖h2ExchangedTriadTransfer triad advectingMode transportedMode receiverMode‖ ≤
      (primitiveTorusStokesScale *
        (6 * (lowRadius : ℝ) * (highRadius : ℝ))) *
          ‖triadicEnergyFace triad.advecting triad.transported
            advectingMode transportedMode receiverMode‖ := by
  rw [h2ExchangedTriadTransfer_eq_stokesDifference_mul
    triad advectingMode transportedMode receiverMode hdivergence,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (abs_torusStokesEigenvalue_difference_le_six_mul_cubeRadii
      triad lowRadius highRadius hadvecting htransported hreceiver)
    (norm_nonneg _)

/-- Dyadic high--high--low specialization of the calibrated transfer bound.  The low shell length
survives because the exchanged signed pair was combined before taking its norm. -/
theorem norm_calibratedH2ExchangedTriadTransfer_le_of_highHighLowDyadic
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (triad : AddressedClosedFourierTriad) (lowLevel highLevel : ℕ)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (_hseparated : lowLevel + 1 ≤ highLevel)
    (hadvecting : triad.advecting ∈ dyadicFrequencyShell lowLevel)
    (htransported : triad.transported ∈ dyadicFrequencyShell highLevel)
    (hreceiver : triad.receiver ∈ dyadicFrequencyShell highLevel) :
    ‖calibratedH2ExchangedTriadTransfer calibration triad
        advectingMode transportedMode receiverMode‖ ≤
      (calibratedStokesScale calibration *
        (6 * (dyadicRadius (lowLevel + 1) : ℝ) *
          (dyadicRadius (highLevel + 1) : ℝ))) *
            ‖triadicEnergyFace triad.advecting triad.transported
              advectingMode transportedMode receiverMode‖ := by
  exact norm_calibratedH2ExchangedTriadTransfer_le_six_mul_cubeRadii
    calibration triad (dyadicRadius (lowLevel + 1)) (dyadicRadius (highLevel + 1))
    advectingMode transportedMode receiverMode hdivergence
    ((mem_dyadicFrequencyShell_iff lowLevel triad.advecting).mp hadvecting).1
    ((mem_dyadicFrequencyShell_iff highLevel triad.transported).mp htransported).1
    ((mem_dyadicFrequencyShell_iff highLevel triad.receiver).mp hreceiver).1

/-- Actual standing-torus dyadic high--high--low transfer bound after exact cancellation. -/
theorem norm_h2ExchangedTriadTransfer_le_of_highHighLowDyadic
    (triad : AddressedClosedFourierTriad) (lowLevel highLevel : ℕ)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0)
    (_hseparated : lowLevel + 1 ≤ highLevel)
    (hadvecting : triad.advecting ∈ dyadicFrequencyShell lowLevel)
    (htransported : triad.transported ∈ dyadicFrequencyShell highLevel)
    (hreceiver : triad.receiver ∈ dyadicFrequencyShell highLevel) :
    ‖h2ExchangedTriadTransfer triad advectingMode transportedMode receiverMode‖ ≤
      (primitiveTorusStokesScale *
        (6 * (dyadicRadius (lowLevel + 1) : ℝ) *
          (dyadicRadius (highLevel + 1) : ℝ))) *
            ‖triadicEnergyFace triad.advecting triad.transported
              advectingMode transportedMode receiverMode‖ := by
  exact norm_h2ExchangedTriadTransfer_le_six_mul_cubeRadii
    triad (dyadicRadius (lowLevel + 1)) (dyadicRadius (highLevel + 1))
    advectingMode transportedMode receiverMode hdivergence
    ((mem_dyadicFrequencyShell_iff lowLevel triad.advecting).mp hadvecting).1
    ((mem_dyadicFrequencyShell_iff highLevel triad.transported).mp htransported).1
    ((mem_dyadicFrequencyShell_iff highLevel triad.receiver).mp hreceiver).1

/-! ## Same-radius null fibre -/

/-- Equal squared radius is exactly the zero fibre of the exchanged advecting-pairing swing. -/
theorem advectingPairingSwing_eq_zero_of_equal_frequencySquared
    (triad : AddressedClosedFourierTriad)
    (hradius : frequencySquared triad.transported = frequencySquared triad.receiver) :
    frequencyPairing triad.advecting triad.receiver -
        frequencyPairing triad.advecting triad.transported = 0 := by
  have hlever :=
    frequencySquared_transported_sub_receiver_eq_advecting_pairing_swing triad
  rw [hradius, sub_self] at hlever
  exact hlever.symm

/-- Equal-radius exchanged pins have zero intrinsic Stokes-coordinate lever before the amplitude
face or any norm receiver is consulted. -/
theorem calibratedTorusStokesEigenvalue_difference_eq_zero_of_equal_frequencySquared
    {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι)
    (triad : AddressedClosedFourierTriad)
    (hradius : frequencySquared triad.transported = frequencySquared triad.receiver) :
    calibratedTorusStokesEigenvalue calibration triad.transported -
        calibratedTorusStokesEigenvalue calibration triad.receiver = 0 := by
  rw [calibratedTorusStokesEigenvalue_transported_sub_receiver,
    advectingPairingSwing_eq_zero_of_equal_frequencySquared triad hradius, mul_zero]

/-- The standing torus Stokes lever has the same exact equal-radius null fibre. -/
theorem torusStokesEigenvalue_difference_eq_zero_of_equal_frequencySquared
    (triad : AddressedClosedFourierTriad)
    (hradius : frequencySquared triad.transported = frequencySquared triad.receiver) :
    torusStokesEigenvalue triad.transported -
        torusStokesEigenvalue triad.receiver = 0 := by
  rw [torusStokesEigenvalue_transported_sub_receiver,
    advectingPairingSwing_eq_zero_of_equal_frequencySquared triad hradius, mul_zero]

section Audit

#print axioms abs_frequencyPairing_le_frequencyL1_mul_frequencyL1
#print axioms abs_advectingPairingSwing_le_frequencyL1
#print axioms abs_calibratedTorusStokesEigenvalue_difference_le_frequencyL1
#print axioms abs_torusStokesEigenvalue_difference_le_frequencyL1
#print axioms abs_advectingPairingSwing_le_six_mul_cubeRadii
#print axioms abs_calibratedTorusStokesEigenvalue_difference_le_of_highHighLowDyadic
#print axioms abs_torusStokesEigenvalue_difference_le_of_highHighLowDyadic
#print axioms dyadicLowHighLengthRatio_lt_one
#print axioms dyadic_low_mul_high_eq_ratio_mul_high_sq
#print axioms norm_calibratedH2ExchangedTriadTransfer_le_frequencyL1
#print axioms norm_h2ExchangedTriadTransfer_le_frequencyL1
#print axioms norm_calibratedH2ExchangedTriadTransfer_le_six_mul_cubeRadii
#print axioms norm_h2ExchangedTriadTransfer_le_six_mul_cubeRadii
#print axioms norm_calibratedH2ExchangedTriadTransfer_le_of_highHighLowDyadic
#print axioms norm_h2ExchangedTriadTransfer_le_of_highHighLowDyadic
#print axioms advectingPairingSwing_eq_zero_of_equal_frequencySquared
#print axioms calibratedTorusStokesEigenvalue_difference_eq_zero_of_equal_frequencySquared
#print axioms torusStokesEigenvalue_difference_eq_zero_of_equal_frequencySquared

end Audit

end Soma.Holonics.Millennium.NavierStokesH2TriadShellLeverBound
