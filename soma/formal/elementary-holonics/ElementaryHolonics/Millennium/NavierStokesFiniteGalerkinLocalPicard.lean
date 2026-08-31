import ElementaryHolonics.Millennium.NavierStokesFinitePicardAncestryService
import Mathlib.Analysis.ODE.PicardLindelof

/-!
# A finite Galerkin local Picard solver

**[proved-derived; formal-checked]** The cumulative ancestry cone is fixed as one finite carrier
and every state is zero-extended outside it.  The resulting Galerkin vector field contains the
named diagonal Stokes rate and the existing finite advective--Leray interaction.  Unlike the
untruncated finite-aperture chronology, this is a genuinely finite-dimensional autonomous ODE.

The exact coordinate-atom costs from the ancestry service give explicit quadratic and Lipschitz
bounds.  On a declared ball they determine a concrete short symmetric clock.  Mathlib's
Picard--Lindelöf construction then returns a genuine fixed point of the integral equation and its
factorial iterate-distance estimate.  These conclusions concern only the fixed finite Galerkin
carrier.  No cofinal-carrier convergence, agreement with an untruncated mild solution, terminal
control, or Navier--Stokes regularity conclusion is asserted.
-/

noncomputable section

open Function MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal Interval Nat

namespace Soma.Holonics.Millennium.NavierStokesFiniteGalerkinLocalPicard

open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFinitePicardAncestryService
open Soma.Holonics.Millennium.NavierStokesFinitePicardChronology
open Soma.Holonics.Millennium.NavierStokesFiniteScaleAncestry
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Fixed finite carrier and zero extension -/

/-- State space on one fixed finite Galerkin carrier. -/
abbrev FiniteGalerkinState (carrier : Finset SpatialFrequency) :=
  FiniteFourierState carrier

/-- Zero extension of one finite state to the complete address population. -/
def finiteGalerkinZeroExtension
    {carrier : Finset SpatialFrequency} (state : FiniteGalerkinState carrier) :
    ComplexFourierModePopulation :=
  fun frequency ↦ if hfrequency : frequency ∈ carrier then
    state ⟨frequency, hfrequency⟩ else 0

theorem enorm_finiteGalerkinZeroExtension_le
    {carrier : Finset SpatialFrequency} (state : FiniteGalerkinState carrier)
    (frequency : SpatialFrequency) :
    ‖finiteGalerkinZeroExtension state frequency‖ₑ ≤ ‖state‖ₑ := by
  by_cases hfrequency : frequency ∈ carrier
  · rw [finiteGalerkinZeroExtension, dif_pos hfrequency]
    simp only [enorm_eq_nnnorm, ENNReal.coe_le_coe]
    exact nnnorm_le_pi_nnnorm state ⟨frequency, hfrequency⟩
  · rw [finiteGalerkinZeroExtension, dif_neg hfrequency, enorm_zero]
    exact bot_le

/-- The bilinear projected Galerkin interaction, restricted back to the fixed carrier. -/
def finiteGalerkinProjectedInteraction
    (carrier aperture : Finset SpatialFrequency)
    (left right : FiniteGalerkinState carrier) : FiniteGalerkinState carrier :=
  fun output ↦
    finiteProjectedAdvectiveCoefficient aperture
      (finiteGalerkinZeroExtension left) (finiteGalerkinZeroExtension right) output.1

/-- The autonomous finite-dimensional Navier--Stokes Galerkin vector field. -/
def finiteGalerkinNavierStokesVectorField
    (nu : ℝ) (carrier aperture : Finset SpatialFrequency)
    (state : FiniteGalerkinState carrier) : FiniteGalerkinState carrier :=
  fun output ↦
    -((nu * torusStokesEigenvalue output.1 : ℝ) : ℂ) • state output -
      finiteGalerkinProjectedInteraction carrier aperture state state output

/-! ## Exact quadratic difference -/

@[simp]
theorem finiteGalerkinZeroExtension_sub
    {carrier : Finset SpatialFrequency} (left right : FiniteGalerkinState carrier) :
    finiteGalerkinZeroExtension (left - right) =
      fun frequency ↦ finiteGalerkinZeroExtension left frequency -
        finiteGalerkinZeroExtension right frequency := by
  funext frequency
  by_cases hfrequency : frequency ∈ carrier
  · simp [finiteGalerkinZeroExtension, hfrequency]
  · simp [finiteGalerkinZeroExtension, hfrequency]

private theorem finiteGalerkinZeroExtension_eq_add_sub
    {carrier : Finset SpatialFrequency} (left right : FiniteGalerkinState carrier) :
    finiteGalerkinZeroExtension left =
      fun frequency ↦ finiteGalerkinZeroExtension right frequency +
        finiteGalerkinZeroExtension (left - right) frequency := by
  rw [finiteGalerkinZeroExtension_sub]
  funext frequency
  module

/-- The quadratic difference is reconstructed from the two cross terms and the marked--marked
remainder.  Here the marked state is the actual iterate difference, not an assumed derivative. -/
theorem finiteGalerkinProjectedInteraction_self_sub_self
    (carrier aperture : Finset SpatialFrequency)
    (left right : FiniteGalerkinState carrier) :
    finiteGalerkinProjectedInteraction carrier aperture left left -
        finiteGalerkinProjectedInteraction carrier aperture right right =
      finiteGalerkinProjectedInteraction carrier aperture (left - right) right +
        finiteGalerkinProjectedInteraction carrier aperture right (left - right) +
        finiteGalerkinProjectedInteraction carrier aperture (left - right) (left - right) := by
  funext output
  change
    finiteProjectedAdvectiveCoefficient aperture
        (finiteGalerkinZeroExtension left) (finiteGalerkinZeroExtension left) output.1 -
      finiteProjectedAdvectiveCoefficient aperture
        (finiteGalerkinZeroExtension right) (finiteGalerkinZeroExtension right) output.1 = _
  rw [finiteGalerkinZeroExtension_eq_add_sub left right]
  exact finiteProjectedAdvectiveCoefficient_add_self_sub aperture
    (finiteGalerkinZeroExtension right) (finiteGalerkinZeroExtension (left - right)) output.1

/-! ## Actual finite operator costs -/

/-- Sum of all actual finite interaction costs seen by the fixed output carrier. -/
def finiteGalerkinInteractionExtendedCost
    (carrier aperture : Finset SpatialFrequency) : ℝ≥0∞ :=
  ∑ output ∈ carrier, finiteProjectedInteractionOutputCost output aperture

theorem finiteGalerkinInteractionExtendedCost_ne_top
    (carrier aperture : Finset SpatialFrequency) :
    finiteGalerkinInteractionExtendedCost carrier aperture ≠ ∞ := by
  unfold finiteGalerkinInteractionExtendedCost
  exact ENNReal.sum_ne_top.2 fun output _houtput ↦
    finiteProjectedInteractionOutputCost_ne_top output aperture

/-- The same finite interaction cost in the nonnegative-real chart required by Picard--Lindelöf. -/
def finiteGalerkinInteractionCost
    (carrier aperture : Finset SpatialFrequency) : ℝ≥0 :=
  (finiteGalerkinInteractionExtendedCost carrier aperture).toNNReal

/-- Complete named diagonal Stokes cost on the finite carrier. -/
def finiteGalerkinStokesCost
    (nu : ℝ) (carrier : Finset SpatialFrequency) : ℝ≥0 :=
  ∑ output ∈ carrier, ‖((nu * torusStokesEigenvalue output : ℝ) : ℂ)‖₊

private theorem finiteProjectedInteractionOutputCost_le_total
    (carrier aperture : Finset SpatialFrequency) {output : SpatialFrequency}
    (houtput : output ∈ carrier) :
    finiteProjectedInteractionOutputCost output aperture ≤
      finiteGalerkinInteractionExtendedCost carrier aperture := by
  unfold finiteGalerkinInteractionExtendedCost
  exact Finset.single_le_sum
    (fun address _haddress ↦ (zero_le : (0 : ℝ≥0∞) ≤
      finiteProjectedInteractionOutputCost address aperture)) houtput

private theorem enorm_finiteProjectedCoefficient_zeroExtension_le
    (carrier aperture : Finset SpatialFrequency)
    (left right : FiniteGalerkinState carrier) (output : SpatialFrequency) :
    ‖finiteProjectedAdvectiveCoefficient aperture
        (finiteGalerkinZeroExtension left) (finiteGalerkinZeroExtension right) output‖ₑ ≤
      finiteProjectedInteractionOutputCost output aperture * ‖left‖ₑ * ‖right‖ₑ := by
  calc
    _ ≤ ∑ parent ∈ aperture,
        finiteProjectedInteractionAtomCost output parent *
          ‖finiteGalerkinZeroExtension left parent‖ₑ *
          ‖finiteGalerkinZeroExtension right
            (transportedFrequencyAt output parent)‖ₑ :=
      enorm_finiteProjectedAdvectiveCoefficient_le_atomPayments _ _ _ _
    _ ≤ ∑ parent ∈ aperture,
        finiteProjectedInteractionAtomCost output parent * ‖left‖ₑ * ‖right‖ₑ := by
      apply Finset.sum_le_sum
      intro parent _hparent
      exact mul_le_mul'
        (mul_le_mul' le_rfl
          (enorm_finiteGalerkinZeroExtension_le left parent))
        (enorm_finiteGalerkinZeroExtension_le right
          (transportedFrequencyAt output parent))
    _ = _ := by
      unfold finiteProjectedInteractionOutputCost
      rw [Finset.sum_mul, Finset.sum_mul]

/-- Exact finite quadratic service in the fixed-carrier sup norm. -/
theorem nnnorm_finiteGalerkinProjectedInteraction_le
    (carrier aperture : Finset SpatialFrequency)
    (left right : FiniteGalerkinState carrier) :
    ‖finiteGalerkinProjectedInteraction carrier aperture left right‖₊ ≤
      finiteGalerkinInteractionCost carrier aperture * ‖left‖₊ * ‖right‖₊ := by
  apply pi_nnnorm_le_iff.mpr
  intro output
  have hmode := enorm_finiteProjectedCoefficient_zeroExtension_le
    carrier aperture left right output.1
  have hcost := finiteProjectedInteractionOutputCost_le_total
    carrier aperture output.2
  have hmode' :
      ‖finiteGalerkinProjectedInteraction carrier aperture left right output‖ₑ ≤
        finiteGalerkinInteractionExtendedCost carrier aperture * ‖left‖ₑ * ‖right‖ₑ :=
    hmode.trans (mul_le_mul' (mul_le_mul' hcost le_rfl) le_rfl)
  rw [← ENNReal.coe_toNNReal
    (finiteGalerkinInteractionExtendedCost_ne_top carrier aperture)] at hmode'
  apply ENNReal.coe_le_coe.mp
  simpa only [finiteGalerkinInteractionCost, enorm_eq_nnnorm, ENNReal.coe_mul]
    using hmode'

theorem norm_finiteGalerkinProjectedInteraction_le
    (carrier aperture : Finset SpatialFrequency)
    (left right : FiniteGalerkinState carrier) :
    ‖finiteGalerkinProjectedInteraction carrier aperture left right‖ ≤
      finiteGalerkinInteractionCost carrier aperture * ‖left‖ * ‖right‖ := by
  exact_mod_cast nnnorm_finiteGalerkinProjectedInteraction_le carrier aperture left right

/-- The actual quadratic difference bound.  Its third term is the marked--marked remainder, so no
linearization or unspecified derivative constant is hidden. -/
theorem norm_finiteGalerkinProjectedInteraction_self_sub_self_le
    (carrier aperture : Finset SpatialFrequency)
    (left right : FiniteGalerkinState carrier) :
    ‖finiteGalerkinProjectedInteraction carrier aperture left left -
        finiteGalerkinProjectedInteraction carrier aperture right right‖ ≤
      finiteGalerkinInteractionCost carrier aperture *
        (2 * ‖right‖ + ‖left - right‖) * ‖left - right‖ := by
  rw [finiteGalerkinProjectedInteraction_self_sub_self]
  calc
    _ ≤ ‖finiteGalerkinProjectedInteraction carrier aperture (left - right) right +
          finiteGalerkinProjectedInteraction carrier aperture right (left - right)‖ +
        ‖finiteGalerkinProjectedInteraction carrier aperture (left - right) (left - right)‖ :=
      norm_add_le _ _
    _ ≤ (‖finiteGalerkinProjectedInteraction carrier aperture (left - right) right‖ +
          ‖finiteGalerkinProjectedInteraction carrier aperture right (left - right)‖) +
        ‖finiteGalerkinProjectedInteraction carrier aperture (left - right) (left - right)‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (finiteGalerkinInteractionCost carrier aperture * ‖left - right‖ * ‖right‖ +
          finiteGalerkinInteractionCost carrier aperture * ‖right‖ * ‖left - right‖) +
        finiteGalerkinInteractionCost carrier aperture * ‖left - right‖ * ‖left - right‖ := by
      gcongr
      · exact norm_finiteGalerkinProjectedInteraction_le carrier aperture (left - right) right
      · exact norm_finiteGalerkinProjectedInteraction_le carrier aperture right (left - right)
      · exact norm_finiteGalerkinProjectedInteraction_le carrier aperture
          (left - right) (left - right)
    _ = _ := by ring

/-! ## One actual finite ball service -/

/-- The largest state norm visible on the declared closed ball. -/
def finiteGalerkinBallAmplitude
    {carrier : Finset SpatialFrequency} (initial : FiniteGalerkinState carrier)
    (radius : ℝ≥0) : ℝ≥0 :=
  ‖initial‖₊ + radius

theorem norm_le_finiteGalerkinBallAmplitude
    {carrier : Finset SpatialFrequency} (initial state : FiniteGalerkinState carrier)
    (radius : ℝ≥0) (hstate : state ∈ closedBall initial radius) :
    ‖state‖ ≤ finiteGalerkinBallAmplitude initial radius := by
  calc
    ‖state‖ ≤ ‖state - initial‖ + ‖initial‖ := norm_le_norm_sub_add _ _
    _ ≤ radius + ‖initial‖ := by
      gcongr
      exact mem_closedBall_iff_norm.mp hstate
    _ = finiteGalerkinBallAmplitude initial radius := by
      simp [finiteGalerkinBallAmplitude, add_comm]

/-- Exact diagonal Stokes service in the fixed-carrier sup norm. -/
theorem norm_finiteGalerkinStokesPart_le
    (nu : ℝ) (carrier : Finset SpatialFrequency)
    (state : FiniteGalerkinState carrier) :
    ‖fun output : {frequency // frequency ∈ carrier} ↦
        -((nu * torusStokesEigenvalue output.1 : ℝ) : ℂ) • state output‖ ≤
      finiteGalerkinStokesCost nu carrier * ‖state‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro output
  rw [norm_smul, norm_neg]
  have hcoefficient :
      ‖((nu * torusStokesEigenvalue output.1 : ℝ) : ℂ)‖ ≤
        finiteGalerkinStokesCost nu carrier := by
    have hcoefficientNN :
        ‖((nu * torusStokesEigenvalue output.1 : ℝ) : ℂ)‖₊ ≤
          finiteGalerkinStokesCost nu carrier := by
      unfold finiteGalerkinStokesCost
      exact Finset.single_le_sum
        (fun address _haddress ↦ (zero_le : (0 : ℝ≥0) ≤
          ‖((nu * torusStokesEigenvalue address : ℝ) : ℂ)‖₊)) output.2
    exact_mod_cast hcoefficientNN
  exact mul_le_mul hcoefficient (norm_le_pi_norm state output)
    (norm_nonneg _) (by positivity)

theorem norm_finiteGalerkinNavierStokesVectorField_le
    (nu : ℝ) (carrier aperture : Finset SpatialFrequency)
    (state : FiniteGalerkinState carrier) :
    ‖finiteGalerkinNavierStokesVectorField nu carrier aperture state‖ ≤
      finiteGalerkinStokesCost nu carrier * ‖state‖ +
        finiteGalerkinInteractionCost carrier aperture * ‖state‖ ^ 2 := by
  calc
    _ ≤ ‖fun output : {frequency // frequency ∈ carrier} ↦
        -((nu * torusStokesEigenvalue output.1 : ℝ) : ℂ) • state output‖ +
      ‖finiteGalerkinProjectedInteraction carrier aperture state state‖ :=
      norm_sub_le _ _
    _ ≤ _ := by
      gcongr
      · exact norm_finiteGalerkinStokesPart_le nu carrier state
      · simpa [pow_two, mul_assoc] using
          norm_finiteGalerkinProjectedInteraction_le carrier aperture state state

/-- An exact subtraction law separating the linear Stokes response from the quadratic
interaction difference. -/
theorem finiteGalerkinNavierStokesVectorField_sub
    (nu : ℝ) (carrier aperture : Finset SpatialFrequency)
    (left right : FiniteGalerkinState carrier) :
    finiteGalerkinNavierStokesVectorField nu carrier aperture left -
        finiteGalerkinNavierStokesVectorField nu carrier aperture right =
      (fun output : {frequency // frequency ∈ carrier} ↦
        -((nu * torusStokesEigenvalue output.1 : ℝ) : ℂ) • (left - right) output) -
      (finiteGalerkinProjectedInteraction carrier aperture left left -
        finiteGalerkinProjectedInteraction carrier aperture right right) := by
  funext output
  unfold finiteGalerkinNavierStokesVectorField
  simp only [Pi.sub_apply]
  module

/-- Concrete norm service of the finite vector field throughout one closed ball. -/
def finiteGalerkinBallVectorCost
    (nu : ℝ) (carrier aperture : Finset SpatialFrequency)
    (initial : FiniteGalerkinState carrier) (radius : ℝ≥0) : ℝ≥0 :=
  finiteGalerkinStokesCost nu carrier * finiteGalerkinBallAmplitude initial radius +
    finiteGalerkinInteractionCost carrier aperture *
      finiteGalerkinBallAmplitude initial radius ^ 2

/-- Concrete Lipschitz service on the same ball.  The factor four pays for the exact
marked--marked remainder using `‖left - right‖ ≤ 2 * amplitude`. -/
def finiteGalerkinBallLipschitzCost
    (nu : ℝ) (carrier aperture : Finset SpatialFrequency)
    (initial : FiniteGalerkinState carrier) (radius : ℝ≥0) : ℝ≥0 :=
  finiteGalerkinStokesCost nu carrier +
    4 * finiteGalerkinInteractionCost carrier aperture *
      finiteGalerkinBallAmplitude initial radius

theorem norm_finiteGalerkinNavierStokesVectorField_le_ballVectorCost
    (nu : ℝ) (carrier aperture : Finset SpatialFrequency)
    (initial state : FiniteGalerkinState carrier) (radius : ℝ≥0)
    (hstate : state ∈ closedBall initial radius) :
    ‖finiteGalerkinNavierStokesVectorField nu carrier aperture state‖ ≤
      finiteGalerkinBallVectorCost nu carrier aperture initial radius := by
  have hnorm := norm_le_finiteGalerkinBallAmplitude initial state radius hstate
  calc
    _ ≤ finiteGalerkinStokesCost nu carrier * ‖state‖ +
        finiteGalerkinInteractionCost carrier aperture * ‖state‖ ^ 2 :=
      norm_finiteGalerkinNavierStokesVectorField_le nu carrier aperture state
    _ ≤ finiteGalerkinStokesCost nu carrier * finiteGalerkinBallAmplitude initial radius +
        finiteGalerkinInteractionCost carrier aperture *
          finiteGalerkinBallAmplitude initial radius ^ 2 := by gcongr
    _ = _ := rfl

theorem norm_finiteGalerkinNavierStokesVectorField_sub_le_ballLipschitzCost
    (nu : ℝ) (carrier aperture : Finset SpatialFrequency)
    (initial left right : FiniteGalerkinState carrier) (radius : ℝ≥0)
    (hleft : left ∈ closedBall initial radius)
    (hright : right ∈ closedBall initial radius) :
    ‖finiteGalerkinNavierStokesVectorField nu carrier aperture left -
        finiteGalerkinNavierStokesVectorField nu carrier aperture right‖ ≤
      finiteGalerkinBallLipschitzCost nu carrier aperture initial radius *
        ‖left - right‖ := by
  let amplitude : ℝ := finiteGalerkinBallAmplitude initial radius
  have hleftNorm : ‖left‖ ≤ amplitude :=
    norm_le_finiteGalerkinBallAmplitude initial left radius hleft
  have hrightNorm : ‖right‖ ≤ amplitude :=
    norm_le_finiteGalerkinBallAmplitude initial right radius hright
  have hdiff : ‖left - right‖ ≤ 2 * amplitude := by
    calc
      ‖left - right‖ ≤ ‖left‖ + ‖right‖ := norm_sub_le _ _
      _ ≤ amplitude + amplitude := add_le_add hleftNorm hrightNorm
      _ = 2 * amplitude := by ring
  rw [finiteGalerkinNavierStokesVectorField_sub]
  calc
    _ ≤ ‖fun output : {frequency // frequency ∈ carrier} ↦
          -((nu * torusStokesEigenvalue output.1 : ℝ) : ℂ) • (left - right) output‖ +
        ‖finiteGalerkinProjectedInteraction carrier aperture left left -
          finiteGalerkinProjectedInteraction carrier aperture right right‖ := norm_sub_le _ _
    _ ≤ finiteGalerkinStokesCost nu carrier * ‖left - right‖ +
        finiteGalerkinInteractionCost carrier aperture *
          (2 * ‖right‖ + ‖left - right‖) * ‖left - right‖ := by
      gcongr
      · exact norm_finiteGalerkinStokesPart_le nu carrier (left - right)
      · exact norm_finiteGalerkinProjectedInteraction_self_sub_self_le
          carrier aperture left right
    _ ≤ finiteGalerkinStokesCost nu carrier * ‖left - right‖ +
        finiteGalerkinInteractionCost carrier aperture *
          (4 * amplitude) * ‖left - right‖ := by
      gcongr
      calc
        2 * ‖right‖ + ‖left - right‖ ≤ 2 * amplitude + 2 * amplitude := by gcongr
        _ = 4 * amplitude := by ring
    _ = finiteGalerkinBallLipschitzCost nu carrier aperture initial radius *
        ‖left - right‖ := by
      simp only [finiteGalerkinBallLipschitzCost, amplitude, NNReal.coe_add, NNReal.coe_mul]
      norm_num
      ring

/-- The autonomous finite Galerkin vector field is Lipschitz on the actual declared ball with the
explicit service coefficient above. -/
theorem lipschitzOnWith_finiteGalerkinNavierStokesVectorField
    (nu : ℝ) (carrier aperture : Finset SpatialFrequency)
    (initial : FiniteGalerkinState carrier) (radius : ℝ≥0) :
    LipschitzOnWith (finiteGalerkinBallLipschitzCost nu carrier aperture initial radius)
      (finiteGalerkinNavierStokesVectorField nu carrier aperture)
      (closedBall initial radius) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro left hleft right hright
  simpa only [dist_eq_norm] using
    norm_finiteGalerkinNavierStokesVectorField_sub_le_ballLipschitzCost
      nu carrier aperture initial left right radius hleft hright

/-! ## The clock and the finite local solver -/

/-- A short-time clock paid for by the actual vector-field service.  The added unit prevents a
zero service from producing an undefined division while preserving strict positivity whenever the
declared state radius is positive. -/
def finiteGalerkinLocalClock
    (nu : ℝ) (carrier aperture : Finset SpatialFrequency)
    (initial : FiniteGalerkinState carrier) (radius : ℝ≥0) : ℝ≥0 :=
  radius / (finiteGalerkinBallVectorCost nu carrier aperture initial radius + 1)

theorem finiteGalerkinLocalClock_pos
    (nu : ℝ) (carrier aperture : Finset SpatialFrequency)
    (initial : FiniteGalerkinState carrier) {radius : ℝ≥0} (hradius : 0 < radius) :
    0 < finiteGalerkinLocalClock nu carrier aperture initial radius := by
  unfold finiteGalerkinLocalClock
  positivity

/-- The fixed finite Galerkin vector field satisfies Picard--Lindelöf on its explicit symmetric
clock.  Every constant in this statement is computed from the declared carrier, aperture, initial
state, viscosity coordinate, and state radius. -/
theorem finiteGalerkin_isPicardLindelof
    (nu restartTime : ℝ) (carrier aperture : Finset SpatialFrequency)
    (initial : FiniteGalerkinState carrier) (radius : ℝ≥0)
    (hradius : 0 < radius) :
    IsPicardLindelof
      (fun _ ↦ finiteGalerkinNavierStokesVectorField nu carrier aperture)
      (tmin := restartTime - finiteGalerkinLocalClock nu carrier aperture initial radius)
      (tmax := restartTime + finiteGalerkinLocalClock nu carrier aperture initial radius)
      ⟨restartTime, by simp⟩
      initial radius 0
      (finiteGalerkinBallVectorCost nu carrier aperture initial radius)
      (finiteGalerkinBallLipschitzCost nu carrier aperture initial radius) := by
  apply IsPicardLindelof.of_time_independent
  · intro state hstate
    exact norm_finiteGalerkinNavierStokesVectorField_le_ballVectorCost
      nu carrier aperture initial state radius hstate
  · exact lipschitzOnWith_finiteGalerkinNavierStokesVectorField
      nu carrier aperture initial radius
  · simp only [add_sub_cancel_left, sub_sub_cancel, max_self, NNReal.coe_zero, sub_zero]
    unfold finiteGalerkinLocalClock
    push_cast
    calc
      (finiteGalerkinBallVectorCost nu carrier aperture initial radius : ℝ) *
          ((radius : ℝ) /
            ((finiteGalerkinBallVectorCost nu carrier aperture initial radius : ℝ) + 1)) =
        (finiteGalerkinBallVectorCost nu carrier aperture initial radius : ℝ) /
            ((finiteGalerkinBallVectorCost nu carrier aperture initial radius : ℝ) + 1) *
          radius := by ring
      _ ≤ 1 * radius := by
        gcongr
        rw [div_le_one (by positivity :
          (0 : ℝ) < finiteGalerkinBallVectorCost nu carrier aperture initial radius + 1)]
        exact le_add_of_nonneg_right zero_le_one
      _ = radius := one_mul _

/-- A genuine local integral solution of the fixed-carrier Galerkin equation.  The returned path is
a fixed point of the Picard integral transport on the complete explicit clock interval. -/
theorem exists_finiteGalerkinLocalPicardSolution
    (nu restartTime : ℝ) (carrier aperture : Finset SpatialFrequency)
    (initial : FiniteGalerkinState carrier) (radius : ℝ≥0)
    (hradius : 0 < radius) :
    ∃ path : ℝ → FiniteGalerkinState carrier,
      path restartTime = initial ∧
      ∀ targetTime ∈ Set.Icc
          (restartTime - finiteGalerkinLocalClock nu carrier aperture initial radius)
          (restartTime + finiteGalerkinLocalClock nu carrier aperture initial radius),
        path targetTime = ODE.picard
          (fun _ ↦ finiteGalerkinNavierStokesVectorField nu carrier aperture)
          restartTime initial path targetTime := by
  let start : Set.Icc
      (restartTime - finiteGalerkinLocalClock nu carrier aperture initial radius)
      (restartTime + finiteGalerkinLocalClock nu carrier aperture initial radius) :=
    ⟨restartTime, by simp⟩
  have hf := finiteGalerkin_isPicardLindelof
    nu restartTime carrier aperture initial radius hradius
  have hinitial : initial ∈ closedBall initial (0 : ℝ≥0) := by simp
  simpa only [start] using
    IsPicardLindelof.exists_eq_forall_mem_Icc_eq_picard hf hinitial

/-- The earned factorial majorant for differences of finite Galerkin Picard iterates.  This is the
standard Volterra-simplex suppression, now instantiated with the actual carrier/aperture
Lipschitz cost rather than an assumed service constant. -/
theorem finiteGalerkinPicardIterate_dist_le
    (nu restartTime : ℝ) (carrier aperture : Finset SpatialFrequency)
    (initial : FiniteGalerkinState carrier) (radius : ℝ≥0)
    (hradius : 0 < radius)
    (alpha beta : ODE.FunSpace
      (⟨restartTime, by simp⟩ : Set.Icc
        (restartTime - finiteGalerkinLocalClock nu carrier aperture initial radius)
        (restartTime + finiteGalerkinLocalClock nu carrier aperture initial radius))
      initial 0 (finiteGalerkinBallVectorCost nu carrier aperture initial radius))
    (generation : ℕ)
    (targetTime : Set.Icc
      (restartTime - finiteGalerkinLocalClock nu carrier aperture initial radius)
      (restartTime + finiteGalerkinLocalClock nu carrier aperture initial radius)) :
    let hf := finiteGalerkin_isPicardLindelof
      nu restartTime carrier aperture initial radius hradius
    let hinitial : initial ∈ closedBall initial (0 : ℝ≥0) := by simp
    dist ((ODE.FunSpace.next hf hinitial)^[generation] alpha targetTime)
        ((ODE.FunSpace.next hf hinitial)^[generation] beta targetTime) ≤
      (finiteGalerkinBallLipschitzCost nu carrier aperture initial radius *
          |targetTime.1 - restartTime|) ^ generation /
        generation ! * dist alpha beta := by
  dsimp only
  exact ODE.FunSpace.dist_iterate_next_apply_le
    (finiteGalerkin_isPicardLindelof
      nu restartTime carrier aperture initial radius hradius)
    (by simp) alpha beta generation targetTime

/-- Some explicitly serviced finite iterate of the local Picard operator is a genuine contraction.
Its existence follows from the preceding factorial majorant, not from a one-step smallness claim. -/
theorem exists_finiteGalerkinPicardIterate_contracting
    (nu restartTime : ℝ) (carrier aperture : Finset SpatialFrequency)
    (initial : FiniteGalerkinState carrier) (radius : ℝ≥0)
    (hradius : 0 < radius) :
    let hf := finiteGalerkin_isPicardLindelof
      nu restartTime carrier aperture initial radius hradius
    let hinitial : initial ∈ closedBall initial (0 : ℝ≥0) := by simp
    ∃ (generation : ℕ) (contractionCost : ℝ≥0),
      ContractingWith contractionCost
        (ODE.FunSpace.next hf hinitial)^[generation] := by
  dsimp only
  obtain ⟨generation, contractionCost, hcontracting⟩ :=
    ODE.FunSpace.exists_contractingWith_iterate_next
      (finiteGalerkin_isPicardLindelof
        nu restartTime carrier aperture initial radius hradius)
  exact ⟨generation, contractionCost, hcontracting initial (by simp)⟩

/-- The complete finite-interval Picard function space contains an actual fixed point.  This is the
fixed-carrier convergence object used by the exterior integral-solution theorem above. -/
theorem exists_finiteGalerkinPicardFixedPoint
    (nu restartTime : ℝ) (carrier aperture : Finset SpatialFrequency)
    (initial : FiniteGalerkinState carrier) (radius : ℝ≥0)
    (hradius : 0 < radius) :
    let hf := finiteGalerkin_isPicardLindelof
      nu restartTime carrier aperture initial radius hradius
    let hinitial : initial ∈ closedBall initial (0 : ℝ≥0) := by simp
    ∃ alpha : ODE.FunSpace
        (⟨restartTime, by simp⟩ : Set.Icc
          (restartTime - finiteGalerkinLocalClock nu carrier aperture initial radius)
          (restartTime + finiteGalerkinLocalClock nu carrier aperture initial radius))
        initial 0 (finiteGalerkinBallVectorCost nu carrier aperture initial radius),
      IsFixedPt (ODE.FunSpace.next hf hinitial) alpha := by
  dsimp only
  exact ODE.FunSpace.exists_isFixedPt_next
    (finiteGalerkin_isPicardLindelof
      nu restartTime carrier aperture initial radius hradius) (by simp)

/-! ## The cumulative ancestry-cone instance -/

/-- The fixed carrier can be chosen to be exactly the finite cumulative ancestry cone built by the
preceding owner. -/
abbrev FiniteHorizonAncestryGalerkinState
    (aperture terminal : Finset SpatialFrequency) (horizon : ℕ) :=
  FiniteGalerkinState (finiteHorizonAncestryReceiver aperture terminal horizon)

/-- Direct local-solver instance on the declared cumulative ancestry cone.  Fixing the horizon is
essential: increasing the horizon changes the state space and requires a separate cofinal passage. -/
theorem exists_finiteHorizonAncestryLocalPicardSolution
    (nu restartTime : ℝ) (aperture terminal : Finset SpatialFrequency) (horizon : ℕ)
    (initial : FiniteHorizonAncestryGalerkinState aperture terminal horizon)
    (radius : ℝ≥0) (hradius : 0 < radius) :
    ∃ path : ℝ → FiniteHorizonAncestryGalerkinState aperture terminal horizon,
      path restartTime = initial ∧
      ∀ targetTime ∈ Set.Icc
          (restartTime - finiteGalerkinLocalClock nu
            (finiteHorizonAncestryReceiver aperture terminal horizon) aperture initial radius)
          (restartTime + finiteGalerkinLocalClock nu
            (finiteHorizonAncestryReceiver aperture terminal horizon) aperture initial radius),
        path targetTime = ODE.picard
          (fun _ ↦ finiteGalerkinNavierStokesVectorField nu
            (finiteHorizonAncestryReceiver aperture terminal horizon) aperture)
          restartTime initial path targetTime := by
  exact exists_finiteGalerkinLocalPicardSolution nu restartTime
    (finiteHorizonAncestryReceiver aperture terminal horizon) aperture initial radius hradius

section Audit

#print axioms nnnorm_finiteGalerkinProjectedInteraction_le
#print axioms norm_finiteGalerkinNavierStokesVectorField_le
#print axioms finiteGalerkinProjectedInteraction_self_sub_self
#print axioms lipschitzOnWith_finiteGalerkinNavierStokesVectorField
#print axioms finiteGalerkin_isPicardLindelof
#print axioms exists_finiteGalerkinLocalPicardSolution
#print axioms finiteGalerkinPicardIterate_dist_le
#print axioms exists_finiteGalerkinPicardIterate_contracting
#print axioms exists_finiteGalerkinPicardFixedPoint
#print axioms exists_finiteHorizonAncestryLocalPicardSolution

end Audit

end Soma.Holonics.Millennium.NavierStokesFiniteGalerkinLocalPicard
