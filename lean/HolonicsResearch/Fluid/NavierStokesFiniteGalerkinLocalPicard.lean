import HolonicsResearch.Fluid.NavierStokesFinitePicardAncestryService
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

namespace Holonics.Fluid.NavierStokesFiniteGalerkinLocalPicard

open Holonics.Fluid.NavierStokesDyadicFlowCommutator
open Holonics.Fluid.NavierStokesFiniteGalerkin
open Holonics.Fluid.NavierStokesFiniteFourierHeat
open Holonics.Fluid.NavierStokesFinitePicardAncestryService
open Holonics.Fluid.NavierStokesFinitePicardChronology
open Holonics.Fluid.NavierStokesFiniteScaleAncestry
open Holonics.Fluid.NavierStokesFourierTriads
open Holonics.Fluid.NavierStokesMildFourierNonlinearity
open Holonics.Fluid.NavierStokesTorusFourier

/-! ## Fixed finite carrier and zero extension -/

/-! ## Slot linearity of the actual finite projected interaction -/

section InteractionLinearity
variable {carrier : Finset SpatialFrequency} (aperture : Finset SpatialFrequency)

theorem finiteGalerkinZeroExtension_neg (u : FiniteGalerkinState carrier) :
    finiteGalerkinZeroExtension (-u) = fun p ↦ -finiteGalerkinZeroExtension u p := by
  funext p
  by_cases hp : p ∈ carrier <;> simp [finiteGalerkinZeroExtension, hp]

end InteractionLinearity

/-! ## Exact quadratic difference -/

/-! ## Actual finite operator costs -/

/-- Complete named diagonal Stokes cost on the finite carrier. -/
def finiteGalerkinStokesCost
    (nu : ℝ) (carrier : Finset SpatialFrequency) : ℝ≥0 :=
  ∑ output ∈ carrier, ‖((nu * torusStokesEigenvalue output : ℝ) : ℂ)‖₊

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

#print axioms norm_finiteGalerkinNavierStokesVectorField_le
#print axioms lipschitzOnWith_finiteGalerkinNavierStokesVectorField
#print axioms finiteGalerkin_isPicardLindelof
#print axioms exists_finiteGalerkinLocalPicardSolution
#print axioms finiteGalerkinPicardIterate_dist_le
#print axioms exists_finiteGalerkinPicardIterate_contracting
#print axioms exists_finiteGalerkinPicardFixedPoint
#print axioms exists_finiteHorizonAncestryLocalPicardSolution

end Audit

end Holonics.Fluid.NavierStokesFiniteGalerkinLocalPicard
