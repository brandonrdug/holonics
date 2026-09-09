import ElementaryHolonics.Transport.ChangingReceiver
import ElementaryHolonics.Millennium.NavierStokesFiniteGalerkinLocalPicard

/-!
# Finite Galerkin fluid receiver closure

This module gives one concrete changing-receiver instance for the finite Galerkin
Navier--Stokes vector field.  A continuous real-linear receiver `q` and a lift
retain a resolved state and its hidden fibre.  The receiver closure defect is
then exactly the Stokes response of the hidden state together with all three
quadratic feedback terms.  The quadratic source is the existing finite
advective--Leray interaction; it is not replaced by a generic bilinear proxy.

The results concern one declared finite carrier and make no continuum or
Galerkin-limit claim.
-/

noncomputable section

open Soma.Holonics
open Soma.Holonics.Transport.ChangingReceiver
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFiniteGalerkinLocalPicard
open Soma.Holonics.Millennium.NavierStokesTorusFourier

namespace Soma.Holonics.Physics.FluidReceiverClosure

abbrev FluidState (carrier : Finset SpatialFrequency) :=
  FiniteGalerkinState carrier

variable {carrier : Finset SpatialFrequency} {Y : Type*}
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def resolvedState (q : FluidState carrier →L[ℝ] Y)
    (lift : Y →L[ℝ] FluidState carrier) (state : FluidState carrier) :
    FluidState carrier :=
  lift (q state)

def hiddenState (q : FluidState carrier →L[ℝ] Y)
    (lift : Y →L[ℝ] FluidState carrier) (state : FluidState carrier) :
    FluidState carrier :=
  state - resolvedState q lift state

def finiteGalerkinCoarseVectorField
    (nu : ℝ) (aperture : Finset SpatialFrequency)
    (q : FluidState carrier →L[ℝ] Y)
    (lift : Y →L[ℝ] FluidState carrier) : Y → Y :=
  fun coarseState ↦ q
    (finiteGalerkinNavierStokesVectorField nu carrier aperture (lift coarseState))

/-- The Stokes component of the actual finite Galerkin Navier--Stokes field. -/
def finiteGalerkinStokesPart
    (nu : ℝ) (state : FluidState carrier) : FluidState carrier :=
  fun output ↦
    -((nu * torusStokesEigenvalue output.1 : ℝ) : ℂ) • state output

theorem finiteGalerkinNavierStokesVectorField_eq_stokes_sub_source
    (nu : ℝ) (aperture : Finset SpatialFrequency) (state : FluidState carrier) :
    finiteGalerkinNavierStokesVectorField nu carrier aperture state =
      finiteGalerkinStokesPart nu state -
        finiteGalerkinProjectedInteraction carrier aperture state state := by
  rfl

theorem hiddenState_eq_sub_resolvedState
    (q : FluidState carrier →L[ℝ] Y)
    (lift : Y →L[ℝ] FluidState carrier) (state : FluidState carrier) :
    hiddenState q lift state = state - resolvedState q lift state := rfl

theorem q_hiddenState_eq_zero
    (q : FluidState carrier →L[ℝ] Y)
    (lift : Y →L[ℝ] FluidState carrier)
    (hsection : q.comp lift = ContinuousLinearMap.id ℝ Y)
    (state : FluidState carrier) :
    q (hiddenState q lift state) = 0 := by
  unfold hiddenState resolvedState
  rw [map_sub]
  have hsection_apply := congrArg (fun L : Y →L[ℝ] Y ↦ L (q state)) hsection
  simpa using (sub_eq_zero.mpr hsection_apply.symm)

theorem finiteGalerkinCoarseVectorField_apply
    (nu : ℝ) (aperture : Finset SpatialFrequency)
    (q : FluidState carrier →L[ℝ] Y)
    (lift : Y →L[ℝ] FluidState carrier) (coarseState : Y) :
    finiteGalerkinCoarseVectorField nu aperture q lift coarseState =
      q (finiteGalerkinNavierStokesVectorField nu carrier aperture (lift coarseState)) := rfl

/-- The changing receiver defect is the complete hidden-state feedback return. -/
theorem finiteGalerkin_rateDefect_eq_chartRate_hidden_feedback
    (nu : ℝ) (aperture : Finset SpatialFrequency)
    (q : FluidState carrier →L[ℝ] Y)
    (lift : Y →L[ℝ] FluidState carrier)
    (chartRate : FluidState carrier →L[ℝ] Y)
    (state : FluidState carrier) :
    rateDefect q chartRate
        (finiteGalerkinNavierStokesVectorField nu carrier aperture)
        (finiteGalerkinCoarseVectorField nu aperture q lift) state =
      chartRate state + q (
        finiteGalerkinStokesPart nu (hiddenState q lift state) -
          finiteGalerkinProjectedInteraction carrier aperture
            (hiddenState q lift state) (resolvedState q lift state) -
          finiteGalerkinProjectedInteraction carrier aperture
            (resolvedState q lift state) (hiddenState q lift state) -
          finiteGalerkinProjectedInteraction carrier aperture
            (hiddenState q lift state) (hiddenState q lift state)) := by
  unfold rateDefect finiteGalerkinCoarseVectorField
  change chartRate state + q
      (finiteGalerkinNavierStokesVectorField nu carrier aperture state) -
      q (finiteGalerkinNavierStokesVectorField nu carrier aperture
        (resolvedState q lift state)) = _
  rw [add_sub_assoc, ← map_sub]
  have hstate := finiteGalerkinNavierStokesVectorField_sub
    nu carrier aperture state (resolvedState q lift state)
  rw [hstate]
  rw [finiteGalerkinProjectedInteraction_self_sub_self]
  unfold hiddenState resolvedState
  rw [map_sub]
  rw [← map_sub]
  congr 1
  unfold finiteGalerkinStokesPart
  congr 1
  module

theorem finiteGalerkin_rateDefect_eq_hidden_feedback
    (nu : ℝ) (aperture : Finset SpatialFrequency)
    (q : FluidState carrier →L[ℝ] Y)
    (lift : Y →L[ℝ] FluidState carrier)
    (state : FluidState carrier) :
    rateDefect q 0
        (finiteGalerkinNavierStokesVectorField nu carrier aperture)
        (finiteGalerkinCoarseVectorField nu aperture q lift) state =
      (0 : Y) + q (
        finiteGalerkinStokesPart nu (hiddenState q lift state) -
          finiteGalerkinProjectedInteraction carrier aperture
            (hiddenState q lift state) (resolvedState q lift state) -
          finiteGalerkinProjectedInteraction carrier aperture
            (resolvedState q lift state) (hiddenState q lift state) -
          finiteGalerkinProjectedInteraction carrier aperture
            (hiddenState q lift state) (hiddenState q lift state)) := by
  simpa using finiteGalerkin_rateDefect_eq_chartRate_hidden_feedback
    nu aperture q lift 0 state

theorem finiteGalerkin_rateDefect_eq_hidden_feedback_of_section
    (nu : ℝ) (aperture : Finset SpatialFrequency)
    (q : FluidState carrier →L[ℝ] Y)
    (lift : Y →L[ℝ] FluidState carrier)
    (hsection : q.comp lift = ContinuousLinearMap.id ℝ Y)
    (state : FluidState carrier) :
    q (hiddenState q lift state) = 0 ∧
      rateDefect q 0
          (finiteGalerkinNavierStokesVectorField nu carrier aperture)
          (finiteGalerkinCoarseVectorField nu aperture q lift) state =
        (0 : Y) + q (
          finiteGalerkinStokesPart nu (hiddenState q lift state) -
            finiteGalerkinProjectedInteraction carrier aperture
              (hiddenState q lift state) (resolvedState q lift state) -
            finiteGalerkinProjectedInteraction carrier aperture
              (resolvedState q lift state) (hiddenState q lift state) -
            finiteGalerkinProjectedInteraction carrier aperture
              (hiddenState q lift state) (hiddenState q lift state)) := by
  exact ⟨q_hiddenState_eq_zero q lift hsection state,
    finiteGalerkin_rateDefect_eq_hidden_feedback nu aperture q lift state⟩

/-- The actual Galerkin trajectory, received through a moving chart, obeys the complete coarse
equation with the exhibited unresolved-mode feedback. The derivative hypotheses bind the maps
to the trajectory; the algebra alone does not assert a continuum solution. -/
theorem moving_galerkin_receiver_equation
    (nu : ℝ) (aperture : Finset SpatialFrequency)
    (q : ℝ → FluidState carrier →L[ℝ] Y)
    (state : ℝ → FluidState carrier) (time : ℝ)
    (lift : Y →L[ℝ] FluidState carrier)
    (chartRate : FluidState carrier →L[ℝ] Y)
    (hchart : HasDerivAt q chartRate time)
    (hstate : HasDerivAt state
      (finiteGalerkinNavierStokesVectorField nu carrier aperture (state time)) time) :
    HasDerivAt (fun t ↦ q t (state t))
      (finiteGalerkinCoarseVectorField nu aperture (q time) lift (q time (state time)) +
        (chartRate (state time) + q time (
          finiteGalerkinStokesPart nu (hiddenState (q time) lift (state time)) -
            finiteGalerkinProjectedInteraction carrier aperture
              (hiddenState (q time) lift (state time)) (resolvedState (q time) lift (state time)) -
            finiteGalerkinProjectedInteraction carrier aperture
              (resolvedState (q time) lift (state time)) (hiddenState (q time) lift (state time)) -
            finiteGalerkinProjectedInteraction carrier aperture
              (hiddenState (q time) lift (state time)) (hiddenState (q time) lift (state time)))))
      time := by
  have h := moving_receiver_rate q state time chartRate
    (finiteGalerkinNavierStokesVectorField nu carrier aperture)
    (finiteGalerkinCoarseVectorField nu aperture (q time) lift) hchart hstate
  rw [finiteGalerkin_rateDefect_eq_chartRate_hidden_feedback] at h
  exact h

/-- At a cut whose receiver and lift are identity, chart motion is still a real receiver-rate
term. It cannot be dropped merely because the current hidden state vanishes. -/
theorem full_receiver_retains_chart_motion
    (nu : ℝ) (aperture : Finset SpatialFrequency)
    (chartRate : FluidState carrier →L[ℝ] FluidState carrier)
    (state : FluidState carrier) :
    rateDefect (ContinuousLinearMap.id ℝ (FluidState carrier)) chartRate
        (finiteGalerkinNavierStokesVectorField nu carrier aperture)
        (finiteGalerkinCoarseVectorField nu aperture
          (ContinuousLinearMap.id ℝ (FluidState carrier))
          (ContinuousLinearMap.id ℝ (FluidState carrier))) state = chartRate state := by
  simp [rateDefect, finiteGalerkinCoarseVectorField]

/-- A quantitative receiver of the full defect, using the existing carrier/aperture-dependent
quadratic bound. It is taken after the exact signed feedback and carries no uniform continuum
bound or automatic choice of truncation. -/
theorem norm_fluid_rateDefect_le
    (nu : ℝ) (aperture : Finset SpatialFrequency)
    (q : FluidState carrier →L[ℝ] Y)
    (lift : Y →L[ℝ] FluidState carrier)
    (chartRate : FluidState carrier →L[ℝ] Y)
    (state : FluidState carrier) :
    ‖rateDefect q chartRate
      (finiteGalerkinNavierStokesVectorField nu carrier aperture)
      (finiteGalerkinCoarseVectorField nu aperture q lift) state‖ ≤
      ‖chartRate state‖ + ‖q‖ *
        (‖finiteGalerkinStokesPart nu (hiddenState q lift state)‖ +
          finiteGalerkinInteractionCost carrier aperture *
            (2 * ‖resolvedState q lift state‖ + ‖hiddenState q lift state‖) *
            ‖hiddenState q lift state‖) := by
  have hdelta := finiteGalerkinNavierStokesVectorField_sub
    nu carrier aperture state (resolvedState q lift state)
  change _ = finiteGalerkinStokesPart nu (hiddenState q lift state) -
    (finiteGalerkinProjectedInteraction carrier aperture state state -
      finiteGalerkinProjectedInteraction carrier aperture
        (resolvedState q lift state) (resolvedState q lift state)) at hdelta
  have hbound := norm_finiteGalerkinProjectedInteraction_self_sub_self_le
    carrier aperture state (resolvedState q lift state)
  unfold rateDefect finiteGalerkinCoarseVectorField
  rw [add_sub_assoc, ← map_sub]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ((q.le_opNorm _).trans ?_))
  dsimp only [resolvedState] at hdelta
  rw [hdelta]
  exact mul_le_mul_of_nonneg_left
    ((norm_sub_le _ _).trans (add_le_add le_rfl hbound)) (norm_nonneg q)

end Soma.Holonics.Physics.FluidReceiverClosure

section Audit
open Soma.Holonics.Physics.FluidReceiverClosure
#print axioms q_hiddenState_eq_zero
#print axioms finiteGalerkin_rateDefect_eq_hidden_feedback
#print axioms finiteGalerkin_rateDefect_eq_hidden_feedback_of_section
#print axioms finiteGalerkin_rateDefect_eq_chartRate_hidden_feedback
#print axioms moving_galerkin_receiver_equation
#print axioms full_receiver_retains_chart_motion
#print axioms norm_fluid_rateDefect_le
end Audit
