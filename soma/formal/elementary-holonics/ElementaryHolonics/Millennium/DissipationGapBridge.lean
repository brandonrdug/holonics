import ElementaryHolonics.Millennium.NavierStokesPeriodicEnergy
import ElementaryHolonics.Millennium.HilbertTransportRefinement
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exact bridge from an energy balance and a dissipation gap

This file composes two already-returned owners without identifying their physical realizations.
`NavierStokesPeriodicEnergy` supplies an exact positive-time balance

`E' = -nu D + W`,

while `HilbertTransportRefinement` separates a coercive estimate `lambda E <= D` from the open
question of whether one positive `lambda` survives every refinement scale.  The abstract bridge
below records exactly what follows when both ports are present:

* the differential inequality `E' <= -(nu * lambda) E + W`;
* weak and strict unforced decay, including an interval exponential comparison;
* the obstruction to a positive unforced stationary state;
* exact forced balance at a stationary occurrence, and equality when the gap is saturated.

The final two sections attach the abstract ports to the actual periodic Navier--Stokes energy law
and to actual finite Hilbert transport complexes.  They do not assert a Navier--Stokes coercive
estimate, a scale-uniform Yang--Mills gap, a continuum realization, or global regularity.

Truth status: the two predicates are `definition`; every theorem is `proved-derived`; the
problem-specific coercive and uniform-limit hypotheses remain `open` unless explicitly supplied.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.DissipationGapBridge

/-- An exact energy-dissipation-work balance on the named time population. -/
def EnergyBalanceOn (S : Set ℝ) (nu : ℝ)
    (E D W : ℝ → ℝ) : Prop :=
  ∀ t, t ∈ S → HasDerivAt E (-nu * D t + W t) t

/-- A quantitative dissipation separator on the named time population. -/
def DissipationGapOn (S : Set ℝ) (lambda : ℝ)
    (E D : ℝ → ℝ) : Prop :=
  ∀ t, t ∈ S → lambda * E t ≤ D t

/-- The exact balance identifies the ordinary derivative at every admitted occurrence. -/
theorem deriv_eq_viscous_dissipation_add_work
    {S : Set ℝ} {nu : ℝ} {E D W : ℝ → ℝ}
    (hbalance : EnergyBalanceOn S nu E D W) {t : ℝ} (ht : t ∈ S) :
    deriv E t = -nu * D t + W t :=
  (hbalance t ht).deriv

/-- A gap converts the exact balance into the forced differential inequality. -/
theorem derivative_le_forcing_sub_gap
    {S : Set ℝ} {nu lambda : ℝ} {E D W : ℝ → ℝ}
    (hbalance : EnergyBalanceOn S nu E D W)
    (hgap : DissipationGapOn S lambda E D)
    (hnu : 0 ≤ nu) {t : ℝ} (ht : t ∈ S) :
    deriv E t ≤ -(nu * lambda) * E t + W t := by
  rw [deriv_eq_viscous_dissipation_add_work hbalance ht]
  have hscaled : nu * (lambda * E t) <= nu * D t :=
    mul_le_mul_of_nonneg_left (hgap t ht) hnu
  calc
    -nu * D t + W t <= -nu * (lambda * E t) + W t := by
      simpa [add_comm] using add_le_add_right (neg_le_neg hscaled) (W t)
    _ = -(nu * lambda) * E t + W t := by ring

/-- With no work input, nonnegative viscosity, gap, and energy make the instantaneous energy
derivative nonpositive. -/
theorem unforced_derivative_nonpositive
    {S : Set ℝ} {nu lambda : ℝ} {E D W : ℝ → ℝ}
    (hbalance : EnergyBalanceOn S nu E D W)
    (hgap : DissipationGapOn S lambda E D)
    (hnu : 0 ≤ nu) (hlambda : 0 ≤ lambda)
    {t : ℝ} (ht : t ∈ S) (henergy : 0 ≤ E t) (hwork : W t = 0) :
    deriv E t ≤ 0 := by
  calc
    deriv E t <= -(nu * lambda) * E t + W t :=
      derivative_le_forcing_sub_gap hbalance hgap hnu ht
    _ = -(nu * lambda) * E t := by rw [hwork, add_zero]
    _ <= 0 := by
      simpa [mul_assoc] using
        neg_nonpos.mpr (mul_nonneg (mul_nonneg hnu hlambda) henergy)

/-- Positive viscosity, gap, and energy make the unforced instantaneous decay strict. -/
theorem unforced_derivative_negative
    {S : Set ℝ} {nu lambda : ℝ} {E D W : ℝ → ℝ}
    (hbalance : EnergyBalanceOn S nu E D W)
    (hgap : DissipationGapOn S lambda E D)
    (hnu : 0 < nu) (hlambda : 0 < lambda)
    {t : ℝ} (ht : t ∈ S) (henergy : 0 < E t) (hwork : W t = 0) :
    deriv E t < 0 := by
  have hbound := derivative_le_forcing_sub_gap hbalance hgap hnu.le ht
  rw [hwork, add_zero] at hbound
  exact lt_of_le_of_lt hbound (by
    simpa [mul_assoc] using neg_neg_of_pos (mul_pos (mul_pos hnu hlambda) henergy))

/-- At a stationary occurrence, exact work input equals viscous dissipation. -/
theorem stationary_forcing_eq_viscous_dissipation
    {S : Set ℝ} {nu : ℝ} {E D W : ℝ → ℝ}
    (hbalance : EnergyBalanceOn S nu E D W)
    {t : ℝ} (ht : t ∈ S) (hstationary : deriv E t = 0) :
    W t = nu * D t := by
  have hderiv := deriv_eq_viscous_dissipation_add_work hbalance ht
  linarith

/-- At stationarity, nonnegative viscosity and a gap force the work input to dominate the gap
reading. -/
theorem stationary_forcing_ge_gap_reading
    {S : Set ℝ} {nu lambda : ℝ} {E D W : ℝ → ℝ}
    (hbalance : EnergyBalanceOn S nu E D W)
    (hgap : DissipationGapOn S lambda E D)
    (hnu : 0 ≤ nu) {t : ℝ} (ht : t ∈ S)
    (hstationary : deriv E t = 0) :
    nu * lambda * E t ≤ W t := by
  rw [stationary_forcing_eq_viscous_dissipation hbalance ht hstationary]
  have := mul_le_mul_of_nonneg_left (hgap t ht) hnu
  nlinarith

/-- If the dissipation gap is saturated, stationary forcing balances the gap reading exactly. -/
theorem stationary_forcing_eq_gap_reading_of_exact
    {S : Set ℝ} {nu lambda : ℝ} {E D W : ℝ → ℝ}
    (hbalance : EnergyBalanceOn S nu E D W)
    {t : ℝ} (ht : t ∈ S) (hstationary : deriv E t = 0)
    (hexact : D t = lambda * E t) :
    W t = nu * lambda * E t := by
  rw [stationary_forcing_eq_viscous_dissipation hbalance ht hstationary, hexact]
  ring

/-- A positive-energy unforced occurrence cannot be stationary when viscosity and the gap are
strictly positive. -/
theorem no_positive_unforced_stationary_occurrence
    {S : Set ℝ} {nu lambda : ℝ} {E D W : ℝ → ℝ}
    (hbalance : EnergyBalanceOn S nu E D W)
    (hgap : DissipationGapOn S lambda E D)
    (hnu : 0 < nu) (hlambda : 0 < lambda)
    {t : ℝ} (ht : t ∈ S) (henergy : 0 < E t) (hwork : W t = 0) :
    deriv E t ≠ 0 := by
  have hnegative :=
    unforced_derivative_negative hbalance hgap hnu hlambda ht henergy hwork
  exact ne_of_lt hnegative

/-- Consequently, a nonnegative-energy unforced stationary occurrence has zero energy. -/
theorem unforced_stationary_energy_eq_zero
    {S : Set ℝ} {nu lambda : ℝ} {E D W : ℝ → ℝ}
    (hbalance : EnergyBalanceOn S nu E D W)
    (hgap : DissipationGapOn S lambda E D)
    (hnu : 0 < nu) (hlambda : 0 < lambda)
    {t : ℝ} (ht : t ∈ S) (henergy : 0 ≤ E t) (hwork : W t = 0)
    (hstationary : deriv E t = 0) :
    E t = 0 := by
  apply le_antisymm
  · by_contra hnot
    have hpositive : 0 < E t := lt_of_not_ge hnot
    exact (no_positive_unforced_stationary_occurrence
      hbalance hgap hnu hlambda ht hpositive hwork) hstationary
  · exact henergy

/-! ## Interval consequences -/

/-- The unforced energy is weakly decreasing on an interval when its energy is nonnegative there. -/
theorem unforced_energy_antitoneOn
    {a b nu lambda : ℝ} {E D W : ℝ → ℝ}
    (hbalance : EnergyBalanceOn (Icc a b) nu E D W)
    (hgap : DissipationGapOn (Icc a b) lambda E D)
    (hnu : 0 ≤ nu) (hlambda : 0 ≤ lambda)
    (henergy : ∀ t ∈ Icc a b, 0 ≤ E t)
    (hwork : ∀ t ∈ Icc a b, W t = 0) :
    AntitoneOn E (Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
  · intro t ht
    exact (hbalance t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hbalance t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    exact unforced_derivative_nonpositive hbalance hgap hnu hlambda
      (interior_subset ht) (henergy t (interior_subset ht))
      (hwork t (interior_subset ht))

/-- If the energy stays positive in the interval interior, the unforced decay is strict. -/
theorem unforced_energy_strictAntiOn
    {a b nu lambda : ℝ} {E D W : ℝ → ℝ}
    (hbalance : EnergyBalanceOn (Icc a b) nu E D W)
    (hgap : DissipationGapOn (Icc a b) lambda E D)
    (hnu : 0 < nu) (hlambda : 0 < lambda)
    (henergy : ∀ t ∈ interior (Icc a b), 0 < E t)
    (hwork : ∀ t ∈ Icc a b, W t = 0) :
    StrictAntiOn E (Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a b)
  · intro t ht
    exact (hbalance t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact unforced_derivative_negative hbalance hgap hnu hlambda
      (interior_subset ht) (henergy t ht) (hwork t (interior_subset ht))

/-- The integrating-factor receiver for a proposed decay rate. -/
def weightedEnergy (rate : ℝ) (E : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (rate * t) * E t

/-- Exact differentiation of the integrating-factor receiver. -/
theorem hasDerivAt_weightedEnergy
    {rate t E' : ℝ} {E : ℝ → ℝ} (hE : HasDerivAt E E' t) :
    HasDerivAt (weightedEnergy rate E)
      (Real.exp (rate * t) * (E' + rate * E t)) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (rate * s))
      (Real.exp (rate * t) * rate) t := by
    simpa using ((hasDerivAt_id t).const_mul rate).exp
  unfold weightedEnergy
  apply (hexp.mul hE).congr_deriv
  ring

/-- Under an unforced gap, the integrating-factor receiver is antitone. -/
theorem unforced_weightedEnergy_antitoneOn
    {a b nu lambda : ℝ} {E D W : ℝ → ℝ}
    (hbalance : EnergyBalanceOn (Icc a b) nu E D W)
    (hgap : DissipationGapOn (Icc a b) lambda E D)
    (hnu : 0 ≤ nu)
    (hwork : ∀ t ∈ Icc a b, W t = 0) :
    AntitoneOn (weightedEnergy (nu * lambda) E) (Icc a b) := by
  let weightedDerivative : ℝ → ℝ := fun t =>
    Real.exp ((nu * lambda) * t) *
      ((-nu * D t + W t) + (nu * lambda) * E t)
  have hweighted : ∀ t ∈ Icc a b,
      HasDerivAt (weightedEnergy (nu * lambda) E) (weightedDerivative t) t := by
    intro t ht
    exact hasDerivAt_weightedEnergy (hbalance t ht)
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
  · intro t ht
    exact (hweighted t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hweighted t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hweighted t (interior_subset ht)).deriv]
    dsimp [weightedDerivative]
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    rw [hwork t (interior_subset ht)]
    calc
      -nu * D t + 0 + (nu * lambda) * E t =
          nu * (lambda * E t - D t) := by ring
      _ <= 0 := mul_nonpos_of_nonneg_of_nonpos hnu
        (sub_nonpos.mpr (hgap t (interior_subset ht)))

/-- The exact exponential comparison returned by the unforced gap.  Positivity of `nu` and
`lambda` turns the displayed factor into genuine decay; no continuum-uniform value is inferred. -/
theorem unforced_exponential_comparison
    {a b nu lambda : ℝ} {E D W : ℝ → ℝ}
    (hbalance : EnergyBalanceOn (Icc a b) nu E D W)
    (hgap : DissipationGapOn (Icc a b) lambda E D)
    (hnu : 0 ≤ nu)
    (hwork : ∀ t ∈ Icc a b, W t = 0)
    (hab : a ≤ b) :
    E b ≤ Real.exp (-(nu * lambda) * (b - a)) * E a := by
  have hantitone := unforced_weightedEnergy_antitoneOn hbalance hgap hnu hwork
  have hweighted :
      weightedEnergy (nu * lambda) E b <= weightedEnergy (nu * lambda) E a :=
    hantitone ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hexpPositive : 0 < Real.exp ((nu * lambda) * b) := Real.exp_pos _
  calc
    E b <= (Real.exp ((nu * lambda) * a) * E a) /
        Real.exp ((nu * lambda) * b) := by
      apply (le_div_iff₀ hexpPositive).2
      simpa [weightedEnergy, mul_comm] using hweighted
    _ = Real.exp (-(nu * lambda) * (b - a)) * E a := by
      calc
        (Real.exp ((nu * lambda) * a) * E a) /
            Real.exp ((nu * lambda) * b) =
            (Real.exp ((nu * lambda) * a) /
              Real.exp ((nu * lambda) * b)) * E a := by ring
        _ = Real.exp ((nu * lambda) * a - (nu * lambda) * b) * E a := by
          rw [Real.exp_sub]
        _ = Real.exp (-(nu * lambda) * (b - a)) * E a := by
          congr 2
          ring

/-! ## Attachment to the actual periodic Navier--Stokes balance -/

namespace NavierStokesAttachment

open MeasureTheory
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy

/-- The full component-gradient population in the proved periodic energy equality. -/
def periodicDissipation (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∫ x in unitCube, ∑ i : Fin 3,
    ‖gradient (fun y ↦ velocity y t i) x‖ ^ 2

/-- The forcing-work population in the proved periodic energy equality. -/
def periodicForcingWork (force velocity : VelocityField) (t : ℝ) : ℝ :=
  ∫ x in unitCube, inner ℝ (force x t) (velocity x t)

/-- The concrete periodic solution fills the abstract exact-balance port at every positive time. -/
theorem periodicSolution_energyBalanceOn_positiveTime
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure) :
    EnergyBalanceOn (Ioi 0) nu
      (periodicKineticEnergy velocity)
      (periodicDissipation velocity)
      (periodicForcingWork force velocity) := by
  intro t ht
  simpa [periodicDissipation, periodicForcingWork] using
    periodicSolution_hasDerivAt_periodicKineticEnergy solution t ht

/-- Any separately proved periodic dissipation gap therefore gives the exact differential
inequality.  The gap is an input, not a conclusion of the energy equality. -/
theorem periodicSolution_derivative_le_forcing_sub_gap
    {nu lambda : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (hgap : DissipationGapOn (Ioi 0) lambda
      (periodicKineticEnergy velocity) (periodicDissipation velocity))
    (hnu : 0 ≤ nu) {t : ℝ} (ht : 0 < t) :
    deriv (periodicKineticEnergy velocity) t ≤
      -(nu * lambda) * periodicKineticEnergy velocity t +
        periodicForcingWork force velocity t :=
  derivative_le_forcing_sub_gap
    (periodicSolution_energyBalanceOn_positiveTime solution) hgap hnu ht

end NavierStokesAttachment

/-! ## Attachment to actual finite Hilbert transport gaps -/

namespace HilbertAttachment

open Soma.Holonics.Millennium.Coupling

universe u

variable {Scale : Type u} [Preorder Scale] [Nonempty Scale]

/-- Each actual finite scale supplies a positive pathwise separator.  The witness may depend on
the scale and is not promoted to a continuum-uniform gap. -/
theorem eachFiniteScale_supplies_pathwise_gap
    (system : DirectedHilbertTransportSystem Scale) (scale : Scale)
    (S : Set ℝ)
    (path : ℝ → (system.object scale).chain.nonharmonic) :
    ∃ lambda : ℝ, 0 < lambda ∧
      DissipationGapOn S lambda
        (fun t => norm (path t) ^ 2)
        (fun t => (system.object scale).chain.nonharmonicReceiverForm.B
          (path t) (path t)) := by
  obtain ⟨lambda, hlambda, hgap⟩ := system.eachScaleHasNonharmonicGap scale
  exact ⟨lambda, hlambda, fun t _ht => hgap (path t)⟩

/-- A supplied uniform Hilbert gap gives the same pathwise separator at every scale.  Existence of
that uniform hypothesis remains exactly the open alternative isolated by the refinement owner. -/
theorem uniformGap_supplies_all_pathwise_gaps
    (system : DirectedHilbertTransportSystem Scale)
    (huniform : system.HasUniformNonharmonicGap)
    (S : Set ℝ) :
    ∃ lambda : ℝ, 0 < lambda ∧
      ∀ (scale : Scale)
        (path : ℝ → (system.object scale).chain.nonharmonic),
        DissipationGapOn S lambda
          (fun t => norm (path t) ^ 2)
          (fun t => (system.object scale).chain.nonharmonicReceiverForm.B
            (path t) (path t)) := by
  obtain ⟨lambda, hlambda, hgap⟩ := huniform
  exact ⟨lambda, hlambda, fun scale path t _ht => hgap scale (path t)⟩

end HilbertAttachment

end Soma.Holonics.Millennium.DissipationGapBridge
