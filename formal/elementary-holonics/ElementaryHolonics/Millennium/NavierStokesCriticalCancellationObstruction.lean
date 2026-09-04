import ElementaryHolonics.Millennium.HolonicComplexParametron
import ElementaryHolonics.Millennium.NavierStokesFourierTriads

/-!
# Cancellation cannot be recovered after absolute coefficient mass

**[proved-derived; formal-checked]**  The finite Fourier-triad owner and the Complex Parametron
owner both retain exact oriented cancellation before a norm receiver is applied.  This file records
the corresponding reconstruction obstruction: an exchanged divergence-free triad pair and a
half-turn phase pair have zero oriented return, while their absolute occurrence mass is twice the
norm of either surviving face.

Repeating one nonzero opposite-phase pair at every dyadic address therefore gives a pointwise-zero
oriented shell return whose absolute shell-mass population is not summable.  Consequently neither
the signed triad return nor the half-turn/holonomy quotient can, by itself, supply the `ℓ1`/Besov
shell service required by the current critical mild receiver.  A successful endpoint passage must
retain an additional scale-local receiver (for example a Dini, Lorentz, Carleson, or comparable
constitutive current) before absolute mass is taken.

This is a receiver counterexample.  It makes no claim about blow-up or about the existence of a
Navier--Stokes solution.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesCriticalCancellationObstruction

open Soma.Holonics.Millennium.HolonicComplexParametron
open Soma.Holonics.Millennium.HolonicParametron
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The generic two-occurrence reconstruction fibre -/

/-- Two oppositely oriented occurrences before the cancellation receiver is taken. -/
def oppositePhasePair (face : ℂ) : Fin 2 → ℂ
  | 0 => face
  | 1 => -face

/-- The signed return of the complete two-occurrence population. -/
def oppositePhasePairReturn (face : ℂ) : ℂ :=
  ∑ occurrence : Fin 2, oppositePhasePair face occurrence

/-- The absolute occurrence mass of the same population. -/
def oppositePhasePairAbsoluteMass (face : ℂ) : ℝ :=
  ∑ occurrence : Fin 2, ‖oppositePhasePair face occurrence‖

/-- The signed receiver collapses every opposite-phase pair. -/
@[simp]
theorem oppositePhasePairReturn_eq_zero (face : ℂ) :
    oppositePhasePairReturn face = 0 := by
  simp [oppositePhasePairReturn, oppositePhasePair, Fin.sum_univ_two]

/-- The complete reconstruction fibre still contains twice the norm of either face. -/
@[simp]
theorem oppositePhasePairAbsoluteMass_eq (face : ℂ) :
    oppositePhasePairAbsoluteMass face = 2 * ‖face‖ := by
  simp only [oppositePhasePairAbsoluteMass, oppositePhasePair, Fin.sum_univ_two, norm_neg]
  ring

/-- No scalar coefficient can reconstruct absolute occurrence mass from only the signed return.
The obstruction already fires on one unit face, independently of any frequency calibration. -/
theorem no_absoluteMass_factorization_through_oppositePhaseReturn :
    ¬ ∃ coefficient : ℝ, ∀ face : ℂ,
      oppositePhasePairAbsoluteMass face ≤
        coefficient * ‖oppositePhasePairReturn face‖ := by
  rintro ⟨coefficient, hcoefficient⟩
  have h := hcoefficient (1 : ℂ)
  simp at h
  linarith

/-! ## The exact Fourier-triad face has the same reconstruction fibre -/

/-- Absolute mass of the two exchanged energy faces for one addressed Fourier triad. -/
def exchangedTriadAbsoluteMass
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector) : ℝ :=
  ‖triadicEnergyFace triad.advecting triad.transported
      advectingMode transportedMode receiverMode‖ +
    ‖triadicEnergyFace triad.advecting triad.receiver
      advectingMode receiverMode transportedMode‖

/-- Exact signed cancellation does not reduce the absolute triad population: under the same
divergence hypothesis it is exactly twice the norm of the first exchanged face. -/
theorem exchangedTriadAbsoluteMass_eq_two_norm
    (triad : AddressedClosedFourierTriad)
    (advectingMode transportedMode receiverMode : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector triad.advecting) advectingMode = 0) :
    exchangedTriadAbsoluteMass triad advectingMode transportedMode receiverMode =
      2 * ‖triadicEnergyFace triad.advecting triad.transported
        advectingMode transportedMode receiverMode‖ := by
  have hcancel := exchanged_triadicEnergyFace_cancel triad
    advectingMode transportedMode receiverMode hdivergence
  have hsecond :
      triadicEnergyFace triad.advecting triad.receiver
          advectingMode receiverMode transportedMode =
        -triadicEnergyFace triad.advecting triad.transported
          advectingMode transportedMode receiverMode := by
    exact eq_neg_of_add_eq_zero_right hcancel
  unfold exchangedTriadAbsoluteMass
  rw [hsecond, norm_neg]
  ring

/-! ## The Complex Parametron half-turn has the same reconstruction fibre -/

/-- Signed return of one complete phase population together with its common half-turn. -/
def parametronHalfTurnReturn
    {Branch : Type*} [Fintype Branch]
    (amplitude phase : Branch → ℝ) : ℂ :=
  phaseSuperposition amplitude phase +
    phaseSuperposition amplitude (fun branch ↦ halfTurnSheet (phase branch))

/-- Absolute mass before the two phase sheets are condensed. -/
def parametronHalfTurnAbsoluteMass
    {Branch : Type*} [Fintype Branch]
    (amplitude phase : Branch → ℝ) : ℝ :=
  ‖phaseSuperposition amplitude phase‖ +
    ‖phaseSuperposition amplitude (fun branch ↦ halfTurnSheet (phase branch))‖

@[simp]
theorem parametronHalfTurnReturn_eq_zero
    {Branch : Type*} [Fintype Branch]
    (amplitude phase : Branch → ℝ) :
    parametronHalfTurnReturn amplitude phase = 0 := by
  rw [parametronHalfTurnReturn, phaseSuperposition_halfTurn]
  exact add_neg_cancel _

/-- A half-turn changes orientation, not absolute mass. -/
theorem parametronHalfTurnAbsoluteMass_eq_two_norm
    {Branch : Type*} [Fintype Branch]
    (amplitude phase : Branch → ℝ) :
    parametronHalfTurnAbsoluteMass amplitude phase =
      2 * ‖phaseSuperposition amplitude phase‖ := by
  rw [parametronHalfTurnAbsoluteMass, phaseSuperposition_halfTurn, norm_neg]
  ring

/-! ## Critical dyadic repetition: zero return, nonsummable absolute mass -/

/-- One identical unit opposite-phase pair at every dyadic address. -/
def criticalDyadicPhaseReturn (_level : ℕ) : ℂ :=
  oppositePhasePairReturn 1

/-- Absolute occurrence mass at the same dyadic address. -/
def criticalDyadicPhaseAbsoluteMass (_level : ℕ) : ℝ :=
  oppositePhasePairAbsoluteMass 1

@[simp]
theorem criticalDyadicPhaseReturn_eq_zero (level : ℕ) :
    criticalDyadicPhaseReturn level = 0 := by
  simp [criticalDyadicPhaseReturn]

@[simp]
theorem criticalDyadicPhaseAbsoluteMass_eq_two (level : ℕ) :
    criticalDyadicPhaseAbsoluteMass level = 2 := by
  simp [criticalDyadicPhaseAbsoluteMass]

/-- The constant critical shell population cannot furnish a summable absolute majorant, even
though its oriented return vanishes at every scale. -/
theorem not_summable_criticalDyadicPhaseAbsoluteMass :
    ¬ Summable criticalDyadicPhaseAbsoluteMass := by
  rw [show criticalDyadicPhaseAbsoluteMass = fun _ : ℕ ↦ (2 : ℝ) by
    funext level
    exact criticalDyadicPhaseAbsoluteMass_eq_two level]
  rw [summable_const_iff]
  norm_num

/-! ## Audit -/

#print axioms oppositePhasePairReturn_eq_zero
#print axioms oppositePhasePairAbsoluteMass_eq
#print axioms no_absoluteMass_factorization_through_oppositePhaseReturn
#print axioms exchangedTriadAbsoluteMass_eq_two_norm
#print axioms parametronHalfTurnReturn_eq_zero
#print axioms parametronHalfTurnAbsoluteMass_eq_two_norm
#print axioms not_summable_criticalDyadicPhaseAbsoluteMass

end Soma.Holonics.Millennium.NavierStokesCriticalCancellationObstruction
