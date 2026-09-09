import ElementaryHolonics.Foundation.InformationReceiver
import ElementaryHolonics.Millennium.HolonicMembraneActionTransport

/-!
# Receiver-relative information differences

Information loss is kept as a difference between declared receiver faces.  These identities do not
introduce a learner, a force law, or a global information state.  The final obstruction reuses the
existing cross-entropy receiver fibre: a scalar face cannot determine a later physical/current
face when two admitted occurrences share that scalar and differ at the later face.
-/

noncomputable section

namespace Soma.Holonics.Physics.InformationDifference

open scoped BigOperators
open Soma.Holonics.Computation.HolonicInformationTheory
open Soma.Holonics.Computation.HolonicInformationTheory.PositiveProbabilitySection
open Soma.Holonics.Millennium.HolonicMembraneActionTransport

variable {Index : Type*} [Fintype Index]

def energyExpectation (energy : Index → ℝ)
    (p : PositiveProbabilitySection Index) : ℝ :=
  ∑ index, p.mass index * energy index

def freeEnergy (thermalScale : ℝ) (energy : Index → ℝ)
    (p : PositiveProbabilitySection Index) : ℝ :=
  energyExpectation energy p - thermalScale * entropy p

theorem crossEntropy_self_eq_entropy (p : PositiveProbabilitySection Index) :
    crossEntropy p p = entropy p := by
  rfl

theorem crossEntropy_excess_eq_kl
    (reference emitted : PositiveProbabilitySection Index) :
    crossEntropy reference emitted - entropy reference =
      klDivergence reference emitted := by
  rw [crossEntropy_eq_entropy_add_kl]
  ring

theorem thermal_crossEntropy_identity
    (thermalScale : ℝ) (energy : Index → ℝ) (logZ : ℝ)
    (p q : PositiveProbabilitySection Index)
    (canonical : ∀ index,
      thermalScale * Real.log (q.mass index) =
        -energy index - thermalScale * logZ) :
    thermalScale * crossEntropy p q =
      energyExpectation energy p + thermalScale * logZ := by
  unfold crossEntropy energyExpectation
  calc
    thermalScale * (-∑ index, p.mass index * Real.log (q.mass index)) =
        ∑ index, p.mass index * (-thermalScale * Real.log (q.mass index)) := by
      rw [mul_neg, Finset.mul_sum]
      calc
        -(∑ index, thermalScale * (p.mass index * Real.log (q.mass index))) =
            -(∑ index, p.mass index * (thermalScale * Real.log (q.mass index))) := by
          congr 1
          apply Finset.sum_congr rfl
          intro index hindex
          ring
        _ = ∑ index, p.mass index * (-thermalScale * Real.log (q.mass index)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro index hindex
          ring
    _ = ∑ index, p.mass index * (energy index + thermalScale * logZ) := by
      apply Finset.sum_congr rfl
      intro index hindex
      have h := canonical index
      rw [show -thermalScale * Real.log (q.mass index) =
          energy index + thermalScale * logZ by linarith]
    _ = ∑ index, p.mass index * energy index + thermalScale * logZ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      rw [show (fun index => p.mass index * (thermalScale * logZ)) =
          (fun index => (thermalScale * logZ) * p.mass index) by
            funext index; ring]
      rw [← Finset.mul_sum, p.normalized]
      ring

theorem freeEnergy_difference_eq_thermalScale_mul_kl
    (thermalScale : ℝ) (energy : Index → ℝ) (logZ : ℝ)
    (p q : PositiveProbabilitySection Index)
    (canonical : ∀ index,
      thermalScale * Real.log (q.mass index) =
        -energy index - thermalScale * logZ) :
    freeEnergy thermalScale energy p - freeEnergy thermalScale energy q =
      thermalScale * klDivergence p q := by
  have hpq := thermal_crossEntropy_identity thermalScale energy logZ p q canonical
  have hqq := thermal_crossEntropy_identity thermalScale energy logZ q q canonical
  rw [crossEntropy_self_eq_entropy q] at hqq
  have hkl : thermalScale * crossEntropy p q - thermalScale * entropy p =
      thermalScale * klDivergence p q := by
    calc
      thermalScale * crossEntropy p q - thermalScale * entropy p =
          thermalScale * (crossEntropy p q - entropy p) := by ring
      _ = thermalScale * klDivergence p q := by
        rw [crossEntropy_excess_eq_kl]
  unfold freeEnergy
  linarith

def halfSection : PositiveProbabilitySection Bool where
  mass := fun _ ↦ (1 / 2 : ℝ)
  positive := by intro index; norm_num
  normalized := by norm_num [Fintype.sum_bool]

theorem halfSection_crossEntropy_ne_zero :
    crossEntropy halfSection halfSection ≠ 0 := by
  rw [crossEntropy_self_eq_entropy]
  unfold entropy halfSection
  norm_num [Fintype.sum_bool]

theorem no_current_factor_of_equal_crossEntropy
    {Action Current : Type*} {Index : Type*} [Fintype Index]
    (receiver : FiniteCrossEntropyReceiver Action Index)
    (current : Action → Current) {left right : Action}
    (equalFace : receiver.face left = receiver.face right)
    (separated : current left ≠ current right) :
    ¬ ∃ factor : ℝ → Current, ∀ action,
      current action = factor (receiver.face action) := by
  rintro ⟨factor, factors⟩
  apply separated
  calc
    current left = factor (receiver.face left) := factors left
    _ = factor (receiver.face right) := congrArg factor equalFace
    _ = current right := (factors right).symm

theorem membrane_tail_scalar_does_not_determine_action :
    ¬ ∃ factor : ℝ → Bool, ∀ action,
      action = factor (tailCrossEntropyReceiver.face action) :=
  tailCrossEntropyReceiver_no_identitySuccessorFactor

section Audit

#print axioms crossEntropy_self_eq_entropy
#print axioms crossEntropy_excess_eq_kl
#print axioms halfSection_crossEntropy_ne_zero
#print axioms no_current_factor_of_equal_crossEntropy
#print axioms membrane_tail_scalar_does_not_determine_action
#print axioms thermal_crossEntropy_identity
#print axioms freeEnergy_difference_eq_thermalScale_mul_kl

end Audit

end Soma.Holonics.Physics.InformationDifference
