import Holonics.Foundation.InformationReceiver
import Holonics.Foundation.FiniteCrossEntropyReceiver
import Mathlib.Data.Complex.Basic

/-!
# Receiver-relative information differences

Information loss is kept as a difference between declared receiver faces.  These identities do not
introduce a learner, a force law, or a global information state.  The final obstruction reuses the
existing cross-entropy receiver fibre: a scalar face cannot determine a later physical/current
face when two admitted occurrences share that scalar and differ at the later face.
-/

noncomputable section

namespace Holonics.Physics.InformationDifference

open scoped BigOperators
open Holonics.Computation.HolonicInformationTheory
open Holonics.Computation.HolonicInformationTheory.PositiveProbabilitySection
open Holonics.Foundation.HolonicMembraneActionTransport

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

/-! ## Lifted phase information and its parity

The phase is a supplied real lift, including winding. Conjugating that lift is a declared
comparison involution; it neither exchanges the source/reference distributions nor reverses
physical chronology. These definitions formalize the existing complex-information construction
recorded on September 12, before any scalar phase mean is used as a future state.
-/

def phaseMean (p : PositiveProbabilitySection Index) (phase : Index → ℝ) : ℝ :=
  ∑ index, p.mass index * phase index

theorem phaseMean_add (p : PositiveProbabilitySection Index) (a b : Index → ℝ) :
    phaseMean p (fun i => a i + b i) = phaseMean p a + phaseMean p b := by
  simp [phaseMean, mul_add, Finset.sum_add_distrib]

theorem phaseMean_sub (p : PositiveProbabilitySection Index) (a b : Index → ℝ) :
    phaseMean p (fun i => a i - b i) = phaseMean p a - phaseMean p b := by
  simp [phaseMean, mul_sub, Finset.sum_sub_distrib]

theorem phaseMean_neg (p : PositiveProbabilitySection Index) (a : Index → ℝ) :
    phaseMean p (fun i => -a i) = -phaseMean p a := by
  simp [phaseMean, Finset.sum_neg_distrib]

/-- Probability-calibrated information in bits, paired with the retained angular-lift reading.
The factor two converts the logarithm of an amplitude to the logarithm of its intensity. -/
def liftedCrossEntropy (p q : PositiveProbabilitySection Index) (phase : Index → ℝ) : ℂ :=
  ⟨crossEntropy p q / Real.log 2, -(2 / Real.log 2) * phaseMean p phase⟩

theorem liftedCrossEntropy_real (p q : PositiveProbabilitySection Index)
    (phase : Index → ℝ) :
    (liftedCrossEntropy p q phase).re = crossEntropy p q / Real.log 2 := rfl

theorem liftedCrossEntropy_excess (p q : PositiveProbabilitySection Index)
    (sourcePhase receiverPhase : Index → ℝ) :
    liftedCrossEntropy p q receiverPhase - liftedCrossEntropy p p sourcePhase =
      (⟨klDivergence p q / Real.log 2,
        -(2 / Real.log 2) * phaseMean p (fun i => receiverPhase i - sourcePhase i)⟩ : ℂ) := by
  apply Complex.ext
  · change crossEntropy p q / Real.log 2 - crossEntropy p p / Real.log 2 = _
    rw [← sub_div, crossEntropy_self_eq_entropy, crossEntropy_excess_eq_kl]
  · change -(2 / Real.log 2) * phaseMean p receiverPhase -
        -(2 / Real.log 2) * phaseMean p sourcePhase = _
    rw [phaseMean_sub]
    ring

/-- The code-length face is even and the phase face odd under simultaneous lift conjugation. -/
theorem liftedCrossEntropy_conjugate (p q : PositiveProbabilitySection Index)
    (phase : Index → ℝ) :
    liftedCrossEntropy p q (fun i => -phase i) = star (liftedCrossEntropy p q phase) := by
  apply Complex.ext <;> simp [liftedCrossEntropy, phaseMean_neg]

/-- A common channel-wise rechart of the compared phase lifts cancels from their difference. -/
theorem liftedCrossEntropy_commonPhase (p q : PositiveProbabilitySection Index)
    (sourcePhase receiverPhase shift : Index → ℝ) :
    liftedCrossEntropy p q (fun i => receiverPhase i + shift i) -
        liftedCrossEntropy p p (fun i => sourcePhase i + shift i) =
      liftedCrossEntropy p q receiverPhase - liftedCrossEntropy p p sourcePhase := by
  apply Complex.ext
  · rfl
  · change -(2 / Real.log 2) * phaseMean p (fun i => receiverPhase i + shift i) -
        -(2 / Real.log 2) * phaseMean p (fun i => sourcePhase i + shift i) = _
    rw [phaseMean_add, phaseMean_add]
    change _ = -(2 / Real.log 2) * phaseMean p receiverPhase -
      -(2 / Real.log 2) * phaseMean p sourcePhase
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

section Audit

#print axioms crossEntropy_self_eq_entropy
#print axioms crossEntropy_excess_eq_kl
#print axioms halfSection_crossEntropy_ne_zero
#print axioms no_current_factor_of_equal_crossEntropy
#print axioms thermal_crossEntropy_identity
#print axioms freeEnergy_difference_eq_thermalScale_mul_kl
#print axioms liftedCrossEntropy_real
#print axioms liftedCrossEntropy_excess
#print axioms liftedCrossEntropy_conjugate
#print axioms liftedCrossEntropy_commonPhase

end Audit

end Holonics.Physics.InformationDifference
