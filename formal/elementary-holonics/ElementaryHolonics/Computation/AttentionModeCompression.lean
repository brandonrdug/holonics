import Mathlib
import ElementaryHolonics.Foundation.GeneratorInference

/-!
  Exact finite-class aggregation for normalized kernel-weighted currents.

  The pair `(mass,current)` is the compositional carrier.  Normalization is a
  receiver projection; it is not used as an associative carrier by itself.
-/

namespace Soma.Holonics.Computation.AttentionModeCompression

open scoped BigOperators
open Soma.Holonics.Computation.HolonicAdjointNormalization
open Soma.Holonics.Computation.HolonicInformationTheory
open Soma.Holonics.Foundation

variable {Q I C V : Type*}
variable [Fintype I] [Fintype C] [DecidableEq C]
variable [AddCommMonoid V] [Module ℝ V]

def classMass (π : I → C) (w : I → ℝ) (c : C) : ℝ :=
  ∑ i ∈ (Finset.univ.filter (fun i => π i = c)), w i

def classCurrent (π : I → C) (w : I → ℝ) (v : I → V) (c : C) : V :=
  ∑ i ∈ (Finset.univ.filter (fun i => π i = c)), w i • v i

def attentionDenominator (b : Q → C → ℝ) (π : I → C) (w : I → ℝ) (q : Q) : ℝ :=
  ∑ c : C, b q c * classMass π w c

def attentionNumerator (b : Q → C → ℝ) (π : I → C) (w : I → ℝ) (v : I → V) (q : Q) : V :=
  ∑ c : C, b q c • classCurrent π w v c

theorem classMass_sum (π : I → C) (w : I → ℝ) :
    ∑ c : C, classMass π w c = ∑ i : I, w i := by
  simp only [classMass]
  exact Finset.sum_fiberwise (Finset.univ : Finset I) π (fun i => w i)

theorem classCurrent_sum (π : I → C) (w : I → ℝ) (v : I → V) :
    ∑ c : C, classCurrent π w v c = ∑ i : I, w i • v i := by
  simp only [classCurrent]
  exact Finset.sum_fiberwise (Finset.univ : Finset I) π (fun i => w i • v i)

theorem attentionDenominator_eq (b : Q → C → ℝ) (π : I → C) (w : I → ℝ) (q : Q) :
    attentionDenominator b π w q = ∑ i : I, b q (π i) * w i := by
  simp only [attentionDenominator, classMass]
  rw [← Finset.sum_fiberwise (Finset.univ : Finset I) π (fun i => b q (π i) * w i)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [hi]

theorem attentionNumerator_eq (b : Q → C → ℝ) (π : I → C) (w : I → ℝ)
    (v : I → V) (q : Q) :
    attentionNumerator b π w v q = ∑ i : I, (b q (π i) * w i) • v i := by
  simp only [attentionNumerator, classCurrent]
  rw [← Finset.sum_fiberwise (Finset.univ : Finset I) π
    (fun i => (b q (π i) * w i) • v i)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [hi, smul_smul]

theorem normalized_attention_exact (b : Q → C → ℝ) (π : I → C) (w : I → ℝ)
    (v : I → V) (q : Q) (hden : attentionDenominator b π w q ≠ 0) :
    (attentionDenominator b π w q)⁻¹ • attentionNumerator b π w v q =
      (∑ i : I, b q (π i) * w i)⁻¹ • ∑ i : I, (b q (π i) * w i) • v i := by
  rw [attentionDenominator_eq, attentionNumerator_eq]

theorem summary_smul_transport (a : ℝ) (π : I → C) (w : I → ℝ) (v : I → V) :
    a • (∑ c : C, classCurrent π w v c) =
      ∑ c : C, a • classCurrent π w v c := by
  rw [Finset.smul_sum]

theorem weighted_summary_associative (a b c : ℝ × V) :
    (a.1 + b.1 + c.1, (a.2 + b.2) + c.2) =
      (a.1 + (b.1 + c.1), a.2 + (b.2 + c.2)) := by
  simp [add_assoc]

/-! ## Gibbs/KL receiver bridge -/

theorem score_face_eq_posterior (scores : I → ℝ) [Nonempty I] :
    NormalizedExponential.face scores =
      Soma.Holonics.Foundation.GeneratorInference.posterior
        (fun i : I => -scores i / Real.log 2) := by
  unfold Soma.Holonics.Foundation.GeneratorInference.posterior
  congr 1
  funext i
  field_simp [Soma.Holonics.Foundation.GeneratorInference.bitScale_pos.ne']

theorem attention_free_energy_minimum (scores : I → ℝ) [Nonempty I]
    (q : PositiveProbabilitySection I) :
    GeneratorInference.variational (fun i : I => -scores i / Real.log 2)
        (GeneratorInference.posterior (fun i : I => -scores i / Real.log 2)) ≤
      GeneratorInference.variational (fun i : I => -scores i / Real.log 2) q := by
  exact GeneratorInference.variational_minimum _ _

theorem unweighted_mean_not_associative :
    (((0 : ℝ) + 0) / 2 + 4) / 2 ≠ (0 + ((0 + 4) / 2)) / 2 := by norm_num

theorem linear_summary_transport {W : Type*} [AddCommMonoid W] [Module ℝ W]
    (transport : V →ₗ[ℝ] W) (π : I → C) (w : I → ℝ) (v : I → V) (c : C) :
    transport (classCurrent π w v c) = classCurrent π w (fun i => transport (v i)) c := by
  simp only [classCurrent, map_sum, map_smul]

end Soma.Holonics.Computation.AttentionModeCompression
