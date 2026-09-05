import ElementaryHolonics.Computation.HolonicInformationTheory
import ElementaryHolonics.Millennium.SituatedReturnedDifference
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Causal adjoints, metric gradients, and normalization receivers

This file keeps four objects separate:

* a returned difference in its situated fibre;
* the covector obtained by differentiating a scalar receiver;
* the gradient obtained only after a declared tangent--cotangent chart;
* normalized exponential, RMS, and centered variance faces read from a complete finite section.

Softmax is not installed as native routing.  Its algebraic return is the weighted complete-graph
Laplacian on the admitted finite contact population.  Its constant null direction is therefore a
gauge fibre, not missing native state.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicAdjointNormalization

open scoped BigOperators
open Soma.Holonics.Computation.HolonicInformationTheory
open Soma.Holonics.Millennium.SituatedReturnedDifference

universe uV uI uSource uMiddle uTarget uOccurrence

/-! ## A derivative is a covector; a gradient requires a receiver chart -/

/-- A declared tangent--cotangent identification.  In a conventional finite-dimensional model
this is supplied by a nondegenerate metric/Riesz map.  It is data, not definitional equality. -/
structure MetricGradientChart (V : Type uV) [AddCommGroup V] [Module ℝ V] where
  tangentToCotangent : V ≃ₗ[ℝ] Module.Dual ℝ V

namespace MetricGradientChart

variable {V : Type uV} [AddCommGroup V] [Module ℝ V]

/-- The gradient is the raised scalar differential in one declared chart. -/
def gradient (chart : MetricGradientChart V) (differential : Module.Dual ℝ V) : V :=
  chart.tangentToCotangent.symm differential

@[simp] theorem lower_gradient
    (chart : MetricGradientChart V) (differential : Module.Dual ℝ V) :
    chart.tangentToCotangent (chart.gradient differential) = differential := by
  exact chart.tangentToCotangent.apply_symm_apply differential

/-- Changing the metric chart may change the gradient while leaving the covector fixed. -/
theorem gradient_eq_iff_same_chart_preimage
    (left right : MetricGradientChart V) (differential : Module.Dual ℝ V) :
    left.gradient differential = right.gradient differential ↔
      left.tangentToCotangent.symm differential =
        right.tangentToCotangent.symm differential := Iff.rfl

end MetricGradientChart

/-! The already formalized addressed adjoint theorem is exported here as the neural return law.
It is reverse composition order, not reversal of physical chronology. -/

theorem causalAdjoint_returns_in_reverse_factor_order
    {Source : Type uSource} {Middle : Type uMiddle} {Target : Type uTarget}
    [NormedAddCommGroup Source] [InnerProductSpace ℝ Source] [FiniteDimensional ℝ Source]
    [NormedAddCommGroup Middle] [InnerProductSpace ℝ Middle] [FiniteDimensional ℝ Middle]
    [NormedAddCommGroup Target] [InnerProductSpace ℝ Target] [FiniteDimensional ℝ Target]
    (first : AddressedLinearizedPassage Source Middle)
    (second : AddressedLinearizedPassage Middle Target)
    (word : AddressedTwoStepWord first second) :
    (addressedTwoStepDifferential first second word).adjoint =
      addressedTwoStepReverseAdjoint first second word :=
  addressedTwoStep_adjoint_reverseOrder first second word

/-! ## Normalized exponential receiver and its weighted Laplacian return -/

/-- A declared scalar readout may cross the linear causal adjoint. This is the ideal-law
identity; moving a factor through a finite interval realization still owes its projection bound. -/
theorem causalAdjoint_carries_declared_scale
    {Source : Type*} {Target : Type*}
    [NormedAddCommGroup Source] [InnerProductSpace ℝ Source] [FiniteDimensional ℝ Source]
    [NormedAddCommGroup Target] [InnerProductSpace ℝ Target] [FiniteDimensional ℝ Target]
    (transport : Source →L[ℝ] Target) (scale : ℝ) (returned : Target) :
    transport.adjoint (scale • returned) = scale • transport.adjoint returned :=
  map_smul transport.adjoint scale returned

namespace NormalizedExponential

variable {Index : Type uI} [Fintype Index] [Nonempty Index]

def partition (potential : Index → ℝ) : ℝ :=
  ∑ index, Real.exp (potential index)

theorem partition_pos (potential : Index → ℝ) : 0 < partition potential := by
  classical
  apply Finset.sum_pos'
  · intro index hindex
    exact (Real.exp_pos _).le
  · let index : Index := Classical.choice inferInstance
    exact ⟨index, Finset.mem_univ index, Real.exp_pos _⟩

theorem partition_ne_zero (potential : Index → ℝ) : partition potential ≠ 0 :=
  (partition_pos potential).ne'

/-- Softmax as a positive normalized receiver face over the complete admitted population. -/
def face (potential : Index → ℝ) : PositiveProbabilitySection Index where
  mass index := Real.exp (potential index) / partition potential
  positive index := div_pos (Real.exp_pos _) (partition_pos potential)
  normalized := by
    classical
    simp only [← Finset.sum_div]
    exact div_self (partition_ne_zero potential)

theorem partition_add_common (potential : Index → ℝ) (common : ℝ) :
    partition (fun index => potential index + common) =
      partition potential * Real.exp common := by
  classical
  unfold partition
  simp_rw [Real.exp_add]
  rw [Finset.sum_mul]

/-- A common additive potential is exactly invisible to the normalized receiver. -/
theorem face_add_common (potential : Index → ℝ) (common : ℝ) :
    (face (fun index => potential index + common)).mass = (face potential).mass := by
  funext index
  simp only [face, partition_add_common, Real.exp_add]
  field_simp [partition_ne_zero potential, Real.exp_ne_zero]

/-- The expected receiver reading of one finite section. -/
def expectation (probability : PositiveProbabilitySection Index) (values : Index → ℝ) : ℝ :=
  ∑ index, probability.mass index * values index

/-- The algebraic softmax differential applied to a perturbation.  This is the weighted
complete-graph Laplacian face `beta (diag p - p p^T)`. -/
def laplacianReturn (beta : ℝ) (probability : PositiveProbabilitySection Index)
    (perturbation : Index → ℝ) (index : Index) : ℝ :=
  beta * probability.mass index *
    (perturbation index - expectation probability perturbation)

theorem expectation_const (probability : PositiveProbabilitySection Index) (constant : ℝ) :
    expectation probability (fun _ => constant) = constant := by
  classical
  unfold expectation
  rw [← Finset.sum_mul]
  simp [probability.normalized]

/-- The additive gauge direction lies in the exact kernel. -/
@[simp] theorem laplacianReturn_const
    (beta : ℝ) (probability : PositiveProbabilitySection Index) (constant : ℝ) :
    laplacianReturn beta probability (fun _ => constant) = 0 := by
  funext index
  simp [laplacianReturn, expectation_const]

/-- The complete returned current conserves total probability current. -/
theorem sum_laplacianReturn_zero
    (beta : ℝ) (probability : PositiveProbabilitySection Index)
    (perturbation : Index → ℝ) :
    ∑ index, laplacianReturn beta probability perturbation index = 0 := by
  classical
  let expected := expectation probability perturbation
  calc
    (∑ index, laplacianReturn beta probability perturbation index) =
        ∑ index, beta * (probability.mass index * (perturbation index - expected)) := by
          apply Finset.sum_congr rfl
          intro index hindex
          simp only [laplacianReturn, expected]
          ring
    _ = beta * ∑ index, probability.mass index * (perturbation index - expected) := by
      rw [Finset.mul_sum]
    _ = beta * ((∑ index, probability.mass index * perturbation index) -
        ∑ index, probability.mass index * expected) := by
          congr 1
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
    _ = beta * (expectation probability perturbation -
        (∑ index, probability.mass index) * expected) := by
          unfold expectation
          rw [Finset.sum_mul]
    _ = 0 := by rw [probability.normalized]; simp [expected]

/-- The returned quadratic face is the probability-weighted variance. -/
theorem quadratic_laplacianReturn
    (beta : ℝ) (probability : PositiveProbabilitySection Index)
    (perturbation : Index → ℝ) :
    ∑ index, perturbation index * laplacianReturn beta probability perturbation index =
      beta * ((∑ index, probability.mass index * perturbation index ^ 2) -
        (expectation probability perturbation) ^ 2) := by
  classical
  let expected := expectation probability perturbation
  calc
    (∑ index, perturbation index * laplacianReturn beta probability perturbation index) =
        ∑ index, beta *
          (probability.mass index * (perturbation index ^ 2 - perturbation index * expected)) := by
            apply Finset.sum_congr rfl
            intro index hindex
            simp only [laplacianReturn, expected]
            ring
    _ = beta * ∑ index,
        probability.mass index * (perturbation index ^ 2 - perturbation index * expected) := by
          rw [Finset.mul_sum]
    _ = beta * ((∑ index, probability.mass index * perturbation index ^ 2) -
        ∑ index, (probability.mass index * perturbation index) * expected) := by
          congr 1
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro index hindex
          ring
    _ = beta * ((∑ index, probability.mass index * perturbation index ^ 2) -
        expectation probability perturbation * expected) := by
          unfold expectation
          rw [Finset.sum_mul]
    _ = beta * ((∑ index, probability.mass index * perturbation index ^ 2) -
        (expectation probability perturbation) ^ 2) := by simp [expected, pow_two]

end NormalizedExponential

/-! ## Sigmoid is the binary receiver restriction -/

def sigmoidFace (potential : ℝ) : ℝ :=
  Real.exp potential / (Real.exp potential + 1)

theorem sigmoid_is_binary_normalized_exponential (potential : ℝ) :
    (NormalizedExponential.face (fun index : Bool => if index then potential else 0)).mass true =
      sigmoidFace potential := by
  simp [NormalizedExponential.face, NormalizedExponential.partition, sigmoidFace,
    Fintype.sum_bool]

/-! ## RMS and centered normalization are receiver charts, not native depth -/

namespace FiniteNormalization

variable {Index : Type uI} [Fintype Index] [Nonempty Index]

def population : ℝ := Fintype.card Index

theorem population_pos : 0 < population (Index := Index) := by
  have cardPositive : 0 < Fintype.card Index := Fintype.card_pos
  unfold population
  exact_mod_cast cardPositive

def mean (values : Index → ℝ) : ℝ :=
  (∑ index, values index) / population (Index := Index)

def centered (values : Index → ℝ) (index : Index) : ℝ :=
  values index - mean values

def meanSquare (values : Index → ℝ) : ℝ :=
  (∑ index, values index ^ 2) / population (Index := Index)

/-- “Root mean square” is derived from the exact population total and its receiver cardinality. -/
def rootMeanSquare (values : Index → ℝ) : ℝ :=
  Real.sqrt (meanSquare values)

theorem population_mul_meanSquare (values : Index → ℝ) :
    population (Index := Index) * meanSquare values = ∑ index, values index ^ 2 := by
  simp only [population, meanSquare]
  field_simp [ne_of_gt (population_pos (Index := Index))]

theorem sum_centered_zero (values : Index → ℝ) :
    ∑ index, centered values index = 0 := by
  classical
  simp only [centered, mean, population]
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  simp only [nsmul_eq_mul, Finset.card_univ]
  have card_cast : (Fintype.card Index : ℝ) ≠ 0 :=
    ne_of_gt (population_pos (Index := Index))
  field_simp [card_cast]
  ring

/-- Centering deletes exactly a common additive chart displacement. -/
theorem centered_add_common (values : Index → ℝ) (common : ℝ) :
    centered (fun index => values index + common) = centered values := by
  funext index
  classical
  simp only [centered, mean, population]
  rw [Finset.sum_add_distrib, Finset.sum_const]
  simp only [nsmul_eq_mul, Finset.card_univ]
  have card_cast : (Fintype.card Index : ℝ) ≠ 0 :=
    ne_of_gt (population_pos (Index := Index))
  field_simp [card_cast]
  ring

/-- Layer variance is the RMS energy of the centered section. -/
def centeredMeanSquare (values : Index → ℝ) : ℝ :=
  meanSquare (centered values)

theorem centeredMeanSquare_add_common (values : Index → ℝ) (common : ℝ) :
    centeredMeanSquare (fun index => values index + common) = centeredMeanSquare values := by
  simp only [centeredMeanSquare, centered_add_common]

end FiniteNormalization

/-! ## A scalar loss cannot govern complete returned morphology -/

theorem entropy_doesNot_govern_complete_morphology :
    ¬ ∃ descend : ℝ → (Bool → ℝ),
      ∀ probabilitySection : PositiveProbabilitySection Bool,
        probabilitySection.mass = descend probabilitySection.entropy := by
  rintro ⟨descend, factors⟩
  have equalMass : entropyControlLeft.mass = entropyControlRight.mass := by
    calc
      entropyControlLeft.mass = descend entropyControlLeft.entropy := factors entropyControlLeft
      _ = descend entropyControlRight.entropy := congrArg descend entropyControl_equal_entropy
      _ = entropyControlRight.mass := (factors entropyControlRight).symm
  exact entropyControl_sections_ne equalMass

section Audit

#print axioms MetricGradientChart.lower_gradient
#print axioms causalAdjoint_returns_in_reverse_factor_order
#print axioms NormalizedExponential.face_add_common
#print axioms NormalizedExponential.sum_laplacianReturn_zero
#print axioms NormalizedExponential.quadratic_laplacianReturn
#print axioms sigmoid_is_binary_normalized_exponential
#print axioms FiniteNormalization.population_mul_meanSquare
#print axioms FiniteNormalization.centered_add_common
#print axioms entropy_doesNot_govern_complete_morphology

end Audit

end Soma.Holonics.Computation.HolonicAdjointNormalization
