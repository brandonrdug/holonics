import ElementaryHolonics.Computation.HolonicInformationTheory
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Causal adjoints, metric gradients, and normalization receivers

This file keeps four objects separate:

* a returned difference in its situated fibre;
* the covector obtained by differentiating a scalar receiver;
* the gradient obtained only after a declared tangent--cotangent chart;
* normalized exponential, RMS, and centered variance faces read from a complete finite section.

This file formalizes normalization and its differential on an admitted finite contact population.
Incidence is supplied by the contact law; native normalized/contact owners realize particular
charts.  Its algebraic return is the weighted complete-graph Laplacian, whose constant null
direction is a gauge fibre rather than missing native state.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicAdjointNormalization

open scoped BigOperators
open Soma.Holonics.Computation.HolonicInformationTheory

universe uV uI

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

/-! ## Full joint held relaxation and its algebraic return

The boundary and internal carriers are one product space.  `jointHeldRelaxation` therefore keeps
the held mask and the source-derived scatter on the complete `(q,b)` operand.  Its linear part is
the map whose dual pullback returns a receiver covector; the affine anchor has no differential.
-/

section JointHeldRelaxation

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

def sourceDerivedProjection (D : W →ₗ[ℝ] V) (Dt : V →ₗ[ℝ] W)
    (Kinv : V →ₗ[ℝ] V) : (V × W) →ₗ[ℝ] (V × W) where
  toFun x := (Kinv (x.1 + D x.2), Dt (Kinv (x.1 + D x.2)))
  map_add' x y := by simp [map_add, add_assoc, add_left_comm, add_comm]
  map_smul' c x := by simp

def sourceDerivedScatter (D : W →ₗ[ℝ] V) (Dt : V →ₗ[ℝ] W)
    (Kinv : V →ₗ[ℝ] V) : (V × W) →ₗ[ℝ] (V × W) :=
  (2 : ℝ) • sourceDerivedProjection D Dt Kinv - LinearMap.id

def normalSolveHypothesis (D : W →ₗ[ℝ] V) (Dt : V →ₗ[ℝ] W)
    (Kinv : V →ₗ[ℝ] V) : Prop :=
  Kinv.comp (LinearMap.id + D.comp Dt) = LinearMap.id

theorem sourceDerivedProjection_idempotent
    (D : W →ₗ[ℝ] V) (Dt : V →ₗ[ℝ] W) (Kinv : V →ₗ[ℝ] V)
    (hsolve : normalSolveHypothesis D Dt Kinv) (x : V × W) :
    sourceDerivedProjection D Dt Kinv (sourceDerivedProjection D Dt Kinv x) =
      sourceDerivedProjection D Dt Kinv x := by
  have h := LinearMap.congr_fun hsolve (Kinv (x.1 + D x.2))
  change Kinv (Kinv (x.1 + D x.2) + D (Dt (Kinv (x.1 + D x.2)))) =
    Kinv (x.1 + D x.2) at h
  dsimp [sourceDerivedProjection]
  rw [h]

theorem sourceDerivedScatter_involutive
    (D : W →ₗ[ℝ] V) (Dt : V →ₗ[ℝ] W) (Kinv : V →ₗ[ℝ] V)
    (hsolve : normalSolveHypothesis D Dt Kinv) (x : V × W) :
    sourceDerivedScatter D Dt Kinv (sourceDerivedScatter D Dt Kinv x) = x := by
  let P := sourceDerivedProjection D Dt Kinv
  have hP : P (P x) = P x := sourceDerivedProjection_idempotent D Dt Kinv hsolve x
  change (2 : ℝ) • P ((2 : ℝ) • P x - x) - ((2 : ℝ) • P x - x) = x
  rw [map_sub, map_smul, hP]
  module

def jointHeldLinearPart {X : Type*} [AddCommGroup X] [Module ℝ X]
    (hold scatter : X →ₗ[ℝ] X) (mu : ℝ) : X →ₗ[ℝ] X :=
  ((LinearMap.id : X →ₗ[ℝ] X) - hold).comp (mu • scatter)

def jointHeldRelaxation {X : Type*} [AddCommGroup X] [Module ℝ X]
    (hold scatter : X →ₗ[ℝ] X) (mu : ℝ) (anchor z : X) : X :=
  hold anchor + ((LinearMap.id : X →ₗ[ℝ] X) - hold)
    ((1 - mu) • anchor + mu • scatter z)

def jointHeldPullback {X : Type*} [AddCommGroup X] [Module ℝ X]
    (hold scatter : X →ₗ[ℝ] X) (mu : ℝ) (covector : Module.Dual ℝ X) :
    Module.Dual ℝ X :=
  (jointHeldLinearPart hold scatter mu).dualMap covector

theorem jointHeldRelaxation_linear_part
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (hold scatter : X →ₗ[ℝ] X) (mu : ℝ) (anchor z : X) :
    jointHeldRelaxation hold scatter mu anchor z =
      hold anchor + (jointHeldLinearPart hold scatter mu) z +
        ((LinearMap.id : X →ₗ[ℝ] X) - hold) ((1 - mu) • anchor) := by
  change hold anchor + ((LinearMap.id : X →ₗ[ℝ] X) - hold)
      ((1 - mu) • anchor + mu • scatter z) =
    hold anchor + ((LinearMap.id : X →ₗ[ℝ] X) - hold) (mu • scatter z) +
      ((LinearMap.id : X →ₗ[ℝ] X) - hold) ((1 - mu) • anchor)
  rw [map_add]
  ac_rfl

theorem jointHeldPullback_eq_dual_linear_part
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (hold scatter : X →ₗ[ℝ] X) (mu : ℝ) (covector : Module.Dual ℝ X) :
    jointHeldPullback hold scatter mu covector =
      (jointHeldLinearPart hold scatter mu).dualMap covector := rfl

theorem sourceDerived_jointHeldPullback
    (D : W →ₗ[ℝ] V) (Dt : V →ₗ[ℝ] W) (Kinv : V →ₗ[ℝ] V)
    (hold : (V × W) →ₗ[ℝ] (V × W)) (mu : ℝ)
    (covector : Module.Dual ℝ (V × W)) :
    jointHeldPullback hold (sourceDerivedScatter D Dt Kinv) mu covector =
      (jointHeldLinearPart hold (sourceDerivedScatter D Dt Kinv) mu).dualMap
        covector := rfl

theorem sourceDerived_jointHeldRelaxation_scatter_invariant
    (D : W →ₗ[ℝ] V) (Dt : V →ₗ[ℝ] W) (Kinv : V →ₗ[ℝ] V)
    (hsolve : normalSolveHypothesis D Dt Kinv)
    (hold : (V × W) →ₗ[ℝ] (V × W)) (mu : ℝ)
    (anchor z : V × W) :
    jointHeldRelaxation hold (sourceDerivedScatter D Dt Kinv) mu anchor
        (sourceDerivedScatter D Dt Kinv
          (sourceDerivedScatter D Dt Kinv z)) =
      jointHeldRelaxation hold (sourceDerivedScatter D Dt Kinv) mu anchor z := by
  rw [sourceDerivedScatter_involutive D Dt Kinv hsolve z]

theorem dualMap_comp_reverse_order
    {X Y Z : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
    (first : X →ₗ[ℝ] Y) (second : Y →ₗ[ℝ] Z)
    (covector : Module.Dual ℝ Z) :
    (second.comp first).dualMap covector = first.dualMap (second.dualMap covector) := by
  rfl

end JointHeldRelaxation

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

/-- Log mass retains its potential and the common normalization boundary. -/
theorem log_face_mass (potential : Index → ℝ) (index : Index) :
    Real.log ((face potential).mass index) = potential index - Real.log (partition potential) := by
  simp only [face, Real.log_div (Real.exp_ne_zero _) (partition_ne_zero _), Real.log_exp]

/-- Normalization preserves the ordering of the complete potential population. -/
theorem face_mass_le_iff (potential : Index → ℝ) (left right : Index) :
    (face potential).mass left ≤ (face potential).mass right ↔
      potential left ≤ potential right := by
  change Real.exp (potential left) / partition potential ≤
    Real.exp (potential right) / partition potential ↔ _
  rw [div_le_div_iff_of_pos_right (partition_pos potential), Real.exp_le_exp]

/-- Pairwise potential differences are a complete invariant of this normalized receiver. -/
theorem face_eq_iff_pairwise_differences (left right : Index → ℝ) :
    (face left).mass = (face right).mass ↔
      ∀ i j, left i - left j = right i - right j := by
  constructor
  · intro equal i j
    have hi := congrArg Real.log (congrFun equal i)
    have hj := congrArg Real.log (congrFun equal j)
    rw [log_face_mass, log_face_mass] at hi hj
    linarith
  · intro differences
    classical
    let anchor : Index := Classical.choice inferInstance
    have shifted : left = fun i => right i + (left anchor - right anchor) := by
      funext i
      have h := differences i anchor
      linarith
    rw [shifted]
    exact face_add_common right _

/-- A predicted increment has the full next-current probability face only when the omitted
anchor is a common potential. This is the exact source-map condition used by the shared
normalized sum receiver; a nonconstant current cannot be discarded as a gauge. -/
theorem face_add_eq_iff_anchor_constant (anchor increment : Index → ℝ) :
    (face (fun i => anchor i + increment i)).mass = (face increment).mass ↔
      ∀ i j, anchor i = anchor j := by
  rw [face_eq_iff_pairwise_differences]
  constructor
  · intro equal i j
    have h := equal i j
    linarith
  · intro constant i j
    rw [constant i j]
    ring

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

/-- The sigmoid receiver's directional derivative is its returned binary covariance face. -/
theorem hasDerivAt_sigmoidFace (potential : ℝ) :
    HasDerivAt sigmoidFace (sigmoidFace potential * (1 - sigmoidFace potential)) potential := by
  let e : ℝ := Real.exp potential
  have he : HasDerivAt (fun x : ℝ => Real.exp x) e potential := by
    simpa [e] using (Real.hasDerivAt_exp potential)
  have hden : e + 1 ≠ 0 := by
    dsimp [e]
    positivity
  have hquot := he.div (he.add_const 1) hden
  have hfun : sigmoidFace = (fun x : ℝ => Real.exp x / (Real.exp x + 1)) := by
    funext x
    rfl
  rw [hfun]
  apply hquot.congr_deriv
  dsimp [e, sigmoidFace]
  field_simp [hden]

namespace NormalizedExponential

variable {Index : Type uI} [Fintype Index] [Nonempty Index]

/-- The normalized exponential's directional derivative is its weighted Laplacian return. -/
theorem hasDerivAt_face_mass_sectionLine
    (potential direction : Index → ℝ) (index : Index) :
    HasDerivAt
      (fun t => (face (fun j => potential j + t * direction j)).mass index)
      (laplacianReturn 1 (face potential) direction index) 0 := by
  have harg : ∀ j : Index,
      HasDerivAt (fun t : ℝ => potential j + t * direction j) (direction j) 0 := by
    intro j
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (direction j)).const_add (potential j)
  have hexp : ∀ j : Index,
      HasDerivAt (fun t : ℝ => Real.exp (potential j + t * direction j))
        (Real.exp (potential j) * direction j) 0 := by
    intro j
    simpa using (harg j).exp
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset Index))
    (fun j _hj => hexp j)
  have hden : (∑ j, Real.exp (potential j + 0 * direction j)) ≠ 0 := by
    simpa [partition] using (partition_ne_zero potential)
  have hquot := (hexp index).div hsum hden
  have hfun :
      (fun t => (face (fun j => potential j + t * direction j)).mass index) =
        (fun t => Real.exp (potential index + t * direction index) /
          (∑ j, Real.exp (potential j + t * direction j))) := by
    funext t
    rfl
  rw [hfun]
  apply hquot.congr_deriv
  simp only [laplacianReturn, face, expectation, partition]
  simp only [mul_zero, add_zero, zero_mul]
  have hP : (∑ x, Real.exp (potential x)) ≠ 0 := by
    simpa [partition] using (partition_ne_zero potential)
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  field_simp [hP]
  <;> ring

end NormalizedExponential

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
#print axioms sourceDerivedProjection_idempotent
#print axioms sourceDerivedScatter_involutive
#print axioms jointHeldRelaxation_linear_part
#print axioms sourceDerived_jointHeldPullback
#print axioms sourceDerived_jointHeldRelaxation_scatter_invariant
#print axioms dualMap_comp_reverse_order
#print axioms NormalizedExponential.face_add_common
#print axioms NormalizedExponential.sum_laplacianReturn_zero
#print axioms NormalizedExponential.quadratic_laplacianReturn
#print axioms sigmoid_is_binary_normalized_exponential
#print axioms hasDerivAt_sigmoidFace
#print axioms NormalizedExponential.hasDerivAt_face_mass_sectionLine
#print axioms FiniteNormalization.population_mul_meanSquare
#print axioms FiniteNormalization.centered_add_common
#print axioms entropy_doesNot_govern_complete_morphology

end Audit

end Soma.Holonics.Computation.HolonicAdjointNormalization
