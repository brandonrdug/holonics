import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Exact accumulated normal-response algebra

This owner records the finite complex matrix identity behind one rank-one accumulated update.  The
matrices are ordinary algebraic carriers. The unit-prior objective also bounds a reference
minimizer by its target energy; no optimization algorithm, native runtime or physical energy
interpretation is introduced here.
-/

noncomputable section

namespace Holonics.Physics.AccumulatedNormalResponse

open Matrix

abbrev Column (Index : Type*) := Matrix Index Unit ℂ

variable {Source Target : Type*} [Fintype Source] [Fintype Target]

local instance (priority := 100) : DecidableEq Source := Classical.decEq Source

def updatedGram (H : Matrix Source Source ℂ) (x : Column Source) : Matrix Source Source ℂ :=
  H + x * x.conjTranspose

def updatedCross (B : Matrix Target Source ℂ) (y : Column Target)
    (x : Column Source) : Matrix Target Source ℂ :=
  B + y * x.conjTranspose

def updatedResponse (M : Matrix Target Source ℂ) (x : Column Source) (y : Column Target)
    (g : Column Source) (E : Matrix Target Source ℂ) : Matrix Target Source ℂ :=
  M + (y - M * x) * g.conjTranspose + E

def normalResidual (M : Matrix Target Source ℂ) (H : Matrix Source Source ℂ)
    (B : Matrix Target Source ℂ) : Matrix Target Source ℂ :=
    M * H - B

/-! ## Finite quadratic objective bounds -/

/-- The matrix entries represented in the finite Euclidean space of complex coordinates. -/
def matrixVector {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J ℂ) : EuclideanSpace ℂ (I × J) :=
  (EuclideanSpace.equiv (I × J) ℂ).symm
    (fun index ↦ M index.1 index.2)

/-- The squared Frobenius norm in the declared finite complex matrix chart. -/
def frobeniusSq {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J ℂ) : ℝ :=
  ‖matrixVector M‖ ^ 2

/-- The Frobenius norm in the declared finite complex matrix chart. -/
def frobeniusNorm {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J ℂ) : ℝ :=
  ‖matrixVector M‖

theorem frobeniusNorm_sub_le (M P : Matrix Target Source ℂ) :
    frobeniusNorm (M - P) ≤ frobeniusNorm M + frobeniusNorm P := by
  have hv : matrixVector (M - P) = matrixVector M - matrixVector P := by
    apply (EuclideanSpace.equiv (Target × Source) ℂ).injective
    funext index
    simp [matrixVector]
  rw [frobeniusNorm, hv, frobeniusNorm, frobeniusNorm]
  exact norm_sub_le _ _

theorem frobeniusNorm_sq (M : Matrix Target Source ℂ) :
    frobeniusNorm M ^ 2 = frobeniusSq M := by
  rfl

/-- A finite sample is an input column paired with its target column. -/
abbrev Sample (Source Target : Type*) := Column Source × Column Target

/-- The regularized finite normal objective: reference norm plus all sample residuals. -/
def normalObjective (samples : List (Sample Source Target)) (M : Matrix Target Source ℂ) : ℝ :=
  frobeniusSq M +
    (samples.map (fun sample ↦
      frobeniusSq (M * sample.1 - sample.2))).sum

/-- The nonzero-prior objective used by the resident normal solve. -/
def normalObjectiveWithPrior (W₀ : Matrix Target Source ℂ)
    (samples : List (Sample Source Target)) (M : Matrix Target Source ℂ) : ℝ :=
  frobeniusSq (M - W₀) +
    (samples.map (fun sample ↦
      frobeniusSq (M * sample.1 - sample.2))).sum

theorem frobeniusSq_nonneg (M : Matrix Target Source ℂ) :
    0 ≤ frobeniusSq M := by
  exact sq_nonneg _

/-! ## Explicit unit prior and the derived normal target

The prior block is retained in the normal source independently of observed target energy.  The
two quantities are named separately here so a zero-data packet does not silently erase a nonzero
material prior.
-/

def unitPriorGram : Matrix Source Source ℂ := 1

def unitPriorCross (W₀ : Matrix Target Source ℂ) : Matrix Target Source ℂ := W₀

def unitPriorEnergy (W₀ : Matrix Target Source ℂ) : ℝ := frobeniusSq W₀

def observedTargetEnergy (samples : List (Sample Source Target)) : ℝ :=
  (samples.map (fun sample ↦ frobeniusSq sample.2)).sum

def augmentedTargetEnergy (W₀ : Matrix Target Source ℂ)
    (samples : List (Sample Source Target)) : ℝ :=
  unitPriorEnergy W₀ + observedTargetEnergy samples

theorem unitPrior_data_separation (W₀ : Matrix Target Source ℂ) :
    unitPriorGram = (1 : Matrix Source Source ℂ) ∧
      unitPriorCross W₀ = W₀ ∧
      unitPriorEnergy W₀ = frobeniusSq W₀ := by
  exact ⟨rfl, rfl, rfl⟩

theorem observedTargetEnergy_eq_data (samples : List (Sample Source Target)) :
    observedTargetEnergy samples =
      (samples.map (fun sample ↦ frobeniusSq sample.2)).sum := rfl

theorem augmentedTargetEnergy_nonneg (W₀ : Matrix Target Source ℂ)
    (samples : List (Sample Source Target))
    (hdata : 0 ≤ observedTargetEnergy samples) :
    0 ≤ augmentedTargetEnergy W₀ samples := by
  exact add_nonneg (frobeniusSq_nonneg W₀) hdata

theorem unitPriorEnergy_pos [Nonempty (Target × Source)]
    (W₀ : Matrix Target Source ℂ) (hW₀ : W₀ ≠ 0) :
    0 < unitPriorEnergy W₀ := by
  have hvec : matrixVector W₀ ≠ 0 := by
    intro hz
    apply hW₀
    funext i j
    have hi := congrArg (fun v => v (i, j)) hz
    simpa [matrixVector] using hi
  exact sq_pos_of_pos (norm_pos_iff.mpr hvec)

/-! A derived covector is staged as a normal target at the current material. -/

def normalProxyTarget (W : Matrix Target Source ℂ) (f : Column Source)
    (sigma : ℝ) (g : Column Target) : Column Target :=
  W * f + sigma • g

def normalProxyCross (B W : Matrix Target Source ℂ) (f : Column Source)
    (sigma : ℝ) (g : Column Target) : Matrix Target Source ℂ :=
  B + normalProxyTarget W f sigma g * f.conjTranspose

theorem normalProxyTarget_eq_current_mul_feature_add_covector
    (W : Matrix Target Source ℂ) (f : Column Source) (sigma : ℝ) (g : Column Target) :
    normalProxyTarget W f sigma g = W * f + sigma • g := rfl

theorem normalProxyTarget_residual_eq_scaled_covector
    (W : Matrix Target Source ℂ) (f : Column Source) (sigma : ℝ) (g : Column Target) :
    normalProxyTarget W f sigma g - W * f = sigma • g := by
  simp [normalProxyTarget]

theorem normalProxyCross_eq_updatedCross
    (B W : Matrix Target Source ℂ) (f : Column Source)
    (sigma : ℝ) (g : Column Target) :
    normalProxyCross B W f sigma g =
      updatedCross B (normalProxyTarget W f sigma g) f := rfl

theorem weighted_cauchy_schwarz {I : Type*} [Fintype I]
    (a x : I → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i * x i) ^ 2 ≤ (∑ i, a i) * ∑ i, a i * (x i) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I)
    (fun i => Real.sqrt (a i)) (fun i => Real.sqrt (a i) * x i)
  have hs (i : I) : (Real.sqrt (a i)) ^ 2 = a i := Real.sq_sqrt (ha i)
  have hleft : (∑ i, Real.sqrt (a i) * (Real.sqrt (a i) * x i)) =
      ∑ i, a i * x i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [show Real.sqrt (a i) * (Real.sqrt (a i) * x i) =
      (Real.sqrt (a i)) ^ 2 * x i by ring, hs]
  have hweight : (∑ i, (Real.sqrt (a i)) ^ 2) = ∑ i, a i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hs i
  have hright : (∑ i, (Real.sqrt (a i) * x i) ^ 2) =
      ∑ i, a i * (x i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (Real.sqrt (a i) * x i) ^ 2 =
      (Real.sqrt (a i)) ^ 2 * (x i) ^ 2 by ring, hs]
  rw [hleft, hweight, hright] at h
  exact h

theorem complex_schur_action_sq
    (A : Matrix Target Source ℂ) (a : Target → Source → ℝ)
    (x : Source → ℂ) (R C : ℝ)
    (ha : ∀ i j, 0 ≤ a i j)
    (hnorm : ∀ i j, ‖A i j‖ ≤ a i j)
    (hrows : ∀ i, (∑ j, a i j) ≤ R)
    (hcols : ∀ j, (∑ i, a i j) ≤ C)
    (hR : 0 ≤ R) (_hC : 0 ≤ C) :
    (∑ i, ‖∑ j, A i j * x j‖ ^ 2) ≤
      R * C * ∑ j, ‖x j‖ ^ 2 := by
  have hrow (i : Target) :
      ‖∑ j, A i j * x j‖ ^ 2 ≤
        R * ∑ j, a i j * ‖x j‖ ^ 2 := by
    have htriangle : ‖∑ j, A i j * x j‖ ≤ ∑ j, a i j * ‖x j‖ := by
      calc
        ‖∑ j, A i j * x j‖ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
        _ ≤ ∑ j, a i j * ‖x j‖ := by
          apply Finset.sum_le_sum
          intro j hj
          exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (hnorm i j) (norm_nonneg _))
    have hcs := weighted_cauchy_schwarz (fun j => a i j) (fun j => ‖x j‖) (ha i)
    have hsum_nonneg : 0 ≤ ∑ j, a i j * ‖x j‖ ^ 2 := by
      exact Finset.sum_nonneg fun j hj => mul_nonneg (ha i j) (sq_nonneg _)
    have hsum_norm_nonneg : 0 ≤ ∑ j, a i j * ‖x j‖ := by
      exact Finset.sum_nonneg fun j hj => mul_nonneg (ha i j) (norm_nonneg _)
    have hweighted :
        (∑ j, a i j * ‖x j‖) ^ 2 ≤
          R * ∑ j, a i j * ‖x j‖ ^ 2 :=
      (hcs.trans (mul_le_mul_of_nonneg_right (hrows i) hsum_nonneg))
    exact ((sq_le_sq₀ (norm_nonneg _) hsum_norm_nonneg).2 htriangle).trans hweighted
  calc
    (∑ i, ‖∑ j, A i j * x j‖ ^ 2) ≤
        ∑ i, R * ∑ j, a i j * ‖x j‖ ^ 2 :=
      Finset.sum_le_sum fun i hi => hrow i
    _ = R * ∑ i, ∑ j, a i j * ‖x j‖ ^ 2 := by rw [Finset.mul_sum]
    _ = R * ∑ j, (∑ i, a i j) * ‖x j‖ ^ 2 := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
    _ ≤ R * (C * ∑ j, ‖x j‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · calc
          (∑ j, (∑ i, a i j) * ‖x j‖ ^ 2) ≤
              ∑ j, C * ‖x j‖ ^ 2 := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_right (hcols j) (sq_nonneg _)
          _ = C * ∑ j, ‖x j‖ ^ 2 := by rw [Finset.mul_sum]
      · exact hR
    _ = R * C * ∑ j, ‖x j‖ ^ 2 := by ring

open scoped Matrix.Norms.L2Operator in
theorem square_schur_operator_bound [DecidableEq Source]
    (A : Matrix Source Source ℂ) (a : Source → Source → ℝ) (R C : ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (hnorm : ∀ i j, ‖A i j‖ ≤ a i j)
    (hrows : ∀ i, (∑ j, a i j) ≤ R) (hcols : ∀ j, (∑ i, a i j) ≤ C)
    (hR : 0 ≤ R) (hC : 0 ≤ C) : ‖A‖ ≤ Real.sqrt (R * C) := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hR hC)]
  simp only [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM]
  simpa only [Matrix.mulVec, dotProduct] using
    complex_schur_action_sq A a (WithLp.ofLp x) R C ha hnorm hrows hcols hR hC

open scoped Matrix.Norms.L2Operator in
/-- Taking the complex Gram product before its entrywise bound keeps cancellation
between modes. This is a bound on the current operator, not its previous power envelope. -/
theorem gram_operator_bound [DecidableEq Source]
    (A : Matrix Source Source ℂ) (G : ℝ) (hG : 0 ≤ G)
    (hrows : ∀ i, (∑ j, (|((A.conjTranspose * A) i j).re| +
      |((A.conjTranspose * A) i j).im|)) ≤ G) :
    ‖A‖ ≤ Real.sqrt G := by
  let K := A.conjTranspose * A
  let a := fun i j => |(K i j).re| + |(K i j).im|
  have hhermitian : K.conjTranspose = K := by simp [K]
  have hsymm (i j : Source) : a i j = a j i := by
    have h := congrArg (fun M : Matrix Source Source ℂ => M i j) hhermitian
    change star (K j i) = K i j at h
    dsimp [a]
    rw [← h]
    simp
  have hcols (j : Source) : (∑ i, a i j) ≤ G := by
    calc
      (∑ i, a i j) = ∑ i, a j i := Finset.sum_congr rfl (fun i _ => hsymm i j)
      _ ≤ G := hrows j
  have hbound := square_schur_operator_bound K a G G
    (fun i j => add_nonneg (abs_nonneg _) (abs_nonneg _))
    (fun i j => Complex.norm_le_abs_re_add_abs_im (K i j)) hrows hcols hG hG
  rw [Real.sqrt_mul_self hG] at hbound
  change ‖A.conjTranspose * A‖ ≤ G at hbound
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hbound
  have hsqrt := Real.sq_sqrt hG
  have hn := norm_nonneg A
  have hr := Real.sqrt_nonneg G
  nlinarith

theorem normalObjective_zero (samples : List (Sample Source Target)) :
    normalObjective samples 0 =
      (samples.map (fun sample ↦ frobeniusSq sample.2)).sum := by
  unfold normalObjective
  simp only [frobeniusSq]
  have hzero : ‖matrixVector (0 : Matrix Target Source ℂ)‖ ^ 2 = 0 := by
    change ‖(0 : EuclideanSpace ℂ (Target × Source))‖ ^ 2 = 0
    simp
  rw [hzero, zero_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro sample hsample
  have hneg : matrixVector (-sample.2) = -matrixVector sample.2 := by
    apply PiLp.ext
    intro index
    simp [matrixVector]
  rw [show (0 : Matrix Target Source ℂ) * sample.1 - sample.2 = -sample.2 by
    simp, hneg, norm_neg]

theorem frobeniusSq_le_of_normal_minimizer
    (samples : List (Sample Source Target)) (P : Matrix Target Source ℂ)
    (minimizer : ∀ Q, normalObjective samples P ≤ normalObjective samples Q) :
    frobeniusSq P ≤ (samples.map (fun sample ↦ frobeniusSq sample.2)).sum := by
  have hmin := minimizer 0
  rw [normalObjective_zero] at hmin
  have hnonneg : 0 ≤ (samples.map (fun sample ↦
      frobeniusSq (P * sample.1 - sample.2))).sum := by
    apply List.sum_nonneg
    intro residual hresidual
    obtain ⟨sample, hsample, rfl⟩ := List.mem_map.mp hresidual
    exact frobeniusSq_nonneg _
  exact le_trans (le_add_of_nonneg_right
    hnonneg) hmin

theorem normalObjective_zero_le_of_target_energy
    (samples : List (Sample Source Target)) (targetEnergy : ℝ)
    (target_bound : (samples.map (fun sample ↦ frobeniusSq sample.2)).sum ≤ targetEnergy) :
    normalObjective samples 0 ≤ targetEnergy := by
  rw [normalObjective_zero]
  exact target_bound

theorem normalObjective_le_of_normal_minimizer_target_bound
    (samples : List (Sample Source Target)) (P : Matrix Target Source ℂ)
    (targetEnergy : ℝ)
    (minimizer : ∀ Q, normalObjective samples P ≤ normalObjective samples Q)
    (target_bound : (samples.map (fun sample ↦ frobeniusSq sample.2)).sum ≤ targetEnergy) :
    normalObjective samples P ≤ targetEnergy := by
  exact (minimizer 0).trans
    (normalObjective_zero_le_of_target_energy samples targetEnergy target_bound)

theorem frobeniusSq_le_of_normal_minimizer_target_bound
    (samples : List (Sample Source Target)) (P : Matrix Target Source ℂ)
    (targetEnergy : ℝ)
    (minimizer : ∀ Q, normalObjective samples P ≤ normalObjective samples Q)
    (target_bound : (samples.map (fun sample ↦ frobeniusSq sample.2)).sum ≤ targetEnergy) :
    frobeniusSq P ≤ targetEnergy := by
  exact (frobeniusSq_le_of_normal_minimizer samples P minimizer).trans target_bound

theorem normal_minimizer_frobenius_norm_le_sqrt_target
    (samples : List (Sample Source Target)) (P : Matrix Target Source ℂ)
    (targetEnergy : ℝ)
    (minimizer : ∀ Q, normalObjective samples P ≤ normalObjective samples Q)
    (target_nonneg : 0 ≤ targetEnergy)
    (target_bound : (samples.map (fun sample ↦ frobeniusSq sample.2)).sum ≤ targetEnergy) :
    frobeniusNorm P ≤ Real.sqrt targetEnergy := by
  have hP := frobeniusSq_le_of_normal_minimizer_target_bound samples P
    targetEnergy minimizer target_bound
  rw [← frobeniusNorm_sq] at hP
  have hsqrt : (Real.sqrt targetEnergy) ^ 2 = targetEnergy :=
    Real.sq_sqrt target_nonneg
  have hnorm : 0 ≤ frobeniusNorm P := norm_nonneg _
  have hsqrt_nonneg : 0 ≤ Real.sqrt targetEnergy := Real.sqrt_nonneg _
  nlinarith

def realMatrixPairing {I J : Type*} [Fintype I] [Fintype J]
    (A B : Matrix I J ℂ) : ℝ :=
  inner ℝ (matrixVector A) (matrixVector B)

def normalFittedEnergy (samples : List (Sample Source Target))
    (P : Matrix Target Source ℂ) : ℝ :=
  frobeniusSq P +
    (samples.map (fun sample ↦ frobeniusSq (P * sample.1))).sum

def normalCrossEnergy (W₀ : Matrix Target Source ℂ)
    (samples : List (Sample Source Target)) (P : Matrix Target Source ℂ) : ℝ :=
  realMatrixPairing P W₀ +
    (samples.map (fun sample ↦ realMatrixPairing (P * sample.1) sample.2)).sum

/-- The scalar energy identity returned by a nonzero-prior normal solve.  The matrix normal
equation `P * (I + Σ f f*) = W₀ + Σ y f*` reduces to this identity by pairing with P. -/
def normalSolveEnergyEquation (W₀ : Matrix Target Source ℂ)
    (samples : List (Sample Source Target)) (P : Matrix Target Source ℂ) : Prop :=
  normalFittedEnergy samples P = normalCrossEnergy W₀ samples P

/-! The rectangular bridge used by the normal equation.  The left side is the Frobenius
pairing in the `Target × Source` chart; the right side pairs the two columns after the
source contraction.  It is proved by expanding the finite coordinates, rather than by
invoking a square trace theorem whose index types would hide the rectangular reindexing. -/
theorem realMatrixPairing_mul_outer_eq
    (P : Matrix Target Source ℂ) (y : Column Target) (f : Column Source) :
    realMatrixPairing P (y * f.conjTranspose) =
      realMatrixPairing (P * f) y := by
  classical
  simp [realMatrixPairing, matrixVector, PiLp.inner_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, dotProduct]
  simp only [Fintype.sum_prod_type]
  simp [Fintype.sum_unique, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro target htarget
  simp only [mul_sub, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro source hsource
  ring

def normalSampleGram (samples : List (Sample Source Target)) : Matrix Source Source ℂ :=
  (samples.map (fun sample ↦ sample.1 * sample.1.conjTranspose)).sum

def normalSampleCross (samples : List (Sample Source Target)) : Matrix Target Source ℂ :=
  (samples.map (fun sample ↦ sample.2 * sample.1.conjTranspose)).sum

private theorem realMatrixPairing_add_right
    (A B C : Matrix Target Source ℂ) :
    realMatrixPairing A (B + C) = realMatrixPairing A B + realMatrixPairing A C := by
  have hvec : matrixVector (B + C) = matrixVector B + matrixVector C := by
    apply (EuclideanSpace.equiv (Target × Source) ℂ).injective
    funext index
    simp [matrixVector]
  rw [realMatrixPairing, hvec, inner_add_right]
  rfl

private theorem realMatrixPairing_sum_right
    (A : Matrix Target Source ℂ) (xs : List (Matrix Target Source ℂ)) :
    realMatrixPairing A xs.sum = (xs.map (realMatrixPairing A)).sum := by
  induction xs with
  | nil =>
      simp [realMatrixPairing, matrixVector, PiLp.inner_apply]
  | cons x xs ih =>
      simp only [List.sum_cons, List.map_cons]
      rw [realMatrixPairing_add_right, ih]

private theorem matrix_mul_list_sum
    (P : Matrix Target Source ℂ) (xs : List (Matrix Source Source ℂ)) :
    P * xs.sum = (xs.map (fun X ↦ P * X)).sum := by
  induction xs with
  | nil => simp
  | cons X xs ih =>
      simp only [List.sum_cons, List.map_cons]
      rw [Matrix.mul_add, ih]

theorem normalSolveEnergyEquation_of_matrix_equation
    (W₀ P : Matrix Target Source ℂ) (samples : List (Sample Source Target))
    (matrix_equation :
      P * (1 + normalSampleGram samples) = W₀ + normalSampleCross samples) :
    normalSolveEnergyEquation W₀ samples P := by
  have hleft :
      realMatrixPairing P (P * (1 + normalSampleGram samples)) =
        normalFittedEnergy samples P := by
    rw [Matrix.mul_add, Matrix.mul_one, realMatrixPairing_add_right]
    have hself : realMatrixPairing P P = frobeniusSq P := by
      simpa [realMatrixPairing, frobeniusSq] using
        (real_inner_self_eq_norm_sq (matrixVector P))
    rw [hself, normalSampleGram, matrix_mul_list_sum,
      realMatrixPairing_sum_right]
    simp only [normalFittedEnergy, List.map_map, Function.comp_apply]
    apply congrArg (fun z ↦ frobeniusSq P + z)
    apply congrArg List.sum
    apply List.map_congr_left
    intro sample hsample
    have hbridge := realMatrixPairing_mul_outer_eq P (P * sample.1) sample.1
    have hself : realMatrixPairing (P * sample.1) (P * sample.1) =
        frobeniusSq (P * sample.1) := by
      simpa [realMatrixPairing, frobeniusSq] using
        (real_inner_self_eq_norm_sq (matrixVector (P * sample.1)))
    simpa [Matrix.mul_assoc] using hbridge.trans hself
  have hright :
      realMatrixPairing P (W₀ + normalSampleCross samples) =
        normalCrossEnergy W₀ samples P := by
    rw [realMatrixPairing_add_right, normalSampleCross,
      realMatrixPairing_sum_right]
    apply congrArg (fun z ↦ realMatrixPairing P W₀ + z)
    rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro sample hsample
    exact realMatrixPairing_mul_outer_eq P sample.2 sample.1
  unfold normalSolveEnergyEquation
  calc
    normalFittedEnergy samples P =
        realMatrixPairing P (P * (1 + normalSampleGram samples)) := hleft.symm
    _ = realMatrixPairing P (W₀ + normalSampleCross samples) := by rw [matrix_equation]
    _ = normalCrossEnergy W₀ samples P := hright

private theorem list_cauchy_sq (xs ys : List ℝ) :
    (List.zipWith (· * ·) xs ys).sum ^ 2 ≤
      (xs.map (fun x => x ^ 2)).sum * (ys.map (fun y => y ^ 2)).sum := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      let A := (xs.map (fun z => z ^ 2)).sum
      let B := (ys.map (fun z => z ^ 2)).sum
      let c := (List.zipWith (· * ·) xs ys).sum
      have hrest : c ^ 2 ≤ A * B := by simpa [A, B, c] using ih ys
      have list_sq_nonneg : ∀ (zs : List ℝ),
          0 ≤ (zs.map (fun z => z ^ 2)).sum := by
        intro zs
        induction zs with
        | nil => simp
        | cons z zs ih =>
          simp only [List.map_cons, List.sum_cons]
          linarith [sq_nonneg z]
      have hAnonneg : 0 ≤ A := by simpa [A] using list_sq_nonneg xs
      have hBnonneg : 0 ≤ B := by simpa [B] using list_sq_nonneg ys
      by_cases hB : 0 < B
      · have hs := sq_nonneg (x * B - y * c)
        have hm : 0 ≤ B * (A * B - c ^ 2) :=
          mul_nonneg (le_of_lt hB) (sub_nonneg.mpr hrest)
        dsimp [A, B, c] at *
        simp only [List.sum_cons, List.map_cons]
        nlinarith
      · have hB0 : B = 0 := le_antisymm (le_of_not_gt hB) hBnonneg
        have hc2 : c ^ 2 ≤ 0 := by rw [hB0, mul_zero] at hrest; exact hrest
        have hc : c = 0 := by nlinarith
        dsimp [A, B, c] at *
        simp only [List.sum_cons, List.map_cons, hB0, hc]
        nlinarith [hAnonneg]

private theorem list_sum_neg (xs : List ℝ) :
    (xs.map (fun x => -x)).sum = -(xs.map (fun x => x)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

private theorem list_sum_map_neg {α : Type*} (xs : List α) (f : α → ℝ) :
    (xs.map (fun x => -f x)).sum = -(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

theorem normal_augmented_cauchy
    (samples : List (Sample Source Target)) (W₀ P : Matrix Target Source ℂ) :
    normalCrossEnergy W₀ samples P ^ 2 ≤
      normalFittedEnergy samples P * augmentedTargetEnergy W₀ samples := by
  let xs : List ℝ := frobeniusNorm P ::
    samples.map (fun sample ↦ frobeniusNorm (P * sample.1))
  let ys : List ℝ := frobeniusNorm W₀ ::
    samples.map (fun sample ↦ frobeniusNorm sample.2)
  let cross : ℝ :=
    (List.zipWith (· * ·) xs ys).sum
  have hcross : |normalCrossEnergy W₀ samples P| ≤ cross := by
    have h0 := abs_real_inner_le_norm (matrixVector P) (matrixVector W₀)
    have h0' : -frobeniusNorm P * frobeniusNorm W₀ ≤ realMatrixPairing P W₀ ∧
        realMatrixPairing P W₀ ≤ frobeniusNorm P * frobeniusNorm W₀ := by
      simpa [realMatrixPairing, frobeniusNorm] using (abs_le.mp h0)
    have hs :
        (samples.map (fun sample => realMatrixPairing (P * sample.1) sample.2)).sum ≤
          (samples.map (fun sample =>
            frobeniusNorm (P * sample.1) * frobeniusNorm sample.2)).sum :=
      List.sum_le_sum (fun (sample : Sample Source Target) hsample => by
        simpa [realMatrixPairing, frobeniusNorm] using
          (abs_le.mp (abs_real_inner_le_norm (matrixVector (P * sample.1))
            (matrixVector sample.2))).2)
    have hs' :
        (samples.map (fun sample =>
          -frobeniusNorm (P * sample.1) * frobeniusNorm sample.2)).sum ≤
            (samples.map (fun sample => realMatrixPairing (P * sample.1) sample.2)).sum :=
      List.sum_le_sum (fun (sample : Sample Source Target) hsample => by
        simpa [realMatrixPairing, frobeniusNorm] using
          (abs_le.mp (abs_real_inner_le_norm (matrixVector (P * sample.1))
            (matrixVector sample.2))).1)
    have hzip :
        List.zipWith (· * ·)
            (samples.map (fun sample => frobeniusNorm (P * sample.1)))
            (samples.map (fun sample => frobeniusNorm sample.2)) =
          samples.map (fun sample =>
            frobeniusNorm (P * sample.1) * frobeniusNorm sample.2) := by
      induction samples with
      | nil => rfl
      | cons sample samples ih => simp [ih]
    have hupper : normalCrossEnergy W₀ samples P ≤ cross := by
      dsimp [normalCrossEnergy, cross, xs, ys]
      rw [hzip]
      exact add_le_add h0'.2 hs
    have hlower : -cross ≤ normalCrossEnergy W₀ samples P := by
      dsimp [normalCrossEnergy, cross, xs, ys]
      rw [hzip]
      have hneg :
          (samples.map (fun sample =>
            -frobeniusNorm (P * sample.1) * frobeniusNorm sample.2)).sum =
              -(samples.map (fun sample =>
                frobeniusNorm (P * sample.1) * frobeniusNorm sample.2)).sum := by
        simpa only [neg_mul] using
          list_sum_map_neg samples (fun sample =>
            frobeniusNorm (P * sample.1) * frobeniusNorm sample.2)
      have hsum := add_le_add h0'.1 hs'
      rw [hneg] at hsum
      linarith
    exact (abs_le.mpr ⟨hlower, hupper⟩)
  have hlist := list_cauchy_sq xs ys
  have hcross_nonneg : 0 ≤ cross := by
    have hP : 0 ≤ frobeniusNorm P := norm_nonneg _
    have hW : 0 ≤ frobeniusNorm W₀ := norm_nonneg _
    have list_norm_products : ∀ zs : List (Sample Source Target),
        0 ≤ (List.zipWith (· * ·)
          (zs.map (fun sample ↦ frobeniusNorm (P * sample.1)))
          (zs.map (fun sample ↦ frobeniusNorm sample.2))).sum := by
      intro zs
      induction zs with
      | nil => simp
      | cons sample samples ih =>
        simp only [List.map_cons, List.zipWith, List.sum_cons]
        exact add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ih
    have hs := list_norm_products samples
    dsimp [cross, xs, ys]
    simpa only [List.zipWith, List.map_cons, List.sum_cons] using
      add_nonneg (mul_nonneg hP hW) hs
  have hcrosssq : normalCrossEnergy W₀ samples P ^ 2 ≤ cross ^ 2 := by
    have hsquare := (sq_le_sq₀ (abs_nonneg _) hcross_nonneg).mpr hcross
    simpa [sq_abs] using hsquare
  have henergy :
      (List.map (fun x => x ^ 2) xs).sum *
          (List.map (fun y => y ^ 2) ys).sum =
        normalFittedEnergy samples P * augmentedTargetEnergy W₀ samples := by
    have hPmap :
        samples.map (fun sample => frobeniusNorm (P * sample.1) ^ 2) =
          samples.map (fun sample => frobeniusSq (P * sample.1)) := by
      apply List.map_congr_left
      intro sample hsample
      exact frobeniusNorm_sq _
    have hYmap :
        samples.map (fun sample => frobeniusNorm sample.2 ^ 2) =
          samples.map (fun sample => frobeniusSq sample.2) := by
      apply List.map_congr_left
      intro sample hsample
      exact frobeniusNorm_sq _
    simp only [xs, ys, List.map_cons, List.sum_cons, List.map_map,
      Function.comp_apply, frobeniusNorm_sq]
    change
      (frobeniusSq P + (samples.map (fun sample => frobeniusNorm (P * sample.1) ^ 2)).sum) *
          (frobeniusSq W₀ + (samples.map (fun sample => frobeniusNorm sample.2 ^ 2)).sum) =
        normalFittedEnergy samples P * augmentedTargetEnergy W₀ samples
    rw [hPmap, hYmap]
    rfl
  exact hcrosssq.trans (henergy ▸ hlist)

theorem normal_solution_frobenius_norm_le_sqrt_augmented
    (samples : List (Sample Source Target)) (W₀ P : Matrix Target Source ℂ)
    (normal_equation : normalSolveEnergyEquation W₀ samples P) :
    frobeniusNorm P ≤ Real.sqrt (augmentedTargetEnergy W₀ samples) := by
  have augmented_nonneg : 0 ≤ augmentedTargetEnergy W₀ samples := by
    exact add_nonneg (frobeniusSq_nonneg W₀)
      (List.sum_nonneg fun value hvalue => by
        obtain ⟨sample, hsample, rfl⟩ := List.mem_map.mp hvalue
        exact frobeniusSq_nonneg _)
  have hfit_nonneg : 0 ≤ normalFittedEnergy samples P := by
    unfold normalFittedEnergy
    exact add_nonneg (frobeniusSq_nonneg P) (List.sum_nonneg fun value hvalue ↦ by
      obtain ⟨sample, hsample, rfl⟩ := List.mem_map.mp hvalue
      exact frobeniusSq_nonneg _)
  have hfit : normalFittedEnergy samples P ≤ augmentedTargetEnergy W₀ samples := by
    have augmented_cauchy := normal_augmented_cauchy samples W₀ P
    dsimp [normalSolveEnergyEquation] at normal_equation
    rw [normal_equation] at augmented_cauchy
    by_cases hzero : normalFittedEnergy samples P = 0
    · rw [hzero]
      exact augmented_nonneg
    · have hpos : 0 < normalFittedEnergy samples P := lt_of_le_of_ne hfit_nonneg (Ne.symm hzero)
      nlinarith
  have hP : frobeniusSq P ≤ augmentedTargetEnergy W₀ samples := by
    exact (le_add_of_nonneg_right (List.sum_nonneg fun value hvalue ↦ by
      obtain ⟨sample, hsample, rfl⟩ := List.mem_map.mp hvalue
      exact frobeniusSq_nonneg _)).trans hfit
  rw [← frobeniusNorm_sq] at hP
  have hsqrt : (Real.sqrt (augmentedTargetEnergy W₀ samples)) ^ 2 =
      augmentedTargetEnergy W₀ samples := Real.sq_sqrt augmented_nonneg
  nlinarith [norm_nonneg (matrixVector P), Real.sqrt_nonneg (augmentedTargetEnergy W₀ samples)]

theorem applied_reference_frobenius_bound
    (M P : Matrix Target Source ℂ) (appliedBound referenceBound : ℝ)
    (M_bound : frobeniusSq M ≤ appliedBound ^ 2)
    (P_bound : frobeniusSq P ≤ referenceBound ^ 2)
    (applied_nonneg : 0 ≤ appliedBound)
    (reference_nonneg : 0 ≤ referenceBound) :
    frobeniusSq (M - P) ≤ (appliedBound + referenceBound) ^ 2 := by
  have hMnorm : frobeniusNorm M ≤ appliedBound := by
    have hnorm : 0 ≤ frobeniusNorm M := norm_nonneg _
    have hbound : frobeniusNorm M ^ 2 ≤ appliedBound ^ 2 := by
      rw [frobeniusNorm_sq]
      exact M_bound
    nlinarith
  have hPnorm : frobeniusNorm P ≤ referenceBound := by
    have hnorm : 0 ≤ frobeniusNorm P := norm_nonneg _
    have hbound : frobeniusNorm P ^ 2 ≤ referenceBound ^ 2 := by
      rw [frobeniusNorm_sq]
      exact P_bound
    nlinarith
  have hsum : frobeniusNorm (M - P) ≤ appliedBound + referenceBound :=
    (frobeniusNorm_sub_le M P).trans (add_le_add hMnorm hPnorm)
  rw [← frobeniusNorm_sq]
  have hnonneg : 0 ≤ frobeniusNorm (M - P) := norm_nonneg _
  have hsum_nonneg : 0 ≤ appliedBound + referenceBound :=
    add_nonneg applied_nonneg reference_nonneg
  nlinarith

theorem applied_reference_frobenius_bound_of_normal_minimizer
    (samples : List (Sample Source Target)) (M P : Matrix Target Source ℂ)
    (targetEnergy appliedBound : ℝ)
    (minimizer : ∀ Q, normalObjective samples P ≤ normalObjective samples Q)
    (target_nonneg : 0 ≤ targetEnergy)
    (target_bound : (samples.map (fun sample ↦ frobeniusSq sample.2)).sum ≤ targetEnergy)
    (M_bound : frobeniusSq M ≤ appliedBound ^ 2)
    (applied_nonneg : 0 ≤ appliedBound) :
    frobeniusSq (M - P) ≤ (appliedBound + Real.sqrt targetEnergy) ^ 2 := by
  have hP : frobeniusSq P ≤ (Real.sqrt targetEnergy) ^ 2 := by
    have hP' := frobeniusSq_le_of_normal_minimizer_target_bound samples P
      targetEnergy minimizer target_bound
    rw [Real.sq_sqrt target_nonneg]
    exact hP'
  exact applied_reference_frobenius_bound M P appliedBound (Real.sqrt targetEnergy)
    M_bound hP applied_nonneg (Real.sqrt_nonneg _)

theorem minimum_of_two_valid_bounds {value bound₁ bound₂ : ℝ}
    (h₁ : value ≤ bound₁) (h₂ : value ≤ bound₂) :
    value ≤ min bound₁ bound₂ := by
  exact le_min h₁ h₂

omit [Fintype Target] in
theorem rankOne_update_residual_identity
    (M : Matrix Target Source ℂ) (H : Matrix Source Source ℂ)
    (B : Matrix Target Source ℂ) (x : Column Source) (y : Column Target)
    (g : Column Source) (E : Matrix Target Source ℂ) :
    normalResidual (updatedResponse M x y g E) (updatedGram H x)
        (updatedCross B y x) =
      normalResidual M H B +
        (y - M * x) *
          (g.conjTranspose * (updatedGram H x) - x.conjTranspose) +
        E * (updatedGram H x) := by
  unfold normalResidual updatedResponse updatedGram updatedCross
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.mul_assoc]
  abel

omit [Fintype Target] in
theorem normalResidual_preserved_of_gain_receipt
    (M : Matrix Target Source ℂ) (H : Matrix Source Source ℂ)
    (B : Matrix Target Source ℂ) (x : Column Source) (y : Column Target)
    (g : Column Source) (E : Matrix Target Source ℂ)
    (gain_receipt : g.conjTranspose * updatedGram H x = x.conjTranspose)
    (zero_error : E = 0) :
    normalResidual (updatedResponse M x y g E) (updatedGram H x)
        (updatedCross B y x) = normalResidual M H B := by
  rw [rankOne_update_residual_identity, gain_receipt, zero_error]
  simp

omit [Fintype Source] in
theorem gram_increment
    (x dx : Column Source) :
    (x + dx) * (x + dx).conjTranspose - x * x.conjTranspose =
      dx * x.conjTranspose + x * dx.conjTranspose + dx * dx.conjTranspose := by
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_add]
  abel

omit [Fintype Source] [Fintype Target] in
theorem cross_increment
    (y dy : Column Target) (x dx : Column Source) :
    (y + dy) * (x + dx).conjTranspose - y * x.conjTranspose =
      dy * x.conjTranspose + y * dx.conjTranspose + dy * dx.conjTranspose := by
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_add]
  abel

omit [Fintype Target] in
theorem normal_square_completion
    (M P : Matrix Target Source ℂ) (H : Matrix Source Source ℂ)
    (B : Matrix Target Source ℂ) (hB : B = P * H)
    (hH : H.conjTranspose = H) :
    M * H * M.conjTranspose - M * B.conjTranspose - B * M.conjTranspose =
      (M - P) * H * (M - P).conjTranspose - P * H * P.conjTranspose := by
  subst B
  rw [Matrix.conjTranspose_mul, hH, Matrix.conjTranspose_sub]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

section Audit

#print axioms realMatrixPairing_mul_outer_eq
#print axioms normalSolveEnergyEquation_of_matrix_equation
#print axioms unitPrior_data_separation
#print axioms unitPriorEnergy_pos
#print axioms normalProxyTarget_eq_current_mul_feature_add_covector
#print axioms normalProxyTarget_residual_eq_scaled_covector
#print axioms normalProxyCross_eq_updatedCross
#print axioms normal_solution_frobenius_norm_le_sqrt_augmented
#print axioms rankOne_update_residual_identity
#print axioms normalResidual_preserved_of_gain_receipt
#print axioms gram_increment
#print axioms cross_increment
#print axioms normal_square_completion
#print axioms normal_minimizer_frobenius_norm_le_sqrt_target
#print axioms applied_reference_frobenius_bound_of_normal_minimizer
#print axioms minimum_of_two_valid_bounds
#print axioms weighted_cauchy_schwarz
#print axioms complex_schur_action_sq
#print axioms square_schur_operator_bound
#print axioms gram_operator_bound

end Audit

end Holonics.Physics.AccumulatedNormalResponse
