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

namespace Soma.Holonics.Physics.AccumulatedNormalResponse

open Matrix

abbrev Column (Index : Type*) := Matrix Index Unit ℂ

variable {Source Target : Type*} [Fintype Source] [Fintype Target]

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
def matrixVector (M : Matrix Target Source ℂ) : EuclideanSpace ℂ (Target × Source) :=
  (EuclideanSpace.equiv (Target × Source) ℂ).symm
    (fun index ↦ M index.1 index.2)

/-- The squared Frobenius norm in the declared finite complex matrix chart. -/
def frobeniusSq (M : Matrix Target Source ℂ) : ℝ :=
  ‖matrixVector M‖ ^ 2

/-- The Frobenius norm in the declared finite complex matrix chart. -/
def frobeniusNorm (M : Matrix Target Source ℂ) : ℝ :=
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

theorem frobeniusSq_nonneg (M : Matrix Target Source ℂ) :
    0 ≤ frobeniusSq M := by
  exact sq_nonneg _

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

end Soma.Holonics.Physics.AccumulatedNormalResponse
