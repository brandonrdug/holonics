import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

/-!
# Exact accumulated normal-response algebra

This owner records the finite complex matrix identity behind one rank-one accumulated update.  The
matrices are ordinary algebraic carriers: no optimizer, kernel, numerical implementation, or
physical interpretation is introduced here.
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

end Audit

end Soma.Holonics.Physics.AccumulatedNormalResponse
