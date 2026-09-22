import ElementaryHolonics.Transport.GeneratorMachineCharts
import Mathlib.Tactic

/-!
# Rectangular contact-factor scaling and cotangents

This owner states the exact rational matrix laws used by the resident contact-scale operation.
The machine realification supplies real-coordinate rectangular matrices; no complex-linear or
nonlinear-Jacobian claim is made here.  The rectangular cotangent `⟪G,B⟫_F` is kept distinct from
the scalar Gram derivative `2 ρ BᵀB`.
-/

open scoped BigOperators Matrix
open Matrix

namespace Soma.Holonics.Transport.ContactFactorScale

abbrev Mat (m n : Type*) := Matrix m n ℚ

def amplitude (rho : ℚ) (B : Mat m n) : Mat m n := rho • B

def gram {m n : Type*} [Fintype m] [Fintype n] (B : Mat m n) : Mat n n := Bᵀ * B

def frobeniusPairing {m n : Type*} [Fintype m] [Fintype n] (A B : Mat m n) : ℚ :=
  ∑ i, (A i) ⬝ᵥ (B i)

theorem amplitude_variation (rho drho : ℚ) (B : Mat m n) :
    amplitude (rho + drho) B - amplitude rho B = drho • B := by
  funext i j
  simp [amplitude, sub_eq_add_neg, add_smul]

theorem amplitude_directional_pairing {m n : Type*} [Fintype m] [Fintype n]
    (rho drho : ℚ) (B P : Mat m n) :
    frobeniusPairing P (amplitude (rho + drho) B - amplitude rho B) =
      drho * frobeniusPairing P B := by
  rw [amplitude_variation]
  simp [frobeniusPairing, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem gram_scale {m n : Type*} [Fintype m] [Fintype n]
    (rho : ℚ) (B : Mat m n) :
    gram (amplitude rho B) = rho ^ 2 • gram B := by
  ext i j
  simp [gram, amplitude, Matrix.mul_apply, dotProduct, Finset.mul_sum,
    Finset.sum_mul, smul_eq_mul]
  ring

theorem gram_scale_explicit {m n : Type*} [Fintype m] [Fintype n]
    (rho : ℚ) (B : Mat m n) :
    (amplitude rho B)ᵀ * amplitude rho B = rho ^ 2 • (Bᵀ * B) := by
  exact gram_scale rho B

theorem gram_directional {m n : Type*} [Fintype m] [Fintype n]
    (rho drho : ℚ) (B : Mat m n) :
    gram (amplitude (rho + drho) B) - gram (amplitude rho B) =
      (2 * rho * drho + drho ^ 2) • gram B := by
  rw [gram_scale, gram_scale]
  ext i j
  simp [sub_eq_add_neg, smul_eq_mul]
  ring

theorem nonzero_amplitude_null_kernel {m n : Type*} [Fintype n]
    {x : n → ℚ} {rho : ℚ} (hrho : rho ≠ 0)
    (B : Mat m n) :
    amplitude rho B *ᵥ x = 0 ↔ B *ᵥ x = 0 := by
  simp only [amplitude, smul_mulVec]
  constructor
  · intro h
    rcases smul_eq_zero.mp h with hzero | hvector
    · exact (hrho hzero).elim
    · exact hvector
  · intro h
    rw [h]
    simp

theorem factor_cotangent_pairing
    {m n k0 k1 : Type*}
    [Fintype m] [Fintype n] [Fintype k0] [Fintype k1]
    (P0 : Mat m k0) (C0 : Mat n k0)
    (P1 : Mat m k1) (C1 : Mat n k1) (B : Mat m n) :
    frobeniusPairing (P0 * C0ᵀ + P1 * C1ᵀ) B =
      frobeniusPairing P0 (B * C0) + frobeniusPairing P1 (B * C1) := by
  classical
  simp only [frobeniusPairing, Matrix.add_apply, dotProduct_add, mul_apply, transpose_apply,
    dotProduct, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  have hfactor0 :
      (∑ i, ∑ x, (∑ j, P0 i j * C0 x j) * B i x) =
        ∑ i, ∑ x, ∑ j, P0 i x * (B i j * C0 j x) := by
    calc
      (∑ i, ∑ x, (∑ j, P0 i j * C0 x j) * B i x) =
          ∑ i, ∑ x, ∑ j, (P0 i j * C0 x j) * B i x := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.sum_mul]
      _ = ∑ i, ∑ j, ∑ x, (P0 i j * C0 x j) * B i x := by
            apply Finset.sum_congr rfl
            intro i hi
            exact Finset.sum_comm
      _ = ∑ i, ∑ x, ∑ j, P0 i x * (B i j * C0 j x) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro x hx
            ring
  have hfactor1 :
      (∑ i, ∑ x, (∑ j, P1 i j * C1 x j) * B i x) =
        ∑ i, ∑ x, ∑ j, P1 i x * (B i j * C1 j x) := by
    calc
      (∑ i, ∑ x, (∑ j, P1 i j * C1 x j) * B i x) =
          ∑ i, ∑ x, ∑ j, (P1 i j * C1 x j) * B i x := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.sum_mul]
      _ = ∑ i, ∑ j, ∑ x, (P1 i j * C1 x j) * B i x := by
            apply Finset.sum_congr rfl
            intro i hi
            exact Finset.sum_comm
      _ = ∑ i, ∑ x, ∑ j, P1 i x * (B i j * C1 j x) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro x hx
            ring
  simp_rw [add_mul]
  simp_rw [Finset.sum_add_distrib]
  rw [hfactor0, hfactor1]

end Soma.Holonics.Transport.ContactFactorScale
