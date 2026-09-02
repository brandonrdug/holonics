import ElementaryHolonics.Millennium.NavierStokesModalRiccati

/-!
# Lagrange on the torus modes: the Jacobian mode's Frobenius norm is the vorticity mode's energy

For a real frequency `k` and a divergence-free mode `v` (`k · v = 0`) the Lagrange identity
`|k × v|² = |k|² |v|² − |k · v|²` reduces to `|k × v|² = |k|² |v|²`.  Hence the vorticity mode
`2πi (k × v)` has energy `(2π)² |k|² |v|²`, and that is exactly the Frobenius norm of the
Jacobian mode `(2πi k_j v_i)_{ij}`.  Every entry of the Jacobian mode is therefore bounded by the
square root of the modal vorticity energy.  This is the passage from the tail masses that pay the
shell-step cost to the modal energies the Riccati inequality controls.
-/

noncomputable section

open Set Filter Topology
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesModeLagrange

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment
open Soma.Holonics.Millennium.NavierStokesAlignedStrainBudget

/-- The squared entries of the Jacobian mode sum to `(2π)² |k|² |v|²`. -/
theorem sum_norm_sq_fourierJacobianMode (k : SpatialFrequency) (v : ComplexVector) :
    ∑ i : Fin 3, ∑ j : Fin 3, ‖fourierJacobianMode k v i j‖ ^ 2 =
      (2 * Real.pi) ^ 2 * frequencySquared k * ∑ i : Fin 3, ‖v i‖ ^ 2 := by
  have hentry : ∀ i j : Fin 3, ‖fourierJacobianMode k v i j‖ ^ 2 =
      (2 * Real.pi) ^ 2 * (k j : ℝ) ^ 2 * ‖v i‖ ^ 2 := by
    intro i j
    unfold fourierJacobianMode
    rw [norm_mul, mul_pow]
    congr 1
    simp [mul_pow, sq_abs, abs_of_nonneg Real.pi_nonneg]
  simp_rw [hentry]
  unfold frequencySquared
  simp only [Fin.sum_univ_three]
  ring

/-- **Lagrange on a divergence-free mode.**  `Σ_i |(k × v)_i|² = |k|² |v|²` when `k · v = 0`. -/
theorem sum_norm_sq_complexCross_of_dot_eq_zero (k : SpatialFrequency) (v : ComplexVector)
    (h : complexDot (complexFrequencyVector k) v = 0) :
    ∑ i : Fin 3, ‖complexCross (complexFrequencyVector k) v i‖ ^ 2 =
      frequencySquared k * ∑ i : Fin 3, ‖v i‖ ^ 2 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [complexDot, complexFrequencyVector, dotProduct, Fin.sum_univ_three,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, Complex.zero_re, Complex.zero_im, zero_mul, sub_zero, add_zero] at hre him
  simp only [complexCross, complexFrequencyVector, cross_apply, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons,
    Complex.sq_norm,
    Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero, add_zero]
  unfold frequencySquared
  simp only [Fin.sum_univ_three]
  linear_combination
    (-((k 0 : ℝ) * (v 0).re + (k 1 : ℝ) * (v 1).re + (k 2 : ℝ) * (v 2).re)) * hre +
    (-((k 0 : ℝ) * (v 0).im + (k 1 : ℝ) * (v 1).im + (k 2 : ℝ) * (v 2).im)) * him

/-- The vorticity mode of a divergence-free mode has energy `(2π)² |k|² |v|²`. -/
theorem sum_norm_sq_frequencyCurlMultiplier (k : SpatialFrequency) (v : ComplexVector)
    (h : complexDot (complexFrequencyVector k) v = 0) :
    ∑ i : Fin 3, ‖frequencyCurlMultiplier k v i‖ ^ 2 =
      (2 * Real.pi) ^ 2 * frequencySquared k * ∑ i : Fin 3, ‖v i‖ ^ 2 := by
  have hentry : ∀ i : Fin 3, ‖frequencyCurlMultiplier k v i‖ ^ 2 =
      (2 * Real.pi) ^ 2 * ‖complexCross (complexFrequencyVector k) v i‖ ^ 2 := by
    intro i
    unfold frequencyCurlMultiplier
    rw [Pi.smul_apply, norm_smul, mul_pow]
    congr 1
    simp [abs_of_nonneg Real.pi_nonneg]
  simp_rw [hentry]
  rw [← Finset.mul_sum, sum_norm_sq_complexCross_of_dot_eq_zero k v h]
  ring

/-- **Every Jacobian entry is paid by the modal vorticity energy.** -/
theorem norm_fourierJacobianMode_sq_le (k : SpatialFrequency) (v : ComplexVector)
    (h : complexDot (complexFrequencyVector k) v = 0) (i j : Fin 3) :
    ‖fourierJacobianMode k v i j‖ ^ 2 ≤ ∑ i : Fin 3, ‖frequencyCurlMultiplier k v i‖ ^ 2 := by
  rw [sum_norm_sq_frequencyCurlMultiplier k v h, ← sum_norm_sq_fourierJacobianMode k v]
  calc ‖fourierJacobianMode k v i j‖ ^ 2
      ≤ ∑ j : Fin 3, ‖fourierJacobianMode k v i j‖ ^ 2 :=
        Finset.single_le_sum (f := fun j ↦ ‖fourierJacobianMode k v i j‖ ^ 2)
          (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖fourierJacobianMode k v i j‖ ^ 2 :=
        Finset.single_le_sum (f := fun i ↦ ∑ j : Fin 3, ‖fourierJacobianMode k v i j‖ ^ 2)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i)

section Audit

#print axioms sum_norm_sq_complexCross_of_dot_eq_zero
#print axioms sum_norm_sq_frequencyCurlMultiplier
#print axioms norm_fourierJacobianMode_sq_le

end Audit

end Soma.Holonics.Millennium.NavierStokesModeLagrange
