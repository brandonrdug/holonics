import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import ElementaryHolonics.Millennium.NavierStokesVorticity

/-!
# Periodic flux cancellation on the Navier--Stokes carrier

This module places the periodic face-cancellation law on the actual three-dimensional
`NavierStokes.Space`.  Mathlib's Bochner divergence theorem first returns all six oriented face
integrals of the unit cube.  `IsOnePeriodic` then pairs the opposite faces pointwise, so the
complete divergence period is zero.

The proof passes through the volume-preserving coordinate equivalence for Euclidean space and
the existing Jacobian trace theorem.  Thus neither the volume measure nor the repository's
basis-independent `divergence` is replaced by a coordinate-only surrogate.
-/

noncomputable section

open ContDiff Set MeasureTheory

namespace Soma.Holonics.Millennium.NavierStokesPeriodicFlux

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesVorticity

/-- The standard unit cube, retained on the actual Euclidean `Space` carrier. -/
def unitCube : Set Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ) ⁻¹'
    Icc (0 : Fin 3 → ℝ) (fun _ => (1 : ℝ))

/-- The front face is the back face translated by the declared unit-period direction. -/
theorem unitFront_eq_unitBack_add_single (i : Fin 3) (y : Fin 2 → ℝ) :
    (EuclideanSpace.equiv (Fin 3) ℝ).symm (i.insertNth 1 y) =
      (EuclideanSpace.equiv (Fin 3) ℝ).symm (i.insertNth 0 y) +
        EuclideanSpace.single i 1 := by
  apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
  simp only [map_add, ContinuousLinearEquiv.apply_symm_apply]
  apply funext
  rw [i.forall_iff_succAbove]
  constructor
  · simp
  · intro j
    simp

/-- A coordinate unit vector returns to the standard Euclidean orthonormal basis vector. -/
theorem equiv_symm_single_eq_basisFun (i : Fin 3) :
    (EuclideanSpace.equiv (Fin 3) ℝ).symm (Pi.single i 1) =
      EuclideanSpace.basisFun (Fin 3) ℝ i := by
  change WithLp.toLp 2 (Pi.single i 1) = _
  rw [EuclideanSpace.basisFun_apply]
  rfl

/-- The coordinate sum used by the Bochner divergence theorem is the repository's
basis-independent divergence receiver. -/
theorem sum_coordinate_fderiv_eq_divergence (v : InitialVelocity) (x : Space) :
    (∑ i : Fin 3,
        (EuclideanSpace.proj i).comp (fderiv ℝ v x)
          ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Pi.single i 1))) =
      divergence v x := by
  rw [← divergenceFromJacobian_velocityJacobianAt]
  simp only [divergenceFromJacobian, velocityJacobianAt, jacobianMatrix_apply]
  congr 1
  funext i
  rw [equiv_symm_single_eq_basisFun]
  rfl

/-- **Periodic face conservation.**  The total divergence over one spatial period is zero.

Global `C¹` regularity supplies continuity and integrability on the compact cube.  Periodicity
is used only after the divergence theorem has returned the two addressed faces in each coordinate
direction. -/
theorem integral_divergence_unitCube_eq_zero_of_onePeriodic
    (v : InitialVelocity) (hperiodic : IsOnePeriodic v) (hsmooth : ContDiff ℝ 1 v) :
    ∫ x in unitCube, divergence v x = 0 := by
  let eL : Space ≃L[ℝ] (Fin 3 → ℝ) := EuclideanSpace.equiv (Fin 3) ℝ
  let component : Fin 3 → (Fin 3 → ℝ) → ℝ :=
    fun i z => v (eL.symm z) i
  let componentDerivative :
      Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ :=
    fun i z => (EuclideanSpace.proj i).comp
      ((fderiv ℝ v (eL.symm z)).comp eL.symm.toContinuousLinearMap)
  have he_volume : MeasurePreserving eL volume volume := by
    change MeasurePreserving (@WithLp.ofLp 2 (Fin 3 → ℝ)) volume volume
    exact PiLp.volume_preserving_ofLp (Fin 3)
  have hcontinuous : ∀ i,
      ContinuousOn (component i) (Icc (0 : Fin 3 → ℝ) (fun _ => 1)) := by
    intro i
    exact ((EuclideanSpace.proj i).continuous.comp
      (hsmooth.continuous.comp eL.symm.continuous)).continuousOn
  have hdifferentiable :
      ∀ x ∈ (Set.pi univ fun _ : Fin 3 => Ioo (0 : ℝ) 1) \
          (∅ : Set (Fin 3 → ℝ)), ∀ i,
        HasFDerivAt (component i) (componentDerivative i x) x := by
    intro x _hx i
    exact (EuclideanSpace.proj i).hasFDerivAt.comp x
      ((hsmooth.differentiable (by norm_num) (eL.symm x)).hasFDerivAt.comp x
        eL.symm.hasFDerivAt)
  have hdivergenceContinuous : Continuous (divergence v) := by
    have hsum : Continuous fun x : Space => ∑ i : Fin 3,
        (EuclideanSpace.proj i).comp (fderiv ℝ v x)
          ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Pi.single i 1)) := by
      apply continuous_finset_sum
      intro i _hi
      have happly := hsmooth.continuous_fderiv_apply (by norm_num)
      have hdirection := happly.comp
        (continuous_id.prodMk
          (continuous_const : Continuous fun _ : Space =>
            (EuclideanSpace.equiv (Fin 3) ℝ).symm (Pi.single i 1)))
      exact (EuclideanSpace.proj i).continuous.comp hdirection
    exact hsum.congr (fun x => sum_coordinate_fderiv_eq_divergence v x)
  have hcoordinateDivergence : ∀ z : Fin 3 → ℝ,
      (∑ i : Fin 3, componentDerivative i z (Pi.single i 1)) =
        divergence v (eL.symm z) := by
    intro z
    simpa [componentDerivative, eL] using
      sum_coordinate_fderiv_eq_divergence v (eL.symm z)
  have hcoordinateIntegrable : IntegrableOn
      (fun z : Fin 3 → ℝ => ∑ i : Fin 3, componentDerivative i z (Pi.single i 1))
      (Icc (0 : Fin 3 → ℝ) (fun _ => 1)) := by
    have hcont : Continuous fun z : Fin 3 → ℝ => divergence v (eL.symm z) :=
      hdivergenceContinuous.comp eL.symm.continuous
    exact (hcont.continuousOn.integrableOn_compact isCompact_Icc).congr_fun
      (fun z _hz => (hcoordinateDivergence z).symm) measurableSet_Icc
  have hdivergence :=
    integral_divergence_of_hasFDerivAt_off_countable'
      (0 : Fin 3 → ℝ) (fun _ : Fin 3 => (1 : ℝ)) (fun _ => zero_le_one)
      component componentDerivative (∅ : Set (Fin 3 → ℝ)) (by simp)
      hcontinuous hdifferentiable hcoordinateIntegrable
  calc
    ∫ x in unitCube, divergence v x =
        ∫ z in Icc (0 : Fin 3 → ℝ) (fun _ => 1), divergence v (eL.symm z) := by
      simpa [unitCube, eL] using
        he_volume.setIntegral_preimage_emb eL.toHomeomorph.measurableEmbedding
          (fun z : Fin 3 → ℝ => divergence v (eL.symm z))
          (Icc (0 : Fin 3 → ℝ) (fun _ => 1))
    _ = ∫ z in Icc (0 : Fin 3 → ℝ) (fun _ => 1),
          ∑ i : Fin 3, componentDerivative i z (Pi.single i 1) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro z _hz
      exact (hcoordinateDivergence z).symm
    _ = ∑ i : Fin 3,
          ((∫ y in Icc
              ((0 : Fin 3 → ℝ) ∘ i.succAbove)
              ((fun _ : Fin 3 => (1 : ℝ)) ∘ i.succAbove),
                component i (i.insertNth 1 y)) -
            ∫ y in Icc
              ((0 : Fin 3 → ℝ) ∘ i.succAbove)
              ((fun _ : Fin 3 => (1 : ℝ)) ∘ i.succAbove),
                component i (i.insertNth 0 y)) := hdivergence
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _hi
      apply sub_eq_zero.mpr
      apply setIntegral_congr_fun measurableSet_Icc
      intro y _hy
      change v (eL.symm (i.insertNth 1 y)) i = v (eL.symm (i.insertNth 0 y)) i
      rw [unitFront_eq_unitBack_add_single]
      exact congrArg (fun z : Space => z i)
        (hperiodic (eL.symm (i.insertNth 0 y)) i)

section Audit

#print axioms unitFront_eq_unitBack_add_single
#print axioms equiv_symm_single_eq_basisFun
#print axioms sum_coordinate_fderiv_eq_divergence
#print axioms integral_divergence_unitCube_eq_zero_of_onePeriodic

end Audit

end Soma.Holonics.Millennium.NavierStokesPeriodicFlux
