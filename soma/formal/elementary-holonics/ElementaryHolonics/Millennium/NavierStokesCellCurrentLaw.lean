import ElementaryHolonics.Millennium.NavierStokesPeriodicFlux

/-!
# Divergence-freeness is the current law on the cell

The Clay posing reads `div u = 0` as "the fluid is incompressible".  In this tree the divergence
is the trace of the Jacobian, proved equal to the bare diagonal sum, and it descends to the
per-mode orthogonality `k · û(k) = 0`.  This owner supplies the third reading, the one Brandon
named: on a cell, divergence-freeness is Kirchhoff's current law.  The oriented flux of the field
through the six faces of the unit cell balances exactly,

```text
Σ_i ( ∫_{x_i = 1} u_i − ∫_{x_i = 0} u_i ) = 0,
```

and this needs no periodicity: it is the divergence theorem returning the six addressed faces of
one cell and the pointwise null sum `Σ_i ∂_i u_i = 0` paying the interior.  Sol's periodic face
cancellation (`integral_divergence_unitCube_eq_zero_of_onePeriodic`) is the same face population
with opposite faces identified; the cellular node law (`HolonicDiscreteInduction.sum_nodeDivergence_eq_zero`)
is the same statement on an integer carrier.  Kirchhoff's current law is the no-storage case of
continuity, and incompressibility is exactly zero storage of mass at every cell.
-/

noncomputable section

open Set MeasureTheory

namespace Soma.Holonics.Millennium.NavierStokesCellCurrentLaw

open ContDiff Set MeasureTheory
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux

/-- The chart identification of the Euclidean carrier with three real coordinates. -/
abbrev chart : Space ≃L[ℝ] (Fin 3 → ℝ) := EuclideanSpace.equiv (Fin 3) ℝ

/-- The flux of the `i`-th component through the face `x_i = side` of the unit cell. -/
def faceFlux (v : InitialVelocity) (i : Fin 3) (side : ℝ) : ℝ :=
  ∫ y in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) ((fun _ : Fin 3 => (1 : ℝ)) ∘ i.succAbove),
    v (chart.symm (i.insertNth side y)) i

/-- The face balance of the unit cell: outgoing flux through the front faces minus incoming flux
through the back faces. -/
def faceBalance (v : InitialVelocity) : ℝ :=
  ∑ i : Fin 3, (faceFlux v i 1 - faceFlux v i 0)

/-- **The divergence theorem on one cell.**  The integrated divergence is the face balance. -/
theorem integral_divergence_unitCube_eq_faceBalance
    (v : InitialVelocity) (hsmooth : ContDiff ℝ 1 v) :
    ∫ x in unitCube, divergence v x = faceBalance v := by
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
    _ = faceBalance v := hdivergence

/-- **Kirchhoff's current law on the cell.**  A divergence-free `C¹` field has zero face balance
on the unit cell: what enters through the back faces leaves through the front faces.  No
periodicity is used. -/
theorem faceBalance_eq_zero_of_divergenceFree
    (v : InitialVelocity) (hsmooth : ContDiff ℝ 1 v) (hdivergence : ∀ x, divergence v x = 0) :
    faceBalance v = 0 := by
  rw [← integral_divergence_unitCube_eq_faceBalance v hsmooth]
  simp [hdivergence]

/-- The cell current law for every admitted initial datum. -/
theorem faceBalance_eq_zero_of_initialVelocityCondition
    (v : InitialVelocity) (hv : InitialVelocityCondition v) : faceBalance v = 0 :=
  faceBalance_eq_zero_of_divergenceFree v (hv.smooth.of_le (by simp)) hv.divergenceFree

section Audit

#print axioms integral_divergence_unitCube_eq_faceBalance
#print axioms faceBalance_eq_zero_of_divergenceFree
#print axioms faceBalance_eq_zero_of_initialVelocityCondition

end Audit

end Soma.Holonics.Millennium.NavierStokesCellCurrentLaw
