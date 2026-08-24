import ElementaryHolonics.Millennium.NavierStokesPeriodicFlux
import ElementaryHolonics.Millennium.NavierStokesTorusFourier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The unit cube and the genuine spatial torus carry the same period integral

The Euclidean unit cube and the quotient torus are two receiver charts for one spatial period.
This owner records the exact measure-preserving passage between them.  The only discarded
population is the coordinate boundary, which is Lebesgue-null; no Fourier cutoff or numerical
approximation enters.
-/

noncomputable section

open MeasureTheory Set

namespace Soma.Holonics.Millennium.NavierStokesTorusCubeIntegral

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The coordinatewise quotient sends the half-open product cube to probability Haar measure on
the genuine spatial torus. -/
theorem piToSpatialTorus_measurePreserving_Ioc :
    MeasurePreserving piToSpatialTorus
      (volume.restrict
        (Set.pi Set.univ (fun _ : Fin 3 ↦ Set.Ioc (0 : ℝ) 1)))
      (volume : Measure SpatialTorus) := by
  have hcoordinate : ∀ _i : Fin 3,
      MeasurePreserving ((↑) : ℝ → UnitAddCircle)
        (volume.restrict (Set.Ioc (0 : ℝ) 1))
        (volume : Measure UnitAddCircle) :=
    fun _i ↦ by
      have hstandard := UnitAddCircle.measurePreserving_mk 0
      have hmeasure :
          (@volume UnitAddCircle (AddCircle.measureSpace 1)) =
            AddCircle.haarAddCircle := by
        change ENNReal.ofReal 1 • Measure.addHaarMeasure ⊤ =
          Measure.addHaarMeasure ⊤
        simp
      rw [hmeasure] at hstandard
      simpa only [zero_add] using hstandard
  have hpi := MeasureTheory.measurePreserving_pi
    (fun _ : Fin 3 ↦ volume.restrict (Set.Ioc (0 : ℝ) 1))
    (fun _ : Fin 3 ↦ (volume : Measure UnitAddCircle)) hcoordinate
  rw [← Measure.restrict_pi_pi] at hpi
  simpa only [MeasureTheory.volume_pi, piToSpatialTorus] using hpi

/-- Replacing the half-open product cube by the closed product cube changes no integral. -/
theorem integral_piToSpatialTorus_productIcc
    (field : C(SpatialTorus, ℝ)) :
    ∫ z in Set.Icc (0 : Fin 3 → ℝ) (fun _ ↦ (1 : ℝ)),
        field (piToSpatialTorus z) =
      ∫ q : SpatialTorus, field q := by
  rw [MeasureTheory.volume_pi,
    ← setIntegral_congr_set Measure.univ_pi_Ioc_ae_eq_Icc]
  rw [← piToSpatialTorus_measurePreserving_Ioc.map_eq]
  simpa only [MeasureTheory.volume_pi] using
    (MeasureTheory.integral_map
      piToSpatialTorus_measurePreserving_Ioc.aemeasurable
      field.continuous.aestronglyMeasurable).symm

/-- **Exact period-chart transport.**  Integrating a torus field over probability Haar measure is
the same as integrating its Euclidean pullback over the repository's closed unit cube. -/
theorem integral_euclideanToSpatialTorus_unitCube
    (field : C(SpatialTorus, ℝ)) :
    ∫ x in unitCube, field (euclideanToSpatialTorus x) =
      ∫ q : SpatialTorus, field q := by
  let eL : Space ≃L[ℝ] (Fin 3 → ℝ) := EuclideanSpace.equiv (Fin 3) ℝ
  have heVolume : MeasurePreserving eL volume volume := by
    change MeasurePreserving (@WithLp.ofLp 2 (Fin 3 → ℝ)) volume volume
    exact PiLp.volume_preserving_ofLp (Fin 3)
  calc
    ∫ x in unitCube, field (euclideanToSpatialTorus x) =
        ∫ z in Set.Icc (0 : Fin 3 → ℝ) (fun _ ↦ (1 : ℝ)),
          field (piToSpatialTorus z) := by
      simpa [unitCube, euclideanToSpatialTorus, eL] using
        heVolume.setIntegral_preimage_emb eL.toHomeomorph.measurableEmbedding
          (fun z : Fin 3 → ℝ ↦ field (piToSpatialTorus z))
          (Set.Icc (0 : Fin 3 → ℝ) (fun _ ↦ (1 : ℝ)))
    _ = ∫ q : SpatialTorus, field q :=
      integral_piToSpatialTorus_productIcc field

section Audit

#print axioms piToSpatialTorus_measurePreserving_Ioc
#print axioms integral_piToSpatialTorus_productIcc
#print axioms integral_euclideanToSpatialTorus_unitCube

end Audit

end Soma.Holonics.Millennium.NavierStokesTorusCubeIntegral
