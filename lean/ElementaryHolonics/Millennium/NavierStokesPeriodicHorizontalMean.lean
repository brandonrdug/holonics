import ElementaryHolonics.Millennium.NavierStokesTorusHorizontalMean
import ElementaryHolonics.Millennium.NavierStokesHorizontalMean
import ElementaryHolonics.Millennium.NavierStokesOpenFourierSpatialSymbols

/-!
# The periodic mean is the actual horizontal integral

Normalized Haar averaging on the horizontal torus equals integration over the physical unit
square. The quotient representatives disappear through the actual periodic projection. No choice
of representative or Fourier reconstruction replaces the physical integral.
-/

noncomputable section
open Set Function MeasureTheory
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesPeriodicHorizontalMean
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusHorizontalMean
open Soma.Holonics.Millennium.NavierStokesHorizontalMean
open Soma.Holonics.Millennium.NavierStokesOpenFourierSpatialSymbols

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem unitCircle_integral_eq_interval (f : UnitAddCircle → ℂ) :
    (∫ z : UnitAddCircle, f z) = ∫ x in (0 : ℝ)..1, f (x : UnitAddCircle) := by
  change (∫ z : UnitAddCircle, f z ∂AddCircle.haarAddCircle) = _
  simpa only [fourierCoeff, neg_zero, fourier_zero, ContinuousMap.one_apply, one_smul,
    zero_add, one_div_one] using fourierCoeff_eq_intervalIntegral f 0 0

theorem horizontalMeanTorus_eq_iterated_circle (field : C(SpatialTorus, ℂ))
    (z : UnitAddCircle) :
    horizontalMeanTorus field z =
      ∫ x : UnitAddCircle, ∫ y : UnitAddCircle, field (joinAxialTorus z ![x, y]) := by
  let integrand : C(UnitAddCircle × UnitAddCircle, ℂ) :=
    ⟨fun q ↦ field (joinAxialTorus z ![q.1, q.2]), by
      apply field.continuous.comp
      rw [continuous_pi_iff]
      intro i
      fin_cases i <;> simp [joinAxialTorus] <;> fun_prop⟩
  have hchange : (∫ h : SpatialTorusTail, field (joinAxialTorus z h)) =
      ∫ q : UnitAddCircle × UnitAddCircle, integrand q := by
    have h := (volume_preserving_finTwoArrow UnitAddCircle).integral_comp' integrand
    have hvec (q : SpatialTorusTail) : ![q 0, q 1] = q := by
      ext i
      fin_cases i <;> rfl
    simpa [integrand, MeasurableEquiv.finTwoArrow, hvec] using h
  rw [horizontalMeanTorus_apply, hchange]
  exact integral_prod integrand (continuousMap_integrable_on_compact integrand)

theorem horizontalMeanTorus_eq_iterated_interval (field : C(SpatialTorus, ℂ)) (z : ℝ) :
    horizontalMeanTorus field (z : UnitAddCircle) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        field (joinAxialTorus (z : UnitAddCircle) ![(x : UnitAddCircle), (y : UnitAddCircle)]) := by
  rw [horizontalMeanTorus_eq_iterated_circle, unitCircle_integral_eq_interval]
  apply intervalIntegral.integral_congr
  intro x _
  exact unitCircle_integral_eq_interval _

theorem euclideanToSpatialTorus_assemble (x y z : ℝ) :
    euclideanToSpatialTorus (assemble x y z) =
      joinAxialTorus (z : UnitAddCircle) ![(x : UnitAddCircle), (y : UnitAddCircle)] := by
  ext i
  fin_cases i <;> simp [euclideanToSpatialTorus, piToSpatialTorus, assemble, joinAxialTorus]

theorem horizontalMeanTorus_periodicTorusLift
    (f : Space → ℝ) (hf : Continuous f) (hp : IsOnePeriodic f) (z : ℝ) :
    horizontalMeanTorus (periodicTorusLift (complexScalarField f)
      (continuous_complexScalarField hf) (isOnePeriodic_complexScalarField hp))
      (z : UnitAddCircle) = (horizontalMean f z : ℂ) := by
  rw [horizontalMeanTorus_eq_iterated_interval]
  have hpoint (x y : ℝ) :
      periodicTorusLift (complexScalarField f)
        (continuous_complexScalarField hf) (isOnePeriodic_complexScalarField hp)
        (joinAxialTorus (z : UnitAddCircle) ![(x : UnitAddCircle), (y : UnitAddCircle)]) =
      (f (assemble x y z) : ℂ) := by
    rw [← euclideanToSpatialTorus_assemble, periodicTorusLift_projection]
    rfl
  simp_rw [hpoint, intervalIntegral.integral_ofReal]
  rfl

/-- Vanishing of the complete nonconstant axial Fourier population returns the actual constant
horizontal mean, without assigning the pressure gauge. -/
theorem horizontalMean_eq_of_axial_modes_zero
    (f : Space → ℝ) (hf : Continuous f) (hp : IsOnePeriodic f)
    (hzero : ∀ n : ℤ, n ≠ 0 → scalarFourierMode f hf hp (axialFrequency n) = 0)
    (z w : ℝ) : horizontalMean f z = horizontalMean f w := by
  let field := periodicTorusLift (complexScalarField f)
    (continuous_complexScalarField hf) (isOnePeriodic_complexScalarField hp)
  have hz := horizontalMeanTorus_eq_constant field hzero (z : UnitAddCircle)
  have hw := horizontalMeanTorus_eq_constant field hzero (w : UnitAddCircle)
  have heq := hz.trans hw.symm
  dsimp only [field] at heq
  rw [horizontalMeanTorus_periodicTorusLift f hf hp z,
    horizontalMeanTorus_periodicTorusLift f hf hp w] at heq
  exact Complex.ofReal_injective heq

#print axioms horizontalMeanTorus_periodicTorusLift
#print axioms horizontalMean_eq_of_axial_modes_zero
end Soma.Holonics.Millennium.NavierStokesPeriodicHorizontalMean
