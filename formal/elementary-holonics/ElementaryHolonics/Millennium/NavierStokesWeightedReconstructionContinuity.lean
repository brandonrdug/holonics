import ElementaryHolonics.Millennium.NavierStokesWeightedFourierReconstruction
import ElementaryHolonics.Millennium.NavierStokesWeightedLerayBilinear

/-!
# Continuous transport from the native H³ carrier to its reconstructed field

**[proved-derived]** The full inverse-Fourier return is a bounded complex-linear passage from the
native weighted `H³` population to the uniform continuous complex field on the genuine torus.
Consequently a continuous native time path reconstructs to a jointly continuous spacetime field;
the inverse transform is not merely a pointwise choice at each time face.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedReconstructionContinuity

open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- The exact fixed Cauchy--Schwarz factor used by the native `H³ -> C⁰` passage. -/
def periodicH3UniformEmbeddingConstant : ℝ :=
  periodicH3EmbeddingConstant

theorem periodicH3UniformEmbeddingConstant_nonneg :
    0 ≤ periodicH3UniformEmbeddingConstant :=
  norm_nonneg _

@[simp]
theorem nativeUnweightedComponent_add
    (left right : PeriodicVectorWeightedSobolev 3) (component : Fin 3)
    (k : SpatialFrequency) :
    nativeUnweightedComponent (left + right) component k =
      nativeUnweightedComponent left component k +
        nativeUnweightedComponent right component k := by
  simp [nativeUnweightedComponent, weightedSobolevCoefficients,
    weightedSobolevRawCoefficients, mul_add]

@[simp]
theorem nativeUnweightedComponent_smul
    (scalar : ℂ) (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3)
    (k : SpatialFrequency) :
    nativeUnweightedComponent (scalar • state) component k =
      scalar * nativeUnweightedComponent state component k := by
  simp [nativeUnweightedComponent, weightedSobolevCoefficients,
    weightedSobolevRawCoefficients]
  ring

/-- Quantitative complete-lattice `H³ -> ℓ1` estimate for one component. -/
theorem tsum_norm_nativeUnweightedComponent_le
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) :
    ∑' k, ‖nativeUnweightedComponent state component k‖ ≤
      periodicH3UniformEmbeddingConstant * ‖state component‖ := by
  have hbound :=
    coefficientL1Mass_le_periodicH3EmbeddingConstant_mul
      (weightedSobolevCoefficients 3 (state component))
  rw [periodicH3CoefficientNorm_eq_nativeNorm,
    coefficientWeightedRealization_weightedSobolevCoefficients] at hbound
  exact hbound

/-- Uniform reconstruction of one component is bounded by the native component norm. -/
theorem norm_reconstructedTorusComplexComponent_le
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) :
    ‖reconstructedTorusComplexComponent state component‖ ≤
      periodicH3UniformEmbeddingConstant * ‖state component‖ := by
  have hnormPassages : Summable fun k : SpatialFrequency ↦
      ‖nativeUnweightedComponent state component k •
        UnitAddTorus.mFourier k‖ := by
    simpa only [norm_smul, UnitAddTorus.mFourier_norm, mul_one] using
      summable_norm_nativeUnweightedComponent state component
  calc
    ‖reconstructedTorusComplexComponent state component‖ ≤
        ∑' k, ‖nativeUnweightedComponent state component k •
          UnitAddTorus.mFourier k‖ := by
      exact norm_tsum_le_tsum_norm hnormPassages
    _ = ∑' k, ‖nativeUnweightedComponent state component k‖ := by
      apply tsum_congr
      intro k
      simp only [norm_smul, UnitAddTorus.mFourier_norm, mul_one]
    _ ≤ periodicH3UniformEmbeddingConstant * ‖state component‖ :=
      tsum_norm_nativeUnweightedComponent_le state component

/-- The one-component reconstruction is additive. -/
theorem reconstructedTorusComplexComponent_add
    (left right : PeriodicVectorWeightedSobolev 3) (component : Fin 3) :
    reconstructedTorusComplexComponent (left + right) component =
      reconstructedTorusComplexComponent left component +
        reconstructedTorusComplexComponent right component := by
  rw [reconstructedTorusComplexComponent,
    reconstructedTorusComplexComponent, reconstructedTorusComplexComponent]
  rw [← (summable_nativeFourierPassages left component).tsum_add
    (summable_nativeFourierPassages right component)]
  apply tsum_congr
  intro k
  rw [nativeUnweightedComponent_add]
  ext q
  change
    (nativeUnweightedComponent left component k +
        nativeUnweightedComponent right component k) *
      UnitAddTorus.mFourier k q =
    nativeUnweightedComponent left component k * UnitAddTorus.mFourier k q +
      nativeUnweightedComponent right component k * UnitAddTorus.mFourier k q
  ring

/-- The one-component reconstruction respects complex scalar transport. -/
theorem reconstructedTorusComplexComponent_smul
    (scalar : ℂ) (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) :
    reconstructedTorusComplexComponent (scalar • state) component =
      scalar • reconstructedTorusComplexComponent state component := by
  rw [reconstructedTorusComplexComponent,
    reconstructedTorusComplexComponent,
    ← (summable_nativeFourierPassages state component).tsum_const_smul scalar]
  apply tsum_congr
  intro k
  rw [nativeUnweightedComponent_smul, mul_smul]

/-- The genuine full-lattice inverse transform as a bounded complex-linear receiver. -/
def reconstructedTorusComplexComponentCLM (component : Fin 3) :
    PeriodicVectorWeightedSobolev 3 →L[ℂ]
      C(Soma.Holonics.Millennium.NavierStokesTorusVorticity.SpatialTorus, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun state ↦ reconstructedTorusComplexComponent state component
      map_add' := fun left right ↦
        reconstructedTorusComplexComponent_add left right component
      map_smul' := fun scalar state ↦
        reconstructedTorusComplexComponent_smul scalar state component }
    periodicH3UniformEmbeddingConstant (fun state ↦ by
      exact (norm_reconstructedTorusComplexComponent_le state component).trans
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm state component)
          periodicH3UniformEmbeddingConstant_nonneg))

@[simp]
theorem reconstructedTorusComplexComponentCLM_apply
    (component : Fin 3) (state : PeriodicVectorWeightedSobolev 3) :
    reconstructedTorusComplexComponentCLM component state =
      reconstructedTorusComplexComponent state component :=
  rfl

section Audit

#print axioms tsum_norm_nativeUnweightedComponent_le
#print axioms norm_reconstructedTorusComplexComponent_le
#print axioms reconstructedTorusComplexComponentCLM

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedReconstructionContinuity
