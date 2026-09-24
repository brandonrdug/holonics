import ElementaryHolonics.Millennium.NavierStokesSharpHeatDerivativeReconstruction
import ElementaryHolonics.Millennium.NavierStokesWeightedLerayBilinear

/-!
# The nonlinear source for the sharp second-derivative heat edge

**[proved-derived]** The existing complete-lattice Leray owner returns
`P div (u tensor u)` in native weighted `H2` from native weighted `H3` velocity data.  This module
retains that exact coefficient population and connects its quadratic norm receipt to the sharp
`tau^(-3/4)` reconstructed second-derivative heat kernel.  It assumes neither a mild equation nor
terminal control.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource

open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesSharpHeatDerivative
open Soma.Holonics.Millennium.NavierStokesSharpHeatDerivativeReconstruction
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- Exact native nonlinear Navier--Stokes source `P div (u tensor u)`. -/
def sharpNonlinearSource (u : PeriodicVectorWeightedSobolev 3) :
    PeriodicVectorWeightedSobolev 2 :=
  weightedLerayDivergenceConvolution u u

/-- The source retains the existing exact complete-lattice Leray/divergence coefficient law. -/
theorem sharpNonlinearSource_coefficient
    (u : PeriodicVectorWeightedSobolev 3) (output : Fin 3)
    (k : SpatialFrequency) :
    sharpNonlinearSource u output k =
      (Real.sqrt (periodicSobolevWeight 2 k) : ℂ) *
        lerayProjectMode k
          (fun component ↦
            (h3DivergenceConvolution
              (unweightedVectorThree u) (unweightedVectorThree u) component).1 k) output := by
  exact weightedLerayDivergenceConvolution_coefficient u u output k

/-- Strongest standing native bound: the nonlinear source lies in weighted `H2`, quadratically
controlled by the weighted `H3` velocity norm. -/
theorem norm_sharpNonlinearSource_le
    (u : PeriodicVectorWeightedSobolev 3) :
    ‖sharpNonlinearSource u‖ ≤
      (23328 * periodicH3EmbeddingConstant) * ‖u‖ ^ 2 := by
  simpa [sharpNonlinearSource, pow_two, mul_assoc] using
    norm_weightedLerayDivergenceConvolution_le u u

/-- Every component of the exact source has the same quadratic `H2` control. -/
theorem norm_sharpNonlinearSource_component_le
    (u : PeriodicVectorWeightedSobolev 3) (component : Fin 3) :
    ‖sharpNonlinearSource u component‖ ≤
      (23328 * periodicH3EmbeddingConstant) * ‖u‖ ^ 2 :=
  (norm_le_pi_norm (sharpNonlinearSource u) component).trans
    (norm_sharpNonlinearSource_le u)

/-- The sharp reconstructed D2 heat receiver of the exact nonlinear source.  This is the
coefficient-level Duhamel integrand at elapsed time `dt`. -/
theorem norm_reconstructedSharpNonlinearSourceSecondDerivativeChart_le
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (hlocal : 2 * ((nu : ℝ) * (dt : ℝ)) ≤ 1)
    (u : PeriodicVectorWeightedSobolev 3)
    (component first second : Fin 3) :
    ‖reconstructedHeatH2SecondDerivativeChart nu dt h (sharpNonlinearSource u)
        component first second‖ ≤
      sharpHeatSecondDerivativeH2Constant *
        (2 * ((nu : ℝ) * (dt : ℝ))) ^ (-3 / 4 : ℝ) *
          ((23328 * periodicH3EmbeddingConstant) * ‖u‖ ^ 2) := by
  have hbase := norm_reconstructedHeatH2SecondDerivativeChart_sharp
    nu dt h hlocal (sharpNonlinearSource u) component first second
  have hfactor : 0 ≤ sharpHeatSecondDerivativeH2Constant *
      (2 * ((nu : ℝ) * (dt : ℝ))) ^ (-3 / 4 : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by positivity) _)
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (norm_sharpNonlinearSource_component_le u component) hfactor)

/-- For fixed positive viscosity and fixed weighted `H3` velocity, the quadratic nonlinear
majorant paired with the sharp D2 heat kernel is locally time-integrable. -/
theorem integrableOn_sharpNonlinearDuhamelMajorant
    (nu T : ℝ) (hnu : 0 < nu) (hT : 0 < T)
    (u : PeriodicVectorWeightedSobolev 3) :
    IntegrableOn (fun dt : ℝ ↦
      sharpHeatSecondDerivativeH2Constant * (2 * (nu * dt)) ^ (-3 / 4 : ℝ) *
        ((23328 * periodicH3EmbeddingConstant) * ‖u‖ ^ 2)) (Set.Ioo 0 T) := by
  have hbase : IntegrableOn (fun dt : ℝ ↦ dt ^ (-3 / 4 : ℝ)) (Set.Ioo 0 T) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hT).2 (by norm_num)
  let C := sharpHeatSecondDerivativeH2Constant * (2 * nu) ^ (-3 / 4 : ℝ) *
    ((23328 * periodicH3EmbeddingConstant) * ‖u‖ ^ 2)
  have hscaled := hbase.const_mul C
  refine IntegrableOn.congr_fun hscaled ?_ measurableSet_Ioo
  intro dt hdt
  dsimp [C]
  rw [show 2 * (nu * dt) = (2 * nu) * dt by ring,
    Real.mul_rpow (by positivity) hdt.1.le]
  ring

#print axioms sharpNonlinearSource_coefficient
#print axioms norm_sharpNonlinearSource_le
#print axioms norm_reconstructedSharpNonlinearSourceSecondDerivativeChart_le
#print axioms integrableOn_sharpNonlinearDuhamelMajorant

end Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
