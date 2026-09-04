import ElementaryHolonics.Millennium.NavierStokesSmoothSliceWeightedAllOrders

/-!
# The coordinate word jet is the iterated derivative applied to basis vectors

The all-orders owner iterates first-order directional derivatives along a word of coordinates.
For a smooth field this is the iterated Fréchet derivative evaluated on the corresponding basis
vectors, and is therefore bounded by the operator norm of the iterated derivative.
-/

open Set Filter Topology
open scoped ContDiff
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedAllOrders

namespace Soma.Holonics.Millennium.NavierStokesWordJetIsIteratedDerivative

theorem spatialCoordinateWordJet_eq_iteratedFDeriv (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) :
    ∀ (n : ℕ) (word : Fin n → Fin 3) (x : Space),
      spatialCoordinateWordJet u n word x =
        iteratedFDeriv ℝ n u x (fun i => spatialBasisVector (word i))
  | 0, _word, x => by simp [spatialCoordinateWordJet]
  | n + 1, word, x => by
      have ih : spatialCoordinateWordJet u n (Fin.tail word) =
          fun y => iteratedFDeriv ℝ n u y (fun i => spatialBasisVector (Fin.tail word i)) :=
        funext fun y => spatialCoordinateWordJet_eq_iteratedFDeriv u hu n (Fin.tail word) y
      show spatialDirectionalJet (spatialCoordinateWordJet u n (Fin.tail word)) (word 0) x = _
      rw [spatialDirectionalJet, ih, iteratedFDeriv_succ_apply_left]
      have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n u) x :=
        (hu.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)) x
      have hcomp := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Space) Space
        (fun i => spatialBasisVector (Fin.tail word i))).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
      rw [show (fun y => iteratedFDeriv ℝ n u y (fun i => spatialBasisVector (Fin.tail word i))) =
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Space) Space
          (fun i => spatialBasisVector (Fin.tail word i))) ∘ iteratedFDeriv ℝ n u from rfl, hcomp]
      rfl

/-- The basis vectors have norm one. -/
theorem norm_spatialBasisVector (i : Fin 3) : ‖spatialBasisVector i‖ = 1 := by
  unfold spatialBasisVector
  simp

/-- The word jet is bounded by the operator norm of the iterated derivative. -/
theorem norm_spatialCoordinateWordJet_le (u : InitialVelocity) (hu : ContDiff ℝ ∞ u)
    (n : ℕ) (word : Fin n → Fin 3) (x : Space) :
    ‖spatialCoordinateWordJet u n word x‖ ≤ ‖iteratedFDeriv ℝ n u x‖ := by
  rw [spatialCoordinateWordJet_eq_iteratedFDeriv u hu n word x]
  calc ‖iteratedFDeriv ℝ n u x (fun i => spatialBasisVector (word i))‖
      ≤ ‖iteratedFDeriv ℝ n u x‖ * ∏ i, ‖spatialBasisVector (word i)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ n u x‖ := by simp [norm_spatialBasisVector]

end Soma.Holonics.Millennium.NavierStokesWordJetIsIteratedDerivative
