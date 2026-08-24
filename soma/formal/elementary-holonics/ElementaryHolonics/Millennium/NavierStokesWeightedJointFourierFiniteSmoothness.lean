import ElementaryHolonics.Millennium.NavierStokesWeightedJointFourierSmoothnessBridge

/-!
# Finite joint smoothness of parameterized weighted Fourier reconstruction

**[proved-derived]** This owner aggregates the exact bounded operator-valued Fourier derivative
population, identifies it with the adjacent native Sobolev derivative family, and recovers finite
joint differentiability from a time-smooth native path.  Choosing the matching coherent lift for
each finite receiver then returns joint `C∞` regularity of the actual reconstructed velocity on
the half-open restart slab.
-/

noncomputable section

open Function Set Filter
open scoped BigOperators ComplexConjugate ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedJointFourierFiniteSmoothness

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedJointFourierSmoothnessBridge
open Soma.Holonics.Millennium.NavierStokesWeightedJointSmoothnessScale
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedMildSpacetimeMomentum
open Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Complete first derivative of the evaluation operator -/

/-- A named carrier keeps the nested operator topology explicit during derivative aggregation. -/
abbrev HighOrderEvaluationOperator (order : ℕ) :=
  PeriodicVectorWeightedSobolev order →L[ℝ] ℂ

/-- The spatial derivative of a high-order evaluation operator. -/
abbrev HighOrderEvaluationDerivative (order : ℕ) :=
  Space →L[ℝ] HighOrderEvaluationOperator order

/-- The exact derivative modes form a summable population in the nested operator norm. -/
theorem summable_highOrderFourierEvaluationModeFDeriv
    {order : ℕ} (horder : 7 ≤ order) (component : Fin 3) (x : Space) :
    Summable (fun k : SpatialFrequency ↦
      highOrderFourierEvaluationModeFDeriv order component k x) := by
  letI : CompleteSpace (HighOrderEvaluationOperator order) :=
    ContinuousLinearMap.instCompleteSpace
  letI : CompleteSpace (HighOrderEvaluationDerivative order) :=
    ContinuousLinearMap.instCompleteSpace
  refine @Summable.of_norm_bounded SpatialFrequency
    (HighOrderEvaluationDerivative order) inferInstance inferInstance
    (fun k ↦ highOrderFourierEvaluationModeFDeriv order component k x)
    (fun k ↦ 3 * (periodicSobolevWeight 3 k)⁻¹)
    (summable_periodicSobolevWeight_three_inv.mul_left 3) ?_
  intro k
  show ‖highOrderFourierEvaluationModeFDeriv order component k x‖ ≤
    3 * (periodicSobolevWeight 3 k)⁻¹
  exact norm_highOrderFourierEvaluationModeFDeriv_le
    (order := order) horder component k x

/-- The complete spatial derivative operator obtained from the exact differentiated Fourier
population. -/
def reconstructedHighOrderComplexEvaluationFDeriv
    (r : ℕ) (component : Fin 3) (x : Space) :
    Space →L[ℝ] HighOrderEvaluationOperator (r + 6) :=
  ∑' k : SpatialFrequency,
    highOrderFourierEvaluationModeFDeriv (r + 6) component k x

/-- One adjacent native order closes the derivative of the complete operator-valued Fourier
evaluation field. -/
theorem hasFDerivAt_reconstructedHighOrderComplexEvaluationCLM
    {r : ℕ} (hr : 1 ≤ r) (component : Fin 3) (x : Space) :
    HasFDerivAt
      (reconstructedHighOrderComplexEvaluationCLM r component)
      (reconstructedHighOrderComplexEvaluationFDeriv r component x) x := by
  have h := hasFDerivAt_tsum
    (u := fun k : SpatialFrequency ↦
      3 * (periodicSobolevWeight 3 k)⁻¹)
    (f := fun k : SpatialFrequency ↦
      highOrderFourierEvaluationModeCLM (r + 6) component k)
    (f' := fun k : SpatialFrequency ↦
      highOrderFourierEvaluationModeFDeriv (r + 6) component k)
    (x₀ := x)
    (summable_periodicSobolevWeight_three_inv.mul_left 3)
    (fun k y ↦
      hasFDerivAt_highOrderFourierEvaluationModeCLM
        (r + 6) component k y)
    (fun k y ↦
      norm_highOrderFourierEvaluationModeFDeriv_le
        (order := r + 6) (by omega : 7 ≤ r + 6) component k y)
    (summable_highOrderFourierEvaluationModeCLM
      (by omega : 6 ≤ r + 6) component x)
    x
  simpa only [reconstructedHighOrderComplexEvaluationCLM,
    reconstructedHighOrderComplexEvaluationFDeriv] using h

/-! ## Adjacent-order form of the complete derivative -/

/-- One native spatial derivative, with arithmetic normalized to the parameterized reconstruction
scale. -/
def highOrderAdjacentDerivativeCLM
    (r : ℕ) (coordinate : Fin 3) :
    PeriodicVectorWeightedSobolev (r + 7) →L[ℝ]
      PeriodicVectorWeightedSobolev (r + 6) :=
  (periodicVectorWeightedSobolevDerivativeSuccThreeCLM
    (r + 3) coordinate).restrictScalars ℝ

/-- Evaluate after taking one addressed adjacent native derivative. -/
def highOrderCoordinateDerivativeEvaluationCLM
    (r : ℕ) (component coordinate : Fin 3) (x : Space) :
    HighOrderEvaluationOperator (r + 7) :=
  (reconstructedHighOrderComplexEvaluationCLM r component x).comp
    (highOrderAdjacentDerivativeCLM r coordinate)

/-- The finite-coordinate form of the derivative of the order-`r+1` evaluation field. -/
def adjacentReconstructedHighOrderComplexEvaluationFDeriv
    (r : ℕ) (component : Fin 3) (x : Space) :
    Space →L[ℝ] HighOrderEvaluationOperator (r + 7) :=
  ∑ coordinate : Fin 3,
    (EuclideanSpace.proj coordinate).smulRight
      (highOrderCoordinateDerivativeEvaluationCLM
        r component coordinate x)

/-- On a coordinate basis direction, the summed derivative is exactly evaluation after the
corresponding adjacent native Sobolev derivative. -/
theorem reconstructedHighOrderComplexEvaluationFDeriv_apply_single
    (r : ℕ) (component coordinate : Fin 3) (x : Space) :
    reconstructedHighOrderComplexEvaluationFDeriv (r + 1) component x
        (EuclideanSpace.single coordinate 1) =
      highOrderCoordinateDerivativeEvaluationCLM
        r component coordinate x := by
  rw [reconstructedHighOrderComplexEvaluationFDeriv]
  rw [show
      (∑' k : SpatialFrequency,
        highOrderFourierEvaluationModeFDeriv (r + 1 + 6) component k x)
          (EuclideanSpace.single coordinate 1) =
        ∑' k : SpatialFrequency,
          highOrderFourierEvaluationModeFDeriv
            (r + 1 + 6) component k x
              (EuclideanSpace.single coordinate 1) by
      exact (ContinuousLinearMap.apply ℝ
        (HighOrderEvaluationOperator (r + 1 + 6))
        (EuclideanSpace.single coordinate 1)).map_tsum
          (summable_highOrderFourierEvaluationModeFDeriv
            (by omega : 7 ≤ r + 1 + 6) component x)]
  rw [highOrderCoordinateDerivativeEvaluationCLM,
    reconstructedHighOrderComplexEvaluationCLM]
  rw [show
      (∑' k : SpatialFrequency,
        highOrderFourierEvaluationModeCLM (r + 6) component k x).comp
          (highOrderAdjacentDerivativeCLM r coordinate) =
        ∑' k : SpatialFrequency,
          (highOrderFourierEvaluationModeCLM
            (r + 6) component k x).comp
              (highOrderAdjacentDerivativeCLM r coordinate) by
      exact ((ContinuousLinearMap.compL ℝ
        (PeriodicVectorWeightedSobolev (r + 7))
        (PeriodicVectorWeightedSobolev (r + 6)) ℂ).flip
          (highOrderAdjacentDerivativeCLM r coordinate)).map_tsum
          (summable_highOrderFourierEvaluationModeCLM
            (by omega : 6 ≤ r + 6) component x)]
  apply tsum_congr
  intro k
  apply ContinuousLinearMap.ext
  intro state
  change euclideanFourierCharacterFDeriv k x
      (EuclideanSpace.single coordinate 1) *
        (weightedSobolevCoefficients (r + 1 + 6)
          (state component)).1 k =
    euclideanFourierCharacter k x *
      (weightedSobolevCoefficients (r + 6)
        (periodicVectorWeightedSobolevDerivativeSuccThreeCLM
          (r + 3) coordinate state component)).1 k
  rw [euclideanFourierCharacterFDeriv_apply_single,
    weightedSobolevCoefficients_periodicVectorWeightedSobolevDerivativeSuccThreeCLM_apply]
  simp only [coordinateFourierMultiplier]
  ring

/-- The complete summed derivative is the finite coordinate family of lower-order evaluations
composed with the existing native adjacent derivative maps. -/
theorem reconstructedHighOrderComplexEvaluationFDeriv_eq_adjacent
    (r : ℕ) (component : Fin 3) (x : Space) :
    reconstructedHighOrderComplexEvaluationFDeriv (r + 1) component x =
      adjacentReconstructedHighOrderComplexEvaluationFDeriv
        r component x := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hbasis (coordinate : Fin 3) :
      reconstructedHighOrderComplexEvaluationFDeriv (r + 1) component x
          (b coordinate) =
        adjacentReconstructedHighOrderComplexEvaluationFDeriv
          r component x (b coordinate) := by
    dsimp [b]
    rw [EuclideanSpace.basisFun_apply]
    rw [reconstructedHighOrderComplexEvaluationFDeriv_apply_single]
    simp only [adjacentReconstructedHighOrderComplexEvaluationFDeriv,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      PiLp.proj_apply]
    rw [Finset.sum_eq_single coordinate]
    · simp
    · intro other _ hother
      simp [hother]
    · simp
  apply ContinuousLinearMap.ext
  intro direction
  rw [← b.sum_repr direction]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [hbasis coordinate]

/-- Finite coordinate aggregation preserves every finite smoothness order carried by the
lower-order evaluation field. -/
theorem contDiff_adjacentReconstructedHighOrderComplexEvaluationFDeriv
    {n : ℕ∞} (r : ℕ) (component : Fin 3)
    (h : ContDiff ℝ n
      (reconstructedHighOrderComplexEvaluationCLM r component)) :
    ContDiff ℝ n
      (adjacentReconstructedHighOrderComplexEvaluationFDeriv
        r component) := by
  unfold adjacentReconstructedHighOrderComplexEvaluationFDeriv
  apply ContDiff.sum
  intro coordinate _
  apply contDiff_const.smulRight
  unfold highOrderCoordinateDerivativeEvaluationCLM
  exact h.clm_comp contDiff_const

/-! ## Finite-order operator-valued smoothness -/

/-- Retaining `r` adjacent native orders above the absolute-summation aperture makes the complete
parameterized Fourier evaluation operator `C^n` for every `n ≤ r`. -/
theorem contDiff_reconstructedHighOrderComplexEvaluationCLM
    (n r : ℕ) (hn : n ≤ r) (component : Fin 3) :
    ContDiff ℝ n
      (reconstructedHighOrderComplexEvaluationCLM r component) := by
  induction n generalizing r with
  | zero =>
      exact contDiff_zero.mpr
        (continuous_reconstructedHighOrderComplexEvaluationCLM r component)
  | succ n ih =>
      cases r with
      | zero => omega
      | succ r =>
          apply contDiff_succ_iff_hasFDerivAt.mpr
          refine ⟨adjacentReconstructedHighOrderComplexEvaluationFDeriv
            r component, ?_, ?_⟩
          · exact contDiff_adjacentReconstructedHighOrderComplexEvaluationFDeriv
              r component (ih r (by omega))
          · intro x
            have h := hasFDerivAt_reconstructedHighOrderComplexEvaluationCLM
              (r := r + 1) (by omega) component x
            rw [reconstructedHighOrderComplexEvaluationFDeriv_eq_adjacent] at h
            exact h

/-! ## Joint finite-order reconstruction -/

/-- A `C^r` path in native order `r+6`, evaluated through the exact parameterized Fourier
operator, reconstructs a jointly `C^r` complex component on the corresponding spacetime set. -/
theorem contDiffOn_joint_reconstructedHighOrderComplexComponent
    {s : Set ℝ} (r : ℕ) (component : Fin 3)
    (path : ℝ → PeriodicVectorWeightedSobolev (r + 6))
    (hpath : ContDiffOn ℝ r path s) :
    ContDiffOn ℝ r
      (fun z : Space × ℝ ↦
        reconstructedHigherOrderComplexComponent
          (r + 3) (path z.2) component z.1)
      (Set.univ ×ˢ s) := by
  have hevaluation : ContDiffOn ℝ r
      (fun z : Space × ℝ ↦
        reconstructedHighOrderComplexEvaluationCLM r component z.1)
      (Set.univ ×ˢ s) :=
    ((contDiff_reconstructedHighOrderComplexEvaluationCLM
      r r le_rfl component).comp contDiff_fst).contDiffOn
  have hstate : ContDiffOn ℝ r
      (fun z : Space × ℝ ↦ path z.2) (Set.univ ×ˢ s) :=
    hpath.comp contDiffOn_snd (prod_subset_preimage_snd _ _)
  simpa only [reconstructedHighOrderComplexEvaluationCLM_apply] using
    hevaluation.clm_apply hstate

/-- The real three-coordinate receiver of the same native path is jointly `C^r`, with no change
of coefficient lineage. -/
theorem contDiffOn_joint_reconstructedHigherOrderVelocity
    {s : Set ℝ} (r : ℕ)
    (path : ℝ → PeriodicVectorWeightedSobolev (r + 6))
    (hpath : ContDiffOn ℝ r path s) :
    ContDiffOn ℝ r
      (fun z : Space × ℝ ↦
        reconstructedHigherOrderVelocity (r + 3) (path z.2) z.1)
      (Set.univ ×ˢ s) := by
  rw [contDiffOn_piLp]
  intro component
  simpa only [reconstructedHigherOrderVelocity,
    vectorOfCoordinates_apply] using
      Complex.reCLM.contDiff.comp_contDiffOn
        (contDiffOn_joint_reconstructedHighOrderComplexComponent
          r component path hpath)

/-! ## The coherent mild-tower velocity -/

/-- Every finite joint receiver of the actual weighted reconstructed velocity is supplied by the
corresponding high native lift, its all-order time smoothness, and its exact restriction back to
the common base path. -/
theorem contDiffOn_joint_weightedReconstructedVelocity_order
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) (r : ℕ) :
    ContDiffOn ℝ r
      (fun z : Space × ℝ ↦
        weightedReconstructedVelocity hT base z.2 z.1)
      (openSpaceTimeSlab T) := by
  have hhigh := contDiffOn_joint_reconstructedHigherOrderVelocity r
    (fun t : ℝ ↦ smoothTowerLiftExtension hT tower (r + 3) t)
    (contDiffOn_smoothTowerLiftExtension_Ico_allFiniteOrders
      hT tower nu hnu initial hfixed hreal r (r + 3))
  rw [openSpaceTimeSlab, openTimeSlab]
  apply hhigh.congr
  rintro z hz
  have htIcc : z.2 ∈ Icc (0 : ℝ) T := ⟨hz.2.1, hz.2.2.le⟩
  have hlift :
      smoothTowerLiftExtension hT tower (r + 3) z.2 =
        tower.lift (r + 3) ⟨z.2, htIcc⟩ := by
    change tower.lift (r + 3) (Set.projIcc 0 T hT z.2) = _
    congr 1
    apply Subtype.ext
    simp [Set.projIcc, htIcc.1, htIcc.2]
  rw [reconstructedHigherOrderVelocity_eq_reconstructedVelocity_restrict]
  change weightedReconstructedVelocity hT base z.2 z.1 =
    reconstructedVelocity
      (periodicVectorWeightedSobolevRestrictCLM
        3 (r + 3 + 3) (by omega)
          (smoothTowerLiftExtension hT tower (r + 3) z.2)) z.1
  rw [hlift, tower.restrict_lift]
  unfold weightedReconstructedVelocity
  rw [weightedPathExtension_of_mem hT base htIcc]

/-- The actual weighted reconstructed velocity is jointly `C∞` on the half-open restart slab.
Every finite receiver chooses its matching coherent native lift; the returned field is always the
same base reconstruction by exact order restriction. -/
theorem contDiffOn_infty_joint_weightedReconstructedVelocity
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) :
    ContDiffOn ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
      (fun z : Space × ℝ ↦
        weightedReconstructedVelocity hT base z.2 z.1)
      (openSpaceTimeSlab T) := by
  rw [contDiffOn_infty]
  intro r
  exact contDiffOn_joint_weightedReconstructedVelocity_order
    hT tower nu hnu initial hfixed hreal r

end Soma.Holonics.Millennium.NavierStokesWeightedJointFourierFiniteSmoothness
