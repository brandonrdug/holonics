import ElementaryHolonics.Millennium.NavierStokesCoordinateH3Production

/-!
# The direct and middle faces in the coordinate H³ production population

The exact order-three owner leaves seven lower Leibniz faces after periodic top transport is
removed.  Four are `D³-D¹-D³` or `D¹-D³-D³` faces and are controlled directly by the cube
supremum of the velocity Jacobian.  The other three are the genuine `D²-D²-D³` hexagonal
boundary population.  This owner separates those populations and proves the direct estimate.

The final interpolation of the middle population is not assumed here.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Set
open scoped BigOperators Laplacian

namespace Soma.Holonics.Millennium.NavierStokesCoordinateH3Estimate

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH2Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH3Production

/-! ## An actual cube `L∞` Jacobian receiver -/

/-- The genuine supremum of the spatial Jacobian operator norm over the periodic cube. -/
def cubeGradientSup (u : InitialVelocity) : ℝ :=
  sSup ((fun x ↦ ‖fderiv ℝ u x‖) '' unitCube)

theorem norm_fderiv_le_cubeGradientSup
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (x : Space) (hx : x ∈ unitCube) :
    ‖fderiv ℝ u x‖ ≤ cubeGradientSup u := by
  unfold cubeGradientSup
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hderiv : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hcontinuous : Continuous (fun y ↦ ‖fderiv ℝ u y‖) :=
    hderiv.continuous.norm
  have hbdd : BddAbove ((fun y ↦ ‖fderiv ℝ u y‖) '' unitCube) :=
    hcubeCompact.bddAbove_image hcontinuous.continuousOn
  exact le_csSup hbdd ⟨x, hx, rfl⟩

theorem cubeGradientSup_nonneg
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) :
    0 ≤ cubeGradientSup u := by
  exact (norm_nonneg (fderiv ℝ u 0)).trans
    (norm_fderiv_le_cubeGradientSup u hu 0 (by
      unfold unitCube
      change (0 : Fin 3 → ℝ) ∈ Icc 0 (fun _ ↦ 1)
      exact ⟨le_rfl, fun _ ↦ zero_le_one⟩))

/-- A linear action is bounded by the sum of its coordinate faces whenever every coordinate of
the acting vector has the same scalar bound. -/
theorem norm_clm_apply_le_bound_mul_sum_coordinate
    (L : Space →L[ℝ] Space) (v : Space) (M : ℝ)
    (hv : ∀ coordinate : Fin 3, |v coordinate| ≤ M) :
    ‖L v‖ ≤ M * ∑ coordinate : Fin 3, ‖L (spatialBasisVector coordinate)‖ := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hrepr : ∑ coordinate : Fin 3, (v coordinate) • b coordinate = v := by
    simpa [b, EuclideanSpace.basisFun_repr] using b.sum_repr v
  rw [← hrepr, map_sum]
  calc
    ‖∑ coordinate : Fin 3, L ((v coordinate) • b coordinate)‖ ≤
        ∑ coordinate : Fin 3, ‖L ((v coordinate) • b coordinate)‖ :=
      norm_sum_le _ _
    _ = ∑ coordinate : Fin 3, |v coordinate| * ‖L (b coordinate)‖ := by
      apply Finset.sum_congr rfl
      intro coordinate _hcoordinate
      rw [map_smul, norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ coordinate : Fin 3, M * ‖L (b coordinate)‖ := by
      apply Finset.sum_le_sum
      intro coordinate _hcoordinate
      exact mul_le_mul_of_nonneg_right (hv coordinate) (norm_nonneg _)
    _ = M * ∑ coordinate : Fin 3, ‖L (spatialBasisVector coordinate)‖ := by
      rw [Finset.mul_sum]
      rfl

theorem abs_spatialDirectionalJet_component_le_cubeGradientSup
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u)
    (x : Space) (hx : x ∈ unitCube) (direction component : Fin 3) :
    |spatialDirectionalJet u direction x component| ≤ cubeGradientSup u := by
  calc
    |spatialDirectionalJet u direction x component| =
        ‖spatialDirectionalJet u direction x component‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ‖spatialDirectionalJet u direction x‖ := by
      exact PiLp.norm_apply_le _ component
    _ = ‖fderiv ℝ u x (spatialBasisVector direction)‖ := rfl
    _ ≤ ‖fderiv ℝ u x‖ * ‖spatialBasisVector direction‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ u x‖ := by
      simp [spatialBasisVector]
    _ ≤ cubeGradientSup u := norm_fderiv_le_cubeGradientSup u hu x hx

/-! ## Boolean separation of the seven lower faces -/

/-- The four lower faces containing a first and a third derivative. -/
def thirdCoordinateDirectCommutator
    (velocity : VelocityField) (t : ℝ) (i j k : Fin 3) (x : Space) : Space :=
  fderiv ℝ (fun y ↦ secondCoordinateJet velocity j k y t) x
      (firstCoordinateJet velocity i x t) +
    fderiv ℝ (fun y ↦ secondCoordinateJet velocity i k y t) x
      (firstCoordinateJet velocity j x t) +
    fderiv ℝ (fun y ↦ secondCoordinateJet velocity i j y t) x
      (firstCoordinateJet velocity k x t) +
    fderiv ℝ (fun y ↦ velocity y t) x
      (thirdCoordinateJet velocity i j k x t)

/-- The three `D²-D²` faces forming the middle hexagonal boundary population. -/
def thirdCoordinateMiddleCommutator
    (velocity : VelocityField) (t : ℝ) (i j k : Fin 3) (x : Space) : Space :=
  fderiv ℝ (fun y ↦ firstCoordinateJet velocity k y t) x
      (secondCoordinateJet velocity i j x t) +
    fderiv ℝ (fun y ↦ firstCoordinateJet velocity j y t) x
      (secondCoordinateJet velocity i k x t) +
    fderiv ℝ (fun y ↦ firstCoordinateJet velocity i y t) x
      (secondCoordinateJet velocity j k x t)

theorem thirdCoordinateLowerCommutator_eq_direct_add_middle
    (velocity : VelocityField) (t : ℝ) (i j k : Fin 3) (x : Space) :
    thirdCoordinateLowerCommutator velocity t i j k x =
      thirdCoordinateDirectCommutator velocity t i j k x +
        thirdCoordinateMiddleCommutator velocity t i j k x := by
  unfold thirdCoordinateLowerCommutator thirdCoordinateDirectCommutator
    thirdCoordinateMiddleCommutator
  abel

/-! ## The four directly controlled faces -/

/-- A derivative of an actual order-two jet, acting on an actual first jet, is controlled by the
cube Jacobian supremum times the three order-three coordinate faces of that derivative. -/
theorem openPeriodicSolutionOn_norm_secondJetDerivative_firstJet_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (hx : x ∈ unitCube)
    (direction a b : Fin 3) :
    ‖fderiv ℝ (fun y ↦ secondCoordinateJet velocity a b y t) x
        (firstCoordinateJet velocity direction x t)‖ ≤
      cubeGradientSup (fun y ↦ velocity y t) *
        ∑ coordinate : Fin 3,
          ‖thirdCoordinateJet velocity coordinate a b x t‖ := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let w : InitialVelocity := fun y ↦ firstCoordinateJet velocity direction y t
  let W : InitialVelocity := fun y ↦ secondCoordinateJet velocity a b y t
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hwFun : w = spatialDirectionalJet u direction := by
    funext y
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht y direction
  have hwCoordinate : ∀ coordinate : Fin 3,
      |w x coordinate| ≤ cubeGradientSup u := by
    intro coordinate
    rw [hwFun]
    exact abs_spatialDirectionalJet_component_le_cubeGradientSup
      u hu x hx direction coordinate
  have hbound := norm_clm_apply_le_bound_mul_sum_coordinate
    (fderiv ℝ W x) (w x) (cubeGradientSup u) hwCoordinate
  have hbasis : ∀ coordinate : Fin 3,
      fderiv ℝ W x (spatialBasisVector coordinate) =
        thirdCoordinateJet velocity coordinate a b x t := by
    intro coordinate
    exact (openPeriodicSolutionOn_thirdCoordinateJet_eq_spatialDerivative_secondCoordinateJet
      solution ht x coordinate a b).symm
  simp_rw [hbasis] at hbound
  exact hbound

/-- The `Du(D³u)` face is controlled directly by the same Jacobian supremum. -/
theorem openPeriodicSolutionOn_norm_velocityDerivative_thirdJet_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (hx : x ∈ unitCube)
    (i j k : Fin 3) :
    ‖fderiv ℝ (fun y ↦ velocity y t) x
        (thirdCoordinateJet velocity i j k x t)‖ ≤
      cubeGradientSup (fun y ↦ velocity y t) *
        ‖thirdCoordinateJet velocity i j k x t‖ := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let V : Space := thirdCoordinateJet velocity i j k x t
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  calc
    ‖fderiv ℝ u x V‖ ≤ ‖fderiv ℝ u x‖ * ‖V‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ cubeGradientSup u * ‖V‖ :=
      mul_le_mul_of_nonneg_right
        (norm_fderiv_le_cubeGradientSup u hu x hx) (norm_nonneg _)

/-- The complete four-face direct commutator pairing at one point.  This is the nontrivial local
estimate whose finite summation gives the `3 + 3 + 3 + 1` constant. -/
theorem openPeriodicSolutionOn_abs_inner_thirdCoordinateDirectCommutator_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (hx : x ∈ unitCube)
    (i j k : Fin 3) :
    |inner ℝ (thirdCoordinateDirectCommutator velocity t i j k x)
        (thirdCoordinateJet velocity i j k x t)| ≤
      cubeGradientSup (fun y ↦ velocity y t) *
        ((∑ coordinate : Fin 3,
            ‖thirdCoordinateJet velocity coordinate j k x t‖) +
          (∑ coordinate : Fin 3,
            ‖thirdCoordinateJet velocity coordinate i k x t‖) +
          (∑ coordinate : Fin 3,
            ‖thirdCoordinateJet velocity coordinate i j x t‖) +
          ‖thirdCoordinateJet velocity i j k x t‖) *
        ‖thirdCoordinateJet velocity i j k x t‖ := by
  let A : Space :=
    fderiv ℝ (fun y ↦ secondCoordinateJet velocity j k y t) x
      (firstCoordinateJet velocity i x t)
  let B : Space :=
    fderiv ℝ (fun y ↦ secondCoordinateJet velocity i k y t) x
      (firstCoordinateJet velocity j x t)
  let C : Space :=
    fderiv ℝ (fun y ↦ secondCoordinateJet velocity i j y t) x
      (firstCoordinateJet velocity k x t)
  let D : Space :=
    fderiv ℝ (fun y ↦ velocity y t) x
      (thirdCoordinateJet velocity i j k x t)
  let V : Space := thirdCoordinateJet velocity i j k x t
  let M : ℝ := cubeGradientSup (fun y ↦ velocity y t)
  have hA := openPeriodicSolutionOn_norm_secondJetDerivative_firstJet_le
    solution ht x hx i j k
  have hB := openPeriodicSolutionOn_norm_secondJetDerivative_firstJet_le
    solution ht x hx j i k
  have hC := openPeriodicSolutionOn_norm_secondJetDerivative_firstJet_le
    solution ht x hx k i j
  have hD := openPeriodicSolutionOn_norm_velocityDerivative_thirdJet_le
    solution ht x hx i j k
  have hnorm : ‖A + B + C + D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
    calc
      ‖A + B + C + D‖ ≤ ‖A + B + C‖ + ‖D‖ := norm_add_le _ _
      _ ≤ (‖A + B‖ + ‖C‖) + ‖D‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((‖A‖ + ‖B‖) + ‖C‖) + ‖D‖ := by
        gcongr
        exact norm_add_le _ _
  have hsum :
      ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ ≤
        M * ((∑ coordinate : Fin 3,
            ‖thirdCoordinateJet velocity coordinate j k x t‖) +
          (∑ coordinate : Fin 3,
            ‖thirdCoordinateJet velocity coordinate i k x t‖) +
          (∑ coordinate : Fin 3,
            ‖thirdCoordinateJet velocity coordinate i j x t‖) + ‖V‖) := by
    dsimp [A, B, C, D, M, V]
    calc
      _ ≤
          M * (∑ coordinate : Fin 3,
              ‖thirdCoordinateJet velocity coordinate j k x t‖) +
          M * (∑ coordinate : Fin 3,
              ‖thirdCoordinateJet velocity coordinate i k x t‖) +
          M * (∑ coordinate : Fin 3,
              ‖thirdCoordinateJet velocity coordinate i j x t‖) +
          M * ‖thirdCoordinateJet velocity i j k x t‖ := by
        gcongr
      _ = _ := by ring
  calc
    |inner ℝ (thirdCoordinateDirectCommutator velocity t i j k x) V| ≤
        ‖thirdCoordinateDirectCommutator velocity t i j k x‖ * ‖V‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖A‖ + ‖B‖ + ‖C‖ + ‖D‖) * ‖V‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa [thirdCoordinateDirectCommutator, A, B, C, D] using hnorm
    _ ≤
        (M * ((∑ coordinate : Fin 3,
            ‖thirdCoordinateJet velocity coordinate j k x t‖) +
          (∑ coordinate : Fin 3,
            ‖thirdCoordinateJet velocity coordinate i k x t‖) +
          (∑ coordinate : Fin 3,
            ‖thirdCoordinateJet velocity coordinate i j x t‖) + ‖V‖)) * ‖V‖ :=
      mul_le_mul_of_nonneg_right hsum (norm_nonneg _)

/-! ## The three middle faces and the exact interpolation frontier -/

/-- Every component of a Euclidean vector is bounded by its Euclidean norm. -/
theorem abs_component_le_norm (v : Space) (component : Fin 3) :
    |v component| ≤ ‖v‖ := by
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le v component

/-- A middle `D²-D²` action is bounded by one order-two norm times the three coordinate
order-two faces of the differentiated first jet. -/
theorem openPeriodicSolutionOn_norm_firstJetDerivative_secondJet_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space)
    (firstDirection secondA secondB : Fin 3) :
    ‖fderiv ℝ (fun y ↦ firstCoordinateJet velocity firstDirection y t) x
        (secondCoordinateJet velocity secondA secondB x t)‖ ≤
      ‖secondCoordinateJet velocity secondA secondB x t‖ *
        ∑ coordinate : Fin 3,
          ‖secondCoordinateJet velocity coordinate firstDirection x t‖ := by
  let w : InitialVelocity := fun y ↦ firstCoordinateJet velocity firstDirection y t
  let W : Space := secondCoordinateJet velocity secondA secondB x t
  have hbound := norm_clm_apply_le_bound_mul_sum_coordinate
    (fderiv ℝ w x) W ‖W‖ (abs_component_le_norm W)
  have hbasis : ∀ coordinate : Fin 3,
      fderiv ℝ w x (spatialBasisVector coordinate) =
        secondCoordinateJet velocity coordinate firstDirection x t := by
    intro coordinate
    exact (openPeriodicSolutionOn_secondCoordinateJet_eq_spatialDerivative_firstCoordinateJet
      solution ht x coordinate firstDirection).symm
  simp_rw [hbasis] at hbound
  exact hbound

/-- The middle pairing is reduced exactly to the explicit `D²-D²-D³` boundary population.
This is the point at which a genuine Gagliardo--Nirenberg estimate is required. -/
theorem openPeriodicSolutionOn_abs_inner_thirdCoordinateMiddleCommutator_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (i j k : Fin 3) :
    |inner ℝ (thirdCoordinateMiddleCommutator velocity t i j k x)
        (thirdCoordinateJet velocity i j k x t)| ≤
      (‖secondCoordinateJet velocity i j x t‖ *
          (∑ coordinate : Fin 3,
            ‖secondCoordinateJet velocity coordinate k x t‖) +
        ‖secondCoordinateJet velocity i k x t‖ *
          (∑ coordinate : Fin 3,
            ‖secondCoordinateJet velocity coordinate j x t‖) +
        ‖secondCoordinateJet velocity j k x t‖ *
          (∑ coordinate : Fin 3,
            ‖secondCoordinateJet velocity coordinate i x t‖)) *
        ‖thirdCoordinateJet velocity i j k x t‖ := by
  let A : Space :=
    fderiv ℝ (fun y ↦ firstCoordinateJet velocity k y t) x
      (secondCoordinateJet velocity i j x t)
  let B : Space :=
    fderiv ℝ (fun y ↦ firstCoordinateJet velocity j y t) x
      (secondCoordinateJet velocity i k x t)
  let C : Space :=
    fderiv ℝ (fun y ↦ firstCoordinateJet velocity i y t) x
      (secondCoordinateJet velocity j k x t)
  let V : Space := thirdCoordinateJet velocity i j k x t
  have hA := openPeriodicSolutionOn_norm_firstJetDerivative_secondJet_le
    solution ht x k i j
  have hB := openPeriodicSolutionOn_norm_firstJetDerivative_secondJet_le
    solution ht x j i k
  have hC := openPeriodicSolutionOn_norm_firstJetDerivative_secondJet_le
    solution ht x i j k
  have hnorm : ‖A + B + C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ := by
    calc
      ‖A + B + C‖ ≤ ‖A + B‖ + ‖C‖ := norm_add_le _ _
      _ ≤ (‖A‖ + ‖B‖) + ‖C‖ := add_le_add (norm_add_le _ _) le_rfl
  calc
    |inner ℝ (thirdCoordinateMiddleCommutator velocity t i j k x) V| ≤
        ‖thirdCoordinateMiddleCommutator velocity t i j k x‖ * ‖V‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖A‖ + ‖B‖ + ‖C‖) * ‖V‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa [thirdCoordinateMiddleCommutator, A, B, C] using hnorm
    _ ≤
        (‖secondCoordinateJet velocity i j x t‖ *
            (∑ coordinate : Fin 3,
              ‖secondCoordinateJet velocity coordinate k x t‖) +
          ‖secondCoordinateJet velocity i k x t‖ *
            (∑ coordinate : Fin 3,
              ‖secondCoordinateJet velocity coordinate j x t‖) +
          ‖secondCoordinateJet velocity j k x t‖ *
            (∑ coordinate : Fin 3,
              ‖secondCoordinateJet velocity coordinate i x t‖)) * ‖V‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      gcongr

/-- The exact seven-face pointwise reduction: the proved direct receiver plus the explicit middle
hexagonal boundary.  No interpolation premise is hidden in this statement. -/
theorem openPeriodicSolutionOn_abs_inner_thirdCoordinateLowerCommutator_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (hx : x ∈ unitCube)
    (i j k : Fin 3) :
    |inner ℝ (thirdCoordinateLowerCommutator velocity t i j k x)
        (thirdCoordinateJet velocity i j k x t)| ≤
      cubeGradientSup (fun y ↦ velocity y t) *
        ((∑ coordinate : Fin 3,
            ‖thirdCoordinateJet velocity coordinate j k x t‖) +
          (∑ coordinate : Fin 3,
            ‖thirdCoordinateJet velocity coordinate i k x t‖) +
          (∑ coordinate : Fin 3,
            ‖thirdCoordinateJet velocity coordinate i j x t‖) +
          ‖thirdCoordinateJet velocity i j k x t‖) *
        ‖thirdCoordinateJet velocity i j k x t‖ +
      (‖secondCoordinateJet velocity i j x t‖ *
          (∑ coordinate : Fin 3,
            ‖secondCoordinateJet velocity coordinate k x t‖) +
        ‖secondCoordinateJet velocity i k x t‖ *
          (∑ coordinate : Fin 3,
            ‖secondCoordinateJet velocity coordinate j x t‖) +
        ‖secondCoordinateJet velocity j k x t‖ *
          (∑ coordinate : Fin 3,
            ‖secondCoordinateJet velocity coordinate i x t‖)) *
        ‖thirdCoordinateJet velocity i j k x t‖ := by
  rw [thirdCoordinateLowerCommutator_eq_direct_add_middle, inner_add_left]
  exact (abs_add_le _ _).trans (add_le_add
    (openPeriodicSolutionOn_abs_inner_thirdCoordinateDirectCommutator_le
      solution ht x hx i j k)
    (openPeriodicSolutionOn_abs_inner_thirdCoordinateMiddleCommutator_le
      solution ht x i j k))

/-! ## Kernel audit -/

#print axioms norm_fderiv_le_cubeGradientSup
#print axioms norm_clm_apply_le_bound_mul_sum_coordinate
#print axioms thirdCoordinateLowerCommutator_eq_direct_add_middle
#print axioms openPeriodicSolutionOn_abs_inner_thirdCoordinateDirectCommutator_le
#print axioms openPeriodicSolutionOn_abs_inner_thirdCoordinateMiddleCommutator_le
#print axioms openPeriodicSolutionOn_abs_inner_thirdCoordinateLowerCommutator_le

end Soma.Holonics.Millennium.NavierStokesCoordinateH3Estimate
