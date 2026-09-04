import ElementaryHolonics.Millennium.NavierStokesCoordinateH3Estimate
import ElementaryHolonics.Millennium.NavierStokesCoordinateH3FrequencyComb

/-!
# The lower coordinate faces in the unforced H³ production inequality

The exact coordinate production owners already close orders zero, one, and two.  This owner
attaches those identities to the actual cube Jacobian receiver and to the exact forty-face
coordinate energy.  No Sobolev norm equivalence is used: every addressed order-one or order-two
jet square is selected directly from `coordinateH3EnergyDensity`.

The finite constant is intentionally coarse.  It records the actual population used in the
proof: three order-one words and nine order-two words, with the latter carrying two three-term
mixed faces and one direct Jacobian face.  Sharpening the constant has no continuation
consequence.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Set
open scoped BigOperators Laplacian

namespace Soma.Holonics.Millennium.NavierStokesCoordinateLowerEnergyEstimate

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH2Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH3Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH3Estimate
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FrequencyComb

/-! ## Every lower jet is an actual face of the forty-face receiver -/

theorem coordinateJetEnergyDensity_nonneg
    (velocity : VelocityField) (n : ℕ) (word : Fin n → Fin 3)
    (x : Space) (t : ℝ) :
    0 ≤ coordinateJetEnergyDensity velocity n word x t := by
  unfold coordinateJetEnergyDensity kineticEnergyDensity
  positivity

/-- Any addressed word of order below four is one of the nonnegative faces summed by the
coordinate H³ density. -/
theorem coordinateJetEnergyDensity_le_coordinateH3EnergyDensity
    (velocity : VelocityField) (n : Fin 4)
    (word : Fin (n : ℕ) → Fin 3) (x : Space) (t : ℝ) :
    coordinateJetEnergyDensity velocity n word x t ≤
      coordinateH3EnergyDensity velocity x t := by
  unfold coordinateH3EnergyDensity
  calc
    coordinateJetEnergyDensity velocity n word x t ≤
        ∑ candidate : Fin (n : ℕ) → Fin 3,
          coordinateJetEnergyDensity velocity n candidate x t := by
      exact Finset.single_le_sum
        (fun candidate _hcandidate ↦
          coordinateJetEnergyDensity_nonneg velocity n candidate x t)
        (Finset.mem_univ word)
    _ ≤ ∑ order : Fin 4, ∑ candidate : Fin (order : ℕ) → Fin 3,
          coordinateJetEnergyDensity velocity order candidate x t := by
      let face : Fin 4 → ℝ := fun order ↦
        ∑ candidate : Fin (order : ℕ) → Fin 3,
          coordinateJetEnergyDensity velocity order candidate x t
      have hnonneg : ∀ order ∈ (Finset.univ : Finset (Fin 4)), 0 ≤ face order := by
        intro order _horder
        exact Finset.sum_nonneg (fun candidate _hcandidate ↦
          coordinateJetEnergyDensity_nonneg velocity order candidate x t)
      exact Finset.single_le_sum (s := Finset.univ) (f := face)
        hnonneg (Finset.mem_univ n)

/-- The norm square of any addressed word below order four is at most twice the complete
coordinate density. -/
theorem norm_coordinateJet_sq_le_two_mul_coordinateH3EnergyDensity
    (velocity : VelocityField) (n : Fin 4)
    (word : Fin (n : ℕ) → Fin 3) (x : Space) (t : ℝ) :
    ‖coordinateJet velocity n word x t‖ ^ 2 ≤
      2 * coordinateH3EnergyDensity velocity x t := by
  have hface := coordinateJetEnergyDensity_le_coordinateH3EnergyDensity
    velocity n word x t
  unfold coordinateJetEnergyDensity kineticEnergyDensity at hface
  nlinarith

theorem norm_firstCoordinateJet_sq_le_two_mul_coordinateH3EnergyDensity
    (velocity : VelocityField) (i : Fin 3) (x : Space) (t : ℝ) :
    ‖firstCoordinateJet velocity i x t‖ ^ 2 ≤
      2 * coordinateH3EnergyDensity velocity x t := by
  simpa [firstCoordinateJet, coordinateJetField] using
    norm_coordinateJet_sq_le_two_mul_coordinateH3EnergyDensity velocity
      (⟨1, by norm_num⟩ : Fin 4) (firstCoordinateWord i) x t

theorem norm_secondCoordinateJet_sq_le_two_mul_coordinateH3EnergyDensity
    (velocity : VelocityField) (i j : Fin 3) (x : Space) (t : ℝ) :
    ‖secondCoordinateJet velocity i j x t‖ ^ 2 ≤
      2 * coordinateH3EnergyDensity velocity x t := by
  simpa [secondCoordinateJet, coordinateJetField] using
    norm_coordinateJet_sq_le_two_mul_coordinateH3EnergyDensity velocity
      (⟨2, by norm_num⟩ : Fin 4) (secondCoordinateWord i j) x t

/-! ## The order-one population -/

/-- One order-one stretching face is bounded by the selected Jacobian receiver times its actual
jet square. -/
theorem openPeriodicSolutionOn_neg_inner_velocityDerivative_firstJet_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (hx : x ∈ unitCube)
    (i : Fin 3) :
    -inner ℝ
        (fderiv ℝ (fun y ↦ velocity y t) x (firstCoordinateJet velocity i x t))
        (firstCoordinateJet velocity i x t) ≤
      cubeGradientSup (fun y ↦ velocity y t) *
        ‖firstCoordinateJet velocity i x t‖ ^ 2 := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let w : Space := firstCoordinateJet velocity i x t
  have hu : ContDiff ℝ ∞ u := openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  calc
    -inner ℝ (fderiv ℝ u x w) w ≤ |inner ℝ (fderiv ℝ u x w) w| := neg_le_abs _
    _ ≤ ‖fderiv ℝ u x w‖ * ‖w‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖fderiv ℝ u x‖ * ‖w‖) * ‖w‖ := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ u x‖ * ‖w‖ ^ 2 := by ring
    _ ≤ cubeGradientSup u * ‖w‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (norm_fderiv_le_cubeGradientSup u hu x hx) (sq_nonneg _)

/-- The complete order-one stretching population is bounded by six copies of the complete
coordinate density. -/
theorem openPeriodicSolutionOn_neg_coordinateH1StretchingWork_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    -coordinateH1StretchingWork velocity t ≤
      6 * cubeGradientSup (fun y ↦ velocity y t) * coordinateH3Energy velocity t := by
  let M : ℝ := cubeGradientSup (fun y ↦ velocity y t)
  let E : Space → ℝ := fun x ↦ coordinateH3EnergyDensity velocity x t
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have hrightInt : IntegrableOn (fun x ↦ 2 * M * E x) unitCube :=
    (openPeriodicSolutionOn_coordinateH3EnergyDensity_integrable solution ht).const_mul _
  have hword : ∀ word : Fin 1 → Fin 3,
      -(∫ x in unitCube,
          inner ℝ
            (fderiv ℝ (fun y ↦ velocity y t) x (coordinateJet velocity 1 word x t))
            (coordinateJet velocity 1 word x t)) ≤
        ∫ x in unitCube, 2 * M * E x := by
    intro word
    have hwordEq : word = firstCoordinateWord (word 0) := by
      funext q
      fin_cases q
      rfl
    rw [hwordEq]
    let u : InitialVelocity := fun y ↦ velocity y t
    let w : InitialVelocity := fun x ↦ firstCoordinateJet velocity (word 0) x t
    have hu : ContDiff ℝ ∞ u := openPeriodicSolutionOn_velocitySlice_contDiff solution ht
    have hwFun : w = spatialDirectionalJet u (word 0) := by
      funext x
      exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
        solution ht x (word 0)
    have hw : ContDiff ℝ ∞ w := by
      rw [hwFun]
      exact spatialDirectionalJet_contDiff u hu (word 0)
    have hworkContinuous : Continuous (fun x ↦
        inner ℝ (fderiv ℝ u x (w x)) (w x)) := by
      have hacted : Continuous (fun x ↦ fderiv ℝ u x (w x)) :=
        (hu.continuous_fderiv_apply (by simp)).comp
          (continuous_id.prodMk hw.continuous)
      exact hacted.inner hw.continuous
    have hworkInt : IntegrableOn (fun x ↦
        inner ℝ (fderiv ℝ u x (w x)) (w x)) unitCube :=
      hworkContinuous.continuousOn.integrableOn_compact hcubeCompact
    have hpoint : ∀ x ∈ unitCube,
        -inner ℝ (fderiv ℝ u x (w x)) (w x) ≤ 2 * M * E x := by
      intro x hx
      calc
        -inner ℝ (fderiv ℝ u x (w x)) (w x) ≤ M * ‖w x‖ ^ 2 := by
          simpa [u, w, M] using
            openPeriodicSolutionOn_neg_inner_velocityDerivative_firstJet_le
              solution ht x hx (word 0)
        _ ≤ M * (2 * E x) := by
          apply mul_le_mul_of_nonneg_left _
            (cubeGradientSup_nonneg u hu)
          simpa [w, E] using
            norm_firstCoordinateJet_sq_le_two_mul_coordinateH3EnergyDensity
              velocity (word 0) x t
        _ = 2 * M * E x := by ring
    rw [← integral_neg]
    exact setIntegral_mono_on hworkInt.neg hrightInt hcubeMeasurable hpoint
  unfold coordinateH1StretchingWork
  rw [← Finset.sum_neg_distrib]
  calc
    (∑ word : Fin 1 → Fin 3,
        -∫ x in unitCube,
          inner ℝ
            (fderiv ℝ (fun y ↦ velocity y t) x (coordinateJet velocity 1 word x t))
            (coordinateJet velocity 1 word x t)) ≤
        ∑ _word : Fin 1 → Fin 3, ∫ x in unitCube, 2 * M * E x := by
      exact Finset.sum_le_sum (fun word _hword ↦ hword word)
    _ = (∫ x in unitCube, 2 * M * E x) * 3 := by simp [mul_comm]
    _ = ((2 * M) * (∫ x in unitCube, E x)) * 3 := by
      rw [integral_const_mul]
    _ = 6 * M * (∫ x in unitCube, E x) := by ring
    _ = 6 * M * coordinateH3Energy velocity t := by
      rw [openPeriodicSolutionOn_coordinateH3Energy_eq_integral_density solution ht]

/-! ## The order-two population -/

/-- A first-coordinate derivative acting on another first-coordinate jet is controlled by the
cube Jacobian receiver times the three addressed second-coordinate faces. -/
theorem openPeriodicSolutionOn_norm_firstJetDerivative_firstJet_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (hx : x ∈ unitCube)
    (carriedDirection transportDirection : Fin 3) :
    ‖fderiv ℝ (fun y ↦ firstCoordinateJet velocity carriedDirection y t) x
        (firstCoordinateJet velocity transportDirection x t)‖ ≤
      cubeGradientSup (fun y ↦ velocity y t) *
        ∑ coordinate : Fin 3,
          ‖secondCoordinateJet velocity coordinate carriedDirection x t‖ := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let v : InitialVelocity := fun y ↦ firstCoordinateJet velocity transportDirection y t
  let W : InitialVelocity := fun y ↦ firstCoordinateJet velocity carriedDirection y t
  have hu : ContDiff ℝ ∞ u := openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hvFun : v = spatialDirectionalJet u transportDirection := by
    funext y
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht y transportDirection
  have hvCoordinate : ∀ coordinate : Fin 3,
      |v x coordinate| ≤ cubeGradientSup u := by
    intro coordinate
    rw [hvFun]
    exact abs_spatialDirectionalJet_component_le_cubeGradientSup
      u hu x hx transportDirection coordinate
  have hbound := norm_clm_apply_le_bound_mul_sum_coordinate
    (fderiv ℝ W x) (v x) (cubeGradientSup u) hvCoordinate
  have hbasis : ∀ coordinate : Fin 3,
      fderiv ℝ W x (spatialBasisVector coordinate) =
        secondCoordinateJet velocity coordinate carriedDirection x t := by
    intro coordinate
    exact (openPeriodicSolutionOn_secondCoordinateJet_eq_spatialDerivative_firstCoordinateJet
      solution ht x coordinate carriedDirection).symm
  simp_rw [hbasis] at hbound
  exact hbound

/-- Three addressed norm products are bounded by twelve copies of the complete coordinate
energy density. -/
theorem sum_secondJet_norm_mul_secondJet_norm_le_twelve_density
    (velocity : VelocityField) (carried i j : Fin 3) (x : Space) (t : ℝ) :
    (∑ coordinate : Fin 3,
        ‖secondCoordinateJet velocity coordinate carried x t‖) *
        ‖secondCoordinateJet velocity i j x t‖ ≤
      12 * coordinateH3EnergyDensity velocity x t := by
  let E : ℝ := coordinateH3EnergyDensity velocity x t
  let b : ℝ := ‖secondCoordinateJet velocity i j x t‖
  have hb : b ^ 2 ≤ 2 * E := by
    simpa [b, E] using
      norm_secondCoordinateJet_sq_le_two_mul_coordinateH3EnergyDensity
        velocity i j x t
  have hterm : ∀ coordinate : Fin 3,
      ‖secondCoordinateJet velocity coordinate carried x t‖ * b ≤ 4 * E := by
    intro coordinate
    have ha : ‖secondCoordinateJet velocity coordinate carried x t‖ ^ 2 ≤ 2 * E :=
      norm_secondCoordinateJet_sq_le_two_mul_coordinateH3EnergyDensity
        velocity coordinate carried x t
    nlinarith [sq_nonneg
      (‖secondCoordinateJet velocity coordinate carried x t‖ - b)]
  calc
    (∑ coordinate : Fin 3,
        ‖secondCoordinateJet velocity coordinate carried x t‖) * b =
        ∑ coordinate : Fin 3,
          ‖secondCoordinateJet velocity coordinate carried x t‖ * b := by
      rw [Finset.sum_mul]
    _ ≤ ∑ _coordinate : Fin 3, 4 * E :=
      Finset.sum_le_sum (fun coordinate _hcoordinate ↦ hterm coordinate)
    _ = 12 * E := by simp; ring

/-- One order-two lower commutator pairing is controlled by twenty-six copies of the complete
coordinate density times the actual cube Jacobian receiver. -/
theorem openPeriodicSolutionOn_neg_inner_secondCoordinateLowerCommutator_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (hx : x ∈ unitCube)
    (i j : Fin 3) :
    -inner ℝ (secondCoordinateLowerCommutator velocity t i j x)
        (secondCoordinateJet velocity i j x t) ≤
      26 * cubeGradientSup (fun y ↦ velocity y t) *
        coordinateH3EnergyDensity velocity x t := by
  let A : Space :=
    fderiv ℝ (fun y ↦ firstCoordinateJet velocity j y t) x
      (firstCoordinateJet velocity i x t)
  let B : Space :=
    fderiv ℝ (fun y ↦ firstCoordinateJet velocity i y t) x
      (firstCoordinateJet velocity j x t)
  let D : Space :=
    fderiv ℝ (fun y ↦ velocity y t) x
      (secondCoordinateJet velocity i j x t)
  let W : Space := secondCoordinateJet velocity i j x t
  let M : ℝ := cubeGradientSup (fun y ↦ velocity y t)
  let E : ℝ := coordinateH3EnergyDensity velocity x t
  have hu : ContDiff ℝ ∞ (fun y ↦ velocity y t) :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hM : 0 ≤ M := cubeGradientSup_nonneg (fun y ↦ velocity y t) hu
  have hA := openPeriodicSolutionOn_norm_firstJetDerivative_firstJet_le
    solution ht x hx j i
  have hB := openPeriodicSolutionOn_norm_firstJetDerivative_firstJet_le
    solution ht x hx i j
  have hDactual : ‖D‖ ≤ M * ‖W‖ := by
    dsimp [D, M, W]
    let u : InitialVelocity := fun y ↦ velocity y t
    calc
      ‖fderiv ℝ u x (secondCoordinateJet velocity i j x t)‖ ≤
          ‖fderiv ℝ u x‖ * ‖secondCoordinateJet velocity i j x t‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ cubeGradientSup u * ‖secondCoordinateJet velocity i j x t‖ :=
        mul_le_mul_of_nonneg_right
          (norm_fderiv_le_cubeGradientSup u hu x hx) (norm_nonneg _)
  have hfirst :
      (∑ coordinate : Fin 3,
        ‖secondCoordinateJet velocity coordinate j x t‖) * ‖W‖ ≤ 12 * E := by
    simpa [W, E] using
      sum_secondJet_norm_mul_secondJet_norm_le_twelve_density velocity j i j x t
  have hsecond :
      (∑ coordinate : Fin 3,
        ‖secondCoordinateJet velocity coordinate i x t‖) * ‖W‖ ≤ 12 * E := by
    simpa [W, E] using
      sum_secondJet_norm_mul_secondJet_norm_le_twelve_density velocity i i j x t
  have hWsq : ‖W‖ ^ 2 ≤ 2 * E := by
    simpa [W, E] using
      norm_secondCoordinateJet_sq_le_two_mul_coordinateH3EnergyDensity
        velocity i j x t
  have hnorm : ‖A + B + D‖ ≤ ‖A‖ + ‖B‖ + ‖D‖ := by
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  calc
    -inner ℝ (secondCoordinateLowerCommutator velocity t i j x) W ≤
        |inner ℝ (secondCoordinateLowerCommutator velocity t i j x) W| := neg_le_abs _
    _ ≤ ‖secondCoordinateLowerCommutator velocity t i j x‖ * ‖W‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖A‖ + ‖B‖ + ‖D‖) * ‖W‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa [secondCoordinateLowerCommutator, A, B, D] using hnorm
    _ ≤
        (M * (∑ coordinate : Fin 3,
            ‖secondCoordinateJet velocity coordinate j x t‖) +
          M * (∑ coordinate : Fin 3,
            ‖secondCoordinateJet velocity coordinate i x t‖) +
          M * ‖W‖) * ‖W‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      gcongr
    _ = M * ((∑ coordinate : Fin 3,
            ‖secondCoordinateJet velocity coordinate j x t‖) * ‖W‖) +
          M * ((∑ coordinate : Fin 3,
            ‖secondCoordinateJet velocity coordinate i x t‖) * ‖W‖) +
          M * ‖W‖ ^ 2 := by ring
    _ ≤ M * (12 * E) + M * (12 * E) + M * (2 * E) := by
      gcongr
    _ = 26 * M * E := by ring

theorem openPeriodicSolutionOn_secondCoordinateLowerWork_integrable
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (i j : Fin 3) :
    IntegrableOn (fun x ↦
      inner ℝ (secondCoordinateLowerCommutator velocity t i j x)
        (secondCoordinateJet velocity i j x t)) unitCube := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let wi : InitialVelocity := fun y ↦ firstCoordinateJet velocity i y t
  let wj : InitialVelocity := fun y ↦ firstCoordinateJet velocity j y t
  let W : InitialVelocity := fun y ↦ secondCoordinateJet velocity i j y t
  let lower : InitialVelocity := fun x ↦ secondCoordinateLowerCommutator velocity t i j x
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hu : ContDiff ℝ ∞ u := openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hwiFun : wi = spatialDirectionalJet u i := by
    funext y
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht y i
  have hwjFun : wj = spatialDirectionalJet u j := by
    funext y
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht y j
  have hWFun : W = secondSpatialCoordinateJet u i j := by
    funext y
    exact openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
      solution ht y i j
  have hwi : ContDiff ℝ ∞ wi := by
    rw [hwiFun]
    exact spatialDirectionalJet_contDiff u hu i
  have hwj : ContDiff ℝ ∞ wj := by
    rw [hwjFun]
    exact spatialDirectionalJet_contDiff u hu j
  have hW : ContDiff ℝ ∞ W := by
    rw [hWFun]
    exact secondSpatialCoordinateJet_contDiff u hu i j
  have hDwi : ContDiff ℝ ∞ (fderiv ℝ wi) := hwi.fderiv_right (by simp)
  have hDwj : ContDiff ℝ ∞ (fderiv ℝ wj) := hwj.fderiv_right (by simp)
  have hDu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hlower : ContDiff ℝ ∞ lower := by
    have hfirst : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ wj x (wi x)) := hDwj.clm_apply hwi
    have hsecond : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ wi x (wj x)) := hDwi.clm_apply hwj
    have hthird : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ u x (W x)) := hDu.clm_apply hW
    simpa [lower, secondCoordinateLowerCommutator, u, wi, wj, W] using
      (hfirst.add hsecond).add hthird
  exact (hlower.continuous.inner hW.continuous).continuousOn.integrableOn_compact
    hcubeCompact

/-- The complete nine-word order-two lower population is bounded by 234 copies of the exact
coordinate energy. -/
theorem openPeriodicSolutionOn_neg_coordinateH2LowerWork_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    -coordinateH2LowerWork velocity t ≤
      234 * cubeGradientSup (fun y ↦ velocity y t) * coordinateH3Energy velocity t := by
  let M : ℝ := cubeGradientSup (fun y ↦ velocity y t)
  let E : Space → ℝ := fun x ↦ coordinateH3EnergyDensity velocity x t
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have hrightInt : IntegrableOn (fun x ↦ 26 * M * E x) unitCube :=
    (openPeriodicSolutionOn_coordinateH3EnergyDensity_integrable solution ht).const_mul _
  have hword : ∀ word : Fin 2 → Fin 3,
      -(∫ x in unitCube,
          inner ℝ
            (secondCoordinateLowerCommutator velocity t (word 0) (word 1) x)
            (coordinateJet velocity 2 word x t)) ≤
        ∫ x in unitCube, 26 * M * E x := by
    intro word
    have hwordEq : word = secondCoordinateWord (word 0) (word 1) := by
      funext q
      fin_cases q <;> rfl
    rw [hwordEq]
    have hleftInt := openPeriodicSolutionOn_secondCoordinateLowerWork_integrable
      solution ht (word 0) (word 1)
    have hpoint : ∀ x ∈ unitCube,
        -inner ℝ
            (secondCoordinateLowerCommutator velocity t (word 0) (word 1) x)
            (secondCoordinateJet velocity (word 0) (word 1) x t) ≤
          26 * M * E x := by
      intro x hx
      simpa [M, E] using
        openPeriodicSolutionOn_neg_inner_secondCoordinateLowerCommutator_le
          solution ht x hx (word 0) (word 1)
    rw [← integral_neg]
    exact setIntegral_mono_on hleftInt.neg hrightInt hcubeMeasurable hpoint
  unfold coordinateH2LowerWork
  rw [← Finset.sum_neg_distrib]
  calc
    (∑ word : Fin 2 → Fin 3,
        -∫ x in unitCube,
          inner ℝ
            (secondCoordinateLowerCommutator velocity t (word 0) (word 1) x)
            (coordinateJet velocity 2 word x t)) ≤
        ∑ _word : Fin 2 → Fin 3, ∫ x in unitCube, 26 * M * E x := by
      exact Finset.sum_le_sum (fun word _hword ↦ hword word)
    _ = (∫ x in unitCube, 26 * M * E x) * 9 := by simp [mul_comm]
    _ = ((26 * M) * (∫ x in unitCube, E x)) * 9 := by
      rw [integral_const_mul]
    _ = 234 * M * (∫ x in unitCube, E x) := by ring
    _ = 234 * M * coordinateH3Energy velocity t := by
      rw [openPeriodicSolutionOn_coordinateH3Energy_eq_integral_density solution ht]

/-! ## Dissipation signs and the complete lower-order estimate -/

theorem coordinateH1Dissipation_nonneg (velocity : VelocityField) (t : ℝ) :
    0 ≤ coordinateH1Dissipation velocity t := by
  have hcubeMeasurable : MeasurableSet unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc |>.measurableSet
  unfold coordinateH1Dissipation
  exact Finset.sum_nonneg (fun word _hword ↦
    setIntegral_nonneg hcubeMeasurable
      (fun x _hx ↦ Finset.sum_nonneg (fun component _hcomponent ↦ sq_nonneg _)))

theorem coordinateH2Dissipation_nonneg (velocity : VelocityField) (t : ℝ) :
    0 ≤ coordinateH2Dissipation velocity t := by
  have hcubeMeasurable : MeasurableSet unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc |>.measurableSet
  unfold coordinateH2Dissipation
  exact Finset.sum_nonneg (fun word _hword ↦
    setIntegral_nonneg hcubeMeasurable
      (fun x _hx ↦ Finset.sum_nonneg (fun component _hcomponent ↦ sq_nonneg _)))

theorem openPeriodicSolutionOn_unforced_coordinateH1TimeWork_le
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (hnu : 0 ≤ nu) :
    coordinateH1TimeWork velocity t ≤
      6 * cubeGradientSup (fun y ↦ velocity y t) * coordinateH3Energy velocity t := by
  have hproduction := openPeriodicSolutionOn_unforced_coordinateH1TimeWork_eq_production
    solution ht
  have hdissipation := coordinateH1Dissipation_nonneg velocity t
  have hlower := openPeriodicSolutionOn_neg_coordinateH1StretchingWork_le solution ht
  have hviscous : -nu * coordinateH1Dissipation velocity t ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnu) hdissipation
  linarith

theorem openPeriodicSolutionOn_unforced_coordinateH2TimeWork_le
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (hnu : 0 ≤ nu) :
    coordinateH2TimeWork velocity t ≤
      234 * cubeGradientSup (fun y ↦ velocity y t) * coordinateH3Energy velocity t := by
  have hproduction := openPeriodicSolutionOn_unforced_coordinateH2TimeWork_eq_production
    solution ht
  have hdissipation := coordinateH2Dissipation_nonneg velocity t
  have hlower := openPeriodicSolutionOn_neg_coordinateH2LowerWork_le solution ht
  have hviscous : -nu * coordinateH2Dissipation velocity t ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnu) hdissipation
  linarith

/-! ## The undifferentiated face -/

def coordinateH0Dissipation (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∫ x in unitCube, ∑ component : Fin 3,
    ‖gradient (fun y ↦ velocity y t component) x‖ ^ 2

theorem coordinateH0Dissipation_nonneg (velocity : VelocityField) (t : ℝ) :
    0 ≤ coordinateH0Dissipation velocity t := by
  have hcubeMeasurable : MeasurableSet unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc |>.measurableSet
  unfold coordinateH0Dissipation
  exact setIntegral_nonneg hcubeMeasurable
    (fun x _hx ↦ Finset.sum_nonneg (fun component _hcomponent ↦ sq_nonneg _))

theorem coordinateJet_zero_eq_velocity
    (velocity : VelocityField) (word : Fin 0 → Fin 3) (x : Space) (t : ℝ) :
    coordinateJet velocity 0 word x t = velocity x t := by
  simp [coordinateJet]

/-- The unique order-zero face is the ordinary unforced kinetic-energy production identity. -/
theorem openPeriodicSolutionOn_unforced_coordinateH0TimeWork_eq_dissipation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    coordinateH0TimeWork velocity t = -nu * coordinateH0Dissipation velocity t := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let p : Space → ℝ := fun y ↦ pressure y t
  let time : InitialVelocity := fun y ↦ eulerianTimeJet velocity y t
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have hu : ContDiff ℝ ∞ u := openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hp : ContDiff ℝ ∞ p := openPeriodicSolutionOn_pressureSlice_contDiff solution ht
  have htime : ContDiff ℝ ∞ time :=
    openPeriodicSolutionOn_eulerianTimeJetSlice_contDiff solution ht
  have hDu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hadvection : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ u x (u x)) := hDu.clm_apply hu
  have hpressure : ContDiff ℝ ∞ (gradient p) := gradient_contDiff hp
  have htimeInt : IntegrableOn (fun x ↦ inner ℝ (time x) (u x)) unitCube :=
    (htime.continuous.inner hu.continuous).continuousOn.integrableOn_compact hcubeCompact
  have hadvectionInt : IntegrableOn (fun x ↦
      inner ℝ (fderiv ℝ u x (u x)) (u x)) unitCube :=
    (hadvection.continuous.inner hu.continuous).continuousOn.integrableOn_compact
      hcubeCompact
  have hviscousInt : IntegrableOn (fun x ↦ inner ℝ (Δ u x) (u x)) unitCube :=
    integrableOn_inner_laplacian_unitCube u
      (hu.of_le (WithTop.coe_le_coe.mpr le_top))
  have hpressureInt : IntegrableOn (fun x ↦ inner ℝ (gradient p x) (u x)) unitCube :=
    (hpressure.continuous.inner hu.continuous).continuousOn.integrableOn_compact
      hcubeCompact
  have hpoint : ∀ x,
      inner ℝ (time x) (u x) + inner ℝ (fderiv ℝ u x (u x)) (u x) =
        nu * inner ℝ (Δ u x) (u x) - inner ℝ (gradient p x) (u x) := by
    intro x
    have hpde := openPeriodicSolutionOn_unforced_vector_momentum solution ht x
    have hinner := congrArg (fun z : Space ↦ inner ℝ z (u x)) hpde
    simpa [u, p, time, inner_add_left, inner_sub_left, real_inner_smul_left] using hinner
  have hintegrated :
      (∫ x in unitCube, inner ℝ (time x) (u x)) +
          ∫ x in unitCube, inner ℝ (fderiv ℝ u x (u x)) (u x) =
        nu * (∫ x in unitCube, inner ℝ (Δ u x) (u x)) -
          ∫ x in unitCube, inner ℝ (gradient p x) (u x) := by
    calc
      (∫ x in unitCube, inner ℝ (time x) (u x)) +
          ∫ x in unitCube, inner ℝ (fderiv ℝ u x (u x)) (u x) =
        ∫ x in unitCube,
          (inner ℝ (time x) (u x) + inner ℝ (fderiv ℝ u x (u x)) (u x)) :=
        (integral_add htimeInt hadvectionInt).symm
      _ = ∫ x in unitCube,
          (nu * inner ℝ (Δ u x) (u x) - inner ℝ (gradient p x) (u x)) := by
        apply setIntegral_congr_fun hcubeMeasurable
        intro x _hx
        exact hpoint x
      _ = (∫ x in unitCube, nu * inner ℝ (Δ u x) (u x)) -
          ∫ x in unitCube, inner ℝ (gradient p x) (u x) :=
        integral_sub (hviscousInt.const_mul nu) hpressureInt
      _ = nu * (∫ x in unitCube, inner ℝ (Δ u x) (u x)) -
          ∫ x in unitCube, inner ℝ (gradient p x) (u x) := by
        rw [integral_const_mul]
  have hadvectionZero :
      (∫ x in unitCube, inner ℝ (fderiv ℝ u x (u x)) (u x)) = 0 := by
    apply integral_advectionWork_unitCube_eq_zero u
      (hu.of_le (WithTop.coe_le_coe.mpr le_top))
    · exact solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩
    · exact fun x ↦ solution.incompressible x t ⟨ht.1.le, ht.2⟩
  have hpressureZero :
      (∫ x in unitCube, inner ℝ (gradient p x) (u x)) = 0 := by
    apply integral_pressureWork_unitCube_eq_zero u p
      (hu.of_le (WithTop.coe_le_coe.mpr le_top))
      (hp.of_le (WithTop.coe_le_coe.mpr le_top))
    · exact solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩
    · exact solution.pressurePeriodic t ⟨ht.1.le, ht.2⟩
    · exact fun x ↦ solution.incompressible x t ⟨ht.1.le, ht.2⟩
  have hviscous :
      (∫ x in unitCube, inner ℝ (Δ u x) (u x)) =
        -∫ x in unitCube, ∑ component : Fin 3,
          ‖gradient (fun y ↦ u y component) x‖ ^ 2 :=
    integral_inner_laplacian_eq_neg_integral_component_gradient_sq u
      (hu.of_le (WithTop.coe_le_coe.mpr le_top))
      (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩)
  have htimeEq :
      (∫ x in unitCube, inner ℝ (time x) (u x)) =
        -nu * coordinateH0Dissipation velocity t := by
    unfold coordinateH0Dissipation
    dsimp [u, p, time] at hintegrated hadvectionZero hpressureZero hviscous ⊢
    rw [hadvectionZero, hpressureZero, hviscous] at hintegrated
    linarith
  unfold coordinateH0TimeWork
  calc
    (∑ word : Fin 0 → Fin 3,
        ∫ x in unitCube,
          inner ℝ
            (eulerianTimeJet (coordinateJetField velocity 0 word) x t)
            (coordinateJet velocity 0 word x t)) =
        ∑ _word : Fin 0 → Fin 3,
          ∫ x in unitCube, inner ℝ (time x) (u x) := by
      apply Finset.sum_congr rfl
      intro word _hword
      have hfield : coordinateJetField velocity 0 word = velocity := by
        funext x s
        exact coordinateJet_zero_eq_velocity velocity word x s
      rw [hfield]
      rfl
    _ = ∫ x in unitCube, inner ℝ (time x) (u x) := by simp
    _ = -nu * coordinateH0Dissipation velocity t := htimeEq

theorem openPeriodicSolutionOn_unforced_coordinateH0TimeWork_nonpos
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (hnu : 0 ≤ nu) :
    coordinateH0TimeWork velocity t ≤ 0 := by
  rw [openPeriodicSolutionOn_unforced_coordinateH0TimeWork_eq_dissipation solution ht]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnu)
    (coordinateH0Dissipation_nonneg velocity t)

/-! ## The returned lower-order production law -/

/-- Orders zero through two of the exact coordinate production population are controlled by the
actual cube Jacobian receiver and the differentiated coordinate energy. -/
theorem openPeriodicSolutionOn_unforced_coordinateLowerTimeWork_le_energy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (hnu : 0 ≤ nu) :
    coordinateH0TimeWork velocity t + coordinateH1TimeWork velocity t +
        coordinateH2TimeWork velocity t ≤
      240 * cubeGradientSup (fun y ↦ velocity y t) * coordinateH3Energy velocity t := by
  have hzero := openPeriodicSolutionOn_unforced_coordinateH0TimeWork_nonpos
    solution ht hnu
  have hone := openPeriodicSolutionOn_unforced_coordinateH1TimeWork_le
    solution ht hnu
  have htwo := openPeriodicSolutionOn_unforced_coordinateH2TimeWork_le
    solution ht hnu
  linarith

/-- The same lower-order return factors through the augmented coordinate receiver consumed by
the logarithmic continuation law. -/
theorem openPeriodicSolutionOn_unforced_coordinateLowerTimeWork_le_logReceiver
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (hnu : 0 ≤ nu) :
    coordinateH0TimeWork velocity t + coordinateH1TimeWork velocity t +
        coordinateH2TimeWork velocity t ≤
      240 * cubeGradientSup (fun y ↦ velocity y t) *
        coordinateLogH3Receiver velocity t := by
  have hlower := openPeriodicSolutionOn_unforced_coordinateLowerTimeWork_le_energy
    solution ht hnu
  have hu : ContDiff ℝ ∞ (fun y ↦ velocity y t) :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hM : 0 ≤ cubeGradientSup (fun y ↦ velocity y t) :=
    cubeGradientSup_nonneg _ hu
  have henergy : coordinateH3Energy velocity t ≤ coordinateLogH3Receiver velocity t := by
    unfold coordinateLogH3Receiver
    linarith [Real.exp_pos 1]
  exact hlower.trans (mul_le_mul_of_nonneg_left henergy (mul_nonneg (by norm_num) hM))

/-- Any declared pointwise Jacobian envelope dominates the genuine cube supremum. -/
theorem cubeGradientSup_le_of_pointwise_envelope
    (u : InitialVelocity) (K : ℝ)
    (hK : ∀ x ∈ unitCube, ‖fderiv ℝ u x‖ ≤ K) :
    cubeGradientSup u ≤ K := by
  unfold cubeGradientSup
  apply csSup_le
  · refine ⟨‖fderiv ℝ u 0‖, ?_⟩
    exact ⟨0, by
      unfold unitCube
      change (0 : Fin 3 → ℝ) ∈ Icc 0 (fun _ ↦ 1)
      exact ⟨le_rfl, fun _ ↦ zero_le_one⟩, rfl⟩
  · rintro value ⟨x, hx, rfl⟩
    exact hK x hx

/-- Receiver rebase to the exact time-indexed Jacobian envelope used by the frequency comb. -/
theorem openPeriodicSolutionOn_unforced_coordinateLowerTimeWork_le_envelope
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t K : ℝ} (ht : t ∈ Ioo 0 T) (hnu : 0 ≤ nu)
    (hK : ∀ x ∈ unitCube, ‖fderiv ℝ (fun y ↦ velocity y t) x‖ ≤ K) :
    coordinateH0TimeWork velocity t + coordinateH1TimeWork velocity t +
        coordinateH2TimeWork velocity t ≤
      240 * K * coordinateLogH3Receiver velocity t := by
  have hlower := openPeriodicSolutionOn_unforced_coordinateLowerTimeWork_le_logReceiver
    solution ht hnu
  have hsup := cubeGradientSup_le_of_pointwise_envelope
    (fun y ↦ velocity y t) K hK
  have hreceiver : 0 ≤ coordinateLogH3Receiver velocity t :=
    (one_le_coordinateLogH3Receiver velocity t).trans' zero_le_one
  calc
    coordinateH0TimeWork velocity t + coordinateH1TimeWork velocity t +
        coordinateH2TimeWork velocity t ≤
      240 * cubeGradientSup (fun y ↦ velocity y t) *
        coordinateLogH3Receiver velocity t := hlower
    _ ≤ 240 * K * coordinateLogH3Receiver velocity t := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsup (by norm_num)) hreceiver

section Audit

#print axioms coordinateJetEnergyDensity_le_coordinateH3EnergyDensity
#print axioms openPeriodicSolutionOn_neg_coordinateH1StretchingWork_le
#print axioms openPeriodicSolutionOn_neg_coordinateH2LowerWork_le
#print axioms openPeriodicSolutionOn_unforced_coordinateH0TimeWork_eq_dissipation
#print axioms openPeriodicSolutionOn_unforced_coordinateLowerTimeWork_le_energy
#print axioms openPeriodicSolutionOn_unforced_coordinateLowerTimeWork_le_envelope

end Audit

end Soma.Holonics.Millennium.NavierStokesCoordinateLowerEnergyEstimate
