import ElementaryHolonics.Millennium.NavierStokesOpenWeightedPathPassage
import ElementaryHolonics.Millennium.NavierStokesQuadraticH3Energy

/-!
# The actual weighted H³ path on an arbitrary compact interior interval

**[proved-derived]** Joint spacetime smoothness and the complete smooth-slice Parseval passage
make the actual native weighted `H³` state continuous on every preassigned compact interval
strictly inside an open solution lifespan.  The proof retains all forty spatial derivative
faces: the native distance is controlled by their cube-square difference population, and that
finite population is continuous by compact parametric integration.

This is compact-interior infrastructure.  It supplies neither a modulus uniform in the terminal
face nor a terminal norm bound.
-/

noncomputable section

open ContDiff Filter Function MeasureTheory Set
open scoped BigOperators NNReal

namespace Soma.Holonics.Millennium.NavierStokesOpenCompactWeightedPath

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH2Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH3Production
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenMildFieldReconstruction
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesOpenWeightedPathPassage
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedCommonApertureUniqueness
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelReturnContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderPersistence
open Soma.Holonics.Millennium.NavierStokesWeightedHeatSemigroup
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedLinearPath
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothSliceReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
open Soma.Holonics.Millennium.NavierStokesWeightedShiftedHigherOrderPersistence

/-! ## Exact subtraction before the continuity estimate -/

/-- The smooth-slice native realization preserves subtraction exactly. -/
theorem smoothSliceVectorWeightedH3_sub
    (u v : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (huperiodic : IsOnePeriodic u) (hvperiodic : IsOnePeriodic v) :
    smoothSliceVectorWeightedH3 (u - v) (hu.sub hv)
        (by
          intro x i
          simp only [Pi.sub_apply]
          rw [huperiodic x i, hvperiodic x i]) =
      smoothSliceVectorWeightedH3 u hu huperiodic -
        smoothSliceVectorWeightedH3 v hv hvperiodic := by
  have hsubperiodic : IsOnePeriodic (u - v) := by
    intro x i
    simp only [Pi.sub_apply]
    rw [huperiodic x i, hvperiodic x i]
  let left := smoothSliceVectorWeightedH3 (u - v) (hu.sub hv)
    hsubperiodic
  let right := smoothSliceVectorWeightedH3 u hu huperiodic -
    smoothSliceVectorWeightedH3 v hv hvperiodic
  have hleftReal : IsWeightedFourierReal 3 left :=
    isWeightedFourierReal_smoothSliceVectorWeightedH3
      (u - v) (hu.sub hv) hsubperiodic
  have hrightReal : IsWeightedFourierReal 3 right :=
    (isWeightedFourierReal_smoothSliceVectorWeightedH3 u hu huperiodic).sub
      (isWeightedFourierReal_smoothSliceVectorWeightedH3 v hv hvperiodic)
  have hleftField : reconstructedVelocity left = u - v :=
    reconstructedVelocity_smoothSliceVectorWeightedH3
      (u - v) (hu.sub hv) hsubperiodic
  have hrightField : reconstructedVelocity right = u - v := by
    dsimp only [right]
    funext x
    rw [reconstructedVelocity_sub,
      reconstructedVelocity_smoothSliceVectorWeightedH3 u hu huperiodic,
      reconstructedVelocity_smoothSliceVectorWeightedH3 v hv hvperiodic]
    rfl
  exact weightedH3State_eq_of_reconstructedVelocity_eq
    hleftReal hrightReal (hleftField.trans hrightField.symm)

/-- The native state difference of two actual interior slices is the native realization of their
literal physical difference field. -/
theorem openVelocityWeightedH3State_sub
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (s t : Ioo (0 : ℝ) T) :
    openVelocityWeightedH3State solution t -
        openVelocityWeightedH3State solution s =
      smoothSliceVectorWeightedH3
        ((fun x ↦ velocity x t.1) - (fun x ↦ velocity x s.1))
        ((openPeriodicSolutionOn_velocitySlice_contDiff solution t.2).sub
          (openPeriodicSolutionOn_velocitySlice_contDiff solution s.2))
        (by
          intro x i
          simp only [Pi.sub_apply]
          exact congrArg₂ (fun left right : Space ↦ left - right)
            (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩ x i)
            (solution.velocityPeriodic s.1 ⟨s.2.1.le, s.2.2⟩ x i)) := by
  symm
  exact smoothSliceVectorWeightedH3_sub
    (fun x ↦ velocity x t.1) (fun x ↦ velocity x s.1)
    (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
    (openPeriodicSolutionOn_velocitySlice_contDiff solution s.2)
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)
    (solution.velocityPeriodic s.1 ⟨s.2.1.le, s.2.2⟩)

/-! ## Linearity of the finite spatial-jet population -/

theorem spatialDirectionalJet_sub
    (u v : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (i : Fin 3) :
    spatialDirectionalJet (u - v) i =
      spatialDirectionalJet u i - spatialDirectionalJet v i := by
  funext x
  unfold spatialDirectionalJet
  have hsub := fderiv_sub
    (hu.differentiable (by simp) x) (hv.differentiable (by simp) x)
  rw [hsub]
  rfl

theorem secondSpatialCoordinateJet_sub
    (u v : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (i j : Fin 3) :
    secondSpatialCoordinateJet (u - v) i j =
      secondSpatialCoordinateJet u i j - secondSpatialCoordinateJet v i j := by
  unfold secondSpatialCoordinateJet
  rw [spatialDirectionalJet_sub u v hu hv j]
  exact spatialDirectionalJet_sub
    (spatialDirectionalJet u j) (spatialDirectionalJet v j)
    (spatialDirectionalJet_contDiff u hu j)
    (spatialDirectionalJet_contDiff v hv j) i

theorem thirdSpatialCoordinateJet_sub
    (u v : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (i j l : Fin 3) :
    thirdSpatialCoordinateJet (u - v) i j l =
      thirdSpatialCoordinateJet u i j l -
        thirdSpatialCoordinateJet v i j l := by
  unfold thirdSpatialCoordinateJet
  rw [secondSpatialCoordinateJet_sub u v hu hv j l]
  exact spatialDirectionalJet_sub
    (secondSpatialCoordinateJet u j l) (secondSpatialCoordinateJet v j l)
    (secondSpatialCoordinateJet_contDiff u hu j l)
    (secondSpatialCoordinateJet_contDiff v hv j l) i

/-! ## The complete physical difference population -/

/-- The forty spatial derivative faces of the difference between two velocity slices, summed
over all three output components in the Euclidean cube chart. -/
def openVelocityH3DifferenceCubePopulation
    (velocity : VelocityField) (s t : ℝ) : ℝ :=
  ∑ component : Fin 3,
    ((∫ x in unitCube, (velocity x t component - velocity x s component) ^ 2) +
      (∑ i : Fin 3,
        ∫ x in unitCube,
          (firstCoordinateJet velocity i x t -
            firstCoordinateJet velocity i x s) component ^ 2) +
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x in unitCube,
          (secondCoordinateJet velocity i j x t -
            secondCoordinateJet velocity i j x s) component ^ 2) +
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
        ∫ x in unitCube,
          (thirdCoordinateJet velocity i j l x t -
            thirdCoordinateJet velocity i j l x s) component ^ 2))

theorem smoothSliceDerivativeCubeSquarePopulation_nonneg
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) :
    0 ≤ smoothSliceDerivativeCubeSquarePopulation u hu hperiodic component := by
  unfold smoothSliceDerivativeCubeSquarePopulation
  positivity

theorem openVelocityH3DifferenceCubePopulation_eq_smoothPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (s t : Ioo (0 : ℝ) T) :
    openVelocityH3DifferenceCubePopulation velocity s.1 t.1 =
      ∑ component : Fin 3,
        smoothSliceDerivativeCubeSquarePopulation
          ((fun x ↦ velocity x t.1) - (fun x ↦ velocity x s.1))
          ((openPeriodicSolutionOn_velocitySlice_contDiff solution t.2).sub
            (openPeriodicSolutionOn_velocitySlice_contDiff solution s.2))
          (by
            intro x i
            simp only [Pi.sub_apply]
            exact congrArg₂ (fun left right : Space ↦ left - right)
              (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩ x i)
              (solution.velocityPeriodic s.1 ⟨s.2.1.le, s.2.2⟩ x i))
          component := by
  let u : InitialVelocity := fun x ↦ velocity x t.1
  let v : InitialVelocity := fun x ↦ velocity x s.1
  let hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution t.2
  let hv : ContDiff ℝ ∞ v :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution s.2
  have hcube : MeasurableSet unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc |>.measurableSet
  unfold openVelocityH3DifferenceCubePopulation
  unfold smoothSliceDerivativeCubeSquarePopulation
  apply Finset.sum_congr rfl
  intro component _hcomponent
  have hzero :
      (∫ x in unitCube,
        (velocity x t.1 component - velocity x s.1 component) ^ 2) =
      ∫ x in unitCube,
        (((fun x ↦ velocity x t.1) -
          (fun x ↦ velocity x s.1)) x component) ^ 2 := by
    apply setIntegral_congr_fun hcube
    intro x _hx
    rfl
  have hone :
      (∑ i : Fin 3, ∫ x in unitCube,
        (firstCoordinateJet velocity i x t.1 -
          firstCoordinateJet velocity i x s.1) component ^ 2) =
      ∑ i : Fin 3, ∫ x in unitCube,
        (spatialDirectionalJet
          ((fun x ↦ velocity x t.1) - (fun x ↦ velocity x s.1)) i x component) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _hi
    apply setIntegral_congr_fun hcube
    intro x _hx
    have hsub := congrFun (spatialDirectionalJet_sub u v hu hv i) x
    change (firstCoordinateJet velocity i x t.1 -
        firstCoordinateJet velocity i x s.1) component ^ 2 =
      (spatialDirectionalJet (u - v) i x component) ^ 2
    rw [hsub]
    rw [openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution t.2 x i,
      openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
        solution s.2 x i]
    rfl
  have htwo :
      (∑ i : Fin 3, ∑ j : Fin 3, ∫ x in unitCube,
        (secondCoordinateJet velocity i j x t.1 -
          secondCoordinateJet velocity i j x s.1) component ^ 2) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x in unitCube,
        (secondSpatialCoordinateJet
          ((fun x ↦ velocity x t.1) - (fun x ↦ velocity x s.1))
          i j x component) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    apply setIntegral_congr_fun hcube
    intro x _hx
    have hsub := congrFun (secondSpatialCoordinateJet_sub u v hu hv i j) x
    change (secondCoordinateJet velocity i j x t.1 -
        secondCoordinateJet velocity i j x s.1) component ^ 2 =
      (secondSpatialCoordinateJet (u - v) i j x component) ^ 2
    rw [hsub]
    rw [openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
      solution t.2 x i j,
      openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
        solution s.2 x i j]
    rfl
  have hthree :
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, ∫ x in unitCube,
        (thirdCoordinateJet velocity i j l x t.1 -
          thirdCoordinateJet velocity i j l x s.1) component ^ 2) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, ∫ x in unitCube,
        (thirdSpatialCoordinateJet
          ((fun x ↦ velocity x t.1) - (fun x ↦ velocity x s.1))
          i j l x component) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    apply Finset.sum_congr rfl
    intro l _hl
    apply setIntegral_congr_fun hcube
    intro x _hx
    have hsub := congrFun (thirdSpatialCoordinateJet_sub u v hu hv i j l) x
    change (thirdCoordinateJet velocity i j l x t.1 -
        thirdCoordinateJet velocity i j l x s.1) component ^ 2 =
      (thirdSpatialCoordinateJet (u - v) i j l x component) ^ 2
    rw [hsub]
    rw [openPeriodicSolutionOn_thirdCoordinateJet_eq_thirdSpatialCoordinateJet
      solution t.2 x i j l,
      openPeriodicSolutionOn_thirdCoordinateJet_eq_thirdSpatialCoordinateJet
        solution s.2 x i j l]
    rfl
  rw [hzero, hone, htwo, hthree]

theorem openVelocityH3DifferenceCubePopulation_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (s t : Ioo (0 : ℝ) T) :
    0 ≤ openVelocityH3DifferenceCubePopulation velocity s.1 t.1 := by
  rw [openVelocityH3DifferenceCubePopulation_eq_smoothPopulation solution s t]
  exact Finset.sum_nonneg fun component _ ↦
    smoothSliceDerivativeCubeSquarePopulation_nonneg _ _ _ component

/-- Parseval turns the complete physical difference population into a strong native-distance
control. -/
theorem norm_sq_openVelocityWeightedH3State_sub_le_differencePopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (s t : Ioo (0 : ℝ) T) :
    ‖openVelocityWeightedH3State solution t -
        openVelocityWeightedH3State solution s‖ ^ 2 ≤
      3 * openVelocityH3DifferenceCubePopulation velocity s.1 t.1 := by
  let difference : InitialVelocity :=
    (fun x ↦ velocity x t.1) - (fun x ↦ velocity x s.1)
  let hdifference : ContDiff ℝ ∞ difference :=
    (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2).sub
      (openPeriodicSolutionOn_velocitySlice_contDiff solution s.2)
  let hperiodic : IsOnePeriodic difference := by
    intro x i
    simp only [difference, Pi.sub_apply]
    exact congrArg₂ (fun left right : Space ↦ left - right)
      (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩ x i)
      (solution.velocityPeriodic s.1 ⟨s.2.1.le, s.2.2⟩ x i)
  let stateDifference := openVelocityWeightedH3State solution t -
    openVelocityWeightedH3State solution s
  let population := openVelocityH3DifferenceCubePopulation velocity s.1 t.1
  have hstate : stateDifference =
      smoothSliceVectorWeightedH3 difference hdifference hperiodic := by
    exact openVelocityWeightedH3State_sub solution s t
  have hpopulation : population = ∑ component : Fin 3,
      smoothSliceDerivativeCubeSquarePopulation
        difference hdifference hperiodic component := by
    exact openVelocityH3DifferenceCubePopulation_eq_smoothPopulation solution s t
  have hpopulationNonneg : 0 ≤ population := by
    exact openVelocityH3DifferenceCubePopulation_nonneg solution s t
  have hcomponentSq : ∀ component : Fin 3,
      ‖stateDifference component‖ ^ 2 ≤ 3 * population := by
    intro component
    have hsingle : smoothSliceDerivativeCubeSquarePopulation
        difference hdifference hperiodic component ≤ population := by
      rw [hpopulation]
      exact Finset.single_le_sum
        (fun other _ ↦ smoothSliceDerivativeCubeSquarePopulation_nonneg
          difference hdifference hperiodic other)
        (Finset.mem_univ component)
    calc
      ‖stateDifference component‖ ^ 2 =
          ‖smoothSliceWeightedH3Component
            difference hdifference hperiodic component‖ ^ 2 := by
        rw [hstate]
        rfl
      _ ≤ 3 * smoothSliceDerivativeCubeSquarePopulation
            difference hdifference hperiodic component :=
        norm_sq_smoothSliceWeightedH3Component_le_cubePopulation
          difference hdifference hperiodic component
      _ ≤ 3 * population :=
        mul_le_mul_of_nonneg_left hsingle (by norm_num)
  have hstateNorm : ‖stateDifference‖ ≤ Real.sqrt (3 * population) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro component
    apply (sq_le_sq₀ (norm_nonneg _)
      (Real.sqrt_nonneg (3 * population))).mp
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hpopulationNonneg)]
    exact hcomponentSq component
  change ‖stateDifference‖ ^ 2 ≤ 3 * population
  calc
    ‖stateDifference‖ ^ 2 ≤ (Real.sqrt (3 * population)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (Real.sqrt_nonneg (3 * population))).mpr hstateNorm
    _ = 3 * population :=
      Real.sq_sqrt (mul_nonneg (by norm_num) hpopulationNonneg)

/-! ## Joint-spacetime continuity of the difference population -/

theorem continuous_compact_coordinateJet
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hbT : b < T)
    (n : ℕ) (word : Fin n → Fin 3) :
    Continuous (fun z : Icc a b × Space ↦
      coordinateJet velocity n word z.2 z.1.1) := by
  have habInterior : Icc a b ⊆ Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨ha.trans_le ht.1, ht.2.trans_lt hbT⟩
  let swap : Icc a b × Space → Space × ℝ := fun z ↦ (z.2, z.1.1)
  have hswap : Continuous swap :=
    continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)
  have hswapMem : ∀ z, swap z ∈ Set.univ ×ˢ Ioo (0 : ℝ) T := by
    rintro ⟨t, x⟩
    exact ⟨Set.mem_univ x, habInterior t.2⟩
  simpa only [coordinateJetField, Function.uncurry_apply_pair,
    swap, Function.comp_def] using
    (openPeriodicSolutionOn_coordinateJetField_contDiffOn solution n word).continuousOn
      |>.comp_continuous hswap hswapMem

/-- One coordinate-jet component difference has a continuous compact-cube square integral. -/
theorem continuous_compact_coordinateJetDifferenceIntegral
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hbT : b < T)
    (s : Icc a b) (n : ℕ) (word : Fin n → Fin 3) (component : Fin 3) :
    Continuous (fun t : Icc a b ↦
      ∫ x in unitCube,
        (coordinateJet velocity n word x t.1 -
          coordinateJet velocity n word x s.1) component ^ 2) := by
  have htime := continuous_compact_coordinateJet solution ha hbT n word
  have hbase : Continuous (fun z : Icc a b × Space ↦
      coordinateJet velocity n word z.2 s.1) := by
    have hsInterior : s.1 ∈ Ioo (0 : ℝ) T :=
      ⟨ha.trans_le s.2.1, s.2.2.trans_lt hbT⟩
    let embed : Icc a b × Space → Space × ℝ := fun z ↦ (z.2, s.1)
    have hembed : Continuous embed := continuous_snd.prodMk continuous_const
    have hembedMem : ∀ z, embed z ∈ Set.univ ×ˢ Ioo (0 : ℝ) T := by
      intro z
      exact ⟨Set.mem_univ z.2, hsInterior⟩
    simpa only [coordinateJetField, Function.uncurry_apply_pair,
      embed, Function.comp_def] using
      (openPeriodicSolutionOn_coordinateJetField_contDiffOn solution n word).continuousOn
        |>.comp_continuous hembed hembedMem
  have hdensity : Continuous (Function.uncurry
      (fun t : Icc a b ↦ fun x : Space ↦
        (coordinateJet velocity n word x t.1 -
          coordinateJet velocity n word x s.1) component ^ 2)) := by
    fun_prop
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  exact continuous_parametric_integral_of_continuous hdensity hcubeCompact

/-- The complete forty-face physical difference population varies continuously with the second
time face on any prescribed compact interior interval. -/
theorem continuous_openVelocityH3DifferenceCubePopulation_compact
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (s : Icc a b) :
    Continuous (fun t : Icc a b ↦
      openVelocityH3DifferenceCubePopulation velocity s.1 t.1) := by
  unfold openVelocityH3DifferenceCubePopulation
  apply continuous_finset_sum
  intro component _hcomponent
  have hzero : Continuous (fun t : Icc a b ↦
      ∫ x in unitCube,
        (velocity x t.1 component - velocity x s.1 component) ^ 2) := by
    simpa only [coordinateJet, iteratedFDeriv_zero_apply,
      Function.uncurry_apply_pair, Pi.sub_apply, PiLp.sub_apply] using
      continuous_compact_coordinateJetDifferenceIntegral
        solution ha hbT s 0 (fun i ↦ Fin.elim0 i) component
  have hone : Continuous (fun t : Icc a b ↦
      ∑ i : Fin 3, ∫ x in unitCube,
        (firstCoordinateJet velocity i x t.1 -
          firstCoordinateJet velocity i x s.1) component ^ 2) := by
    apply continuous_finset_sum
    intro i _hi
    simpa only [firstCoordinateJet, coordinateJetField] using
      continuous_compact_coordinateJetDifferenceIntegral
        solution ha hbT s 1 (firstCoordinateWord i) component
  have htwo : Continuous (fun t : Icc a b ↦
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x in unitCube,
        (secondCoordinateJet velocity i j x t.1 -
          secondCoordinateJet velocity i j x s.1) component ^ 2) := by
    apply continuous_finset_sum
    intro i _hi
    apply continuous_finset_sum
    intro j _hj
    simpa only [secondCoordinateJet, coordinateJetField] using
      continuous_compact_coordinateJetDifferenceIntegral
        solution ha hbT s 2 (secondCoordinateWord i j) component
  have hthree : Continuous (fun t : Icc a b ↦
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, ∫ x in unitCube,
        (thirdCoordinateJet velocity i j l x t.1 -
          thirdCoordinateJet velocity i j l x s.1) component ^ 2) := by
    apply continuous_finset_sum
    intro i _hi
    apply continuous_finset_sum
    intro j _hj
    apply continuous_finset_sum
    intro l _hl
    simpa only [thirdCoordinateJet, coordinateJetField] using
      continuous_compact_coordinateJetDifferenceIntegral
        solution ha hbT s 3 (thirdCoordinateWord i j l) component
  exact ((hzero.add hone).add htwo).add hthree

@[simp]
theorem openVelocityH3DifferenceCubePopulation_self
    (velocity : VelocityField) (s : ℝ) :
    openVelocityH3DifferenceCubePopulation velocity s s = 0 := by
  simp [openVelocityH3DifferenceCubePopulation]

/-- The actual native state on the prescribed absolute-time interval. -/
def compactOpenVelocityWeightedH3State
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hbT : b < T)
    (t : Icc a b) : PeriodicVectorWeightedSobolev 3 :=
  openVelocityWeightedH3State solution
    ⟨t.1, ha.trans_le t.2.1, t.2.2.trans_lt hbT⟩

/-- Joint smoothness plus the complete Parseval difference estimate makes the actual native state
norm-continuous on every preassigned compact interval inside the open lifespan. -/
theorem continuous_compactOpenVelocityWeightedH3State
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    Continuous (compactOpenVelocityWeightedH3State solution ha hbT) := by
  rw [continuous_iff_continuousAt]
  intro s
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let population : Icc a b → ℝ := fun t ↦
    openVelocityH3DifferenceCubePopulation velocity s.1 t.1
  have hpopulationContinuous : Continuous population :=
    continuous_openVelocityH3DifferenceCubePopulation_compact
      solution ha hab hbT s
  have hpopulationAt : population s = 0 := by
    simp [population]
  have hpopulationTendsto : Tendsto population (nhds s) (nhds 0) := by
    rw [← hpopulationAt]
    exact hpopulationContinuous.continuousAt
  let upper : Icc a b → ℝ := fun t ↦ Real.sqrt (3 * population t)
  have hupperTendsto : Tendsto upper (nhds s) (nhds 0) := by
    have hscaled : Tendsto (fun t ↦ 3 * population t) (nhds s) (nhds 0) := by
      simpa using tendsto_const_nhds.mul hpopulationTendsto
    change Tendsto
      ((fun x : ℝ ↦ Real.sqrt x) ∘ (fun t ↦ 3 * population t))
      (nhds s) (nhds 0)
    simpa only [Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hscaled
  refine squeeze_zero (fun t ↦ norm_nonneg _ ) (fun t ↦ ?_) hupperTendsto
  let sInterior : Ioo (0 : ℝ) T :=
    ⟨s.1, ha.trans_le s.2.1, s.2.2.trans_lt hbT⟩
  let tInterior : Ioo (0 : ℝ) T :=
    ⟨t.1, ha.trans_le t.2.1, t.2.2.trans_lt hbT⟩
  have hsquare :=
    norm_sq_openVelocityWeightedH3State_sub_le_differencePopulation
      solution sInterior tInterior
  have hpopulationNonneg : 0 ≤ population t := by
    exact openVelocityH3DifferenceCubePopulation_nonneg
      solution sInterior tInterior
  apply (sq_le_sq₀ (norm_nonneg _)
    (Real.sqrt_nonneg (3 * population t))).mp
  rw [Real.sq_sqrt (mul_nonneg (by norm_num) hpopulationNonneg)]
  simpa only [compactOpenVelocityWeightedH3State, population,
    sInterior, tInterior] using hsquare

/-! ## The clock-shifted actual path on the whole compact interval -/

/-- Translate the relative compact clock `[0, b - a]` into the addressed absolute interval
`[a,b]`. -/
def compactOpenWeightedTimeShift
    {a b : ℝ} (hab : a ≤ b) : C(Icc (0 : ℝ) (b - a), Icc a b) where
  toFun tau := ⟨a + tau.1, by
    constructor
    · linarith [tau.2.1]
    · linarith [tau.2.2]⟩
  continuous_toFun :=
    (continuous_const.add continuous_subtype_val).subtype_mk _

@[simp]
theorem compactOpenWeightedTimeShift_apply
    {a b : ℝ} (hab : a ≤ b) (tau : Icc (0 : ℝ) (b - a)) :
    (compactOpenWeightedTimeShift hab tau).1 = a + tau.1 :=
  rfl

/-- The actual open-solution slices, as one native continuous weighted `H³` path over the
entire prescribed relative interval. -/
noncomputable def compactOpenVelocityWeightedH3Path
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    WeightedH3Path (b - a) :=
  ⟨compactOpenVelocityWeightedH3State solution ha hbT ∘
      compactOpenWeightedTimeShift hab,
    (continuous_compactOpenVelocityWeightedH3State solution ha hab hbT).comp
      (compactOpenWeightedTimeShift hab).continuous⟩

@[simp]
theorem compactOpenVelocityWeightedH3Path_apply
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (tau : Icc (0 : ℝ) (b - a)) :
    compactOpenVelocityWeightedH3Path solution ha hab hbT tau =
      openVelocityWeightedH3State solution
        ⟨a + tau.1, by
          constructor
          · linarith [ha, tau.2.1]
          · linarith [tau.2.2, hbT]
        ⟩ :=
  rfl

/-- Reconstruction of the compact actual path returns the original physical velocity slice at
the translated clock face. -/
theorem reconstructedVelocity_compactOpenVelocityWeightedH3Path
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (tau : Icc (0 : ℝ) (b - a)) :
    reconstructedVelocity
        (compactOpenVelocityWeightedH3Path solution ha hab hbT tau) =
      (fun x ↦ velocity x (a + tau.1)) := by
  rw [compactOpenVelocityWeightedH3Path_apply]
  exact reconstructedVelocity_smoothSliceVectorWeightedH3
    (fun x ↦ velocity x (a + tau.1))
    (openPeriodicSolutionOn_velocitySlice_contDiff solution (by
      constructor
      · linarith [ha, tau.2.1]
      · linarith [tau.2.2, hbT]))
    (solution.velocityPeriodic (a + tau.1) (by
      constructor
      · linarith [ha, tau.2.1]
      · linarith [tau.2.2, hbT]))

/-- The exact projected quadratic source is continuous along the whole compact actual path. -/
theorem continuous_sharpNonlinearSource_compactOpenVelocityWeightedH3Path
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    Continuous (fun tau ↦ sharpNonlinearSource
      (compactOpenVelocityWeightedH3Path solution ha hab hbT tau)) := by
  have hsource : Continuous
      (fun state : PeriodicVectorWeightedSobolev 3 ↦
        weightedLerayDivergenceConvolutionContinuous state state) :=
    weightedLerayDivergenceConvolutionContinuous.continuous.clm_apply continuous_id
  exact hsource.comp
    (compactOpenVelocityWeightedH3Path solution ha hab hbT).continuous

/-! ## Exact serial propagation of the mild identity -/

/-- One locally fixed translated segment extends an already-established global mild identity
from its base face to every face of that segment.  This is the exact heat-semigroup/Volterra
gluing law used below. -/
theorem weightedMildMap_point_of_timeShift_fixed
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {L : ℝ} (hL : 0 ≤ L)
    (initial : PeriodicVectorWeightedSobolev 3)
    (path : WeightedH3Path L)
    {r S : ℝ} (hr : 0 ≤ r) (hS : 0 ≤ S) (hrS : r + S ≤ L)
    (hbase :
      weightedMildMap nu hnu hL initial path
          ⟨r, ⟨hr, by linarith [hrS, hS]⟩⟩ =
        path ⟨r, ⟨hr, by linarith [hrS, hS]⟩⟩)
    (hlocal : IsFixedPt
      (weightedMildMap nu hnu hS
        (path ⟨r, ⟨hr, by linarith [hrS, hS]⟩⟩))
      (weightedH3PathTimeShift path r S hr hrS))
    (tau : Icc (0 : ℝ) S) :
    weightedMildMap nu hnu hL initial path
        ⟨r + tau.1, by constructor <;> linarith [tau.2.1, tau.2.2, hrS]⟩ =
      path ⟨r + tau.1, by
        constructor <;> linarith [tau.2.1, tau.2.2, hrS]⟩ := by
  have hrL : r ∈ Icc (0 : ℝ) L :=
    ⟨hr, by linarith [hrS, hS]⟩
  have hrtL : r + tau.1 ∈ Icc (0 : ℝ) L := by
    constructor <;> linarith [tau.2.1, tau.2.2, hrS]
  have hlinear := weightedLinearHeatPath_add
    nu hL initial hr tau.2.1 hrtL.2
  have hreturn := weightedDuhamelReturn_add_eq_heat_add_timeShift
    nu hnu hL path hr hS hrS tau.2
  have hlocalAt := congrArg (fun candidate : WeightedH3Path S ↦ candidate tau) hlocal
  change
    periodicVectorWeightedHeat 3 nu (Real.toNNReal tau.1)
          (path ⟨r, hrL⟩) -
        weightedDuhamelReturn nu hnu hS
          (weightedH3PathTimeShift path r S hr hrS) tau.1 =
      path ⟨r + tau.1, hrtL⟩ at hlocalAt
  change
    weightedLinearHeatPath nu hL initial ⟨r + tau.1, hrtL⟩ -
        weightedDuhamelReturn nu hnu hL path (r + tau.1) =
      path ⟨r + tau.1, hrtL⟩
  rw [hlinear, hreturn]
  change
    periodicVectorWeightedHeat 3 nu (Real.toNNReal tau.1)
          (weightedLinearHeatPath nu hL initial ⟨r, hrL⟩) -
        (periodicVectorWeightedHeat 3 nu (Real.toNNReal tau.1)
            (weightedDuhamelReturn nu hnu hL path r) +
          weightedDuhamelReturn nu hnu hS
            (weightedH3PathTimeShift path r S hr hrS) tau.1) =
      path ⟨r + tau.1, hrtL⟩
  rw [show periodicVectorWeightedHeat 3 nu (Real.toNNReal tau.1)
      (weightedLinearHeatPath nu hL initial ⟨r, hrL⟩) -
        (periodicVectorWeightedHeat 3 nu (Real.toNNReal tau.1)
            (weightedDuhamelReturn nu hnu hL path r) +
          weightedDuhamelReturn nu hnu hS
            (weightedH3PathTimeShift path r S hr hrS) tau.1) =
      periodicVectorWeightedHeat 3 nu (Real.toNNReal tau.1)
          (weightedLinearHeatPath nu hL initial ⟨r, hrL⟩ -
            weightedDuhamelReturn nu hnu hL path r) -
        weightedDuhamelReturn nu hnu hS
          (weightedH3PathTimeShift path r S hr hrS) tau.1 by
    rw [(periodicVectorWeightedHeat 3 nu (Real.toNNReal tau.1)).map_sub]
    abel]
  rw [show weightedLinearHeatPath nu hL initial ⟨r, hrL⟩ -
      weightedDuhamelReturn nu hnu hL path r = path ⟨r, hrL⟩ by
    exact hbase]
  exact hlocalAt

/-- The same gluing calculation before collapsing the base defect: along a locally fixed
translated segment, the global mild defect is exactly heat transport of its base defect. -/
theorem weightedMildMap_defect_add_eq_heat_defect_of_timeShift_fixed
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {L : ℝ} (hL : 0 ≤ L)
    (initial : PeriodicVectorWeightedSobolev 3)
    (path : WeightedH3Path L)
    {r S : ℝ} (hr : 0 ≤ r) (hS : 0 ≤ S) (hrS : r + S ≤ L)
    (hlocal : IsFixedPt
      (weightedMildMap nu hnu hS
        (path ⟨r, ⟨hr, by linarith [hrS, hS]⟩⟩))
      (weightedH3PathTimeShift path r S hr hrS))
    (tau : Icc (0 : ℝ) S) :
    weightedMildMap nu hnu hL initial path
          ⟨r + tau.1, by
            constructor <;> linarith [tau.2.1, tau.2.2, hrS]⟩ -
        path ⟨r + tau.1, by
          constructor <;> linarith [tau.2.1, tau.2.2, hrS]⟩ =
      periodicVectorWeightedHeat 3 nu (Real.toNNReal tau.1)
        (weightedMildMap nu hnu hL initial path
            ⟨r, ⟨hr, by linarith [hrS, hS]⟩⟩ -
          path ⟨r, ⟨hr, by linarith [hrS, hS]⟩⟩) := by
  have hrL : r ∈ Icc (0 : ℝ) L :=
    ⟨hr, by linarith [hrS, hS]⟩
  have hrtL : r + tau.1 ∈ Icc (0 : ℝ) L := by
    constructor <;> linarith [tau.2.1, tau.2.2, hrS]
  have hlinear := weightedLinearHeatPath_add
    nu hL initial hr tau.2.1 hrtL.2
  have hreturn := weightedDuhamelReturn_add_eq_heat_add_timeShift
    nu hnu hL path hr hS hrS tau.2
  have hlocalAt := congrArg (fun candidate : WeightedH3Path S ↦ candidate tau) hlocal
  change
    periodicVectorWeightedHeat 3 nu (Real.toNNReal tau.1)
          (path ⟨r, hrL⟩) -
        weightedDuhamelReturn nu hnu hS
          (weightedH3PathTimeShift path r S hr hrS) tau.1 =
      path ⟨r + tau.1, hrtL⟩ at hlocalAt
  change
    (weightedLinearHeatPath nu hL initial ⟨r + tau.1, hrtL⟩ -
        weightedDuhamelReturn nu hnu hL path (r + tau.1)) -
      path ⟨r + tau.1, hrtL⟩ =
    periodicVectorWeightedHeat 3 nu (Real.toNNReal tau.1)
      ((weightedLinearHeatPath nu hL initial ⟨r, hrL⟩ -
          weightedDuhamelReturn nu hnu hL path r) - path ⟨r, hrL⟩)
  rw [hlinear, hreturn, ← hlocalAt]
  simp only [map_sub]
  abel

/-- Every diagonal native heat passage is injective: each exact Fourier multiplier is a
nonzero exponential. -/
theorem periodicVectorWeightedHeat_injective
    (order : ℕ) (nu t : ℝ≥0) :
    Function.Injective (periodicVectorWeightedHeat order nu t) := by
  intro left right heq
  funext component
  apply Subtype.ext
  funext k
  have hk := congrArg (fun state ↦ state component k) heq
  simp only [periodicVectorWeightedHeat, LinearMap.mkContinuous_apply] at hk
  have hmultiplier :
      (heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) ≠ 0 := by
    have hpositive :
        0 < heatStokesMultiplier (nu : ℝ) (t : ℝ) k := by
      unfold heatStokesMultiplier
      positivity
    exact_mod_cast ne_of_gt hpositive
  exact mul_left_cancel₀ hmultiplier hk

/-! ## A common local restart scale on one compact actual path -/

/-- Enlarging the common state cap can only shorten the explicit native restart clock. -/
theorem weightedRestartTimeFromCap_anti_cap
    {nu cap₁ cap₂ : ℝ} (hnu : 0 < nu)
    (hcap₁ : 0 ≤ cap₁) (hcap₂ : 0 ≤ cap₂) (hcaps : cap₁ ≤ cap₂) :
    weightedRestartTimeFromCap nu cap₂ ≤
      weightedRestartTimeFromCap nu cap₁ := by
  apply duhamelRestartTime_anti_load hnu
    (weightedRestartLoadFromCap_nonneg hcap₁)
    (weightedRestartLoadFromCap_nonneg hcap₂)
  unfold weightedRestartLoadFromCap weightedRestartRadiusFromCap
  exact mul_le_mul_of_nonneg_left (by linarith)
    weightedLerayCoefficient_nonneg

/-- A strictly positive common overlap scale for every restart base in one addressed compact
actual path.  It depends on that compact path norm and on the positive distance from `b` to the
open terminal face, and asserts no terminal-uniform bound. -/
noncomputable def compactOpenUniformOverlap
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) : ℝ :=
  min (T - b)
    (weightedRestartTimeFromCap nu
      ‖compactOpenVelocityWeightedH3Path solution ha hab hbT‖)

theorem compactOpenUniformOverlap_pos
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    0 < compactOpenUniformOverlap solution hnu ha hab hbT := by
  unfold compactOpenUniformOverlap
  exact lt_min (sub_pos.mpr hbT)
    (weightedRestartTimeFromCap_pos hnu
      (norm_nonneg (compactOpenVelocityWeightedH3Path solution ha hab hbT)))

/-- The common compact scale is below the actual state-dependent overlap at every relative base
face of the compact path. -/
theorem compactOpenUniformOverlap_le_openSliceNativeOverlap
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (r : Icc (0 : ℝ) (b - a)) :
    compactOpenUniformOverlap solution hnu ha hab hbT ≤
      openSliceNativeOverlap solution hnu
        ⟨a + r.1, by
          constructor
          · linarith [ha, r.2.1]
          · linarith [r.2.2, hbT]
        ⟩ := by
  let path := compactOpenVelocityWeightedH3Path solution ha hab hbT
  let t₀ : Ioo (0 : ℝ) T :=
    ⟨a + r.1, by
      constructor
      · linarith [ha, r.2.1]
      · linarith [r.2.2, hbT]
    ⟩
  have hstateNorm : ‖openVelocityWeightedH3State solution t₀‖ ≤ ‖path‖ := by
    simpa only [path, t₀, compactOpenVelocityWeightedH3Path_apply] using
      path.norm_coe_le_norm r
  have hclock : weightedRestartTimeFromCap nu ‖path‖ ≤
      weightedRestartTimeFromCap nu
        ‖openVelocityWeightedH3State solution t₀‖ :=
    weightedRestartTimeFromCap_anti_cap hnu
      (norm_nonneg _) (norm_nonneg _) hstateNorm
  have hremaining : T - b ≤ T - t₀.1 := by
    dsimp only [t₀]
    linarith [r.2.2]
  change min (T - b) (weightedRestartTimeFromCap nu ‖path‖) ≤
    min (T - t₀.1)
      (weightedRestartTimeFromCap nu
        ‖openVelocityWeightedH3State solution t₀‖)
  exact min_le_min hremaining hclock

/-- On every subsegment shorter than the actual overlap at its base, translating the one compact
path is exactly the local actual path already identified by restart overlap uniqueness. -/
theorem compactOpenVelocityWeightedH3Path_timeShift_eq_actualOpenWeightedH3Path
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    {r S : ℝ} (hr : 0 ≤ r) (hS : 0 ≤ S) (hrS : r + S ≤ b - a)
    (hSoverlap : S < openSliceNativeOverlap solution hnu
      ⟨a + r, by
        constructor
        · linarith [ha, hr]
        · linarith [hrS, hS, hbT]
      ⟩) :
    weightedH3PathTimeShift
        (compactOpenVelocityWeightedH3Path solution ha hab hbT)
        r S hr hrS =
      actualOpenWeightedH3Path solution hnu
        ⟨a + r, by
          constructor
          · linarith [ha, hr]
          · linarith [hrS, hS, hbT]
        ⟩ S hS hSoverlap := by
  apply ContinuousMap.ext
  intro tau
  rw [weightedH3PathTimeShift_apply,
    compactOpenVelocityWeightedH3Path_apply,
    actualOpenWeightedH3Path_apply]
  congr 2
  ring

/-- Hence every sufficiently short translated segment of the compact actual path satisfies its
own autonomous native mild recurrence, with the literal actual state at its base. -/
theorem compactOpenVelocityWeightedH3Path_timeShift_isFixedPt
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    {r S : ℝ} (hr : 0 ≤ r) (hS : 0 ≤ S) (hrS : r + S ≤ b - a)
    (hSoverlap : S < openSliceNativeOverlap solution hnu
      ⟨a + r, by
        constructor
        · linarith [ha, hr]
        · linarith [hrS, hS, hbT]
      ⟩) :
    IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu) hS
        ((compactOpenVelocityWeightedH3Path solution ha hab hbT)
          ⟨r, ⟨hr, by linarith [hrS, hS]⟩⟩))
      (weightedH3PathTimeShift
        (compactOpenVelocityWeightedH3Path solution ha hab hbT)
        r S hr hrS) := by
  rw [compactOpenVelocityWeightedH3Path_timeShift_eq_actualOpenWeightedH3Path
    solution hnu ha hab hbT hr hS hrS hSoverlap]
  simpa only [compactOpenVelocityWeightedH3Path_apply] using
    actualOpenWeightedH3Path_isFixedPt solution hnu
      ⟨a + r, by
        constructor
        · linarith [ha, hr]
        · linarith [hrS, hS, hbT]
      ⟩ S hS hSoverlap

/-! ## The global defect locus -/

/-- The whole-interval mild defect of the actual compact path, based at its left endpoint. -/
noncomputable def compactOpenWeightedMildDefect
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (tau : Icc (0 : ℝ) (b - a)) : PeriodicVectorWeightedSobolev 3 :=
  weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
      (sub_nonneg.mpr hab)
      (openVelocityWeightedH3State solution
        ⟨a, ha, lt_of_le_of_lt hab hbT⟩)
      (compactOpenVelocityWeightedH3Path solution ha hab hbT) tau -
    compactOpenVelocityWeightedH3Path solution ha hab hbT tau

theorem continuous_compactOpenWeightedMildDefect
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    Continuous (compactOpenWeightedMildDefect solution hnu ha hab hbT) := by
  exact
    ((weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
      (sub_nonneg.mpr hab)
      (openVelocityWeightedH3State solution
        ⟨a, ha, lt_of_le_of_lt hab hbT⟩)
      (compactOpenVelocityWeightedH3Path solution ha hab hbT)).continuous).sub
      (compactOpenVelocityWeightedH3Path solution ha hab hbT).continuous

@[simp]
theorem compactOpenWeightedMildDefect_zero
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    compactOpenWeightedMildDefect solution hnu ha hab hbT
      ⟨0, ⟨le_rfl, sub_nonneg.mpr hab⟩⟩ = 0 := by
  unfold compactOpenWeightedMildDefect
  rw [weightedMildMap_zero]
  rw [compactOpenVelocityWeightedH3Path_apply]
  apply sub_eq_zero.mpr
  congr 2
  norm_num

/-- On every segment shorter than the compact common overlap, the global defect is transported
exactly by the native heat passage. -/
theorem compactOpenWeightedMildDefect_add_eq_heat_defect
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    {r S : ℝ} (hr : 0 ≤ r) (hS : 0 ≤ S) (hrS : r + S ≤ b - a)
    (hScompact : S < compactOpenUniformOverlap solution hnu ha hab hbT)
    (tau : Icc (0 : ℝ) S) :
    compactOpenWeightedMildDefect solution hnu ha hab hbT
        ⟨r + tau.1, by
          constructor <;> linarith [tau.2.1, tau.2.2, hrS]⟩ =
      periodicVectorWeightedHeat 3 (Real.toNNReal nu) (Real.toNNReal tau.1)
        (compactOpenWeightedMildDefect solution hnu ha hab hbT
          ⟨r, ⟨hr, by linarith [hrS, hS]⟩⟩) := by
  let rFace : Icc (0 : ℝ) (b - a) :=
    ⟨r, ⟨hr, by linarith [hrS, hS]⟩⟩
  have hSoverlap : S < openSliceNativeOverlap solution hnu
      ⟨a + r, by
        constructor
        · linarith [ha, hr]
        · linarith [hrS, hS, hbT]
      ⟩ :=
    hScompact.trans_le
      (compactOpenUniformOverlap_le_openSliceNativeOverlap
        solution hnu ha hab hbT rFace)
  have hlocal := compactOpenVelocityWeightedH3Path_timeShift_isFixedPt
    solution hnu ha hab hbT hr hS hrS hSoverlap
  simpa only [compactOpenWeightedMildDefect] using
    weightedMildMap_defect_add_eq_heat_defect_of_timeShift_fixed
      (Real.toNNReal nu) (real_toNNReal_pos hnu)
      (sub_nonneg.mpr hab)
      (openVelocityWeightedH3State solution
        ⟨a, ha, lt_of_le_of_lt hab hbT⟩)
      (compactOpenVelocityWeightedH3Path solution ha hab hbT)
      hr hS hrS hlocal tau

/-- Within the common compact overlap radius, vanishing of the global defect is equivalent at
either time face.  Forward transport gives one direction; injectivity of the exact heat passage
gives the reverse direction. -/
theorem compactOpenWeightedMildDefect_eq_zero_iff_of_dist_lt
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (s t : Icc (0 : ℝ) (b - a))
    (hdist : dist s t < compactOpenUniformOverlap solution hnu ha hab hbT) :
    compactOpenWeightedMildDefect solution hnu ha hab hbT s = 0 ↔
      compactOpenWeightedMildDefect solution hnu ha hab hbT t = 0 := by
  by_cases hst : s.1 ≤ t.1
  · let S : ℝ := t.1 - s.1
    have hS : 0 ≤ S := sub_nonneg.mpr hst
    have hsS : s.1 + S ≤ b - a := by
      dsimp only [S]
      linarith [t.2.2]
    have hScompact : S < compactOpenUniformOverlap solution hnu ha hab hbT := by
      simpa only [S, Subtype.dist_eq, Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hdist
    let tau : Icc (0 : ℝ) S := ⟨S, hS, le_rfl⟩
    have htransport := compactOpenWeightedMildDefect_add_eq_heat_defect
      solution hnu ha hab hbT s.2.1 hS hsS hScompact tau
    have hend : t =
        (⟨s.1 + tau.1, by
          constructor
          · exact add_nonneg s.2.1 tau.2.1
          · linarith [tau.2.2, hsS]⟩ :
          Icc (0 : ℝ) (b - a)) := by
      apply Subtype.ext
      dsimp only [S, tau]
      ring
    have hstart : s =
        (⟨s.1, s.2⟩ : Icc (0 : ℝ) (b - a)) := by rfl
    have htransport' :
        compactOpenWeightedMildDefect solution hnu ha hab hbT t =
          periodicVectorWeightedHeat 3 (Real.toNNReal nu) (Real.toNNReal S)
            (compactOpenWeightedMildDefect solution hnu ha hab hbT s) := by
      calc
        compactOpenWeightedMildDefect solution hnu ha hab hbT t =
            compactOpenWeightedMildDefect solution hnu ha hab hbT
              ⟨s.1 + tau.1, by
                constructor
                · exact add_nonneg s.2.1 tau.2.1
                · linarith [tau.2.2, hsS]⟩ :=
          congrArg _ hend
        _ = periodicVectorWeightedHeat 3 (Real.toNNReal nu)
              (Real.toNNReal tau.1)
              (compactOpenWeightedMildDefect solution hnu ha hab hbT
                ⟨s.1, s.2⟩) := htransport
        _ = periodicVectorWeightedHeat 3 (Real.toNNReal nu)
              (Real.toNNReal S)
              (compactOpenWeightedMildDefect solution hnu ha hab hbT s) := by
          subst tau
          exact congrArg _ (congrArg _ hstart.symm)
    constructor
    · intro hs
      rw [htransport', hs, map_zero]
    · intro ht
      apply periodicVectorWeightedHeat_injective
        3 (Real.toNNReal nu) (Real.toNNReal S)
      rw [map_zero, ← htransport', ht]
  · have hts : t.1 ≤ s.1 := le_of_not_ge hst
    let S : ℝ := s.1 - t.1
    have hS : 0 ≤ S := sub_nonneg.mpr hts
    have htS : t.1 + S ≤ b - a := by
      dsimp only [S]
      linarith [s.2.2]
    have hScompact : S < compactOpenUniformOverlap solution hnu ha hab hbT := by
      have hdist' : dist t s <
          compactOpenUniformOverlap solution hnu ha hab hbT := by
        simpa only [dist_comm] using hdist
      simpa only [S, Subtype.dist_eq, Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr hts), neg_sub] using hdist'
    let tau : Icc (0 : ℝ) S := ⟨S, hS, le_rfl⟩
    have htransport := compactOpenWeightedMildDefect_add_eq_heat_defect
      solution hnu ha hab hbT t.2.1 hS htS hScompact tau
    have hend : s =
        (⟨t.1 + tau.1, by
          constructor
          · exact add_nonneg t.2.1 tau.2.1
          · linarith [tau.2.2, htS]⟩ :
          Icc (0 : ℝ) (b - a)) := by
      apply Subtype.ext
      dsimp only [S, tau]
      ring
    have hstart : t =
        (⟨t.1, t.2⟩ : Icc (0 : ℝ) (b - a)) := by rfl
    have htransport' :
        compactOpenWeightedMildDefect solution hnu ha hab hbT s =
          periodicVectorWeightedHeat 3 (Real.toNNReal nu) (Real.toNNReal S)
            (compactOpenWeightedMildDefect solution hnu ha hab hbT t) := by
      calc
        compactOpenWeightedMildDefect solution hnu ha hab hbT s =
            compactOpenWeightedMildDefect solution hnu ha hab hbT
              ⟨t.1 + tau.1, by
                constructor
                · exact add_nonneg t.2.1 tau.2.1
                · linarith [tau.2.2, htS]⟩ :=
          congrArg _ hend
        _ = periodicVectorWeightedHeat 3 (Real.toNNReal nu)
              (Real.toNNReal tau.1)
              (compactOpenWeightedMildDefect solution hnu ha hab hbT
                ⟨t.1, t.2⟩) := htransport
        _ = periodicVectorWeightedHeat 3 (Real.toNNReal nu)
              (Real.toNNReal S)
              (compactOpenWeightedMildDefect solution hnu ha hab hbT t) := by
          subst tau
          exact congrArg _ (congrArg _ hstart.symm)
    constructor
    · intro hs
      apply periodicVectorWeightedHeat_injective
        3 (Real.toNNReal nu) (Real.toNNReal S)
      rw [map_zero, ← htransport', hs]
    · intro ht
      rw [htransport', ht, map_zero]

/-- The zero-defect locus is nonempty, closed by continuity, and open because every point carries
the same positive compact restart radius and defect vanishing transports in both directions.
Preconnectedness of the closed interval therefore makes the defect vanish everywhere. -/
theorem compactOpenWeightedMildDefect_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (tau : Icc (0 : ℝ) (b - a)) :
    compactOpenWeightedMildDefect solution hnu ha hab hbT tau = 0 := by
  let defect := compactOpenWeightedMildDefect solution hnu ha hab hbT
  let good : Set (Icc (0 : ℝ) (b - a)) := {t | defect t = 0}
  let delta := compactOpenUniformOverlap solution hnu ha hab hbT
  have hdelta : 0 < delta :=
    compactOpenUniformOverlap_pos solution hnu ha hab hbT
  have hclosed : IsClosed good := by
    exact isClosed_eq
      (continuous_compactOpenWeightedMildDefect solution hnu ha hab hbT)
      continuous_const
  have hopen : IsOpen good := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    refine Filter.mem_of_superset (Metric.ball_mem_nhds t hdelta) ?_
    intro s hs
    have hdist : dist s t <
        compactOpenUniformOverlap solution hnu ha hab hbT := by
      simpa only [delta, Metric.mem_ball] using hs
    change compactOpenWeightedMildDefect solution hnu ha hab hbT s = 0
    apply (compactOpenWeightedMildDefect_eq_zero_iff_of_dist_lt
      solution hnu ha hab hbT s t hdist).mpr
    exact ht
  letI : PreconnectedSpace (Icc (0 : ℝ) (b - a)) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  have hzero :
      (⟨0, ⟨le_rfl, sub_nonneg.mpr hab⟩⟩ :
        Icc (0 : ℝ) (b - a)) ∈ good := by
    exact compactOpenWeightedMildDefect_zero solution hnu ha hab hbT
  have hgood : good = Set.univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨_, hzero⟩
  have htau : tau ∈ good := by
    rw [hgood]
    exact Set.mem_univ tau
  exact htau

/-- **Whole compact-interval fixed-point identity.**  The single actual weighted `H³` path on
`[a,b]` satisfies the complete native heat/Duhamel recurrence based at the actual left slice. -/
theorem compactOpenVelocityWeightedH3Path_isFixedPt
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
        (sub_nonneg.mpr hab)
        (openVelocityWeightedH3State solution
          ⟨a, ha, lt_of_le_of_lt hab hbT⟩))
      (compactOpenVelocityWeightedH3Path solution ha hab hbT) := by
  apply ContinuousMap.ext
  intro tau
  exact sub_eq_zero.mp
    (compactOpenWeightedMildDefect_eq_zero
      solution hnu ha hab hbT tau)

section Audit

#print axioms norm_sq_openVelocityWeightedH3State_sub_le_differencePopulation
#print axioms continuous_compactOpenVelocityWeightedH3State
#print axioms compactOpenVelocityWeightedH3Path
#print axioms reconstructedVelocity_compactOpenVelocityWeightedH3Path
#print axioms continuous_sharpNonlinearSource_compactOpenVelocityWeightedH3Path
#print axioms weightedMildMap_defect_add_eq_heat_defect_of_timeShift_fixed
#print axioms periodicVectorWeightedHeat_injective
#print axioms compactOpenWeightedMildDefect_eq_zero
#print axioms compactOpenVelocityWeightedH3Path_isFixedPt

end Audit

end Soma.Holonics.Millennium.NavierStokesOpenCompactWeightedPath
