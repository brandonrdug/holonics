import ElementaryHolonics.Millennium.NavierStokesAdaptiveRectangleH3Service
import ElementaryHolonics.Millennium.NavierStokesOpenH2EnergyH3Dissipation
import ElementaryHolonics.Millennium.NavierStokesTranslationDissipation

/-!
# The native weighted H3 current in the coordinate H2--H3 energy chart

**[proved-derived; formal-checked]** This file identifies the order-three spatial population
which was present under two different receiver charts.  The nine order-two coordinate words each
return three gradient directions; `Fin.consEquiv` reindexes those twenty-seven caused occurrences
as the complete order-three coordinate-word population.  Consequently the native weighted
Fourier `H3` square is paid pointwise by the literal coordinate `H2` storage plus the coordinate
`H3` viscous current.  The order-zero/mean mode remains in `coordinateH2Energy` and is never
renamed as dissipation.

The compact-time theorem then integrates this pointwise comparison and composes it with the exact
coordinate `H2` balance.  Its only remaining source-specific payment is the signed nonlinear
production integral already exposed by that balance; no endpoint-uniform estimate is asserted.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Real Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesWeightedH3CoordinateDissipationBridge

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearSourceSquareOwner
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH2Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH3MiddleRedistribution
open Soma.Holonics.Millennium.NavierStokesCoordinateH3Production
open Soma.Holonics.Millennium.NavierStokesCoordinateLowerEnergyEstimate
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenH2EnergyH3Dissipation
open Soma.Holonics.Millennium.NavierStokesOpenEnergySpacetime
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTranslationDissipation
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The twenty-seven-word coordinate reindexing -/

/-- The gradient square of one order-two word is exactly the three addressed order-three square
populations obtained by prepending one coordinate direction. -/
theorem openPeriodicSolutionOn_orderTwoWordGradient_eq_thirdWordMassSum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (word : Fin 2 → Fin 3) :
    (∫ x in unitCube, ∑ component : Fin 3,
        ‖gradient (fun y ↦ coordinateJet velocity 2 word y t component) x‖ ^ 2) =
      ∑ coordinate : Fin 3,
        thirdWordSquareMass (fun y ↦ velocity y t)
          coordinate (word 0) (word 1) := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let second : InitialVelocity := fun y ↦ coordinateJet velocity 2 word y t
  have hword : word = secondCoordinateWord (word 0) (word 1) := by
    funext q
    fin_cases q <;> rfl
  have hsecond : ContDiff ℝ ∞ second :=
    openPeriodicSolutionOn_coordinateJetSlice_contDiff solution ht 2 word
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have htermIntegrable : ∀ component coordinate : Fin 3,
      IntegrableOn
        (fun x ↦
          (spatialDirectionalJet second coordinate x component) ^ 2)
        unitCube := by
    intro component coordinate
    have hsmooth : ContDiff ℝ ∞
        (fun x ↦ spatialDirectionalJet second coordinate x component) := by
      simpa [Function.comp_def] using
        (EuclideanSpace.proj component).contDiff.comp
          (spatialDirectionalJet_contDiff second hsecond coordinate)
    exact (hsmooth.pow 2).continuous.continuousOn.integrableOn_compact hcubeCompact
  calc
    (∫ x in unitCube, ∑ component : Fin 3,
        ‖gradient (fun y ↦ coordinateJet velocity 2 word y t component) x‖ ^ 2) =
      ∫ x in unitCube, ∑ component : Fin 3, ∑ coordinate : Fin 3,
        (spatialDirectionalJet second coordinate x component) ^ 2 := by
        apply setIntegral_congr_fun hcubeCompact.measurableSet
        intro x _hx
        apply Finset.sum_congr rfl
        intro component _hcomponent
        exact norm_gradient_component_sq_eq_sum_spatialDirectionalJet
          second hsecond component x
    _ = ∑ component : Fin 3, ∑ coordinate : Fin 3,
        ∫ x in unitCube,
          (spatialDirectionalJet second coordinate x component) ^ 2 := by
        rw [integral_finsetSum Finset.univ]
        · apply Finset.sum_congr rfl
          intro component _hcomponent
          rw [integral_finsetSum Finset.univ]
          intro coordinate _hcoordinate
          exact htermIntegrable component coordinate
        · intro component _hcomponent
          exact integrable_finsetSum Finset.univ
            (fun coordinate _hcoordinate ↦ htermIntegrable component coordinate)
    _ = ∑ coordinate : Fin 3, ∑ component : Fin 3,
        ∫ x in unitCube,
          (spatialDirectionalJet second coordinate x component) ^ 2 := by
        rw [Finset.sum_comm]
    _ = ∑ coordinate : Fin 3,
        thirdWordSquareMass u coordinate (word 0) (word 1) := by
        apply Finset.sum_congr rfl
        intro coordinate _hcoordinate
        unfold thirdWordSquareMass
        apply Finset.sum_congr rfl
        intro component _hcomponent
        apply setIntegral_congr_fun hcubeCompact.measurableSet
        intro x _hx
        dsimp [second, u]
        rw [hword]
        have hderiv :
            spatialDirectionalJet
                (fun y ↦ secondCoordinateJet velocity (word 0) (word 1) y t)
                coordinate x =
              thirdSpatialCoordinateJet (fun y ↦ velocity y t)
                coordinate (word 0) (word 1) x := by
          calc
            _ = thirdCoordinateJet velocity coordinate (word 0) (word 1) x t :=
              (openPeriodicSolutionOn_thirdCoordinateJet_eq_spatialDerivative_secondCoordinateJet
                solution ht x coordinate (word 0) (word 1)).symm
            _ = _ :=
              openPeriodicSolutionOn_thirdCoordinateJet_eq_thirdSpatialCoordinateJet
                solution ht x coordinate (word 0) (word 1)
        exact congrArg (fun z : Space ↦ (z component) ^ 2) hderiv

/-- The complete order-two gradient current is exactly the complete order-three square mass.  The
equivalence retains the prepended coordinate as the first letter and the old word as its tail. -/
theorem openPeriodicSolutionOn_coordinateH2Dissipation_eq_thirdOrderSquareMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    coordinateH2Dissipation velocity t =
      thirdOrderSquareMass (fun y ↦ velocity y t) := by
  have hword := openPeriodicSolutionOn_orderTwoWordGradient_eq_thirdWordMassSum
    solution ht
  unfold coordinateH2Dissipation thirdOrderSquareMass
  calc
    (∑ word : Fin 2 → Fin 3,
        ∫ x in unitCube, ∑ component : Fin 3,
          ‖gradient (fun y ↦ coordinateJet velocity 2 word y t component) x‖ ^ 2) =
      ∑ word : Fin 2 → Fin 3, ∑ coordinate : Fin 3,
        thirdWordSquareMass (fun y ↦ velocity y t)
          coordinate (word 0) (word 1) := by
        apply Finset.sum_congr rfl
        intro word _hword
        exact hword word
    _ = ∑ coordinate : Fin 3, ∑ word : Fin 2 → Fin 3,
        thirdWordSquareMass (fun y ↦ velocity y t)
          coordinate (word 0) (word 1) := by
        rw [Finset.sum_comm]
    _ = ∑ pair : Fin 3 × (Fin 2 → Fin 3),
        thirdWordSquareMass (fun y ↦ velocity y t)
          pair.1 (pair.2 0) (pair.2 1) := by
        rw [Fintype.sum_prod_type]
    _ = ∑ word : Fin 3 → Fin 3,
        thirdWordSquareMass (fun y ↦ velocity y t)
          (word 0) (word 1) (word 2) := by
        let e : (Fin 3 × (Fin 2 → Fin 3)) ≃ (Fin 3 → Fin 3) :=
          Fin.consEquiv (fun _ : Fin 3 ↦ Fin 3)
        exact Fintype.sum_equiv e _ _ (fun pair ↦ by
          simp [e, Fin.consEquiv]
          have hlast :
              (Fin.cons pair.1 pair.2 : Fin 3 → Fin 3) (Fin.succ (1 : Fin 2)) =
                pair.2 1 := by simp only [Fin.cons_succ]
          change (Fin.cons pair.1 pair.2 : Fin 3 → Fin 3) 2 = pair.2 1 at hlast
          rw [hlast])

/-! ## Pointwise weighted-H3 comparison -/

/-- The complete coordinate `H3` energy splits into the literal `H2` storage and its order-three
face.  This is only a finite dependent-sum decomposition. -/
theorem coordinateH3Energy_eq_coordinateH2Energy_add_orderEnergy
    (velocity : VelocityField) (t : ℝ) :
    coordinateH3Energy velocity t =
      coordinateH2Energy velocity t + coordinateH3OrderEnergy velocity t := by
  unfold coordinateH3Energy coordinateH2Energy coordinateH3OrderEnergy
  simp [Fin.sum_univ_succ, add_assoc]

/-- The top coordinate energy is exactly half the order-two gradient dissipation. -/
theorem openPeriodicSolutionOn_two_mul_coordinateH3OrderEnergy_eq_coordinateH2Dissipation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    2 * coordinateH3OrderEnergy velocity t = coordinateH2Dissipation velocity t := by
  calc
    2 * coordinateH3OrderEnergy velocity t =
        thirdOrderSquareMass (fun y ↦ velocity y t) :=
      (openPeriodicSolutionOn_thirdOrderSquareMass_eq_two_mul_orderEnergy
        solution ht).symm
    _ = coordinateH2Dissipation velocity t :=
      (openPeriodicSolutionOn_coordinateH2Dissipation_eq_thirdOrderSquareMass
        solution ht).symm

/-- Exact normalization of the comparison: the top-order coordinate storage is one half of the
order-two gradient current. -/
theorem openPeriodicSolutionOn_coordinateH3Energy_eq_H2Energy_add_half_H2Dissipation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    coordinateH3Energy velocity t =
      coordinateH2Energy velocity t + (2 : ℝ)⁻¹ * coordinateH2Dissipation velocity t := by
  rw [coordinateH3Energy_eq_coordinateH2Energy_add_orderEnergy]
  have htop :=
    openPeriodicSolutionOn_two_mul_coordinateH3OrderEnergy_eq_coordinateH2Dissipation
      solution ht
  linarith

/-- Sharp pointwise bridge before the lower-order viscous currents are added. -/
theorem openPeriodicSolutionOn_norm_sq_openVelocityWeightedH3State_le_exact_H2_chart
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (time : Ioo 0 T) :
    ‖openVelocityWeightedH3State solution time‖ ^ 2 ≤
      240 * (coordinateH2Energy velocity time.1 +
        (2 : ℝ)⁻¹ * coordinateH2Dissipation velocity time.1) := by
  have hweighted := openPeriodicSolutionOn_norm_sq_smoothSliceVectorWeightedH3_le
    solution time.2
  change ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x time.1)
      (openPeriodicSolutionOn_velocitySlice_contDiff solution time.2)
      (solution.velocityPeriodic time.1 ⟨time.2.1.le, time.2.2⟩)‖ ^ 2 ≤ _
  calc
    _ ≤ 240 * coordinateH3Energy velocity time.1 := hweighted
    _ = 240 * (coordinateH2Energy velocity time.1 +
        (2 : ℝ)⁻¹ * coordinateH2Dissipation velocity time.1) := by
      rw [openPeriodicSolutionOn_coordinateH3Energy_eq_H2Energy_add_half_H2Dissipation
        solution time.2]

/-- The native weighted Fourier `H3` state is controlled by the exact storage plus viscous
coordinate current.  The mean mode is paid by `coordinateH2Energy`; only the third-order face is
paid by dissipation. -/
theorem openPeriodicSolutionOn_norm_sq_openVelocityWeightedH3State_le_storage_add_dissipation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (time : Ioo 0 T) :
    ‖openVelocityWeightedH3State solution time‖ ^ 2 ≤
      240 * (coordinateH2Energy velocity time.1 +
        coordinateH3ViscousDissipation velocity time.1) := by
  have hweighted := openPeriodicSolutionOn_norm_sq_smoothSliceVectorWeightedH3_le
    solution time.2
  have hsplit := coordinateH3Energy_eq_coordinateH2Energy_add_orderEnergy
    velocity time.1
  have htop :=
    openPeriodicSolutionOn_two_mul_coordinateH3OrderEnergy_eq_coordinateH2Dissipation
      solution time.2
  have hD2 : coordinateH2Dissipation velocity time.1 ≤
      coordinateH3ViscousDissipation velocity time.1 := by
    unfold coordinateH3ViscousDissipation
    have h0 := coordinateH0Dissipation_nonneg velocity time.1
    have h1 := coordinateH1Dissipation_nonneg velocity time.1
    linarith
  have htopNonneg : 0 ≤ coordinateH3OrderEnergy velocity time.1 := by
    unfold coordinateH3OrderEnergy
    exact Finset.sum_nonneg (fun word _hword ↦
      periodicKineticEnergy_nonneg (coordinateJetField velocity 3 word) time.1)
  change ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x time.1)
      (openPeriodicSolutionOn_velocitySlice_contDiff solution time.2)
      (solution.velocityPeriodic time.1 ⟨time.2.1.le, time.2.2⟩)‖ ^ 2 ≤ _
  calc
    _ ≤ 240 * coordinateH3Energy velocity time.1 := hweighted
    _ = 240 * (coordinateH2Energy velocity time.1 +
        coordinateH3OrderEnergy velocity time.1) := by rw [hsplit]
    _ ≤ 240 * (coordinateH2Energy velocity time.1 +
        coordinateH3ViscousDissipation velocity time.1) := by
      gcongr
      linarith [htopNonneg]

/-! ## Compact-time bridge and exact H2-balance composition -/

/-- On the unclamped compact interval the native square current has the same sharp coordinate
payment. -/
theorem compactOpenVelocityWeightedH3SquareCurrent_le_exact_H2_chart
    {T nu a b sourceTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hsourceTime : sourceTime ∈ Icc a b) :
    compactOpenVelocityWeightedH3SquareCurrent solution ha hab hbT sourceTime ≤
      240 * (coordinateH2Energy velocity sourceTime +
        (2 : ℝ)⁻¹ * coordinateH2Dissipation velocity sourceTime) := by
  have hinterior :
      compactInteriorTime ha hab hbT sourceTime =
        (⟨sourceTime, ha.trans_le hsourceTime.1,
          hsourceTime.2.trans_lt hbT⟩ : Ioo (0 : ℝ) T) := by
    apply Subtype.ext
    exact compactInteriorTime_eq ha hab hbT hsourceTime
  unfold compactOpenVelocityWeightedH3SquareCurrent
  rw [hinterior]
  exact openPeriodicSolutionOn_norm_sq_openVelocityWeightedH3State_le_exact_H2_chart
    solution ⟨sourceTime, ha.trans_le hsourceTime.1, hsourceTime.2.trans_lt hbT⟩

/-- The integrable full-dissipation face of the compact pointwise bridge. -/
theorem compactOpenVelocityWeightedH3SquareCurrent_le_H2_storage_add_H3_dissipation
    {T nu a b sourceTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hsourceTime : sourceTime ∈ Icc a b) :
    compactOpenVelocityWeightedH3SquareCurrent solution ha hab hbT sourceTime ≤
      240 * (coordinateH2Energy velocity sourceTime +
        coordinateH3ViscousDissipation velocity sourceTime) := by
  have hinterior :
      compactInteriorTime ha hab hbT sourceTime =
        (⟨sourceTime, ha.trans_le hsourceTime.1,
          hsourceTime.2.trans_lt hbT⟩ : Ioo (0 : ℝ) T) := by
    apply Subtype.ext
    exact compactInteriorTime_eq ha hab hbT hsourceTime
  unfold compactOpenVelocityWeightedH3SquareCurrent
  rw [hinterior]
  exact openPeriodicSolutionOn_norm_sq_openVelocityWeightedH3State_le_storage_add_dissipation
    solution ⟨sourceTime, ha.trans_le hsourceTime.1, hsourceTime.2.trans_lt hbT⟩

/-- Integrated compact native current.  The mean/low modes remain in the storage integral, while
the complete coordinate viscous current is exposed as the balance-compatible payment. -/
theorem integral_compactOpenVelocityWeightedH3SquareCurrent_le_H2_storage_add_H3_dissipation
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    (∫ time in a..b,
        compactOpenVelocityWeightedH3SquareCurrent solution ha hab hbT time) ≤
      240 * ((∫ time in a..b, coordinateH2Energy velocity time) +
        ∫ time in a..b, coordinateH3ViscousDissipation velocity time) := by
  have hcurrentInt : IntervalIntegrable
      (compactOpenVelocityWeightedH3SquareCurrent solution ha hab hbT) volume a b :=
    (continuous_compactOpenVelocityWeightedH3SquareCurrent
      solution ha hab hbT).intervalIntegrable a b
  have henergyContinuousOn : ContinuousOn (coordinateH2Energy velocity) (Icc a b) := by
    intro time htime
    exact (openPeriodicSolutionOn_hasDerivAt_coordinateH2Energy solution
      ⟨ha.trans_le htime.1, htime.2.trans_lt hbT⟩).continuousAt.continuousWithinAt
  have henergyInt : IntervalIntegrable (coordinateH2Energy velocity) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact henergyContinuousOn.integrableOn_compact isCompact_Icc
  have hdissInt : IntervalIntegrable
      (coordinateH3ViscousDissipation velocity) volume a b :=
    openPeriodicSolutionOn_coordinateH3ViscousDissipation_intervalIntegrable
      solution ha hab hbT
  have hrightInt : IntervalIntegrable
      (fun time ↦ 240 * (coordinateH2Energy velocity time +
        coordinateH3ViscousDissipation velocity time)) volume a b :=
    (henergyInt.add hdissInt).const_mul 240
  have hmono := intervalIntegral.integral_mono_on hab hcurrentInt hrightInt
    (fun time htime ↦
      compactOpenVelocityWeightedH3SquareCurrent_le_H2_storage_add_H3_dissipation
        solution ha hab hbT htime)
  calc
    (∫ time in a..b,
        compactOpenVelocityWeightedH3SquareCurrent solution ha hab hbT time) ≤
      ∫ time in a..b, 240 * (coordinateH2Energy velocity time +
        coordinateH3ViscousDissipation velocity time) := hmono
    _ = 240 * ((∫ time in a..b, coordinateH2Energy velocity time) +
        ∫ time in a..b, coordinateH3ViscousDissipation velocity time) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add henergyInt hdissInt]

/-- Composition with the exact coordinate `H2` law.  The endpoint storage and signed nonlinear
production are displayed without an absolute-value relaxation; the time-integrated `H2` storage
is retained because the balance controls dissipation, not this storage occupation current. -/
theorem integral_compactOpenVelocityWeightedH3SquareCurrent_le_of_exact_H2_balance
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    (∫ time in a..b,
        compactOpenVelocityWeightedH3SquareCurrent solution ha hab hbT time) ≤
      240 * ((∫ time in a..b, coordinateH2Energy velocity time) +
        nu⁻¹ * (coordinateH2Energy velocity a +
          (∫ time in a..b, coordinateH2NonlinearProductionCurrent velocity time) -
          coordinateH2Energy velocity b)) := by
  have hbridge :=
    integral_compactOpenVelocityWeightedH3SquareCurrent_le_H2_storage_add_H3_dissipation
      solution ha hab hbT
  have hbalance := openPeriodicSolutionOn_coordinateH2Energy_add_H3Dissipation_eq
    solution ha hab hbT
  have hdissipationEq :
      (∫ time in a..b, coordinateH3ViscousDissipation velocity time) =
        nu⁻¹ * (coordinateH2Energy velocity a +
          (∫ time in a..b, coordinateH2NonlinearProductionCurrent velocity time) -
          coordinateH2Energy velocity b) := by
    calc
      (∫ time in a..b, coordinateH3ViscousDissipation velocity time) =
          nu⁻¹ * (nu *
            ∫ time in a..b, coordinateH3ViscousDissipation velocity time) := by
        field_simp
      _ = nu⁻¹ * (coordinateH2Energy velocity a +
          (∫ time in a..b, coordinateH2NonlinearProductionCurrent velocity time) -
          coordinateH2Energy velocity b) := by
        congr 1
        linarith
  rw [hdissipationEq] at hbridge
  exact hbridge

/-- Source-specific corollary: an admitted upper budget for the signed nonlinear production
replaces the exact dissipation term.  The storage-occupation integral remains a separate payment. -/
theorem integral_compactOpenVelocityWeightedH3SquareCurrent_le_of_productionBudget
    {T nu a b productionBudget : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hproduction :
      (∫ time in a..b, coordinateH2NonlinearProductionCurrent velocity time) ≤
        productionBudget) :
    (∫ time in a..b,
        compactOpenVelocityWeightedH3SquareCurrent solution ha hab hbT time) ≤
      240 * ((∫ time in a..b, coordinateH2Energy velocity time) +
        nu⁻¹ * (coordinateH2Energy velocity a + productionBudget)) := by
  have hbridge :=
    integral_compactOpenVelocityWeightedH3SquareCurrent_le_H2_storage_add_H3_dissipation
      solution ha hab hbT
  have hdissipation :=
    openPeriodicSolutionOn_integral_coordinateH3ViscousDissipation_le_of_production
      solution hnu ha hab hbT hproduction
  calc
    (∫ time in a..b,
        compactOpenVelocityWeightedH3SquareCurrent solution ha hab hbT time) ≤
      240 * ((∫ time in a..b, coordinateH2Energy velocity time) +
        ∫ time in a..b, coordinateH3ViscousDissipation velocity time) := hbridge
    _ ≤ 240 * ((∫ time in a..b, coordinateH2Energy velocity time) +
        nu⁻¹ * (coordinateH2Energy velocity a + productionBudget)) := by
      gcongr

section Audit

#print axioms openPeriodicSolutionOn_coordinateH2Dissipation_eq_thirdOrderSquareMass
#print axioms coordinateH3Energy_eq_coordinateH2Energy_add_orderEnergy
#print axioms
  openPeriodicSolutionOn_coordinateH3Energy_eq_H2Energy_add_half_H2Dissipation
#print axioms
  openPeriodicSolutionOn_norm_sq_openVelocityWeightedH3State_le_exact_H2_chart
#print axioms
  openPeriodicSolutionOn_norm_sq_openVelocityWeightedH3State_le_storage_add_dissipation
#print axioms
  integral_compactOpenVelocityWeightedH3SquareCurrent_le_H2_storage_add_H3_dissipation
#print axioms
  integral_compactOpenVelocityWeightedH3SquareCurrent_le_of_exact_H2_balance
#print axioms
  integral_compactOpenVelocityWeightedH3SquareCurrent_le_of_productionBudget

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedH3CoordinateDissipationBridge
