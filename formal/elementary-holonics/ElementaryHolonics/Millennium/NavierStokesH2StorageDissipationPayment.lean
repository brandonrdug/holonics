import ElementaryHolonics.Millennium.NavierStokesWeightedH3CoordinateDissipationBridge

/-!
# Exact payment of the coordinate H2 storage occupation

**[proved-derived; formal-checked]** The lower derivative faces of `coordinateH2Energy` do not
require a Poincare hypothesis.  On every strict-interior solution slice, their addressed
coordinate occurrences are exactly one half of the order-zero and order-one viscous populations.
The undifferentiated velocity face is kept as kinetic storage.  The unforced energy law makes that
face antitone from the admitted initial trace, including a nonzero constant/Galilean mean.

Consequently

`E2(t) <= E0(0) + (1/2) D3(t)`

and its compact-time integral is paid by interval length times the initial kinetic storage plus
one half of the already exposed H3 viscous current.  No zero-mean frame, Fourier-mode erasure, or
new source estimate is inserted.  This removes the separate storage-occupation debt in the
weighted-H3 bridge; the signed nonlinear-production budget remains the terminal analytical debt.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Real Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearSourceSquareOwner
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH2Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH3MiddleRedistribution
open Soma.Holonics.Millennium.NavierStokesCoordinateLowerEnergyEstimate
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenEnergySpacetime
open Soma.Holonics.Millennium.NavierStokesOpenH2EnergyH3Dissipation
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTranslationDissipation
open Soma.Holonics.Millennium.NavierStokesWeightedH3CoordinateDissipationBridge

/-! ## The three storage faces -/

/-- The complete order-one coordinate storage, with all three addressed directions retained. -/
def coordinateH1Storage (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ word : Fin 1 → Fin 3,
    periodicKineticEnergy (coordinateJetField velocity 1 word) t

/-- The complete order-two coordinate storage, with all nine ordered directions retained. -/
def coordinateH2Storage (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ word : Fin 2 → Fin 3,
    periodicKineticEnergy (coordinateJetField velocity 2 word) t

/-- The literal `1 + 3 + 9` storage splits without changing any receiver. -/
theorem coordinateH2Energy_eq_kinetic_add_H1Storage_add_H2Storage
    (velocity : VelocityField) (t : ℝ) :
    coordinateH2Energy velocity t =
      periodicKineticEnergy velocity t +
        coordinateH1Storage velocity t + coordinateH2Storage velocity t := by
  unfold coordinateH2Energy coordinateH1Storage coordinateH2Storage
  rw [Fin.sum_univ_three]
  change
    (∑ word : Fin 0 → Fin 3,
        periodicKineticEnergy (coordinateJetField velocity 0 word) t) +
        (∑ word : Fin 1 → Fin 3,
          periodicKineticEnergy (coordinateJetField velocity 1 word) t) +
        (∑ word : Fin 2 → Fin 3,
          periodicKineticEnergy (coordinateJetField velocity 2 word) t) =
      periodicKineticEnergy velocity t +
        (∑ word : Fin 1 → Fin 3,
          periodicKineticEnergy (coordinateJetField velocity 1 word) t) +
        ∑ word : Fin 2 → Fin 3,
          periodicKineticEnergy (coordinateJetField velocity 2 word) t
  have hzero : coordinateJetField velocity 0 default = velocity := by
    funext x s
    exact coordinateJet_zero_eq_velocity velocity default x s
  have horderZero :
      (∑ word : Fin 0 → Fin 3,
        periodicKineticEnergy (coordinateJetField velocity 0 word) t) =
        periodicKineticEnergy (coordinateJetField velocity 0 default) t := by
    calc
      (∑ word : Fin 0 → Fin 3,
          periodicKineticEnergy (coordinateJetField velocity 0 word) t) =
        ∑ _word : Fin 0 → Fin 3,
          periodicKineticEnergy (coordinateJetField velocity 0 default) t := by
            apply Finset.sum_congr rfl
            intro word _hword
            exact congrArg
              (fun w : Fin 0 → Fin 3 ↦
                periodicKineticEnergy (coordinateJetField velocity 0 w) t)
              (Subsingleton.elim word default)
      _ = periodicKineticEnergy (coordinateJetField velocity 0 default) t := by simp
  rw [horderZero, hzero]

private def firstCoordinateWordEquiv : Fin 3 ≃ (Fin 1 → Fin 3) where
  toFun := firstCoordinateWord
  invFun := fun word ↦ word 0
  left_inv := by
    intro coordinate
    rfl
  right_inv := by
    intro word
    funext q
    fin_cases q
    rfl

private theorem two_mul_periodicKineticEnergy_eq_integral_norm_sq
    (field : VelocityField) (t : ℝ)
    (_hintegrable : IntegrableOn (fun x ↦ ‖field x t‖ ^ 2) unitCube) :
    2 * periodicKineticEnergy field t =
      ∫ x in unitCube, ‖field x t‖ ^ 2 := by
  unfold periodicKineticEnergy kineticEnergyDensity
  rw [integral_const_mul]
  ring

/-! ## Lower coordinate storage is already viscous current -/

/-- The order-one storage is exactly half the order-zero gradient current. -/
theorem openPeriodicSolutionOn_two_mul_coordinateH1Storage_eq_coordinateH0Dissipation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    2 * coordinateH1Storage velocity t = coordinateH0Dissipation velocity t := by
  let u : InitialVelocity := fun y ↦ velocity y t
  have hu : ContDiff ℝ ∞ u := openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have htermIntegrable : ∀ component coordinate : Fin 3,
      IntegrableOn
        (fun x ↦ (spatialDirectionalJet u coordinate x component) ^ 2)
        unitCube := by
    intro component coordinate
    have hsmooth : ContDiff ℝ ∞
        (fun x ↦ spatialDirectionalJet u coordinate x component) := by
      simpa [Function.comp_def] using
        (EuclideanSpace.proj component).contDiff.comp
          (spatialDirectionalJet_contDiff u hu coordinate)
    exact (hsmooth.pow 2).continuous.continuousOn.integrableOn_compact hcubeCompact
  have hcoordinate : ∀ coordinate : Fin 3,
      (∫ x in unitCube, ∑ component : Fin 3,
          (spatialDirectionalJet u coordinate x component) ^ 2) =
        2 * periodicKineticEnergy
          (coordinateJetField velocity 1 (firstCoordinateWord coordinate)) t := by
    intro coordinate
    have hjet : ∀ x,
        coordinateJetField velocity 1 (firstCoordinateWord coordinate) x t =
          spatialDirectionalJet u coordinate x := by
      intro x
      exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
        solution ht x coordinate
    have hnormInt : IntegrableOn
        (fun x ↦ ‖coordinateJetField velocity 1
          (firstCoordinateWord coordinate) x t‖ ^ 2) unitCube := by
      have hsmooth := openPeriodicSolutionOn_coordinateJetSlice_contDiff
        solution ht 1 (firstCoordinateWord coordinate)
      exact (hsmooth.continuous.norm.pow 2).continuousOn.integrableOn_compact hcubeCompact
    calc
      (∫ x in unitCube, ∑ component : Fin 3,
          (spatialDirectionalJet u coordinate x component) ^ 2) =
        ∫ x in unitCube, ‖spatialDirectionalJet u coordinate x‖ ^ 2 := by
          apply setIntegral_congr_fun hcubeCompact.measurableSet
          intro x _hx
          change (∑ component : Fin 3,
            (spatialDirectionalJet u coordinate x component) ^ 2) =
              ‖spatialDirectionalJet u coordinate x‖ ^ 2
          rw [EuclideanSpace.real_norm_sq_eq]
      _ = ∫ x in unitCube,
          ‖coordinateJetField velocity 1 (firstCoordinateWord coordinate) x t‖ ^ 2 := by
          apply setIntegral_congr_fun hcubeCompact.measurableSet
          intro x _hx
          exact congrArg (fun z : Space ↦ ‖z‖ ^ 2) (hjet x).symm
      _ = 2 * periodicKineticEnergy
          (coordinateJetField velocity 1 (firstCoordinateWord coordinate)) t :=
        (two_mul_periodicKineticEnergy_eq_integral_norm_sq _ _ hnormInt).symm
  unfold coordinateH1Storage coordinateH0Dissipation
  calc
    2 * (∑ word : Fin 1 → Fin 3,
        periodicKineticEnergy (coordinateJetField velocity 1 word) t) =
      ∑ coordinate : Fin 3,
        2 * periodicKineticEnergy
          (coordinateJetField velocity 1 (firstCoordinateWord coordinate)) t := by
        rw [Finset.mul_sum]
        exact (Fintype.sum_equiv firstCoordinateWordEquiv _ _
          (fun coordinate ↦ rfl)).symm
    _ = ∑ coordinate : Fin 3,
        ∫ x in unitCube, ∑ component : Fin 3,
          (spatialDirectionalJet u coordinate x component) ^ 2 := by
        apply Finset.sum_congr rfl
        intro coordinate _hcoordinate
        exact (hcoordinate coordinate).symm
    _ = ∫ x in unitCube, ∑ coordinate : Fin 3, ∑ component : Fin 3,
        (spatialDirectionalJet u coordinate x component) ^ 2 := by
        rw [integral_finsetSum Finset.univ]
        intro coordinate _hcoordinate
        exact integrable_finsetSum Finset.univ
          (fun component _hcomponent ↦ htermIntegrable component coordinate)
    _ = ∫ x in unitCube, ∑ component : Fin 3, ∑ coordinate : Fin 3,
        (spatialDirectionalJet u coordinate x component) ^ 2 := by
        apply setIntegral_congr_fun hcubeCompact.measurableSet
        intro x _hx
        exact Finset.sum_comm
    _ = ∫ x in unitCube, ∑ component : Fin 3,
        ‖gradient (fun y ↦ velocity y t component) x‖ ^ 2 := by
        apply setIntegral_congr_fun hcubeCompact.measurableSet
        intro x _hx
        apply Finset.sum_congr rfl
        intro component _hcomponent
        exact (norm_gradient_component_sq_eq_sum_spatialDirectionalJet
          u hu component x).symm

/-- The order-two storage is exactly half the order-one gradient current. -/
theorem openPeriodicSolutionOn_two_mul_coordinateH2Storage_eq_coordinateH1Dissipation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    2 * coordinateH2Storage velocity t = coordinateH1Dissipation velocity t := by
  let u : InitialVelocity := fun y ↦ velocity y t
  have hu : ContDiff ℝ ∞ u := openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hwordSmooth : ∀ word : Fin 1 → Fin 3,
      ContDiff ℝ ∞ (fun y ↦ coordinateJet velocity 1 word y t) := by
    intro word
    exact openPeriodicSolutionOn_coordinateJetSlice_contDiff solution ht 1 word
  have htermIntegrable : ∀ (word : Fin 1 → Fin 3)
      (component coordinate : Fin 3),
      IntegrableOn
        (fun x ↦ (spatialDirectionalJet
          (fun y ↦ coordinateJet velocity 1 word y t) coordinate x component) ^ 2)
        unitCube := by
    intro word component coordinate
    have hsmooth : ContDiff ℝ ∞ (fun x ↦
        spatialDirectionalJet
          (fun y ↦ coordinateJet velocity 1 word y t) coordinate x component) := by
      simpa [Function.comp_def] using
        (EuclideanSpace.proj component).contDiff.comp
          (spatialDirectionalJet_contDiff _ (hwordSmooth word) coordinate)
    exact (hsmooth.pow 2).continuous.continuousOn.integrableOn_compact hcubeCompact
  have hpair : ∀ (coordinate : Fin 3) (word : Fin 1 → Fin 3),
      (∫ x in unitCube, ∑ component : Fin 3,
          (spatialDirectionalJet
            (fun y ↦ coordinateJet velocity 1 word y t) coordinate x component) ^ 2) =
        2 * periodicKineticEnergy
          (coordinateJetField velocity 2
            (Fin.cons coordinate word : Fin 2 → Fin 3)) t := by
    intro coordinate word
    have hwordEq : word = firstCoordinateWord (word 0) := by
      funext q
      fin_cases q
      rfl
    have hconsEq : (Fin.cons coordinate word : Fin 2 → Fin 3) =
        secondCoordinateWord coordinate (word 0) := by
      funext q
      fin_cases q
      · rfl
      · simp [secondCoordinateWord]
    have hjet : ∀ x,
        coordinateJetField velocity 2 (Fin.cons coordinate word) x t =
          spatialDirectionalJet
            (fun y ↦ coordinateJet velocity 1 word y t) coordinate x := by
      intro x
      calc
        coordinateJetField velocity 2 (Fin.cons coordinate word) x t =
            secondCoordinateJet velocity coordinate (word 0) x t := by
          rw [hconsEq]
          rfl
        _ = spatialDirectionalJet
            (fun y ↦ firstCoordinateJet velocity (word 0) y t) coordinate x :=
          openPeriodicSolutionOn_secondCoordinateJet_eq_spatialDerivative_firstCoordinateJet
            solution ht x coordinate (word 0)
        _ = spatialDirectionalJet
            (fun y ↦ coordinateJet velocity 1 word y t) coordinate x := by
          rw [hwordEq]
          rfl
    have hnormInt : IntegrableOn
        (fun x ↦ ‖coordinateJetField velocity 2
          (Fin.cons coordinate word) x t‖ ^ 2) unitCube := by
      have hsmooth := openPeriodicSolutionOn_coordinateJetSlice_contDiff
        solution ht 2 (Fin.cons coordinate word)
      exact (hsmooth.continuous.norm.pow 2).continuousOn.integrableOn_compact hcubeCompact
    calc
      (∫ x in unitCube, ∑ component : Fin 3,
          (spatialDirectionalJet
            (fun y ↦ coordinateJet velocity 1 word y t) coordinate x component) ^ 2) =
        ∫ x in unitCube,
          ‖spatialDirectionalJet
            (fun y ↦ coordinateJet velocity 1 word y t) coordinate x‖ ^ 2 := by
          apply setIntegral_congr_fun hcubeCompact.measurableSet
          intro x _hx
          change (∑ component : Fin 3,
            (spatialDirectionalJet
              (fun y ↦ coordinateJet velocity 1 word y t) coordinate x component) ^ 2) =
              ‖spatialDirectionalJet
                (fun y ↦ coordinateJet velocity 1 word y t) coordinate x‖ ^ 2
          rw [EuclideanSpace.real_norm_sq_eq]
      _ = ∫ x in unitCube,
          ‖coordinateJetField velocity 2 (Fin.cons coordinate word) x t‖ ^ 2 := by
          apply setIntegral_congr_fun hcubeCompact.measurableSet
          intro x _hx
          exact congrArg (fun z : Space ↦ ‖z‖ ^ 2) (hjet x).symm
      _ = 2 * periodicKineticEnergy
          (coordinateJetField velocity 2 (Fin.cons coordinate word)) t :=
        (two_mul_periodicKineticEnergy_eq_integral_norm_sq _ _ hnormInt).symm
  unfold coordinateH2Storage coordinateH1Dissipation
  calc
    2 * (∑ next : Fin 2 → Fin 3,
        periodicKineticEnergy (coordinateJetField velocity 2 next) t) =
      ∑ pair : Fin 3 × (Fin 1 → Fin 3),
        2 * periodicKineticEnergy
          (coordinateJetField velocity 2 (Fin.cons pair.1 pair.2)) t := by
        rw [Finset.mul_sum]
        let e : (Fin 3 × (Fin 1 → Fin 3)) ≃ (Fin 2 → Fin 3) :=
          Fin.consEquiv (fun _ : Fin 2 ↦ Fin 3)
        exact (Fintype.sum_equiv e _ _ (fun pair ↦ rfl)).symm
    _ = ∑ word : Fin 1 → Fin 3, ∑ coordinate : Fin 3,
        ∫ x in unitCube, ∑ component : Fin 3,
          (spatialDirectionalJet
            (fun y ↦ coordinateJet velocity 1 word y t) coordinate x component) ^ 2 := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro word _hword
        apply Finset.sum_congr rfl
        intro coordinate _hcoordinate
        exact (hpair coordinate word).symm
    _ = ∑ word : Fin 1 → Fin 3,
        ∫ x in unitCube, ∑ coordinate : Fin 3, ∑ component : Fin 3,
          (spatialDirectionalJet
            (fun y ↦ coordinateJet velocity 1 word y t) coordinate x component) ^ 2 := by
        apply Finset.sum_congr rfl
        intro word _hword
        rw [integral_finsetSum Finset.univ]
        intro coordinate _hcoordinate
        exact integrable_finsetSum Finset.univ
          (fun component _hcomponent ↦ htermIntegrable word component coordinate)
    _ = ∑ word : Fin 1 → Fin 3,
        ∫ x in unitCube, ∑ component : Fin 3, ∑ coordinate : Fin 3,
          (spatialDirectionalJet
            (fun y ↦ coordinateJet velocity 1 word y t) coordinate x component) ^ 2 := by
        apply Finset.sum_congr rfl
        intro word _hword
        apply setIntegral_congr_fun hcubeCompact.measurableSet
        intro x _hx
        exact Finset.sum_comm
    _ = ∑ word : Fin 1 → Fin 3,
        ∫ x in unitCube, ∑ component : Fin 3,
          ‖gradient (fun y ↦ coordinateJet velocity 1 word y t component) x‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro word _hword
        apply setIntegral_congr_fun hcubeCompact.measurableSet
        intro x _hx
        apply Finset.sum_congr rfl
        intro component _hcomponent
        exact (norm_gradient_component_sq_eq_sum_spatialDirectionalJet
          (fun y ↦ coordinateJet velocity 1 word y t)
          (hwordSmooth word) component x).symm

/-! ## The Galilean mean stays as kinetic storage -/

/-- Unforced kinetic energy is antitone from the admitted initial trace.  This keeps a constant
mean velocity as storage instead of selecting a privileged zero-mean frame. -/
theorem openPeriodicSolutionOn_periodicKineticEnergy_le_initial
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    periodicKineticEnergy velocity t ≤ periodicKineticEnergy velocity 0 := by
  have hcontinuous :=
    openPeriodicSolutionOn_periodicKineticEnergy_continuousOn_initial solution ht.2
  have hantitone : AntitoneOn (periodicKineticEnergy velocity) (Icc (0 : ℝ) t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
    · intro s hs
      exact hcontinuous s hs
    · intro s hs
      have hs' : s ∈ Ioo (0 : ℝ) t := by simpa [interior_Icc, ht.1] using hs
      exact (openPeriodicSolutionOn_hasDerivAt_periodicKineticEnergy_unforced solution
        ⟨hs'.1, hs'.2.trans ht.2⟩).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Ioo (0 : ℝ) t := by simpa [interior_Icc, ht.1] using hs
      have hderivative :=
        openPeriodicSolutionOn_hasDerivAt_periodicKineticEnergy_unforced solution
          ⟨hs'.1, hs'.2.trans ht.2⟩
      rw [hderivative.deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnu)
        (coordinateH0Dissipation_nonneg velocity s)
  exact hantitone ⟨le_rfl, ht.1.le⟩ ⟨ht.1.le, le_rfl⟩ ht.1.le

/-- Exact pointwise storage payment.  Only the undifferentiated Galilean face reaches the initial
storage; both derivative faces are already contained in `D3`. -/
theorem openPeriodicSolutionOn_coordinateH2Energy_le_initialKinetic_add_half_H3Dissipation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    coordinateH2Energy velocity t ≤
      periodicKineticEnergy velocity 0 +
        (2 : ℝ)⁻¹ * coordinateH3ViscousDissipation velocity t := by
  have hsplit := coordinateH2Energy_eq_kinetic_add_H1Storage_add_H2Storage velocity t
  have hfirst :=
    openPeriodicSolutionOn_two_mul_coordinateH1Storage_eq_coordinateH0Dissipation
      solution ht
  have hsecond :=
    openPeriodicSolutionOn_two_mul_coordinateH2Storage_eq_coordinateH1Dissipation
      solution ht
  have hkinetic := openPeriodicSolutionOn_periodicKineticEnergy_le_initial
    solution hnu ht
  have htop := coordinateH2Dissipation_nonneg velocity t
  unfold coordinateH3ViscousDissipation
  rw [hsplit]
  nlinarith

/-! ## Compact-time payment and composition with the weighted-H3 bridge -/

/-- The complete storage occupation is paid by causal duration times initial kinetic storage plus
one half of the coordinate H3 viscous occupation. -/
theorem openPeriodicSolutionOn_integral_coordinateH2Energy_le_initialKinetic_add_half_H3Dissipation
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    (∫ time in a..b, coordinateH2Energy velocity time) ≤
      (b - a) * periodicKineticEnergy velocity 0 +
        (2 : ℝ)⁻¹ *
          ∫ time in a..b, coordinateH3ViscousDissipation velocity time := by
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
      (fun time ↦ periodicKineticEnergy velocity 0 +
        (2 : ℝ)⁻¹ * coordinateH3ViscousDissipation velocity time) volume a b :=
    intervalIntegrable_const.add (hdissInt.const_mul (2 : ℝ)⁻¹)
  have hmono := intervalIntegral.integral_mono_on hab henergyInt hrightInt
    (fun time htime ↦
      openPeriodicSolutionOn_coordinateH2Energy_le_initialKinetic_add_half_H3Dissipation
        solution hnu ⟨ha.trans_le htime.1, htime.2.trans_lt hbT⟩)
  calc
    (∫ time in a..b, coordinateH2Energy velocity time) ≤
      ∫ time in a..b, (periodicKineticEnergy velocity 0 +
        (2 : ℝ)⁻¹ * coordinateH3ViscousDissipation velocity time) := hmono
    _ = (b - a) * periodicKineticEnergy velocity 0 +
        (2 : ℝ)⁻¹ *
          ∫ time in a..b, coordinateH3ViscousDissipation velocity time := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
        (hdissInt.const_mul (2 : ℝ)⁻¹), intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul]
      ring

/-- The native weighted-H3 square occupation no longer carries a separate `integral E2` debt. -/
theorem integral_compactOpenVelocityWeightedH3SquareCurrent_le_initialKinetic_add_H3Dissipation
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    (∫ time in a..b,
        compactOpenVelocityWeightedH3SquareCurrent solution ha hab hbT time) ≤
      240 * ((b - a) * periodicKineticEnergy velocity 0 +
        (3 / 2 : ℝ) *
          ∫ time in a..b, coordinateH3ViscousDissipation velocity time) := by
  have hbridge :=
    integral_compactOpenVelocityWeightedH3SquareCurrent_le_H2_storage_add_H3_dissipation
      solution ha hab hbT
  have hstorage :=
    openPeriodicSolutionOn_integral_coordinateH2Energy_le_initialKinetic_add_half_H3Dissipation
      solution hnu ha hab hbT
  have hDnonneg : 0 ≤
      ∫ time in a..b, coordinateH3ViscousDissipation velocity time := by
    exact intervalIntegral.integral_nonneg hab
      (fun time _htime ↦ coordinateH3ViscousDissipation_nonneg velocity time)
  have hsum :
      (∫ time in a..b, coordinateH2Energy velocity time) +
          ∫ time in a..b, coordinateH3ViscousDissipation velocity time ≤
        (b - a) * periodicKineticEnergy velocity 0 +
          (3 / 2 : ℝ) *
            ∫ time in a..b, coordinateH3ViscousDissipation velocity time := by
    linarith
  calc
    (∫ time in a..b,
        compactOpenVelocityWeightedH3SquareCurrent solution ha hab hbT time) ≤
      240 * ((∫ time in a..b, coordinateH2Energy velocity time) +
        ∫ time in a..b, coordinateH3ViscousDissipation velocity time) := hbridge
    _ ≤ 240 * ((b - a) * periodicKineticEnergy velocity 0 +
        (3 / 2 : ℝ) *
          ∫ time in a..b, coordinateH3ViscousDissipation velocity time) := by
      exact mul_le_mul_of_nonneg_left hsum (by norm_num)

/-- After the exact H2 balance is applied, the only non-initial payment left in this bridge is the
already identified signed nonlinear production budget.  In particular, the time-integrated H2
storage is no longer an independent hypothesis. -/
theorem integral_compactOpenVelocityWeightedH3SquareCurrent_le_of_productionBudget_without_storageDebt
    {T nu a b productionBudget : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hproduction :
      (∫ time in a..b, coordinateH2NonlinearProductionCurrent velocity time) ≤
        productionBudget) :
    (∫ time in a..b,
        compactOpenVelocityWeightedH3SquareCurrent solution ha hab hbT time) ≤
      240 * ((b - a) * periodicKineticEnergy velocity 0 +
        (3 / 2 : ℝ) * nu⁻¹ *
          (coordinateH2Energy velocity a + productionBudget)) := by
  have hbridge :=
    integral_compactOpenVelocityWeightedH3SquareCurrent_le_initialKinetic_add_H3Dissipation
      solution hnu.le ha hab hbT
  have hdissipation :=
    openPeriodicSolutionOn_integral_coordinateH3ViscousDissipation_le_of_production
      solution hnu ha hab hbT hproduction
  have hfactorNonneg : 0 ≤ (3 / 2 : ℝ) := by norm_num
  have hpaid :
      (3 / 2 : ℝ) *
          ∫ time in a..b, coordinateH3ViscousDissipation velocity time ≤
        (3 / 2 : ℝ) * nu⁻¹ *
          (coordinateH2Energy velocity a + productionBudget) := by
    calc
      (3 / 2 : ℝ) *
          ∫ time in a..b, coordinateH3ViscousDissipation velocity time ≤
        (3 / 2 : ℝ) *
          (nu⁻¹ * (coordinateH2Energy velocity a + productionBudget)) :=
        mul_le_mul_of_nonneg_left hdissipation hfactorNonneg
      _ = (3 / 2 : ℝ) * nu⁻¹ *
          (coordinateH2Energy velocity a + productionBudget) := by ring
  exact hbridge.trans (mul_le_mul_of_nonneg_left
    (add_le_add_right hpaid ((b - a) * periodicKineticEnergy velocity 0))
    (by norm_num))

section Audit

#print axioms coordinateH2Energy_eq_kinetic_add_H1Storage_add_H2Storage
#print axioms openPeriodicSolutionOn_two_mul_coordinateH1Storage_eq_coordinateH0Dissipation
#print axioms openPeriodicSolutionOn_two_mul_coordinateH2Storage_eq_coordinateH1Dissipation
#print axioms openPeriodicSolutionOn_periodicKineticEnergy_le_initial
#print axioms
  openPeriodicSolutionOn_coordinateH2Energy_le_initialKinetic_add_half_H3Dissipation
#print axioms
  openPeriodicSolutionOn_integral_coordinateH2Energy_le_initialKinetic_add_half_H3Dissipation
#print axioms
  integral_compactOpenVelocityWeightedH3SquareCurrent_le_initialKinetic_add_H3Dissipation
#print axioms
  integral_compactOpenVelocityWeightedH3SquareCurrent_le_of_productionBudget_without_storageDebt

end Audit

end Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment
