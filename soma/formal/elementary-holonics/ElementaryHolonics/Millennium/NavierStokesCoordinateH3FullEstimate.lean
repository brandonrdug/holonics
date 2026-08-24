import ElementaryHolonics.Millennium.NavierStokesCoordinateH3MiddleRedistribution
import ElementaryHolonics.Millennium.NavierStokesCoordinateLowerEnergyEstimate

/-!
# The complete coordinate H³ production estimate

The lower-order owner closes the `1 + 3 + 9` faces of the differentiated coordinate energy.
The periodic redistribution owner closes the three middle `D²-D²-D³` faces of every
order-three word.  This file supplies the remaining four direct order-three faces, composes the
exact order-three production identity, and then uses the exact `1 + 3 + 9 + 27` slice equality.

The returned constant is deliberately the transparent finite population
`240 + 540 + 10206 = 10986`.  The theorem is first stated against the genuine cube Jacobian
supremum and then rebased to any actual pointwise Jacobian envelope.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Set
open scoped BigOperators Laplacian

namespace Soma.Holonics.Millennium.NavierStokesCoordinateH3FullEstimate

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
open Soma.Holonics.Millennium.NavierStokesCoordinateH3MiddleRedistribution
open Soma.Holonics.Millennium.NavierStokesCoordinateLowerEnergyEstimate

/-! ## The four direct order-three faces -/

/-- The norm square of every addressed order-three word is one of the forty nonnegative faces of
the coordinate H³ density. -/
theorem norm_thirdCoordinateJet_sq_le_two_mul_coordinateH3EnergyDensity
    (velocity : VelocityField) (i j k : Fin 3) (x : Space) (t : ℝ) :
    ‖thirdCoordinateJet velocity i j k x t‖ ^ 2 ≤
      2 * coordinateH3EnergyDensity velocity x t := by
  simpa [thirdCoordinateJet, coordinateJetField] using
    norm_coordinateJet_sq_le_two_mul_coordinateH3EnergyDensity velocity
      (⟨3, by norm_num⟩ : Fin 4) (thirdCoordinateWord i j k) x t

/-- Three direct order-three products cost six copies of the complete pointwise coordinate
energy. -/
theorem sum_thirdJet_norm_mul_thirdJet_norm_le_six_density
    (velocity : VelocityField) (a b i j k : Fin 3) (x : Space) (t : ℝ) :
    (∑ coordinate : Fin 3,
        ‖thirdCoordinateJet velocity coordinate a b x t‖) *
        ‖thirdCoordinateJet velocity i j k x t‖ ≤
      6 * coordinateH3EnergyDensity velocity x t := by
  let E : ℝ := coordinateH3EnergyDensity velocity x t
  let B : ℝ := ‖thirdCoordinateJet velocity i j k x t‖
  have hB : B ^ 2 ≤ 2 * E := by
    simpa [B, E] using
      norm_thirdCoordinateJet_sq_le_two_mul_coordinateH3EnergyDensity
        velocity i j k x t
  have hterm : ∀ coordinate : Fin 3,
      ‖thirdCoordinateJet velocity coordinate a b x t‖ * B ≤ 2 * E := by
    intro coordinate
    have hA : ‖thirdCoordinateJet velocity coordinate a b x t‖ ^ 2 ≤ 2 * E := by
      simpa [E] using
        norm_thirdCoordinateJet_sq_le_two_mul_coordinateH3EnergyDensity
          velocity coordinate a b x t
    nlinarith [sq_nonneg
      (‖thirdCoordinateJet velocity coordinate a b x t‖ - B)]
  calc
    (∑ coordinate : Fin 3,
        ‖thirdCoordinateJet velocity coordinate a b x t‖) * B =
      ∑ coordinate : Fin 3,
        ‖thirdCoordinateJet velocity coordinate a b x t‖ * B := by
      rw [Finset.sum_mul]
    _ ≤ ∑ _coordinate : Fin 3, 2 * E :=
      Finset.sum_le_sum (fun coordinate _hcoordinate ↦ hterm coordinate)
    _ = 6 * E := by simp; ring

/-- One complete `3 + 3 + 3 + 1` direct commutator pairing costs twenty copies of the
coordinate H³ density. -/
theorem openPeriodicSolutionOn_abs_inner_thirdCoordinateDirectCommutator_le_density
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (hx : x ∈ unitCube)
    (i j k : Fin 3) :
    |inner ℝ (thirdCoordinateDirectCommutator velocity t i j k x)
        (thirdCoordinateJet velocity i j k x t)| ≤
      20 * cubeGradientSup (fun y ↦ velocity y t) *
        coordinateH3EnergyDensity velocity x t := by
  let M : ℝ := cubeGradientSup (fun y ↦ velocity y t)
  let E : ℝ := coordinateH3EnergyDensity velocity x t
  let V : ℝ := ‖thirdCoordinateJet velocity i j k x t‖
  have hpoint :=
    openPeriodicSolutionOn_abs_inner_thirdCoordinateDirectCommutator_le
      solution ht x hx i j k
  have hfirst :
      (∑ coordinate : Fin 3,
          ‖thirdCoordinateJet velocity coordinate j k x t‖) * V ≤ 6 * E := by
    simpa [V, E] using
      sum_thirdJet_norm_mul_thirdJet_norm_le_six_density
        velocity j k i j k x t
  have hsecond :
      (∑ coordinate : Fin 3,
          ‖thirdCoordinateJet velocity coordinate i k x t‖) * V ≤ 6 * E := by
    simpa [V, E] using
      sum_thirdJet_norm_mul_thirdJet_norm_le_six_density
        velocity i k i j k x t
  have hthird :
      (∑ coordinate : Fin 3,
          ‖thirdCoordinateJet velocity coordinate i j x t‖) * V ≤ 6 * E := by
    simpa [V, E] using
      sum_thirdJet_norm_mul_thirdJet_norm_le_six_density
        velocity i j i j k x t
  have hself : V ^ 2 ≤ 2 * E := by
    simpa [V, E] using
      norm_thirdCoordinateJet_sq_le_two_mul_coordinateH3EnergyDensity
        velocity i j k x t
  have hu : ContDiff ℝ ∞ (fun y ↦ velocity y t) :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hM : 0 ≤ M := cubeGradientSup_nonneg _ hu
  calc
    |inner ℝ (thirdCoordinateDirectCommutator velocity t i j k x)
        (thirdCoordinateJet velocity i j k x t)| ≤
      M *
        ((∑ coordinate : Fin 3,
            ‖thirdCoordinateJet velocity coordinate j k x t‖) +
          (∑ coordinate : Fin 3,
            ‖thirdCoordinateJet velocity coordinate i k x t‖) +
          (∑ coordinate : Fin 3,
            ‖thirdCoordinateJet velocity coordinate i j x t‖) + V) * V := by
      simpa [M, V] using hpoint
    _ = M *
        (((∑ coordinate : Fin 3,
            ‖thirdCoordinateJet velocity coordinate j k x t‖) * V) +
          ((∑ coordinate : Fin 3,
            ‖thirdCoordinateJet velocity coordinate i k x t‖) * V) +
          ((∑ coordinate : Fin 3,
            ‖thirdCoordinateJet velocity coordinate i j x t‖) * V) + V ^ 2) := by
      ring
    _ ≤ M * (6 * E + 6 * E + 6 * E + 2 * E) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hself) hM
    _ = 20 * M * E := by ring

/-- The paired direct commutator is continuous on every admitted interior slice. -/
theorem openPeriodicSolutionOn_directPairing_continuous
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (i j k : Fin 3) :
    Continuous (fun x ↦
      inner ℝ (thirdCoordinateDirectCommutator velocity t i j k x)
        (thirdCoordinateJet velocity i j k x t)) := by
  have hu : ContDiff ℝ ∞ (fun x ↦ velocity x t) :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hfirstI : ContDiff ℝ ∞ (fun x ↦ firstCoordinateJet velocity i x t) :=
    openPeriodicSolutionOn_coordinateJetSlice_contDiff solution ht 1 (firstCoordinateWord i)
  have hfirstJ : ContDiff ℝ ∞ (fun x ↦ firstCoordinateJet velocity j x t) :=
    openPeriodicSolutionOn_coordinateJetSlice_contDiff solution ht 1 (firstCoordinateWord j)
  have hfirstK : ContDiff ℝ ∞ (fun x ↦ firstCoordinateJet velocity k x t) :=
    openPeriodicSolutionOn_coordinateJetSlice_contDiff solution ht 1 (firstCoordinateWord k)
  have hsecondIJ : ContDiff ℝ ∞ (fun x ↦ secondCoordinateJet velocity i j x t) :=
    openPeriodicSolutionOn_coordinateJetSlice_contDiff solution ht 2 (secondCoordinateWord i j)
  have hsecondIK : ContDiff ℝ ∞ (fun x ↦ secondCoordinateJet velocity i k x t) :=
    openPeriodicSolutionOn_coordinateJetSlice_contDiff solution ht 2 (secondCoordinateWord i k)
  have hsecondJK : ContDiff ℝ ∞ (fun x ↦ secondCoordinateJet velocity j k x t) :=
    openPeriodicSolutionOn_coordinateJetSlice_contDiff solution ht 2 (secondCoordinateWord j k)
  have hthird : ContDiff ℝ ∞ (fun x ↦ thirdCoordinateJet velocity i j k x t) :=
    openPeriodicSolutionOn_coordinateJetSlice_contDiff solution ht 3 (thirdCoordinateWord i j k)
  have hA : Continuous (fun x ↦
      fderiv ℝ (fun y ↦ secondCoordinateJet velocity j k y t) x
        (firstCoordinateJet velocity i x t)) :=
    ((hsecondJK.fderiv_right (by simp)).clm_apply hfirstI).continuous
  have hB : Continuous (fun x ↦
      fderiv ℝ (fun y ↦ secondCoordinateJet velocity i k y t) x
        (firstCoordinateJet velocity j x t)) :=
    ((hsecondIK.fderiv_right (by simp)).clm_apply hfirstJ).continuous
  have hC : Continuous (fun x ↦
      fderiv ℝ (fun y ↦ secondCoordinateJet velocity i j y t) x
        (firstCoordinateJet velocity k x t)) :=
    ((hsecondIJ.fderiv_right (by simp)).clm_apply hfirstK).continuous
  have hD : Continuous (fun x ↦
      fderiv ℝ (fun y ↦ velocity y t) x
        (thirdCoordinateJet velocity i j k x t)) :=
    ((hu.fderiv_right (by simp)).clm_apply hthird).continuous
  exact (((hA.add hB).add hC).add hD).inner hthird.continuous

/-- All four direct faces over the complete ordered third-word population. -/
def coordinateH3OrderDirectWork (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ word : Fin 3 → Fin 3,
    ∫ x in unitCube,
      inner ℝ
        (thirdCoordinateDirectCommutator velocity t (word 0) (word 1) (word 2) x)
        (thirdCoordinateJet velocity (word 0) (word 1) (word 2) x t)

/-- The complete direct population contributes at most `27 * 20 = 540` copies of the actual
coordinate H³ energy. -/
theorem openPeriodicSolutionOn_abs_coordinateH3OrderDirectWork_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    |coordinateH3OrderDirectWork velocity t| ≤
      540 * cubeGradientSup (fun y ↦ velocity y t) * coordinateH3Energy velocity t := by
  let M : ℝ := cubeGradientSup (fun y ↦ velocity y t)
  let E : Space → ℝ := fun x ↦ coordinateH3EnergyDensity velocity x t
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have hrightInt : IntegrableOn (fun x ↦ 20 * M * E x) unitCube :=
    (openPeriodicSolutionOn_coordinateH3EnergyDensity_integrable solution ht).const_mul _
  have hword : ∀ word : Fin 3 → Fin 3,
      |∫ x in unitCube,
          inner ℝ
            (thirdCoordinateDirectCommutator velocity t
              (word 0) (word 1) (word 2) x)
            (thirdCoordinateJet velocity (word 0) (word 1) (word 2) x t)| ≤
        20 * M * coordinateH3Energy velocity t := by
    intro word
    have hpairingContinuous := openPeriodicSolutionOn_directPairing_continuous
      solution ht (word 0) (word 1) (word 2)
    have hleftInt : IntegrableOn (fun x ↦
        |inner ℝ
          (thirdCoordinateDirectCommutator velocity t
            (word 0) (word 1) (word 2) x)
          (thirdCoordinateJet velocity (word 0) (word 1) (word 2) x t)|) unitCube :=
      hpairingContinuous.abs.continuousOn.integrableOn_compact hcubeCompact
    calc
      |∫ x in unitCube,
          inner ℝ
            (thirdCoordinateDirectCommutator velocity t
              (word 0) (word 1) (word 2) x)
            (thirdCoordinateJet velocity (word 0) (word 1) (word 2) x t)| ≤
        ∫ x in unitCube,
          |inner ℝ
            (thirdCoordinateDirectCommutator velocity t
              (word 0) (word 1) (word 2) x)
            (thirdCoordinateJet velocity (word 0) (word 1) (word 2) x t)| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ x in unitCube, 20 * M * E x := by
        exact setIntegral_mono_on hleftInt hrightInt hcubeMeasurable
          (fun x hx ↦ by
            simpa [M, E] using
              openPeriodicSolutionOn_abs_inner_thirdCoordinateDirectCommutator_le_density
                solution ht x hx (word 0) (word 1) (word 2))
      _ = 20 * M * coordinateH3Energy velocity t := by
        rw [integral_const_mul,
          ← openPeriodicSolutionOn_coordinateH3Energy_eq_integral_density solution ht]
  unfold coordinateH3OrderDirectWork
  calc
    |∑ word : Fin 3 → Fin 3,
        ∫ x in unitCube,
          inner ℝ
            (thirdCoordinateDirectCommutator velocity t
              (word 0) (word 1) (word 2) x)
            (thirdCoordinateJet velocity (word 0) (word 1) (word 2) x t)| ≤
      ∑ word : Fin 3 → Fin 3,
        |∫ x in unitCube,
          inner ℝ
            (thirdCoordinateDirectCommutator velocity t
              (word 0) (word 1) (word 2) x)
            (thirdCoordinateJet velocity (word 0) (word 1) (word 2) x t)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _word : Fin 3 → Fin 3,
        20 * M * coordinateH3Energy velocity t := by
      exact Finset.sum_le_sum (fun word _hword ↦ hword word)
    _ = 540 * M * coordinateH3Energy velocity t := by norm_num; ring

/-! ## Composition with the middle population and exact production -/

/-- The exact seven-face lower work is the sum of the four direct faces and three middle faces. -/
theorem openPeriodicSolutionOn_coordinateH3OrderLowerWork_eq_direct_add_middle
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    coordinateH3OrderLowerWork velocity t =
      coordinateH3OrderDirectWork velocity t + coordinateH3OrderMiddleWork velocity t := by
  unfold coordinateH3OrderLowerWork coordinateH3OrderDirectWork
    coordinateH3OrderMiddleWork
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro word _hword
  have hwordEq : word = thirdCoordinateWord (word 0) (word 1) (word 2) := by
    funext q
    fin_cases q <;> rfl
  have hjet : ∀ x : Space,
      coordinateJet velocity 3 word x t =
        thirdCoordinateJet velocity (word 0) (word 1) (word 2) x t := by
    intro x
    rw [hwordEq]
    rfl
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hdirectInt : IntegrableOn (fun x ↦
      inner ℝ
        (thirdCoordinateDirectCommutator velocity t (word 0) (word 1) (word 2) x)
        (thirdCoordinateJet velocity (word 0) (word 1) (word 2) x t)) unitCube :=
    (openPeriodicSolutionOn_directPairing_continuous
      solution ht (word 0) (word 1) (word 2)).continuousOn.integrableOn_compact hcubeCompact
  have hmiddleInt : IntegrableOn (fun x ↦
      inner ℝ
        (thirdCoordinateMiddleCommutator velocity t (word 0) (word 1) (word 2) x)
        (thirdCoordinateJet velocity (word 0) (word 1) (word 2) x t)) unitCube :=
    (openPeriodicSolutionOn_middlePairing_continuous
      solution ht (word 0) (word 1) (word 2)).continuousOn.integrableOn_compact hcubeCompact
  rw [← integral_add hdirectInt hmiddleInt]
  apply setIntegral_congr_fun hcubeCompact.measurableSet
  intro x _hx
  simp only
  rw [hjet x, ← inner_add_left,
    ← thirdCoordinateLowerCommutator_eq_direct_add_middle]

/-- The order-three energy slice is one nonnegative face of the complete coordinate H³ energy. -/
theorem coordinateH3OrderEnergy_le_coordinateH3Energy
    (velocity : VelocityField) (t : ℝ) :
    coordinateH3OrderEnergy velocity t ≤ coordinateH3Energy velocity t := by
  let orderThree : Fin 4 := ⟨3, by norm_num⟩
  let face : Fin 4 → ℝ := fun n ↦
    ∑ word : Fin (n : ℕ) → Fin 3,
      periodicKineticEnergy (coordinateJetField velocity n word) t
  have hnonneg : ∀ n ∈ (Finset.univ : Finset (Fin 4)), 0 ≤ face n := by
    intro n _hn
    unfold face periodicKineticEnergy kineticEnergyDensity
    exact Finset.sum_nonneg (fun word _hword ↦
      integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x ↦ by positivity)))
  have hsingle := Finset.single_le_sum (s := Finset.univ) (f := face)
    hnonneg (Finset.mem_univ orderThree)
  simpa [coordinateH3OrderEnergy, coordinateH3Energy, face, orderThree] using hsingle

theorem coordinateH3OrderDissipation_nonneg (velocity : VelocityField) (t : ℝ) :
    0 ≤ coordinateH3OrderDissipation velocity t := by
  have hcubeMeasurable : MeasurableSet unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc |>.measurableSet
  unfold coordinateH3OrderDissipation
  exact Finset.sum_nonneg (fun word _hword ↦
    setIntegral_nonneg hcubeMeasurable
      (fun x _hx ↦ Finset.sum_nonneg (fun component _hcomponent ↦ by positivity)))

/-- The exact unforced order-three production identity, with viscosity retained by sign, closes
against the actual cube Jacobian receiver. -/
theorem openPeriodicSolutionOn_unforced_coordinateH3OrderTimeWork_le
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (hnu : 0 ≤ nu) :
    coordinateH3OrderTimeWork velocity t ≤
      10746 * cubeGradientSup (fun y ↦ velocity y t) * coordinateH3Energy velocity t := by
  let M : ℝ := cubeGradientSup (fun y ↦ velocity y t)
  let E : ℝ := coordinateH3Energy velocity t
  have hproduction :=
    openPeriodicSolutionOn_unforced_coordinateH3OrderTimeWork_eq_production solution ht
  have hdissipation := coordinateH3OrderDissipation_nonneg velocity t
  have hviscous : -nu * coordinateH3OrderDissipation velocity t ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnu) hdissipation
  have hlowerEq :=
    openPeriodicSolutionOn_coordinateH3OrderLowerWork_eq_direct_add_middle solution ht
  have hdirect := openPeriodicSolutionOn_abs_coordinateH3OrderDirectWork_le solution ht
  have hmiddleOrder :=
    openPeriodicSolutionOn_abs_coordinateH3OrderMiddleWork_le_orderEnergy solution ht
  have hu : ContDiff ℝ ∞ (fun y ↦ velocity y t) :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hM : 0 ≤ M := cubeGradientSup_nonneg _ hu
  have horderEnergy := coordinateH3OrderEnergy_le_coordinateH3Energy velocity t
  have hmiddle : |coordinateH3OrderMiddleWork velocity t| ≤ 10206 * M * E := by
    calc
      |coordinateH3OrderMiddleWork velocity t| ≤
          10206 * M * coordinateH3OrderEnergy velocity t := by
        simpa [M] using hmiddleOrder
      _ ≤ 10206 * M * E := by
        exact mul_le_mul_of_nonneg_left horderEnergy
          (mul_nonneg (by norm_num) hM)
  have hlower : -coordinateH3OrderLowerWork velocity t ≤ 10746 * M * E := by
    rw [hlowerEq]
    calc
      -(coordinateH3OrderDirectWork velocity t +
          coordinateH3OrderMiddleWork velocity t) ≤
        |coordinateH3OrderDirectWork velocity t| +
          |coordinateH3OrderMiddleWork velocity t| := by
        nlinarith [neg_le_abs (coordinateH3OrderDirectWork velocity t),
          neg_le_abs (coordinateH3OrderMiddleWork velocity t)]
      _ ≤ 540 * M * E + 10206 * M * E := by
        exact add_le_add (by simpa [M, E] using hdirect) hmiddle
      _ = 10746 * M * E := by ring
  dsimp [M, E] at hviscous hlower ⊢
  linarith

/-! ## The complete forty-face return and Jacobian-envelope rebase -/

/-- **Complete coordinate H³ production estimate.**  The exact forty-word time work is bounded
by the genuine cube Jacobian supremum times the differentiated logarithmic receiver. -/
theorem openPeriodicSolutionOn_unforced_coordinateH3TimeWork_le_logReceiver
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (hnu : 0 ≤ nu) :
    coordinateH3TimeWork velocity t ≤
      10986 * cubeGradientSup (fun y ↦ velocity y t) *
        coordinateLogH3Receiver velocity t := by
  let M : ℝ := cubeGradientSup (fun y ↦ velocity y t)
  let E : ℝ := coordinateH3Energy velocity t
  let H : ℝ := coordinateLogH3Receiver velocity t
  have hslices := coordinateH3TimeWork_eq_orderSlices velocity t
  have hlower := openPeriodicSolutionOn_unforced_coordinateLowerTimeWork_le_energy
    solution ht hnu
  have hthird := openPeriodicSolutionOn_unforced_coordinateH3OrderTimeWork_le
    solution ht hnu
  have hu : ContDiff ℝ ∞ (fun y ↦ velocity y t) :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hM : 0 ≤ M := cubeGradientSup_nonneg _ hu
  have henergy : E ≤ H := by
    dsimp [E, H, coordinateLogH3Receiver]
    linarith [Real.exp_pos 1]
  have hraw : coordinateH3TimeWork velocity t ≤ 10986 * M * E := by
    rw [hslices]
    dsimp [M, E] at hlower hthird ⊢
    linarith
  calc
    coordinateH3TimeWork velocity t ≤ 10986 * M * E := hraw
    _ ≤ 10986 * M * H := by
      exact mul_le_mul_of_nonneg_left henergy
        (mul_nonneg (by norm_num) hM)
    _ = 10986 * cubeGradientSup (fun y ↦ velocity y t) *
        coordinateLogH3Receiver velocity t := rfl

/-- The same complete estimate rebased to the actual pointwise Jacobian envelope required by the
coordinate frequency comb. -/
theorem openPeriodicSolutionOn_unforced_coordinateH3TimeWork_le_envelope
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t K : ℝ} (ht : t ∈ Ioo 0 T) (hnu : 0 ≤ nu)
    (hK : ∀ x ∈ unitCube, ‖fderiv ℝ (fun y ↦ velocity y t) x‖ ≤ K) :
    coordinateH3TimeWork velocity t ≤
      10986 * K * coordinateLogH3Receiver velocity t := by
  have hproduction :=
    openPeriodicSolutionOn_unforced_coordinateH3TimeWork_le_logReceiver solution ht hnu
  have hsup := cubeGradientSup_le_of_pointwise_envelope
    (fun y ↦ velocity y t) K hK
  have hreceiver : 0 ≤ coordinateLogH3Receiver velocity t :=
    (one_le_coordinateLogH3Receiver velocity t).trans' zero_le_one
  calc
    coordinateH3TimeWork velocity t ≤
        10986 * cubeGradientSup (fun y ↦ velocity y t) *
          coordinateLogH3Receiver velocity t := hproduction
    _ ≤ 10986 * K * coordinateLogH3Receiver velocity t := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsup (by norm_num)) hreceiver

section Audit

#print axioms openPeriodicSolutionOn_abs_inner_thirdCoordinateDirectCommutator_le_density
#print axioms openPeriodicSolutionOn_abs_coordinateH3OrderDirectWork_le
#print axioms openPeriodicSolutionOn_coordinateH3OrderLowerWork_eq_direct_add_middle
#print axioms coordinateH3OrderEnergy_le_coordinateH3Energy
#print axioms openPeriodicSolutionOn_unforced_coordinateH3OrderTimeWork_le
#print axioms openPeriodicSolutionOn_unforced_coordinateH3TimeWork_le_logReceiver
#print axioms openPeriodicSolutionOn_unforced_coordinateH3TimeWork_le_envelope

end Audit

end Soma.Holonics.Millennium.NavierStokesCoordinateH3FullEstimate
