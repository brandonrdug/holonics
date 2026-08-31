import ElementaryHolonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
import ElementaryHolonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
import ElementaryHolonics.Millennium.NavierStokesSmoothHodgeJacobianBand

/-!
# The annular Hodge scale chain

**[proved-derived]** The smooth low-pass Jacobian at radius `r + 1` is exactly the low-pass at
radius `r` plus the actual adjacent Hodge band at that scale.  Iterating returns a telescoping
ordered word: the radius-`R` carrier is the base carrier plus every addressed annular passage in
`Finset.range R`.

This is the literal filtered-path composition behind the informal phrase “repeat the localized
solution across scales.”  It is not an analogy and it does not identify a finite aperture with the
complete Jacobian.  The complete reconstruction fibre remains supplied separately by
`NavierStokesCoordinateJacobianFourierReconstruction`.
-/

noncomputable section

open Set
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesAnnularHodgeScaleChain

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianMatrixBridge
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesHodgeBandReconstruction
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

/-- A finite synthesis may be enlarged to a declared outer aperture when every newly admitted
coefficient vanishes.  The addressed support inclusion is retained explicitly. -/
theorem finiteFourierSynthesis_eq_of_subset_of_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (coeff : SpatialFrequency → E) {inner outer : Finset SpatialFrequency}
    (hsubset : inner ⊆ outer)
    (hzero : ∀ frequency ∈ outer, frequency ∉ inner → coeff frequency = 0) :
    finiteFourierSynthesis coeff inner = finiteFourierSynthesis coeff outer := by
  ext q
  change (∑ frequency ∈ inner,
      UnitAddTorus.mFourier frequency q • coeff frequency) =
    ∑ frequency ∈ outer,
      UnitAddTorus.mFourier frequency q • coeff frequency
  apply Finset.sum_subset hsubset
  intro frequency houter hinner
  rw [hzero frequency houter hinner]
  simp

/-- The actual smooth Hodge low-pass at one integer radius.  Its multiplier is the tensor de la
Vallée Poussin chart applied to the genuine Jacobian coefficient population. -/
def openPeriodicSmoothHodgeJacobianLowPass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) : C(SpatialTorus, ComplexJacobianArray) :=
  finiteFourierSynthesis
    (fun frequency ↦
      (tensorValleePoussinWeight radius frequency : ℂ) •
        openPeriodicJacobianFourierMode solution t frequency)
    (frequencyCube (valleePoussinOuterRadius radius))

/-- The low-pass synthesis can be mounted in the next scale's larger aperture without changing
the returned field. -/
theorem openPeriodicSmoothHodgeJacobianLowPass_eq_nextAperture
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) :
    openPeriodicSmoothHodgeJacobianLowPass solution t radius =
      finiteFourierSynthesis
        (fun frequency ↦
          (tensorValleePoussinWeight radius frequency : ℂ) •
            openPeriodicJacobianFourierMode solution t frequency)
        (frequencyCube (valleePoussinOuterRadius (radius + 1))) := by
  unfold openPeriodicSmoothHodgeJacobianLowPass
  apply finiteFourierSynthesis_eq_of_subset_of_eq_zero
  · apply frequencyCube_mono
    unfold valleePoussinOuterRadius
    omega
  · intro frequency _houter hinner
    rw [tensorValleePoussinWeight_eq_zero_of_not_mem_outer radius hinner]
    simp

/-- **One scale passage.**  Moving the smooth Jacobian low-pass from radius `r` to `r + 1`
deposits exactly the actual adjacent Hodge band at radius `r`. -/
theorem openPeriodicSmoothHodgeJacobianLowPass_succ
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) :
    openPeriodicSmoothHodgeJacobianLowPass solution t (radius + 1) =
      openPeriodicSmoothHodgeJacobianLowPass solution t radius +
        openPeriodicSmoothHodgeJacobianBand solution t radius := by
  have hbase := openPeriodicSmoothHodgeJacobianLowPass_eq_nextAperture
    solution t radius
  rw [openPeriodicSmoothHodgeJacobianBand_eq_actualAdjacentMultiplier,
    hbase]
  ext q component coordinate
  unfold openPeriodicSmoothHodgeJacobianLowPass finiteFourierSynthesis
  simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  simp only [adjacentValleePoussinWeight]
  push_cast
  ring

/-- **Complete finite scale word.**  The radius-`R` low-pass is the base face followed by every
adjacent annular passage in order.  No band is duplicated or forgotten. -/
theorem openPeriodicSmoothHodgeJacobianLowPass_eq_base_add_sum_bands
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) :
    openPeriodicSmoothHodgeJacobianLowPass solution t radius =
      openPeriodicSmoothHodgeJacobianLowPass solution t 0 +
        ∑ scale ∈ Finset.range radius,
          openPeriodicSmoothHodgeJacobianBand solution t scale := by
  induction radius with
  | zero => simp
  | succ radius inductionHypothesis =>
      rw [openPeriodicSmoothHodgeJacobianLowPass_succ,
        inductionHypothesis, Finset.sum_range_succ]
      abel

/-- Norm shadow of the exact scale word.  This deliberately retains each band receiver; the
annular kernel theorem may later insert its reciprocal-scale bound term by term. -/
theorem norm_openPeriodicSmoothHodgeJacobianLowPass_le_base_add_sum_bands
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) :
    ‖openPeriodicSmoothHodgeJacobianLowPass solution t radius‖ ≤
      ‖openPeriodicSmoothHodgeJacobianLowPass solution t 0‖ +
        ∑ scale ∈ Finset.range radius,
          ‖openPeriodicSmoothHodgeJacobianBand solution t scale‖ := by
  rw [openPeriodicSmoothHodgeJacobianLowPass_eq_base_add_sum_bands]
  exact (norm_add_le _ _).trans
    (add_le_add (le_refl _) (norm_sum_le _ _))

/-! ## The fixed base face is controlled by the actual critical receiver -/

/-- The degree-zero Hodge ascent sends one vorticity pin to a Jacobian array with norm at most
three times the vector norm.  The factor three is the complete addressed input-coordinate
population, not an unspecified norm-equivalence constant. -/
theorem norm_hodgeJacobianMode_le_three_mul
    (frequency : SpatialFrequency) (vorticityMode : ComplexVector) :
    ‖hodgeJacobianMode frequency vorticityMode‖ ≤ 3 * ‖vorticityMode‖ := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))]
  intro component
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))]
  intro coordinate
  rw [hodgeJacobianMode_eq_sum_multiplierEntry]
  calc
    ‖∑ input : Fin 3,
        hodgeJacobianMultiplierEntry frequency component coordinate input *
          vorticityMode input‖ ≤
        ∑ input : Fin 3,
          ‖hodgeJacobianMultiplierEntry frequency component coordinate input *
            vorticityMode input‖ := norm_sum_le _ _
    _ ≤ ∑ _input : Fin 3, ‖vorticityMode‖ := by
      apply Finset.sum_le_sum
      intro input _hinput
      rw [norm_mul]
      exact (mul_le_mul
        (norm_hodgeJacobianMultiplierEntry_le_one
          frequency component coordinate input)
        ((norm_le_pi_norm vorticityMode input))
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ = 3 * ‖vorticityMode‖ := by
      simp

/-- Every actual Jacobian pin is bounded by three payments of the actual critical-vorticity
receiver. -/
theorem norm_openPeriodicJacobianFourierMode_le_three_mul_criticalVorticityRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) :
    ‖openPeriodicJacobianFourierMode solution t frequency‖ ≤
      3 * criticalVorticityRate solution t.1 := by
  calc
    ‖openPeriodicJacobianFourierMode solution t frequency‖ =
        ‖hodgeJacobianMode frequency
          (openPeriodicVorticityFourierMode solution t frequency)‖ := by
      rw [hodgeJacobianMode_openPeriodicVorticityFourierMode]
    _ ≤ 3 * ‖openPeriodicVorticityFourierMode solution t frequency‖ :=
      norm_hodgeJacobianMode_le_three_mul _ _
    _ ≤ 3 * criticalVorticityRate solution t.1 :=
      mul_le_mul_of_nonneg_left
        (norm_openPeriodicVorticityFourierMode_le_criticalVorticityRate
          solution t frequency) (by norm_num)

/-- The fixed radius-zero low-pass costs at most `81` times the actual critical receiver: its
outer cube has exactly `27` pins and each complete Jacobian array costs at most three. -/
theorem norm_openPeriodicSmoothHodgeJacobianLowPass_zero_apply_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (q : SpatialTorus) :
    ‖openPeriodicSmoothHodgeJacobianLowPass solution t 0 q‖ ≤
      81 * criticalVorticityRate solution t.1 := by
  unfold openPeriodicSmoothHodgeJacobianLowPass
  refine (norm_finiteFourierSynthesis_le_sum_norm _ _ q).trans ?_
  calc
    (∑ frequency ∈ frequencyCube (valleePoussinOuterRadius 0),
        ‖(tensorValleePoussinWeight 0 frequency : ℂ) •
          openPeriodicJacobianFourierMode solution t frequency‖) ≤
        ∑ _frequency ∈ frequencyCube (valleePoussinOuterRadius 0),
          3 * criticalVorticityRate solution t.1 := by
      apply Finset.sum_le_sum
      intro frequency _hfrequency
      rw [norm_smul]
      obtain ⟨hweightNonneg, hweightOne⟩ :=
        tensorValleePoussinWeight_mem_unitInterval 0 frequency
      have hweightNorm :
          ‖(tensorValleePoussinWeight 0 frequency : ℂ)‖ ≤ 1 := by
        simpa [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hweightNonneg] using hweightOne
      exact (mul_le_mul hweightNorm
        (norm_openPeriodicJacobianFourierMode_le_three_mul_criticalVorticityRate
          solution t frequency)
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ = 81 * criticalVorticityRate solution t.1 := by
      rw [Finset.sum_const, nsmul_eq_mul, card_frequencyCube]
      norm_num [valleePoussinOuterRadius]
      ring

/-- Enlarging a finite aperture can only decrease the exact coefficient reconstruction-fibre
mass.  The proof compares the two retained subtype populations through the same complete
summable Jacobian series. -/
theorem openPeriodicJacobianCoefficientTailMass_antitone
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) {inner outer : Finset SpatialFrequency}
    (hsubset : inner ⊆ outer) :
    openPeriodicJacobianCoefficientTailMass solution t outer ≤
      openPeriodicJacobianCoefficientTailMass solution t inner := by
  unfold openPeriodicJacobianCoefficientTailMass
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro component
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro coordinate
  let coefficientNorm : SpatialFrequency → ℝ := fun frequency ↦
    ‖openPeriodicJacobianFourierMode solution t frequency component coordinate‖
  have hfull : Summable coefficientNorm :=
    summable_norm_openPeriodicJacobianFourierMode_entry
      solution t component coordinate
  have hsumLe :
      (∑ frequency ∈ inner, coefficientNorm frequency) ≤
        ∑ frequency ∈ outer, coefficientNorm frequency :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun frequency _houter _hinner ↦ norm_nonneg _)
  have hinnerSplit := hfull.sum_add_tsum_subtype_compl inner
  have houterSplit := hfull.sum_add_tsum_subtype_compl outer
  have htail :
      (∑' frequency : {frequency : SpatialFrequency // frequency ∉ outer},
          coefficientNorm frequency.1) ≤
        ∑' frequency : {frequency : SpatialFrequency // frequency ∉ inner},
          coefficientNorm frequency.1 := by
    linarith
  have houterNonneg :
      0 ≤ ∑' frequency : {frequency : SpatialFrequency // frequency ∉ outer},
        coefficientNorm frequency.1 := tsum_nonneg fun _ ↦ norm_nonneg _
  have hinnerNonneg :
      0 ≤ ∑' frequency : {frequency : SpatialFrequency // frequency ∉ inner},
        coefficientNorm frequency.1 := tsum_nonneg fun _ ↦ norm_nonneg _
  calc
    ‖∑' frequency : {frequency : SpatialFrequency // frequency ∉ outer},
        coefficientNorm frequency.1‖ =
        ∑' frequency : {frequency : SpatialFrequency // frequency ∉ outer},
          coefficientNorm frequency.1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg houterNonneg]
    _ ≤ ∑' frequency : {frequency : SpatialFrequency // frequency ∉ inner},
          coefficientNorm frequency.1 := htail
    _ = ‖∑' frequency : {frequency : SpatialFrequency // frequency ∉ inner},
          coefficientNorm frequency.1‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hinnerNonneg]
    _ ≤ ‖(fun coordinate : Fin 3 ↦
          ∑' frequency : {frequency : SpatialFrequency // frequency ∉ inner},
            ‖openPeriodicJacobianFourierMode solution t frequency.1
              component coordinate‖)‖ :=
      norm_le_pi_norm
        (fun innerCoordinate : Fin 3 ↦
          ∑' frequency : {frequency : SpatialFrequency // frequency ∉ inner},
            ‖openPeriodicJacobianFourierMode solution t frequency.1
              component innerCoordinate‖) coordinate
    _ ≤ ‖fun component : Fin 3 ↦ fun coordinate : Fin 3 ↦
          ∑' frequency : {frequency : SpatialFrequency // frequency ∉ inner},
            ‖openPeriodicJacobianFourierMode solution t frequency.1
              component coordinate‖‖ :=
      norm_le_pi_norm
        (fun outerComponent : Fin 3 ↦ fun outerCoordinate : Fin 3 ↦
          ∑' frequency : {frequency : SpatialFrequency // frequency ∉ inner},
            ‖openPeriodicJacobianFourierMode solution t frequency.1
              outerComponent outerCoordinate‖) component

/-- The finite transition population between the sharp outer aperture and the smooth low-pass
chart. -/
def openPeriodicJacobianScaleTransition
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) (q : SpatialTorus) : ComplexJacobianArray :=
  openPeriodicJacobianBandProjector solution t
      (frequencyCube (valleePoussinOuterRadius radius)) q -
    openPeriodicSmoothHodgeJacobianLowPass solution t radius q

/-- The transition is exactly the finite synthesis of the complementary smooth multiplier. -/
theorem openPeriodicJacobianScaleTransition_eq_finiteFourierSynthesis
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) (q : SpatialTorus) :
    openPeriodicJacobianScaleTransition solution t radius q =
      finiteFourierSynthesis
        (fun frequency ↦
          ((1 - tensorValleePoussinWeight radius frequency : ℝ) : ℂ) •
            openPeriodicJacobianFourierMode solution t frequency)
        (frequencyCube (valleePoussinOuterRadius radius)) q := by
  funext component coordinate
  unfold openPeriodicJacobianScaleTransition
    openPeriodicJacobianBandProjector
    openPeriodicSmoothHodgeJacobianLowPass finiteFourierSynthesis
  simp only [ContinuousMap.coe_mk, Pi.sub_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  push_cast
  ring

/-- The finite smooth/sharp transition is already part of the coefficient reconstruction fibre
outside the plateau cube. -/
theorem norm_openPeriodicJacobianScaleTransition_le_tailMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) (q : SpatialTorus) :
    ‖openPeriodicJacobianScaleTransition solution t radius q‖ ≤
      openPeriodicJacobianCoefficientTailMass solution t
        (frequencyCube (radius + 1)) := by
  rw [openPeriodicJacobianScaleTransition_eq_finiteFourierSynthesis]
  rw [pi_norm_le_iff_of_nonneg (by
    unfold openPeriodicJacobianCoefficientTailMass
    positivity)]
  intro component
  rw [pi_norm_le_iff_of_nonneg (by
    unfold openPeriodicJacobianCoefficientTailMass
    positivity)]
  intro coordinate
  let inner := frequencyCube (radius + 1)
  let outer := frequencyCube (valleePoussinOuterRadius radius)
  let coefficientNorm : SpatialFrequency → ℝ := fun frequency ↦
    ‖openPeriodicJacobianFourierMode solution t frequency component coordinate‖
  let complementModes : Finset {frequency : SpatialFrequency // frequency ∉ inner} :=
    outer.subtype fun frequency ↦ frequency ∉ inner
  have hfull : Summable coefficientNorm :=
    summable_norm_openPeriodicJacobianFourierMode_entry
      solution t component coordinate
  have hsubtype : Summable fun frequency :
      {frequency : SpatialFrequency // frequency ∉ inner} ↦
        coefficientNorm frequency.1 :=
    hfull.subtype {frequency : SpatialFrequency | frequency ∉ inner}
  have hfiniteToTail :
      (∑ frequency ∈ complementModes, coefficientNorm frequency.1) ≤
        ∑' frequency : {frequency : SpatialFrequency // frequency ∉ inner},
          coefficientNorm frequency.1 :=
    hsubtype.sum_le_tsum complementModes
      (fun frequency _hfrequency ↦ norm_nonneg _)
  have hfilteredToSubtype :
      (∑ frequency ∈ outer with frequency ∉ inner,
          coefficientNorm frequency) =
        ∑ frequency ∈ complementModes, coefficientNorm frequency.1 := by
    dsimp [complementModes]
    exact (Finset.sum_subtype_eq_sum_filter coefficientNorm).symm
  have htailNonneg :
      0 ≤ ∑' frequency : {frequency : SpatialFrequency // frequency ∉ inner},
        coefficientNorm frequency.1 := tsum_nonneg fun _ ↦ norm_nonneg _
  have hentryToMass :
      (∑' frequency : {frequency : SpatialFrequency // frequency ∉ inner},
          coefficientNorm frequency.1) ≤
        openPeriodicJacobianCoefficientTailMass solution t inner := by
    calc
      (∑' frequency : {frequency : SpatialFrequency // frequency ∉ inner},
          coefficientNorm frequency.1) =
          ‖∑' frequency : {frequency : SpatialFrequency // frequency ∉ inner},
            coefficientNorm frequency.1‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg htailNonneg]
      _ ≤ ‖(fun innerCoordinate : Fin 3 ↦
            ∑' frequency : {frequency : SpatialFrequency // frequency ∉ inner},
              ‖openPeriodicJacobianFourierMode solution t frequency.1
                component innerCoordinate‖)‖ :=
        norm_le_pi_norm
          (fun innerCoordinate : Fin 3 ↦
            ∑' frequency : {frequency : SpatialFrequency // frequency ∉ inner},
              ‖openPeriodicJacobianFourierMode solution t frequency.1
                component innerCoordinate‖) coordinate
      _ ≤ ‖fun outerComponent : Fin 3 ↦ fun outerCoordinate : Fin 3 ↦
            ∑' frequency : {frequency : SpatialFrequency // frequency ∉ inner},
              ‖openPeriodicJacobianFourierMode solution t frequency.1
                outerComponent outerCoordinate‖‖ :=
        norm_le_pi_norm
          (fun outerComponent : Fin 3 ↦ fun outerCoordinate : Fin 3 ↦
            ∑' frequency : {frequency : SpatialFrequency // frequency ∉ inner},
              ‖openPeriodicJacobianFourierMode solution t frequency.1
                outerComponent outerCoordinate‖) component
      _ = openPeriodicJacobianCoefficientTailMass solution t inner := rfl
  unfold finiteFourierSynthesis
  simp only [ContinuousMap.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change ‖∑ frequency ∈ outer,
      UnitAddTorus.mFourier frequency q *
        (((1 - tensorValleePoussinWeight radius frequency : ℝ) : ℂ) *
          openPeriodicJacobianFourierMode solution t frequency component coordinate)‖ ≤ _
  calc
    ‖∑ frequency ∈ outer,
        UnitAddTorus.mFourier frequency q *
          (((1 - tensorValleePoussinWeight radius frequency : ℝ) : ℂ) *
            openPeriodicJacobianFourierMode solution t frequency component coordinate)‖ ≤
        ∑ frequency ∈ outer,
          ‖UnitAddTorus.mFourier frequency q *
            (((1 - tensorValleePoussinWeight radius frequency : ℝ) : ℂ) *
              openPeriodicJacobianFourierMode solution t frequency
                component coordinate)‖ := norm_sum_le _ _
    _ ≤ ∑ frequency ∈ outer,
          if frequency ∉ inner then coefficientNorm frequency else 0 := by
      apply Finset.sum_le_sum
      intro frequency _hfrequency
      by_cases hinner : frequency ∈ inner
      · rw [if_neg (not_not.mpr hinner)]
        have hplateau : tensorValleePoussinWeight radius frequency = 1 :=
          tensorValleePoussinWeight_eq_one radius hinner
        simp [hplateau]
      · rw [if_pos hinner]
        obtain ⟨hweightNonneg, hweightOne⟩ :=
          tensorValleePoussinWeight_mem_unitInterval radius frequency
        have hcharacter : ‖UnitAddTorus.mFourier frequency q‖ = 1 := by
          simp [UnitAddTorus.mFourier, norm_prod, Circle.norm_coe]
        rw [norm_mul, hcharacter, one_mul, norm_mul,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr hweightOne)]
        have hcomplementOne :
            1 - tensorValleePoussinWeight radius frequency ≤ 1 := by
          linarith
        exact mul_le_of_le_one_left (norm_nonneg _)
          hcomplementOne
    _ = ∑ frequency ∈ outer with frequency ∉ inner,
          coefficientNorm frequency := by
      rw [Finset.sum_filter]
    _ = ∑ frequency ∈ complementModes,
          coefficientNorm frequency.1 := hfilteredToSubtype
    _ ≤ ∑' frequency : {frequency : SpatialFrequency // frequency ∉ inner},
          coefficientNorm frequency.1 := hfiniteToTail
    _ ≤ openPeriodicJacobianCoefficientTailMass solution t inner := hentryToMass

/-! ## The complete receiver retains the transition annulus and infinite exterior -/

/-- The complete reconstruction fibre left by the radius-`R` smooth low-pass.  It has two
addressed populations: the finite transition from the sharp outer aperture to the smooth
multiplier, and the full subtype-indexed complement outside that aperture. -/
def openPeriodicJacobianScaleReconstructionFiber
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) (q : SpatialTorus) : ComplexJacobianArray :=
  openPeriodicJacobianBandProjector solution t
      (frequencyCube (valleePoussinOuterRadius radius)) q -
    openPeriodicSmoothHodgeJacobianLowPass solution t radius q +
      openPeriodicJacobianArrayFourierTail solution t
        (frequencyCube (valleePoussinOuterRadius radius)) q

/-- The scale fibre is the finite smooth/sharp transition followed by the infinite outer tail. -/
theorem openPeriodicJacobianScaleReconstructionFiber_eq_transition_add_tail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) (q : SpatialTorus) :
    openPeriodicJacobianScaleReconstructionFiber solution t radius q =
      openPeriodicJacobianScaleTransition solution t radius q +
        openPeriodicJacobianArrayFourierTail solution t
          (frequencyCube (valleePoussinOuterRadius radius)) q := by
  rfl

/-- The plateau cube lies inside the declared outer support of its smooth low-pass. -/
theorem frequencyCube_radius_add_one_subset_valleePoussinOuter
    (radius : ℕ) :
    frequencyCube (radius + 1) ⊆
      frequencyCube (valleePoussinOuterRadius radius) := by
  apply frequencyCube_mono
  unfold valleePoussinOuterRadius
  omega

/-- Both constituents of the scale fibre are controlled by the same complete coefficient tail
outside the plateau.  The factor two records the finite transition and infinite exterior as
distinct caused populations. -/
theorem norm_openPeriodicJacobianScaleReconstructionFiber_le_two_mul_tailMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) (q : SpatialTorus) :
    ‖openPeriodicJacobianScaleReconstructionFiber solution t radius q‖ ≤
      2 * openPeriodicJacobianCoefficientTailMass solution t
        (frequencyCube (radius + 1)) := by
  let inner := frequencyCube (radius + 1)
  let outer := frequencyCube (valleePoussinOuterRadius radius)
  have htransition :
      ‖openPeriodicJacobianScaleTransition solution t radius q‖ ≤
        openPeriodicJacobianCoefficientTailMass solution t inner := by
    simpa [inner] using
      norm_openPeriodicJacobianScaleTransition_le_tailMass
        solution t radius q
  have htail :
      ‖openPeriodicJacobianArrayFourierTail solution t outer q‖ ≤
        openPeriodicJacobianCoefficientTailMass solution t outer :=
    norm_openPeriodicJacobianArrayFourierTail_le solution t outer q
  have hsubset : inner ⊆ outer :=
    frequencyCube_radius_add_one_subset_valleePoussinOuter radius
  have htailMass :
      openPeriodicJacobianCoefficientTailMass solution t outer ≤
        openPeriodicJacobianCoefficientTailMass solution t inner :=
    openPeriodicJacobianCoefficientTailMass_antitone solution t hsubset
  have hfiber :
      openPeriodicJacobianScaleReconstructionFiber solution t radius q =
        openPeriodicJacobianScaleTransition solution t radius q +
          openPeriodicJacobianArrayFourierTail solution t outer q := by
    simpa [outer] using
      openPeriodicJacobianScaleReconstructionFiber_eq_transition_add_tail
        solution t radius q
  have hresult :
      ‖openPeriodicJacobianScaleReconstructionFiber solution t radius q‖ ≤
        2 * openPeriodicJacobianCoefficientTailMass solution t inner := by
    rw [hfiber]
    calc
      ‖openPeriodicJacobianScaleTransition solution t radius q +
          openPeriodicJacobianArrayFourierTail solution t outer q‖ ≤
        ‖openPeriodicJacobianScaleTransition solution t radius q‖ +
          ‖openPeriodicJacobianArrayFourierTail solution t outer q‖ := norm_add_le _ _
      _ ≤ openPeriodicJacobianCoefficientTailMass solution t inner +
          openPeriodicJacobianCoefficientTailMass solution t outer :=
        add_le_add htransition htail
      _ ≤ openPeriodicJacobianCoefficientTailMass solution t inner +
          openPeriodicJacobianCoefficientTailMass solution t inner :=
        add_le_add (le_refl _) htailMass
      _ = 2 * openPeriodicJacobianCoefficientTailMass solution t inner := by ring
  simpa [inner] using hresult

/-- Exact low-pass/fibre decomposition of the literal descended Jacobian array. -/
theorem openPeriodicTorusJacobianArraySlice_eq_lowPass_add_scaleFiber
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) (q : SpatialTorus) :
    openPeriodicTorusJacobianArraySlice solution t q =
      openPeriodicSmoothHodgeJacobianLowPass solution t radius q +
        openPeriodicJacobianScaleReconstructionFiber solution t radius q := by
  rw [openPeriodicTorusJacobianArraySlice_eq_band_add_arrayTail]
  unfold openPeriodicJacobianScaleReconstructionFiber
  abel

/-- **The composed scale circulation.**  The actual receiver is the base face, followed by the
ordered population of adjacent Hodge passages, together with the complete unresolved scale
fibre.  This is an equality of the physical Jacobian array at every torus receiver. -/
theorem openPeriodicTorusJacobianArraySlice_eq_base_add_sum_bands_add_scaleFiber
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) (q : SpatialTorus) :
    openPeriodicTorusJacobianArraySlice solution t q =
      openPeriodicSmoothHodgeJacobianLowPass solution t 0 q +
        (∑ scale ∈ Finset.range radius,
          openPeriodicSmoothHodgeJacobianBand solution t scale q) +
        openPeriodicJacobianScaleReconstructionFiber solution t radius q := by
  have hdecomposition :=
    openPeriodicTorusJacobianArraySlice_eq_lowPass_add_scaleFiber
      solution t radius q
  have hchain := congrArg (fun field : C(SpatialTorus, ComplexJacobianArray) ↦ field q)
    (openPeriodicSmoothHodgeJacobianLowPass_eq_base_add_sum_bands
      solution t radius)
  simp only [ContinuousMap.add_apply] at hchain
  have hsumEvaluation :
      (∑ scale ∈ Finset.range radius,
          openPeriodicSmoothHodgeJacobianBand solution t scale) q =
        ∑ scale ∈ Finset.range radius,
          openPeriodicSmoothHodgeJacobianBand solution t scale q := by
    simp
  rw [hdecomposition, hchain, hsumEvaluation]

/-- Receiver shadow of the composed scale circulation.  The unresolved fibre remains visible as
its own term and is not promoted into a theorem about a finite aperture. -/
theorem norm_openPeriodicTorusJacobianArraySlice_le_scaleCirculation
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) (q : SpatialTorus) :
    ‖openPeriodicTorusJacobianArraySlice solution t q‖ ≤
      ‖openPeriodicSmoothHodgeJacobianLowPass solution t 0 q‖ +
        (∑ scale ∈ Finset.range radius,
          ‖openPeriodicSmoothHodgeJacobianBand solution t scale q‖) +
        ‖openPeriodicJacobianScaleReconstructionFiber solution t radius q‖ := by
  rw [openPeriodicTorusJacobianArraySlice_eq_base_add_sum_bands_add_scaleFiber]
  exact (norm_add_le _ _).trans
    (add_le_add
      ((norm_add_le _ _).trans
        (add_le_add (le_refl _) (norm_sum_le _ _)))
      (le_refl _))

/-- Pointwise BKM scale decomposition before inserting the annular physical-kernel constant. -/
theorem norm_openPeriodicTorusJacobianArraySlice_le_kernelScaleSum_add_tail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) (q : SpatialTorus) :
    ‖openPeriodicTorusJacobianArraySlice solution t q‖ ≤
      81 * criticalVorticityRate solution t.1 +
        (∑ scale ∈ Finset.range radius,
          adjacentHodgeJacobianKernelL1 scale *
            criticalVorticityRate solution t.1) +
        2 * openPeriodicJacobianCoefficientTailMass solution t
          (frequencyCube (radius + 1)) := by
  refine (norm_openPeriodicTorusJacobianArraySlice_le_scaleCirculation
    solution t radius q).trans ?_
  apply add_le_add
  · apply add_le_add
    · exact norm_openPeriodicSmoothHodgeJacobianLowPass_zero_apply_le
        solution t q
    · apply Finset.sum_le_sum
      intro scale _hscale
      exact norm_openPeriodicSmoothHodgeJacobianBand_le_kernelL1_mul_criticalVorticityRate
        solution t scale q
  · exact norm_openPeriodicJacobianScaleReconstructionFiber_le_two_mul_tailMass
      solution t radius q

section Audit

#print axioms finiteFourierSynthesis_eq_of_subset_of_eq_zero
#print axioms openPeriodicSmoothHodgeJacobianLowPass_eq_nextAperture
#print axioms openPeriodicSmoothHodgeJacobianLowPass_succ
#print axioms openPeriodicSmoothHodgeJacobianLowPass_eq_base_add_sum_bands
#print axioms norm_openPeriodicSmoothHodgeJacobianLowPass_le_base_add_sum_bands
#print axioms norm_hodgeJacobianMode_le_three_mul
#print axioms norm_openPeriodicJacobianFourierMode_le_three_mul_criticalVorticityRate
#print axioms norm_openPeriodicSmoothHodgeJacobianLowPass_zero_apply_le
#print axioms openPeriodicJacobianCoefficientTailMass_antitone
#print axioms openPeriodicJacobianScaleTransition_eq_finiteFourierSynthesis
#print axioms norm_openPeriodicJacobianScaleTransition_le_tailMass
#print axioms norm_openPeriodicJacobianScaleReconstructionFiber_le_two_mul_tailMass
#print axioms openPeriodicTorusJacobianArraySlice_eq_lowPass_add_scaleFiber
#print axioms openPeriodicTorusJacobianArraySlice_eq_base_add_sum_bands_add_scaleFiber
#print axioms norm_openPeriodicTorusJacobianArraySlice_le_scaleCirculation
#print axioms norm_openPeriodicTorusJacobianArraySlice_le_kernelScaleSum_add_tail

end Audit

end Soma.Holonics.Millennium.NavierStokesAnnularHodgeScaleChain
