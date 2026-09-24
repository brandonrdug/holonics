import ElementaryHolonics.Millennium.NavierStokesAnnularHodgeKernelDifference

/-!
# Reindexed annular Hodge coefficient slices and their scale receivers

**[proved-derived]** This owner begins the actual coefficient-side discharge of the annular Hodge
kernel `L1` frontier.  It reindexes every addressed coordinate slice of the genuine three-
dimensional multiplier onto a centered natural interval, proves that the scalar de la Vallée
Poussin charts stay in the unit interval, and obtains the resulting linear-in-radius coefficient
mass bound for the full Hodge entry.

The exact zero-padded first and second differences are retained rather than replaced by an
asymptotic label.  The genuine centered scalar chart is identified with its trapezoid, giving the
exact total second variation `4 / (radius + 1)`.  Product-difference identities then separate this
closed scalar contribution from the remaining rational Hodge variation required by iterated
Abel/Fubini.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesFejerMultiplier
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference

/-! ## Unit bounds for the scalar chart -/

/-- Every one-coordinate de la Vallée Poussin multiplier is nonnegative. -/
theorem coordinateValleePoussinWeight_nonneg
    (radius : ℕ) (frequency : ℤ) :
    0 ≤ coordinateValleePoussinWeight radius frequency := by
  by_cases hplateau : frequency.natAbs ≤ radius + 1
  · rw [coordinateValleePoussinWeight_eq_one radius hplateau]
    norm_num
  · have hinner : ¬frequency.natAbs ≤ radius := by omega
    unfold coordinateValleePoussinWeight
    have hzero : coordinateHatWeight radius frequency = 0 := by
      simp [coordinateHatWeight, hinner]
    rw [hzero, sub_zero]
    exact mul_nonneg (by norm_num)
      (coordinateHatWeight_nonneg (valleePoussinOuterRadius radius) frequency)

/-- Every one-coordinate de la Vallée Poussin multiplier is at most one. -/
theorem coordinateValleePoussinWeight_le_one
    (radius : ℕ) (frequency : ℤ) :
    coordinateValleePoussinWeight radius frequency ≤ 1 := by
  by_cases hplateau : frequency.natAbs ≤ radius + 1
  · rw [coordinateValleePoussinWeight_eq_one radius hplateau]
  · have hinner : ¬frequency.natAbs ≤ radius := by omega
    by_cases houter : frequency.natAbs ≤ valleePoussinOuterRadius radius
    · have habsLower : (radius + 2 : ℝ) ≤ (frequency.natAbs : ℝ) := by
        exact_mod_cast (show radius + 2 ≤ frequency.natAbs by omega)
      have houterDenominator :
          (valleePoussinOuterRadius radius : ℝ) + 1 =
            2 * (radius + 1 : ℝ) := by
        norm_cast
      have hsub :
          (((valleePoussinOuterRadius radius + 1 - frequency.natAbs : ℕ) : ℝ)) =
            (valleePoussinOuterRadius radius + 1 : ℝ) - frequency.natAbs := by
        rw [Nat.cast_sub (by omega :
          frequency.natAbs ≤ valleePoussinOuterRadius radius + 1)]
        push_cast
        rfl
      simp only [coordinateValleePoussinWeight, coordinateHatWeight,
        if_pos houter, if_neg hinner]
      rw [hsub, houterDenominator]
      have hdenominator : 0 < 2 * (radius + 1 : ℝ) := by positivity
      rw [sub_zero, ← mul_div_assoc, div_le_iff₀ hdenominator]
      nlinarith
    · have houterZero : coordinateHatWeight (valleePoussinOuterRadius radius) frequency = 0 := by
        simp [coordinateHatWeight, houter]
      have hinnerZero : coordinateHatWeight radius frequency = 0 := by
        simp [coordinateHatWeight, hinner]
      simp [coordinateValleePoussinWeight, houterZero, hinnerZero]

/-- Exact linear taper outside the plateau and inside the outer support. -/
theorem coordinateValleePoussinWeight_eq_taper
    (radius : ℕ) {frequency : ℤ}
    (hplateau : radius + 1 < frequency.natAbs)
    (houter : frequency.natAbs ≤ valleePoussinOuterRadius radius) :
    coordinateValleePoussinWeight radius frequency =
      ((valleePoussinOuterRadius radius + 1 - frequency.natAbs : ℕ) : ℝ) /
        (radius + 1 : ℝ) := by
  have hinner : ¬frequency.natAbs ≤ radius := by omega
  simp only [coordinateValleePoussinWeight, coordinateHatWeight,
    if_pos houter, if_neg hinner]
  have houterDenominator :
      (valleePoussinOuterRadius radius : ℝ) + 1 =
        2 * (radius + 1 : ℝ) := by
    norm_cast
  rw [houterDenominator]
  have hdenominator : (radius + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Tensor de la Vallée Poussin multipliers stay in the unit interval. -/
theorem tensorValleePoussinWeight_mem_unitInterval
    (radius : ℕ) (frequency : SpatialFrequency) :
    0 ≤ tensorValleePoussinWeight radius frequency ∧
      tensorValleePoussinWeight radius frequency ≤ 1 := by
  constructor
  · unfold tensorValleePoussinWeight
    exact Finset.prod_nonneg fun coordinate _ ↦
      coordinateValleePoussinWeight_nonneg radius (frequency coordinate)
  · unfold tensorValleePoussinWeight
    apply Finset.prod_le_one
    · intro coordinate _
      exact coordinateValleePoussinWeight_nonneg radius (frequency coordinate)
    · intro coordinate _
      exact coordinateValleePoussinWeight_le_one radius (frequency coordinate)

/-- The adjacent scalar chart has magnitude at most one at every lattice frequency. -/
theorem abs_adjacentValleePoussinWeight_le_one
    (radius : ℕ) (frequency : SpatialFrequency) :
    |adjacentValleePoussinWeight radius frequency| ≤ 1 := by
  obtain ⟨hnextNonneg, hnextOne⟩ :=
    tensorValleePoussinWeight_mem_unitInterval (radius + 1) frequency
  obtain ⟨hbaseNonneg, hbaseOne⟩ :=
    tensorValleePoussinWeight_mem_unitInterval radius frequency
  rw [abs_le]
  constructor <;> unfold adjacentValleePoussinWeight <;> linarith

/-! ## Centered reindexing of actual coordinate slices -/

/-- Number of integer frequencies in the centered interval `[-radius, radius]`. -/
def centeredFrequencyCount (radius : ℕ) : ℕ := 2 * radius + 1

/-- The `index`-th integer in the centered interval, with zero-based natural indexing. -/
def centeredFrequency (radius index : ℕ) : ℤ :=
  (index : ℤ) - (radius : ℤ)

/-- Replace one addressed frequency coordinate while retaining the other two. -/
def replaceFrequencyCoordinate
    (axis : Fin 3) (base : SpatialFrequency) (value : ℤ) : SpatialFrequency :=
  Function.update base axis value

/-- One actual scalar entry of the adjacent Hodge multiplier. -/
def annularHodgeMultiplierCoefficient
    (radius : ℕ) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3) : ℂ :=
  (adjacentValleePoussinWeight radius frequency : ℂ) *
    hodgeJacobianMultiplierEntry frequency component coordinate input

/-- Natural-indexed slice through one coordinate of the actual three-dimensional annular Hodge
coefficient population.  The slice aperture is the exact adjacent outer radius. -/
def annularHodgeCoefficientSlice
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) (index : ℕ) : ℂ :=
  let outer := valleePoussinOuterRadius (radius + 1)
  annularHodgeMultiplierCoefficient radius
    (replaceFrequencyCoordinate axis base (centeredFrequency outer index))
    component coordinate input

/-- Scalar-chart factor of an actual reindexed coefficient slice. -/
def annularWeightSlice
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) (index : ℕ) : ℂ :=
  let outer := valleePoussinOuterRadius (radius + 1)
  (adjacentValleePoussinWeight radius
    (replaceFrequencyCoordinate axis base (centeredFrequency outer index)) : ℂ)

/-- Rational Hodge factor of an actual reindexed coefficient slice. -/
def hodgeMultiplierSlice
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) (index : ℕ) : ℂ :=
  let outer := valleePoussinOuterRadius (radius + 1)
  hodgeJacobianMultiplierEntry
    (replaceFrequencyCoordinate axis base (centeredFrequency outer index))
    component coordinate input

/-- The actual slice is exactly the product of its scalar chart and rational Hodge factors. -/
theorem annularHodgeCoefficientSlice_eq_weight_mul_hodge
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) (index : ℕ) :
    annularHodgeCoefficientSlice radius axis base component coordinate input index =
      annularWeightSlice radius axis base index *
        hodgeMultiplierSlice radius axis base component coordinate input index := by
  rfl

/-- Replacements in distinct frequency coordinates commute.  Consequently all mixed-difference
charts used by iterated Abel transport are independent of the order in which axes are opened. -/
theorem replaceFrequencyCoordinate_comm
    {first second : Fin 3} (haxes : first ≠ second)
    (base : SpatialFrequency) (firstValue secondValue : ℤ) :
    replaceFrequencyCoordinate first
        (replaceFrequencyCoordinate second base secondValue) firstValue =
      replaceFrequencyCoordinate second
        (replaceFrequencyCoordinate first base firstValue) secondValue := by
  unfold replaceFrequencyCoordinate
  exact Function.update_comm haxes.symm secondValue firstValue base

/-- Actual double-coordinate coefficient chart used by mixed differences and nested Fubini. -/
def annularHodgeCoefficientDoubleSlice
    (radius : ℕ) (first second : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) (firstIndex secondIndex : ℕ) : ℂ :=
  let outer := valleePoussinOuterRadius (radius + 1)
  annularHodgeMultiplierCoefficient radius
    (replaceFrequencyCoordinate first
      (replaceFrequencyCoordinate second base (centeredFrequency outer secondIndex))
      (centeredFrequency outer firstIndex))
    component coordinate input

/-- Distinct-axis double slices commute after swapping their addressed indices. -/
theorem annularHodgeCoefficientDoubleSlice_comm
    {first second : Fin 3} (haxes : first ≠ second)
    (radius : ℕ) (base : SpatialFrequency)
    (component coordinate input : Fin 3) (firstIndex secondIndex : ℕ) :
    annularHodgeCoefficientDoubleSlice radius first second base
        component coordinate input firstIndex secondIndex =
      annularHodgeCoefficientDoubleSlice radius second first base
        component coordinate input secondIndex firstIndex := by
  simp only [annularHodgeCoefficientDoubleSlice]
  rw [replaceFrequencyCoordinate_comm haxes]

/-- The centered index really lies in the declared integer interval. -/
theorem centeredFrequency_mem_interval
    (radius index : ℕ) (hindex : index < centeredFrequencyCount radius) :
    -(radius : ℤ) ≤ centeredFrequency radius index ∧
      centeredFrequency radius index ≤ (radius : ℤ) := by
  unfold centeredFrequencyCount at hindex
  unfold centeredFrequency
  constructor <;> omega

/-- Centered indexing is injective. -/
theorem centeredFrequency_injective (radius : ℕ) :
    Function.Injective (centeredFrequency radius) := by
  intro first second heq
  unfold centeredFrequency at heq
  omega

/-- Absolute value on the left half of a centered chart. -/
theorem natAbs_centeredFrequency_of_le
    {radius index : ℕ} (hindex : index ≤ radius) :
    (centeredFrequency radius index).natAbs = radius - index := by
  unfold centeredFrequency
  have hnonpos : (index : ℤ) - (radius : ℤ) ≤ 0 := by omega
  have hcast :
      (((index : ℤ) - (radius : ℤ)).natAbs : ℤ) =
        ((radius - index : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs, abs_of_nonpos hnonpos]
    omega
  exact_mod_cast hcast

/-- Absolute value on the right half of a centered chart. -/
theorem natAbs_centeredFrequency_of_ge
    {radius index : ℕ} (hindex : radius ≤ index) :
    (centeredFrequency radius index).natAbs = index - radius := by
  unfold centeredFrequency
  have hnonneg : 0 ≤ (index : ℤ) - (radius : ℤ) := by omega
  have hcast :
      (((index : ℤ) - (radius : ℤ)).natAbs : ℤ) =
        ((index - radius : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs, abs_of_nonneg hnonneg]
    omega
  exact_mod_cast hcast

/-! ## Exact scalar trapezoid variation -/

/-- The centered natural chart of one scalar de la Vallée Poussin multiplier. -/
def centeredCoordinateValleePoussinSlice (radius index : ℕ) : ℂ :=
  (coordinateValleePoussinWeight radius
    (centeredFrequency (valleePoussinOuterRadius radius) index) : ℂ)

/-- The same centered scalar chart written as its explicit left ramp, plateau, right ramp, and
zero exterior. -/
def centeredValleePoussinProfile (radius index : ℕ) : ℂ :=
  if index ≤ radius then
    (index + 1 : ℂ) / (radius + 1 : ℂ)
  else if index ≤ 3 * radius + 2 then
    1
  else if index < 4 * radius + 3 then
    (4 * radius + 3 - index : ℕ) / (radius + 1 : ℂ)
  else
    0

theorem centeredValleePoussinProfile_eq_left
    {radius index : ℕ} (hindex : index ≤ radius) :
    centeredValleePoussinProfile radius index =
      (index + 1 : ℂ) / (radius + 1 : ℂ) := by
  simp [centeredValleePoussinProfile, hindex]

theorem centeredValleePoussinProfile_eq_plateau
    {radius index : ℕ} (hlower : radius < index)
    (hupper : index ≤ 3 * radius + 2) :
    centeredValleePoussinProfile radius index = 1 := by
  simp [centeredValleePoussinProfile, show ¬index ≤ radius by omega, hupper]

theorem centeredValleePoussinProfile_eq_right
    {radius index : ℕ} (hlower : 3 * radius + 2 < index)
    (hupper : index < 4 * radius + 3) :
    centeredValleePoussinProfile radius index =
      (4 * radius + 3 - index : ℕ) / (radius + 1 : ℂ) := by
  simp [centeredValleePoussinProfile, show ¬index ≤ radius by omega,
    show ¬index ≤ 3 * radius + 2 by omega, hupper]

theorem centeredValleePoussinProfile_eq_zero
    {radius index : ℕ} (hindex : 4 * radius + 3 ≤ index) :
    centeredValleePoussinProfile radius index = 0 := by
  simp [centeredValleePoussinProfile, show ¬index ≤ radius by omega,
    show ¬index ≤ 3 * radius + 2 by omega, show ¬index < 4 * radius + 3 by omega]

theorem centeredValleePoussinProfile_last (radius : ℕ) :
    centeredValleePoussinProfile radius (4 * radius + 2) =
      1 / (radius + 1 : ℂ) := by
  by_cases hzero : radius = 0
  · subst radius
    norm_num [centeredValleePoussinProfile]
  · rw [centeredValleePoussinProfile_eq_right
      (show 3 * radius + 2 < 4 * radius + 2 by omega)
      (show 4 * radius + 2 < 4 * radius + 3 by omega)]
    have hnumerator : 4 * radius + 3 - (4 * radius + 2) = 1 := by omega
    rw [hnumerator]
    norm_num

/-- The first backward difference of the explicit scalar trapezoid, including both zero-padded
boundaries. -/
theorem zeroPaddedBackwardDifference_centeredValleePoussinProfile
    (radius index : ℕ) :
    zeroPaddedBackwardDifference (centeredValleePoussinProfile radius)
        (4 * radius + 3) index =
      if index ≤ radius then
        1 / (radius + 1 : ℂ)
      else if index ≤ 3 * radius + 2 then
        0
      else if index ≤ 4 * radius + 3 then
        -(1 / (radius + 1 : ℂ))
      else
        0 := by
  have hdenominator : (radius + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show radius + 1 ≠ 0 by omega)
  by_cases hzero : index = 0
  · subst index
    simp [zeroPaddedBackwardDifference, zeroPaddedCoefficient,
      centeredValleePoussinProfile]
  by_cases hleft : index ≤ radius
  · have hindexCount : index < 4 * radius + 3 := by omega
    have hpreviousCount : index - 1 < 4 * radius + 3 := by omega
    have hpreviousLeft : index - 1 ≤ radius := by omega
    simp only [zeroPaddedBackwardDifference, zeroPaddedCoefficient,
      if_pos hindexCount, if_neg hzero, if_pos hpreviousCount]
    rw [centeredValleePoussinProfile_eq_left hleft,
      centeredValleePoussinProfile_eq_left hpreviousLeft]
    simp only [if_pos hleft]
    rw [Nat.cast_sub (show 1 ≤ index by omega)]
    push_cast
    field_simp
    ring
  by_cases hplateau : index ≤ 3 * radius + 2
  · have hindexCount : index < 4 * radius + 3 := by omega
    have hpreviousCount : index - 1 < 4 * radius + 3 := by omega
    have hpreviousLower : radius ≤ index - 1 := by omega
    by_cases hpreviousLeft : index - 1 ≤ radius
    · have hpreviousEq : index - 1 = radius := by omega
      simp only [zeroPaddedBackwardDifference, zeroPaddedCoefficient,
        if_pos hindexCount, if_neg hzero, if_pos hpreviousCount]
      rw [centeredValleePoussinProfile_eq_plateau (show radius < index by omega) hplateau,
        centeredValleePoussinProfile_eq_left hpreviousLeft, hpreviousEq]
      simp only [if_neg hleft, if_pos hplateau]
      field_simp
      ring
    · have hpreviousPlateau : index - 1 ≤ 3 * radius + 2 := by omega
      simp only [zeroPaddedBackwardDifference, zeroPaddedCoefficient,
        if_pos hindexCount, if_neg hzero, if_pos hpreviousCount]
      rw [centeredValleePoussinProfile_eq_plateau (show radius < index by omega) hplateau,
        centeredValleePoussinProfile_eq_plateau (show radius < index - 1 by omega)
          hpreviousPlateau]
      simp [hleft, hplateau]
  by_cases hinterior : index < 4 * radius + 3
  · have hpreviousCount : index - 1 < 4 * radius + 3 := by omega
    by_cases hpreviousPlateau : index - 1 ≤ 3 * radius + 2
    · have hpreviousEq : index - 1 = 3 * radius + 2 := by omega
      have hrightNumerator : 4 * radius + 3 - index = radius := by omega
      simp only [zeroPaddedBackwardDifference, zeroPaddedCoefficient,
        if_pos hinterior, if_neg hzero, if_pos hpreviousCount]
      rw [centeredValleePoussinProfile_eq_right (show 3 * radius + 2 < index by omega)
          hinterior,
        centeredValleePoussinProfile_eq_plateau (show radius < index - 1 by omega)
          hpreviousPlateau,
        hrightNumerator]
      simp only [if_neg hleft, if_neg hplateau, if_pos (show index ≤ 4 * radius + 3 by omega)]
      field_simp
      ring
    · have hpreviousRight : index - 1 < 4 * radius + 3 := by omega
      have hrightStep :
          4 * radius + 3 - (index - 1) =
            (4 * radius + 3 - index) + 1 := by omega
      simp only [zeroPaddedBackwardDifference, zeroPaddedCoefficient,
        if_pos hinterior, if_neg hzero, if_pos hpreviousCount]
      rw [centeredValleePoussinProfile_eq_right (show 3 * radius + 2 < index by omega)
          hinterior,
        centeredValleePoussinProfile_eq_right (show 3 * radius + 2 < index - 1 by omega)
          hpreviousRight,
        hrightStep]
      simp only [if_neg hleft, if_neg hplateau, if_pos (show index ≤ 4 * radius + 3 by omega)]
      push_cast
      field_simp
      ring
  · by_cases hboundary : index ≤ 4 * radius + 3
    · have hindexEq : index = 4 * radius + 3 := by omega
      subst index
      have hpreviousCount : (4 * radius + 3) - 1 < 4 * radius + 3 := by omega
      have hpreviousEq : (4 * radius + 3) - 1 = 4 * radius + 2 := by omega
      simp only [zeroPaddedBackwardDifference, zeroPaddedCoefficient,
        if_neg hinterior, if_neg hzero, if_pos hpreviousCount, zero_sub]
      rw [hpreviousEq, centeredValleePoussinProfile_last]
      simp [hleft, hplateau]
    · have hpreviousOutside : ¬ (index - 1 < 4 * radius + 3) := by omega
      simp [zeroPaddedBackwardDifference, zeroPaddedCoefficient,
        hinterior, hzero, hpreviousOutside, hleft, hplateau, hboundary]

/-- Explicit slope chart of the centered scalar trapezoid. -/
def centeredValleePoussinFirstDifference (radius index : ℕ) : ℂ :=
  if index ≤ radius then
    1 / (radius + 1 : ℂ)
  else if index ≤ 3 * radius + 2 then
    0
  else if index ≤ 4 * radius + 3 then
    -(1 / (radius + 1 : ℂ))
  else
    0

theorem zeroPaddedBackwardDifference_centeredValleePoussinProfile_eq_firstDifference
    (radius index : ℕ) :
    zeroPaddedBackwardDifference (centeredValleePoussinProfile radius)
        (4 * radius + 3) index =
      centeredValleePoussinFirstDifference radius index := by
  simpa [centeredValleePoussinFirstDifference] using
    zeroPaddedBackwardDifference_centeredValleePoussinProfile radius index

/-- A second zero extension is redundant for the already zero-extended slope chart. -/
theorem zeroPaddedCoefficient_firstDifference_eq
    (radius index : ℕ) :
    zeroPaddedCoefficient
        (zeroPaddedBackwardDifference (centeredValleePoussinProfile radius)
          (4 * radius + 3))
        (4 * radius + 4) index =
      centeredValleePoussinFirstDifference radius index := by
  by_cases hindex : index < 4 * radius + 4
  · simp [zeroPaddedCoefficient, hindex,
      zeroPaddedBackwardDifference_centeredValleePoussinProfile_eq_firstDifference]
  · have hleft : ¬index ≤ radius := by omega
    have hplateau : ¬index ≤ 3 * radius + 2 := by omega
    have hright : ¬index ≤ 4 * radius + 3 := by omega
    simp [zeroPaddedCoefficient, hindex, centeredValleePoussinFirstDifference,
      hleft, hplateau, hright]

/-- **Four-corner identity.** The zero-padded second difference of a centered scalar de la Vallée
Poussin chart is supported at exactly its two exterior and two ramp/plateau transitions. -/
theorem zeroPaddedSecondDifference_centeredValleePoussinProfile
    (radius index : ℕ) :
    zeroPaddedSecondDifference (centeredValleePoussinProfile radius)
        (4 * radius + 3) index =
      if index = 0 then
        1 / (radius + 1 : ℂ)
      else if index = radius + 1 then
        -(1 / (radius + 1 : ℂ))
      else if index = 3 * radius + 3 then
        -(1 / (radius + 1 : ℂ))
      else if index = 4 * radius + 4 then
        1 / (radius + 1 : ℂ)
      else
        0 := by
  change
    zeroPaddedCoefficient
          (zeroPaddedBackwardDifference (centeredValleePoussinProfile radius)
            (4 * radius + 3))
          (4 * radius + 4) index -
        (if index = 0 then 0 else
          zeroPaddedCoefficient
            (zeroPaddedBackwardDifference (centeredValleePoussinProfile radius)
              (4 * radius + 3))
            (4 * radius + 4) (index - 1)) = _
  rw [zeroPaddedCoefficient_firstDifference_eq]
  by_cases hzero : index = 0
  · subst index
    simp [centeredValleePoussinFirstDifference]
  · rw [if_neg hzero, zeroPaddedCoefficient_firstDifference_eq]
    unfold centeredValleePoussinFirstDifference
    split_ifs
    all_goals try omega
    all_goals simp

/-- Norm form of the four-corner identity, written additively so finite summation separates the
four addressed corners. -/
theorem norm_zeroPaddedSecondDifference_centeredValleePoussinProfile
    (radius index : ℕ) :
    ‖zeroPaddedSecondDifference (centeredValleePoussinProfile radius)
        (4 * radius + 3) index‖ =
      (if index = 0 then 1 / (radius + 1 : ℝ) else 0) +
      (if index = radius + 1 then 1 / (radius + 1 : ℝ) else 0) +
      (if index = 3 * radius + 3 then 1 / (radius + 1 : ℝ) else 0) +
      (if index = 4 * radius + 4 then 1 / (radius + 1 : ℝ) else 0) := by
  rw [zeroPaddedSecondDifference_centeredValleePoussinProfile]
  have hnorm : ‖(1 / (radius + 1 : ℂ))‖ = 1 / (radius + 1 : ℝ) := by
    rw [norm_div, norm_one]
    congr 1
    convert Complex.norm_natCast (radius + 1) using 1 <;> norm_num
  split_ifs
  all_goals try omega
  all_goals try simp only [norm_neg, norm_zero, zero_add, add_zero]
  all_goals exact hnorm

/-- **Reciprocal-scale scalar curvature.** Total zero-padded second variation of one coordinate
chart is exactly `4 / (radius + 1)`. -/
theorem sum_norm_zeroPaddedSecondDifference_centeredValleePoussinProfile
    (radius : ℕ) :
    (∑ index ∈ Finset.range (4 * radius + 5),
      ‖zeroPaddedSecondDifference (centeredValleePoussinProfile radius)
        (4 * radius + 3) index‖) =
      4 / (radius + 1 : ℝ) := by
  simp_rw [norm_zeroPaddedSecondDifference_centeredValleePoussinProfile]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp [show 0 < 4 * radius + 5 by omega,
    show radius + 1 < 4 * radius + 5 by omega,
    show 3 * radius + 3 < 4 * radius + 5 by omega,
    show 4 * radius + 4 < 4 * radius + 5 by omega]
  ring

/-- The explicit trapezoid is exactly the repository's genuine centered scalar multiplier chart,
including its zero exterior. -/
theorem centeredCoordinateValleePoussinSlice_eq_profile
    (radius index : ℕ) :
    centeredCoordinateValleePoussinSlice radius index =
      centeredValleePoussinProfile radius index := by
  by_cases hleft : index ≤ radius
  · rw [centeredValleePoussinProfile_eq_left hleft]
    have houterIndex : index ≤ valleePoussinOuterRadius radius := by
      unfold valleePoussinOuterRadius
      omega
    have habs := natAbs_centeredFrequency_of_le houterIndex
    by_cases hedge : index = radius
    · subst index
      have habsEdge :
          (centeredFrequency (valleePoussinOuterRadius radius) radius).natAbs =
            radius + 1 := by
        rw [habs]
        unfold valleePoussinOuterRadius
        omega
      simp only [centeredCoordinateValleePoussinSlice]
      rw [coordinateValleePoussinWeight_eq_one radius (by omega)]
      have hdenominator : (radius + 1 : ℂ) ≠ 0 := by
        exact_mod_cast (show radius + 1 ≠ 0 by omega)
      field_simp
      norm_num
    · have hplateau :
          radius + 1 <
            (centeredFrequency (valleePoussinOuterRadius radius) index).natAbs := by
        rw [habs]
        unfold valleePoussinOuterRadius
        omega
      have houter :
          (centeredFrequency (valleePoussinOuterRadius radius) index).natAbs ≤
            valleePoussinOuterRadius radius := by
        rw [habs]
        exact Nat.sub_le _ _
      have hnumerator :
          valleePoussinOuterRadius radius + 1 -
              (centeredFrequency (valleePoussinOuterRadius radius) index).natAbs =
            index + 1 := by
        rw [habs]
        unfold valleePoussinOuterRadius
        omega
      simp only [centeredCoordinateValleePoussinSlice]
      rw [coordinateValleePoussinWeight_eq_taper radius hplateau houter,
        hnumerator]
      push_cast
      rfl
  by_cases hplateau : index ≤ 3 * radius + 2
  · rw [centeredValleePoussinProfile_eq_plateau (show radius < index by omega) hplateau]
    have habsBound :
        (centeredFrequency (valleePoussinOuterRadius radius) index).natAbs ≤
          radius + 1 := by
      by_cases hcenter : index ≤ valleePoussinOuterRadius radius
      · rw [natAbs_centeredFrequency_of_le hcenter]
        unfold valleePoussinOuterRadius
        omega
      · rw [natAbs_centeredFrequency_of_ge (show
            valleePoussinOuterRadius radius ≤ index by omega)]
        unfold valleePoussinOuterRadius
        omega
    simp [centeredCoordinateValleePoussinSlice,
      coordinateValleePoussinWeight_eq_one radius habsBound]
  by_cases hinterior : index < 4 * radius + 3
  · rw [centeredValleePoussinProfile_eq_right (show 3 * radius + 2 < index by omega)
      hinterior]
    have hcenter : valleePoussinOuterRadius radius ≤ index := by
      unfold valleePoussinOuterRadius
      omega
    have habs := natAbs_centeredFrequency_of_ge hcenter
    have houter :
        (centeredFrequency (valleePoussinOuterRadius radius) index).natAbs ≤
          valleePoussinOuterRadius radius := by
      rw [habs]
      unfold valleePoussinOuterRadius
      omega
    have houterPlateau :
        radius + 1 <
          (centeredFrequency (valleePoussinOuterRadius radius) index).natAbs := by
      rw [habs]
      unfold valleePoussinOuterRadius
      omega
    have hnumerator :
        valleePoussinOuterRadius radius + 1 -
            (centeredFrequency (valleePoussinOuterRadius radius) index).natAbs =
          4 * radius + 3 - index := by
      rw [habs]
      unfold valleePoussinOuterRadius
      omega
    simp only [centeredCoordinateValleePoussinSlice]
    rw [coordinateValleePoussinWeight_eq_taper radius houterPlateau houter,
      hnumerator]
    push_cast
    rfl
  · rw [centeredValleePoussinProfile_eq_zero (show 4 * radius + 3 ≤ index by omega)]
    have hcenter : valleePoussinOuterRadius radius ≤ index := by
      unfold valleePoussinOuterRadius
      omega
    have habs := natAbs_centeredFrequency_of_ge hcenter
    have houter :
        valleePoussinOuterRadius radius <
          (centeredFrequency (valleePoussinOuterRadius radius) index).natAbs := by
      rw [habs]
      unfold valleePoussinOuterRadius
      omega
    simp [centeredCoordinateValleePoussinSlice,
      coordinateValleePoussinWeight_eq_zero_of_outer_lt radius houter]

/-- The genuine centered scalar multiplier therefore has the same reciprocal-scale total second
variation as the explicit chart. -/
theorem sum_norm_zeroPaddedSecondDifference_centeredCoordinateValleePoussinSlice
    (radius : ℕ) :
    (∑ index ∈ Finset.range (4 * radius + 5),
      ‖zeroPaddedSecondDifference (centeredCoordinateValleePoussinSlice radius)
        (4 * radius + 3) index‖) =
      4 / (radius + 1 : ℝ) := by
  have hchart :
      centeredCoordinateValleePoussinSlice radius =
        centeredValleePoussinProfile radius := by
    funext index
    exact centeredCoordinateValleePoussinSlice_eq_profile radius index
  rw [hchart]
  exact sum_norm_zeroPaddedSecondDifference_centeredValleePoussinProfile radius

/-- Every zero-padded first difference of the centered scalar chart has reciprocal-scale
magnitude. -/
theorem norm_zeroPaddedBackwardDifference_centeredValleePoussinProfile_le
    (radius index : ℕ) :
    ‖zeroPaddedBackwardDifference (centeredValleePoussinProfile radius)
        (4 * radius + 3) index‖ ≤
      1 / (radius + 1 : ℝ) := by
  rw [zeroPaddedBackwardDifference_centeredValleePoussinProfile_eq_firstDifference]
  have hnorm : ‖(1 / (radius + 1 : ℂ))‖ = 1 / (radius + 1 : ℝ) := by
    rw [norm_div, norm_one]
    congr 1
    convert Complex.norm_natCast (radius + 1) using 1 <;> norm_num
  unfold centeredValleePoussinFirstDifference
  split_ifs
  all_goals try rw [norm_neg]
  all_goals try rw [hnorm]
  all_goals
    simpa only [norm_zero] using
      (show 0 ≤ 1 / (radius + 1 : ℝ) by positivity)

/-- Consequently the total first variation is uniformly bounded by four.  The exact value is two;
the four bound is the scale statement needed by the chart/Hodge product interaction. -/
theorem sum_norm_zeroPaddedBackwardDifference_centeredValleePoussinProfile_le_four
    (radius : ℕ) :
    (∑ index ∈ Finset.range (4 * radius + 4),
      ‖zeroPaddedBackwardDifference (centeredValleePoussinProfile radius)
        (4 * radius + 3) index‖) ≤ 4 := by
  calc
    (∑ index ∈ Finset.range (4 * radius + 4),
      ‖zeroPaddedBackwardDifference (centeredValleePoussinProfile radius)
        (4 * radius + 3) index‖) ≤
        ∑ _index ∈ Finset.range (4 * radius + 4),
          (1 / (radius + 1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro index _hindex
      exact norm_zeroPaddedBackwardDifference_centeredValleePoussinProfile_le radius index
    _ = 4 := by
      simp
      have hdenominator : (radius + 1 : ℝ) ≠ 0 := by positivity
      field_simp

/-- Uniform total first variation for the genuine centered scalar multiplier. -/
theorem sum_norm_zeroPaddedBackwardDifference_centeredCoordinateValleePoussinSlice_le_four
    (radius : ℕ) :
    (∑ index ∈ Finset.range (4 * radius + 4),
      ‖zeroPaddedBackwardDifference (centeredCoordinateValleePoussinSlice radius)
        (4 * radius + 3) index‖) ≤ 4 := by
  have hchart :
      centeredCoordinateValleePoussinSlice radius =
        centeredValleePoussinProfile radius := by
    funext index
    exact centeredCoordinateValleePoussinSlice_eq_profile radius index
  rw [hchart]
  exact sum_norm_zeroPaddedBackwardDifference_centeredValleePoussinProfile_le_four radius

/-- Exact one-coordinate reindexing: the natural centered chart enumerates the genuine integer
interval once, in order, with no cutoff or duplicate. -/
theorem sum_Icc_eq_sum_centeredFrequency
    {M : Type*} [AddCommMonoid M] (radius : ℕ) (f : ℤ → M) :
    (∑ frequency ∈ Finset.Icc (-(radius : ℤ)) (radius : ℤ), f frequency) =
      ∑ index ∈ Finset.range (centeredFrequencyCount radius),
        f (centeredFrequency radius index) := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply]
  have hcount : ((radius : ℤ) + 1 - -(radius : ℤ)).toNat =
      centeredFrequencyCount radius := by
    unfold centeredFrequencyCount
    omega
  rw [hcount]
  apply Finset.sum_congr rfl
  intro index _hindex
  congr 1
  unfold centeredFrequency
  omega

/-- Two centered interval reindexings compose as an exact nested sum. -/
theorem sum_Icc_sum_Icc_eq_sum_centeredFrequency
    {M : Type*} [AddCommMonoid M] (radius : ℕ) (f : ℤ → ℤ → M) :
    (∑ first ∈ Finset.Icc (-(radius : ℤ)) (radius : ℤ),
      ∑ second ∈ Finset.Icc (-(radius : ℤ)) (radius : ℤ), f first second) =
      ∑ firstIndex ∈ Finset.range (centeredFrequencyCount radius),
        ∑ secondIndex ∈ Finset.range (centeredFrequencyCount radius),
          f (centeredFrequency radius firstIndex)
            (centeredFrequency radius secondIndex) := by
  rw [sum_Icc_eq_sum_centeredFrequency]
  apply Finset.sum_congr rfl
  intro firstIndex _hfirst
  exact sum_Icc_eq_sum_centeredFrequency radius
    (fun second ↦ f (centeredFrequency radius firstIndex) second)

/-- Three centered interval reindexings compose as the exact nested population required by
coordinatewise Abel/Fubini. -/
theorem sum_Icc_sum_Icc_sum_Icc_eq_sum_centeredFrequency
    {M : Type*} [AddCommMonoid M] (radius : ℕ) (f : ℤ → ℤ → ℤ → M) :
    (∑ first ∈ Finset.Icc (-(radius : ℤ)) (radius : ℤ),
      ∑ second ∈ Finset.Icc (-(radius : ℤ)) (radius : ℤ),
        ∑ third ∈ Finset.Icc (-(radius : ℤ)) (radius : ℤ),
          f first second third) =
      ∑ firstIndex ∈ Finset.range (centeredFrequencyCount radius),
        ∑ secondIndex ∈ Finset.range (centeredFrequencyCount radius),
          ∑ thirdIndex ∈ Finset.range (centeredFrequencyCount radius),
            f (centeredFrequency radius firstIndex)
              (centeredFrequency radius secondIndex)
              (centeredFrequency radius thirdIndex) := by
  rw [sum_Icc_eq_sum_centeredFrequency]
  apply Finset.sum_congr rfl
  intro firstIndex _hfirst
  exact sum_Icc_sum_Icc_eq_sum_centeredFrequency radius
    (fun second third ↦ f (centeredFrequency radius firstIndex) second third)

/-- Each actual annular Hodge coefficient has magnitude at most one. -/
theorem norm_annularHodgeMultiplierCoefficient_le_one
    (radius : ℕ) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3) :
    ‖annularHodgeMultiplierCoefficient radius frequency component coordinate input‖ ≤ 1 := by
  refine (norm_adjacentHodgeJacobianMultiplierEntry_le_weight
    radius frequency component coordinate input).trans ?_
  exact abs_adjacentValleePoussinWeight_le_one radius frequency

/-- **Linear scale mass.** Every reindexed coordinate slice of an actual scalar Hodge entry has
coefficient mass at most the exact number of lattice points in the outer interval. -/
theorem sum_norm_annularHodgeCoefficientSlice_le_count
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) :
    (∑ index ∈ Finset.range
        (centeredFrequencyCount (valleePoussinOuterRadius (radius + 1))),
      ‖annularHodgeCoefficientSlice radius axis base component coordinate input index‖) ≤
      centeredFrequencyCount (valleePoussinOuterRadius (radius + 1)) := by
  calc
    (∑ index ∈ Finset.range
        (centeredFrequencyCount (valleePoussinOuterRadius (radius + 1))),
      ‖annularHodgeCoefficientSlice radius axis base component coordinate input index‖) ≤
      ∑ _index ∈ Finset.range
        (centeredFrequencyCount (valleePoussinOuterRadius (radius + 1))), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro index _hindex
      exact norm_annularHodgeMultiplierCoefficient_le_one radius _ component coordinate input
    _ = centeredFrequencyCount (valleePoussinOuterRadius (radius + 1)) := by simp

/-- The linear mass constant in the original adjacent radius is exactly `4 radius + 7`. -/
theorem centeredFrequencyCount_adjacentOuterRadius (radius : ℕ) :
    centeredFrequencyCount (valleePoussinOuterRadius (radius + 1)) = 4 * radius + 7 := by
  unfold centeredFrequencyCount valleePoussinOuterRadius
  omega

/-- The preceding slice mass bound in an explicit original-radius chart. -/
theorem sum_norm_annularHodgeCoefficientSlice_le_four_mul_radius_add_seven
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) :
    (∑ index ∈ Finset.range (4 * radius + 7),
      ‖annularHodgeCoefficientSlice radius axis base component coordinate input index‖) ≤
      4 * radius + 7 := by
  simpa [centeredFrequencyCount_adjacentOuterRadius] using
    sum_norm_annularHodgeCoefficientSlice_le_count
      radius axis base component coordinate input

/-! ## Exact second-variation receiver for the actual slice -/

/-- Algebraic second-difference product rule with every interaction term retained. -/
theorem secondBackwardDifference_mul
    (a0 a1 a2 b0 b1 b2 : ℂ) :
    a2 * b2 - 2 * (a1 * b1) + a0 * b0 =
      (a2 - 2 * a1 + a0) * b2 +
        2 * (a1 - a0) * (b2 - b1) +
          a0 * (b2 - 2 * b1 + b0) := by
  ring

/-- Norm receiver for the exact second-difference product rule. -/
theorem norm_secondBackwardDifference_mul_le
    (a0 a1 a2 b0 b1 b2 : ℂ) :
    ‖a2 * b2 - 2 * (a1 * b1) + a0 * b0‖ ≤
      ‖a2 - 2 * a1 + a0‖ * ‖b2‖ +
        2 * ‖a1 - a0‖ * ‖b2 - b1‖ +
          ‖a0‖ * ‖b2 - 2 * b1 + b0‖ := by
  rw [secondBackwardDifference_mul]
  calc
    ‖(a2 - 2 * a1 + a0) * b2 +
        2 * (a1 - a0) * (b2 - b1) +
          a0 * (b2 - 2 * b1 + b0)‖ ≤
      ‖(a2 - 2 * a1 + a0) * b2 +
        2 * (a1 - a0) * (b2 - b1)‖ +
          ‖a0 * (b2 - 2 * b1 + b0)‖ := norm_add_le _ _
    _ ≤ (‖(a2 - 2 * a1 + a0) * b2‖ +
          ‖2 * (a1 - a0) * (b2 - b1)‖) +
        ‖a0 * (b2 - 2 * b1 + b0)‖ := by
      gcongr
      exact norm_add_le _ _
    _ = ‖a2 - 2 * a1 + a0‖ * ‖b2‖ +
        2 * ‖a1 - a0‖ * ‖b2 - b1‖ +
          ‖a0‖ * ‖b2 - 2 * b1 + b0‖ := by
      simp only [norm_mul]
      rw [show ‖(2 : ℂ)‖ = 2 by norm_num]

/-- Exact second-difference decomposition of the actual annular coefficient slice into scalar
chart curvature, chart/Hodge first-difference interaction, and rational Hodge curvature. -/
theorem annularHodgeCoefficientSlice_secondDifference_eq
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) (index : ℕ) :
    annularHodgeCoefficientSlice radius axis base component coordinate input index -
        2 * annularHodgeCoefficientSlice radius axis base component coordinate input (index - 1) +
        annularHodgeCoefficientSlice radius axis base component coordinate input (index - 2) =
      (annularWeightSlice radius axis base index -
          2 * annularWeightSlice radius axis base (index - 1) +
          annularWeightSlice radius axis base (index - 2)) *
        hodgeMultiplierSlice radius axis base component coordinate input index +
      2 * (annularWeightSlice radius axis base (index - 1) -
          annularWeightSlice radius axis base (index - 2)) *
        (hodgeMultiplierSlice radius axis base component coordinate input index -
          hodgeMultiplierSlice radius axis base component coordinate input (index - 1)) +
      annularWeightSlice radius axis base (index - 2) *
        (hodgeMultiplierSlice radius axis base component coordinate input index -
          2 * hodgeMultiplierSlice radius axis base component coordinate input (index - 1) +
          hodgeMultiplierSlice radius axis base component coordinate input (index - 2)) := by
  rw [annularHodgeCoefficientSlice_eq_weight_mul_hodge,
    annularHodgeCoefficientSlice_eq_weight_mul_hodge,
    annularHodgeCoefficientSlice_eq_weight_mul_hodge]
  exact secondBackwardDifference_mul _ _ _ _ _ _

/-- Norm form of the actual second-difference decomposition. -/
theorem norm_annularHodgeCoefficientSlice_secondDifference_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) (index : ℕ) :
    ‖annularHodgeCoefficientSlice radius axis base component coordinate input index -
        2 * annularHodgeCoefficientSlice radius axis base component coordinate input (index - 1) +
        annularHodgeCoefficientSlice radius axis base component coordinate input (index - 2)‖ ≤
      ‖annularWeightSlice radius axis base index -
          2 * annularWeightSlice radius axis base (index - 1) +
          annularWeightSlice radius axis base (index - 2)‖ *
        ‖hodgeMultiplierSlice radius axis base component coordinate input index‖ +
      2 * ‖annularWeightSlice radius axis base (index - 1) -
          annularWeightSlice radius axis base (index - 2)‖ *
        ‖hodgeMultiplierSlice radius axis base component coordinate input index -
          hodgeMultiplierSlice radius axis base component coordinate input (index - 1)‖ +
      ‖annularWeightSlice radius axis base (index - 2)‖ *
        ‖hodgeMultiplierSlice radius axis base component coordinate input index -
          2 * hodgeMultiplierSlice radius axis base component coordinate input (index - 1) +
          hodgeMultiplierSlice radius axis base component coordinate input (index - 2)‖ := by
  rw [annularHodgeCoefficientSlice_eq_weight_mul_hodge,
    annularHodgeCoefficientSlice_eq_weight_mul_hodge,
    annularHodgeCoefficientSlice_eq_weight_mul_hodge]
  exact norm_secondBackwardDifference_mul_le _ _ _ _ _ _

/-- Zero padding preserves a uniform coefficient bound. -/
theorem norm_zeroPaddedCoefficient_le
    {coefficient : ℕ → ℂ} {bound : ℝ} (hbound : 0 ≤ bound)
    (hcoefficient : ∀ index, ‖coefficient index‖ ≤ bound)
    (count index : ℕ) :
    ‖zeroPaddedCoefficient coefficient count index‖ ≤ bound := by
  unfold zeroPaddedCoefficient
  split_ifs
  · exact hcoefficient index
  · simpa using hbound

/-- One zero-padded backward difference costs at most twice a uniform coefficient bound. -/
theorem norm_zeroPaddedBackwardDifference_le
    {coefficient : ℕ → ℂ} {bound : ℝ} (hbound : 0 ≤ bound)
    (hcoefficient : ∀ index, ‖coefficient index‖ ≤ bound)
    (count index : ℕ) :
    ‖zeroPaddedBackwardDifference coefficient count index‖ ≤ 2 * bound := by
  unfold zeroPaddedBackwardDifference
  calc
    ‖zeroPaddedCoefficient coefficient count index -
        (if index = 0 then 0 else
          zeroPaddedCoefficient coefficient count (index - 1))‖ ≤
      ‖zeroPaddedCoefficient coefficient count index‖ +
        ‖if index = 0 then 0 else
          zeroPaddedCoefficient coefficient count (index - 1)‖ := norm_sub_le _ _
    _ ≤ bound + bound := by
      gcongr
      · exact norm_zeroPaddedCoefficient_le hbound hcoefficient count index
      · split_ifs
        · simpa using hbound
        · exact norm_zeroPaddedCoefficient_le hbound hcoefficient count (index - 1)
    _ = 2 * bound := by ring

/-- Two zero-padded backward differences cost at most four times a uniform coefficient bound. -/
theorem norm_zeroPaddedSecondDifference_le
    {coefficient : ℕ → ℂ} {bound : ℝ} (hbound : 0 ≤ bound)
    (hcoefficient : ∀ index, ‖coefficient index‖ ≤ bound)
    (count index : ℕ) :
    ‖zeroPaddedSecondDifference coefficient count index‖ ≤ 4 * bound := by
  unfold zeroPaddedSecondDifference
  have hfirst : ∀ position,
      ‖zeroPaddedBackwardDifference coefficient count position‖ ≤ 2 * bound :=
    fun position ↦
      norm_zeroPaddedBackwardDifference_le hbound hcoefficient count position
  have htwoNonneg : 0 ≤ 2 * bound := mul_nonneg (by norm_num) hbound
  exact (norm_zeroPaddedBackwardDifference_le htwoNonneg hfirst (count + 1) index).trans_eq
    (by ring)

/-! ## Mixed coordinate receiver for iterated Fubini -/

/-- Canonical iterated zero-padded second difference on a finite coefficient rectangle.  Together
with `annularHodgeCoefficientDoubleSlice_comm`, this is the mixed receiver for an addressed Fubini
order. -/
def zeroPaddedMixedSecondDifference
    (coefficient : ℕ → ℕ → ℂ) (firstCount secondCount firstIndex secondIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifference
    (fun first ↦ zeroPaddedSecondDifference (coefficient first) secondCount secondIndex)
    firstCount firstIndex

/-- A uniform coefficient bound costs at most sixteen after two second-difference passages in
distinct coordinates. -/
theorem norm_zeroPaddedMixedSecondDifference_le
    {coefficient : ℕ → ℕ → ℂ} {bound : ℝ} (hbound : 0 ≤ bound)
    (hcoefficient : ∀ first second, ‖coefficient first second‖ ≤ bound)
    (firstCount secondCount firstIndex secondIndex : ℕ) :
    ‖zeroPaddedMixedSecondDifference coefficient
        firstCount secondCount firstIndex secondIndex‖ ≤
      16 * bound := by
  unfold zeroPaddedMixedSecondDifference
  have hinner : ∀ first,
      ‖zeroPaddedSecondDifference (coefficient first) secondCount secondIndex‖ ≤
        4 * bound := fun first ↦
    norm_zeroPaddedSecondDifference_le hbound (hcoefficient first)
      secondCount secondIndex
  have hfourNonneg : 0 ≤ 4 * bound := mul_nonneg (by norm_num) hbound
  exact (norm_zeroPaddedSecondDifference_le hfourNonneg hinner
    firstCount firstIndex).trans_eq (by ring)

/-- Actual mixed second difference of a doubly reindexed annular Hodge coefficient chart. -/
def annularHodgeCoefficientMixedSecondDifference
    (radius : ℕ) (first second : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) (firstIndex secondIndex : ℕ) : ℂ :=
  zeroPaddedMixedSecondDifference
    (annularHodgeCoefficientDoubleSlice radius first second base component coordinate input)
    (4 * radius + 7) (4 * radius + 7) firstIndex secondIndex

/-- Unconditional pointwise guard on the actual mixed Fubini receiver. -/
theorem norm_annularHodgeCoefficientMixedSecondDifference_le_sixteen
    (radius : ℕ) (first second : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) (firstIndex secondIndex : ℕ) :
    ‖annularHodgeCoefficientMixedSecondDifference radius first second base
        component coordinate input firstIndex secondIndex‖ ≤ 16 := by
  unfold annularHodgeCoefficientMixedSecondDifference
  simpa using norm_zeroPaddedMixedSecondDifference_le
    (coefficient := annularHodgeCoefficientDoubleSlice radius first second base
      component coordinate input) (bound := (1 : ℝ))
    (by norm_num)
    (fun firstIndex secondIndex ↦
      norm_annularHodgeMultiplierCoefficient_le_one radius _ component coordinate input)
    (4 * radius + 7) (4 * radius + 7) firstIndex secondIndex

/-- Total mixed second variation of an actual doubly reindexed coefficient chart. -/
def annularHodgeCoefficientMixedSecondVariation
    (radius : ℕ) (first second : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) : ℝ :=
  ∑ firstIndex ∈ Finset.range (4 * radius + 9),
    ∑ secondIndex ∈ Finset.range (4 * radius + 9),
      ‖annularHodgeCoefficientMixedSecondDifference radius first second base
        component coordinate input firstIndex secondIndex‖

/-- Explicit magnitude-only scale guard for the mixed receiver.  Its quadratic growth records the
precise improvement still owed by scalar four-corner sparsity and rational Hodge variation. -/
theorem annularHodgeCoefficientMixedSecondVariation_le
    (radius : ℕ) (first second : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) :
    annularHodgeCoefficientMixedSecondVariation radius first second base
        component coordinate input ≤
      16 * (4 * radius + 9 : ℝ) ^ 2 := by
  unfold annularHodgeCoefficientMixedSecondVariation
  calc
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 9),
        ‖annularHodgeCoefficientMixedSecondDifference radius first second base
          component coordinate input firstIndex secondIndex‖) ≤
      ∑ _firstIndex ∈ Finset.range (4 * radius + 9),
        ∑ _secondIndex ∈ Finset.range (4 * radius + 9), (16 : ℝ) := by
      apply Finset.sum_le_sum
      intro firstIndex _hfirst
      apply Finset.sum_le_sum
      intro secondIndex _hsecond
      exact norm_annularHodgeCoefficientMixedSecondDifference_le_sixteen
        radius first second base component coordinate input firstIndex secondIndex
    _ = 16 * (4 * radius + 9 : ℝ) ^ 2 := by
      simp
      ring

/-- Total zero-padded second variation of one actual reindexed coefficient slice. -/
def annularHodgeCoefficientSliceSecondVariation
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) : ℝ :=
  let count := 4 * radius + 7
  ∑ index ∈ Finset.range (count + 2),
    ‖zeroPaddedSecondDifference
      (annularHodgeCoefficientSlice radius axis base component coordinate input)
      count index‖

/-- A fully unconditional, but deliberately coarse, actual-slice second-variation guard.  It
confirms the receiver and all padding boundaries; the reciprocal-radius improvement must use the
piecewise-linear chart and rational Hodge difference structure rather than magnitude alone. -/
theorem annularHodgeCoefficientSliceSecondVariation_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) :
    annularHodgeCoefficientSliceSecondVariation
        radius axis base component coordinate input ≤
      16 * radius + 36 := by
  unfold annularHodgeCoefficientSliceSecondVariation
  calc
    (∑ index ∈ Finset.range (4 * radius + 7 + 2),
      ‖zeroPaddedSecondDifference
        (annularHodgeCoefficientSlice radius axis base component coordinate input)
        (4 * radius + 7) index‖) ≤
      ∑ _index ∈ Finset.range (4 * radius + 7 + 2), (4 : ℝ) := by
        apply Finset.sum_le_sum
        intro index _hindex
        simpa using norm_zeroPaddedSecondDifference_le (coefficient :=
          annularHodgeCoefficientSlice radius axis base component coordinate input)
          (bound := (1 : ℝ)) (by norm_num)
          (fun position ↦ norm_annularHodgeMultiplierCoefficient_le_one
            radius _ component coordinate input)
          (4 * radius + 7) index
    _ = 16 * radius + 36 := by
      simp
      ring

/-- The actual one-coordinate synthesis receives the exact two-regime Abel envelope with all
current unconditional constants exposed. -/
theorem norm_annularHodgeCoefficientSliceSynthesis_le_currentEnvelope
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) {z : ℂ}
    (hzNorm : ‖z‖ = 1) (hz : z ≠ 1) :
    ‖∑ index ∈ Finset.range (4 * radius + 7),
        annularHodgeCoefficientSlice radius axis base component coordinate input index *
          z ^ index‖ ≤
      min (4 * radius + 7 : ℝ)
        ((16 * radius + 36 : ℝ) / ‖1 - z‖ ^ 2) := by
  refine (norm_finiteCharacterSynthesis_le_mass_min_secondVariation
    (annularHodgeCoefficientSlice radius axis base component coordinate input)
    hzNorm hz (4 * radius + 7)).trans ?_
  apply min_le_min
  · exact_mod_cast sum_norm_annularHodgeCoefficientSlice_le_four_mul_radius_add_seven
      radius axis base component coordinate input
  · apply div_le_div_of_nonneg_right
      (annularHodgeCoefficientSliceSecondVariation_le
        radius axis base component coordinate input) (by positivity)

section Audit

#print axioms coordinateValleePoussinWeight_nonneg
#print axioms coordinateValleePoussinWeight_le_one
#print axioms tensorValleePoussinWeight_mem_unitInterval
#print axioms abs_adjacentValleePoussinWeight_le_one
#print axioms centeredFrequency_mem_interval
#print axioms centeredFrequency_injective
#print axioms natAbs_centeredFrequency_of_le
#print axioms natAbs_centeredFrequency_of_ge
#print axioms zeroPaddedBackwardDifference_centeredValleePoussinProfile
#print axioms zeroPaddedSecondDifference_centeredValleePoussinProfile
#print axioms sum_norm_zeroPaddedSecondDifference_centeredValleePoussinProfile
#print axioms centeredCoordinateValleePoussinSlice_eq_profile
#print axioms sum_norm_zeroPaddedSecondDifference_centeredCoordinateValleePoussinSlice
#print axioms sum_norm_zeroPaddedBackwardDifference_centeredCoordinateValleePoussinSlice_le_four
#print axioms sum_Icc_eq_sum_centeredFrequency
#print axioms sum_Icc_sum_Icc_sum_Icc_eq_sum_centeredFrequency
#print axioms annularHodgeCoefficientSlice_eq_weight_mul_hodge
#print axioms replaceFrequencyCoordinate_comm
#print axioms annularHodgeCoefficientDoubleSlice_comm
#print axioms norm_annularHodgeMultiplierCoefficient_le_one
#print axioms sum_norm_annularHodgeCoefficientSlice_le_four_mul_radius_add_seven
#print axioms secondBackwardDifference_mul
#print axioms norm_annularHodgeCoefficientSlice_secondDifference_le
#print axioms norm_zeroPaddedSecondDifference_le
#print axioms norm_zeroPaddedMixedSecondDifference_le
#print axioms norm_annularHodgeCoefficientMixedSecondDifference_le_sixteen
#print axioms annularHodgeCoefficientMixedSecondVariation_le
#print axioms annularHodgeCoefficientSliceSecondVariation_le
#print axioms norm_annularHodgeCoefficientSliceSynthesis_le_currentEnvelope

end Audit

end Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
