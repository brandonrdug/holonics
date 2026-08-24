import ElementaryHolonics.Millennium.NavierStokesTorusVorticity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Fourier receivers for periodic three-dimensional fields

This module binds a one-periodic Euclidean presentation to the genuine quotient carrier
`(ℝ / ℤ)³` before taking any Fourier receiver.  The field remains primary; its coefficient family
is a receiver indexed by the integer character lattice.
-/

noncomputable section

open ContDiff Function Set Topology MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Soma.Holonics.Millennium.NavierStokesTorusFourier

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan

/- `mFourierCoeff` is normalized with probability Haar measure on every circle.  Keep that same
measure chart explicit throughout this module; the interval-integration `MeasureSpace` instance
has total mass equal to the period and is intentionally a different chart in mathlib. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The integer character lattice of the genuine spatial three-torus. -/
abbrev SpatialFrequency := Fin 3 → ℤ

/-- Fourier coefficient of a field already living on the genuine quotient carrier. -/
def torusSpatialFourierCoeff (field : SpatialTorus → ℂ) (k : SpatialFrequency) : ℂ :=
  UnitAddTorus.mFourierCoeff field k

/-- The `k`-th spatial Fourier receiver of a continuous one-periodic complex scalar field. -/
def scalarSpatialFourierCoeff
    (field : Space → ℂ) (hcontinuous : Continuous field)
    (hperiodic : IsOnePeriodic field) (k : SpatialFrequency) : ℂ :=
  torusSpatialFourierCoeff (periodicTorusLift field hcontinuous hperiodic) k

/-- The remaining two circle coordinates after exposing coordinate zero. -/
abbrev SpatialTorusTail := UnitAddTorus (Fin 2)

/-- Rejoin coordinate zero and the remaining two coordinates. -/
def joinFirstTorus (q : UnitAddCircle) (tail : SpatialTorusTail) : SpatialTorus :=
  Fin.cons q tail

@[simp]
theorem joinFirstTorus_zero (q : UnitAddCircle) (tail : SpatialTorusTail) :
    joinFirstTorus q tail 0 = q := rfl

@[simp]
theorem joinFirstTorus_succ (q : UnitAddCircle) (tail : SpatialTorusTail) (j : Fin 2) :
    joinFirstTorus q tail j.succ = tail j := rfl

/-- The join chart is continuous in both incoming factors. -/
theorem continuous_joinFirstTorus :
    Continuous (fun z : UnitAddCircle × SpatialTorusTail ↦ joinFirstTorus z.1 z.2) := by
  rw [continuous_pi_iff]
  intro i
  fin_cases i
  · exact continuous_fst
  · exact (continuous_apply 0).comp continuous_snd
  · exact (continuous_apply 1).comp continuous_snd

/-- The measurable product chart which exposes coordinate zero. -/
def splitFirstTorus : SpatialTorus ≃ᵐ UnitAddCircle × SpatialTorusTail :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ UnitAddCircle) 0

@[simp]
theorem splitFirstTorus_symm_apply (z : UnitAddCircle × SpatialTorusTail) :
    splitFirstTorus.symm z = joinFirstTorus z.1 z.2 := by
  ext i
  fin_cases i <;>
    simp [splitFirstTorus, joinFirstTorus,
      MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

/-- Haar volume on the genuine three-torus splits as the product of the exposed circle and the
remaining two-torus. -/
theorem splitFirstTorus_measurePreserving :
    MeasurePreserving splitFirstTorus
      (volume : Measure SpatialTorus)
      ((volume : Measure UnitAddCircle).prod (volume : Measure SpatialTorusTail)) := by
  simpa only [splitFirstTorus, volume_pi] using
    (measurePreserving_piFinSuccAbove
      (fun _ : Fin 3 ↦ (volume : Measure UnitAddCircle)) 0)

/-- The zeroth coordinate of a spatial frequency. -/
def firstFrequency (k : SpatialFrequency) : ℤ := k 0

/-- The two-coordinate tail of a spatial frequency. -/
def tailFrequency (k : SpatialFrequency) : Fin 2 → ℤ := fun j ↦ k j.succ

@[simp]
theorem firstFrequency_neg (k : SpatialFrequency) :
    firstFrequency (-k) = -firstFrequency k := rfl

@[simp]
theorem tailFrequency_neg (k : SpatialFrequency) :
    tailFrequency (-k) = -tailFrequency k := by
  rfl

/-- The genuine torus character factors through the exposed-coordinate product chart. -/
theorem mFourier_joinFirstTorus (k : SpatialFrequency)
    (q : UnitAddCircle) (tail : SpatialTorusTail) :
    UnitAddTorus.mFourier k (joinFirstTorus q tail) =
      fourier (firstFrequency k) q * UnitAddTorus.mFourier (tailFrequency k) tail := by
  simp [UnitAddTorus.mFourier, joinFirstTorus, firstFrequency, tailFrequency,
    Fin.prod_univ_succ] ; rfl

/-- A continuous complex field on a compact carrier is Bochner integrable against finite volume. -/
theorem continuousMap_integrable_on_compact
    {X E : Type*} [TopologicalSpace X] [CompactSpace X] [MeasureSpace X]
    [BorelSpace X]
    [IsFiniteMeasure (volume : Measure X)]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopologyEither X E] (f : C(X, E)) : Integrable f := by
  refine Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖ ?_
  filter_upwards [] with x
  exact f.norm_coe_le_norm x

/-- Fubini receipt for one spatial Fourier coefficient after exposing coordinate zero.  The
remaining character is retained as a two-torus receiver rather than replacing the quotient by a
cube. -/
theorem torusSpatialFourierCoeff_eq_integral_tail_fourierCoeff
    (field : C(SpatialTorus, ℂ)) (k : SpatialFrequency) :
    torusSpatialFourierCoeff field k =
      ∫ tail : SpatialTorusTail,
        UnitAddTorus.mFourier (-tailFrequency k) tail *
          fourierCoeff (fun q : UnitAddCircle ↦ field (joinFirstTorus q tail))
            (firstFrequency k) := by
  let integrand : C(SpatialTorus, ℂ) := UnitAddTorus.mFourier (-k) * field
  let splitIntegrand : C(UnitAddCircle × SpatialTorusTail, ℂ) :=
    integrand.comp ⟨_, continuous_joinFirstTorus⟩
  have hchange :
      (∫ x : SpatialTorus, integrand x) =
        ∫ z : UnitAddCircle × SpatialTorusTail, splitIntegrand z := by
    have h := splitFirstTorus_measurePreserving.integral_comp'
      (fun z : UnitAddCircle × SpatialTorusTail ↦
        integrand (splitFirstTorus.symm z))
    simpa [splitIntegrand, splitFirstTorus_symm_apply] using h
  have hIntegrable : Integrable splitIntegrand :=
    continuousMap_integrable_on_compact splitIntegrand
  rw [torusSpatialFourierCoeff, UnitAddTorus.mFourierCoeff]
  change (∫ x : SpatialTorus, integrand x) = _
  rw [hchange]
  have hFubini :
      (∫ z : UnitAddCircle × SpatialTorusTail, splitIntegrand z) =
        ∫ tail : SpatialTorusTail, ∫ q : UnitAddCircle, splitIntegrand (q, tail) := by
    exact integral_prod_symm splitIntegrand hIntegrable
  rw [hFubini]
  apply integral_congr_ae
  filter_upwards [] with tail
  rw [show (∫ q : UnitAddCircle, splitIntegrand (q, tail)) =
      UnitAddTorus.mFourier (-tailFrequency k) tail *
        ∫ q : UnitAddCircle,
          fourier (-(firstFrequency k)) q * field (joinFirstTorus q tail) by
      change (∫ q : UnitAddCircle,
        UnitAddTorus.mFourier (-k) (joinFirstTorus q tail) *
          field (joinFirstTorus q tail)) = _
      simp_rw [mFourier_joinFirstTorus]
      simp only [firstFrequency_neg, tailFrequency_neg]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with q
      ring]
  rfl

/-- On the unit circle, the normalized Haar coefficient is exactly the coefficient of the real
lift over one period. -/
theorem fourierCoeff_eq_fourierCoeffOn_lift
    (field : UnitAddCircle → ℂ) (n : ℤ) :
    fourierCoeff field n =
      fourierCoeffOn (a := (0 : ℝ)) (b := 1) zero_lt_one
        (fun x : ℝ ↦ field (x : UnitAddCircle)) n := by
  rw [fourierCoeff_eq_intervalIntegral field n 0, fourierCoeffOn_eq_integral]
  norm_num

/-- Exact one-circle derivative multiplier, including the zero mode.  The convention is
`fourier n (x mod 1) = exp(2π i n x)`, so differentiation multiplies mode `n` by
`2π i n`. -/
theorem fourierCoeff_derivative_eq_frequency_mul
    (field derivative : C(UnitAddCircle, ℂ))
    (hderivative : ∀ x : ℝ,
      HasDerivAt (fun s : ℝ ↦ field (s : UnitAddCircle))
        (derivative (x : UnitAddCircle)) x)
    (n : ℤ) :
    fourierCoeff derivative n =
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * fourierCoeff field n := by
  let F : ℝ → ℂ := fun x ↦ field (x : UnitAddCircle)
  let F' : ℝ → ℂ := fun x ↦ derivative (x : UnitAddCircle)
  have hcontinuousF' : Continuous F' :=
    derivative.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))
  have hInterval : IntervalIntegrable F' volume (0 : ℝ) 1 :=
    hcontinuousF'.intervalIntegrable _ _
  rw [fourierCoeff_eq_fourierCoeffOn_lift,
    fourierCoeff_eq_fourierCoeffOn_lift]
  change fourierCoeffOn zero_lt_one F' n =
    (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
      fourierCoeffOn zero_lt_one F n
  by_cases hn : n = 0
  · subst n
    have hfundamental : ∫ x in (0 : ℝ)..1, F' x = F 1 - F 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ ↦ hderivative x) hInterval
    rw [fourierCoeffOn_eq_integral]
    simp only [Int.cast_zero, mul_zero, zero_mul, one_div, sub_zero, one_smul,
      neg_zero, fourier_zero]
    have hperiod : F 1 = F 0 := by
      change field ((1 : ℝ) : UnitAddCircle) = field ((0 : ℝ) : UnitAddCircle)
      congr 1
      simpa using (AddCircle.coe_add_period (1 : ℝ) (0 : ℝ))
    rw [hperiod, sub_self] at hfundamental
    simpa only [inv_one, one_smul] using hfundamental
  · have hformula := fourierCoeffOn_of_hasDerivAt zero_lt_one hn
      (fun x _ ↦ hderivative x) hInterval
    have hperiod : F 1 = F 0 := by
      change field ((1 : ℝ) : UnitAddCircle) = field ((0 : ℝ) : UnitAddCircle)
      congr 1
      simpa using (AddCircle.coe_add_period (1 : ℝ) (0 : ℝ))
    have hperiod' :
        field ((1 : ℝ) : UnitAddCircle) = field ((0 : ℝ) : UnitAddCircle) := hperiod
    norm_num only [sub_zero] at hformula
    rw [hperiod', sub_self, mul_zero, zero_sub] at hformula
    have hone : (((1 : ℝ) : ℂ) - ((0 : ℝ) : ℂ)) = 1 := by norm_num
    rw [hone, one_mul] at hformula
    have hmultiplier : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) ≠ 0 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero) hnC
    have hformula' :
        fourierCoeffOn zero_lt_one (fun s : ℝ ↦ field (s : UnitAddCircle)) n =
          fourierCoeffOn zero_lt_one (fun s : ℝ ↦ derivative (s : UnitAddCircle)) n /
            (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
      calc
        _ = 1 / (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))) *
            (-fourierCoeffOn zero_lt_one
              (fun s : ℝ ↦ derivative (s : UnitAddCircle)) n) := by
                simpa only [neg_mul] using hformula
        _ = _ := by field_simp [hmultiplier]
    have hcleared := (div_eq_iff hmultiplier).mp hformula'.symm
    dsimp only [F, F']
    simpa only [mul_comm] using hcleared

/-- Restrict a three-torus field to the coordinate-zero circle while retaining the other two
coordinates as situated parameters. -/
def firstCoordinateSlice (field : C(SpatialTorus, ℂ))
    (tail : SpatialTorusTail) : C(UnitAddCircle, ℂ) where
  toFun q := field (joinFirstTorus q tail)
  continuous_toFun := by
    apply field.continuous.comp
    rw [continuous_pi_iff]
    intro i
    fin_cases i
    · exact continuous_id
    · exact continuous_const
    · exact continuous_const

/-- A torus field `derivative` is the coordinate-zero derivative of `field` when every real lift
of every situated two-torus slice has that derivative. -/
def IsFirstCoordinateDerivative
    (field derivative : C(SpatialTorus, ℂ)) : Prop :=
  ∀ (tail : SpatialTorusTail) (x : ℝ),
    HasDerivAt
      (fun s : ℝ ↦ firstCoordinateSlice field tail (s : UnitAddCircle))
      (firstCoordinateSlice derivative tail (x : UnitAddCircle)) x

/-- Exact derivative-to-frequency identity on the genuine spatial three-torus, for coordinate
zero.  No cube representative occurs: Fubini exposes one Haar circle, proves the one-circle
identity, and glues the remaining two-torus character back into the receiver. -/
theorem torusSpatialFourierCoeff_firstCoordinateDerivative
    (field derivative : C(SpatialTorus, ℂ))
    (hderivative : IsFirstCoordinateDerivative field derivative)
    (k : SpatialFrequency) :
    torusSpatialFourierCoeff derivative k =
      (2 * (Real.pi : ℂ) * Complex.I * (firstFrequency k : ℂ)) *
        torusSpatialFourierCoeff field k := by
  rw [torusSpatialFourierCoeff_eq_integral_tail_fourierCoeff,
    torusSpatialFourierCoeff_eq_integral_tail_fourierCoeff]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with tail
  have hslice := fourierCoeff_derivative_eq_frequency_mul
    (firstCoordinateSlice field tail) (firstCoordinateSlice derivative tail)
    (hderivative tail) (firstFrequency k)
  change UnitAddTorus.mFourier (-tailFrequency k) tail *
      fourierCoeff (firstCoordinateSlice derivative tail) (firstFrequency k) =
    (2 * (Real.pi : ℂ) * Complex.I * (firstFrequency k : ℂ)) *
      (UnitAddTorus.mFourier (-tailFrequency k) tail *
        fourierCoeff (firstCoordinateSlice field tail) (firstFrequency k))
  rw [hslice]
  ring

/-! ## Coordinate reindexing and all three derivative multipliers -/

/-- Swap coordinate zero with a selected coordinate.  This is an involution and therefore gives
the same reindexing on spatial points and on the integer character lattice. -/
def coordinateSwap (coordinate : Fin 3) : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 coordinate

/-- Reindex a torus point by the coordinate swap. -/
def coordinateReindexTorus (coordinate : Fin 3) (q : SpatialTorus) : SpatialTorus :=
  fun i ↦ q (coordinateSwap coordinate i)

/-- The continuous torus automorphism underlying coordinate reindexing. -/
def coordinateReindexTorusMap (coordinate : Fin 3) : C(SpatialTorus, SpatialTorus) where
  toFun := coordinateReindexTorus coordinate
  continuous_toFun := by
    rw [continuous_pi_iff]
    intro i
    exact continuous_apply (coordinateSwap coordinate i)

/-- The same reindexing as a measurable equivalence, for transport of Haar integrals. -/
def coordinateReindexTorusMeasurableEquiv (coordinate : Fin 3) :
    SpatialTorus ≃ᵐ SpatialTorus :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin 3 ↦ UnitAddCircle) (coordinateSwap coordinate)

@[simp]
theorem coordinateReindexTorusMeasurableEquiv_apply
    (coordinate : Fin 3) (q : SpatialTorus) :
    coordinateReindexTorusMeasurableEquiv coordinate q =
      coordinateReindexTorus coordinate q := by
  ext i
  change (Equiv.piCongrLeft (fun _ : Fin 3 ↦ UnitAddCircle)
      (coordinateSwap coordinate) q) i = q (coordinateSwap coordinate i)
  rw [Equiv.piCongrLeft_apply]
  simp [coordinateSwap, Equiv.swap_apply_self]

@[simp]
theorem coordinateReindexTorus_self
    (coordinate : Fin 3) (q : SpatialTorus) :
    coordinateReindexTorus coordinate (coordinateReindexTorus coordinate q) = q := by
  ext i
  simp [coordinateReindexTorus, coordinateSwap, Equiv.swap_apply_self]

/-- Coordinate reindexing preserves probability Haar volume on the genuine three-torus. -/
theorem coordinateReindexTorus_measurePreserving (coordinate : Fin 3) :
    MeasurePreserving (coordinateReindexTorusMeasurableEquiv coordinate)
      (volume : Measure SpatialTorus) (volume : Measure SpatialTorus) := by
  simpa only [coordinateReindexTorusMeasurableEquiv, volume_pi] using
    (measurePreserving_piCongrLeft
      (fun _ : Fin 3 ↦ (volume : Measure UnitAddCircle)) (coordinateSwap coordinate))

/-- Reindex a frequency by the same coordinate swap. -/
def coordinateReindexFrequency (coordinate : Fin 3) (k : SpatialFrequency) :
    SpatialFrequency :=
  fun i ↦ k (coordinateSwap coordinate i)

@[simp]
theorem coordinateReindexFrequency_zero (coordinate : Fin 3) :
    coordinateReindexFrequency coordinate 0 = 0 := rfl

@[simp]
theorem coordinateReindexFrequency_apply_zero
    (coordinate : Fin 3) (k : SpatialFrequency) :
    coordinateReindexFrequency coordinate k 0 = k coordinate := by
  simp [coordinateReindexFrequency, coordinateSwap]

@[simp]
theorem coordinateReindexFrequency_neg
    (coordinate : Fin 3) (k : SpatialFrequency) :
    coordinateReindexFrequency coordinate (-k) =
      -coordinateReindexFrequency coordinate k := rfl

/-- Reindexing both a torus point and its character frequency leaves the character unchanged. -/
theorem mFourier_coordinateReindex
    (coordinate : Fin 3) (k : SpatialFrequency) (q : SpatialTorus) :
    UnitAddTorus.mFourier (coordinateReindexFrequency coordinate k)
        (coordinateReindexTorus coordinate q) =
      UnitAddTorus.mFourier k q := by
  simp only [UnitAddTorus.mFourier, coordinateReindexFrequency,
    coordinateReindexTorus]
  change (∏ i : Fin 3,
      (fun j ↦ fourier (k j) (q j)) (coordinateSwap coordinate i)) = _
  exact Equiv.prod_comp (coordinateSwap coordinate) (fun j ↦ fourier (k j) (q j))

/-- Fourier coefficients commute exactly with simultaneous coordinate reindexing of the field
and frequency.  This is the transport receipt which lets the coordinate-zero Fubini proof serve
all three spatial directions. -/
theorem torusSpatialFourierCoeff_coordinateReindex
    (coordinate : Fin 3) (field : C(SpatialTorus, ℂ)) (k : SpatialFrequency) :
    torusSpatialFourierCoeff
        (field.comp (coordinateReindexTorusMap coordinate))
        (coordinateReindexFrequency coordinate k) =
      torusSpatialFourierCoeff field k := by
  rw [torusSpatialFourierCoeff, UnitAddTorus.mFourierCoeff,
    torusSpatialFourierCoeff, UnitAddTorus.mFourierCoeff]
  let integrand : SpatialTorus → ℂ :=
    fun q ↦ UnitAddTorus.mFourier (-k) q * field q
  calc
    (∫ q : SpatialTorus,
        UnitAddTorus.mFourier (-coordinateReindexFrequency coordinate k) q •
          (field.comp (coordinateReindexTorusMap coordinate)) q) =
      ∫ q : SpatialTorus,
        integrand (coordinateReindexTorusMeasurableEquiv coordinate q) := by
          apply integral_congr_ae
          filter_upwards [] with q
          rw [coordinateReindexTorusMeasurableEquiv_apply]
          change UnitAddTorus.mFourier (-coordinateReindexFrequency coordinate k) q *
              field (coordinateReindexTorus coordinate q) = _
          rw [← coordinateReindexFrequency_neg]
          have hcharacter := mFourier_coordinateReindex coordinate (-k)
            (coordinateReindexTorus coordinate q)
          simp only [coordinateReindexTorus_self] at hcharacter
          rw [hcharacter]
    _ = ∫ q : SpatialTorus, integrand q :=
      (coordinateReindexTorus_measurePreserving coordinate).integral_comp' integrand

/-- A selected coordinate derivative is the coordinate-zero derivative after the exact torus
reindexing above.  This definition carries the other two coordinates as genuine quotient
parameters and contains no cube representative. -/
def IsCoordinateDerivative (coordinate : Fin 3)
    (field derivative : C(SpatialTorus, ℂ)) : Prop :=
  IsFirstCoordinateDerivative
    (field.comp (coordinateReindexTorusMap coordinate))
    (derivative.comp (coordinateReindexTorusMap coordinate))

/-- **All-coordinate derivative multiplier on the genuine three-torus.**  One coordinate swap,
one Haar-preserving reindexing receipt, and the coordinate-zero Fubini theorem give the exact
identity simultaneously for coordinates `0`, `1`, and `2`. -/
theorem torusSpatialFourierCoeff_coordinateDerivative
    (coordinate : Fin 3) (field derivative : C(SpatialTorus, ℂ))
    (hderivative : IsCoordinateDerivative coordinate field derivative)
    (k : SpatialFrequency) :
    torusSpatialFourierCoeff derivative k =
      (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
        torusSpatialFourierCoeff field k := by
  have h := torusSpatialFourierCoeff_firstCoordinateDerivative
    (field.comp (coordinateReindexTorusMap coordinate))
    (derivative.comp (coordinateReindexTorusMap coordinate))
    hderivative (coordinateReindexFrequency coordinate k)
  rw [torusSpatialFourierCoeff_coordinateReindex,
    torusSpatialFourierCoeff_coordinateReindex] at h
  simpa [firstFrequency] using h

/-! ## The mean fibre and the vector receiver -/

/-- The full zero frequency is exactly the Haar mean of the field. -/
theorem torusSpatialFourierCoeff_zero_eq_mean (field : SpatialTorus → ℂ) :
    torusSpatialFourierCoeff field 0 = ∫ q : SpatialTorus, field q := by
  simp [torusSpatialFourierCoeff, UnitAddTorus.mFourierCoeff,
    UnitAddTorus.mFourier_zero]

/-- A periodic coordinate derivative carries no full zero mode.  This is the exact mean
obstruction: the derivative receiver cannot reconstruct the constant component of its source. -/
theorem torusSpatialFourierCoeff_firstDerivative_zero
    (field derivative : C(SpatialTorus, ℂ))
    (hderivative : IsFirstCoordinateDerivative field derivative) :
    torusSpatialFourierCoeff derivative 0 = 0 := by
  simpa [firstFrequency] using
    torusSpatialFourierCoeff_firstCoordinateDerivative field derivative hderivative 0

/-- The coordinate-zero multiplier vanishes exactly on the frequency hyperplane `k₀ = 0`.
Thus one coordinate derivative has a larger reconstruction fibre than merely the constant mode;
the intersection of all three coordinate multiplier kernels is the full zero frequency. -/
theorem firstCoordinateMultiplier_eq_zero_iff (k : SpatialFrequency) :
    2 * (Real.pi : ℂ) * Complex.I * (firstFrequency k : ℂ) = 0 ↔
      firstFrequency k = 0 := by
  have hconstant : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero
  rw [mul_eq_zero]
  simp only [hconstant, false_or, Int.cast_eq_zero]

/-- Coordinatewise complexification of the real Euclidean velocity carrier. -/
def complexifySpace (v : Space) : Fin 3 → ℂ := fun i ↦ (v i : ℂ)

/-- Complexification is a continuous receiver on the finite-dimensional real carrier. -/
theorem continuous_complexifySpace : Continuous complexifySpace := by
  rw [continuous_pi_iff]
  intro i
  exact Complex.continuous_ofReal.comp
    ((continuous_apply i).comp (EuclideanSpace.equiv (Fin 3) ℝ).continuous)

/-- A real continuous field stays continuous after coordinatewise complexification. -/
theorem continuous_complexify_field
    {field : Space → Space} (hfield : Continuous field) :
    Continuous (fun x ↦ complexifySpace (field x)) :=
  continuous_complexifySpace.comp hfield

/-- Complexification preserves every unit-period incidence. -/
theorem isOnePeriodic_complexify_field
    {field : Space → Space} (hfield : IsOnePeriodic field) :
    IsOnePeriodic (fun x ↦ complexifySpace (field x)) := by
  intro x j
  exact congrArg complexifySpace (hfield x j)

/-- The vector Fourier receiver is the coordinatewise genuine-torus coefficient of the
complexified real field. -/
def vectorSpatialFourierCoeff
    (field : Space → Space) (hcontinuous : Continuous field)
    (hperiodic : IsOnePeriodic field) (k : SpatialFrequency) : Fin 3 → ℂ :=
  UnitAddTorus.mFourierCoeff
    (periodicTorusLift (fun x ↦ complexifySpace (field x))
      (continuous_complexify_field hcontinuous)
      (isOnePeriodic_complexify_field hperiodic)) k

/-- The vector receiver is genuinely the coefficient of the quotient lift, not a tuple of cube
surrogates. -/
theorem vectorSpatialFourierCoeff_eq_mFourierCoeff
    (field : Space → Space) (hcontinuous : Continuous field)
    (hperiodic : IsOnePeriodic field) (k : SpatialFrequency) :
    vectorSpatialFourierCoeff field hcontinuous hperiodic k =
      UnitAddTorus.mFourierCoeff
        (periodicTorusLift (fun x ↦ complexifySpace (field x))
          (continuous_complexify_field hcontinuous)
          (isOnePeriodic_complexify_field hperiodic)) k := rfl

/-! ## Actual smooth periodic velocity derivatives -/

open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy

/-- One complexified component of a real velocity slice. -/
def complexVelocityComponent (velocity : InitialVelocity) (component : Fin 3) : Space → ℂ :=
  fun x ↦ (velocity x component : ℂ)

/-- One complexified entry of the actual Fréchet-Jacobian chart. -/
def complexJacobianComponent (velocity : InitialVelocity)
    (component coordinate : Fin 3) : Space → ℂ :=
  fun x ↦ (velocityJacobianAt velocity x component coordinate : ℂ)

theorem continuous_complexVelocityComponent
    {velocity : InitialVelocity} (hvelocity : Continuous velocity) (component : Fin 3) :
    Continuous (complexVelocityComponent velocity component) := by
  exact Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj component).continuous.comp hvelocity)

theorem isOnePeriodic_complexVelocityComponent
    {velocity : InitialVelocity} (hperiodic : IsOnePeriodic velocity) (component : Fin 3) :
    IsOnePeriodic (complexVelocityComponent velocity component) := by
  intro x i
  exact congrArg (fun v : Space ↦ (v component : ℂ)) (hperiodic x i)

/-- A genuinely `C¹` velocity has continuous actual Jacobian components; this explicitly
prevents the totalized `fderiv` chart from being used without its differentiability admission. -/
theorem continuous_complexJacobianComponent
    {velocity : InitialVelocity} (hvelocity : ContDiff ℝ 1 velocity)
    (component coordinate : Fin 3) :
    Continuous (complexJacobianComponent velocity component coordinate) := by
  have haction : Continuous (fun x ↦
      (fderiv ℝ velocity x) (EuclideanSpace.basisFun (Fin 3) ℝ coordinate)) :=
    (ContinuousLinearMap.apply ℝ Space
      (EuclideanSpace.basisFun (Fin 3) ℝ coordinate)).continuous.comp
        (hvelocity.continuous_fderiv (by norm_num))
  have hcoordinate : Continuous (fun x ↦
      ((fderiv ℝ velocity x) (EuclideanSpace.basisFun (Fin 3) ℝ coordinate)) component) :=
    (EuclideanSpace.proj component).continuous.comp haction
  simpa [complexJacobianComponent, velocityJacobianAt, jacobianMatrix_apply] using
    Complex.continuous_ofReal.comp hcoordinate

/-- Differentiation preserves the periodic incidence of every actual Jacobian component. -/
theorem isOnePeriodic_complexJacobianComponent
    {velocity : InitialVelocity} (hperiodic : IsOnePeriodic velocity)
    (component coordinate : Fin 3) :
    IsOnePeriodic (complexJacobianComponent velocity component coordinate) := by
  intro x i
  exact congrArg
    (fun D : Space →L[ℝ] Space ↦
      (jacobianMatrix D component coordinate : ℂ))
    (fderiv_isOnePeriodic velocity hperiodic x i)

/-- The explicit Euclidean line whose quotient is the selected-coordinate circle after
reindexing.  The anchor is retained so differentiation occurs at the addressed real parameter. -/
def coordinateLinePoint (coordinate : Fin 3) (tail : SpatialTorusTail)
    (anchor s : ℝ) : Space :=
  euclideanRepresentative
      (coordinateReindexTorus coordinate
        (joinFirstTorus (anchor : UnitAddCircle) tail)) +
    (s - anchor) • EuclideanSpace.basisFun (Fin 3) ℝ coordinate

/-- The line above projects exactly to the reindexed genuine-torus slice. -/
theorem euclideanToSpatialTorus_coordinateLinePoint
    (coordinate : Fin 3) (tail : SpatialTorusTail) (anchor s : ℝ) :
    euclideanToSpatialTorus (coordinateLinePoint coordinate tail anchor s) =
      coordinateReindexTorus coordinate
        (joinFirstTorus (s : UnitAddCircle) tail) := by
  let q := coordinateReindexTorus coordinate
    (joinFirstTorus (anchor : UnitAddCircle) tail)
  have hrepresentative := euclideanToSpatialTorus_representative q
  ext i
  have hi := congrFun hrepresentative i
  fin_cases coordinate <;> fin_cases i <;>
    simp [coordinateLinePoint, q, coordinateReindexTorus, coordinateSwap,
      Equiv.swap_apply_def, joinFirstTorus,
      euclideanToSpatialTorus, piToSpatialTorus] at hi ⊢ <;>
    simp [hi, sub_eq_add_neg, add_assoc]
  all_goals rfl

/-- The coordinate line has the selected Euclidean basis vector as its exact derivative. -/
theorem coordinateLinePoint_hasDerivAt
    (coordinate : Fin 3) (tail : SpatialTorusTail) (anchor : ℝ) :
    HasDerivAt (coordinateLinePoint coordinate tail anchor)
      (EuclideanSpace.basisFun (Fin 3) ℝ coordinate) anchor := by
  let base := euclideanRepresentative
    (coordinateReindexTorus coordinate
      (joinFirstTorus (anchor : UnitAddCircle) tail))
  change HasDerivAt
    (fun s : ℝ ↦ base + (s - anchor) •
      EuclideanSpace.basisFun (Fin 3) ℝ coordinate)
    (EuclideanSpace.basisFun (Fin 3) ℝ coordinate) anchor
  convert (hasDerivAt_const anchor base).add
    (((hasDerivAt_id anchor).sub_const anchor).smul_const
      (EuclideanSpace.basisFun (Fin 3) ℝ coordinate)) using 1 <;> simp

/-- The quotient lifts of an actual `C¹`, one-periodic velocity component and its actual
Jacobian entry form the selected-coordinate derivative pair required by the Fourier theorem. -/
theorem periodicTorusLift_isCoordinateDerivative
    {velocity : InitialVelocity} (hvelocity : ContDiff ℝ 1 velocity)
    (hperiodic : IsOnePeriodic velocity) (component coordinate : Fin 3) :
    IsCoordinateDerivative coordinate
      (periodicTorusLift (complexVelocityComponent velocity component)
        (continuous_complexVelocityComponent hvelocity.continuous component)
        (isOnePeriodic_complexVelocityComponent hperiodic component))
      (periodicTorusLift (complexJacobianComponent velocity component coordinate)
        (continuous_complexJacobianComponent hvelocity component coordinate)
        (isOnePeriodic_complexJacobianComponent hperiodic component coordinate)) := by
  intro tail anchor
  let velocityLift := periodicTorusLift (complexVelocityComponent velocity component)
    (continuous_complexVelocityComponent hvelocity.continuous component)
    (isOnePeriodic_complexVelocityComponent hperiodic component)
  let derivativeLift := periodicTorusLift
    (complexJacobianComponent velocity component coordinate)
    (continuous_complexJacobianComponent hvelocity component coordinate)
    (isOnePeriodic_complexJacobianComponent hperiodic component coordinate)
  have hvelocityLine :
      (fun s : ℝ ↦ firstCoordinateSlice
        (velocityLift.comp (coordinateReindexTorusMap coordinate)) tail
          (s : UnitAddCircle)) =
      fun s : ℝ ↦ complexVelocityComponent velocity component
        (coordinateLinePoint coordinate tail anchor s) := by
    funext s
    change velocityLift
        (coordinateReindexTorus coordinate
          (joinFirstTorus (s : UnitAddCircle) tail)) = _
    rw [← euclideanToSpatialTorus_coordinateLinePoint]
    exact periodicTorusLift_projection _ _ _ _
  have hderivativeAt :
      firstCoordinateSlice
        (derivativeLift.comp (coordinateReindexTorusMap coordinate)) tail
          (anchor : UnitAddCircle) =
      complexJacobianComponent velocity component coordinate
        (coordinateLinePoint coordinate tail anchor anchor) := by
    change derivativeLift
        (coordinateReindexTorus coordinate
          (joinFirstTorus (anchor : UnitAddCircle) tail)) = _
    rw [← euclideanToSpatialTorus_coordinateLinePoint]
    exact periodicTorusLift_projection _ _ _ _
  have hvelocityAlongLine : HasDerivAt
      (fun s : ℝ ↦ complexVelocityComponent velocity component
        (coordinateLinePoint coordinate tail anchor s))
      (complexJacobianComponent velocity component coordinate
        (coordinateLinePoint coordinate tail anchor anchor)) anchor := by
    have hcomposed :=
      (hvelocity.differentiable (by norm_num)
        (coordinateLinePoint coordinate tail anchor anchor)).hasFDerivAt.comp_hasDerivAt
          anchor (coordinateLinePoint_hasDerivAt coordinate tail anchor)
    have hreal := (EuclideanSpace.proj component).hasFDerivAt.comp_hasDerivAt
      anchor hcomposed
    have hcomplex := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt anchor hreal
    simpa [Function.comp_def, complexVelocityComponent, complexJacobianComponent,
      velocityJacobianAt, jacobianMatrix_apply] using hcomplex
  rw [hvelocityLine, hderivativeAt]
  exact hvelocityAlongLine

/-- Evaluating the vector Fourier receiver is exactly the scalar coefficient of the matching
complexified component. -/
theorem vectorSpatialFourierCoeff_apply
    (velocity : InitialVelocity) (hcontinuous : Continuous velocity)
    (hperiodic : IsOnePeriodic velocity) (k : SpatialFrequency) (component : Fin 3) :
    vectorSpatialFourierCoeff velocity hcontinuous hperiodic k component =
      torusSpatialFourierCoeff
        (periodicTorusLift (complexVelocityComponent velocity component)
          (continuous_complexVelocityComponent hcontinuous component)
          (isOnePeriodic_complexVelocityComponent hperiodic component)) k := by
  let vectorLift := periodicTorusLift (fun x ↦ complexifySpace (velocity x))
    (continuous_complexify_field hcontinuous)
    (isOnePeriodic_complexify_field hperiodic)
  let scalarLift := periodicTorusLift (complexVelocityComponent velocity component)
    (continuous_complexVelocityComponent hcontinuous component)
    (isOnePeriodic_complexVelocityComponent hperiodic component)
  let integrand : C(SpatialTorus, Fin 3 → ℂ) := {
    toFun := fun q ↦ UnitAddTorus.mFourier (-k) q • vectorLift q
    continuous_toFun :=
      (UnitAddTorus.mFourier (-k)).continuous.smul vectorLift.continuous }
  have hintegrable : Integrable integrand :=
    continuousMap_integrable_on_compact integrand
  let projection : (Fin 3 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj component
  rw [vectorSpatialFourierCoeff, UnitAddTorus.mFourierCoeff,
    torusSpatialFourierCoeff, UnitAddTorus.mFourierCoeff]
  change projection (∫ q : SpatialTorus, integrand q) = _
  rw [← projection.integral_comp_comm hintegrable]
  apply integral_congr_ae
  filter_upwards [] with q
  change UnitAddTorus.mFourier (-k) q * vectorLift q component =
    UnitAddTorus.mFourier (-k) q * scalarLift q
  congr 1

/-- Matrix of genuine-torus Fourier coefficients of the admitted actual spatial Jacobian. -/
def actualJacobianFourierMode
    (velocity : InitialVelocity) (hvelocity : ContDiff ℝ 1 velocity)
    (hperiodic : IsOnePeriodic velocity) (k : SpatialFrequency) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  fun component coordinate ↦
    torusSpatialFourierCoeff
      (periodicTorusLift (complexJacobianComponent velocity component coordinate)
        (continuous_complexJacobianComponent hvelocity component coordinate)
        (isOnePeriodic_complexJacobianComponent hperiodic component coordinate)) k

/-- The nine actual Jacobian coefficients of a smooth periodic velocity obey the nine exact
derivative multipliers. -/
theorem actualJacobianFourierMode_eq_multiplier
    (velocity : InitialVelocity) (hvelocity : ContDiff ℝ 1 velocity)
    (hperiodic : IsOnePeriodic velocity) (k : SpatialFrequency)
    (component coordinate : Fin 3) :
    actualJacobianFourierMode velocity hvelocity hperiodic k component coordinate =
      (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
        vectorSpatialFourierCoeff velocity hvelocity.continuous hperiodic k component := by
  rw [vectorSpatialFourierCoeff_apply]
  exact torusSpatialFourierCoeff_coordinateDerivative coordinate _ _
    (periodicTorusLift_isCoordinateDerivative hvelocity hperiodic component coordinate) k

/-- The actual vorticity of a `C¹` velocity slice is continuous. -/
theorem continuous_vorticityAt
    {velocity : InitialVelocity} (hvelocity : ContDiff ℝ 1 velocity) :
    Continuous (fun x ↦ vorticityAt velocity x) := by
  have hderivative := hvelocity.continuous_fderiv (by norm_num)
  simpa [vorticityAt, velocityJacobianAt] using
    derivativeCurlLinearMap.continuous.comp hderivative

/-- The actual vorticity preserves every unit-period incidence of its source velocity. -/
theorem isOnePeriodic_vorticityAt
    {velocity : InitialVelocity} (hperiodic : IsOnePeriodic velocity) :
    IsOnePeriodic (fun x ↦ vorticityAt velocity x) := by
  intro x i
  exact congrArg derivativeCurlLinearMap
    (fderiv_isOnePeriodic velocity hperiodic x i)

/-- Fourier coefficients preserve subtraction of continuous scalar torus fields. -/
theorem torusSpatialFourierCoeff_sub
    (field₁ field₂ : C(SpatialTorus, ℂ)) (k : SpatialFrequency) :
    torusSpatialFourierCoeff (field₁ - field₂) k =
      torusSpatialFourierCoeff field₁ k - torusSpatialFourierCoeff field₂ k := by
  simp only [torusSpatialFourierCoeff, UnitAddTorus.mFourierCoeff]
  have h₁ : Integrable (fun q : SpatialTorus ↦
      UnitAddTorus.mFourier (-k) q * field₁ q) :=
    continuousMap_integrable_on_compact (UnitAddTorus.mFourier (-k) * field₁)
  have h₂ : Integrable (fun q : SpatialTorus ↦
      UnitAddTorus.mFourier (-k) q * field₂ q) :=
    continuousMap_integrable_on_compact (UnitAddTorus.mFourier (-k) * field₂)
  calc
    (∫ q : SpatialTorus, UnitAddTorus.mFourier (-k) q • (field₁ - field₂) q) =
        ∫ q : SpatialTorus,
          UnitAddTorus.mFourier (-k) q * field₁ q -
            UnitAddTorus.mFourier (-k) q * field₂ q := by
              apply integral_congr_ae
              filter_upwards [] with q
              change _ * (field₁ q - field₂ q) = _
              ring
    _ = _ := integral_sub h₁ h₂

/-- Fourier coefficients preserve addition of continuous scalar torus fields. -/
theorem torusSpatialFourierCoeff_add
    (field₁ field₂ : C(SpatialTorus, ℂ)) (k : SpatialFrequency) :
    torusSpatialFourierCoeff (field₁ + field₂) k =
      torusSpatialFourierCoeff field₁ k + torusSpatialFourierCoeff field₂ k := by
  simp only [torusSpatialFourierCoeff, UnitAddTorus.mFourierCoeff]
  have h₁ : Integrable (fun q : SpatialTorus ↦
      UnitAddTorus.mFourier (-k) q * field₁ q) :=
    continuousMap_integrable_on_compact (UnitAddTorus.mFourier (-k) * field₁)
  have h₂ : Integrable (fun q : SpatialTorus ↦
      UnitAddTorus.mFourier (-k) q * field₂ q) :=
    continuousMap_integrable_on_compact (UnitAddTorus.mFourier (-k) * field₂)
  calc
    (∫ q : SpatialTorus, UnitAddTorus.mFourier (-k) q • (field₁ + field₂) q) =
        ∫ q : SpatialTorus,
          UnitAddTorus.mFourier (-k) q * field₁ q +
            UnitAddTorus.mFourier (-k) q * field₂ q := by
              apply integral_congr_ae
              filter_upwards [] with q
              change _ * (field₁ q + field₂ q) = _
              ring
    _ = _ := integral_add h₁ h₂

/-! ## Curl at one frequency -/

/-- Complex coordinate vector carried by one Fourier mode. -/
abbrev ComplexVector := Fin 3 → ℂ

/-- Complex Jacobian chart carried by one Fourier mode. -/
abbrev ComplexMatrix3 := Matrix (Fin 3) (Fin 3) ℂ

/-- The integer frequency embedded coordinatewise in the complex receiver. -/
def complexFrequencyVector (k : SpatialFrequency) : ComplexVector := fun j ↦ (k j : ℂ)

/-- Complex cross interaction, with the same orientation as the repository's real `cross`. -/
def complexCross (a b : ComplexVector) : ComplexVector := crossProduct a b

/-- Curl of a complex Jacobian chart, with rows indexing output components and columns indexing
spatial derivatives. -/
def complexCurlFromJacobian (J : ComplexMatrix3) : ComplexVector := ![
  J 2 1 - J 1 2,
  J 0 2 - J 2 0,
  J 1 0 - J 0 1]

/-- Jacobian coefficient forced by the derivative multiplier convention
`∂ⱼ ↔ 2π i kⱼ`. -/
def fourierJacobianMode (k : SpatialFrequency) (velocityMode : ComplexVector) :
    ComplexMatrix3 :=
  fun component coordinate ↦
    (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) * velocityMode component

/-- The oriented curl multiplier at frequency `k`. -/
def frequencyCurlMultiplier (k : SpatialFrequency) (velocityMode : ComplexVector) :
    ComplexVector :=
  (2 * (Real.pi : ℂ) * Complex.I) •
    complexCross (complexFrequencyVector k) velocityMode

/-- **Exact curl mode identity.**  Under the coefficient convention proved above, the Jacobian
mode curls to `2π i (k × û(k))`.  This is an algebraic consequence of the three derivative
multipliers; it does not assume a BKM inequality, Biot--Savart bound, or local-existence theorem. -/
theorem complexCurl_fourierJacobianMode
    (k : SpatialFrequency) (velocityMode : ComplexVector) :
    complexCurlFromJacobian (fourierJacobianMode k velocityMode) =
      frequencyCurlMultiplier k velocityMode := by
  ext i
  fin_cases i <;>
    simp [complexCurlFromJacobian, fourierJacobianMode, frequencyCurlMultiplier,
      complexCross, complexFrequencyVector, crossProduct] <;>
    ring

/-- Curl-mode gluing receipt from separately established component derivative coefficients.  This
is the interface an all-coordinate analytic derivative theorem must supply. -/
theorem complexCurl_eq_frequencyCurlMultiplier_of_derivativeCoefficients
    (k : SpatialFrequency) (velocityMode : ComplexVector) (jacobianMode : ComplexMatrix3)
    (hderivatives : ∀ component coordinate,
      jacobianMode component coordinate =
        (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
          velocityMode component) :
    complexCurlFromJacobian jacobianMode = frequencyCurlMultiplier k velocityMode := by
  have hmode : jacobianMode = fourierJacobianMode k velocityMode := by
    ext component coordinate
    exact hderivatives component coordinate
  rw [hmode, complexCurl_fourierJacobianMode]

/-! ## Curl and divergence of an actual periodic velocity slice -/

/-- Genuine-torus Fourier coefficient of the actual vorticity of a smooth periodic velocity. -/
def actualVorticityFourierMode
    (velocity : InitialVelocity) (hvelocity : ContDiff ℝ 1 velocity)
    (hperiodic : IsOnePeriodic velocity) (k : SpatialFrequency) : ComplexVector :=
  vectorSpatialFourierCoeff (fun x ↦ vorticityAt velocity x)
    (continuous_vorticityAt hvelocity) (isOnePeriodic_vorticityAt hperiodic) k

/-- The Fourier coefficient of actual pointwise vorticity is exactly the curl of the matrix of
actual Jacobian coefficients. -/
theorem actualVorticityFourierMode_eq_complexCurl
    (velocity : InitialVelocity) (hvelocity : ContDiff ℝ 1 velocity)
    (hperiodic : IsOnePeriodic velocity) (k : SpatialFrequency) :
    actualVorticityFourierMode velocity hvelocity hperiodic k =
      complexCurlFromJacobian
        (actualJacobianFourierMode velocity hvelocity hperiodic k) := by
  ext component
  rw [actualVorticityFourierMode, vectorSpatialFourierCoeff_apply]
  fin_cases component
  · change torusSpatialFourierCoeff (fun q ↦ periodicTorusLift
        (complexVelocityComponent (fun x ↦ vorticityAt velocity x) 0)
        (continuous_complexVelocityComponent (continuous_vorticityAt hvelocity) 0)
        (isOnePeriodic_complexVelocityComponent (isOnePeriodic_vorticityAt hperiodic) 0) q) k = _
    let J₂₁ := periodicTorusLift (complexJacobianComponent velocity 2 1)
      (continuous_complexJacobianComponent hvelocity 2 1)
      (isOnePeriodic_complexJacobianComponent hperiodic 2 1)
    let J₁₂ := periodicTorusLift (complexJacobianComponent velocity 1 2)
      (continuous_complexJacobianComponent hvelocity 1 2)
      (isOnePeriodic_complexJacobianComponent hperiodic 1 2)
    have hfield : (fun q ↦ periodicTorusLift
        (complexVelocityComponent (fun x ↦ vorticityAt velocity x) 0)
        (continuous_complexVelocityComponent (continuous_vorticityAt hvelocity) 0)
        (isOnePeriodic_complexVelocityComponent (isOnePeriodic_vorticityAt hperiodic) 0) q) =
          fun q ↦ (J₂₁ - J₁₂) q := by
      funext q
      simp [J₂₁, J₁₂, periodicTorusLift, periodicTorusLiftFunction,
        complexVelocityComponent, complexJacobianComponent, vorticityAt,
        velocityJacobianAt, curlFromJacobian, vectorOfCoordinates]
    rw [hfield]
    change torusSpatialFourierCoeff (J₂₁ - J₁₂) k = _
    rw [torusSpatialFourierCoeff_sub]
    simp [complexCurlFromJacobian, actualJacobianFourierMode, J₂₁, J₁₂]
  · change torusSpatialFourierCoeff (fun q ↦ periodicTorusLift
        (complexVelocityComponent (fun x ↦ vorticityAt velocity x) 1)
        (continuous_complexVelocityComponent (continuous_vorticityAt hvelocity) 1)
        (isOnePeriodic_complexVelocityComponent (isOnePeriodic_vorticityAt hperiodic) 1) q) k = _
    let J₀₂ := periodicTorusLift (complexJacobianComponent velocity 0 2)
      (continuous_complexJacobianComponent hvelocity 0 2)
      (isOnePeriodic_complexJacobianComponent hperiodic 0 2)
    let J₂₀ := periodicTorusLift (complexJacobianComponent velocity 2 0)
      (continuous_complexJacobianComponent hvelocity 2 0)
      (isOnePeriodic_complexJacobianComponent hperiodic 2 0)
    have hfield : (fun q ↦ periodicTorusLift
        (complexVelocityComponent (fun x ↦ vorticityAt velocity x) 1)
        (continuous_complexVelocityComponent (continuous_vorticityAt hvelocity) 1)
        (isOnePeriodic_complexVelocityComponent (isOnePeriodic_vorticityAt hperiodic) 1) q) =
          fun q ↦ (J₀₂ - J₂₀) q := by
      funext q
      simp [J₀₂, J₂₀, periodicTorusLift, periodicTorusLiftFunction,
        complexVelocityComponent, complexJacobianComponent, vorticityAt,
        velocityJacobianAt, curlFromJacobian, vectorOfCoordinates]
    rw [hfield]
    change torusSpatialFourierCoeff (J₀₂ - J₂₀) k = _
    rw [torusSpatialFourierCoeff_sub]
    simp [complexCurlFromJacobian, actualJacobianFourierMode, J₀₂, J₂₀]
  · change torusSpatialFourierCoeff (fun q ↦ periodicTorusLift
        (complexVelocityComponent (fun x ↦ vorticityAt velocity x) 2)
        (continuous_complexVelocityComponent (continuous_vorticityAt hvelocity) 2)
        (isOnePeriodic_complexVelocityComponent (isOnePeriodic_vorticityAt hperiodic) 2) q) k = _
    let J₁₀ := periodicTorusLift (complexJacobianComponent velocity 1 0)
      (continuous_complexJacobianComponent hvelocity 1 0)
      (isOnePeriodic_complexJacobianComponent hperiodic 1 0)
    let J₀₁ := periodicTorusLift (complexJacobianComponent velocity 0 1)
      (continuous_complexJacobianComponent hvelocity 0 1)
      (isOnePeriodic_complexJacobianComponent hperiodic 0 1)
    have hfield : (fun q ↦ periodicTorusLift
        (complexVelocityComponent (fun x ↦ vorticityAt velocity x) 2)
        (continuous_complexVelocityComponent (continuous_vorticityAt hvelocity) 2)
        (isOnePeriodic_complexVelocityComponent (isOnePeriodic_vorticityAt hperiodic) 2) q) =
          fun q ↦ (J₁₀ - J₀₁) q := by
      funext q
      simp [J₁₀, J₀₁, periodicTorusLift, periodicTorusLiftFunction,
        complexVelocityComponent, complexJacobianComponent, vorticityAt,
        velocityJacobianAt, curlFromJacobian, vectorOfCoordinates]
    rw [hfield]
    change torusSpatialFourierCoeff (J₁₀ - J₀₁) k = _
    rw [torusSpatialFourierCoeff_sub]
    simp [complexCurlFromJacobian, actualJacobianFourierMode, J₁₀, J₀₁]

/-- **Actual curl-mode identity.**  For every `C¹`, one-periodic real velocity slice, the
genuine-torus Fourier coefficients of its actual vorticity satisfy
`ω̂(k) = 2π i (k × û(k))`. -/
theorem actualVorticityFourierMode_eq_frequencyCurlMultiplier
    (velocity : InitialVelocity) (hvelocity : ContDiff ℝ 1 velocity)
    (hperiodic : IsOnePeriodic velocity) (k : SpatialFrequency) :
    actualVorticityFourierMode velocity hvelocity hperiodic k =
      frequencyCurlMultiplier k
        (vectorSpatialFourierCoeff velocity hvelocity.continuous hperiodic k) := by
  rw [actualVorticityFourierMode_eq_complexCurl]
  exact complexCurl_eq_frequencyCurlMultiplier_of_derivativeCoefficients
    k (vectorSpatialFourierCoeff velocity hvelocity.continuous hperiodic k)
      (actualJacobianFourierMode velocity hvelocity hperiodic k)
      (actualJacobianFourierMode_eq_multiplier velocity hvelocity hperiodic k)

/-- Pointwise incompressibility forces the trace of the actual Jacobian Fourier mode to vanish. -/
theorem actualJacobianFourierMode_trace_eq_zero
    (velocity : InitialVelocity) (hvelocity : ContDiff ℝ 1 velocity)
    (hperiodic : IsOnePeriodic velocity)
    (hdivergence : ∀ x, divergence velocity x = 0) (k : SpatialFrequency) :
    actualJacobianFourierMode velocity hvelocity hperiodic k 0 0 +
        actualJacobianFourierMode velocity hvelocity hperiodic k 1 1 +
          actualJacobianFourierMode velocity hvelocity hperiodic k 2 2 = 0 := by
  let J₀₀ := periodicTorusLift (complexJacobianComponent velocity 0 0)
    (continuous_complexJacobianComponent hvelocity 0 0)
    (isOnePeriodic_complexJacobianComponent hperiodic 0 0)
  let J₁₁ := periodicTorusLift (complexJacobianComponent velocity 1 1)
    (continuous_complexJacobianComponent hvelocity 1 1)
    (isOnePeriodic_complexJacobianComponent hperiodic 1 1)
  let J₂₂ := periodicTorusLift (complexJacobianComponent velocity 2 2)
    (continuous_complexJacobianComponent hvelocity 2 2)
    (isOnePeriodic_complexJacobianComponent hperiodic 2 2)
  have hfield : (J₀₀ + J₁₁) + J₂₂ = 0 := by
    ext q
    have htrace :
        divergenceFromJacobian
          (velocityJacobianAt velocity (euclideanRepresentative q)) = 0 := by
      rw [divergenceFromJacobian_velocityJacobianAt, hdivergence]
    have htraceReal :
        velocityJacobianAt velocity (euclideanRepresentative q) 0 0 +
            velocityJacobianAt velocity (euclideanRepresentative q) 1 1 +
              velocityJacobianAt velocity (euclideanRepresentative q) 2 2 = 0 := by
      simpa [divergenceFromJacobian, Fin.sum_univ_succ, add_assoc] using htrace
    change ((velocityJacobianAt velocity (euclideanRepresentative q) 0 0 : ℝ) : ℂ) +
        (velocityJacobianAt velocity (euclideanRepresentative q) 1 1 : ℂ) +
          (velocityJacobianAt velocity (euclideanRepresentative q) 2 2 : ℂ) = 0
    exact_mod_cast htraceReal
  change torusSpatialFourierCoeff J₀₀ k +
      torusSpatialFourierCoeff J₁₁ k +
        torusSpatialFourierCoeff J₂₂ k = 0
  rw [← torusSpatialFourierCoeff_add J₀₀ J₁₁]
  have hcoe₀₁ : (⇑(J₀₀ + J₁₁) : SpatialTorus → ℂ) = ⇑J₀₀ + ⇑J₁₁ := rfl
  rw [← hcoe₀₁]
  rw [← torusSpatialFourierCoeff_add (J₀₀ + J₁₁) J₂₂]
  have hcoe₀₁₂ : (⇑((J₀₀ + J₁₁) + J₂₂) : SpatialTorus → ℂ) =
      ⇑(J₀₀ + J₁₁) + ⇑J₂₂ := rfl
  rw [← hcoe₀₁₂]
  have hfieldFunction : (⇑((J₀₀ + J₁₁) + J₂₂) : SpatialTorus → ℂ) = 0 :=
    congrArg (fun field : C(SpatialTorus, ℂ) ↦ (field : SpatialTorus → ℂ)) hfield
  rw [hfieldFunction]
  simp [torusSpatialFourierCoeff, UnitAddTorus.mFourierCoeff]

/-- The curl multiplier annihilates every spatial mean mode, independently of its vector value. -/
@[simp]
theorem frequencyCurlMultiplier_zero (velocityMode : ComplexVector) :
    frequencyCurlMultiplier 0 velocityMode = 0 := by
  ext i
  fin_cases i <;>
    simp [frequencyCurlMultiplier, complexCross, complexFrequencyVector, crossProduct]

/-- Consequently the Jacobian realization of a mean mode has zero curl. -/
@[simp]
theorem complexCurl_fourierJacobianMode_zero (velocityMode : ComplexVector) :
    complexCurlFromJacobian (fourierJacobianMode 0 velocityMode) = 0 := by
  rw [complexCurl_fourierJacobianMode, frequencyCurlMultiplier_zero]

/-! ## Nonzero-mode Hodge reconstruction -/

/-- Bilinear complex dot receiver (no conjugation), appropriate to the integer frequency vector. -/
def complexDot (a b : ComplexVector) : ℂ := dotProduct a b

/-- Euclidean squared length of an integer spatial frequency. -/
def frequencySquared (k : SpatialFrequency) : ℝ :=
  ∑ j : Fin 3, (k j : ℝ) ^ 2

/-- Every nonzero integer frequency has strictly positive squared length. -/
theorem frequencySquared_pos {k : SpatialFrequency} (hk : k ≠ 0) :
    0 < frequencySquared k := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hk
  have hjReal : (k j : ℝ) ≠ 0 := by exact_mod_cast hj
  refine Finset.sum_pos' (fun i _ ↦ sq_nonneg (k i : ℝ)) ?_
  exact ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero hjReal⟩

/-- The complex bilinear self-dot of the embedded frequency is its real squared length. -/
theorem complexDot_frequency_self (k : SpatialFrequency) :
    complexDot (complexFrequencyVector k) (complexFrequencyVector k) =
      (frequencySquared k : ℂ) := by
  simp only [complexDot, dotProduct, complexFrequencyVector, frequencySquared]
  push_cast
  simp only [pow_two]

/-- Pointwise incompressibility descends to the exact Fourier-mode condition
`k · û(k) = 0` for every genuine-torus frequency. -/
theorem complexDot_vectorSpatialFourierCoeff_eq_zero_of_divergenceFree
    (velocity : InitialVelocity) (hvelocity : ContDiff ℝ 1 velocity)
    (hperiodic : IsOnePeriodic velocity)
    (hdivergence : ∀ x, divergence velocity x = 0) (k : SpatialFrequency) :
    complexDot (complexFrequencyVector k)
      (vectorSpatialFourierCoeff velocity hvelocity.continuous hperiodic k) = 0 := by
  let U := vectorSpatialFourierCoeff velocity hvelocity.continuous hperiodic k
  let J := actualJacobianFourierMode velocity hvelocity hperiodic k
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have h₀ := actualJacobianFourierMode_eq_multiplier
    velocity hvelocity hperiodic k 0 0
  have h₁ := actualJacobianFourierMode_eq_multiplier
    velocity hvelocity hperiodic k 1 1
  have h₂ := actualJacobianFourierMode_eq_multiplier
    velocity hvelocity hperiodic k 2 2
  change J 0 0 = c * (k 0 : ℂ) * U 0 at h₀
  change J 1 1 = c * (k 1 : ℂ) * U 1 at h₁
  change J 2 2 = c * (k 2 : ℂ) * U 2 at h₂
  have htrace : J 0 0 + J 1 1 + J 2 2 = 0 :=
    actualJacobianFourierMode_trace_eq_zero
      velocity hvelocity hperiodic hdivergence k
  have hfactor :
      c * complexDot (complexFrequencyVector k) U =
        J 0 0 + J 1 1 + J 2 2 := by
    rw [h₀, h₁, h₂]
    simp [complexDot, dotProduct, complexFrequencyVector, Fin.sum_univ_succ]
    ring
  have hmul : c * complexDot (complexFrequencyVector k) U = 0 :=
    hfactor.trans htrace
  have hc : c ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero
  exact (mul_eq_zero.mp hmul).resolve_left hc

/-- Hodge reconstruction of a velocity mode from its vorticity mode.  Division is totalized in
the definition; the theorem below opens it only under the exact nonzero-frequency receipt. -/
def nonzeroModeHodgeReconstruction
    (k : SpatialFrequency) (vorticityMode : ComplexVector) : ComplexVector :=
  (Complex.I /
      (2 * (Real.pi : ℂ) * (frequencySquared k : ℂ))) •
    complexCross (complexFrequencyVector k) vorticityMode

/-- **Exact nonzero-mode Hodge inversion.**  If `k ≠ 0`, the velocity mode is divergence-free
(`k · û(k) = 0`), and vorticity is `2π i (k × û(k))`, then

`û(k) = i / (2π |k|²) · (k × ω̂(k))`.

Together with `frequencyCurlMultiplier_zero`, this identifies the full zero frequency as the sole
joint curl/divergence obstruction in this coefficient algebra. -/
theorem nonzeroModeHodgeReconstruction_frequencyCurlMultiplier
    {k : SpatialFrequency} (hk : k ≠ 0) (velocityMode : ComplexVector)
    (hdivergence : complexDot (complexFrequencyVector k) velocityMode = 0) :
    nonzeroModeHodgeReconstruction k
        (frequencyCurlMultiplier k velocityMode) = velocityMode := by
  let K : ComplexVector := complexFrequencyVector k
  let s : ℂ := (frequencySquared k : ℂ)
  have hsReal : frequencySquared k ≠ 0 := (frequencySquared_pos hk).ne'
  have hs : s ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr hsReal
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hdotSelf : complexDot K K = s := by
    exact complexDot_frequency_self k
  have htriple : complexCross K (complexCross K velocityMode) = (-s) • velocityMode := by
    have h := cross_cross_eq_smul_sub_smul' K K velocityMode
    change complexCross K (complexCross K velocityMode) =
      (complexDot K velocityMode) • K - (complexDot K K) • velocityMode at h
    rw [hdivergence, hdotSelf, zero_smul, zero_sub] at h
    simpa only [neg_smul] using h
  have hscalar :
      (Complex.I / (2 * (Real.pi : ℂ) * s)) *
          (2 * (Real.pi : ℂ) * Complex.I) * (-s) = 1 := by
    field_simp [hpi, hs]
    simp
  change (Complex.I / (2 * (Real.pi : ℂ) * s)) •
      complexCross K
        ((2 * (Real.pi : ℂ) * Complex.I) • complexCross K velocityMode) = velocityMode
  rw [show complexCross K
      ((2 * (Real.pi : ℂ) * Complex.I) • complexCross K velocityMode) =
        (2 * (Real.pi : ℂ) * Complex.I) •
          complexCross K (complexCross K velocityMode) by
      exact map_smul (crossProduct K) _ _]
  rw [htriple, smul_smul, smul_smul, hscalar, one_smul]

/-- **Actual-slice nonzero-mode Hodge reconstruction.**  A smooth, periodic, pointwise
incompressible real velocity is reconstructed from the genuine-torus Fourier coefficient of its
actual vorticity at every nonzero frequency. -/
theorem nonzeroModeHodgeReconstruction_actualVorticityFourierMode
    (velocity : InitialVelocity) (hvelocity : ContDiff ℝ 1 velocity)
    (hperiodic : IsOnePeriodic velocity)
    (hdivergence : ∀ x, divergence velocity x = 0)
    {k : SpatialFrequency} (hk : k ≠ 0) :
    nonzeroModeHodgeReconstruction k
        (actualVorticityFourierMode velocity hvelocity hperiodic k) =
      vectorSpatialFourierCoeff velocity hvelocity.continuous hperiodic k := by
  rw [actualVorticityFourierMode_eq_frequencyCurlMultiplier]
  exact nonzeroModeHodgeReconstruction_frequencyCurlMultiplier hk _
    (complexDot_vectorSpatialFourierCoeff_eq_zero_of_divergenceFree
      velocity hvelocity hperiodic hdivergence k)

/-! ## Binding to the active open-lifespan Navier--Stokes carrier -/

/-- Every strict-interior velocity slice of an open-lifespan solution is globally smooth in its
spatial variable.  The strict upper-time inequality is essential: the half-open carrier makes no
smoothness assertion at its absent terminal face. -/
theorem openPeriodicSolutionOn_velocitySlice_contDiff
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    ContDiff ℝ ∞ (fun x ↦ velocity x t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hdomain :
      NavierStokesOpenLifespan.openSpaceTimeSlab T ∈ nhds (x, t) := by
    apply Filter.mem_of_superset
      (prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht.1 ht.2))
    rintro ⟨y, s⟩ ⟨_hy, hs⟩
    exact ⟨Set.mem_univ y, ⟨hs.1.le, hs.2⟩⟩
  have huncurry := solution.velocitySmooth.contDiffAt hdomain
  have hpair : ContDiffAt ℝ ∞ (fun y : Space ↦ (y, t)) x :=
    contDiffAt_id.prodMk contDiffAt_const
  simpa [Function.comp_def] using huncurry.comp x hpair

/-- The first-order spatial smoothness receipt extracted from a strict open-lifespan slice. -/
theorem openPeriodicSolutionOn_velocitySlice_contDiff_one
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    ContDiff ℝ 1 (fun x ↦ velocity x t) :=
  (openPeriodicSolutionOn_velocitySlice_contDiff solution ht).of_le (by norm_num)

/-- Fourier coefficient of the actual velocity slice of an open periodic solution. -/
def openPeriodicVelocityFourierMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) : ComplexVector :=
  vectorSpatialFourierCoeff (fun x ↦ velocity x t.1)
    (openPeriodicSolutionOn_velocitySlice_contDiff_one solution t.2).continuous
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩) k

/-- Fourier coefficient of the actual vorticity of an open periodic solution slice. -/
def openPeriodicVorticityFourierMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) : ComplexVector :=
  actualVorticityFourierMode (fun x ↦ velocity x t.1)
    (openPeriodicSolutionOn_velocitySlice_contDiff_one solution t.2)
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩) k

/-- **Exact curl descent for an admitted solution slice.**  At every strict interior time, the
genuine-torus Fourier coefficient of the actual vorticity is exactly
`2π i (k × û(k))`. -/
theorem openPeriodicSolutionOn_vorticityFourierMode_eq_frequencyCurlMultiplier
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    openPeriodicVorticityFourierMode solution t k =
      frequencyCurlMultiplier k (openPeriodicVelocityFourierMode solution t k) := by
  exact actualVorticityFourierMode_eq_frequencyCurlMultiplier
    (fun x ↦ velocity x t.1)
    (openPeriodicSolutionOn_velocitySlice_contDiff_one solution t.2)
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩) k

/-- **Exact nonzero-mode ascent for an admitted solution slice.**  Incompressibility discharges
the longitudinal obstruction, so every nonzero velocity mode is reconstructed from its actual
vorticity mode.  The zero mode remains the precise joint curl/divergence obstruction. -/
theorem openPeriodicSolutionOn_nonzeroModeHodgeReconstruction
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) {k : SpatialFrequency} (hk : k ≠ 0) :
    nonzeroModeHodgeReconstruction k
        (openPeriodicVorticityFourierMode solution t k) =
      openPeriodicVelocityFourierMode solution t k := by
  apply nonzeroModeHodgeReconstruction_actualVorticityFourierMode
    (fun x ↦ velocity x t.1)
    (openPeriodicSolutionOn_velocitySlice_contDiff_one solution t.2)
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)
    (fun x ↦ solution.incompressible x t.1 ⟨t.2.1.le, t.2.2⟩)
    hk

#print axioms splitFirstTorus_measurePreserving
#print axioms torusSpatialFourierCoeff_eq_integral_tail_fourierCoeff
#print axioms fourierCoeff_derivative_eq_frequency_mul
#print axioms torusSpatialFourierCoeff_firstCoordinateDerivative
#print axioms torusSpatialFourierCoeff_zero_eq_mean
#print axioms torusSpatialFourierCoeff_firstDerivative_zero
#print axioms firstCoordinateMultiplier_eq_zero_iff
#print axioms vectorSpatialFourierCoeff
#print axioms complexCurl_fourierJacobianMode
#print axioms complexCurl_eq_frequencyCurlMultiplier_of_derivativeCoefficients
#print axioms frequencyCurlMultiplier_zero
#print axioms frequencySquared_pos
#print axioms nonzeroModeHodgeReconstruction_frequencyCurlMultiplier
#print axioms torusSpatialFourierCoeff_coordinateDerivative
#print axioms periodicTorusLift_isCoordinateDerivative
#print axioms actualVorticityFourierMode_eq_frequencyCurlMultiplier
#print axioms complexDot_vectorSpatialFourierCoeff_eq_zero_of_divergenceFree
#print axioms nonzeroModeHodgeReconstruction_actualVorticityFourierMode
#print axioms openPeriodicSolutionOn_vorticityFourierMode_eq_frequencyCurlMultiplier
#print axioms openPeriodicSolutionOn_nonzeroModeHodgeReconstruction

end Soma.Holonics.Millennium.NavierStokesTorusFourier
