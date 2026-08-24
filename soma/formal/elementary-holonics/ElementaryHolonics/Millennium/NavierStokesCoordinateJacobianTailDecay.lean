import ElementaryHolonics.Millennium.NavierStokesAnnularHodgeScaleChain
import ElementaryHolonics.Millennium.NavierStokesSmoothSliceWeightedH3

/-!
# Quantitative decay of the complete Jacobian reconstruction fibre

**[proved-derived]** This owner extracts an explicit reciprocal scale from the complete `H³`
Jacobian coefficient tail.  The lattice proof keeps a separable exponent `7/12` in every
coordinate (strictly beyond the one-dimensional summability threshold) and spends the remaining
`1/12` only in a coordinate which actually exits the declared frequency cube.  Consequently the
reciprocal first-moment square mass decays as `(R+1)^(-1/6)`.

The result is the quantitative analytic attachment needed to balance the exact scale fibre from
`NavierStokesAnnularHodgeScaleChain`; no finite aperture is identified with the complete field.
-/

noncomputable section

open Set
open scoped BigOperators ENNReal
open Filter

namespace Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FrequencyComb
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## A summable lattice remainder after extracting one reciprocal scale -/

/-- The retained one-coordinate exponent after spending `1/12` of the original `2/3`. -/
def jacobianTailCoordinateWeight (n : ℤ) : ℝ :=
  (1 + (n : ℝ) ^ 2) ^ (-(7 / 12 : ℝ))

theorem jacobianTailCoordinateWeight_nonneg (n : ℤ) :
    0 ≤ jacobianTailCoordinateWeight n :=
  Real.rpow_nonneg (by positivity) _

/-- The retained coordinate weight is summable because its absolute-power exponent is `7/6>1`.
-/
theorem summable_jacobianTailCoordinateWeight :
    Summable jacobianTailCoordinateWeight := by
  have hp : Summable fun n : ℤ ↦ |(n : ℝ)| ^ (-(7 / 6 : ℝ)) :=
    Real.summable_abs_int_rpow (by norm_num)
  let bound : ℤ → ℝ := fun n ↦
    if n = 0 then 1 else |(n : ℝ)| ^ (-(7 / 6 : ℝ))
  have hbound : Summable bound := by
    apply hp.congr_cofinite
    filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
    simp [bound, hn]
  refine Summable.of_nonneg_of_le
    (fun n ↦ jacobianTailCoordinateWeight_nonneg n) (fun n ↦ ?_) hbound
  by_cases hn : n = 0
  · subst n
    simp [jacobianTailCoordinateWeight, bound]
  · rw [show bound n = |(n : ℝ)| ^ (-(7 / 6 : ℝ)) by simp [bound, hn]]
    have habs : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
    have hsq : (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := by rw [sq_abs]
    calc
      jacobianTailCoordinateWeight n ≤
          ((n : ℝ) ^ 2) ^ (-(7 / 12 : ℝ)) := by
        apply Real.rpow_le_rpow_of_nonpos (sq_pos_of_ne_zero (by exact_mod_cast hn))
        · linarith
        · norm_num
      _ = |(n : ℝ)| ^ (-(7 / 6 : ℝ)) := by
        rw [hsq, ← Real.rpow_natCast]
        rw [← Real.rpow_mul (le_of_lt habs)]
        congr 2
        norm_num

private theorem summable_pair_jacobianTailCoordinateWeight :
    Summable fun k : ℤ × ℤ ↦
      jacobianTailCoordinateWeight k.1 * jacobianTailCoordinateWeight k.2 := by
  exact summable_jacobianTailCoordinateWeight.mul_of_nonneg
    summable_jacobianTailCoordinateWeight
    jacobianTailCoordinateWeight_nonneg jacobianTailCoordinateWeight_nonneg

private theorem summable_triple_jacobianTailCoordinateWeight :
    Summable fun k : (ℤ × ℤ) × ℤ ↦
      (jacobianTailCoordinateWeight k.1.1 *
        jacobianTailCoordinateWeight k.1.2) *
          jacobianTailCoordinateWeight k.2 := by
  exact summable_pair_jacobianTailCoordinateWeight.mul_of_nonneg
    summable_jacobianTailCoordinateWeight
    (fun k ↦ mul_nonneg (jacobianTailCoordinateWeight_nonneg k.1)
      (jacobianTailCoordinateWeight_nonneg k.2))
    jacobianTailCoordinateWeight_nonneg

/-- The complete retained `7/12+7/12+7/12` lattice receiver. -/
def jacobianTailLatticeWeight (frequency : SpatialFrequency) : ℝ :=
  jacobianTailCoordinateWeight (frequency 0) *
    jacobianTailCoordinateWeight (frequency 1) *
      jacobianTailCoordinateWeight (frequency 2)

theorem jacobianTailLatticeWeight_nonneg (frequency : SpatialFrequency) :
    0 ≤ jacobianTailLatticeWeight frequency := by
  unfold jacobianTailLatticeWeight
  exact mul_nonneg
    (mul_nonneg
      (jacobianTailCoordinateWeight_nonneg (frequency 0))
      (jacobianTailCoordinateWeight_nonneg (frequency 1)))
    (jacobianTailCoordinateWeight_nonneg (frequency 2))

theorem summable_jacobianTailLatticeWeight :
    Summable jacobianTailLatticeWeight := by
  have htranslated := frequencyTripleEquiv.summable_iff.mpr
    summable_triple_jacobianTailCoordinateWeight
  simpa only [Function.comp_apply, frequencyTripleEquiv,
    jacobianTailLatticeWeight] using htranslated

/-- The finite lattice constant left after extracting the reciprocal scale. -/
def jacobianTailLatticeMass : ℝ := ∑' frequency, jacobianTailLatticeWeight frequency

theorem jacobianTailLatticeMass_nonneg : 0 ≤ jacobianTailLatticeMass :=
  tsum_nonneg jacobianTailLatticeWeight_nonneg

/-- The explicitly extracted reciprocal scale. -/
def jacobianTailScale (radius : ℕ) : ℝ :=
  (radius + 1 : ℝ) ^ (-(1 / 6 : ℝ))

theorem jacobianTailScale_nonneg (radius : ℕ) :
    0 ≤ jacobianTailScale radius :=
  Real.rpow_nonneg (by positivity) _

/-! ## One escaping coordinate pays the scale -/

/-- On every coordinate, the original `2/3` weight is bounded by the retained `7/12` weight. -/
theorem fractionalCoordinateWeight_le_jacobianTailCoordinateWeight (n : ℤ) :
    fractionalCoordinateWeight n ≤ jacobianTailCoordinateWeight n := by
  unfold fractionalCoordinateWeight jacobianTailCoordinateWeight
  apply Real.rpow_le_rpow_of_exponent_le
    (by nlinarith [sq_nonneg (n : ℝ)])
  norm_num

/-- If one integer coordinate leaves radius `R`, it pays the extracted `(R+1)^(-1/6)` scale. -/
theorem fractionalCoordinateWeight_le_scale_mul_tailWeight
    (radius : ℕ) (n : ℤ) (houtside : radius < n.natAbs) :
    fractionalCoordinateWeight n ≤
      jacobianTailScale radius * jacobianTailCoordinateWeight n := by
  let base : ℝ := 1 + (n : ℝ) ^ 2
  let scaleBase : ℝ := (radius + 1 : ℝ)
  have hbasePos : 0 < base := by dsimp [base]; positivity
  have hscalePos : 0 < scaleBase := by dsimp [scaleBase]; positivity
  have habs : scaleBase ≤ |(n : ℝ)| := by
    have hcast : ((radius + 1 : ℕ) : ℝ) ≤ (n.natAbs : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr houtside)
    rw [Nat.cast_natAbs] at hcast
    simpa [scaleBase] using hcast
  have hscaleSq : scaleBase ^ 2 ≤ base := by
    have hsquare : scaleBase ^ 2 ≤ |(n : ℝ)| ^ 2 := by
      nlinarith [abs_nonneg (n : ℝ)]
    have hnSquare : (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := by rw [sq_abs]
    dsimp [base]
    rw [hnSquare]
    nlinarith [sq_nonneg (|(n : ℝ)| - scaleBase)]
  have hextracted :
      base ^ (-(1 / 12 : ℝ)) ≤ jacobianTailScale radius := by
    calc
      base ^ (-(1 / 12 : ℝ)) ≤
          (scaleBase ^ 2) ^ (-(1 / 12 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hscalePos) hscaleSq (by norm_num)
      _ = scaleBase ^ (-(1 / 6 : ℝ)) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hscalePos.le]
        congr 2
        norm_num
      _ = jacobianTailScale radius := by
        simp [jacobianTailScale, scaleBase]
  have hsplit :
      base ^ (-(2 / 3 : ℝ)) =
        base ^ (-(1 / 12 : ℝ)) * base ^ (-(7 / 12 : ℝ)) := by
    rw [← Real.rpow_add hbasePos]
    congr 2
    norm_num
  rw [fractionalCoordinateWeight, jacobianTailCoordinateWeight]
  change base ^ (-(2 / 3 : ℝ)) ≤
    jacobianTailScale radius * base ^ (-(7 / 12 : ℝ))
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hextracted (Real.rpow_nonneg hbasePos.le _)

/-- Leaving a frequency cube is witnessed by one addressed escaping coordinate. -/
theorem exists_coordinate_natAbs_gt_of_not_mem_frequencyCube
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∉ frequencyCube radius) :
    ∃ coordinate : Fin 3, radius < (frequency coordinate).natAbs := by
  by_contra hnot
  push_neg at hnot
  apply hfrequency
  rw [mem_frequencyCube_iff]
  intro coordinate
  exact (natAbs_le_iff_bounds radius (frequency coordinate)).mp
    (hnot coordinate)

/-- The complete first-moment reciprocal weight outside the cube pays one explicit scale while
retaining a globally summable lattice receiver. -/
theorem fractionalFirstMomentWeight_le_scale_mul_tailLatticeWeight
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∉ frequencyCube radius) :
    fractionalFirstMomentWeight frequency ≤
      jacobianTailScale radius * jacobianTailLatticeWeight frequency := by
  obtain ⟨coordinate, hcoordinate⟩ :=
    exists_coordinate_natAbs_gt_of_not_mem_frequencyCube radius hfrequency
  have h0 := fractionalCoordinateWeight_le_jacobianTailCoordinateWeight (frequency 0)
  have h1 := fractionalCoordinateWeight_le_jacobianTailCoordinateWeight (frequency 1)
  have h2 := fractionalCoordinateWeight_le_jacobianTailCoordinateWeight (frequency 2)
  have hs := fractionalCoordinateWeight_le_scale_mul_tailWeight
    radius (frequency coordinate) hcoordinate
  have hf0 : 0 ≤ fractionalCoordinateWeight (frequency 0) :=
    fractionalCoordinateWeight_nonneg _
  have hf1 : 0 ≤ fractionalCoordinateWeight (frequency 1) :=
    fractionalCoordinateWeight_nonneg _
  have hf2 : 0 ≤ fractionalCoordinateWeight (frequency 2) :=
    fractionalCoordinateWeight_nonneg _
  have hj0 : 0 ≤ jacobianTailCoordinateWeight (frequency 0) :=
    jacobianTailCoordinateWeight_nonneg _
  have hj1 : 0 ≤ jacobianTailCoordinateWeight (frequency 1) :=
    jacobianTailCoordinateWeight_nonneg _
  have hj2 : 0 ≤ jacobianTailCoordinateWeight (frequency 2) :=
    jacobianTailCoordinateWeight_nonneg _
  have hscale : 0 ≤ jacobianTailScale radius := jacobianTailScale_nonneg _
  unfold fractionalFirstMomentWeight jacobianTailLatticeWeight
  fin_cases coordinate
  · have hs0 : fractionalCoordinateWeight (frequency 0) ≤
        jacobianTailScale radius * jacobianTailCoordinateWeight (frequency 0) := by
      simpa using hs
    have h01 : fractionalCoordinateWeight (frequency 0) *
          fractionalCoordinateWeight (frequency 1) ≤
        (jacobianTailScale radius * jacobianTailCoordinateWeight (frequency 0)) *
          jacobianTailCoordinateWeight (frequency 1) :=
      mul_le_mul hs0 h1 hf1 (mul_nonneg hscale hj0)
    calc
      fractionalCoordinateWeight (frequency 0) *
          fractionalCoordinateWeight (frequency 1) *
            fractionalCoordinateWeight (frequency 2) ≤
        (jacobianTailScale radius * jacobianTailCoordinateWeight (frequency 0)) *
          jacobianTailCoordinateWeight (frequency 1) *
            jacobianTailCoordinateWeight (frequency 2) :=
        mul_le_mul h01 h2 hf2 (mul_nonneg (mul_nonneg hscale hj0) hj1)
      _ = _ := by ring
  · have hs1 : fractionalCoordinateWeight (frequency 1) ≤
        jacobianTailScale radius * jacobianTailCoordinateWeight (frequency 1) := by
      simpa using hs
    have h01 : fractionalCoordinateWeight (frequency 0) *
          fractionalCoordinateWeight (frequency 1) ≤
        jacobianTailCoordinateWeight (frequency 0) *
          (jacobianTailScale radius * jacobianTailCoordinateWeight (frequency 1)) :=
      mul_le_mul h0 hs1 hf1 hj0
    calc
      fractionalCoordinateWeight (frequency 0) *
          fractionalCoordinateWeight (frequency 1) *
            fractionalCoordinateWeight (frequency 2) ≤
        jacobianTailCoordinateWeight (frequency 0) *
          (jacobianTailScale radius * jacobianTailCoordinateWeight (frequency 1)) *
            jacobianTailCoordinateWeight (frequency 2) :=
        mul_le_mul h01 h2 hf2 (mul_nonneg hj0 (mul_nonneg hscale hj1))
      _ = _ := by ring
  · have hs2 : fractionalCoordinateWeight (frequency 2) ≤
        jacobianTailScale radius * jacobianTailCoordinateWeight (frequency 2) := by
      simpa using hs
    have h01 : fractionalCoordinateWeight (frequency 0) *
          fractionalCoordinateWeight (frequency 1) ≤
        jacobianTailCoordinateWeight (frequency 0) *
          jacobianTailCoordinateWeight (frequency 1) :=
      mul_le_mul h0 h1 hf1 hj0
    calc
      fractionalCoordinateWeight (frequency 0) *
          fractionalCoordinateWeight (frequency 1) *
            fractionalCoordinateWeight (frequency 2) ≤
        jacobianTailCoordinateWeight (frequency 0) *
          jacobianTailCoordinateWeight (frequency 1) *
            (jacobianTailScale radius * jacobianTailCoordinateWeight (frequency 2)) :=
        mul_le_mul h01 hs2 hf2 (mul_nonneg hj0 hj1)
      _ = _ := by ring

/-! ## Complete subtype tail estimate -/

/-- The full fractional reciprocal population outside the cube has explicit scale decay. -/
theorem tsum_fractionalFirstMomentWeight_compl_frequencyCube_le
    (radius : ℕ) :
    (∑' frequency : {frequency : SpatialFrequency // frequency ∉ frequencyCube radius},
        fractionalFirstMomentWeight frequency.1) ≤
      jacobianTailScale radius * jacobianTailLatticeMass := by
  let complement := {frequency : SpatialFrequency // frequency ∉ frequencyCube radius}
  have hleft : Summable fun frequency : complement ↦
      fractionalFirstMomentWeight frequency.1 :=
    summable_fractionalFirstMomentWeight.subtype
      {frequency : SpatialFrequency | frequency ∉ frequencyCube radius}
  have hrightBase : Summable fun frequency : complement ↦
      jacobianTailLatticeWeight frequency.1 :=
    summable_jacobianTailLatticeWeight.subtype
      {frequency : SpatialFrequency | frequency ∉ frequencyCube radius}
  have hright : Summable fun frequency : complement ↦
      jacobianTailScale radius * jacobianTailLatticeWeight frequency.1 :=
    hrightBase.mul_left _
  have hpoint : ∀ frequency : complement,
      fractionalFirstMomentWeight frequency.1 ≤
        jacobianTailScale radius * jacobianTailLatticeWeight frequency.1 :=
    fun frequency ↦
      fractionalFirstMomentWeight_le_scale_mul_tailLatticeWeight
        radius frequency.2
  calc
    (∑' frequency : complement,
        fractionalFirstMomentWeight frequency.1) ≤
        ∑' frequency : complement,
          jacobianTailScale radius * jacobianTailLatticeWeight frequency.1 :=
      hleft.tsum_le_tsum hpoint hright
    _ = jacobianTailScale radius *
        (∑' frequency : complement,
          jacobianTailLatticeWeight frequency.1) :=
      hrightBase.tsum_mul_left _
    _ ≤ jacobianTailScale radius * jacobianTailLatticeMass := by
      apply mul_le_mul_of_nonneg_left _ (jacobianTailScale_nonneg radius)
      exact Summable.tsum_subtype_le jacobianTailLatticeWeight
        {frequency : SpatialFrequency | frequency ∉ frequencyCube radius}
        jacobianTailLatticeWeight_nonneg summable_jacobianTailLatticeWeight

/-- Therefore every addressed reciprocal derivative-square population has the same explicit
tail bound. -/
theorem tsum_coordinate_sq_div_weight_three_compl_frequencyCube_le
    (coordinate : Fin 3) (radius : ℕ) :
    (∑' frequency : {frequency : SpatialFrequency // frequency ∉ frequencyCube radius},
        (frequency.1 coordinate : ℝ) ^ 2 /
          periodicSobolevWeight 3 frequency.1) ≤
      jacobianTailScale radius * jacobianTailLatticeMass := by
  let complement := {frequency : SpatialFrequency // frequency ∉ frequencyCube radius}
  have hright : Summable fun frequency : complement ↦
      fractionalFirstMomentWeight frequency.1 :=
    summable_fractionalFirstMomentWeight.subtype
      {frequency : SpatialFrequency | frequency ∉ frequencyCube radius}
  have hpoint : ∀ frequency : complement,
      (frequency.1 coordinate : ℝ) ^ 2 /
          periodicSobolevWeight 3 frequency.1 ≤
        fractionalFirstMomentWeight frequency.1 :=
    fun frequency ↦
      coordinate_sq_div_periodicSobolevWeight_three_le_fractional
        coordinate frequency.1
  have hleft : Summable fun frequency : complement ↦
      (frequency.1 coordinate : ℝ) ^ 2 /
        periodicSobolevWeight 3 frequency.1 :=
    Summable.of_nonneg_of_le
      (fun frequency ↦ div_nonneg (sq_nonneg _)
        (periodicSobolevWeight_nonneg 3 frequency.1))
      hpoint hright
  exact (hleft.tsum_le_tsum
    hpoint hright).trans
    (tsum_fractionalFirstMomentWeight_compl_frequencyCube_le radius)

/-! ## Tail-restricted Fourier `ℓ²` carriers and Cauchy--Schwarz -/

/-- The addressed complement population outside one frequency cube. -/
abbrev FrequencyCubeComplement (radius : ℕ) :=
  {frequency : SpatialFrequency // frequency ∉ frequencyCube radius}

private theorem norm_coordinateReciprocalSobolevThreeSqrtTail_sq
    (coordinate : Fin 3) (radius : ℕ)
    (frequency : FrequencyCubeComplement radius) :
    ‖(((|(frequency.1 coordinate : ℝ)| /
        Real.sqrt (periodicSobolevWeight 3 frequency.1) : ℝ) : ℂ))‖ ^ 2 =
      (frequency.1 coordinate : ℝ) ^ 2 /
        periodicSobolevWeight 3 frequency.1 := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)),
    div_pow, sq_abs,
    Real.sq_sqrt (periodicSobolevWeight_nonneg 3 frequency.1)]

/-- The reciprocal derivative weight restricted to the complete unresolved frequency fibre. -/
def coordinateReciprocalSobolevThreeSqrtTail
    (coordinate : Fin 3) (radius : ℕ) :
    ℓ²(FrequencyCubeComplement radius, ℂ) :=
  ⟨fun frequency ↦ (((|(frequency.1 coordinate : ℝ)| /
      Real.sqrt (periodicSobolevWeight 3 frequency.1) : ℝ) : ℂ)), by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    simpa only [Real.rpow_two,
      norm_coordinateReciprocalSobolevThreeSqrtTail_sq] using
        (summable_coordinate_sq_div_periodicSobolevWeight_three coordinate).subtype
          {frequency : SpatialFrequency | frequency ∉ frequencyCube radius}⟩

private theorem norm_weightedSobolevThreeCoefficientTail_sq
    (coeff : PeriodicSobolevCoefficients 3) (radius : ℕ)
    (frequency : FrequencyCubeComplement radius) :
    ‖(Real.sqrt (periodicSobolevWeight 3 frequency.1) : ℂ) *
        coeff.1 frequency.1‖ ^ 2 =
      periodicSobolevWeight 3 frequency.1 * ‖coeff.1 frequency.1‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (periodicSobolevWeight_nonneg 3 frequency.1)]

/-- The actual weighted `H³` population restricted to the same unresolved fibre. -/
def weightedSobolevThreeCoefficientTail
    (coeff : PeriodicSobolevCoefficients 3) (radius : ℕ) :
    ℓ²(FrequencyCubeComplement radius, ℂ) :=
  ⟨fun frequency ↦
      (Real.sqrt (periodicSobolevWeight 3 frequency.1) : ℂ) *
        coeff.1 frequency.1, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    simpa only [Real.rpow_two,
      norm_weightedSobolevThreeCoefficientTail_sq] using
        coeff.2.subtype
          {frequency : SpatialFrequency | frequency ∉ frequencyCube radius}⟩

/-- The reciprocal tail carrier has exactly the quantitative square bound proved above. -/
theorem norm_coordinateReciprocalSobolevThreeSqrtTail_sq_le
    (coordinate : Fin 3) (radius : ℕ) :
    ‖coordinateReciprocalSobolevThreeSqrtTail coordinate radius‖ ^ 2 ≤
      jacobianTailScale radius * jacobianTailLatticeMass := by
  have hnorm := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (coordinateReciprocalSobolevThreeSqrtTail coordinate radius)
  have hnormSq :
      ‖coordinateReciprocalSobolevThreeSqrtTail coordinate radius‖ ^ 2 =
        ∑' frequency : FrequencyCubeComplement radius,
          (frequency.1 coordinate : ℝ) ^ 2 /
            periodicSobolevWeight 3 frequency.1 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      coordinateReciprocalSobolevThreeSqrtTail,
      norm_coordinateReciprocalSobolevThreeSqrtTail_sq] using hnorm
  rw [hnormSq]
  exact tsum_coordinate_sq_div_weight_three_compl_frequencyCube_le
    coordinate radius

/-- Square-root form of the same explicit scale decay. -/
theorem norm_coordinateReciprocalSobolevThreeSqrtTail_le
    (coordinate : Fin 3) (radius : ℕ) :
    ‖coordinateReciprocalSobolevThreeSqrtTail coordinate radius‖ ≤
      Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) := by
  have hsquare := norm_coordinateReciprocalSobolevThreeSqrtTail_sq_le
    coordinate radius
  calc
    ‖coordinateReciprocalSobolevThreeSqrtTail coordinate radius‖ =
        Real.sqrt
          (‖coordinateReciprocalSobolevThreeSqrtTail coordinate radius‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ ≤ Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) :=
      Real.sqrt_le_sqrt hsquare

/-- Restricting the weighted coefficient population to an unresolved fibre cannot increase its
Hilbert norm. -/
theorem norm_weightedSobolevThreeCoefficientTail_le
    (coeff : PeriodicSobolevCoefficients 3) (radius : ℕ) :
    ‖weightedSobolevThreeCoefficientTail coeff radius‖ ≤
      ‖weightedSobolevThreeCoefficient coeff‖ := by
  have hsum := Summable.tsum_subtype_le
    (fun frequency : SpatialFrequency ↦
      periodicSobolevWeight 3 frequency * ‖coeff.1 frequency‖ ^ 2)
    {frequency : SpatialFrequency | frequency ∉ frequencyCube radius}
    (fun frequency ↦ mul_nonneg (periodicSobolevWeight_nonneg 3 frequency)
      (sq_nonneg _)) coeff.2
  have hleftNorm := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (weightedSobolevThreeCoefficientTail coeff radius)
  have hrightNorm := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (weightedSobolevThreeCoefficient coeff)
  have hleftSq :
      ‖weightedSobolevThreeCoefficientTail coeff radius‖ ^ 2 =
        ∑' frequency : FrequencyCubeComplement radius,
          periodicSobolevWeight 3 frequency.1 * ‖coeff.1 frequency.1‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      weightedSobolevThreeCoefficientTail,
      norm_weightedSobolevThreeCoefficientTail_sq] using hleftNorm
  have hrightSq :
      ‖weightedSobolevThreeCoefficient coeff‖ ^ 2 =
        ∑' frequency : SpatialFrequency,
          periodicSobolevWeight 3 frequency * ‖coeff.1 frequency‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      weightedSobolevThreeCoefficient, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (periodicSobolevWeight_nonneg 3 _)] using hrightNorm
  have hsum' :
      (∑' frequency : FrequencyCubeComplement radius,
          periodicSobolevWeight 3 frequency.1 * ‖coeff.1 frequency.1‖ ^ 2) ≤
        ∑' frequency : SpatialFrequency,
          periodicSobolevWeight 3 frequency * ‖coeff.1 frequency‖ ^ 2 := by
    simpa only [Function.comp_apply] using hsum
  rw [← hleftSq, ← hrightSq] at hsum'
  nlinarith [norm_nonneg (weightedSobolevThreeCoefficientTail coeff radius),
    norm_nonneg (weightedSobolevThreeCoefficient coeff), hsum']

private theorem coordinateReciprocal_mul_weightedTail_eq
    (coeff : PeriodicSobolevCoefficients 3) (coordinate : Fin 3)
    (radius : ℕ) (frequency : FrequencyCubeComplement radius) :
    ‖coordinateReciprocalSobolevThreeSqrtTail coordinate radius frequency‖ *
        ‖weightedSobolevThreeCoefficientTail coeff radius frequency‖ =
      |(frequency.1 coordinate : ℝ)| * ‖coeff.1 frequency.1‖ := by
  have hweightPos : 0 < periodicSobolevWeight 3 frequency.1 :=
    periodicSobolevWeight_pos 3 frequency.1
  have hsqrtPos : 0 < Real.sqrt (periodicSobolevWeight 3 frequency.1) :=
    Real.sqrt_pos.2 hweightPos
  simp only [coordinateReciprocalSobolevThreeSqrtTail,
    weightedSobolevThreeCoefficientTail, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_div, abs_of_nonneg (abs_nonneg _),
    abs_of_pos hsqrtPos]
  field_simp

/-- Quantitative Cauchy--Schwarz decay of the actual first coefficient moment outside a cube. -/
theorem tsum_coordinate_mul_norm_compl_frequencyCube_le
    (coeff : PeriodicSobolevCoefficients 3) (coordinate : Fin 3)
    (radius : ℕ) :
    (∑' frequency : FrequencyCubeComplement radius,
        |(frequency.1 coordinate : ℝ)| * ‖coeff.1 frequency.1‖) ≤
      Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
        ‖weightedSobolevThreeCoefficient coeff‖ := by
  have hholder :
      (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa only [ENNReal.toReal_ofNat] using Real.HolderConjugate.two_two
  let reciprocal := coordinateReciprocalSobolevThreeSqrtTail coordinate radius
  let weighted := weightedSobolevThreeCoefficientTail coeff radius
  calc
    (∑' frequency : FrequencyCubeComplement radius,
        |(frequency.1 coordinate : ℝ)| * ‖coeff.1 frequency.1‖) =
        ∑' frequency : FrequencyCubeComplement radius,
          ‖reciprocal frequency‖ * ‖weighted frequency‖ := by
      apply tsum_congr
      intro frequency
      exact (coordinateReciprocal_mul_weightedTail_eq
        coeff coordinate radius frequency).symm
    _ ≤ ‖reciprocal‖ * ‖weighted‖ :=
      lp.tsum_mul_le_mul_norm' hholder reciprocal weighted
    _ ≤ Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
        ‖weighted‖ := by
      exact mul_le_mul_of_nonneg_right
        (norm_coordinateReciprocalSobolevThreeSqrtTail_le coordinate radius)
        (norm_nonneg _)
    _ ≤ Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
        ‖weightedSobolevThreeCoefficient coeff‖ := by
      exact mul_le_mul_of_nonneg_left
        (norm_weightedSobolevThreeCoefficientTail_le coeff radius)
        (Real.sqrt_nonneg _)

/-! ## Attachment to the actual smooth solution slice -/

/-- Native form of the quantitative coefficient-tail estimate. -/
theorem tsum_coordinate_mul_norm_nativeUnweightedComponent_compl_frequencyCube_le
    (state : PeriodicVectorWeightedSobolev 3) (component coordinate : Fin 3)
    (radius : ℕ) :
    (∑' frequency : FrequencyCubeComplement radius,
        |(frequency.1 coordinate : ℝ)| *
          ‖nativeUnweightedComponent state component frequency.1‖) ≤
      Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
        ‖state component‖ := by
  let coeff := weightedSobolevCoefficients 3 (state component)
  have htail := tsum_coordinate_mul_norm_compl_frequencyCube_le
    coeff coordinate radius
  have hweighted : weightedSobolevThreeCoefficient coeff = state component := by
    change coefficientWeightedRealization 3
      (weightedSobolevCoefficients 3 (state component)) = state component
    exact coefficientWeightedRealization_weightedSobolevCoefficients 3
      (state component)
  simpa only [coeff, nativeUnweightedComponent, hweighted] using htail

/-- One actual Jacobian-entry tail is bounded by the explicit reciprocal scale times the native
`H³` norm of its velocity component. -/
theorem tsum_norm_openPeriodicJacobianFourierMode_entry_compl_frequencyCube_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (component coordinate : Fin 3) (radius : ℕ) :
    (∑' frequency : FrequencyCubeComplement radius,
        ‖openPeriodicJacobianFourierMode solution t frequency.1
          component coordinate‖) ≤
      (2 * Real.pi) *
        (Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
          ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
            (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
            (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩) component‖) := by
  let u : InitialVelocity := fun x ↦ velocity x t.1
  let hu := openPeriodicSolutionOn_velocitySlice_contDiff solution t.2
  let hperiodic : IsOnePeriodic u :=
    solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩
  let state : PeriodicVectorWeightedSobolev 3 :=
    smoothSliceVectorWeightedH3 u hu hperiodic
  have hmoment :=
    tsum_coordinate_mul_norm_nativeUnweightedComponent_compl_frequencyCube_le
      state component coordinate radius
  have hsummable : Summable fun frequency : FrequencyCubeComplement radius ↦
      |(frequency.1 coordinate : ℝ)| *
        ‖nativeUnweightedComponent state component frequency.1‖ :=
    (summable_coordinate_mul_norm_nativeUnweightedComponent
      state component coordinate).subtype
        {frequency : SpatialFrequency | frequency ∉ frequencyCube radius}
  have hmode : ∀ frequency : FrequencyCubeComplement radius,
      ‖openPeriodicJacobianFourierMode solution t frequency.1
          component coordinate‖ =
        (2 * Real.pi) *
          (|(frequency.1 coordinate : ℝ)| *
            ‖nativeUnweightedComponent state component frequency.1‖) := by
    intro frequency
    have hcoefficient := actualJacobianFourierMode_eq_multiplier
      u (hu.of_le (by norm_num)) hperiodic frequency.1 component coordinate
    change ‖actualJacobianFourierMode u (hu.of_le (by norm_num)) hperiodic
        frequency.1 component coordinate‖ = _
    rw [hcoefficient]
    have hunweighted := unweighted_smoothSliceVectorWeightedH3_apply
      u hu hperiodic component frequency.1
    change nativeUnweightedComponent state component frequency.1 = _ at hunweighted
    rw [hunweighted]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I,
      Complex.norm_intCast]
    ring
  calc
    (∑' frequency : FrequencyCubeComplement radius,
        ‖openPeriodicJacobianFourierMode solution t frequency.1
          component coordinate‖) =
        ∑' frequency : FrequencyCubeComplement radius,
          (2 * Real.pi) *
            (|(frequency.1 coordinate : ℝ)| *
              ‖nativeUnweightedComponent state component frequency.1‖) := by
      apply tsum_congr
      exact hmode
    _ = (2 * Real.pi) *
        ∑' frequency : FrequencyCubeComplement radius,
          |(frequency.1 coordinate : ℝ)| *
            ‖nativeUnweightedComponent state component frequency.1‖ :=
      hsummable.tsum_mul_left _
    _ ≤ (2 * Real.pi) *
        (Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
          ‖state component‖) :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)

/-- All nine actual Jacobian faces share the same explicit tail scale; the outer product norm
retains their component and derivative addresses. -/
theorem openPeriodicJacobianCoefficientTailMass_frequencyCube_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) :
    openPeriodicJacobianCoefficientTailMass solution t (frequencyCube radius) ≤
      (2 * Real.pi) *
        Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
          ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
            (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
            (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖ := by
  let state : PeriodicVectorWeightedSobolev 3 :=
    smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
      (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
      (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)
  let factor : ℝ :=
    (2 * Real.pi) *
      Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass)
  have hfactor : 0 ≤ factor := by
    dsimp [factor]
    positivity
  unfold openPeriodicJacobianCoefficientTailMass
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hfactor (norm_nonneg state))]
  intro component
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hfactor (norm_nonneg state))]
  intro coordinate
  have hsumNonneg :
      0 ≤ ∑' frequency : FrequencyCubeComplement radius,
        ‖openPeriodicJacobianFourierMode solution t frequency.1
          component coordinate‖ :=
    tsum_nonneg fun _ ↦ norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hsumNonneg]
  calc
    (∑' frequency : FrequencyCubeComplement radius,
        ‖openPeriodicJacobianFourierMode solution t frequency.1
          component coordinate‖) ≤
        (2 * Real.pi) *
          (Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
            ‖state component‖) :=
      tsum_norm_openPeriodicJacobianFourierMode_entry_compl_frequencyCube_le
        solution t component coordinate radius
    _ = factor * ‖state component‖ := by
      dsimp [factor]
      ring
    _ ≤ factor * ‖state‖ := by
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm state component) hfactor

/-- The quantitative reconstruction fibre expressed only through the positive logarithmic `H³`
receiver used by the continuation line. -/
theorem openPeriodicJacobianCoefficientTailMass_frequencyCube_le_logReceiver
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (radius : ℕ) :
    openPeriodicJacobianCoefficientTailMass solution ⟨t, ht⟩
        (frequencyCube radius) ≤
      (2 * Real.pi) *
        Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
          Real.sqrt (240 * coordinateLogH3Receiver velocity t) := by
  let time : Ioo 0 T := ⟨t, ht⟩
  let state : PeriodicVectorWeightedSobolev 3 :=
    smoothSliceVectorWeightedH3 (fun x ↦ velocity x t)
      (openPeriodicSolutionOn_velocitySlice_contDiff solution ht)
      (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩)
  let factor : ℝ :=
    (2 * Real.pi) *
      Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass)
  have htail := openPeriodicJacobianCoefficientTailMass_frequencyCube_le
    solution time radius
  have hsquare :=
    openPeriodicSolutionOn_norm_sq_smoothSliceVectorWeightedH3_le_logReceiver
      solution ht
  have hreceiver : 0 ≤ 240 * coordinateLogH3Receiver velocity t :=
    mul_nonneg (by norm_num) (le_trans (by norm_num)
      (one_le_coordinateLogH3Receiver velocity t))
  have hstate : ‖state‖ ≤
      Real.sqrt (240 * coordinateLogH3Receiver velocity t) := by
    calc
      ‖state‖ = Real.sqrt (‖state‖ ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ ≤ Real.sqrt (240 * coordinateLogH3Receiver velocity t) :=
        Real.sqrt_le_sqrt hsquare
  have hfactor : 0 ≤ factor := by
    dsimp [factor]
    positivity
  calc
    openPeriodicJacobianCoefficientTailMass solution ⟨t, ht⟩
        (frequencyCube radius) ≤ factor * ‖state‖ := by
      simpa only [time, state, factor, mul_assoc] using htail
    _ ≤ factor * Real.sqrt (240 * coordinateLogH3Receiver velocity t) :=
      mul_le_mul_of_nonneg_left hstate hfactor

section Audit

#print axioms summable_jacobianTailCoordinateWeight
#print axioms summable_jacobianTailLatticeWeight
#print axioms fractionalCoordinateWeight_le_scale_mul_tailWeight
#print axioms exists_coordinate_natAbs_gt_of_not_mem_frequencyCube
#print axioms fractionalFirstMomentWeight_le_scale_mul_tailLatticeWeight
#print axioms tsum_fractionalFirstMomentWeight_compl_frequencyCube_le
#print axioms tsum_coordinate_sq_div_weight_three_compl_frequencyCube_le
#print axioms norm_coordinateReciprocalSobolevThreeSqrtTail_sq_le
#print axioms norm_weightedSobolevThreeCoefficientTail_le
#print axioms tsum_coordinate_mul_norm_compl_frequencyCube_le
#print axioms tsum_norm_openPeriodicJacobianFourierMode_entry_compl_frequencyCube_le
#print axioms openPeriodicJacobianCoefficientTailMass_frequencyCube_le
#print axioms openPeriodicJacobianCoefficientTailMass_frequencyCube_le_logReceiver

end Audit

end Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
