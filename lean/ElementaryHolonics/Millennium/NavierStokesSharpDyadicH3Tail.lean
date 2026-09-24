import ElementaryHolonics.Millennium.NavierStokesVorticityBandBernsteinAlternative

/-!
# Sharp dyadic `H³` derivative tails on the periodic frequency lattice

**[proved-derived]** The separable coordinate split used by the first quantitative Jacobian-tail
owner loses most of the isotropic three-dimensional shell decay.  This owner keeps the actual
cube shells.  A shell at radius `2^j` has `O(2^(3j))` modes, while each reciprocal derivative
square weight is `O(2^(-4j))`; its total mass is therefore `O(2^(-j))`.

The resulting square-root coefficient tail is `O(2^(-j/2)) · ‖u‖_H³`.  This is an interior-slice
estimate only.  No terminal trace or time-integrated `H³` control is inferred.
-/

noncomputable section

open Set
open scoped BigOperators ENNReal lp

namespace Soma.Holonics.Millennium.NavierStokesSharpDyadicH3Tail

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FrequencyComb
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityBandBernsteinAlternative
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## One isotropic dyadic shell -/

/-- The actual reciprocal derivative-square population on one dyadic cube shell. -/
def sharpJacobianDyadicShellSquareMass (coordinate : Fin 3) (level : ℕ) : ℝ :=
  ∑ frequency ∈ dyadicFrequencyShell level,
    (frequency coordinate : ℝ) ^ 2 / periodicSobolevWeight 3 frequency

/-- Outside a cube of positive radius, each reciprocal `H³` derivative-square weight pays the
full fourth power of that radius. -/
theorem coordinate_sq_div_weight_three_le_inv_radius_four
    (coordinate : Fin 3) (radius : ℕ) (hradius : 0 < radius)
    {frequency : SpatialFrequency} (hfrequency : frequency ∉ frequencyCube radius) :
    (frequency coordinate : ℝ) ^ 2 / periodicSobolevWeight 3 frequency ≤
      ((radius : ℝ) ^ 4)⁻¹ := by
  obtain ⟨escaping, hescaping⟩ :=
    exists_coordinate_natAbs_gt_of_not_mem_frequencyCube radius hfrequency
  have hfrequencyNonneg : 0 ≤ frequencySquared frequency := by
    unfold frequencySquared
    positivity
  have hcoordinate : (frequency coordinate : ℝ) ^ 2 ≤ frequencySquared frequency := by
    unfold frequencySquared
    exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (frequency i : ℝ))
      (Finset.mem_univ coordinate)
  have hescapingCast : (radius : ℝ) < |(frequency escaping : ℝ)| := by
    have hnat : radius < (frequency escaping).natAbs := hescaping
    have hcast : (radius : ℝ) < ((frequency escaping).natAbs : ℝ) := by
      exact_mod_cast hnat
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
  have hradiusCast : 0 < (radius : ℝ) := by exact_mod_cast hradius
  have hradiusSq : (radius : ℝ) ^ 2 ≤ frequencySquared frequency := by
    have hsquare : (radius : ℝ) ^ 2 < |(frequency escaping : ℝ)| ^ 2 := by
      nlinarith [abs_nonneg (frequency escaping : ℝ)]
    have hescapeCoordinate :
        |(frequency escaping : ℝ)| ^ 2 ≤ frequencySquared frequency := by
      unfold frequencySquared
      simpa only [sq_abs] using
        (Finset.single_le_sum (fun i _ ↦ sq_nonneg (frequency i : ℝ))
          (Finset.mem_univ escaping))
    exact hsquare.le.trans hescapeCoordinate
  have hfrequencyPos : 0 < frequencySquared frequency :=
    lt_of_lt_of_le (sq_pos_of_pos hradiusCast) hradiusSq
  have hscale : 1 ≤ (2 * Real.pi) ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hscaledFrequency :
      frequencySquared frequency ≤ (2 * Real.pi) ^ 2 * frequencySquared frequency :=
    by simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hscale hfrequencyNonneg)
  have hfrequency_le_weightBase :
      frequencySquared frequency ≤ 1 + torusStokesEigenvalue frequency := by
    rw [torusStokesEigenvalue]
    linarith
  have hdenominator :
      (frequencySquared frequency) ^ 3 ≤ periodicSobolevWeight 3 frequency := by
    rw [periodicSobolevWeight]
    exact pow_le_pow_left₀ hfrequencyNonneg hfrequency_le_weightBase 3
  have hfirst :
      (frequency coordinate : ℝ) ^ 2 / periodicSobolevWeight 3 frequency ≤
        frequencySquared frequency / (frequencySquared frequency) ^ 3 := by
    exact div_le_div₀ hfrequencyNonneg hcoordinate
      (pow_pos hfrequencyPos 3) hdenominator
  have hsquareInv :
      frequencySquared frequency / (frequencySquared frequency) ^ 3 =
        ((frequencySquared frequency) ^ 2)⁻¹ := by
    field_simp
  have hpow : (radius : ℝ) ^ 4 ≤ (frequencySquared frequency) ^ 2 := by
    calc
      (radius : ℝ) ^ 4 = ((radius : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ (frequencySquared frequency) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg (radius : ℝ)) hradiusSq 2
  calc
    (frequency coordinate : ℝ) ^ 2 / periodicSobolevWeight 3 frequency ≤
        frequencySquared frequency / (frequencySquared frequency) ^ 3 := hfirst
    _ = ((frequencySquared frequency) ^ 2)⁻¹ := hsquareInv
    _ ≤ ((radius : ℝ) ^ 4)⁻¹ :=
      (inv_le_inv₀ (pow_pos hfrequencyPos 2) (pow_pos hradiusCast 4)).2 hpow

/-- A dyadic shell contains at most `125 · (2^j)^3` modes. -/
theorem card_dyadicFrequencyShell_le_one_hundred_twenty_five_mul_cube
    (level : ℕ) :
    (dyadicFrequencyShell level).card ≤ 125 * (dyadicRadius level) ^ 3 := by
  have hsubset : dyadicFrequencyShell level ⊆ frequencyCube (dyadicRadius (level + 1)) :=
    fun _ h ↦ (Finset.mem_sdiff.mp h).1
  have hcard := Finset.card_le_card hsubset
  rw [card_frequencyCube] at hcard
  have hradiusPos : 0 < dyadicRadius level := by
    simp [dyadicRadius]
  have hnext : dyadicRadius (level + 1) = 2 * dyadicRadius level := by
    simp [dyadicRadius, pow_succ, mul_comm]
  rw [hnext] at hcard
  calc
    (dyadicFrequencyShell level).card ≤
        (2 * (2 * dyadicRadius level) + 1) ^ 3 := hcard
    _ ≤ (5 * dyadicRadius level) ^ 3 := by
      apply Nat.pow_le_pow_left
      omega
    _ = 125 * (dyadicRadius level) ^ 3 := by ring

/-- The reciprocal derivative-square mass of shell `j` is at most `125 / 2^j`. -/
theorem sharpJacobianDyadicShellSquareMass_le (coordinate : Fin 3) (level : ℕ) :
    sharpJacobianDyadicShellSquareMass coordinate level ≤
      125 * ((dyadicRadius level : ℝ))⁻¹ := by
  have hradiusPos : 0 < dyadicRadius level := by simp [dyadicRadius]
  have hpoint (frequency : SpatialFrequency)
      (hfrequency : frequency ∈ dyadicFrequencyShell level) :
      (frequency coordinate : ℝ) ^ 2 / periodicSobolevWeight 3 frequency ≤
        (((dyadicRadius level : ℝ) ^ 4)⁻¹) := by
    exact coordinate_sq_div_weight_three_le_inv_radius_four coordinate
      (dyadicRadius level) hradiusPos (Finset.mem_sdiff.mp hfrequency).2
  unfold sharpJacobianDyadicShellSquareMass
  calc
    (∑ frequency ∈ dyadicFrequencyShell level,
        (frequency coordinate : ℝ) ^ 2 / periodicSobolevWeight 3 frequency) ≤
        (dyadicFrequencyShell level).card •
          (((dyadicRadius level : ℝ) ^ 4)⁻¹) :=
      Finset.sum_le_card_nsmul _ _ _ hpoint
    _ = ((dyadicFrequencyShell level).card : ℝ) *
          (((dyadicRadius level : ℝ) ^ 4)⁻¹) := by simp
    _ ≤ (125 * (dyadicRadius level) ^ 3 : ℕ) *
          (((dyadicRadius level : ℝ) ^ 4)⁻¹) := by
      gcongr
      exact_mod_cast
        card_dyadicFrequencyShell_le_one_hundred_twenty_five_mul_cube level
    _ = 125 * ((dyadicRadius level : ℝ))⁻¹ := by
      have hradiusCast : (dyadicRadius level : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp

theorem sharpJacobianDyadicShellSquareMass_nonneg (coordinate : Fin 3) (level : ℕ) :
    0 ≤ sharpJacobianDyadicShellSquareMass coordinate level := by
  unfold sharpJacobianDyadicShellSquareMass
  exact Finset.sum_nonneg fun frequency _ ↦
    div_nonneg (sq_nonneg _) (periodicSobolevWeight_nonneg 3 frequency)

/-- The shell estimate in literal geometric-scale form. -/
theorem sharpJacobianDyadicShellSquareMass_le_geometric
    (coordinate : Fin 3) (level : ℕ) :
    sharpJacobianDyadicShellSquareMass coordinate level ≤
      125 * (1 / 2 : ℝ) ^ level := by
  calc
    sharpJacobianDyadicShellSquareMass coordinate level ≤
        125 * ((dyadicRadius level : ℝ))⁻¹ :=
      sharpJacobianDyadicShellSquareMass_le coordinate level
    _ = 125 * (1 / 2 : ℝ) ^ level := by
      simp [dyadicRadius, one_div, inv_pow]

/-- The complete dyadic shell population beyond `depth`. -/
def sharpJacobianDyadicShellTailMass (coordinate : Fin 3) (depth : ℕ) : ℝ :=
  ∑' offset : ℕ, sharpJacobianDyadicShellSquareMass coordinate (depth + offset)

theorem summable_sharpJacobianDyadicShellSquareMass_from
    (coordinate : Fin 3) (depth : ℕ) :
    Summable fun offset : ℕ ↦
      sharpJacobianDyadicShellSquareMass coordinate (depth + offset) := by
  let majorant : ℕ → ℝ := fun offset ↦ 125 * (1 / 2 : ℝ) ^ (depth + offset)
  have hmajorant : Summable majorant := by
    have hgeom : Summable fun offset : ℕ ↦ (1 / 2 : ℝ) ^ offset :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hscaled := hgeom.mul_left (125 * (1 / 2 : ℝ) ^ depth)
    exact hscaled.congr fun offset ↦ by
      simp only [majorant, pow_add]
      ring
  exact Summable.of_nonneg_of_le
    (fun offset ↦ sharpJacobianDyadicShellSquareMass_nonneg coordinate _)
    (fun offset ↦ sharpJacobianDyadicShellSquareMass_le_geometric coordinate _)
    hmajorant

/-- Summing all dyadic shells beyond `depth` retains the sharp `2^(-depth)` square-mass rate. -/
theorem sharpJacobianDyadicShellTailMass_le (coordinate : Fin 3) (depth : ℕ) :
    sharpJacobianDyadicShellTailMass coordinate depth ≤
      250 * ((dyadicRadius depth : ℝ))⁻¹ := by
  let majorant : ℕ → ℝ := fun offset ↦ 125 * (1 / 2 : ℝ) ^ (depth + offset)
  have hsummable := summable_sharpJacobianDyadicShellSquareMass_from coordinate depth
  have hmajorant : Summable majorant := by
    have hgeom : Summable fun offset : ℕ ↦ (1 / 2 : ℝ) ^ offset :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hscaled := hgeom.mul_left (125 * (1 / 2 : ℝ) ^ depth)
    exact hscaled.congr fun offset ↦ by
      simp only [majorant, pow_add]
      ring
  unfold sharpJacobianDyadicShellTailMass
  calc
    (∑' offset : ℕ,
        sharpJacobianDyadicShellSquareMass coordinate (depth + offset)) ≤
        ∑' offset : ℕ, majorant offset :=
      hsummable.tsum_le_tsum
        (fun offset ↦ sharpJacobianDyadicShellSquareMass_le_geometric coordinate _)
        hmajorant
    _ = ∑' offset : ℕ,
          (125 * (1 / 2 : ℝ) ^ depth) * (1 / 2 : ℝ) ^ offset := by
      apply tsum_congr
      intro offset
      simp only [majorant, pow_add]
      ring
    _ = (125 * (1 / 2 : ℝ) ^ depth) *
          ∑' offset : ℕ, (1 / 2 : ℝ) ^ offset := tsum_mul_left
    _ = 250 * ((dyadicRadius depth : ℝ))⁻¹ := by
      rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)]
      norm_num [dyadicRadius, one_div, inv_pow]
      simp [one_div]
      ring

/-! ## Reconstruction of the complete cube complement -/

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega

/-- Every finite population of unresolved frequencies lies in one later dyadic aperture. -/
private theorem finite_frequencyCubeComplement_subset_laterCube
    (depth : ℕ) (u : Finset (FrequencyCubeComplement (dyadicRadius depth))) :
    ∃ offset : ℕ,
      u.map (Function.Embedding.subtype
        (fun frequency : SpatialFrequency ↦ frequency ∉ frequencyCube (dyadicRadius depth))) ⊆
        frequencyCube (dyadicRadius (depth + offset)) := by
  let coordinateMass : SpatialFrequency → ℕ := fun frequency ↦
    ∑ coordinate : Fin 3, (frequency coordinate).natAbs
  let offset : ℕ :=
    (∑ frequency ∈ u.map (Function.Embedding.subtype
      (fun frequency : SpatialFrequency ↦ frequency ∉ frequencyCube (dyadicRadius depth))),
        coordinateMass frequency) + 1
  refine ⟨offset, ?_⟩
  intro frequency hfrequency
  rw [mem_frequencyCube_iff]
  intro coordinate
  have hcoordinateMass : (frequency coordinate).natAbs ≤ coordinateMass frequency := by
    unfold coordinateMass
    exact Finset.single_le_sum
      (s := Finset.univ) (f := fun axis ↦ (frequency axis).natAbs)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ coordinate)
  have hmassTotal : coordinateMass frequency ≤
      ∑ k ∈ u.map (Function.Embedding.subtype
        (fun k : SpatialFrequency ↦ k ∉ frequencyCube (dyadicRadius depth))),
          coordinateMass k := by
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hfrequency
  have hcoordinateOffset : (frequency coordinate).natAbs ≤ offset := by
    dsimp [offset]
    omega
  have hoffsetPow : offset ≤ dyadicRadius (depth + offset) := by
    calc
      offset ≤ 2 ^ offset := nat_le_two_pow offset
      _ ≤ 2 ^ (depth + offset) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left offset depth)
      _ = dyadicRadius (depth + offset) := by rfl
  exact (natAbs_le_iff_bounds _ _).mp (hcoordinateOffset.trans hoffsetPow)

/-- The actual reciprocal derivative-square population over the complete complement of the
dyadic cube has the shell bound.  This is the sharp `O(2^(-depth))` lattice estimate. -/
theorem tsum_coordinate_sq_div_weight_three_compl_dyadicCube_le_shellTail
    (coordinate : Fin 3) (depth : ℕ) :
    (∑' frequency : FrequencyCubeComplement (dyadicRadius depth),
        (frequency.1 coordinate : ℝ) ^ 2 /
          periodicSobolevWeight 3 frequency.1) ≤
      sharpJacobianDyadicShellTailMass coordinate depth := by
  let weight : SpatialFrequency → ℝ := fun frequency ↦
    (frequency coordinate : ℝ) ^ 2 / periodicSobolevWeight 3 frequency
  have hsummable : Summable fun frequency : FrequencyCubeComplement (dyadicRadius depth) ↦
      weight frequency.1 :=
    (summable_coordinate_sq_div_periodicSobolevWeight_three coordinate).subtype
      {frequency : SpatialFrequency | frequency ∉ frequencyCube (dyadicRadius depth)}
  apply hsummable.tsum_le_of_sum_le
  intro u
  obtain ⟨offset, houter⟩ :=
    finite_frequencyCubeComplement_subset_laterCube depth u
  let raw : Finset SpatialFrequency :=
    u.map (Function.Embedding.subtype
      (fun frequency : SpatialFrequency ↦ frequency ∉ frequencyCube (dyadicRadius depth)))
  let cubes : ℕ → Finset SpatialFrequency := fun step ↦
    frequencyCube (dyadicRadius (depth + step))
  have hcubes : Monotone cubes := by
    intro first second hfirst
    apply frequencyCube_mono
    unfold dyadicRadius
    exact Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_left hfirst depth)
  have hrawSubset : raw ⊆ cubes offset \ cubes 0 := by
    intro frequency hfrequency
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact houter hfrequency
    · rcases Finset.mem_map.mp hfrequency with ⟨source, _hsource, rfl⟩
      simpa [cubes] using source.2
  have hrawLe : (∑ frequency ∈ raw, weight frequency) ≤
      ∑ frequency ∈ cubes offset \ cubes 0, weight frequency := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hrawSubset
      (fun frequency _ _ ↦
        div_nonneg (sq_nonneg _) (periodicSobolevWeight_nonneg 3 frequency))
  have hdecomposition := Finset.sum_eq_sum_range_sdiff cubes hcubes weight offset
  have hinnerSubset : cubes 0 ⊆ cubes offset := hcubes (Nat.zero_le offset)
  have hsdiff := Finset.sum_sdiff hinnerSubset (f := weight)
  have hdiffEq : (∑ frequency ∈ cubes offset \ cubes 0, weight frequency) =
      ∑ step ∈ Finset.range offset,
        ∑ frequency ∈ cubes (step + 1) \ cubes step, weight frequency := by
    rw [hdecomposition] at hsdiff
    linarith
  have hshellEq (step : ℕ) :
      cubes (step + 1) \ cubes step = dyadicFrequencyShell (depth + step) := by
    unfold cubes dyadicFrequencyShell
    congr 1
  have hfiniteShellLe :
      (∑ step ∈ Finset.range offset,
        ∑ frequency ∈ cubes (step + 1) \ cubes step, weight frequency) ≤
        sharpJacobianDyadicShellTailMass coordinate depth := by
    have hshellSummable :=
      summable_sharpJacobianDyadicShellSquareMass_from coordinate depth
    unfold sharpJacobianDyadicShellTailMass
    calc
      (∑ step ∈ Finset.range offset,
          ∑ frequency ∈ cubes (step + 1) \ cubes step, weight frequency) =
          ∑ step ∈ Finset.range offset,
            sharpJacobianDyadicShellSquareMass coordinate (depth + step) := by
        apply Finset.sum_congr rfl
        intro step _hstep
        rw [hshellEq step]
        rfl
      _ ≤ ∑' step : ℕ,
          sharpJacobianDyadicShellSquareMass coordinate (depth + step) :=
        hshellSummable.sum_le_tsum _
          (fun step _ ↦
            sharpJacobianDyadicShellSquareMass_nonneg coordinate (depth + step))
  have hsumRaw : (∑ frequency ∈ raw, weight frequency) =
      ∑ frequency ∈ u, weight frequency.1 := by
    unfold raw
    exact Finset.sum_map u
      (Function.Embedding.subtype
        (fun frequency : SpatialFrequency ↦
          frequency ∉ frequencyCube (dyadicRadius depth))) weight
  calc
    (∑ frequency ∈ u, weight frequency.1) =
        ∑ frequency ∈ raw, weight frequency := hsumRaw.symm
    _ ≤ ∑ frequency ∈ cubes offset \ cubes 0, weight frequency := hrawLe
    _ = ∑ step ∈ Finset.range offset,
        ∑ frequency ∈ cubes (step + 1) \ cubes step, weight frequency := hdiffEq
    _ ≤ sharpJacobianDyadicShellTailMass coordinate depth := hfiniteShellLe

/-- Explicit sharp lattice tail: the square mass is at most `250 · 2^(-depth)`. -/
theorem tsum_coordinate_sq_div_weight_three_compl_dyadicCube_le
    (coordinate : Fin 3) (depth : ℕ) :
    (∑' frequency : FrequencyCubeComplement (dyadicRadius depth),
        (frequency.1 coordinate : ℝ) ^ 2 /
          periodicSobolevWeight 3 frequency.1) ≤
      250 * ((dyadicRadius depth : ℝ))⁻¹ :=
  (tsum_coordinate_sq_div_weight_three_compl_dyadicCube_le_shellTail
    coordinate depth).trans (sharpJacobianDyadicShellTailMass_le coordinate depth)

/-! ## Sharp square-root coefficient tail -/

private theorem norm_coordinateReciprocalSobolevThreeSqrtTail_sq_at
    (coordinate : Fin 3) (radius : ℕ)
    (frequency : FrequencyCubeComplement radius) :
    ‖coordinateReciprocalSobolevThreeSqrtTail coordinate radius frequency‖ ^ 2 =
      (frequency.1 coordinate : ℝ) ^ 2 /
        periodicSobolevWeight 3 frequency.1 := by
  rw [coordinateReciprocalSobolevThreeSqrtTail, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)),
    div_pow, sq_abs,
    Real.sq_sqrt (periodicSobolevWeight_nonneg 3 frequency.1)]

/-- The reciprocal derivative carrier itself decays at the sharp square-root shell rate. -/
theorem norm_coordinateReciprocalSobolevThreeSqrtTail_dyadic_le
    (coordinate : Fin 3) (depth : ℕ) :
    ‖coordinateReciprocalSobolevThreeSqrtTail coordinate (dyadicRadius depth)‖ ≤
      Real.sqrt (250 * ((dyadicRadius depth : ℝ))⁻¹) := by
  have hnorm := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (coordinateReciprocalSobolevThreeSqrtTail coordinate (dyadicRadius depth))
  have hnormSq :
      ‖coordinateReciprocalSobolevThreeSqrtTail coordinate (dyadicRadius depth)‖ ^ 2 =
        ∑' frequency : FrequencyCubeComplement (dyadicRadius depth),
          (frequency.1 coordinate : ℝ) ^ 2 /
            periodicSobolevWeight 3 frequency.1 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      norm_coordinateReciprocalSobolevThreeSqrtTail_sq_at] using hnorm
  have hsquare :
      ‖coordinateReciprocalSobolevThreeSqrtTail coordinate (dyadicRadius depth)‖ ^ 2 ≤
        250 * ((dyadicRadius depth : ℝ))⁻¹ := by
    rw [hnormSq]
    exact tsum_coordinate_sq_div_weight_three_compl_dyadicCube_le coordinate depth
  calc
    ‖coordinateReciprocalSobolevThreeSqrtTail coordinate (dyadicRadius depth)‖ =
        Real.sqrt
          (‖coordinateReciprocalSobolevThreeSqrtTail coordinate (dyadicRadius depth)‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ ≤ Real.sqrt (250 * ((dyadicRadius depth : ℝ))⁻¹) :=
      Real.sqrt_le_sqrt hsquare

private theorem coordinateReciprocal_mul_weightedTail_eq_at
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

/-- Sharp generic `H³` derivative coefficient tail beyond the dyadic cube.  Since
`dyadicRadius depth = 2^depth`, the displayed factor is exactly `O(2^(-depth/2))`. -/
theorem tsum_coordinate_mul_norm_compl_dyadicCube_le
    (coeff : PeriodicSobolevCoefficients 3) (coordinate : Fin 3)
    (depth : ℕ) :
    (∑' frequency : FrequencyCubeComplement (dyadicRadius depth),
        |(frequency.1 coordinate : ℝ)| * ‖coeff.1 frequency.1‖) ≤
      Real.sqrt (250 * ((dyadicRadius depth : ℝ))⁻¹) *
        ‖weightedSobolevThreeCoefficient coeff‖ := by
  have hholder :
      (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa only [ENNReal.toReal_ofNat] using Real.HolderConjugate.two_two
  let reciprocal := coordinateReciprocalSobolevThreeSqrtTail coordinate (dyadicRadius depth)
  let weighted := weightedSobolevThreeCoefficientTail coeff (dyadicRadius depth)
  calc
    (∑' frequency : FrequencyCubeComplement (dyadicRadius depth),
        |(frequency.1 coordinate : ℝ)| * ‖coeff.1 frequency.1‖) =
        ∑' frequency : FrequencyCubeComplement (dyadicRadius depth),
          ‖reciprocal frequency‖ * ‖weighted frequency‖ := by
      apply tsum_congr
      intro frequency
      exact (coordinateReciprocal_mul_weightedTail_eq_at
        coeff coordinate (dyadicRadius depth) frequency).symm
    _ ≤ ‖reciprocal‖ * ‖weighted‖ :=
      lp.tsum_mul_le_mul_norm' hholder reciprocal weighted
    _ ≤ Real.sqrt (250 * ((dyadicRadius depth : ℝ))⁻¹) *
        ‖weighted‖ := by
      exact mul_le_mul_of_nonneg_right
        (norm_coordinateReciprocalSobolevThreeSqrtTail_dyadic_le coordinate depth)
        (norm_nonneg _)
    _ ≤ Real.sqrt (250 * ((dyadicRadius depth : ℝ))⁻¹) *
        ‖weightedSobolevThreeCoefficient coeff‖ := by
      exact mul_le_mul_of_nonneg_left
        (norm_weightedSobolevThreeCoefficientTail_le coeff (dyadicRadius depth))
        (Real.sqrt_nonneg _)

#print axioms coordinate_sq_div_weight_three_le_inv_radius_four
#print axioms sharpJacobianDyadicShellSquareMass_le
#print axioms sharpJacobianDyadicShellTailMass_le
#print axioms tsum_coordinate_sq_div_weight_three_compl_dyadicCube_le
#print axioms norm_coordinateReciprocalSobolevThreeSqrtTail_dyadic_le
#print axioms tsum_coordinate_mul_norm_compl_dyadicCube_le

end Soma.Holonics.Millennium.NavierStokesSharpDyadicH3Tail
