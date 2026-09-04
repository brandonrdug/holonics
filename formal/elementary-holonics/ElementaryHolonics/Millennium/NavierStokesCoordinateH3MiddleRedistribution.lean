import ElementaryHolonics.Millennium.NavierStokesPeriodicCubeInterpolation

/-!
# Trilinear redistribution of the three middle H³ faces

The periodic cubic-flux owner supplies an actual fourth-power estimate for every ordered second
spatial jet.  This file composes two such returns with the third-jet quadratic population.  The
composition uses the scaled polynomial Young inequality

`a b c ≤ a⁴ / (4 M) + b⁴ / (4 M) + M c² / 2`

when `M > 0`; the `M = 0` fibre is retained separately and follows from vanishing of either
nonnegative fourth-power integral.  Thus the result remains linear, rather than quadratic, in the
actual cube Jacobian supremum.  No Fourier `ℓ¹` receiver or `H³`-by-`H³` substitution is used.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Set
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesCoordinateH3MiddleRedistribution

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH2Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH3Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH3Estimate
open Soma.Holonics.Millennium.NavierStokesPeriodicCubeInterpolation

/-! ## A scale-exact trilinear integral lemma -/

/-- The polynomial form of the `(4,4,2)` Young inequality, with the scale exposed. -/
theorem mul_three_le_fourth_div_add_fourth_div_add_half_sq
    {a b c M : ℝ} (hM : 0 < M) :
    a * b * c ≤
      (1 / (4 * M)) * a ^ 4 + (1 / (4 * M)) * b ^ 4 + (M / 2) * c ^ 2 := by
  have hab : 0 ≤ (a ^ 2 - b ^ 2) ^ 2 := sq_nonneg _
  have habc : 0 ≤ (a * b - M * c) ^ 2 := sq_nonneg _
  have hscaled : 4 * M * (a * b * c) ≤ a ^ 4 + b ^ 4 + 2 * M ^ 2 * c ^ 2 := by
    nlinarith
  calc
    a * b * c ≤ (a ^ 4 + b ^ 4 + 2 * M ^ 2 * c ^ 2) / (4 * M) :=
      (le_div_iff₀ (by positivity)).2 (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled)
    _ = (1 / (4 * M)) * a ^ 4 + (1 / (4 * M)) * b ^ 4 +
        (M / 2) * c ^ 2 := by
      field_simp
      ring

/-- Two fourth-power returns and one quadratic return compose to a trilinear bound which is
linear in `M`.  The zero-scale fibre is proved from the actual vanishing integral, not excluded. -/
theorem integral_norm_mul_norm_mul_norm_le_seven_mul
    (A B C : Space → Space) (M EA EB EC : ℝ)
    (hA : ContDiff ℝ 0 A) (hB : ContDiff ℝ 0 B) (hC : ContDiff ℝ 0 C)
    (hM : 0 ≤ M) (hEA : 0 ≤ EA) (hEB : 0 ≤ EB) (hEC : 0 ≤ EC)
    (hA4 : ∫ x in unitCube, ‖A x‖ ^ 4 ≤ 27 * M ^ 2 * EA)
    (hB4 : ∫ x in unitCube, ‖B x‖ ^ 4 ≤ 27 * M ^ 2 * EB)
    (hC2 : ∫ x in unitCube, ‖C x‖ ^ 2 = EC) :
    ∫ x in unitCube, ‖A x‖ * ‖B x‖ * ‖C x‖ ≤ 7 * M * (EA + EB + EC) := by
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  have hA4Int : IntegrableOn (fun x ↦ ‖A x‖ ^ 4) unitCube :=
    ((hA.continuous.norm.pow 4).continuousOn).integrableOn_compact hcubeCompact
  have hB4Int : IntegrableOn (fun x ↦ ‖B x‖ ^ 4) unitCube :=
    ((hB.continuous.norm.pow 4).continuousOn).integrableOn_compact hcubeCompact
  have hC2Int : IntegrableOn (fun x ↦ ‖C x‖ ^ 2) unitCube :=
    ((hC.continuous.norm.pow 2).continuousOn).integrableOn_compact hcubeCompact
  have htripleInt : IntegrableOn (fun x ↦ ‖A x‖ * ‖B x‖ * ‖C x‖) unitCube :=
    (((hA.continuous.norm.mul hB.continuous.norm).mul hC.continuous.norm).continuousOn
      ).integrableOn_compact hcubeCompact
  rcases hM.eq_or_lt with rfl | hMpos
  · have hAIntegralNonneg : 0 ≤ ∫ x in unitCube, ‖A x‖ ^ 4 :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x ↦ by positivity))
    have hAIntegralZero : ∫ x in unitCube, ‖A x‖ ^ 4 = 0 := by
      have hupper : ∫ x in unitCube, ‖A x‖ ^ 4 ≤ 0 := by simpa using hA4
      exact le_antisymm hupper hAIntegralNonneg
    have hAZero : (fun x ↦ ‖A x‖ ^ 4) =ᵐ[volume.restrict unitCube] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun x ↦ by positivity) hA4Int).1 hAIntegralZero
    have htripleZero : (fun x ↦ ‖A x‖ * ‖B x‖ * ‖C x‖) =ᵐ[volume.restrict unitCube] 0 := by
      filter_upwards [hAZero] with x hx
      have hnormA : ‖A x‖ = 0 := by
        exact eq_zero_of_pow_eq_zero hx
      simp [hnormA]
    rw [integral_congr_ae htripleZero]
    norm_num
  · have hpoint : ∀ x ∈ unitCube,
        ‖A x‖ * ‖B x‖ * ‖C x‖ ≤
          (1 / (4 * M)) * ‖A x‖ ^ 4 + (1 / (4 * M)) * ‖B x‖ ^ 4 +
            (M / 2) * ‖C x‖ ^ 2 := by
      intro x _hx
      exact mul_three_le_fourth_div_add_fourth_div_add_half_sq hMpos
    have hrightInt : IntegrableOn
        (fun x ↦ (1 / (4 * M)) * ‖A x‖ ^ 4 + (1 / (4 * M)) * ‖B x‖ ^ 4 +
          (M / 2) * ‖C x‖ ^ 2) unitCube :=
      ((hA4Int.const_mul _).add (hB4Int.const_mul _)).add (hC2Int.const_mul _)
    have hintegral := setIntegral_mono_on htripleInt hrightInt
      hcubeCompact.measurableSet hpoint
    have hrightEval :
        (∫ x in unitCube,
          ((1 / (4 * M)) * ‖A x‖ ^ 4 + (1 / (4 * M)) * ‖B x‖ ^ 4) +
            (M / 2) * ‖C x‖ ^ 2) =
          (1 / (4 * M)) * (∫ x in unitCube, ‖A x‖ ^ 4) +
            (1 / (4 * M)) * (∫ x in unitCube, ‖B x‖ ^ 4) +
              (M / 2) * EC := by
      calc
        _ =
            (∫ x in unitCube,
              (1 / (4 * M)) * ‖A x‖ ^ 4 + (1 / (4 * M)) * ‖B x‖ ^ 4) +
              ∫ x in unitCube, (M / 2) * ‖C x‖ ^ 2 := by
          exact integral_add ((hA4Int.const_mul _).add (hB4Int.const_mul _))
            (hC2Int.const_mul _)
        _ =
            ((∫ x in unitCube, (1 / (4 * M)) * ‖A x‖ ^ 4) +
              ∫ x in unitCube, (1 / (4 * M)) * ‖B x‖ ^ 4) +
              ∫ x in unitCube, (M / 2) * ‖C x‖ ^ 2 := by
          rw [integral_add (hA4Int.const_mul _) (hB4Int.const_mul _)]
        _ = _ := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul, hC2]
    rw [hrightEval] at hintegral
    calc
      ∫ x in unitCube, ‖A x‖ * ‖B x‖ * ‖C x‖ ≤
          (1 / (4 * M)) * (27 * M ^ 2 * EA) +
            (1 / (4 * M)) * (27 * M ^ 2 * EB) + (M / 2) * EC := by
        exact hintegral.trans (by gcongr)
      _ = (27 / 4) * M * EA + (27 / 4) * M * EB + (1 / 2) * M * EC := by
        field_simp [ne_of_gt hMpos]
      _ ≤ 7 * M * (EA + EB + EC) := by
        nlinarith

/-! ## The actual ordered third-jet quadratic population -/

/-- The component-complete quadratic mass of one ordered third spatial word. -/
def thirdWordSquareMass (u : InitialVelocity) (i j k : Fin 3) : ℝ :=
  ∑ component : Fin 3,
    ∫ x in unitCube, (thirdSpatialCoordinateJet u i j k x component) ^ 2

theorem thirdWordSquareMass_nonneg (u : InitialVelocity) (i j k : Fin 3) :
    0 ≤ thirdWordSquareMass u i j k := by
  apply Finset.sum_nonneg
  intro component _hcomponent
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _))

/-- Euclidean norm-square integration is exactly the retained finite component population. -/
theorem integral_norm_thirdSpatialCoordinateJet_sq_eq_mass
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (i j k : Fin 3) :
    ∫ x in unitCube, ‖thirdSpatialCoordinateJet u i j k x‖ ^ 2 =
      thirdWordSquareMass u i j k := by
  let third : InitialVelocity := thirdSpatialCoordinateJet u i j k
  have hthird : ContDiff ℝ ∞ third := thirdSpatialCoordinateJet_contDiff u hu i j k
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  have hcomponentInt : ∀ component : Fin 3,
      IntegrableOn (fun x ↦ (third x component) ^ 2) unitCube := by
    intro component
    exact ((((EuclideanSpace.proj component).continuous.comp hthird.continuous).pow 2).continuousOn
      ).integrableOn_compact hcubeCompact
  calc
    ∫ x in unitCube, ‖thirdSpatialCoordinateJet u i j k x‖ ^ 2 =
        ∫ x in unitCube, ∑ component : Fin 3, (third x component) ^ 2 := by
      apply setIntegral_congr_fun hcubeCompact.measurableSet
      intro x _hx
      change ‖third x‖ ^ 2 = ∑ component : Fin 3, (third x component) ^ 2
      simpa [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq (third x)
    _ = ∑ component : Fin 3, ∫ x in unitCube, (third x component) ^ 2 :=
      integral_finset_sum Finset.univ (fun component _hcomponent ↦ hcomponentInt component)
    _ = thirdWordSquareMass u i j k := rfl

/-- One actual `D²-D²-D³` norm face is linear in the Jacobian supremum and is returned by
three addressed third-word quadratic masses. -/
theorem integral_norm_second_mul_norm_second_mul_norm_third_le
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (i j a b p q r : Fin 3) :
    ∫ x in unitCube,
        ‖secondSpatialCoordinateJet u i j x‖ *
          ‖secondSpatialCoordinateJet u a b x‖ *
            ‖thirdSpatialCoordinateJet u p q r x‖ ≤
      7 * cubeGradientSup u *
        (thirdWordSquareMass u i i j + thirdWordSquareMass u a a b +
          thirdWordSquareMass u p q r) := by
  let A : InitialVelocity := secondSpatialCoordinateJet u i j
  let B : InitialVelocity := secondSpatialCoordinateJet u a b
  let C : InitialVelocity := thirdSpatialCoordinateJet u p q r
  have hA : ContDiff ℝ 0 A := (secondSpatialCoordinateJet_contDiff u hu i j).of_le (by simp)
  have hB : ContDiff ℝ 0 B := (secondSpatialCoordinateJet_contDiff u hu a b).of_le (by simp)
  have hC : ContDiff ℝ 0 C := (thirdSpatialCoordinateJet_contDiff u hu p q r).of_le (by simp)
  have hM := cubeGradientSup_nonneg u hu
  have hA4 := integral_norm_secondSpatialCoordinateJet_fourth_le u hu hperiodic i j
  have hB4 := integral_norm_secondSpatialCoordinateJet_fourth_le u hu hperiodic a b
  have hC2 := integral_norm_thirdSpatialCoordinateJet_sq_eq_mass u hu p q r
  simpa [A, B, C] using
    integral_norm_mul_norm_mul_norm_le_seven_mul A B C (cubeGradientSup u)
      (thirdWordSquareMass u i i j) (thirdWordSquareMass u a a b)
      (thirdWordSquareMass u p q r) hA hB hC hM
      (thirdWordSquareMass_nonneg u i i j)
      (thirdWordSquareMass_nonneg u a a b)
      (thirdWordSquareMass_nonneg u p q r) hA4 hB4 hC2

/-! ## The complete middle population of one ordered third word -/

/-- The complete component-retaining quadratic population of all twenty-seven ordered third
spatial words. -/
def thirdOrderSquareMass (u : InitialVelocity) : ℝ :=
  ∑ word : Fin 3 → Fin 3,
    thirdWordSquareMass u (word 0) (word 1) (word 2)

theorem thirdOrderSquareMass_nonneg (u : InitialVelocity) :
    0 ≤ thirdOrderSquareMass u := by
  exact Finset.sum_nonneg fun word _hword ↦
    thirdWordSquareMass_nonneg u (word 0) (word 1) (word 2)

theorem thirdWordSquareMass_le_thirdOrderSquareMass
    (u : InitialVelocity) (i j k : Fin 3) :
    thirdWordSquareMass u i j k ≤ thirdOrderSquareMass u := by
  let word : Fin 3 → Fin 3 := ![i, j, k]
  have hsingle := Finset.single_le_sum
    (fun candidate (_hcandidate : candidate ∈ (Finset.univ : Finset (Fin 3 → Fin 3))) ↦
      thirdWordSquareMass_nonneg u (candidate 0) (candidate 1) (candidate 2))
    (Finset.mem_univ word)
  simpa [thirdOrderSquareMass, word] using hsingle

/-- Each addressed trilinear face is bounded by twenty-one copies of the complete order-three
quadratic population. -/
theorem integral_norm_second_mul_norm_second_mul_norm_third_le_orderMass
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (i j a b p q r : Fin 3) :
    ∫ x in unitCube,
        ‖secondSpatialCoordinateJet u i j x‖ *
          ‖secondSpatialCoordinateJet u a b x‖ *
            ‖thirdSpatialCoordinateJet u p q r x‖ ≤
      21 * cubeGradientSup u * thirdOrderSquareMass u := by
  have hface := integral_norm_second_mul_norm_second_mul_norm_third_le
    u hu hperiodic i j a b p q r
  have hM := cubeGradientSup_nonneg u hu
  have hi := thirdWordSquareMass_le_thirdOrderSquareMass u i i j
  have ha := thirdWordSquareMass_le_thirdOrderSquareMass u a a b
  have hp := thirdWordSquareMass_le_thirdOrderSquareMass u p q r
  calc
    _ ≤ 7 * cubeGradientSup u *
        (thirdWordSquareMass u i i j + thirdWordSquareMass u a a b +
          thirdWordSquareMass u p q r) := hface
    _ ≤ 7 * cubeGradientSup u *
        (thirdOrderSquareMass u + thirdOrderSquareMass u + thirdOrderSquareMass u) := by
      gcongr
    _ = 21 * cubeGradientSup u * thirdOrderSquareMass u := by ring

/-- The nine norm products carried by the three middle faces after expanding their three
coordinate actions. -/
def spatialMiddleTriplePopulation
    (u : InitialVelocity) (i j k : Fin 3) (x : Space) : ℝ :=
  ∑ coordinate : Fin 3,
    (‖secondSpatialCoordinateJet u i j x‖ *
        ‖secondSpatialCoordinateJet u coordinate k x‖ *
          ‖thirdSpatialCoordinateJet u i j k x‖ +
      ‖secondSpatialCoordinateJet u i k x‖ *
        ‖secondSpatialCoordinateJet u coordinate j x‖ *
          ‖thirdSpatialCoordinateJet u i j k x‖ +
      ‖secondSpatialCoordinateJet u j k x‖ *
        ‖secondSpatialCoordinateJet u coordinate i x‖ *
          ‖thirdSpatialCoordinateJet u i j k x‖)

theorem spatialMiddleTriplePopulation_eq_grouped
    (u : InitialVelocity) (i j k : Fin 3) (x : Space) :
    spatialMiddleTriplePopulation u i j k x =
      (‖secondSpatialCoordinateJet u i j x‖ *
          (∑ coordinate : Fin 3, ‖secondSpatialCoordinateJet u coordinate k x‖) +
        ‖secondSpatialCoordinateJet u i k x‖ *
          (∑ coordinate : Fin 3, ‖secondSpatialCoordinateJet u coordinate j x‖) +
        ‖secondSpatialCoordinateJet u j k x‖ *
          (∑ coordinate : Fin 3, ‖secondSpatialCoordinateJet u coordinate i x‖)) *
        ‖thirdSpatialCoordinateJet u i j k x‖ := by
  unfold spatialMiddleTriplePopulation
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [add_mul, add_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]

theorem spatialMiddleTriplePopulation_nonneg
    (u : InitialVelocity) (i j k : Fin 3) (x : Space) :
    0 ≤ spatialMiddleTriplePopulation u i j k x := by
  apply Finset.sum_nonneg
  intro coordinate _hcoordinate
  positivity

theorem spatialMiddleTriplePopulation_continuous
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (i j k : Fin 3) :
    Continuous (spatialMiddleTriplePopulation u i j k) := by
  apply continuous_finset_sum
  intro coordinate _hcoordinate
  have hij := (secondSpatialCoordinateJet_contDiff u hu i j).continuous.norm
  have hik := (secondSpatialCoordinateJet_contDiff u hu i k).continuous.norm
  have hjk := (secondSpatialCoordinateJet_contDiff u hu j k).continuous.norm
  have hck := (secondSpatialCoordinateJet_contDiff u hu coordinate k).continuous.norm
  have hcj := (secondSpatialCoordinateJet_contDiff u hu coordinate j).continuous.norm
  have hci := (secondSpatialCoordinateJet_contDiff u hu coordinate i).continuous.norm
  have hthird := (thirdSpatialCoordinateJet_contDiff u hu i j k).continuous.norm
  exact (((hij.mul hck).mul hthird).add ((hik.mul hcj).mul hthird)).add
    ((hjk.mul hci).mul hthird)

/-- The full nine-term middle norm population for one ordered word is linear in the cube
Jacobian supremum and quadratic in the complete order-three population. -/
theorem integral_spatialMiddleTriplePopulation_le
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (i j k : Fin 3) :
    ∫ x in unitCube, spatialMiddleTriplePopulation u i j k x ≤
      189 * cubeGradientSup u * thirdOrderSquareMass u := by
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  have htermInt : ∀ coordinate : Fin 3,
      IntegrableOn
        (fun x ↦
          ‖secondSpatialCoordinateJet u i j x‖ *
              ‖secondSpatialCoordinateJet u coordinate k x‖ *
                ‖thirdSpatialCoordinateJet u i j k x‖ +
            ‖secondSpatialCoordinateJet u i k x‖ *
              ‖secondSpatialCoordinateJet u coordinate j x‖ *
                ‖thirdSpatialCoordinateJet u i j k x‖ +
            ‖secondSpatialCoordinateJet u j k x‖ *
              ‖secondSpatialCoordinateJet u coordinate i x‖ *
                ‖thirdSpatialCoordinateJet u i j k x‖) unitCube := by
    intro coordinate
    have hcont : Continuous
        (fun x ↦
          ‖secondSpatialCoordinateJet u i j x‖ *
              ‖secondSpatialCoordinateJet u coordinate k x‖ *
                ‖thirdSpatialCoordinateJet u i j k x‖ +
            ‖secondSpatialCoordinateJet u i k x‖ *
              ‖secondSpatialCoordinateJet u coordinate j x‖ *
                ‖thirdSpatialCoordinateJet u i j k x‖ +
            ‖secondSpatialCoordinateJet u j k x‖ *
              ‖secondSpatialCoordinateJet u coordinate i x‖ *
                ‖thirdSpatialCoordinateJet u i j k x‖) := by
      have hij := (secondSpatialCoordinateJet_contDiff u hu i j).continuous.norm
      have hik := (secondSpatialCoordinateJet_contDiff u hu i k).continuous.norm
      have hjk := (secondSpatialCoordinateJet_contDiff u hu j k).continuous.norm
      have hck := (secondSpatialCoordinateJet_contDiff u hu coordinate k).continuous.norm
      have hcj := (secondSpatialCoordinateJet_contDiff u hu coordinate j).continuous.norm
      have hci := (secondSpatialCoordinateJet_contDiff u hu coordinate i).continuous.norm
      have hthird := (thirdSpatialCoordinateJet_contDiff u hu i j k).continuous.norm
      exact (((hij.mul hck).mul hthird).add ((hik.mul hcj).mul hthird)).add
        ((hjk.mul hci).mul hthird)
    exact hcont.continuousOn.integrableOn_compact hcubeCompact
  rw [show (∫ x in unitCube, spatialMiddleTriplePopulation u i j k x) =
      ∑ coordinate : Fin 3,
        ∫ x in unitCube,
          (‖secondSpatialCoordinateJet u i j x‖ *
                ‖secondSpatialCoordinateJet u coordinate k x‖ *
                  ‖thirdSpatialCoordinateJet u i j k x‖ +
            ‖secondSpatialCoordinateJet u i k x‖ *
                ‖secondSpatialCoordinateJet u coordinate j x‖ *
                  ‖thirdSpatialCoordinateJet u i j k x‖ +
            ‖secondSpatialCoordinateJet u j k x‖ *
                ‖secondSpatialCoordinateJet u coordinate i x‖ *
                  ‖thirdSpatialCoordinateJet u i j k x‖) by
    exact integral_finset_sum Finset.univ (fun coordinate _hcoordinate ↦ htermInt coordinate)]
  calc
    _ ≤ ∑ _coordinate : Fin 3,
        (21 * cubeGradientSup u * thirdOrderSquareMass u +
          21 * cubeGradientSup u * thirdOrderSquareMass u +
          21 * cubeGradientSup u * thirdOrderSquareMass u) := by
      apply Finset.sum_le_sum
      intro coordinate _hcoordinate
      have hfirstInt : IntegrableOn
          (fun x ↦ ‖secondSpatialCoordinateJet u i j x‖ *
            ‖secondSpatialCoordinateJet u coordinate k x‖ *
              ‖thirdSpatialCoordinateJet u i j k x‖) unitCube := by
        have hcont := (((secondSpatialCoordinateJet_contDiff u hu i j).continuous.norm.mul
          (secondSpatialCoordinateJet_contDiff u hu coordinate k).continuous.norm).mul
            (thirdSpatialCoordinateJet_contDiff u hu i j k).continuous.norm)
        exact hcont.continuousOn.integrableOn_compact hcubeCompact
      have hsecondInt : IntegrableOn
          (fun x ↦ ‖secondSpatialCoordinateJet u i k x‖ *
            ‖secondSpatialCoordinateJet u coordinate j x‖ *
              ‖thirdSpatialCoordinateJet u i j k x‖) unitCube := by
        have hcont := (((secondSpatialCoordinateJet_contDiff u hu i k).continuous.norm.mul
          (secondSpatialCoordinateJet_contDiff u hu coordinate j).continuous.norm).mul
            (thirdSpatialCoordinateJet_contDiff u hu i j k).continuous.norm)
        exact hcont.continuousOn.integrableOn_compact hcubeCompact
      have hthirdInt : IntegrableOn
          (fun x ↦ ‖secondSpatialCoordinateJet u j k x‖ *
            ‖secondSpatialCoordinateJet u coordinate i x‖ *
              ‖thirdSpatialCoordinateJet u i j k x‖) unitCube := by
        have hcont := (((secondSpatialCoordinateJet_contDiff u hu j k).continuous.norm.mul
          (secondSpatialCoordinateJet_contDiff u hu coordinate i).continuous.norm).mul
            (thirdSpatialCoordinateJet_contDiff u hu i j k).continuous.norm)
        exact hcont.continuousOn.integrableOn_compact hcubeCompact
      have hsplit :
          (∫ x in unitCube,
            (‖secondSpatialCoordinateJet u i j x‖ *
                ‖secondSpatialCoordinateJet u coordinate k x‖ *
                  ‖thirdSpatialCoordinateJet u i j k x‖ +
              ‖secondSpatialCoordinateJet u i k x‖ *
                ‖secondSpatialCoordinateJet u coordinate j x‖ *
                  ‖thirdSpatialCoordinateJet u i j k x‖) +
              ‖secondSpatialCoordinateJet u j k x‖ *
                ‖secondSpatialCoordinateJet u coordinate i x‖ *
                  ‖thirdSpatialCoordinateJet u i j k x‖) =
            ((∫ x in unitCube,
              ‖secondSpatialCoordinateJet u i j x‖ *
                ‖secondSpatialCoordinateJet u coordinate k x‖ *
                  ‖thirdSpatialCoordinateJet u i j k x‖) +
            (∫ x in unitCube,
              ‖secondSpatialCoordinateJet u i k x‖ *
                ‖secondSpatialCoordinateJet u coordinate j x‖ *
                  ‖thirdSpatialCoordinateJet u i j k x‖)) +
            ∫ x in unitCube,
              ‖secondSpatialCoordinateJet u j k x‖ *
                ‖secondSpatialCoordinateJet u coordinate i x‖ *
                  ‖thirdSpatialCoordinateJet u i j k x‖ := by
        calc
          _ =
              (∫ x in unitCube,
                ‖secondSpatialCoordinateJet u i j x‖ *
                    ‖secondSpatialCoordinateJet u coordinate k x‖ *
                      ‖thirdSpatialCoordinateJet u i j k x‖ +
                  ‖secondSpatialCoordinateJet u i k x‖ *
                    ‖secondSpatialCoordinateJet u coordinate j x‖ *
                      ‖thirdSpatialCoordinateJet u i j k x‖) +
                ∫ x in unitCube,
                  ‖secondSpatialCoordinateJet u j k x‖ *
                    ‖secondSpatialCoordinateJet u coordinate i x‖ *
                      ‖thirdSpatialCoordinateJet u i j k x‖ :=
            integral_add (hfirstInt.add hsecondInt) hthirdInt
          _ = _ := by rw [integral_add hfirstInt hsecondInt]
      rw [hsplit]
      exact add_le_add
        (add_le_add
          (integral_norm_second_mul_norm_second_mul_norm_third_le_orderMass
            u hu hperiodic i j coordinate k i j k)
          (integral_norm_second_mul_norm_second_mul_norm_third_le_orderMass
            u hu hperiodic i k coordinate j i j k))
        (integral_norm_second_mul_norm_second_mul_norm_third_le_orderMass
          u hu hperiodic j k coordinate i i j k)
    _ = 189 * cubeGradientSup u * thirdOrderSquareMass u := by
      simp
      ring

/-! ## Return to the actual open-lifespan solution -/

/-- Every fixed-time coordinate jet is globally smooth in space at an admitted interior
occurrence. -/
theorem openPeriodicSolutionOn_coordinateJetSlice_contDiff
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (n : ℕ) (word : Fin n → Fin 3) :
    ContDiff ℝ ∞ (fun x ↦ coordinateJet velocity n word x t) := by
  have hfield := openPeriodicSolutionOn_coordinateJetField_contDiffOn solution n word
  rw [contDiff_iff_contDiffAt]
  intro x
  have hdomain :
      Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T ∈
        nhds (x, t) :=
    prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht.1 ht.2)
  have hjoint : ContDiffAt ℝ ∞
      (Function.uncurry (coordinateJetField velocity n word)) (x, t) :=
    hfield.contDiffAt hdomain
  simpa [coordinateJetField, Function.comp_def] using
    hjoint.comp x (contDiffAt_id.prodMk contDiffAt_const)

/-- The existing pointwise middle estimate, rebased onto the actual spatial slice, is exactly
bounded by the nine-term spatial population. -/
theorem openPeriodicSolutionOn_abs_inner_middle_le_spatialPopulation
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (i j k : Fin 3) :
    |inner ℝ (thirdCoordinateMiddleCommutator velocity t i j k x)
        (thirdCoordinateJet velocity i j k x t)| ≤
      spatialMiddleTriplePopulation (fun y ↦ velocity y t) i j k x := by
  have hpoint := openPeriodicSolutionOn_abs_inner_thirdCoordinateMiddleCommutator_le
    solution ht x i j k
  simp_rw [openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
    solution ht x] at hpoint
  rw [openPeriodicSolutionOn_thirdCoordinateJet_eq_thirdSpatialCoordinateJet
    solution ht x i j k] at hpoint
  rw [openPeriodicSolutionOn_thirdCoordinateJet_eq_thirdSpatialCoordinateJet
    solution ht x i j k]
  rw [spatialMiddleTriplePopulation_eq_grouped]
  exact hpoint

/-- The paired middle commutator integrand is continuous on the actual slice. -/
theorem openPeriodicSolutionOn_middlePairing_continuous
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (i j k : Fin 3) :
    Continuous (fun x ↦
      inner ℝ (thirdCoordinateMiddleCommutator velocity t i j k x)
        (thirdCoordinateJet velocity i j k x t)) := by
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
      fderiv ℝ (fun y ↦ firstCoordinateJet velocity k y t) x
        (secondCoordinateJet velocity i j x t)) :=
    ((hfirstK.fderiv_right (by simp)).clm_apply hsecondIJ).continuous
  have hB : Continuous (fun x ↦
      fderiv ℝ (fun y ↦ firstCoordinateJet velocity j y t) x
        (secondCoordinateJet velocity i k x t)) :=
    ((hfirstJ.fderiv_right (by simp)).clm_apply hsecondIK).continuous
  have hC : Continuous (fun x ↦
      fderiv ℝ (fun y ↦ firstCoordinateJet velocity i y t) x
        (secondCoordinateJet velocity j k x t)) :=
    ((hfirstI.fderiv_right (by simp)).clm_apply hsecondJK).continuous
  exact ((hA.add hB).add hC).inner hthird.continuous

/-- **The three middle faces are closed for one actual ordered third word.**  The coefficient is
linear in the genuine cube Jacobian supremum and the receiver is the complete ordered third-word
quadratic population. -/
theorem openPeriodicSolutionOn_abs_integral_thirdCoordinateMiddleCommutator_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (i j k : Fin 3) :
    |∫ x in unitCube,
        inner ℝ (thirdCoordinateMiddleCommutator velocity t i j k x)
          (thirdCoordinateJet velocity i j k x t)| ≤
      189 * cubeGradientSup (fun y ↦ velocity y t) *
        thirdOrderSquareMass (fun y ↦ velocity y t) := by
  let u : InitialVelocity := fun y ↦ velocity y t
  have hu : ContDiff ℝ ∞ u := openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hperiodic : IsOnePeriodic u :=
    solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  have hpairingContinuous := openPeriodicSolutionOn_middlePairing_continuous solution ht i j k
  have habsInt : IntegrableOn (fun x ↦
      |inner ℝ (thirdCoordinateMiddleCommutator velocity t i j k x)
        (thirdCoordinateJet velocity i j k x t)|) unitCube :=
    hpairingContinuous.abs.continuousOn.integrableOn_compact hcubeCompact
  have hpopulationInt : IntegrableOn
      (spatialMiddleTriplePopulation u i j k) unitCube :=
    (spatialMiddleTriplePopulation_continuous u hu i j k).continuousOn.integrableOn_compact
      hcubeCompact
  calc
    |∫ x in unitCube,
        inner ℝ (thirdCoordinateMiddleCommutator velocity t i j k x)
          (thirdCoordinateJet velocity i j k x t)| ≤
        ∫ x in unitCube,
          |inner ℝ (thirdCoordinateMiddleCommutator velocity t i j k x)
            (thirdCoordinateJet velocity i j k x t)| := abs_integral_le_integral_abs
    _ ≤ ∫ x in unitCube, spatialMiddleTriplePopulation u i j k x :=
      setIntegral_mono_on habsInt hpopulationInt hcubeCompact.measurableSet
        (fun x hx ↦ openPeriodicSolutionOn_abs_inner_middle_le_spatialPopulation
          solution ht x i j k)
    _ ≤ 189 * cubeGradientSup u * thirdOrderSquareMass u :=
      integral_spatialMiddleTriplePopulation_le u hu hperiodic i j k

/-! ## The complete twenty-seven-word middle return -/

/-- All three middle faces over the complete ordered third-word population. -/
def coordinateH3OrderMiddleWork (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ word : Fin 3 → Fin 3,
    ∫ x in unitCube,
      inner ℝ
        (thirdCoordinateMiddleCommutator velocity t (word 0) (word 1) (word 2) x)
        (thirdCoordinateJet velocity (word 0) (word 1) (word 2) x t)

/-- The order-three slice of the existing coordinate `H³` energy. -/
def coordinateH3OrderEnergy (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ word : Fin 3 → Fin 3,
    periodicKineticEnergy (coordinateJetField velocity 3 word) t

/-- On an admitted solution slice, the spatial third-word square population is exactly twice the
existing kinetic-energy normalization of the order-three coordinate slice. -/
theorem openPeriodicSolutionOn_thirdOrderSquareMass_eq_two_mul_orderEnergy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    thirdOrderSquareMass (fun y ↦ velocity y t) =
      2 * coordinateH3OrderEnergy velocity t := by
  let u : InitialVelocity := fun y ↦ velocity y t
  have hu : ContDiff ℝ ∞ u := openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hword : ∀ word : Fin 3 → Fin 3,
      thirdWordSquareMass u (word 0) (word 1) (word 2) =
        2 * periodicKineticEnergy (coordinateJetField velocity 3 word) t := by
    intro word
    have hwordEq : word = thirdCoordinateWord (word 0) (word 1) (word 2) := by
      funext q
      fin_cases q <;> rfl
    have hjet : ∀ x : Space,
        coordinateJet velocity 3 word x t =
          thirdSpatialCoordinateJet u (word 0) (word 1) (word 2) x :=
      fun x ↦ by
        rw [hwordEq]
        exact openPeriodicSolutionOn_thirdCoordinateJet_eq_thirdSpatialCoordinateJet
          solution ht x (word 0) (word 1) (word 2)
    rw [← integral_norm_thirdSpatialCoordinateJet_sq_eq_mass
      u hu (word 0) (word 1) (word 2)]
    unfold periodicKineticEnergy kineticEnergyDensity coordinateJetField
    have hcubeCompact : IsCompact unitCube := by
      unfold unitCube
      exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc
    have hnormInt : IntegrableOn
        (fun x ↦ ‖coordinateJet velocity 3 word x t‖ ^ 2)
        unitCube := by
      have hthird := openPeriodicSolutionOn_coordinateJetSlice_contDiff solution ht 3 word
      exact ((hthird.continuous.norm.pow 2).continuousOn).integrableOn_compact hcubeCompact
    calc
      ∫ x in unitCube,
          ‖thirdSpatialCoordinateJet u (word 0) (word 1) (word 2) x‖ ^ 2 =
        ∫ x in unitCube,
          ‖coordinateJet velocity 3 word x t‖ ^ 2 := by
        apply setIntegral_congr_fun hcubeCompact.measurableSet
        intro x _hx
        exact congrArg (fun r : ℝ ↦ r ^ 2) (congrArg norm (hjet x).symm)
      _ = 2 *
          ∫ x in unitCube,
            (1 / 2 : ℝ) *
              ‖coordinateJet velocity 3 word x t‖ ^ 2 := by
        rw [integral_const_mul]
        ring
  unfold thirdOrderSquareMass coordinateH3OrderEnergy
  calc
    ∑ word : Fin 3 → Fin 3,
        thirdWordSquareMass u (word 0) (word 1) (word 2) =
      ∑ word : Fin 3 → Fin 3,
        2 * periodicKineticEnergy (coordinateJetField velocity 3 word) t := by
      apply Finset.sum_congr rfl
      intro word _hword
      exact hword word
    _ = 2 * ∑ word : Fin 3 → Fin 3,
        periodicKineticEnergy (coordinateJetField velocity 3 word) t := by
      rw [Finset.mul_sum]

/-- **The complete middle hexagonal population is closed.**  Its finite constant is the exact
`27 * 189 = 5103` returned by summing the per-word estimate; no hidden supremum or interpolation
premise remains. -/
theorem openPeriodicSolutionOn_abs_coordinateH3OrderMiddleWork_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    |coordinateH3OrderMiddleWork velocity t| ≤
      5103 * cubeGradientSup (fun y ↦ velocity y t) *
        thirdOrderSquareMass (fun y ↦ velocity y t) := by
  unfold coordinateH3OrderMiddleWork
  calc
    |∑ word : Fin 3 → Fin 3,
        ∫ x in unitCube,
          inner ℝ
            (thirdCoordinateMiddleCommutator velocity t
              (word 0) (word 1) (word 2) x)
            (thirdCoordinateJet velocity (word 0) (word 1) (word 2) x t)| ≤
      ∑ word : Fin 3 → Fin 3,
        |∫ x in unitCube,
          inner ℝ
            (thirdCoordinateMiddleCommutator velocity t
              (word 0) (word 1) (word 2) x)
            (thirdCoordinateJet velocity (word 0) (word 1) (word 2) x t)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _word : Fin 3 → Fin 3,
        (189 * cubeGradientSup (fun y ↦ velocity y t) *
          thirdOrderSquareMass (fun y ↦ velocity y t)) := by
      apply Finset.sum_le_sum
      intro word _hword
      exact openPeriodicSolutionOn_abs_integral_thirdCoordinateMiddleCommutator_le
        solution ht (word 0) (word 1) (word 2)
    _ = 5103 * cubeGradientSup (fun y ↦ velocity y t) *
        thirdOrderSquareMass (fun y ↦ velocity y t) := by
      norm_num
      ring

/-- The same complete middle estimate expressed in the existing half-square order-three energy
normalization. -/
theorem openPeriodicSolutionOn_abs_coordinateH3OrderMiddleWork_le_orderEnergy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    |coordinateH3OrderMiddleWork velocity t| ≤
      10206 * cubeGradientSup (fun y ↦ velocity y t) *
        coordinateH3OrderEnergy velocity t := by
  have hmiddle := openPeriodicSolutionOn_abs_coordinateH3OrderMiddleWork_le solution ht
  rw [openPeriodicSolutionOn_thirdOrderSquareMass_eq_two_mul_orderEnergy solution ht] at hmiddle
  convert hmiddle using 1
  ring

/-! ## Kernel audit -/

#print axioms mul_three_le_fourth_div_add_fourth_div_add_half_sq
#print axioms integral_norm_mul_norm_mul_norm_le_seven_mul
#print axioms thirdWordSquareMass_nonneg
#print axioms integral_norm_thirdSpatialCoordinateJet_sq_eq_mass
#print axioms integral_norm_second_mul_norm_second_mul_norm_third_le
#print axioms thirdOrderSquareMass_nonneg
#print axioms thirdWordSquareMass_le_thirdOrderSquareMass
#print axioms integral_norm_second_mul_norm_second_mul_norm_third_le_orderMass
#print axioms spatialMiddleTriplePopulation_eq_grouped
#print axioms integral_spatialMiddleTriplePopulation_le
#print axioms openPeriodicSolutionOn_coordinateJetSlice_contDiff
#print axioms openPeriodicSolutionOn_abs_inner_middle_le_spatialPopulation
#print axioms openPeriodicSolutionOn_middlePairing_continuous
#print axioms openPeriodicSolutionOn_abs_integral_thirdCoordinateMiddleCommutator_le
#print axioms openPeriodicSolutionOn_thirdOrderSquareMass_eq_two_mul_orderEnergy
#print axioms openPeriodicSolutionOn_abs_coordinateH3OrderMiddleWork_le
#print axioms openPeriodicSolutionOn_abs_coordinateH3OrderMiddleWork_le_orderEnergy

end Soma.Holonics.Millennium.NavierStokesCoordinateH3MiddleRedistribution
