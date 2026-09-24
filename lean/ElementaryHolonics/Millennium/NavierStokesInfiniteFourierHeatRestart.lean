import ElementaryHolonics.Millennium.NavierStokesInfiniteFourierHeatH3
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Infinite Fourier heat restart on the periodic `H³` carrier

The predecessor supplied the genuine infinite Fourier Hilbert carrier and its positive-time
`L² → H³` squeeze.  This successor restricts the same diagonal passage to data already in the
weighted `H³` carrier.  It proves exact weighted-energy contraction, packages three components
without truncating the frequency population, and retains the exact semigroup law.

It also proves strong continuity at time zero on the complete Fourier `ℓ²` carrier by dominated
convergence over the entire frequency lattice.  No finite cutoff, heat-generator identity,
nonlinear fixed point, mild Navier--Stokes solution, or local-existence assertion is used.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open Filter Topology

namespace Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3

/-! ## The diagonal action restricted to the weighted `H³` carrier -/

/-- [proved-derived] The heat multiplier contracts each squared Fourier coefficient. -/
theorem norm_infiniteHeatCoefficientEvolution_apply_sq_le
    (nu t : ℝ≥0) (coeff : PeriodicFourierL2) (k : SpatialFrequency) :
    ‖infiniteHeatCoefficientEvolution nu t coeff k‖ ^ 2 ≤ ‖coeff k‖ ^ 2 := by
  obtain ⟨hm0, hm1⟩ := heatStokesMultiplier_mem_unitInterval
    nu.coe_nonneg t.coe_nonneg k
  have hmSq :
      heatStokesMultiplier (nu : ℝ) (t : ℝ) k *
          heatStokesMultiplier (nu : ℝ) (t : ℝ) k ≤ 1 := by
    nlinarith
  simp only [infiniteHeatCoefficientEvolution_apply, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm0, pow_two]
  calc
    (heatStokesMultiplier (nu : ℝ) (t : ℝ) k * ‖coeff k‖) *
        (heatStokesMultiplier (nu : ℝ) (t : ℝ) k * ‖coeff k‖) =
        (heatStokesMultiplier (nu : ℝ) (t : ℝ) k *
          heatStokesMultiplier (nu : ℝ) (t : ℝ) k) *
            (‖coeff k‖ * ‖coeff k‖) := by ring
    _ ≤ 1 * (‖coeff k‖ * ‖coeff k‖) :=
      mul_le_mul_of_nonneg_right hmSq (mul_self_nonneg _)
    _ = ‖coeff k‖ * ‖coeff k‖ := one_mul _

/-- [definition] The same infinite diagonal heat action, now returned inside the honest
weighted `H³` coefficient carrier. -/
def infiniteHeatPeriodicSobolevThreeEvolution
    (nu t : ℝ≥0) (coeff : PeriodicSobolevCoefficients 3) :
    PeriodicSobolevCoefficients 3 :=
  ⟨infiniteHeatCoefficientEvolution nu t coeff.1, by
    unfold HasPeriodicSobolevCoefficients
    refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_) coeff.2
    · exact mul_nonneg (periodicSobolevWeight_nonneg 3 k) (sq_nonneg _)
    · exact mul_le_mul_of_nonneg_left
        (norm_infiniteHeatCoefficientEvolution_apply_sq_le nu t coeff.1 k)
        (periodicSobolevWeight_nonneg 3 k)⟩

/-- [definition] The complete weighted squared `H³` Fourier receiver. -/
def periodicSobolevThreeSquaredEnergy
    (coeff : PeriodicSobolevCoefficients 3) : ℝ :=
  ∑' k, periodicSobolevWeight 3 k * ‖coeff.1 k‖ ^ 2

/-- [proved-derived] Heat is nonexpanding in the complete weighted squared `H³` receiver. -/
theorem periodicSobolevThreeSquaredEnergy_infiniteHeat_le
    (nu t : ℝ≥0) (coeff : PeriodicSobolevCoefficients 3) :
    periodicSobolevThreeSquaredEnergy
        (infiniteHeatPeriodicSobolevThreeEvolution nu t coeff) ≤
      periodicSobolevThreeSquaredEnergy coeff := by
  unfold periodicSobolevThreeSquaredEnergy
  exact (infiniteHeatPeriodicSobolevThreeEvolution nu t coeff).2.tsum_le_tsum
    (fun k ↦
    mul_le_mul_of_nonneg_left
      (norm_infiniteHeatCoefficientEvolution_apply_sq_le nu t coeff.1 k)
      (periodicSobolevWeight_nonneg 3 k)) coeff.2

/-- [proved-derived] The restricted action starts at the identity on the exact subtype. -/
@[simp]
theorem infiniteHeatPeriodicSobolevThreeEvolution_zero_time
    (nu : ℝ≥0) (coeff : PeriodicSobolevCoefficients 3) :
    infiniteHeatPeriodicSobolevThreeEvolution nu 0 coeff = coeff := by
  apply Subtype.ext
  exact infiniteHeatCoefficientEvolution_zero_time nu coeff.1

/-- [proved-derived] The restricted `H³` action retains the exact infinite semigroup law. -/
theorem infiniteHeatPeriodicSobolevThreeEvolution_add
    (nu s t : ℝ≥0) (coeff : PeriodicSobolevCoefficients 3) :
    infiniteHeatPeriodicSobolevThreeEvolution nu (s + t) coeff =
      infiniteHeatPeriodicSobolevThreeEvolution nu s
        (infiniteHeatPeriodicSobolevThreeEvolution nu t coeff) := by
  apply Subtype.ext
  exact infiniteHeatCoefficientEvolution_add nu s t coeff.1

/-! ## Three-component weighted carrier -/

/-- [definition] Three complete weighted `H³` Fourier components. -/
abbrev PeriodicVectorSobolevThree := Fin 3 → PeriodicSobolevCoefficients 3

/-- [definition] Componentwise infinite heat action on the vector `H³` carrier. -/
def infiniteVectorSobolevThreeHeatEvolution
    (nu t : ℝ≥0) (state : PeriodicVectorSobolevThree) :
    PeriodicVectorSobolevThree :=
  fun component ↦ infiniteHeatPeriodicSobolevThreeEvolution nu t (state component)

/-- [proved-derived] Every vector component is exactly the scalar infinite diagonal action. -/
theorem infiniteVectorSobolevThreeHeatEvolution_component
    (nu t : ℝ≥0) (state : PeriodicVectorSobolevThree) (component : Fin 3) :
    (infiniteVectorSobolevThreeHeatEvolution nu t state component).1 =
      infiniteHeatCoefficientEvolution nu t (state component).1 := rfl

/-- [proved-derived] The vector `H³` action starts at the identity. -/
@[simp]
theorem infiniteVectorSobolevThreeHeatEvolution_zero_time
    (nu : ℝ≥0) (state : PeriodicVectorSobolevThree) :
    infiniteVectorSobolevThreeHeatEvolution nu 0 state = state := by
  funext component
  exact infiniteHeatPeriodicSobolevThreeEvolution_zero_time nu (state component)

/-- [proved-derived] Exact semigroup identity on all three complete weighted carriers. -/
theorem infiniteVectorSobolevThreeHeatEvolution_add
    (nu s t : ℝ≥0) (state : PeriodicVectorSobolevThree) :
    infiniteVectorSobolevThreeHeatEvolution nu (s + t) state =
      infiniteVectorSobolevThreeHeatEvolution nu s
        (infiniteVectorSobolevThreeHeatEvolution nu t state) := by
  funext component
  exact infiniteHeatPeriodicSobolevThreeEvolution_add nu s t (state component)

/-- [definition] Forget only the weighted witnesses, retaining every vector coefficient. -/
def periodicVectorSobolevThreeCoefficients
    (state : PeriodicVectorSobolevThree) : PeriodicVectorFourierL2 :=
  fun component ↦ (state component).1

/-- [proved-derived] Forgetting the weighted witnesses commutes exactly with vector heat. -/
theorem periodicVectorSobolevThreeCoefficients_infiniteHeat
    (nu t : ℝ≥0) (state : PeriodicVectorSobolevThree) :
    periodicVectorSobolevThreeCoefficients
        (infiniteVectorSobolevThreeHeatEvolution nu t state) =
      infiniteVectorHeatCoefficientEvolution nu t
        (periodicVectorSobolevThreeCoefficients state) := rfl

/-- [proved-derived] The vector `H³` heat action preserves the complete zero mode. -/
theorem vectorCoefficientAt_zero_infiniteVectorSobolevThreeHeatEvolution
    (nu t : ℝ≥0) (state : PeriodicVectorSobolevThree) :
    vectorCoefficientAt
        (periodicVectorSobolevThreeCoefficients
          (infiniteVectorSobolevThreeHeatEvolution nu t state)) 0 =
      vectorCoefficientAt (periodicVectorSobolevThreeCoefficients state) 0 := by
  rw [periodicVectorSobolevThreeCoefficients_infiniteHeat]
  exact vectorCoefficientAt_zero_infiniteVectorHeatCoefficientEvolution nu t _

/-- [proved-derived] Modewise Fourier divergence constraints survive on the vector `H³`
subtype. -/
theorem infiniteVectorSobolevThreeHeatEvolution_preserves_divergenceFree
    {state : PeriodicVectorSobolevThree}
    (hstate : IsModewiseDivergenceFree
      (periodicVectorSobolevThreeCoefficients state)) (nu t : ℝ≥0) :
    IsModewiseDivergenceFree
      (periodicVectorSobolevThreeCoefficients
        (infiniteVectorSobolevThreeHeatEvolution nu t state)) := by
  rw [periodicVectorSobolevThreeCoefficients_infiniteHeat]
  exact infiniteVectorHeatCoefficientEvolution_preserves_divergenceFree hstate nu t

/-! ## Strong continuity at zero on the complete Fourier Hilbert carrier -/

private theorem norm_infiniteHeatCoefficientEvolution_apply_le
    (nu t : ℝ≥0) (coeff : PeriodicFourierL2) (k : SpatialFrequency) :
    ‖infiniteHeatCoefficientEvolution nu t coeff k‖ ≤ ‖coeff k‖ := by
  have hsquare :=
    norm_infiniteHeatCoefficientEvolution_apply_sq_le nu t coeff k
  nlinarith [norm_nonneg (infiniteHeatCoefficientEvolution nu t coeff k),
    norm_nonneg (coeff k)]

private theorem norm_infiniteHeatCoefficientEvolution_sub_apply_sq_le
    (nu t : ℝ≥0) (coeff : PeriodicFourierL2) (k : SpatialFrequency) :
    ‖infiniteHeatCoefficientEvolution nu t coeff k - coeff k‖ ^ 2 ≤
      4 * ‖coeff k‖ ^ 2 := by
  have hdiff :
      ‖infiniteHeatCoefficientEvolution nu t coeff k - coeff k‖ ≤
        2 * ‖coeff k‖ := by
    calc
      ‖infiniteHeatCoefficientEvolution nu t coeff k - coeff k‖ ≤
          ‖infiniteHeatCoefficientEvolution nu t coeff k‖ + ‖coeff k‖ :=
        norm_sub_le _ _
      _ ≤ ‖coeff k‖ + ‖coeff k‖ :=
        add_le_add
          (norm_infiniteHeatCoefficientEvolution_apply_le nu t coeff k) le_rfl
      _ = 2 * ‖coeff k‖ := by ring
  calc
    ‖infiniteHeatCoefficientEvolution nu t coeff k - coeff k‖ ^ 2 ≤
        (2 * ‖coeff k‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hdiff 2
    _ = 4 * ‖coeff k‖ ^ 2 := by ring

private theorem tendsto_infiniteHeatCoefficientEvolution_apply_zero_time
    (nu : ℝ≥0) (coeff : PeriodicFourierL2) (k : SpatialFrequency) :
    Tendsto (fun t : ℝ≥0 ↦ infiniteHeatCoefficientEvolution nu t coeff k)
      (𝓝 0) (𝓝 (coeff k)) := by
  simp only [infiniteHeatCoefficientEvolution_apply]
  have hcontinuous : ContinuousAt
      (fun t : ℝ≥0 ↦
        (heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) * coeff k) 0 := by
    unfold heatStokesMultiplier
    fun_prop
  have hzero :
      (heatStokesMultiplier (nu : ℝ) (0 : ℝ≥0) k : ℂ) * coeff k = coeff k := by
    simp [heatStokesMultiplier]
  change Tendsto
    (fun t : ℝ≥0 ↦
      (heatStokesMultiplier (nu : ℝ) (t : ℝ) k : ℂ) * coeff k)
    (𝓝 0)
    (𝓝 ((heatStokesMultiplier (nu : ℝ) ((0 : ℝ≥0) : ℝ) k : ℂ) * coeff k))
      at hcontinuous
  rw [hzero] at hcontinuous
  exact hcontinuous

/-- [proved-derived] The genuine infinite diagonal Fourier heat semigroup is strongly continuous
at time zero in `ℓ²`.  The proof sums over every frequency and uses a summable dominator; no finite
mode population appears. -/
theorem tendsto_infiniteHeatCoefficientEvolution_zero_time
    (nu : ℝ≥0) (coeff : PeriodicFourierL2) :
    Tendsto (fun t : ℝ≥0 ↦ infiniteHeatCoefficientEvolution nu t coeff)
      (𝓝 0) (𝓝 coeff) := by
  let differenceSquared : ℝ≥0 → SpatialFrequency → ℝ :=
    fun t k ↦ ‖infiniteHeatCoefficientEvolution nu t coeff k - coeff k‖ ^ 2
  let bound : SpatialFrequency → ℝ := fun k ↦ 4 * ‖coeff k‖ ^ 2
  have hcoeff : Summable (fun k ↦ ‖coeff k‖ ^ 2) := by
    have h := (lp.memℓp coeff).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa using h
  have hbound : Summable bound := by
    exact hcoeff.mul_left 4
  have hpoint : ∀ k,
      Tendsto (differenceSquared · k) (𝓝 0) (𝓝 (0 : ℝ)) := by
    intro k
    have hcoordinate :=
      (tendsto_infiniteHeatCoefficientEvolution_apply_zero_time nu coeff k).sub_const
        (coeff k)
    have hnorm := tendsto_norm.comp hcoordinate
    simpa [differenceSquared] using hnorm.pow 2
  have hdominated : ∀ᶠ t in 𝓝 (0 : ℝ≥0), ∀ k,
      ‖differenceSquared t k‖ ≤ bound k := by
    refine Eventually.of_forall (fun t k ↦ ?_)
    dsimp [differenceSquared, bound]
    rw [abs_of_nonneg (sq_nonneg _)]
    exact norm_infiniteHeatCoefficientEvolution_sub_apply_sq_le nu t coeff k
  have htsum : Tendsto (fun t ↦ ∑' k, differenceSquared t k)
      (𝓝 0) (𝓝 (0 : ℝ)) := by
    have h := tendsto_tsum_of_dominated_convergence
      (f := differenceSquared) (g := fun _ ↦ (0 : ℝ))
      (bound := bound) hbound hpoint hdominated
    simpa using h
  have hnormSquare : Tendsto
      (fun t : ℝ≥0 ↦ ‖infiniteHeatCoefficientEvolution nu t coeff - coeff‖ ^ 2)
      (𝓝 0) (𝓝 (0 : ℝ)) := by
    convert htsum using 1
    · funext t
      have h := lp.norm_rpow_eq_tsum
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
        (infiniteHeatCoefficientEvolution nu t coeff - coeff)
      simpa only [differenceSquared, ENNReal.toReal_ofNat, Real.rpow_two,
        lp.coeFn_sub, Pi.sub_apply] using h
  have hnorm : Tendsto
      (fun t : ℝ≥0 ↦ ‖infiniteHeatCoefficientEvolution nu t coeff - coeff‖)
      (𝓝 0) (𝓝 (0 : ℝ)) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hnormSquare
    change Tendsto
      (fun t : ℝ≥0 ↦ Real.sqrt
        (‖infiniteHeatCoefficientEvolution nu t coeff - coeff‖ ^ 2))
      (𝓝 0) (𝓝 (Real.sqrt 0)) at hsqrt
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  apply tendsto_iff_dist_tendsto_zero.2
  simpa only [dist_eq_norm] using hnorm

/-- [proved-derived] Conjugating by Mathlib's Fourier Hilbert isometry gives strong continuity
at zero on the actual periodic torus `L²` carrier. -/
theorem tendsto_infinitePeriodicHeatEvolution_zero_time
    (nu : ℝ≥0) (field : PeriodicL2) :
    Tendsto (fun t : ℝ≥0 ↦ infinitePeriodicHeatEvolution nu t field)
      (𝓝 0) (𝓝 field) := by
  have hcoeff := tendsto_infiniteHeatCoefficientEvolution_zero_time nu
    (periodicFourierRepresentation field)
  have houter : Tendsto (fun coeff ↦ periodicFourierRepresentation.symm coeff)
      (𝓝 (periodicFourierRepresentation field))
      (𝓝 (periodicFourierRepresentation.symm
        (periodicFourierRepresentation field))) :=
    periodicFourierRepresentation.symm.continuous.tendsto _
  have hreturn := houter.comp hcoeff
  rw [periodicFourierRepresentation.symm_apply_apply] at hreturn
  change Tendsto
    (periodicFourierRepresentation.symm ∘
      (fun t : ℝ≥0 ↦
        infiniteHeatCoefficientEvolution nu t (periodicFourierRepresentation field)))
    (𝓝 0) (𝓝 field)
  exact hreturn

#print axioms periodicSobolevThreeSquaredEnergy_infiniteHeat_le
#print axioms infiniteHeatPeriodicSobolevThreeEvolution_add
#print axioms infiniteVectorSobolevThreeHeatEvolution_add
#print axioms infiniteVectorSobolevThreeHeatEvolution_preserves_divergenceFree
#print axioms tendsto_infiniteHeatCoefficientEvolution_zero_time
#print axioms tendsto_infinitePeriodicHeatEvolution_zero_time

end Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
