import ElementaryHolonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
import ElementaryHolonics.Millennium.NavierStokesProjectedDyadicShellEvolution

/-!
# Pair-compatible cofinal apertures and projected-source convergence

**[proved-derived; formal-checked]**  For every output frequency `k`, the aperture

`A_R(k) = cube_R ∪ (k - cube_R)`

is finite, invariant under the exchange `p ↦ k - p`, monotone in `R`, and cofinal in the
complete integer-frequency population.  The existing absolute `H³` coefficient summability then
makes the finite velocity-advection population converge coefficientwise to the complete native
`H³` convolution.  Exact pair symmetry identifies its curl with the signed finite
`stretching - transport` population.  Consequently the projected finite source converges to the
actual projected vorticity source and the explicit reconstruction residual tends to zero.

No terminal-time uniformity, scale summability, or critical absorption estimate is asserted.
-/

noncomputable section

open Set Filter Topology
open scoped BigOperators ENNReal NNReal lp

namespace Soma.Holonics.Millennium.NavierStokesPairCompatibleApertureConvergence

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesProjectedDyadicShellEvolution
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## A finite reflection-closed cofinal aperture -/

/-- The radius-`R` cube together with every exchanged partner `k - p`. -/
def pairCompatibleFrequencyAperture
    (k : SpatialFrequency) (radius : ℕ) : Finset SpatialFrequency :=
  pairedFrequencyAperture k (frequencyCube radius)

/-- Every aperture in the family is closed under the interaction exchange `p ↦ k - p`. -/
theorem pairCompatibleFrequencyAperture_isTransportPaired
    (k : SpatialFrequency) (radius : ℕ) :
    IsTransportPairedAperture k (pairCompatibleFrequencyAperture k radius) :=
  pairedFrequencyAperture_isTransportPaired k (frequencyCube radius)

/-- Enlarging the radius retains every previously admitted interaction pin. -/
theorem pairCompatibleFrequencyAperture_mono
    (k : SpatialFrequency) : Monotone (pairCompatibleFrequencyAperture k) := by
  intro inner outer hinner
  unfold pairCompatibleFrequencyAperture pairedFrequencyAperture
  apply Finset.union_subset_union
  · exact frequencyCube_mono hinner
  · exact Finset.image_subset_image (frequencyCube_mono hinner)

/-- Every lattice frequency enters some centered finite cube. -/
theorem exists_mem_frequencyCube (p : SpatialFrequency) :
    ∃ radius : ℕ, p ∈ frequencyCube radius := by
  let radius : ℕ := ∑ coordinate : Fin 3, (p coordinate).natAbs
  refine ⟨radius, ?_⟩
  rw [mem_frequencyCube_iff]
  intro coordinate
  have hcoordinate : (p coordinate).natAbs ≤ radius := by
    unfold radius
    exact Finset.single_le_sum
      (f := fun axis ↦ (p axis).natAbs)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ coordinate)
  have habs : |p coordinate| ≤ (radius : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hcoordinate
  exact abs_le.mp habs

/-- Hence every advecting pin enters the pair-compatible aperture family. -/
theorem exists_mem_pairCompatibleFrequencyAperture
    (k p : SpatialFrequency) :
    ∃ radius : ℕ, p ∈ pairCompatibleFrequencyAperture k radius := by
  obtain ⟨radius, hp⟩ := exists_mem_frequencyCube p
  exact ⟨radius, subset_pairedFrequencyAperture k (frequencyCube radius) hp⟩

/-- The `k`-dependent finite apertures are genuinely cofinal in the directed finite-population
filter, not merely pointwise exhaustive. -/
theorem tendsto_pairCompatibleFrequencyAperture_atTop
    (k : SpatialFrequency) :
    Tendsto (pairCompatibleFrequencyAperture k) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro population
  obtain ⟨radius, hradius⟩ :
      ∃ radius : ℕ, population ⊆ pairCompatibleFrequencyAperture k radius := by
    classical
    induction population using Finset.induction_on with
    | empty => exact ⟨0, Finset.empty_subset _⟩
    | @insert p population hp ih =>
        obtain ⟨populationRadius, hpopulation⟩ := ih
        obtain ⟨pinRadius, hpin⟩ :=
          exists_mem_pairCompatibleFrequencyAperture k p
        refine ⟨max populationRadius pinRadius, ?_⟩
        intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hq
        · exact (pairCompatibleFrequencyAperture_mono k
            (Nat.le_max_right _ _)) hpin
        · exact (pairCompatibleFrequencyAperture_mono k
            (Nat.le_max_left _ _)) (hpopulation hq)
  exact Filter.eventually_atTop.2 ⟨radius, fun later hlater ↦
    hradius.trans (pairCompatibleFrequencyAperture_mono k hlater)⟩

/-- Every absolutely summable population is reconstructed along the pair-compatible aperture
family. -/
theorem tendsto_sum_pairCompatibleFrequencyAperture
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (k : SpatialFrequency) {population : SpatialFrequency → E}
    (hsummable : Summable population) :
    Tendsto
      (fun radius : ℕ ↦
        ∑ p ∈ pairCompatibleFrequencyAperture k radius, population p)
      atTop (nhds (∑' p, population p)) := by
  exact hsummable.hasSum.comp (tendsto_pairCompatibleFrequencyAperture_atTop k)

/-! ## Absolute convergence of the actual advective population -/

/-- One ordered advective interaction component is the finite sum of the same differentiated
scalar convolution terms used by the complete native `H³` owner. -/
private theorem complexAdvectiveInteraction_apply_eq_sum
    (p q : SpatialFrequency) (advecting transported : ComplexVector)
    (output : Fin 3) :
    complexAdvectiveInteraction p q advecting transported output =
      ∑ coordinate : Fin 3,
        advecting coordinate *
          ((2 * (Real.pi : ℂ) * Complex.I * (q coordinate : ℂ)) *
            transported output) := by
  simp only [complexAdvectiveInteraction, complexDot, dotProduct,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  simp only [complexFrequencyVector]
  ring

/-- Each coordinate contribution to an actual fixed-output advective interaction is absolutely
summable on the complete frequency population. -/
private theorem summable_openAdvectiveCoordinateTerm
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) (output coordinate : Fin 3) :
    Summable fun p : SpatialFrequency ↦
      openPeriodicVelocityFourierMode solution t p coordinate *
        ((2 * (Real.pi : ℂ) * Complex.I *
            ((k - p) coordinate : ℂ)) *
          openPeriodicVelocityFourierMode solution t (k - p) output) := by
  let state : PeriodicVectorSobolevThree := openVelocityH3State solution t
  have habsolute :=
    periodicVectorSobolevThree_hasAbsolutelySummableComponents state
  have hstate : Summable fun p : SpatialFrequency ↦
        (state coordinate).1 p *
          ((2 * (Real.pi : ℂ) * Complex.I *
              ((k - p) coordinate : ℂ)) *
            (state output).1 (k - p)) := by
    apply Summable.of_norm
    have hbound : Summable fun p : SpatialFrequency ↦
        ‖(state coordinate).1 p‖ *
          ‖periodicSobolevThreeDerivative coordinate (state output)‖ :=
      (habsolute coordinate).mul_right _
    refine Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _) (fun p ↦ ?_) hbound
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [periodicSobolevThreeDerivative_apply] using
      (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (periodicSobolevThreeDerivative coordinate (state output)) (k - p))
  apply hstate.congr
  intro p
  rw [openVelocityH3State_mode_eq_openPeriodicVelocityFourierMode
    solution t coordinate p]
  rw [openVelocityH3State_mode_eq_openPeriodicVelocityFourierMode
    solution t output (k - p)]

/-- The complete actual advective interaction fibre is absolutely summable at every fixed
output coefficient and vector component. -/
private theorem summable_openAdvectiveInteraction_component
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) (output : Fin 3) :
    Summable fun p : SpatialFrequency ↦
      complexAdvectiveInteraction p (transportedFrequencyAt k p)
        (openPeriodicVelocityFourierMode solution t p)
        (openPeriodicVelocityFourierMode solution t
          (transportedFrequencyAt k p)) output := by
  have hsum : Summable fun p : SpatialFrequency ↦
      ∑ coordinate : Fin 3,
        openPeriodicVelocityFourierMode solution t p coordinate *
          ((2 * (Real.pi : ℂ) * Complex.I *
              ((k - p) coordinate : ℂ)) *
            openPeriodicVelocityFourierMode solution t (k - p) output) := by
    apply summable_sum
    intro coordinate _hcoordinate
    exact summable_openAdvectiveCoordinateTerm solution t k output coordinate
  apply hsum.congr
  intro p
  rw [complexAdvectiveInteraction_apply_eq_sum]
  rfl

/-! ## Cofinal projected-source and residual convergence -/

/-- The finite actual velocity-advection coefficient converges to the complete native `H³`
convolution coefficient along the pair-compatible apertures. -/
theorem tendsto_finiteOpenAdvectiveCoefficient_pairCompatible
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    Tendsto
      (fun radius : ℕ ↦
        finiteAdvectiveCoefficient (pairCompatibleFrequencyAperture k radius)
          (openPeriodicVelocityFourierMode solution t)
          (openPeriodicVelocityFourierMode solution t) k)
      atTop
      (nhds (vectorCoefficientAt
        (h3AdvectiveConvolution (openVelocityH3State solution t)
          (openVelocityH3State solution t)) k)) := by
  apply tendsto_pi_nhds.2
  intro output
  have hsum := tendsto_sum_pairCompatibleFrequencyAperture k
    (summable_openAdvectiveInteraction_component solution t k output)
  have habsolute := periodicVectorSobolevThree_hasAbsolutelySummableComponents
    (openVelocityH3State solution t)
  change Tendsto
    (fun radius : ℕ ↦
      finiteAdvectiveCoefficient (pairCompatibleFrequencyAperture k radius)
        (openPeriodicVelocityFourierMode solution t)
        (openPeriodicVelocityFourierMode solution t) k output)
    atTop
    (nhds (h3AdvectiveConvolution (openVelocityH3State solution t)
      (openVelocityH3State solution t) output k))
  rw [h3AdvectiveConvolution_apply habsolute]
  have hcoordinate : ∀ coordinate ∈ (Finset.univ : Finset (Fin 3)),
      Summable fun p : SpatialFrequency ↦
        openPeriodicVelocityFourierMode solution t p coordinate *
          ((2 * (Real.pi : ℂ) * Complex.I *
              ((k - p) coordinate : ℂ)) *
            openPeriodicVelocityFourierMode solution t (k - p) output) := by
    intro coordinate _hcoordinate
    exact summable_openAdvectiveCoordinateTerm solution t k output coordinate
  simp_rw [openVelocityH3State_mode_eq_openPeriodicVelocityFourierMode]
  simpa only [finiteAdvectiveCoefficient, Finset.sum_apply,
    vectorCoefficientAt, transportedFrequencyAt,
    complexAdvectiveInteraction_apply_eq_sum,
    ← Summable.tsum_finsetSum hcoordinate] using hsum

/-- Curling the preceding cofinal limit reaches the actual nonlinear vorticity mode. -/
theorem tendsto_finiteOpenVorticityNonlinearCoefficient_pairCompatible
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    Tendsto
      (fun radius : ℕ ↦
        finiteOpenVorticityNonlinearCoefficient solution t
          (pairCompatibleFrequencyAperture k radius) k)
      atTop (nhds (vorticityNonlinearMode solution t k)) := by
  have hadvection :=
    tendsto_finiteOpenAdvectiveCoefficient_pairCompatible solution t k
  have hcurl :=
    ((frequencyCurlMultiplierCLM k).continuous.continuousAt.tendsto.comp hadvection).neg
  rw [vorticityNonlinearMode_eq_completeActualAdvectionConvolution solution t k]
  simpa only [finiteOpenVorticityNonlinearCoefficient,
    Function.comp_apply, frequencyCurlMultiplierCLM_apply] using hcurl

/-- On a pair-compatible aperture, the signed finite `stretching - transport` population is
literally the direct multiplier projection of the finite curl source. -/
theorem finiteOpenProjectedVorticityNonlinearCoefficient_pairCompatible_eq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale radius : ℕ) (k : SpatialFrequency) :
    finiteOpenProjectedVorticityNonlinearCoefficient solution t scale
        (pairCompatibleFrequencyAperture k radius) k =
      (dyadicHodgeBandWeight scale k : ℂ) •
        finiteOpenVorticityNonlinearCoefficient solution t
          (pairCompatibleFrequencyAperture k radius) k := by
  rw [finiteOpenVorticityNonlinearCoefficient_eq_stretching_sub_transport
    solution t (pairCompatibleFrequencyAperture k radius) k
      (pairCompatibleFrequencyAperture_isTransportPaired k radius)]
  unfold finiteOpenProjectedVorticityNonlinearCoefficient
  simp only [sub_eq_add_neg, smul_add, smul_neg]
  abel

/-- The finite signed projected source converges to the actual projected nonlinear source. -/
theorem tendsto_finiteOpenProjectedVorticityNonlinearCoefficient_pairCompatible
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (k : SpatialFrequency) :
    Tendsto
      (fun radius : ℕ ↦
        finiteOpenProjectedVorticityNonlinearCoefficient solution t scale
          (pairCompatibleFrequencyAperture k radius) k)
      atTop
      (nhds ((dyadicHodgeBandWeight scale k : ℂ) •
        vorticityNonlinearMode solution t k)) := by
  have hlimit :=
    (tendsto_finiteOpenVorticityNonlinearCoefficient_pairCompatible
      solution t k).const_smul (dyadicHodgeBandWeight scale k : ℂ)
  simpa only [finiteOpenProjectedVorticityNonlinearCoefficient_pairCompatible_eq]
    using hlimit

/-- The explicit source reconstruction fibre vanishes along the genuinely cofinal,
pair-compatible aperture family. -/
theorem tendsto_finiteOpenProjectedVorticitySourceResidual_pairCompatible
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (k : SpatialFrequency) :
    Tendsto
      (fun radius : ℕ ↦
        finiteOpenProjectedVorticitySourceResidual solution t scale
          (pairCompatibleFrequencyAperture k radius) k)
      atTop (nhds 0) := by
  have hlimit : Tendsto
      (fun radius : ℕ ↦
        (dyadicHodgeBandWeight scale k : ℂ) •
            vorticityNonlinearMode solution t k -
          finiteOpenProjectedVorticityNonlinearCoefficient solution t scale
            (pairCompatibleFrequencyAperture k radius) k)
      atTop
      (nhds (((dyadicHodgeBandWeight scale k : ℂ) •
        vorticityNonlinearMode solution t k) -
          (dyadicHodgeBandWeight scale k : ℂ) •
            vorticityNonlinearMode solution t k)) :=
    tendsto_const_nhds.sub
      (tendsto_finiteOpenProjectedVorticityNonlinearCoefficient_pairCompatible
        solution t scale k)
  simpa only [finiteOpenProjectedVorticitySourceResidual, sub_self] using hlimit

section Audit

#print axioms pairCompatibleFrequencyAperture_isTransportPaired
#print axioms tendsto_pairCompatibleFrequencyAperture_atTop
#print axioms tendsto_finiteOpenAdvectiveCoefficient_pairCompatible
#print axioms tendsto_finiteOpenVorticityNonlinearCoefficient_pairCompatible
#print axioms finiteOpenProjectedVorticityNonlinearCoefficient_pairCompatible_eq
#print axioms tendsto_finiteOpenProjectedVorticityNonlinearCoefficient_pairCompatible
#print axioms tendsto_finiteOpenProjectedVorticitySourceResidual_pairCompatible

end Audit

end Soma.Holonics.Millennium.NavierStokesPairCompatibleApertureConvergence
