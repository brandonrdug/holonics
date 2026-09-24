import ElementaryHolonics.Millennium.NavierStokesSmoothDyadicLinearScaleBoundary
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

/-!
# A depth-uniform receiver for the finite linear dyadic boundary

**[proved-derived; formal-checked]**  The cumulative multiplier left after summing finitely many
positive direct Hodge bands is itself a real multiplier in the unit interval.  Consequently the
complete finite population of ordinary two-copy band energies is bounded, uniformly in the
chosen depth, by the square of the complete actual vorticity coefficient `L¹` receiver on the
same time slice.

This is a genuine depth-uniform scale estimate.  It does not assert terminal-time integrability
of the receiving `L¹` population and therefore does not discharge the Navier--Stokes finish line.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearUniformBoundary

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeBandPositivity
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandIntegratedBalance
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearPhaseBand
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearScaleBoundary
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicTriadFluxCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The cumulative boundary is a positive contraction -/

theorem smoothDyadicCumulativeBoundaryMultiplier_re_eq
    (depth : ℕ) (frequency : SpatialFrequency) :
    (smoothDyadicCumulativeBoundaryMultiplier depth frequency).re =
      tensorValleePoussinWeight (dyadicHodgeParameter depth) frequency -
        tensorValleePoussinWeight (dyadicHodgeParameter 0) frequency := by
  simp [smoothDyadicCumulativeBoundaryMultiplier]

theorem smoothDyadicCumulativeBoundaryMultiplier_re_nonneg
    (depth : ℕ) (frequency : SpatialFrequency) :
    0 ≤ (smoothDyadicCumulativeBoundaryMultiplier depth frequency).re := by
  have htelescoping :=
    sum_complex_dyadicHodgeBandWeight_eq_lowPass_boundary depth frequency
  have hreal := congrArg Complex.re htelescoping
  have hreal' :
      (∑ scale ∈ Finset.range depth,
          dyadicHodgeBandWeight scale frequency) =
        tensorValleePoussinWeight (dyadicHodgeParameter depth) frequency -
          tensorValleePoussinWeight (dyadicHodgeParameter 0) frequency := by
    simpa using hreal
  have hsum :
      0 ≤ ∑ scale ∈ Finset.range depth,
        dyadicHodgeBandWeight scale frequency :=
    Finset.sum_nonneg fun scale _hscale ↦
      dyadicHodgeBandWeight_nonneg scale frequency
  rw [smoothDyadicCumulativeBoundaryMultiplier_re_eq]
  exact hsum.trans_eq hreal'

theorem smoothDyadicCumulativeBoundaryMultiplier_re_le_one
    (depth : ℕ) (frequency : SpatialFrequency) :
    (smoothDyadicCumulativeBoundaryMultiplier depth frequency).re ≤ 1 := by
  obtain ⟨_depthNonneg, hdepthOne⟩ :=
    tensorValleePoussinWeight_mem_unitInterval
      (dyadicHodgeParameter depth) frequency
  obtain ⟨hbaseNonneg, _hbaseOne⟩ :=
    tensorValleePoussinWeight_mem_unitInterval
      (dyadicHodgeParameter 0) frequency
  rw [smoothDyadicCumulativeBoundaryMultiplier_re_eq]
  linarith

theorem smoothDyadicCumulativeBoundaryMultiplier_re_mem_unitInterval
    (depth : ℕ) (frequency : SpatialFrequency) :
    0 ≤ (smoothDyadicCumulativeBoundaryMultiplier depth frequency).re ∧
      (smoothDyadicCumulativeBoundaryMultiplier depth frequency).re ≤ 1 :=
  ⟨smoothDyadicCumulativeBoundaryMultiplier_re_nonneg depth frequency,
    smoothDyadicCumulativeBoundaryMultiplier_re_le_one depth frequency⟩

theorem smoothDyadicCumulativeBoundaryMultiplier_im_eq_zero
    (depth : ℕ) (frequency : SpatialFrequency) :
    (smoothDyadicCumulativeBoundaryMultiplier depth frequency).im = 0 := by
  simp [smoothDyadicCumulativeBoundaryMultiplier]

/-! ## Actual depth-uniform energy estimate -/

theorem complexVectorEuclideanSquare_le_complexVectorL1_sq
    (coefficient : ComplexVector) :
    complexVectorEuclideanSquare coefficient ≤
      complexVectorL1 coefficient ^ 2 := by
  calc
    complexVectorEuclideanSquare coefficient =
        ∑ component : Fin 3, ‖coefficient component‖ ^ 2 := by
      simp [complexVectorEuclideanSquare, Complex.normSq_eq_norm_sq]
    _ ≤ (∑ component : Fin 3, ‖coefficient component‖) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg fun component _hcomponent ↦
        norm_nonneg (coefficient component)
    _ = complexVectorL1 coefficient ^ 2 := by
      simp [complexVectorL1, Fin.sum_univ_succ]
      ring

/-- The positive finite low-pass boundary storage is no larger than the unweighted coefficient
energy in its aperture. -/
theorem linearBoundaryStorage_le_finiteVorticityEnergy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    (linearMultiplierCoefficientStorage
        (smoothDyadicCumulativeBoundaryMultiplier depth)
        (smoothDyadicBandNativeAperture depth)
        (openPeriodicVorticityFourierMode solution t)).re ≤
      (1 / 2 : ℝ) *
        ∑ frequency ∈ smoothDyadicBandNativeAperture depth,
          complexVectorEuclideanSquare
            (openPeriodicVorticityFourierMode solution t frequency) := by
  unfold linearMultiplierCoefficientStorage
  simp_rw [complexVectorHermitianPairing_self_eq]
  have hmap :
      (∑ frequency ∈ smoothDyadicBandNativeAperture depth,
        (1 / 2 : ℂ) * smoothDyadicCumulativeBoundaryMultiplier depth frequency *
          (complexVectorEuclideanSquare
            (openPeriodicVorticityFourierMode solution t frequency) : ℂ)).re =
        ∑ frequency ∈ smoothDyadicBandNativeAperture depth,
          ((1 / 2 : ℂ) * smoothDyadicCumulativeBoundaryMultiplier depth frequency *
            (complexVectorEuclideanSquare
              (openPeriodicVorticityFourierMode solution t frequency) : ℂ)).re := by
    change Complex.reCLM
      (∑ frequency ∈ smoothDyadicBandNativeAperture depth,
        (1 / 2 : ℂ) * smoothDyadicCumulativeBoundaryMultiplier depth frequency *
          (complexVectorEuclideanSquare
            (openPeriodicVorticityFourierMode solution t frequency) : ℂ)) = _
    rw [map_sum]
    rfl
  rw [hmap]
  calc
    (∑ frequency ∈ smoothDyadicBandNativeAperture depth,
        ((1 / 2 : ℂ) * smoothDyadicCumulativeBoundaryMultiplier depth frequency *
          (complexVectorEuclideanSquare
            (openPeriodicVorticityFourierMode solution t frequency) : ℂ)).re) ≤
      ∑ frequency ∈ smoothDyadicBandNativeAperture depth,
        (1 / 2 : ℝ) * complexVectorEuclideanSquare
          (openPeriodicVorticityFourierMode solution t frequency) := by
        apply Finset.sum_le_sum
        intro frequency _hfrequency
        have hboundaryReal :
            smoothDyadicCumulativeBoundaryMultiplier depth frequency =
              ((smoothDyadicCumulativeBoundaryMultiplier depth frequency).re : ℂ) := by
          apply Complex.ext
          · simp
          · simp [smoothDyadicCumulativeBoundaryMultiplier_im_eq_zero]
        rw [hboundaryReal]
        have hsquareNonneg :
            0 ≤ complexVectorEuclideanSquare
              (openPeriodicVorticityFourierMode solution t frequency) := by
          unfold complexVectorEuclideanSquare
          exact Finset.sum_nonneg fun component _hcomponent ↦
            Complex.normSq_nonneg _
        have hterm :
            (((1 / 2 : ℂ) *
                ((smoothDyadicCumulativeBoundaryMultiplier depth frequency).re : ℂ) *
                (complexVectorEuclideanSquare
                  (openPeriodicVorticityFourierMode solution t frequency) : ℂ)).re) =
              (1 / 2 : ℝ) *
                (smoothDyadicCumulativeBoundaryMultiplier depth frequency).re *
                complexVectorEuclideanSquare
                  (openPeriodicVorticityFourierMode solution t frequency) := by
          norm_num
        rw [hterm]
        have hboundaryLe :=
          smoothDyadicCumulativeBoundaryMultiplier_re_le_one depth frequency
        nlinarith
    _ = _ := by rw [Finset.mul_sum]

/-- Every finite coefficient-energy aperture is bounded by the square of the complete actual
coefficient `L¹` population. -/
theorem finiteVorticityEnergy_le_fullCoefficientMass_sq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (aperture : Finset SpatialFrequency) :
    (∑ frequency ∈ aperture,
        complexVectorEuclideanSquare
          (openPeriodicVorticityFourierMode solution t frequency)) ≤
      openPeriodicFullVorticityCoefficientMass solution t ^ 2 := by
  let mass : SpatialFrequency → ℝ := fun frequency ↦
    complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency)
  have hmassSummable : Summable mass :=
    summable_complexVectorL1_openPeriodicVorticityFourierMode solution t
  have hfiniteMassNonneg : 0 ≤ ∑ frequency ∈ aperture, mass frequency :=
    Finset.sum_nonneg fun frequency _hfrequency ↦ complexVectorL1_nonneg _
  have hfinite_le_full :
      (∑ frequency ∈ aperture, mass frequency) ≤ ∑' frequency, mass frequency :=
    hmassSummable.sum_le_tsum aperture fun frequency _hfrequency ↦
      complexVectorL1_nonneg _
  have hfullNonneg : 0 ≤ ∑' frequency, mass frequency :=
    tsum_nonneg fun frequency ↦ complexVectorL1_nonneg _
  calc
    (∑ frequency ∈ aperture,
        complexVectorEuclideanSquare
          (openPeriodicVorticityFourierMode solution t frequency)) ≤
      ∑ frequency ∈ aperture, mass frequency ^ 2 := by
        apply Finset.sum_le_sum
        intro frequency _hfrequency
        exact complexVectorEuclideanSquare_le_complexVectorL1_sq _
    _ ≤ (∑ frequency ∈ aperture, mass frequency) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg fun frequency _hfrequency ↦
        complexVectorL1_nonneg _
    _ ≤ (∑' frequency, mass frequency) ^ 2 :=
      (sq_le_sq₀ hfiniteMassNonneg hfullNonneg).2 hfinite_le_full
    _ = openPeriodicFullVorticityCoefficientMass solution t ^ 2 := by
      rfl

/-- **Actual depth-uniform finite-scale estimate.**  The complete ordinary smooth-band energy
population below any depth is paid by one depth-independent receiver on the same solution slice.
No terminal hypothesis or generated receipt occurs in the statement. -/
theorem sum_openSmoothDyadicBandRealEnergy_le_fullCoefficientMass_sq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    (∑ scale ∈ Finset.range depth,
        openSmoothDyadicBandRealEnergy solution t scale) ≤
      (1 / 2 : ℝ) *
        openPeriodicFullVorticityCoefficientMass solution t ^ 2 := by
  calc
    (∑ scale ∈ Finset.range depth,
        openSmoothDyadicBandRealEnergy solution t scale) ≤
      (linearMultiplierCoefficientStorage
        (smoothDyadicCumulativeBoundaryMultiplier depth)
        (smoothDyadicBandNativeAperture depth)
        (openPeriodicVorticityFourierMode solution t)).re :=
      sum_openSmoothDyadicBandRealEnergy_le_lowPass_boundary
        solution t depth
    _ ≤ (1 / 2 : ℝ) *
        ∑ frequency ∈ smoothDyadicBandNativeAperture depth,
          complexVectorEuclideanSquare
            (openPeriodicVorticityFourierMode solution t frequency) :=
      linearBoundaryStorage_le_finiteVorticityEnergy solution t depth
    _ ≤ (1 / 2 : ℝ) *
        openPeriodicFullVorticityCoefficientMass solution t ^ 2 :=
      mul_le_mul_of_nonneg_left
        (finiteVorticityEnergy_le_fullCoefficientMass_sq
          solution t (smoothDyadicBandNativeAperture depth)) (by norm_num)

/-- The actual full ordinary smooth-band energy word is summable on every admitted solution
slice, now as a consequence of the depth-independent receiver rather than a separate smooth-tail
construction. -/
theorem summable_openSmoothDyadicBandRealEnergy_of_fullCoefficientMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    Summable fun scale : ℕ ↦ openSmoothDyadicBandRealEnergy solution t scale := by
  apply summable_of_sum_range_le
    (fun scale ↦ openSmoothDyadicBandRealEnergy_nonneg solution t scale)
  intro depth
  exact sum_openSmoothDyadicBandRealEnergy_le_fullCoefficientMass_sq
    solution t depth

/-- **Infinite-depth scale estimate.**  Passing through monotone finite prefixes preserves the
same actual depth-independent coefficient receiver. -/
theorem tsum_openSmoothDyadicBandRealEnergy_le_fullCoefficientMass_sq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    (∑' scale : ℕ, openSmoothDyadicBandRealEnergy solution t scale) ≤
      (1 / 2 : ℝ) *
        openPeriodicFullVorticityCoefficientMass solution t ^ 2 := by
  exact Real.tsum_le_of_sum_range_le
    (fun scale ↦ openSmoothDyadicBandRealEnergy_nonneg solution t scale)
    (sum_openSmoothDyadicBandRealEnergy_le_fullCoefficientMass_sq solution t)

section Audit

#print axioms smoothDyadicCumulativeBoundaryMultiplier_re_mem_unitInterval
#print axioms linearBoundaryStorage_le_finiteVorticityEnergy
#print axioms finiteVorticityEnergy_le_fullCoefficientMass_sq
#print axioms sum_openSmoothDyadicBandRealEnergy_le_fullCoefficientMass_sq
#print axioms tsum_openSmoothDyadicBandRealEnergy_le_fullCoefficientMass_sq

end Audit

end Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearUniformBoundary
