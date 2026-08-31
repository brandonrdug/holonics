import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeScaleChain
import ElementaryHolonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation

/-!
# Direct dyadic Hodge kernel variation

**[proved-derived]** This owner reindexes the genuine direct dyadic Hodge multiplier into one
centered coefficient cube.  The cancellation between consecutive low passes remains inside each
coefficient before any norm is taken.  Exact one- and three-coordinate Abel passages therefore
land on zero-padded variations of the direct band itself, including all aperture and zero-crossing
stencils.

No uniform physical `L1` conclusion is asserted here.  Its remaining analytic input is a
scale-uniform collection of direct dyadic subset-variation masses, followed by the coordinate-face
integration which combines their Abel factors.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedFubini
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain

/-! ## One centered owner for the direct band coefficient -/

/-- The common centered aperture radius of the direct dyadic band. -/
def dyadicHodgeApertureRadius (scale : ℕ) : ℕ :=
  dyadicHodgeOuterCutoff (scale + 1)

/-- The exact number of lattice positions in each displayed dyadic aperture coordinate. -/
def dyadicHodgeApertureCount (scale : ℕ) : ℕ :=
  centeredFrequencyCount (dyadicHodgeApertureRadius scale)

/-- The direct aperture is the next dyadic support radius, exactly. -/
theorem dyadicHodgeApertureRadius_eq (scale : ℕ) :
    dyadicHodgeApertureRadius scale = dyadicRadius (scale + 2) - 1 := by
  unfold dyadicHodgeApertureRadius
  simpa [Nat.add_assoc] using dyadicHodgeOuterCutoff_eq (scale + 1)

/-- The displayed population has the exact next-support dyadic cardinality. -/
theorem dyadicHodgeApertureCount_eq (scale : ℕ) :
    dyadicHodgeApertureCount scale = dyadicRadius (scale + 3) - 1 := by
  have hpositive : 1 ≤ dyadicRadius (scale + 2) := by
    exact Nat.one_le_pow (scale + 2) 2 (by norm_num)
  have hsucc : dyadicRadius (scale + 3) = 2 * dyadicRadius (scale + 2) := by
    simp only [dyadicRadius, show scale + 3 = (scale + 2) + 1 by omega, pow_succ]
    ring
  rw [dyadicHodgeApertureCount, centeredFrequencyCount,
    dyadicHodgeApertureRadius_eq, hsucc]
  omega

/-- The lattice frequency at one natural-indexed position of the complete dyadic aperture. -/
def dyadicHodgeApertureFrequency
    (scale firstIndex secondIndex thirdIndex : ℕ) : SpatialFrequency :=
  ![centeredFrequency (dyadicHodgeApertureRadius scale) firstIndex,
    centeredFrequency (dyadicHodgeApertureRadius scale) secondIndex,
    centeredFrequency (dyadicHodgeApertureRadius scale) thirdIndex]

/-- The common left endpoint of the centered dyadic aperture. -/
def dyadicHodgeApertureBaseFrequency (scale : ℕ) : SpatialFrequency :=
  fun _ ↦ -(dyadicHodgeApertureRadius scale : ℤ)

/-- One genuine direct-band coefficient.  The subtraction occurs before multiplication by the
Hodge entry and, crucially, before any norm. -/
def dyadicHodgeCubeCoefficient
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  (dyadicHodgeBandWeight scale
      (dyadicHodgeApertureFrequency scale firstIndex secondIndex thirdIndex) : ℂ) *
    hodgeJacobianMultiplierEntry
      (dyadicHodgeApertureFrequency scale firstIndex secondIndex thirdIndex)
      component coordinate input

/-- The direct coefficient exposes the consecutive-profile cancellation without a triangle
separation. -/
theorem dyadicHodgeCubeCoefficient_eq_profileDifference_mul_hodge
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) :
    dyadicHodgeCubeCoefficient scale component coordinate input
        firstIndex secondIndex thirdIndex =
      ((tensorValleePoussinWeight (dyadicHodgeParameter (scale + 1))
          (dyadicHodgeApertureFrequency scale firstIndex secondIndex thirdIndex) : ℂ) -
        (tensorValleePoussinWeight (dyadicHodgeParameter scale)
          (dyadicHodgeApertureFrequency scale firstIndex secondIndex thirdIndex) : ℂ)) *
        hodgeJacobianMultiplierEntry
          (dyadicHodgeApertureFrequency scale firstIndex secondIndex thirdIndex)
          component coordinate input := by
  unfold dyadicHodgeCubeCoefficient dyadicHodgeBandWeight
  push_cast
  rfl

/-- Every in-range displayed index denotes a frequency in the actual outer support cube. -/
theorem dyadicHodgeApertureFrequency_mem_outer_of_indices
    (scale firstIndex secondIndex thirdIndex : ℕ)
    (hfirst : firstIndex < dyadicHodgeApertureCount scale)
    (hsecond : secondIndex < dyadicHodgeApertureCount scale)
    (hthird : thirdIndex < dyadicHodgeApertureCount scale) :
    dyadicHodgeApertureFrequency scale firstIndex secondIndex thirdIndex ∈
      frequencyCube (dyadicHodgeApertureRadius scale) := by
  rw [mem_frequencyCube_iff]
  intro axis
  fin_cases axis
  · simpa [dyadicHodgeApertureFrequency, dyadicHodgeApertureCount] using
      centeredFrequency_mem_interval (dyadicHodgeApertureRadius scale)
        firstIndex hfirst
  · simpa [dyadicHodgeApertureFrequency, dyadicHodgeApertureCount] using
      centeredFrequency_mem_interval (dyadicHodgeApertureRadius scale)
        secondIndex hsecond
  · simpa [dyadicHodgeApertureFrequency, dyadicHodgeApertureCount] using
      centeredFrequency_mem_interval (dyadicHodgeApertureRadius scale)
        thirdIndex hthird

/-- The direct coefficient vanishes on the smaller exact dyadic cube, retaining the cancellation
at the totalized zero mode as part of the same statement. -/
theorem dyadicHodgeCubeCoefficient_eq_zero_of_mem_inner
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ)
    (hfrequency :
      dyadicHodgeApertureFrequency scale firstIndex secondIndex thirdIndex ∈
        frequencyCube (dyadicHodgeInnerCutoff scale)) :
    dyadicHodgeCubeCoefficient scale component coordinate input
      firstIndex secondIndex thirdIndex = 0 := by
  unfold dyadicHodgeCubeCoefficient
  rw [dyadicHodgeBandWeight_eq_zero_of_mem_inner scale hfrequency]
  simp

/-- A direct dyadic scalar band coefficient stays in the unit interval in magnitude. -/
theorem abs_dyadicHodgeBandWeight_le_one
    (scale : ℕ) (frequency : SpatialFrequency) :
    |dyadicHodgeBandWeight scale frequency| ≤ 1 := by
  obtain ⟨hnextNonneg, hnextOne⟩ :=
    tensorValleePoussinWeight_mem_unitInterval
      (dyadicHodgeParameter (scale + 1)) frequency
  obtain ⟨hbaseNonneg, hbaseOne⟩ :=
    tensorValleePoussinWeight_mem_unitInterval
      (dyadicHodgeParameter scale) frequency
  rw [abs_le]
  constructor <;> unfold dyadicHodgeBandWeight <;> linarith

/-- Every direct coefficient has magnitude at most one before summation. -/
theorem norm_dyadicHodgeCubeCoefficient_le_one
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) :
    ‖dyadicHodgeCubeCoefficient scale component coordinate input
      firstIndex secondIndex thirdIndex‖ ≤ 1 := by
  unfold dyadicHodgeCubeCoefficient
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |dyadicHodgeBandWeight scale
        (dyadicHodgeApertureFrequency scale firstIndex secondIndex thirdIndex)| *
          ‖hodgeJacobianMultiplierEntry
            (dyadicHodgeApertureFrequency scale firstIndex secondIndex thirdIndex)
            component coordinate input‖ ≤
      |dyadicHodgeBandWeight scale
        (dyadicHodgeApertureFrequency scale firstIndex secondIndex thirdIndex)| * 1 :=
          mul_le_mul_of_nonneg_left
            (norm_hodgeJacobianMultiplierEntry_le_one _ component coordinate input)
            (abs_nonneg _)
    _ ≤ 1 := by simpa using abs_dyadicHodgeBandWeight_le_one scale _

/-- The zero-order direct coefficient mass has its sharp aperture-population scaling. -/
theorem sum_norm_dyadicHodgeCubeCoefficient_le_count_cube
    (scale : ℕ) (component coordinate input : Fin 3) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicHodgeCubeCoefficient scale component coordinate input
            firstIndex secondIndex thirdIndex‖) ≤
      (dyadicHodgeApertureCount scale : ℝ) ^ 3 := by
  calc
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicHodgeCubeCoefficient scale component coordinate input
            firstIndex secondIndex thirdIndex‖) ≤
      ∑ _firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ _secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ∑ _thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
            (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro firstIndex _hfirstIndex
      apply Finset.sum_le_sum
      intro secondIndex _hsecondIndex
      apply Finset.sum_le_sum
      intro thirdIndex _hthirdIndex
      exact norm_dyadicHodgeCubeCoefficient_le_one scale component coordinate input
        firstIndex secondIndex thirdIndex
    _ = (dyadicHodgeApertureCount scale : ℝ) ^ 3 := by
      simp
      ring

/-! ## Exact centered physical synthesis -/

/-- The aperture character factors into its common endpoint and three natural powers. -/
theorem mFourier_dyadicHodgeApertureFrequency
    (scale firstIndex secondIndex thirdIndex : ℕ)
    (q : UnitAddTorus (Fin 3)) :
    UnitAddTorus.mFourier
        (dyadicHodgeApertureFrequency scale firstIndex secondIndex thirdIndex) q =
      UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
        fourier 1 (q 0) ^ firstIndex * fourier 1 (q 1) ^ secondIndex *
          fourier 1 (q 2) ^ thirdIndex := by
  dsimp only [UnitAddTorus.mFourier, dyadicHodgeApertureFrequency,
    dyadicHodgeApertureBaseFrequency, ContinuousMap.coe_mk]
  simp only [Fin.prod_univ_three]
  change
    fourier (centeredFrequency (dyadicHodgeApertureRadius scale) firstIndex)
          (q 0) *
        fourier (centeredFrequency (dyadicHodgeApertureRadius scale) secondIndex)
          (q 1) *
          fourier (centeredFrequency (dyadicHodgeApertureRadius scale) thirdIndex)
            (q 2) =
      (fourier (-(dyadicHodgeApertureRadius scale : ℤ)) (q 0) *
        fourier (-(dyadicHodgeApertureRadius scale : ℤ)) (q 1) *
          fourier (-(dyadicHodgeApertureRadius scale : ℤ)) (q 2)) *
        fourier 1 (q 0) ^ firstIndex * fourier 1 (q 1) ^ secondIndex *
          fourier 1 (q 2) ^ thirdIndex
  rw [fourier_centeredFrequency_eq_endpoint_mul_pow,
    fourier_centeredFrequency_eq_endpoint_mul_pow,
    fourier_centeredFrequency_eq_endpoint_mul_pow]
  ring

/-- The genuine direct dyadic physical kernel is the centered synthesis of the single direct
coefficient cube. -/
theorem dyadicHodgeJacobianKernelEntry_eq_centeredSynthesis
    (scale : ℕ) (component coordinate input : Fin 3)
    (q : UnitAddTorus (Fin 3)) :
    dyadicHodgeJacobianKernelEntry scale component coordinate input q =
      UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
        finiteCharacterSynthesisThree
          (dyadicHodgeCubeCoefficient scale component coordinate input)
          (fourier 1 (q 0)) (fourier 1 (q 1)) (fourier 1 (q 2))
          (dyadicHodgeApertureCount scale) (dyadicHodgeApertureCount scale)
          (dyadicHodgeApertureCount scale) := by
  unfold dyadicHodgeJacobianKernelEntry finiteFourierSynthesis
  change (∑ frequency ∈ frequencyCube (dyadicHodgeApertureRadius scale),
      UnitAddTorus.mFourier frequency q *
        ((dyadicHodgeBandWeight scale frequency : ℂ) *
          hodgeJacobianMultiplierEntry frequency component coordinate input)) = _
  rw [sum_frequencyCube_eq_sum_centeredAperture]
  change (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          UnitAddTorus.mFourier
              (dyadicHodgeApertureFrequency scale firstIndex secondIndex thirdIndex) q *
            dyadicHodgeCubeCoefficient scale component coordinate input
              firstIndex secondIndex thirdIndex) = _
  simp_rw [mFourier_dyadicHodgeApertureFrequency]
  unfold finiteCharacterSynthesisThree
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro firstIndex _hfirstIndex
  calc
    (∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
      ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
            fourier 1 (q 0) ^ firstIndex * fourier 1 (q 1) ^ secondIndex *
              fourier 1 (q 2) ^ thirdIndex *
                dyadicHodgeCubeCoefficient scale component coordinate input
                  firstIndex secondIndex thirdIndex) =
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        (UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
          fourier 1 (q 0) ^ firstIndex) *
          ((∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
              dyadicHodgeCubeCoefficient scale component coordinate input
                firstIndex secondIndex thirdIndex * fourier 1 (q 2) ^ thirdIndex) *
            fourier 1 (q 1) ^ secondIndex) := by
              apply Finset.sum_congr rfl
              intro secondIndex _hsecondIndex
              calc
                (∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
                  UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
                      fourier 1 (q 0) ^ firstIndex * fourier 1 (q 1) ^ secondIndex *
                        fourier 1 (q 2) ^ thirdIndex *
                          dyadicHodgeCubeCoefficient scale component coordinate input
                            firstIndex secondIndex thirdIndex) =
                    (UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
                      fourier 1 (q 0) ^ firstIndex * fourier 1 (q 1) ^ secondIndex) *
                        (∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
                          dyadicHodgeCubeCoefficient scale component coordinate input
                            firstIndex secondIndex thirdIndex *
                              fourier 1 (q 2) ^ thirdIndex) := by
                                rw [Finset.mul_sum]
                                apply Finset.sum_congr rfl
                                intro thirdIndex _hthirdIndex
                                ring
                _ = UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
                    fourier 1 (q 0) ^ firstIndex *
                      ((∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
                        dyadicHodgeCubeCoefficient scale component coordinate input
                          firstIndex secondIndex thirdIndex *
                            fourier 1 (q 2) ^ thirdIndex) *
                          fourier 1 (q 1) ^ secondIndex) := by ring
    _ = (UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
          fourier 1 (q 0) ^ firstIndex) *
        (∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ((∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
              dyadicHodgeCubeCoefficient scale component coordinate input
                firstIndex secondIndex thirdIndex * fourier 1 (q 2) ^ thirdIndex) *
            fourier 1 (q 1) ^ secondIndex)) := by
              rw [Finset.mul_sum]
    _ = UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
        ((∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          (∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
            dyadicHodgeCubeCoefficient scale component coordinate input
              firstIndex secondIndex thirdIndex * fourier 1 (q 2) ^ thirdIndex) *
            fourier 1 (q 1) ^ secondIndex) *
          fourier 1 (q 0) ^ firstIndex) := by ring

/-! ## Direct zero-padded subset variations and Abel passages -/

/-- Second difference in the first displayed coordinate of the direct dyadic coefficient. -/
def dyadicHodgeCubeSecondDifferenceFirst
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifferenceFirst
    (dyadicHodgeCubeCoefficient scale component coordinate input)
    (dyadicHodgeApertureCount scale) firstIndex secondIndex thirdIndex

/-- Ordered second differences in all three coordinates of the direct dyadic coefficient. -/
def dyadicHodgeCubeSecondDifferenceAll
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifferenceAll
    (dyadicHodgeCubeCoefficient scale component coordinate input)
    (dyadicHodgeApertureCount scale) (dyadicHodgeApertureCount scale)
    (dyadicHodgeApertureCount scale) firstIndex secondIndex thirdIndex

/-- Exact one-coordinate Abel identity for the direct dyadic Hodge kernel. -/
theorem dyadicHodgeJacobianKernelEntry_firstAbel
    (scale : ℕ) (component coordinate input : Fin 3)
    (q : UnitAddTorus (Fin 3)) :
    (1 - fourier 1 (q 0)) ^ 2 *
        dyadicHodgeJacobianKernelEntry scale component coordinate input q =
      UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
        finiteCharacterSynthesisThree
          (dyadicHodgeCubeSecondDifferenceFirst scale component coordinate input)
          (fourier 1 (q 0)) (fourier 1 (q 1)) (fourier 1 (q 2))
          (dyadicHodgeApertureCount scale + 2) (dyadicHodgeApertureCount scale)
          (dyadicHodgeApertureCount scale) := by
  rw [dyadicHodgeJacobianKernelEntry_eq_centeredSynthesis]
  unfold dyadicHodgeCubeSecondDifferenceFirst
  rw [finiteCharacterSynthesisThree_secondDifferenceFirst]
  ring

/-- Exact triple Abel identity.  Every direct-band aperture residue remains in the single mixed
coefficient population on the right. -/
theorem dyadicHodgeJacobianKernelEntry_tripleAbel
    (scale : ℕ) (component coordinate input : Fin 3)
    (q : UnitAddTorus (Fin 3)) :
    (1 - fourier 1 (q 0)) ^ 2 * (1 - fourier 1 (q 1)) ^ 2 *
          (1 - fourier 1 (q 2)) ^ 2 *
            dyadicHodgeJacobianKernelEntry scale component coordinate input q =
      UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q *
        finiteCharacterSynthesisThree
          (dyadicHodgeCubeSecondDifferenceAll scale component coordinate input)
          (fourier 1 (q 0)) (fourier 1 (q 1)) (fourier 1 (q 2))
          (dyadicHodgeApertureCount scale + 2)
          (dyadicHodgeApertureCount scale + 2)
          (dyadicHodgeApertureCount scale + 2) := by
  rw [dyadicHodgeJacobianKernelEntry_eq_centeredSynthesis]
  unfold dyadicHodgeCubeSecondDifferenceAll
  rw [finiteCharacterSynthesisThree_secondDifferenceAll]
  ring

/-- After the three exact Abel factors, the physical direct-band entry is controlled with
constant one by the direct mixed variation mass.  Cancellation has not been separated. -/
theorem norm_dyadicHodgeJacobianKernelEntry_tripleAbel_le_directMixedMass
    (scale : ℕ) (component coordinate input : Fin 3)
    (q : UnitAddTorus (Fin 3)) :
    ‖(1 - fourier 1 (q 0)) ^ 2 * (1 - fourier 1 (q 1)) ^ 2 *
          (1 - fourier 1 (q 2)) ^ 2 *
            dyadicHodgeJacobianKernelEntry scale component coordinate input q‖ ≤
      ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
            ‖dyadicHodgeCubeSecondDifferenceAll scale component coordinate input
              firstIndex secondIndex thirdIndex‖ := by
  rw [dyadicHodgeJacobianKernelEntry_tripleAbel, norm_mul]
  have hbase :
      ‖UnitAddTorus.mFourier (dyadicHodgeApertureBaseFrequency scale) q‖ = 1 := by
    simp [UnitAddTorus.mFourier, norm_prod, Circle.norm_coe]
  rw [hbase, one_mul]
  apply norm_finiteCharacterSynthesisThree_le_mass
  all_goals rw [fourier_apply]
  all_goals exact Circle.norm_coe _

#print axioms dyadicHodgeJacobianKernelEntry_eq_centeredSynthesis
#print axioms dyadicHodgeJacobianKernelEntry_firstAbel
#print axioms dyadicHodgeJacobianKernelEntry_tripleAbel
#print axioms norm_dyadicHodgeJacobianKernelEntry_tripleAbel_le_directMixedMass

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation
