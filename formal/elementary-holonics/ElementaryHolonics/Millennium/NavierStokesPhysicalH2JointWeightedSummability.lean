import ElementaryHolonics.Millennium.NavierStokesCofinalOutputReceiverClosure

/-!
# Joint unbounded H²-weight summability of the complete vorticity interactions

**[proved-derived; formal-checked]**  A smooth interior periodic solution slice supplies the
complete `(1 + λ)`-weighted vorticity coefficient mass.  The weight is not an assumed sequence:
its three coordinate occurrences are the Fourier coefficients of the actual diagonal second
spatial derivatives of vorticity, each retained in the standing smooth `H³` carrier.

That single receiver mass majorizes the weighted receiving occurrence in the complete transport
population and the weighted output occurrence in the complete stretching population.  The two
product-lattice summability theorems therefore preserve every existing address while closing the
joint unbounded-weight gates required before global Fubini.  No terminal estimate is asserted.
-/

noncomputable section

open Set
open scoped BigOperators ComplexConjugate

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2JointWeightedSummability

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCofinalOutputReceiverClosure
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesCoordinateH2Production
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTranslationDissipation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

/-! ## The actual second-derivative coefficient occurrences -/

/-- The smooth `H³` carrier of one diagonal second spatial derivative of the actual vorticity
slice.  Its extra regularity comes from the admitted smooth solution, not from a terminal bound. -/
def openVorticitySecondCoordinateDerivativeH3State
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (coordinate : Fin 3) : PeriodicVectorSobolevThree :=
  let omega : InitialVelocity := fun x ↦ vorticityField velocity x t.1
  let homega : ContDiff ℝ (⊤ : ℕ∞) omega :=
    openPeriodicSolutionOn_vorticitySlice_contDiff solution t
  let hperiodic : IsOnePeriodic omega :=
    openPeriodicSolutionOn_vorticityField_isOnePeriodic solution t.2
  smoothSliceH3State (secondSpatialCoordinateJet omega coordinate coordinate)
    (secondSpatialCoordinateJet_contDiff omega homega coordinate coordinate)
    (secondSpatialCoordinateJet_isOnePeriodic omega hperiodic coordinate coordinate)

/-- One diagonal second-derivative occurrence has exactly its addressed coordinate Stokes
weight times the norm of the source vorticity coefficient. -/
theorem norm_openVorticitySecondCoordinateDerivativeH3State_apply
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (coordinate output : Fin 3) (frequency : SpatialFrequency) :
    ‖(openVorticitySecondCoordinateDerivativeH3State
        solution t coordinate output).1 frequency‖ =
      coordinateStokesEigenvalue coordinate frequency *
        ‖openPeriodicVorticityFourierMode solution t frequency output‖ := by
  let omega : InitialVelocity := fun x ↦ vorticityField velocity x t.1
  let homega : ContDiff ℝ (⊤ : ℕ∞) omega :=
    openPeriodicSolutionOn_vorticitySlice_contDiff solution t
  let hperiodic : IsOnePeriodic omega :=
    openPeriodicSolutionOn_vorticityField_isOnePeriodic solution t.2
  have hsquare := norm_sq_smoothSliceFourierL2_second
    omega homega hperiodic coordinate coordinate output frequency
  have hsource := smoothSliceFourierL2_vorticity_eq_openPeriodicVorticityFourierMode
    solution t output frequency
  have hsource' :
      smoothSliceFourierL2 omega homega hperiodic output frequency =
        openPeriodicVorticityFourierMode solution t frequency output := by
    simpa only [omega, homega, hperiodic] using hsource
  change ‖smoothSliceFourierL2
      (secondSpatialCoordinateJet omega coordinate coordinate)
      (secondSpatialCoordinateJet_contDiff omega homega coordinate coordinate)
      (secondSpatialCoordinateJet_isOnePeriodic omega hperiodic coordinate coordinate)
      output frequency‖ =
    coordinateStokesEigenvalue coordinate frequency *
      ‖openPeriodicVorticityFourierMode solution t frequency output‖
  rw [← hsource']
  have hcoordinate := coordinateStokesEigenvalue_nonneg coordinate frequency
  have hleft : 0 ≤ ‖smoothSliceFourierL2
      (secondSpatialCoordinateJet omega coordinate coordinate)
      (secondSpatialCoordinateJet_contDiff omega homega coordinate coordinate)
      (secondSpatialCoordinateJet_isOnePeriodic omega hperiodic coordinate coordinate)
      output frequency‖ := norm_nonneg _
  have hright : 0 ≤ ‖smoothSliceFourierL2 omega homega hperiodic output frequency‖ :=
    norm_nonneg _
  have hsquare' :
      ‖smoothSliceFourierL2
        (secondSpatialCoordinateJet omega coordinate coordinate)
        (secondSpatialCoordinateJet_contDiff omega homega coordinate coordinate)
        (secondSpatialCoordinateJet_isOnePeriodic omega hperiodic coordinate coordinate)
        output frequency‖ ^ 2 =
      (coordinateStokesEigenvalue coordinate frequency *
        ‖smoothSliceFourierL2 omega homega hperiodic output frequency‖) ^ 2 := by
    calc
      _ = coordinateStokesEigenvalue coordinate frequency *
          coordinateStokesEigenvalue coordinate frequency *
            ‖smoothSliceFourierL2 omega homega hperiodic output frequency‖ ^ 2 := hsquare
      _ = _ := by ring
  exact (sq_eq_sq₀ hleft (mul_nonneg hcoordinate hright)).mp hsquare'

/-- Each coordinate-weighted component of the actual vorticity population is summable. -/
theorem summable_coordinateStokesEigenvalue_mul_norm_openPeriodicVorticityFourierMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (coordinate output : Fin 3) :
    Summable fun frequency : SpatialFrequency ↦
      coordinateStokesEigenvalue coordinate frequency *
        ‖openPeriodicVorticityFourierMode solution t frequency output‖ := by
  exact (periodicVectorSobolevThree_hasAbsolutelySummableComponents
      (openVorticitySecondCoordinateDerivativeH3State solution t coordinate) output).congr
    (fun frequency ↦
      (norm_openVorticitySecondCoordinateDerivativeH3State_apply
        solution t coordinate output frequency))

/-- The full Stokes-weighted norm of every actual vorticity component is summable. -/
theorem summable_torusStokesEigenvalue_mul_norm_openPeriodicVorticityFourierMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (output : Fin 3) :
    Summable fun frequency : SpatialFrequency ↦
      torusStokesEigenvalue frequency *
        ‖openPeriodicVorticityFourierMode solution t frequency output‖ := by
  have hcoordinates : Summable fun frequency : SpatialFrequency ↦
      ∑ coordinate : Fin 3,
        coordinateStokesEigenvalue coordinate frequency *
          ‖openPeriodicVorticityFourierMode solution t frequency output‖ := by
    apply summable_sum
    intro coordinate _hcoordinate
    exact summable_coordinateStokesEigenvalue_mul_norm_openPeriodicVorticityFourierMode
      solution t coordinate output
  exact hcoordinates.congr (fun frequency ↦ by
    rw [torusStokesEigenvalue_eq_sum_coordinate, Finset.sum_mul])

/-- The complete vector `L¹` vorticity mass remains summable after the full Stokes weight. -/
theorem summable_torusStokesEigenvalue_mul_complexVectorL1_openPeriodicVorticityFourierMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    Summable fun frequency : SpatialFrequency ↦
      torusStokesEigenvalue frequency *
        complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency) := by
  have hcomponents : Summable fun frequency : SpatialFrequency ↦
      ∑ output : Fin 3,
        torusStokesEigenvalue frequency *
          ‖openPeriodicVorticityFourierMode solution t frequency output‖ := by
    apply summable_sum
    intro output _houtput
    exact summable_torusStokesEigenvalue_mul_norm_openPeriodicVorticityFourierMode
      solution t output
  exact hcomponents.congr (fun frequency ↦ by
    unfold complexVectorL1
    simp only [Fin.sum_univ_three]
    ring)

/-- The common inhomogeneous H² multiplier receiver has a complete summable vorticity mass. -/
theorem summable_one_add_torusStokesEigenvalue_mul_complexVectorL1_openPeriodicVorticityFourierMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    Summable fun frequency : SpatialFrequency ↦
      (1 + torusStokesEigenvalue frequency) *
        complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency) := by
  have hunweighted :=
    summable_complexVectorL1_openPeriodicVorticityFourierMode solution t
  have hweighted :=
    summable_torusStokesEigenvalue_mul_complexVectorL1_openPeriodicVorticityFourierMode
      solution t
  exact (hunweighted.add hweighted).congr (fun frequency ↦ by ring)

/-! ## The two complete weighted interaction populations -/

/-- A weighted receiving component is bounded by the complete inhomogeneous weighted vorticity
mass, while retaining its exact receiving address. -/
theorem one_add_torusStokesEigenvalue_mul_norm_openPeriodicVorticityFourierMode_component_le_fullMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) (output : Fin 3) :
    (1 + torusStokesEigenvalue frequency) *
        ‖openPeriodicVorticityFourierMode solution t frequency output‖ ≤
      ∑' mode : SpatialFrequency,
        (1 + torusStokesEigenvalue mode) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t mode) := by
  have hcomponent :
      (1 + torusStokesEigenvalue frequency) *
          ‖openPeriodicVorticityFourierMode solution t frequency output‖ ≤
        (1 + torusStokesEigenvalue frequency) *
          complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency) := by
    apply mul_le_mul_of_nonneg_left
      ((norm_le_pi_norm
        (openPeriodicVorticityFourierMode solution t frequency) output).trans
          (norm_complexVector_le_complexVectorL1 _))
    linarith [torusStokesEigenvalue_nonneg frequency]
  have hsingle :=
    (summable_one_add_torusStokesEigenvalue_mul_complexVectorL1_openPeriodicVorticityFourierMode
      solution t).sum_le_tsum {frequency} (fun mode _hmode ↦
        mul_nonneg (by linarith [torusStokesEigenvalue_nonneg mode])
          (complexVectorL1_nonneg _))
  exact hcomponent.trans (by simpa using hsingle)

/-- **First joint Fubini gate.**  The complete transport population is absolutely summable after
the unbounded H² receiver multiplier. -/
theorem summable_one_add_torusStokesEigenvalue_mul_norm_completeOpenVorticityTransportFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    Summable fun address : CompleteTransportAddress ↦
      (1 + torusStokesEigenvalue (completeTransportReceiver address)) *
        ‖completeOpenVorticityTransportFace solution t address‖ := by
  let mass : ℝ := ∑' mode : SpatialFrequency,
    (1 + torusStokesEigenvalue mode) *
      complexVectorL1 (openPeriodicVorticityFourierMode solution t mode)
  have hcoordinates : Summable fun address : CompleteTransportAddress ↦
      ∑ output : Fin 3, ∑ coordinate : Fin 3,
        (1 + torusStokesEigenvalue (completeTransportReceiver address)) *
          ‖completeOpenVorticityTransportCoordinateFace
            solution t coordinate output address‖ := by
    apply summable_sum
    intro output _houtput
    apply summable_sum
    intro coordinate _hcoordinate
    have hvelocity :=
      summable_norm_openPeriodicVelocityFourierMode_component solution t coordinate
    have hderivative :=
      summable_norm_openVorticityDirectionalDerivativeH3State_component
        solution t coordinate output
    have hproduct : Summable fun address : CompleteTransportAddress ↦
        ‖openPeriodicVelocityFourierMode solution t address.1 coordinate‖ *
          ‖(openVorticityDirectionalDerivativeH3State
            solution t coordinate output).1 address.2‖ :=
      hvelocity.mul_of_nonneg hderivative (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
    have hmajorant := hproduct.mul_right mass
    refine Summable.of_nonneg_of_le (fun address ↦
      mul_nonneg
        (by linarith [torusStokesEigenvalue_nonneg (completeTransportReceiver address)])
        (norm_nonneg _))
      (fun address ↦ ?_) hmajorant
    rw [completeOpenVorticityTransportCoordinateFace, norm_mul, norm_mul]
    calc
      (1 + torusStokesEigenvalue (completeTransportReceiver address)) *
          (‖openPeriodicVelocityFourierMode solution t address.1 coordinate‖ *
              ‖(openVorticityDirectionalDerivativeH3State
                solution t coordinate output).1 address.2‖ *
            ‖openPeriodicVorticityFourierMode solution t
              (completeTransportReceiver address) output‖) =
        (‖openPeriodicVelocityFourierMode solution t address.1 coordinate‖ *
          ‖(openVorticityDirectionalDerivativeH3State
            solution t coordinate output).1 address.2‖) *
          ((1 + torusStokesEigenvalue (completeTransportReceiver address)) *
            ‖openPeriodicVorticityFourierMode solution t
              (completeTransportReceiver address) output‖) := by ring
      _ ≤ (‖openPeriodicVelocityFourierMode solution t address.1 coordinate‖ *
          ‖(openVorticityDirectionalDerivativeH3State
            solution t coordinate output).1 address.2‖) * mass := by
        apply mul_le_mul_of_nonneg_left
          (one_add_torusStokesEigenvalue_mul_norm_openPeriodicVorticityFourierMode_component_le_fullMass
            solution t (completeTransportReceiver address) output)
        exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine Summable.of_nonneg_of_le (fun address ↦
    mul_nonneg
      (by linarith [torusStokesEigenvalue_nonneg (completeTransportReceiver address)])
      (norm_nonneg _))
    (fun address ↦ ?_) hcoordinates
  rw [completeOpenVorticityTransportFace_eq_sum_coordinateFaces]
  calc
    (1 + torusStokesEigenvalue (completeTransportReceiver address)) *
        ‖∑ output : Fin 3, ∑ coordinate : Fin 3,
          completeOpenVorticityTransportCoordinateFace
            solution t coordinate output address‖ ≤
      (1 + torusStokesEigenvalue (completeTransportReceiver address)) *
        (∑ output : Fin 3, ∑ coordinate : Fin 3,
          ‖completeOpenVorticityTransportCoordinateFace
            solution t coordinate output address‖) := by
      apply mul_le_mul_of_nonneg_left
        ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun output _houtput ↦ norm_sum_le _ _))
      linarith [torusStokesEigenvalue_nonneg (completeTransportReceiver address)]
    _ = ∑ output : Fin 3, ∑ coordinate : Fin 3,
        (1 + torusStokesEigenvalue (completeTransportReceiver address)) *
          ‖completeOpenVorticityTransportCoordinateFace
            solution t coordinate output address‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro output _houtput
      rw [Finset.mul_sum]

/-- **Second joint Fubini gate.**  The complete symmetric stretching population is absolutely
summable after the unbounded H² output multiplier. -/
theorem summable_one_add_torusStokesEigenvalue_mul_norm_completeOpenVorticityStretchingFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    Summable fun address : CompleteStretchingAddress ↦
      (1 + torusStokesEigenvalue address.1) *
        ‖completeOpenVorticityStretchingFace solution t address‖ := by
  let mass : ℝ := ∑' mode : SpatialFrequency,
    (1 + torusStokesEigenvalue mode) *
      complexVectorL1 (openPeriodicVorticityFourierMode solution t mode)
  have hcoordinates : Summable fun address : CompleteStretchingAddress ↦
      ∑ output : Fin 3, ∑ coordinate : Fin 3,
        (1 + torusStokesEigenvalue address.1) *
          ‖completeOpenVorticityStretchingCoordinateFace
            solution t coordinate output address‖ := by
    apply summable_sum
    intro output _houtput
    apply summable_sum
    intro coordinate _hcoordinate
    have hvorticity : Summable fun frequency : SpatialFrequency ↦
        ‖openPeriodicVorticityFourierMode solution t frequency coordinate‖ := by
      refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun frequency ↦ ?_)
        (summable_complexVectorL1_openPeriodicVorticityFourierMode solution t)
      exact (norm_le_pi_norm
        (openPeriodicVorticityFourierMode solution t frequency) coordinate).trans
          (norm_complexVector_le_complexVectorL1 _)
    have hderivative :=
      summable_norm_openVelocityDirectionalDerivativeH3State_component
        solution t coordinate output
    have hproduct : Summable fun pair : SpatialFrequency × SpatialFrequency ↦
        ‖openPeriodicVorticityFourierMode solution t pair.1 coordinate‖ *
          ‖(openVelocityDirectionalDerivativeH3State
            solution t coordinate output).1 pair.2‖ :=
      hvorticity.mul_of_nonneg hderivative (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
    let rebase : (SpatialFrequency × SpatialFrequency) ≃ CompleteStretchingAddress :=
      { toFun := fun pair ↦ (pair.1 + pair.2, pair.1)
        invFun := fun address ↦ (address.2, address.1 - address.2)
        left_inv := by intro pair; ext <;> simp
        right_inv := by intro address; ext <;> simp }
    have hrebase : Summable fun address : CompleteStretchingAddress ↦
        ‖openPeriodicVorticityFourierMode solution t address.2 coordinate‖ *
          ‖(openVelocityDirectionalDerivativeH3State
            solution t coordinate output).1 (address.1 - address.2)‖ := by
      exact (hproduct.comp_injective rebase.symm.injective).congr (fun _ ↦ rfl)
    have hmajorant := hrebase.mul_right mass
    refine Summable.of_nonneg_of_le (fun address ↦
      mul_nonneg (by linarith [torusStokesEigenvalue_nonneg address.1]) (norm_nonneg _))
      (fun address ↦ ?_) hmajorant
    rw [completeOpenVorticityStretchingCoordinateFace, norm_mul, norm_mul,
      starRingEnd_apply, norm_star]
    calc
      (1 + torusStokesEigenvalue address.1) *
          (‖openPeriodicVorticityFourierMode solution t address.1 output‖ *
              ‖openPeriodicVorticityFourierMode solution t address.2 coordinate‖ *
            ‖(openVelocityDirectionalDerivativeH3State
              solution t coordinate output).1 (address.1 - address.2)‖) =
        (‖openPeriodicVorticityFourierMode solution t address.2 coordinate‖ *
          ‖(openVelocityDirectionalDerivativeH3State
            solution t coordinate output).1 (address.1 - address.2)‖) *
          ((1 + torusStokesEigenvalue address.1) *
            ‖openPeriodicVorticityFourierMode solution t address.1 output‖) := by ring
      _ ≤ (‖openPeriodicVorticityFourierMode solution t address.2 coordinate‖ *
          ‖(openVelocityDirectionalDerivativeH3State
            solution t coordinate output).1 (address.1 - address.2)‖) * mass := by
        apply mul_le_mul_of_nonneg_left
          (one_add_torusStokesEigenvalue_mul_norm_openPeriodicVorticityFourierMode_component_le_fullMass
            solution t address.1 output)
        exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine Summable.of_nonneg_of_le (fun address ↦
    mul_nonneg (by linarith [torusStokesEigenvalue_nonneg address.1]) (norm_nonneg _))
    (fun address ↦ ?_) hcoordinates
  unfold completeOpenVorticityStretchingFace
  let first := ∑ output : Fin 3, ∑ coordinate : Fin 3,
    completeOpenVorticityStretchingCoordinateFace
      solution t coordinate output address
  calc
    (1 + torusStokesEigenvalue address.1) *
        ‖(1 / 2 : ℂ) * (first + conj first)‖ ≤
      (1 + torusStokesEigenvalue address.1) * ‖first‖ := by
        apply mul_le_mul_of_nonneg_left _
          (by linarith [torusStokesEigenvalue_nonneg address.1])
        calc
          ‖(1 / 2 : ℂ) * (first + conj first)‖ ≤
              (1 / 2 : ℝ) * (‖first‖ + ‖conj first‖) := by
            rw [norm_mul]
            have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
            rw [hhalf]
            exact mul_le_mul_of_nonneg_left (norm_add_le first (conj first)) (by norm_num)
          _ = ‖first‖ := by rw [starRingEnd_apply, norm_star]; ring
    _ ≤ (1 + torusStokesEigenvalue address.1) *
        (∑ output : Fin 3, ∑ coordinate : Fin 3,
          ‖completeOpenVorticityStretchingCoordinateFace
            solution t coordinate output address‖) := by
      apply mul_le_mul_of_nonneg_left
        ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun output _houtput ↦ norm_sum_le _ _))
      linarith [torusStokesEigenvalue_nonneg address.1]
    _ = ∑ output : Fin 3, ∑ coordinate : Fin 3,
        (1 + torusStokesEigenvalue address.1) *
          ‖completeOpenVorticityStretchingCoordinateFace
            solution t coordinate output address‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro output _houtput
      rw [Finset.mul_sum]

section Audit

#print axioms norm_openVorticitySecondCoordinateDerivativeH3State_apply
#print axioms summable_one_add_torusStokesEigenvalue_mul_complexVectorL1_openPeriodicVorticityFourierMode
#print axioms summable_one_add_torusStokesEigenvalue_mul_norm_completeOpenVorticityTransportFace
#print axioms summable_one_add_torusStokesEigenvalue_mul_norm_completeOpenVorticityStretchingFace

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2JointWeightedSummability
