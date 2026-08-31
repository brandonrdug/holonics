import ElementaryHolonics.Millennium.NavierStokesPeriodicEnergy

/-!
# Periodic vorticity and the exact enstrophy receiver

This module composes the existing local curl passage, positive-time smooth-solution carrier, and
periodic integration-by-parts owner.  It derives the spatial periodicity and smoothness of the
actual vorticity field, proves cancellation of vorticity transport by an incompressible periodic
velocity, and returns the forced enstrophy equality from an explicitly typed pointwise vorticity
balance.

The pointwise balance is kept here as a visible typed port.  The successor module
`NavierStokesCurlCommutation` fills it directly from the official momentum equation by proving the
mixed space--time curl and spatial curl--Laplacian commutation squares.  Once that port is supplied,
all remaining analytic work in the periodic enstrophy identity is discharged here from compact
positive-time smoothness.  The three-dimensional stretching integral remains in the equality.
Under nonnegative viscosity, an exact final equivalence says that nonincrease occurs precisely when
the `nu D` term absorbs stretching plus curl-forcing work; no estimate asserting that absorption is
introduced.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Set
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesVorticity

/-! ## The actual positive-time vorticity field -/

/-- Spatial curl of a time-dependent velocity field, evaluated on its time slice.  The
`PeriodicSolution` smoothness testimony below admits every positive-time occurrence as an actual
derivative. -/
def vorticityField (velocity : VelocityField) : VelocityField :=
  fun x t => vorticityAt (fun y => velocity y t) x

/-- The fixed continuous-linear inclusion of a spatial direction into a space--time direction. -/
def spatialInclusion : Space →L[ℝ] Space × ℝ :=
  ContinuousLinearMap.inl ℝ Space ℝ

/-- Curl after restricting a joint space--time derivative to its spatial directions. -/
def jointSpatialCurlLinearMap :
    ((Space × ℝ) →L[ℝ] Space) →L[ℝ] Space :=
  derivativeCurlLinearMap.comp
    ((ContinuousLinearMap.compL ℝ Space (Space × ℝ) Space).flip spatialInclusion)

/-- The joint-derivative realization of spatial vorticity.  At every admitted positive-time
occurrence it agrees exactly with `vorticityField`. -/
def jointVorticityField (velocity : VelocityField) : VelocityField :=
  fun x t => jointSpatialCurlLinearMap
    (fderiv ℝ (Function.uncurry velocity) (x, t))

/-- At an interior positive-time occurrence, taking the derivative of a spatial slice is exactly
restriction of the joint derivative to the spatial inclusion. -/
theorem jointVorticityField_eq_vorticityField_of_contDiffAt
    (velocity : VelocityField) (x : Space) (t : ℝ)
    (hvelocity : ContDiffAt ℝ 1 (Function.uncurry velocity) (x, t)) :
    jointVorticityField velocity x t = vorticityField velocity x t := by
  have hjoint : DifferentiableAt ℝ (Function.uncurry velocity) (x, t) :=
    hvelocity.differentiableAt (by norm_num)
  have hslice := hjoint.hasFDerivAt.comp x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
  have hsliceFDeriv :
      fderiv ℝ (fun y => velocity y t) x =
        (fderiv ℝ (Function.uncurry velocity) (x, t)).comp spatialInclusion := by
    simpa [Function.comp_def, spatialInclusion] using hslice.fderiv
  unfold jointVorticityField vorticityField vorticityAt velocityJacobianAt
  change derivativeCurlLinearMap
      ((fderiv ℝ (Function.uncurry velocity) (x, t)).comp spatialInclusion) =
    derivativeCurlLinearMap (fderiv ℝ (fun y => velocity y t) x)
  rw [hsliceFDeriv]

/-- The two vorticity realizations coincide on every positive-time event of an admitted smooth
solution. -/
theorem smoothSolution_jointVorticityField_eq_vorticityField
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution nu initial force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    jointVorticityField velocity x t = vorticityField velocity x t := by
  apply jointVorticityField_eq_vorticityField_of_contDiffAt
  have hdomain : Set.univ ×ˢ Set.Ici (0 : ℝ) ∈ nhds (x, t) := by
    apply Filter.mem_of_superset (prod_mem_nhds Filter.univ_mem (Ioi_mem_nhds ht))
    rintro z ⟨_hzspace, hztime⟩
    exact ⟨Set.mem_univ z.1, show 0 ≤ z.2 from le_of_lt hztime⟩
  exact (solution.velocitySmooth.contDiffAt hdomain).of_le (by norm_num)

/-- Differentiation and the fixed curl receiver preserve every declared unit period. -/
theorem vorticityField_isOnePeriodic
    (velocity : VelocityField) (t : ℝ)
    (hperiodic : IsOnePeriodic (fun x => velocity x t)) :
    IsOnePeriodic (fun x => vorticityField velocity x t) := by
  intro x i
  unfold vorticityField vorticityAt velocityJacobianAt
  change derivativeCurlLinearMap
      (fderiv ℝ (fun y => velocity y t) (x + EuclideanSpace.single i 1)) =
    derivativeCurlLinearMap (fderiv ℝ (fun y => velocity y t) x)
  rw [fderiv_isOnePeriodic (fun y => velocity y t) hperiodic x i]

/-- A `C³` velocity slice has a `C²` vorticity slice. -/
theorem vorticityField_contDiff_two
    (velocity : VelocityField) (t : ℝ)
    (hvelocity : ContDiff ℝ 3 (fun x => velocity x t)) :
    ContDiff ℝ 2 (fun x => vorticityField velocity x t) := by
  unfold vorticityField vorticityAt velocityJacobianAt
  change ContDiff ℝ 2 (derivativeCurlLinearMap ∘ fderiv ℝ (fun x => velocity x t))
  exact derivativeCurlLinearMap.contDiff.comp
    (hvelocity.fderiv_right (by norm_num))

/-- A `C²` velocity slice has a `C¹` vorticity slice. -/
theorem vorticityField_contDiff_one
    (velocity : VelocityField) (t : ℝ)
    (hvelocity : ContDiff ℝ 2 (fun x => velocity x t)) :
    ContDiff ℝ 1 (fun x => vorticityField velocity x t) := by
  unfold vorticityField vorticityAt velocityJacobianAt
  change ContDiff ℝ 1 (derivativeCurlLinearMap ∘ fderiv ℝ (fun x => velocity x t))
  exact derivativeCurlLinearMap.contDiff.comp
    (hvelocity.fderiv_right (by norm_num))

/-- Joint vorticity is smooth throughout the open positive-time cylinder.  This is obtained by
restricting the joint derivative through a fixed spatial port and then applying the fixed curl
receiver. -/
theorem smoothSolution_jointVorticityField_contDiffOn_positiveTime
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution nu initial force velocity pressure) :
    ContDiffOn ℝ ∞ (Function.uncurry (jointVorticityField velocity))
      (Set.univ ×ˢ Set.Ioi (0 : ℝ)) := by
  let positiveCylinder : Set (Space × ℝ) := Set.univ ×ˢ Set.Ioi (0 : ℝ)
  have hopen : IsOpen positiveCylinder := isOpen_univ.prod isOpen_Ioi
  have hvelocity : ContDiffOn ℝ ∞ (Function.uncurry velocity) positiveCylinder := by
    apply solution.velocitySmooth.mono
    rintro ⟨x, t⟩ ⟨_hx, ht⟩
    exact ⟨Set.mem_univ x, show 0 ≤ t from ht.le⟩
  have hderivative : ContDiffOn ℝ ∞
      (fderiv ℝ (Function.uncurry velocity)) positiveCylinder :=
    hvelocity.fderiv_of_isOpen hopen (by simp)
  have hcurl := jointSpatialCurlLinearMap.contDiff.comp_contDiffOn hderivative
  apply hcurl.congr
  intro z hz
  rfl

/-- The actual slice-defined vorticity field is jointly smooth at positive time.  The proof uses
the exact equality of the joint-derivative and slice-derivative realizations, not a new curl
definition. -/
theorem smoothSolution_vorticityField_contDiffOn_positiveTime
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution nu initial force velocity pressure) :
    ContDiffOn ℝ ∞ (Function.uncurry (vorticityField velocity))
      (Set.univ ×ˢ Set.Ioi (0 : ℝ)) := by
  apply (smoothSolution_jointVorticityField_contDiffOn_positiveTime solution).congr
  rintro ⟨x, t⟩ ⟨_hx, ht⟩
  exact (smoothSolution_jointVorticityField_eq_vorticityField solution x t ht).symm

/-- Every periodic solution supplies a globally `C²` spatial vorticity slice at positive time. -/
theorem periodicSolution_vorticityField_contDiff_two
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    ContDiff ℝ 2 (fun x => vorticityField velocity x t) := by
  apply vorticityField_contDiff_two
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime velocity x t
    solution.velocitySmooth ht).of_le (WithTop.coe_le_coe.mpr le_top)

/-- Every periodic solution supplies a periodic spatial vorticity slice at positive time. -/
theorem periodicSolution_vorticityField_isOnePeriodic
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    IsOnePeriodic (fun x => vorticityField velocity x t) :=
  vorticityField_isOnePeriodic velocity t (solution.velocityPeriodic t ht.le)

/-- The actual positive-time vorticity slice remains in the divergence-free fibre. -/
theorem periodicSolution_divergence_vorticityField_eq_zero
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    divergence (fun y => vorticityField velocity y t) x = 0 :=
  smoothSolution_divergence_vorticityAt_eq_zero solution.toSmoothSolution x t ht

/-! ## Periodic cancellation of transported enstrophy -/

/-- Directional differentiation of half the squared norm.  Unlike the kinetic-energy specialization
already in `NavierStokesPeriodicEnergy`, the transporting direction is an independent field. -/
theorem inner_gradient_kineticEnergyDensity_direction
    (transport carried : InitialVelocity) (x : Space)
    (hcarried : DifferentiableAt ℝ carried x) :
    inner ℝ (gradient (kineticEnergyDensity carried) x) (transport x) =
      inner ℝ (fderiv ℝ carried x (transport x)) (carried x) := by
  have hnorm : DifferentiableAt ℝ (fun y => ‖carried y‖ ^ 2) x :=
    hcarried.norm_sq ℝ
  have henergy : DifferentiableAt ℝ (kineticEnergyDensity carried) x :=
    hnorm.const_mul (1 / 2 : ℝ)
  rw [inner_gradient_left]
  unfold kineticEnergyDensity
  rw [fderiv_const_mul hnorm (1 / 2 : ℝ)]
  rw [(hcarried.hasFDerivAt.norm_sq).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [innerSL_apply_apply]
  rw [real_inner_comm]
  ring

/-- Product rule for the enstrophy flux: transport work plus the divergence residue. -/
theorem divergence_kineticEnergyFlux_direction
    (transport carried : InitialVelocity) (x : Space)
    (htransport : DifferentiableAt ℝ transport x)
    (hcarried : DifferentiableAt ℝ carried x) :
    divergence (fun y => kineticEnergyDensity carried y • transport y) x =
      inner ℝ (fderiv ℝ carried x (transport x)) (carried x) +
        kineticEnergyDensity carried x * divergence transport x := by
  have henergy : DifferentiableAt ℝ (kineticEnergyDensity carried) x :=
    (hcarried.norm_sq ℝ).const_mul (1 / 2 : ℝ)
  rw [divergence_pressureFlux transport (kineticEnergyDensity carried) x
    htransport henergy, inner_gradient_kineticEnergyDensity_direction transport carried x hcarried]

/-- **Periodic incompressible transport does no net enstrophy work.**  Both the carrier and the
transporting velocity are kept explicit. -/
theorem integral_transportWork_unitCube_eq_zero
    (transport carried : InitialVelocity)
    (htransport : ContDiff ℝ 1 transport) (hcarried : ContDiff ℝ 1 carried)
    (htransportPeriodic : IsOnePeriodic transport)
    (hcarriedPeriodic : IsOnePeriodic carried)
    (htransportIncompressible : ∀ x, divergence transport x = 0) :
    ∫ x in unitCube,
      inner ℝ (fderiv ℝ carried x (transport x)) (carried x) = 0 := by
  have henergySmooth : ContDiff ℝ 1 (kineticEnergyDensity carried) := by
    unfold kineticEnergyDensity
    exact contDiff_const.mul (hcarried.norm_sq ℝ)
  have hfluxSmooth : ContDiff ℝ 1
      (fun x => kineticEnergyDensity carried x • transport x) :=
    henergySmooth.smul htransport
  have henergyPeriodic : IsOnePeriodic (kineticEnergyDensity carried) := by
    intro x i
    unfold kineticEnergyDensity
    rw [hcarriedPeriodic x i]
  have hfluxPeriodic : IsOnePeriodic
      (fun x => kineticEnergyDensity carried x • transport x) :=
    pressureFlux_isOnePeriodic transport (kineticEnergyDensity carried)
      htransportPeriodic henergyPeriodic
  have hfluxIntegral := integral_divergence_unitCube_eq_zero_of_onePeriodic
    (fun x => kineticEnergyDensity carried x • transport x) hfluxPeriodic hfluxSmooth
  have hcubeMeasurable : MeasurableSet unitCube := by
    exact measurableSet_Icc.preimage
      (EuclideanSpace.equiv (Fin 3) ℝ).continuous.measurable
  calc
    ∫ x in unitCube,
        inner ℝ (fderiv ℝ carried x (transport x)) (carried x) =
      ∫ x in unitCube,
        divergence (fun y => kineticEnergyDensity carried y • transport y) x := by
          apply setIntegral_congr_fun hcubeMeasurable
          intro x _hx
          rw [divergence_kineticEnergyFlux_direction transport carried x
            (htransport.differentiable (by norm_num) x)
            (hcarried.differentiable (by norm_num) x),
            htransportIncompressible x, mul_zero, add_zero]
    _ = 0 := hfluxIntegral

/-- The exact transport cancellation attached to a periodic solution's positive-time vorticity
slice. -/
theorem periodicSolution_integral_vorticityTransport_eq_zero
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    ∫ x in unitCube,
      inner ℝ
        (fderiv ℝ (fun y => vorticityField velocity y t) x (velocity x t))
        (vorticityField velocity x t) = 0 := by
  apply integral_transportWork_unitCube_eq_zero
  · rw [contDiff_iff_contDiffAt]
    intro x
    exact (spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime velocity x t
      solution.velocitySmooth ht).of_le (by norm_num)
  · exact (periodicSolution_vorticityField_contDiff_two solution t ht).of_le (by norm_num)
  · exact solution.velocityPeriodic t ht.le
  · exact periodicSolution_vorticityField_isOnePeriodic solution t ht
  · exact fun x => solution.incompressible x t ht.le

/-! ## Positive-time differentiation for a general smooth carried field -/

/-- A jointly smooth field on the open positive-time cylinder has a smooth spatial slice at every
positive time. -/
theorem positiveTimeSpatialSlice_contDiffAt
    (field : VelocityField) (x : Space) (t : ℝ) (ht : 0 < t)
    (hfield : ContDiffOn ℝ ∞ (Function.uncurry field)
      (Set.univ ×ˢ Set.Ioi (0 : ℝ))) :
    ContDiffAt ℝ ∞ (fun y => field y t) x := by
  have hdomain : Set.univ ×ˢ Set.Ioi (0 : ℝ) ∈ nhds (x, t) := by
    exact prod_mem_nhds Filter.univ_mem (Ioi_mem_nhds ht)
  have huncurry := hfield.contDiffAt hdomain
  have hpair : ContDiffAt ℝ ∞ (fun y : Space => (y, t)) x :=
    contDiffAt_id.prodMk contDiffAt_const
  simpa [Function.comp_def] using huncurry.comp x hpair

/-- The Eulerian time jet of a jointly smooth positive-time field is continuous across every
positive-time spatial slice. -/
theorem eulerianTimeJet_continuous_of_contDiffOn_positiveTime
    (field : VelocityField)
    (hfield : ContDiffOn ℝ ∞ (Function.uncurry field)
      (Set.univ ×ˢ Set.Ioi (0 : ℝ)))
    (t : ℝ) (ht : 0 < t) :
    Continuous (fun x => eulerianTimeJet field x t) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hdomain : Set.univ ×ˢ Set.Ioi (0 : ℝ) ∈ nhds (x, t) :=
    prod_mem_nhds Filter.univ_mem (Ioi_mem_nhds ht)
  have hjoint : ContDiffAt ℝ ∞ (Function.uncurry field) (x, t) :=
    hfield.contDiffAt hdomain
  have hjetAt : ContinuousAt
      (fun z => fderiv ℝ (Function.uncurry field) z (0, 1)) (x, t) :=
    (hjoint.continuousAt_fderiv (by simp)).clm_apply continuousAt_const
  have hpair : ContinuousAt (fun y : Space => (y, t)) x :=
    continuousAt_id.prodMk continuousAt_const
  simpa [eulerianTimeJet, Function.comp_def] using hjetAt.comp_of_eq hpair rfl

/-- Pointwise differentiation of half the squared norm for any jointly smooth positive-time
field. -/
theorem hasDerivAt_kineticEnergyDensity_time_of_contDiffOn_positiveTime
    (field : VelocityField)
    (hfield : ContDiffOn ℝ ∞ (Function.uncurry field)
      (Set.univ ×ˢ Set.Ioi (0 : ℝ)))
    (x : Space) (t : ℝ) (ht : 0 < t) :
    HasDerivAt
      (fun τ => kineticEnergyDensity (fun y => field y τ) x)
      (inner ℝ (eulerianTimeJet field x t) (field x t)) t := by
  have hdomain : Set.univ ×ˢ Set.Ioi (0 : ℝ) ∈ nhds (x, t) :=
    prod_mem_nhds Filter.univ_mem (Ioi_mem_nhds ht)
  have hjoint : DifferentiableAt ℝ (Function.uncurry field) (x, t) :=
    (hfield.contDiffAt hdomain).differentiableAt (by simp)
  have htime := hjoint.hasFDerivAt.comp t
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t)
  have hfieldTime : HasDerivAt (field x) (eulerianTimeJet field x t) t := by
    simpa [eulerianTimeJet, Function.comp_def] using htime.hasDerivAt
  have hnorm := hfieldTime.norm_sq.const_mul (1 / 2 : ℝ)
  simpa [kineticEnergyDensity, real_inner_comm] using hnorm

/-- **Differentiation of the unit-cube quadratic receiver for a general positive-time smooth
field.**

Compactness of one unit cube times a closed time interval supplies the domination needed to
interchange derivative and integral.  No periodicity or solution equation is used; the receiver
becomes one spatial period only after the periodic-solution attachment below. -/
theorem hasDerivAt_periodicKineticEnergy_eq_timeWork_of_contDiffOn_positiveTime
    (field : VelocityField)
    (hfield : ContDiffOn ℝ ∞ (Function.uncurry field)
      (Set.univ ×ˢ Set.Ioi (0 : ℝ)))
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (periodicKineticEnergy field)
      (∫ x in unitCube, inner ℝ (eulerianTimeJet field x t) (field x t)) t := by
  let timeSet : Set ℝ := Ioo (t / 2) (3 * t / 2)
  let timeCompact : Set ℝ := Icc (t / 2) (3 * t / 2)
  let positiveCylinder : Set (Space × ℝ) := Set.univ ×ˢ Ioi (0 : ℝ)
  let compactCylinder : Set (Space × ℝ) := unitCube ×ˢ timeCompact
  have htimeSet : timeSet ∈ nhds t := by
    simpa [timeSet] using (Ioo_mem_nhds (by linarith : t / 2 < t)
      (by linarith : t < 3 * t / 2))
  have hjointJetContinuous : ContinuousOn
      (fun z : Space × ℝ =>
        fderiv ℝ (Function.uncurry field) z (0, 1)) positiveCylinder := by
    have hfd : ContinuousOn (fderiv ℝ (Function.uncurry field)) positiveCylinder :=
      hfield.continuousOn_fderiv_of_isOpen (isOpen_univ.prod isOpen_Ioi)
        (WithTop.coe_le_coe.mpr le_top)
    exact hfd.clm_apply continuousOn_const
  have hjointWorkContinuous : ContinuousOn
      (fun z : Space × ℝ =>
        inner ℝ (eulerianTimeJet field z.1 z.2) (field z.1 z.2))
      positiveCylinder := by
    exact hjointJetContinuous.inner hfield.continuousOn
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have hcompactCylinder : IsCompact compactCylinder := hcubeCompact.prod isCompact_Icc
  have hcompactSubset : compactCylinder ⊆ positiveCylinder := by
    rintro ⟨x, τ⟩ ⟨hx, hτ⟩
    exact ⟨Set.mem_univ x, lt_of_lt_of_le (half_pos ht) hτ.1⟩
  have hworkNormContinuous : ContinuousOn
      (fun z : Space × ℝ =>
        ‖inner ℝ (eulerianTimeJet field z.1 z.2) (field z.1 z.2)‖)
      compactCylinder :=
    (hjointWorkContinuous.mono hcompactSubset).norm
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (hcompactCylinder.bddAbove_image hworkNormContinuous)
  have hFmeas : ∀ᶠ τ in nhds t, AEStronglyMeasurable
      (fun x => kineticEnergyDensity (fun y => field y τ) x)
      (volume.restrict unitCube) := by
    filter_upwards [Ioi_mem_nhds ht] with τ hτ
    have hslice : ContDiff ℝ ∞ (fun x => field x τ) := by
      rw [contDiff_iff_contDiffAt]
      intro x
      exact positiveTimeSpatialSlice_contDiffAt field x τ hτ hfield
    exact (contDiff_const.mul (hslice.norm_sq ℝ)).continuous.aestronglyMeasurable
  have hFint : Integrable
      (fun x => kineticEnergyDensity (fun y => field y t) x)
      (volume.restrict unitCube) := by
    have hslice : ContDiff ℝ ∞ (fun x => field x t) := by
      rw [contDiff_iff_contDiffAt]
      intro x
      exact positiveTimeSpatialSlice_contDiffAt field x t ht hfield
    exact (contDiff_const.mul (hslice.norm_sq ℝ)).continuous.continuousOn
      |>.integrableOn_compact hcubeCompact
  have hF'meas : AEStronglyMeasurable
      (fun x => inner ℝ (eulerianTimeJet field x t) (field x t))
      (volume.restrict unitCube) := by
    have hslice : ContDiff ℝ ∞ (fun x => field x t) := by
      rw [contDiff_iff_contDiffAt]
      intro x
      exact positiveTimeSpatialSlice_contDiffAt field x t ht hfield
    exact ((eulerianTimeJet_continuous_of_contDiffOn_positiveTime field hfield t ht).inner
      hslice.continuous).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume.restrict unitCube), ∀ τ ∈ timeSet,
      ‖inner ℝ (eulerianTimeJet field x τ) (field x τ)‖ ≤ C := by
    filter_upwards [ae_restrict_mem hcubeMeasurable] with x hx
    intro τ hτ
    apply hC
    refine ⟨(x, τ), ?_, rfl⟩
    exact ⟨hx, hτ.1.le, hτ.2.le⟩
  have hboundIntegrable : Integrable (fun _ : Space => C)
      (volume.restrict unitCube) :=
    integrableOn_const hcubeCompact.measure_lt_top.ne
  have hdiff : ∀ᵐ x ∂(volume.restrict unitCube), ∀ τ ∈ timeSet,
      HasDerivAt
        (fun σ => kineticEnergyDensity (fun y => field y σ) x)
        (inner ℝ (eulerianTimeJet field x τ) (field x τ)) τ := by
    filter_upwards with x
    intro τ hτ
    apply hasDerivAt_kineticEnergyDensity_time_of_contDiffOn_positiveTime
      field hfield x τ
    exact lt_trans (half_pos ht) hτ.1
  convert (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun τ x => kineticEnergyDensity (fun y => field y τ) x)
      (F' := fun τ x => inner ℝ (eulerianTimeJet field x τ) (field x τ))
      (bound := fun _ : Space => C) (x₀ := t) (s := timeSet)
      (μ := volume.restrict unitCube)
      htimeSet hFmeas hFint hF'meas hbound hboundIntegrable hdiff).2 using 1 <;>
    rfl

/-- The unit-cube receiver for half the squared vorticity.  It is a one-period enstrophy only when
paired with the periodicity testimony supplied by `PeriodicSolution`. -/
def periodicEnstrophy (velocity : VelocityField) (t : ℝ) : ℝ :=
  periodicKineticEnergy (vorticityField velocity) t

/-- The periodic enstrophy derivative before applying the vorticity equation. -/
theorem periodicSolution_hasDerivAt_periodicEnstrophy_eq_timeWork
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (periodicEnstrophy velocity)
      (∫ x in unitCube,
        inner ℝ (eulerianTimeJet (vorticityField velocity) x t)
          (vorticityField velocity x t)) t := by
  convert hasDerivAt_periodicKineticEnergy_eq_timeWork_of_contDiffOn_positiveTime
      (vorticityField velocity)
      (smoothSolution_vorticityField_contDiffOn_positiveTime solution.toSmoothSolution) t ht
    using 1 <;> rfl

/-! ## The vorticity equation port and its integrated consequence -/

/-- The exact curled-momentum receipt at a fixed time, before expanding the nonlinear curl.  Its
left time-curl square requires mixed space--time derivative symmetry, and its viscous square
requires curl to commute with the vector Laplacian.  `NavierStokesCurlCommutation` derives both and
constructs this receipt from `SmoothSolution`.  The nonlinear square is *not* assumed here; it is
composed from the existing `smoothSolution_vorticityAt_advection` theorem below, where stretching
is derived. -/
structure HasPointwiseVorticityBalanceAt
    (nu : ℝ) (force velocity : VelocityField) (t : ℝ) : Prop where
  /-- `C²` admission makes the totalized force curl an actual continuous spatial derivative and
  supplies its compact-cube integrability. -/
  forceSpatialSmooth : ContDiff ℝ 2 (fun x => force x t)
  curledMomentum : ∀ x,
    eulerianTimeJet (vorticityField velocity) x t +
        vorticityAt
          (fun y => fderiv ℝ (fun z => velocity z t) y (velocity y t)) x =
      nu • Δ (fun y => vorticityField velocity y t) x +
        vorticityField force x t

/-- **Stretching derived from the actual nonlinear curl square.**  Composing the curled-momentum
receipt with the admitted positive-time identity
`curl ((u · ∇)u) = (u · ∇)ω - (ω · ∇)u` returns the expanded pointwise vorticity equation. -/
theorem pointwiseVorticityBalance
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t)
    (hbalance : HasPointwiseVorticityBalanceAt nu force velocity t)
    (x : Space) :
    eulerianTimeJet (vorticityField velocity) x t +
        fderiv ℝ (fun y => vorticityField velocity y t) x (velocity x t) =
      fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t) +
        nu • Δ (fun y => vorticityField velocity y t) x +
          vorticityField force x t := by
  have hnonlinear := smoothSolution_vorticityAt_advection solution x t ht
  have hcurled := hbalance.curledMomentum x
  change vorticityAt
      (fun y => fderiv ℝ (fun z => velocity z t) y (velocity y t)) x =
    fderiv ℝ (fun y => vorticityField velocity y t) x (velocity x t) -
      fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t) at hnonlinear
  rw [hnonlinear] at hcurled
  calc
    eulerianTimeJet (vorticityField velocity) x t +
        fderiv ℝ (fun y => vorticityField velocity y t) x (velocity x t) =
      (eulerianTimeJet (vorticityField velocity) x t +
          (fderiv ℝ (fun y => vorticityField velocity y t) x (velocity x t) -
            fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t))) +
        fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t) := by abel
    _ = (nu • Δ (fun y => vorticityField velocity y t) x +
          vorticityField force x t) +
        fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t) := by
          rw [hcurled]
    _ = fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t) +
        nu • Δ (fun y => vorticityField velocity y t) x +
          vorticityField force x t := by abel

/-- The pointwise balance read against vorticity.  This is where the three-dimensional stretching
population enters enstrophy evolution. -/
theorem pointwiseVorticityBalance_inner
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {t : ℝ}
    (solution : SmoothSolution nu initial force velocity pressure)
    (ht : 0 < t)
    (hbalance : HasPointwiseVorticityBalanceAt nu force velocity t)
    (x : Space) :
    inner ℝ (eulerianTimeJet (vorticityField velocity) x t)
        (vorticityField velocity x t) +
      inner ℝ
        (fderiv ℝ (fun y => vorticityField velocity y t) x (velocity x t))
        (vorticityField velocity x t) =
    inner ℝ
        (fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t))
        (vorticityField velocity x t) +
      nu * inner ℝ (Δ (fun y => vorticityField velocity y t) x)
        (vorticityField velocity x t) +
      inner ℝ (vorticityField force x t) (vorticityField velocity x t) := by
  have hread := congrArg
    (fun z : Space => inner ℝ z (vorticityField velocity x t))
    (pointwiseVorticityBalance solution t ht hbalance x)
  simpa [inner_add_left, real_inner_smul_left] using hread

/-- Viscous vorticity work is exactly minus the component-gradient-square population over one
period. -/
theorem periodicSolution_integral_vorticityLaplacian_eq_neg_dissipation
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    ∫ x in unitCube,
      inner ℝ (Δ (fun y => vorticityField velocity y t) x)
        (vorticityField velocity x t) =
      -∫ x in unitCube, ∑ i : Fin 3,
        ‖gradient (fun y => vorticityField velocity y t i) x‖ ^ 2 := by
  apply integral_inner_laplacian_eq_neg_integral_component_gradient_sq
  · exact periodicSolution_vorticityField_contDiff_two solution t ht
  · exact periodicSolution_vorticityField_isOnePeriodic solution t ht

/-- The totalized scalar receiver for the component-gradient-square integrand.  It is admitted as
a physical dissipation population only together with the integrability receipt proved below for
positive-time periodic solutions. -/
def periodicVorticityDissipation (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∫ x in unitCube, ∑ i : Fin 3,
    ‖gradient (fun y => vorticityField velocity y t i) x‖ ^ 2

/-- The totalized scalar receiver for signed three-dimensional vortex-stretching work.  The
positive-time solution theorem below supplies its compact-cube integrability. -/
def periodicVortexStretching (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∫ x in unitCube,
    inner ℝ
      (fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t))
      (vorticityField velocity x t)

/-- The totalized scalar receiver for curl-forcing work.  A
`HasPointwiseVorticityBalanceAt.forceSpatialSmooth` receipt admits its derivative and
integrability in the enstrophy theorem below. -/
def periodicCurlForcingWork
    (force velocity : VelocityField) (t : ℝ) : ℝ :=
  ∫ x in unitCube,
    inner ℝ (vorticityField force x t) (vorticityField velocity x t)

/-- The algebraic scalar assembled from the three totalized unit-cube receivers.  The solution
theorem below supplies the periodicity, integrability, and positive-time derivative attachment. -/
def periodicEnstrophyRate
    (nu : ℝ) (force velocity : VelocityField) (t : ℝ) : ℝ :=
  -nu * periodicVorticityDissipation velocity t +
    periodicVortexStretching velocity t +
      periodicCurlForcingWork force velocity t

/-- The component-gradient-square integrand is integrable for every admitted positive-time
periodic solution occurrence. -/
theorem periodicSolution_vorticityDissipation_integrable
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun x => ∑ i : Fin 3,
      ‖gradient (fun y => vorticityField velocity y t i) x‖ ^ 2) unitCube := by
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have homega : ContDiff ℝ 2 (fun x => vorticityField velocity x t) :=
    periodicSolution_vorticityField_contDiff_two solution t ht
  have hcomponent : ∀ i : Fin 3,
      ContDiff ℝ 2 (fun x => vorticityField velocity x t i) := by
    intro i
    simpa [Function.comp_def] using (EuclideanSpace.proj i).contDiff.comp homega
  have hintegrand : Continuous (fun x => ∑ i : Fin 3,
      ‖gradient (fun y => vorticityField velocity y t i) x‖ ^ 2) := by
    apply continuous_finset_sum
    intro i _hi
    exact (gradient_contDiff_one _ (hcomponent i)).norm_sq ℝ |>.continuous
  exact hintegrand.continuousOn.integrableOn_compact hcubeCompact

/-- With explicit integrability testimony, the dissipation receiver is nonnegative.  This theorem
does not assign a sign to either stretching or curl-forcing work. -/
theorem periodicVorticityDissipation_nonneg
    (velocity : VelocityField) (t : ℝ)
    (_hintegrable : IntegrableOn (fun x => ∑ i : Fin 3,
      ‖gradient (fun y => vorticityField velocity y t i) x‖ ^ 2) unitCube) :
    0 ≤ periodicVorticityDissipation velocity t := by
  unfold periodicVorticityDissipation
  apply integral_nonneg_of_ae
  filter_upwards with x
  exact Finset.sum_nonneg fun i _hi => sq_nonneg _

/-- The nonnegativity receipt attached to an admitted positive-time periodic solution. -/
theorem periodicSolution_periodicVorticityDissipation_nonneg
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    0 ≤ periodicVorticityDissipation velocity t :=
  periodicVorticityDissipation_nonneg velocity t
    (periodicSolution_vorticityDissipation_integrable solution t ht)

/-- **The integrated forced periodic enstrophy identity.**

Every regularity and integrability input other than the pointwise vorticity balance is derived from
the admitted periodic smooth solution.  In particular, curl-forcing work is proved integrable from
the balance itself and the other smooth terms; it is not silently totalized away. -/
theorem periodicSolution_integral_vorticityTimeWork_eq_enstrophyRate
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t)
    (hbalance : HasPointwiseVorticityBalanceAt nu force velocity t) :
    ∫ x in unitCube,
      inner ℝ (eulerianTimeJet (vorticityField velocity) x t)
        (vorticityField velocity x t) =
      periodicEnstrophyRate nu force velocity t := by
  let u : InitialVelocity := fun x => velocity x t
  let omega : InitialVelocity := fun x => vorticityField velocity x t
  let curlForce : InitialVelocity := fun x => vorticityField force x t
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have hu : ContDiff ℝ ∞ u := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime velocity x t
      solution.velocitySmooth ht
  have homega : ContDiff ℝ 2 omega :=
    periodicSolution_vorticityField_contDiff_two solution t ht
  have homegaOne : ContDiff ℝ 1 omega := homega.of_le (by norm_num)
  have htimeContinuous : Continuous (fun x =>
      inner ℝ (eulerianTimeJet (vorticityField velocity) x t) (omega x)) :=
    (eulerianTimeJet_continuous_of_contDiffOn_positiveTime
      (vorticityField velocity)
      (smoothSolution_vorticityField_contDiffOn_positiveTime solution.toSmoothSolution)
      t ht).inner homega.continuous
  have htransportContinuous : Continuous (fun x =>
      inner ℝ (fderiv ℝ omega x (u x)) (omega x)) := by
    have htransported : Continuous (fun x => fderiv ℝ omega x (u x)) :=
      (homega.continuous_fderiv_apply (by norm_num)).comp
        (continuous_id.prodMk hu.continuous)
    exact htransported.inner homega.continuous
  have hstretchingContinuous : Continuous (fun x =>
      inner ℝ (fderiv ℝ u x (omega x)) (omega x)) := by
    have hstretched : Continuous (fun x => fderiv ℝ u x (omega x)) :=
      (hu.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk homega.continuous)
    exact hstretched.inner homega.continuous
  have htimeInt : IntegrableOn (fun x =>
      inner ℝ (eulerianTimeJet (vorticityField velocity) x t) (omega x)) unitCube :=
    htimeContinuous.continuousOn.integrableOn_compact hcubeCompact
  have htransportInt : IntegrableOn (fun x =>
      inner ℝ (fderiv ℝ omega x (u x)) (omega x)) unitCube :=
    htransportContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hstretchingInt : IntegrableOn (fun x =>
      inner ℝ (fderiv ℝ u x (omega x)) (omega x)) unitCube :=
    hstretchingContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hviscousInt : IntegrableOn (fun x =>
      inner ℝ (Δ omega x) (omega x)) unitCube :=
    integrableOn_inner_laplacian_unitCube omega homega
  have hforceInt : IntegrableOn (fun x =>
      inner ℝ (curlForce x) (omega x)) unitCube := by
    have hcurlForce : ContDiff ℝ 1 curlForce :=
      vorticityField_contDiff_one force t hbalance.forceSpatialSmooth
    exact (hcurlForce.continuous.inner homega.continuous).continuousOn
      |>.integrableOn_compact hcubeCompact
  have hintegrated :
      (∫ x in unitCube,
        inner ℝ (eulerianTimeJet (vorticityField velocity) x t) (omega x)) +
        ∫ x in unitCube, inner ℝ (fderiv ℝ omega x (u x)) (omega x) =
      (∫ x in unitCube,
        inner ℝ (fderiv ℝ u x (omega x)) (omega x)) +
        nu * (∫ x in unitCube, inner ℝ (Δ omega x) (omega x)) +
          ∫ x in unitCube, inner ℝ (curlForce x) (omega x) := by
    calc
      (∫ x in unitCube,
          inner ℝ (eulerianTimeJet (vorticityField velocity) x t) (omega x)) +
          ∫ x in unitCube, inner ℝ (fderiv ℝ omega x (u x)) (omega x) =
        ∫ x in unitCube,
          (inner ℝ (eulerianTimeJet (vorticityField velocity) x t) (omega x) +
            inner ℝ (fderiv ℝ omega x (u x)) (omega x)) :=
              (integral_add htimeInt htransportInt).symm
      _ = ∫ x in unitCube,
          ((inner ℝ (fderiv ℝ u x (omega x)) (omega x) +
              nu * inner ℝ (Δ omega x) (omega x)) +
            inner ℝ (curlForce x) (omega x)) := by
              apply setIntegral_congr_fun hcubeMeasurable
              intro x _hx
              exact pointwiseVorticityBalance_inner solution.toSmoothSolution ht hbalance x
      _ = (∫ x in unitCube,
          (inner ℝ (fderiv ℝ u x (omega x)) (omega x) +
            nu * inner ℝ (Δ omega x) (omega x))) +
          ∫ x in unitCube, inner ℝ (curlForce x) (omega x) :=
            integral_add (hstretchingInt.add (hviscousInt.const_mul nu)) hforceInt
      _ = ((∫ x in unitCube,
          inner ℝ (fderiv ℝ u x (omega x)) (omega x)) +
          ∫ x in unitCube, nu * inner ℝ (Δ omega x) (omega x)) +
          ∫ x in unitCube, inner ℝ (curlForce x) (omega x) := by
            rw [integral_add hstretchingInt (hviscousInt.const_mul nu)]
      _ = (∫ x in unitCube,
          inner ℝ (fderiv ℝ u x (omega x)) (omega x)) +
          nu * (∫ x in unitCube, inner ℝ (Δ omega x) (omega x)) +
          ∫ x in unitCube, inner ℝ (curlForce x) (omega x) := by
            rw [integral_const_mul]
  have htransportZero := periodicSolution_integral_vorticityTransport_eq_zero solution t ht
  have hviscous :=
    periodicSolution_integral_vorticityLaplacian_eq_neg_dissipation solution t ht
  change (∫ x in unitCube,
      inner ℝ (eulerianTimeJet (vorticityField velocity) x t)
        (vorticityField velocity x t)) = _
  change (∫ x in unitCube,
      inner ℝ (eulerianTimeJet (vorticityField velocity) x t)
        (vorticityField velocity x t)) +
      (∫ x in unitCube,
        inner ℝ
          (fderiv ℝ (fun y => vorticityField velocity y t) x (velocity x t))
          (vorticityField velocity x t)) =
    (∫ x in unitCube,
      inner ℝ
        (fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t))
        (vorticityField velocity x t)) +
      nu * (∫ x in unitCube,
        inner ℝ (Δ (fun y => vorticityField velocity y t) x)
          (vorticityField velocity x t)) +
      ∫ x in unitCube,
        inner ℝ (vorticityField force x t) (vorticityField velocity x t) at hintegrated
  rw [htransportZero, hviscous] at hintegrated
  unfold periodicEnstrophyRate periodicVorticityDissipation periodicVortexStretching
    periodicCurlForcingWork
  linarith

/-- **The complete conditional forced periodic enstrophy equality at positive time.**  The only
extra input beyond `PeriodicSolution` is the visibly named pointwise vorticity-balance attachment. -/
theorem periodicSolution_hasDerivAt_periodicEnstrophy
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t)
    (hbalance : HasPointwiseVorticityBalanceAt nu force velocity t) :
    HasDerivAt (periodicEnstrophy velocity)
      (periodicEnstrophyRate nu force velocity t) t := by
  have hderivative := periodicSolution_hasDerivAt_periodicEnstrophy_eq_timeWork
    solution t ht
  rw [periodicSolution_integral_vorticityTimeWork_eq_enstrophyRate
    solution t ht hbalance] at hderivative
  exact hderivative

/-! ## The exact a priori closure obstruction -/

/-- For nonnegative viscosity, the admitted positive-time solution has nonnegative viscous
dissipation coefficient times population. -/
theorem periodicSolution_viscousVorticityDissipation_nonneg
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) (hnu : 0 ≤ nu) :
    0 ≤ nu * periodicVorticityDissipation velocity t :=
  mul_nonneg hnu
    (periodicSolution_periodicVorticityDissipation_nonneg solution t ht)

/-- With nonnegative viscosity, the algebraic rate is nonpositive exactly when the `nu D` term
absorbs the combined stretching and curl-forcing receivers.  Physical interpretation additionally
uses the periodic-solution integrability attachments; the enstrophy identity proves the inequality
on neither side automatically. -/
theorem periodicEnstrophyRate_nonpos_iff_stretching_forcing_absorbed
    (nu : ℝ) (force velocity : VelocityField) (t : ℝ) (_hnu : 0 ≤ nu) :
    periodicEnstrophyRate nu force velocity t ≤ 0 ↔
      periodicVortexStretching velocity t +
          periodicCurlForcingWork force velocity t ≤
        nu * periodicVorticityDissipation velocity t := by
  unfold periodicEnstrophyRate
  constructor <;> intro h <;> linarith

/-- On an admitted balance, nonincrease of actual periodic enstrophy has exactly the same
stretching-absorption obstruction. -/
theorem periodicSolution_deriv_periodicEnstrophy_nonpos_iff
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) (hnu : 0 ≤ nu)
    (hbalance : HasPointwiseVorticityBalanceAt nu force velocity t) :
    deriv (periodicEnstrophy velocity) t ≤ 0 ↔
      periodicVortexStretching velocity t +
          periodicCurlForcingWork force velocity t ≤
        nu * periodicVorticityDissipation velocity t := by
  have hderivative := periodicSolution_hasDerivAt_periodicEnstrophy
    solution t ht hbalance
  rw [hderivative.deriv]
  exact periodicEnstrophyRate_nonpos_iff_stretching_forcing_absorbed
    nu force velocity t hnu

/-- At an admitted differentiable velocity occurrence, pointwise stretching is controlled by the
operator norm of the actual velocity Jacobian times vorticity squared.  Closing this receiver still
requires spacetime control of that Jacobian (or a stronger scale-critical substitute); kinetic
energy alone supplies no such theorem here. -/
theorem abs_vortexStretching_le_jacobianNorm_mul_vorticityNormSq
    (velocity : VelocityField) (x : Space) (t : ℝ)
    (_hadmitted : DifferentiableAt ℝ (fun y => velocity y t) x) :
    |inner ℝ
        (fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t))
        (vorticityField velocity x t)| ≤
      ‖fderiv ℝ (fun y => velocity y t) x‖ *
        ‖vorticityField velocity x t‖ ^ 2 := by
  calc
    |inner ℝ
        (fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t))
        (vorticityField velocity x t)| ≤
      ‖fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t)‖ *
        ‖vorticityField velocity x t‖ :=
          abs_real_inner_le_norm _ _
    _ ≤ (‖fderiv ℝ (fun y => velocity y t) x‖ *
          ‖vorticityField velocity x t‖) *
        ‖vorticityField velocity x t‖ := by
          gcongr
          exact (fderiv ℝ (fun y => velocity y t) x).le_opNorm _
    _ = ‖fderiv ℝ (fun y => velocity y t) x‖ *
        ‖vorticityField velocity x t‖ ^ 2 := by ring

/-- The admitted stretching bound attached to every positive-time periodic-solution event. -/
theorem periodicSolution_abs_vortexStretching_le_jacobianNorm_mul_vorticityNormSq
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    |inner ℝ
        (fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t))
        (vorticityField velocity x t)| ≤
      ‖fderiv ℝ (fun y => velocity y t) x‖ *
        ‖vorticityField velocity x t‖ ^ 2 :=
  abs_vortexStretching_le_jacobianNorm_mul_vorticityNormSq velocity x t
    (smoothSolution_velocitySlice_differentiableAt solution.toSmoothSolution x t ht)

end Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
