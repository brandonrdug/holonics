import ElementaryHolonics.Millennium.NavierStokesFiniteTimeVorticity

/-!
# Finite-time periodic enstrophy

The pointwise finite-slab vorticity balance is integrated on the periodic cube here.  Joint
smoothness on the open slab justifies differentiation under the integral, and the periodic return
cancels transport and identifies viscous work with negative dissipation.  The terminal continuation
question remains outside this owner.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Real Set
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesVorticity

/-! ## Differentiating the finite-interval quadratic receiver -/

/-- The Eulerian time jet of a jointly smooth interior field is spatially continuous. -/
theorem eulerianTimeJet_continuous_of_contDiffOn_openSlab
    {T : ℝ} (field : VelocityField)
    (hfield : ContDiffOn ℝ ∞ (Function.uncurry field) (openSpaceTimeSlab T))
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    Continuous (fun x => eulerianTimeJet field x t) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hjoint : ContDiffAt ℝ ∞ (Function.uncurry field) (x, t) :=
    hfield.contDiffAt
      (prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht0 htT))
  have hjetAt : ContinuousAt
      (fun z => fderiv ℝ (Function.uncurry field) z (0, 1)) (x, t) :=
    (hjoint.continuousAt_fderiv (by simp)).clm_apply continuousAt_const
  have hpair : ContinuousAt (fun y : Space => (y, t)) x :=
    continuousAt_id.prodMk continuousAt_const
  simpa [eulerianTimeJet, Function.comp_def] using hjetAt.comp_of_eq hpair rfl

/-- Pointwise differentiation of the quadratic density on an open finite slab. -/
theorem hasDerivAt_kineticEnergyDensity_time_of_contDiffOn_openSlab
    {T : ℝ} (field : VelocityField)
    (hfield : ContDiffOn ℝ ∞ (Function.uncurry field) (openSpaceTimeSlab T))
    (x : Space) {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt
      (fun τ => kineticEnergyDensity (fun y => field y τ) x)
      (inner ℝ (eulerianTimeJet field x t) (field x t)) t := by
  have hjoint : DifferentiableAt ℝ (Function.uncurry field) (x, t) :=
    (hfield.contDiffAt
      (prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht0 htT)))
      |>.differentiableAt (by simp)
  have htime := hjoint.hasFDerivAt.comp t
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t)
  have hfieldTime : HasDerivAt (field x) (eulerianTimeJet field x t) t := by
    simpa [eulerianTimeJet, Function.comp_def] using htime.hasDerivAt
  have hnorm := hfieldTime.norm_sq.const_mul (1 / 2 : ℝ)
  simpa [kineticEnergyDensity, real_inner_comm] using hnorm

/-- Differentiation under the unit-cube integral for a jointly smooth field on `0 < t < T`. -/
theorem hasDerivAt_periodicKineticEnergy_eq_timeWork_of_contDiffOn_openSlab
    {T : ℝ} (field : VelocityField)
    (hfield : ContDiffOn ℝ ∞ (Function.uncurry field) (openSpaceTimeSlab T))
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (periodicKineticEnergy field)
      (∫ x in unitCube, inner ℝ (eulerianTimeJet field x t) (field x t)) t := by
  let lower : ℝ := t / 2
  let upper : ℝ := (t + T) / 2
  let timeSet : Set ℝ := Ioo lower upper
  let timeCompact : Set ℝ := Icc lower upper
  let compactCylinder : Set (Space × ℝ) := unitCube ×ˢ timeCompact
  have hlower0 : 0 < lower := by dsimp [lower]; linarith
  have htupper : t < upper := by dsimp [upper]; linarith
  have hupperT : upper < T := by dsimp [upper]; linarith
  have htimeSet : timeSet ∈ nhds t := by
    apply Ioo_mem_nhds <;> dsimp [timeSet, lower, upper] <;> linarith
  have hjointJetContinuous : ContinuousOn
      (fun z : Space × ℝ => fderiv ℝ (Function.uncurry field) z (0, 1))
      (openSpaceTimeSlab T) := by
    have hfd : ContinuousOn (fderiv ℝ (Function.uncurry field))
        (openSpaceTimeSlab T) :=
      hfield.continuousOn_fderiv_of_isOpen (isOpen_univ.prod isOpen_Ioo)
        (WithTop.coe_le_coe.mpr le_top)
    exact hfd.clm_apply continuousOn_const
  have hjointWorkContinuous : ContinuousOn
      (fun z : Space × ℝ =>
        inner ℝ (eulerianTimeJet field z.1 z.2) (field z.1 z.2))
      (openSpaceTimeSlab T) :=
    hjointJetContinuous.inner hfield.continuousOn
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have hcompactCylinder : IsCompact compactCylinder := hcubeCompact.prod isCompact_Icc
  have hcompactSubset : compactCylinder ⊆ openSpaceTimeSlab T := by
    rintro ⟨x, τ⟩ ⟨hx, hτ⟩
    exact ⟨Set.mem_univ x, lt_of_lt_of_le hlower0 hτ.1,
      lt_of_le_of_lt hτ.2 hupperT⟩
  have hworkNormContinuous : ContinuousOn
      (fun z : Space × ℝ =>
        ‖inner ℝ (eulerianTimeJet field z.1 z.2) (field z.1 z.2)‖)
      compactCylinder := (hjointWorkContinuous.mono hcompactSubset).norm
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (hcompactCylinder.bddAbove_image hworkNormContinuous)
  have hFmeas : ∀ᶠ τ in nhds t, AEStronglyMeasurable
      (fun x => kineticEnergyDensity (fun y => field y τ) x)
      (volume.restrict unitCube) := by
    filter_upwards [Ioo_mem_nhds ht0 htT] with τ hτ
    have hslice : ContDiff ℝ ∞ (fun x => field x τ) := by
      rw [contDiff_iff_contDiffAt]
      intro x
      have hjoint : ContDiffAt ℝ ∞ (Function.uncurry field) (x, τ) :=
        hfield.contDiffAt
          (prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds hτ.1 hτ.2))
      simpa [Function.comp_def] using
        hjoint.comp x (contDiffAt_id.prodMk contDiffAt_const)
    exact (contDiff_const.mul (hslice.norm_sq ℝ)).continuous.aestronglyMeasurable
  have hslice : ContDiff ℝ ∞ (fun x => field x t) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    have hjoint : ContDiffAt ℝ ∞ (Function.uncurry field) (x, t) :=
      hfield.contDiffAt
        (prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht0 htT))
    simpa [Function.comp_def] using
      hjoint.comp x (contDiffAt_id.prodMk contDiffAt_const)
  have hFint : Integrable
      (fun x => kineticEnergyDensity (fun y => field y t) x)
      (volume.restrict unitCube) :=
    (contDiff_const.mul (hslice.norm_sq ℝ)).continuous.continuousOn
      |>.integrableOn_compact hcubeCompact
  have hF'meas : AEStronglyMeasurable
      (fun x => inner ℝ (eulerianTimeJet field x t) (field x t))
      (volume.restrict unitCube) :=
    ((eulerianTimeJet_continuous_of_contDiffOn_openSlab field hfield ht0 htT).inner
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
    apply hasDerivAt_kineticEnergyDensity_time_of_contDiffOn_openSlab field hfield x
    · exact lt_trans hlower0 hτ.1
    · exact lt_trans hτ.2 hupperT
  simpa [periodicKineticEnergy] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun τ x => kineticEnergyDensity (fun y => field y τ) x)
      (F' := fun τ x => inner ℝ (eulerianTimeJet field x τ) (field x τ))
      (bound := fun _ : Space => C) (x₀ := t) (s := timeSet)
      (μ := volume.restrict unitCube)
      htimeSet hFmeas hFint hF'meas hbound hboundIntegrable hdiff).2

/-! ## Periodic finite-slab attachments -/

/-- Interior vorticity slices of a finite periodic solution are spatially `C²`. -/
theorem periodicSolutionOn_vorticityField_contDiff_two
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    ContDiff ℝ 2 (fun x => vorticityField velocity x t) :=
  vorticityField_contDiff_two velocity t
    ((smoothSolutionOn_velocitySpatialSmooth solution.toSmoothSolutionOn ht0 htT).of_le
      (WithTop.coe_le_coe.mpr le_top))

/-- Interior vorticity slices retain every declared spatial period. -/
theorem periodicSolutionOn_vorticityField_isOnePeriodic
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    IsOnePeriodic (fun x => vorticityField velocity x t) :=
  vorticityField_isOnePeriodic velocity t
    (solution.velocityPeriodic t ⟨ht0.le, htT.le⟩)

/-- Periodic incompressible transport does no net vorticity work on an interior slab slice. -/
theorem periodicSolutionOn_integral_vorticityTransport_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    ∫ x in unitCube,
      inner ℝ
        (fderiv ℝ (fun y => vorticityField velocity y t) x (velocity x t))
        (vorticityField velocity x t) = 0 := by
  apply integral_transportWork_unitCube_eq_zero
  · exact (smoothSolutionOn_velocitySpatialSmooth
      solution.toSmoothSolutionOn ht0 htT).of_le (by norm_num)
  · exact (periodicSolutionOn_vorticityField_contDiff_two
      solution ht0 htT).of_le (by norm_num)
  · exact solution.velocityPeriodic t ⟨ht0.le, htT.le⟩
  · exact periodicSolutionOn_vorticityField_isOnePeriodic solution ht0 htT
  · exact fun x => solution.incompressible x t ⟨ht0.le, htT.le⟩

/-- Periodic integration by parts identifies finite-slab viscous vorticity work with negative
dissipation. -/
theorem periodicSolutionOn_integral_vorticityLaplacian_eq_neg_dissipation
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    ∫ x in unitCube,
      inner ℝ (Δ (fun y => vorticityField velocity y t) x)
        (vorticityField velocity x t) =
      -periodicVorticityDissipation velocity t := by
  unfold periodicVorticityDissipation
  apply integral_inner_laplacian_eq_neg_integral_component_gradient_sq
  · exact periodicSolutionOn_vorticityField_contDiff_two solution ht0 htT
  · exact periodicSolutionOn_vorticityField_isOnePeriodic solution ht0 htT

/-- The finite-slab enstrophy receiver has the expected time-work derivative at every interior
time, before using the PDE. -/
theorem periodicSolutionOn_hasDerivAt_periodicEnstrophy_eq_timeWork
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (periodicEnstrophy velocity)
      (∫ x in unitCube,
        inner ℝ (eulerianTimeJet (vorticityField velocity) x t)
          (vorticityField velocity x t)) t := by
  simpa [periodicEnstrophy] using
    hasDerivAt_periodicKineticEnergy_eq_timeWork_of_contDiffOn_openSlab
      (vorticityField velocity)
      (smoothSolutionOn_vorticityField_contDiffOn_interior
        solution.toSmoothSolutionOn) ht0 htT

/-- The finite-slab pointwise balance read against the actual vorticity. -/
theorem smoothSolutionOn_pointwiseVorticityBalance_inner
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) :
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
    (smoothSolutionOn_pointwiseVorticityBalance solution ht0 htT x)
  simpa [inner_add_left, real_inner_smul_left] using hread

/-- The exact forced periodic enstrophy identity on the finite slab interior. -/
theorem periodicSolutionOn_integral_vorticityTimeWork_eq_enstrophyRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
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
  have hu : ContDiff ℝ ∞ u :=
    smoothSolutionOn_velocitySpatialSmooth solution.toSmoothSolutionOn ht0 htT
  have homega : ContDiff ℝ 2 omega :=
    periodicSolutionOn_vorticityField_contDiff_two solution ht0 htT
  have htimeContinuous : Continuous (fun x =>
      inner ℝ (eulerianTimeJet (vorticityField velocity) x t) (omega x)) :=
    (eulerianTimeJet_continuous_of_contDiffOn_openSlab
      (vorticityField velocity)
      (smoothSolutionOn_vorticityField_contDiffOn_interior
        solution.toSmoothSolutionOn) ht0 htT).inner homega.continuous
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
  have hforceSmooth : ContDiff ℝ 2 (fun x => force x t) :=
    smoothSolutionOn_forceSpatialSmooth solution.toSmoothSolutionOn ht0 htT
  have hforceInt : IntegrableOn (fun x =>
      inner ℝ (curlForce x) (omega x)) unitCube := by
    have hcurlForce : ContDiff ℝ 1 curlForce :=
      vorticityField_contDiff_one force t hforceSmooth
    exact (hcurlForce.continuous.inner homega.continuous).continuousOn
      |>.integrableOn_compact hcubeCompact
  have hintegrated :
      (∫ x in unitCube,
        inner ℝ (eulerianTimeJet (vorticityField velocity) x t) (omega x)) +
        ∫ x in unitCube, inner ℝ (fderiv ℝ omega x (u x)) (omega x) =
      (∫ x in unitCube, inner ℝ (fderiv ℝ u x (omega x)) (omega x)) +
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
              exact smoothSolutionOn_pointwiseVorticityBalance_inner
                solution.toSmoothSolutionOn ht0 htT x
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
  have htransportZero :=
    periodicSolutionOn_integral_vorticityTransport_eq_zero solution ht0 htT
  have hviscous :=
    periodicSolutionOn_integral_vorticityLaplacian_eq_neg_dissipation
      solution ht0 htT
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
  unfold periodicEnstrophyRate periodicVortexStretching periodicCurlForcingWork
  linarith

/-- The exact enstrophy derivative follows from finite-slab momentum alone at every interior
event. -/
theorem periodicSolutionOn_hasDerivAt_periodicEnstrophy_fromMomentum
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (periodicEnstrophy velocity)
      (periodicEnstrophyRate nu force velocity t) t := by
  have hderivative := periodicSolutionOn_hasDerivAt_periodicEnstrophy_eq_timeWork
    solution ht0 htT
  rw [periodicSolutionOn_integral_vorticityTimeWork_eq_enstrophyRate
    solution ht0 htT] at hderivative
  exact hderivative


section Audit

#print axioms periodicSolutionOn_hasDerivAt_periodicEnstrophy_fromMomentum

end Audit

end Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
