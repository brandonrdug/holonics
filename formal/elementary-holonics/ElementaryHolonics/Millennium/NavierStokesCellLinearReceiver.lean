import ElementaryHolonics.Millennium.NavierStokesFiniteTimeEnstrophy

/-!
# Linear cell receivers for a jointly smooth velocity field

This owner differentiates one actual Cartesian component over the unit cell.  The domination and
compact interior-time geometry follow the existing periodic kinetic-energy proof, while the receiver is
linear rather than quadratic.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Real Set Filter Topology
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesCellLinearReceiver

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux

theorem hasDerivAt_cellComponentIntegral_of_contDiffOn_openSlab
    {T : ℝ} (field : VelocityField)
    (hfield : ContDiffOn ℝ ∞ (Function.uncurry field) (openSpaceTimeSlab T))
    (component : Fin 3) {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt
      (fun s ↦ ∫ x in unitCube, field x s component)
      (∫ x in unitCube, (eulerianTimeJet field x t) component) t := by
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
  have hjointComponentContinuous : ContinuousOn
      (fun z : Space × ℝ => (eulerianTimeJet field z.1 z.2) component)
      (openSpaceTimeSlab T) := by
    have hjet := hjointJetContinuous
    have hproj : ContinuousOn
        (fun z : Space × ℝ =>
          (EuclideanSpace.proj component)
            (fderiv ℝ (Function.uncurry field) z (0, 1)))
        (openSpaceTimeSlab T) :=
      (EuclideanSpace.proj component).continuous.comp_continuousOn hjet
    simpa [eulerianTimeJet] using hproj
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
  have hcomponentNormContinuous : ContinuousOn
      (fun z : Space × ℝ => ‖(eulerianTimeJet field z.1 z.2) component‖)
      compactCylinder := (hjointComponentContinuous.mono hcompactSubset).norm
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (hcompactCylinder.bddAbove_image hcomponentNormContinuous)
  have hFmeas : ∀ᶠ τ in nhds t, AEStronglyMeasurable
      (fun x => field x τ component) (volume.restrict unitCube) := by
    filter_upwards [Ioo_mem_nhds ht0 htT] with τ hτ
    have hslice : ContDiff ℝ ∞ (fun x => field x τ) := by
      rw [contDiff_iff_contDiffAt]
      intro x
      have hjoint : ContDiffAt ℝ ∞ (Function.uncurry field) (x, τ) :=
        hfield.contDiffAt (x := (x, τ))
        (prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds hτ.1 hτ.2))
      simpa [Function.comp_def] using
        hjoint.comp x (contDiffAt_id.prodMk contDiffAt_const)
    exact ((EuclideanSpace.proj component).contDiff.comp hslice).continuous
      |>.aestronglyMeasurable
  have hslice : ContDiff ℝ ∞ (fun x => field x t) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    have hjoint : ContDiffAt ℝ ∞ (Function.uncurry field) (x, t) :=
      hfield.contDiffAt (x := (x, t))
      (prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht0 htT))
    simpa [Function.comp_def] using
      hjoint.comp x (contDiffAt_id.prodMk contDiffAt_const)
  have hFint : Integrable
      (fun x => field x t component) (volume.restrict unitCube) :=
    have hsliceComponent : ContDiff ℝ ∞ (fun x => field x t component) := by
      exact (EuclideanSpace.proj component).contDiff.comp hslice
    hsliceComponent.continuous.continuousOn.integrableOn_compact hcubeCompact
  have hF'meas : AEStronglyMeasurable
      (fun x => (eulerianTimeJet field x t) component)
      (volume.restrict unitCube) :=
    ((EuclideanSpace.proj component).continuous.comp
      (eulerianTimeJet_continuous_of_contDiffOn_openSlab field hfield ht0 htT)).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume.restrict unitCube), ∀ τ ∈ timeSet,
      ‖(eulerianTimeJet field x τ) component‖ ≤ C := by
    filter_upwards [ae_restrict_mem hcubeMeasurable] with x hx
    intro τ hτ
    apply hC
    refine ⟨(x, τ), ?_, rfl⟩
    exact ⟨hx, hτ.1.le, hτ.2.le⟩
  have hboundIntegrable : Integrable (fun _ : Space => C)
      (volume.restrict unitCube) :=
    integrableOn_const hcubeCompact.measure_lt_top.ne
  have hdiff : ∀ᵐ x ∂(volume.restrict unitCube), ∀ τ ∈ timeSet,
      HasDerivAt (fun σ => field x σ component)
        ((eulerianTimeJet field x τ) component) τ := by
    filter_upwards with x
    intro τ hτ
    have hjoint : ContDiffAt ℝ ∞ (Function.uncurry field) (x, τ) :=
      hfield.contDiffAt (x := (x, τ))
        (prod_mem_nhds Filter.univ_mem
          (Ioo_mem_nhds (lt_trans hlower0 hτ.1) (lt_trans hτ.2 hupperT)))
    have hjoint' : DifferentiableAt ℝ (Function.uncurry field) (x, τ) :=
      hjoint.differentiableAt (by simp)
    have htime := hjoint'.hasFDerivAt.comp τ
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) x τ)
    have hfieldTime : HasDerivAt (field x)
        (eulerianTimeJet field x τ) τ := by
      simpa [eulerianTimeJet, Function.comp_def] using htime.hasDerivAt
    have hcomponent := (EuclideanSpace.proj component).hasFDerivAt.comp τ hfieldTime
    simpa [Function.comp_def] using hcomponent.hasDerivAt
  convert (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun τ x => field x τ component)
      (F' := fun τ x => (eulerianTimeJet field x τ) component)
      (bound := fun _ : Space => C) (x₀ := t) (s := timeSet)
      (μ := volume.restrict unitCube)
      htimeSet hFmeas hFint hF'meas hbound hboundIntegrable hdiff).2 using 1

#print axioms hasDerivAt_cellComponentIntegral_of_contDiffOn_openSlab

end Soma.Holonics.Millennium.NavierStokesCellLinearReceiver
