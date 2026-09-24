import ElementaryHolonics.Millennium.NavierStokesCombBarycenterDefect

/-!
# The Fourier Kirchhoff law: the transfer currents sum to zero

Two-field Parseval on the slice identifies the real pairing of Fourier modes with the cube
integral of the product of fields.  Applied to the advection field and the velocity, the periodic
advection work `∫ ⟨(u·∇)u, u⟩ = 0` (incompressibility and periodicity only) becomes the lattice
current law

```text
Σ'_k Re ⟨adv_k, û_k⟩ = 0 :
```

the transfer into every finite family of receivers is exactly the negative of the transfer into
its complement.  The tail can only be fed at the expense of the band.
-/

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped Finset ComplexConjugate ContDiff

namespace Soma.Holonics.Millennium.NavierStokesFourierKirchhoff

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment
open Soma.Holonics.Millennium.NavierStokesAlignedStrainBudget
open Soma.Holonics.Millennium.NavierStokesModalRiccati
open Soma.Holonics.Millennium.NavierStokesHalfRadiusReach
open Soma.Holonics.Millennium.NavierStokesShellStepCost
open Soma.Holonics.Millennium.NavierStokesMomentSwap
open Soma.Holonics.Millennium.NavierStokesMomentGap
open Soma.Holonics.Millennium.NavierStokesYoungFeed
open Soma.Holonics.Millennium.NavierStokesYoungTsum
open Soma.Holonics.Millennium.NavierStokesWeightedTailEnergy
open Soma.Holonics.Millennium.NavierStokesIncoherentBandMass
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFourthMomentRiccati
open Soma.Holonics.Millennium.NavierStokesWeightedYoung
open Soma.Holonics.Millennium.NavierStokesMomentInterpolation
open Soma.Holonics.Millennium.NavierStokesSixthYoung
open Soma.Holonics.Millennium.NavierStokesYoungRiccati
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesModeLagrange
open Soma.Holonics.Millennium.NavierStokesTailRelevance
open Soma.Holonics.Millennium.NavierStokesTailBoundedControl
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesModalGronwall
open Soma.Holonics.Millennium.NavierStokesTailGronwall
open Soma.Holonics.Millennium.NavierStokesFrequencyReach
open Soma.Holonics.Millennium.NavierStokesH2VorticityShellDissipationBridge
open Soma.Holonics.Millennium.NavierStokesYoungClosure
open Soma.Holonics.Millennium.NavierStokesMomentClosure
open Soma.Holonics.Millennium.NavierStokesIncoherentSource
open Soma.Holonics.Millennium.NavierStokesIncoherentClosure
open Soma.Holonics.Millennium.NavierStokesOpenEnergySpacetime
open Soma.Holonics.Millennium.NavierStokesCoordinateLowerEnergyEstimate
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesVelocityMassEnergy
open Soma.Holonics.Millennium.NavierStokesBandCoherence
open Soma.Holonics.Millennium.NavierStokesBandBarycenter
open Soma.Holonics.Millennium.NavierStokesCombBarycenterDefect
open Soma.Holonics.Millennium.NavierStokesTorusCubeIntegral
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat

/- Mathlib's multivariate Fourier basis uses probability Haar measure on each unit circle. -/
local instance kirchhoffMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Two-field Parseval on the slice -/

/-- **The real Parseval pairing of two smooth periodic components.** -/
theorem hasSum_re_conj_mul_smoothSliceFourierL2 (u v : InitialVelocity) (hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v) (hpu : IsOnePeriodic u) (hpv : IsOnePeriodic v) (c : Fin 3) :
    HasSum (fun k ↦ (conj (smoothSliceFourierL2 u hu hpu c k) * smoothSliceFourierL2 v hv hpv c k).re)
      (∫ q : SpatialTorus,
        (conj (smoothSliceComponentLift u hu hpu c q) * smoothSliceComponentLift v hv hpv c q).re) := by
  set U := smoothSliceComponentLift u hu hpu c with hU
  set V := smoothSliceComponentLift v hv hpv c with hV
  have h := UnitAddTorus.hasSum_prod_mFourierCoeff (U.toLp 2 volume ℂ) (V.toLp 2 volume ℂ)
  have hre := RCLike.hasSum_re ℂ h
  have hint : Integrable (fun q ↦ conj ((U.toLp 2 volume ℂ) q) * (V.toLp 2 volume ℂ) q) volume := by
    have := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (U.toLp 2 volume ℂ) (V.toLp 2 volume ℂ)
    simp only [RCLike.inner_apply] at this
    exact this.congr (Filter.Eventually.of_forall fun x ↦ mul_comm _ _)
  rw [← integral_re hint] at hre
  simp only [RCLike.re_to_complex] at hre
  have hintegral : (∫ q : SpatialTorus, (conj ((U.toLp 2 volume ℂ) q) * (V.toLp 2 volume ℂ) q).re) =
      ∫ q : SpatialTorus, (conj (U q) * V q).re := by
    have hcoeU : ((U.toLp 2 volume ℂ : SpatialTorus → ℂ)) =ᵐ[volume] U := U.coeFn_toLp volume
    have hcoeV : ((V.toLp 2 volume ℂ : SpatialTorus → ℂ)) =ᵐ[volume] V := V.coeFn_toLp volume
    apply integral_congr_ae
    filter_upwards [hcoeU, hcoeV] with q hqU hqV
    rw [hqU, hqV]
  rw [hintegral] at hre
  refine HasSum.congr_fun hre (fun k ↦ ?_)
  have e1 : smoothSliceFourierL2 u hu hpu c k = UnitAddTorus.mFourierCoeff (U.toLp 2 volume ℂ) k :=
    periodicFourierRepresentation_apply (U.toLp 2 volume ℂ) k
  have e2 : smoothSliceFourierL2 v hv hpv c k = UnitAddTorus.mFourierCoeff (V.toLp 2 volume ℂ) k :=
    periodicFourierRepresentation_apply (V.toLp 2 volume ℂ) k
  rw [e1, e2]

/-- **The torus pairing is the cube integral of the product.** -/
theorem integral_re_conj_mul_lift_eq (u v : InitialVelocity) (hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v) (hpu : IsOnePeriodic u) (hpv : IsOnePeriodic v) (c : Fin 3) :
    (∫ q : SpatialTorus,
        (conj (smoothSliceComponentLift u hu hpu c q) * smoothSliceComponentLift v hv hpv c q).re) =
      ∫ x in NavierStokesPeriodicFlux.unitCube, u x c * v x c := by
  let pairLift : C(SpatialTorus, ℝ) := {
    toFun := fun q ↦
      (conj (smoothSliceComponentLift u hu hpu c q) * smoothSliceComponentLift v hv hpv c q).re
    continuous_toFun := Complex.continuous_re.comp
      ((Complex.continuous_conj.comp (smoothSliceComponentLift u hu hpu c).continuous).mul
        (smoothSliceComponentLift v hv hpv c).continuous) }
  have hchart := integral_euclideanToSpatialTorus_unitCube pairLift
  calc
    (∫ q : SpatialTorus,
        (conj (smoothSliceComponentLift u hu hpu c q) * smoothSliceComponentLift v hv hpv c q).re) =
        ∫ x in NavierStokesPeriodicFlux.unitCube, pairLift (euclideanToSpatialTorus x) := by
      have hvolume :
          @volume SpatialTorus
              (@MeasureSpace.pi (Fin 3) (Fin.fintype 3) (fun _ ↦ UnitAddCircle)
                (fun _ ↦ kirchhoffMeasureSpaceUnitAddCircle)) =
            @volume SpatialTorus
              (@MeasureSpace.pi (Fin 3) (Fin.fintype 3) (fun _ ↦ UnitAddCircle)
                (fun _ ↦ AddCircle.measureSpace 1)) := by
        simp only [MeasureTheory.volume_pi]
        congr 1
        funext i
        change AddCircle.haarAddCircle =
          @volume UnitAddCircle (AddCircle.measureSpace 1)
        rw [AddCircle.volume_eq_smul_haarAddCircle]
        simp
      rw [hvolume]
      simpa [pairLift] using hchart.symm
    _ = ∫ x in NavierStokesPeriodicFlux.unitCube, u x c * v x c := by
      apply setIntegral_congr_fun
      · unfold NavierStokesPeriodicFlux.unitCube
        exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
          isCompact_Icc |>.measurableSet
      · intro x _hx
        simp only [pairLift, ContinuousMap.coe_mk, smoothSliceComponentLift]
        rw [periodicTorusLift_projection, periodicTorusLift_projection]
        simp [complexVelocityComponent]

/-! ## The transfer current and its conservation -/

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

/-- **The transfer into a receiver**: the real pairing of the advection mode with the velocity
mode. -/
def transfer (k : SpatialFrequency) : ℝ :=
  ∑ c : Fin 3,
    (conj (openActualAdvectionMode solution t k c) * openPeriodicVelocityFourierMode solution t k c).re

theorem hasSum_transfer_component (c : Fin 3) :
    HasSum (fun k ↦
        (conj (openActualAdvectionMode solution t k c) *
          openPeriodicVelocityFourierMode solution t k c).re)
      (∫ x in NavierStokesPeriodicFlux.unitCube,
        actualAdvectionField (fun x ↦ velocity x t.1) x c * velocity x t.1 c) := by
  have hu := openPeriodicSolutionOn_velocitySlice_contDiff solution t.2
  have hpu := solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩
  have hv := actualAdvectionField_contDiff hu
  have hpv := actualAdvectionField_isOnePeriodic hpu
  have h := hasSum_re_conj_mul_smoothSliceFourierL2 (actualAdvectionField (fun x ↦ velocity x t.1))
    (fun x ↦ velocity x t.1) hv hu hpv hpu c
  rw [integral_re_conj_mul_lift_eq] at h
  refine HasSum.congr_fun h (fun k ↦ ?_)
  rw [smoothSliceFourierL2_apply, smoothSliceFourierL2_apply]
  rfl

/-- **The Fourier Kirchhoff law**: the transfer currents sum to zero. -/
theorem hasSum_transfer : HasSum (transfer solution t) 0 := by
  have hu := openPeriodicSolutionOn_velocitySlice_contDiff solution t.2
  have hpu := solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩
  have hdiv : ∀ x, divergence (fun y ↦ velocity y t.1) x = 0 :=
    fun x ↦ solution.incompressible x t.1 ⟨t.2.1.le, t.2.2⟩
  have hzero := integral_advectionWork_unitCube_eq_zero (fun x ↦ velocity x t.1)
    (hu.of_le (by simp)) hpu hdiv
  have hsum : HasSum (transfer solution t)
      (∑ c : Fin 3, ∫ x in NavierStokesPeriodicFlux.unitCube,
        actualAdvectionField (fun x ↦ velocity x t.1) x c * velocity x t.1 c) :=
    hasSum_sum fun c _ ↦ hasSum_transfer_component solution t c
  have hcubeCompact : IsCompact NavierStokesPeriodicFlux.unitCube := by
    unfold NavierStokesPeriodicFlux.unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  have hv := actualAdvectionField_contDiff hu
  have hint : ∀ c ∈ (Finset.univ : Finset (Fin 3)), IntegrableOn
      (fun x ↦ actualAdvectionField (fun x ↦ velocity x t.1) x c * velocity x t.1 c)
      NavierStokesPeriodicFlux.unitCube := by
    intro c _
    exact (((EuclideanSpace.proj c).continuous.comp hv.continuous).mul
      ((EuclideanSpace.proj c).continuous.comp hu.continuous)).continuousOn.integrableOn_compact
      hcubeCompact
  have hcalc : (∑ c : Fin 3, ∫ x in NavierStokesPeriodicFlux.unitCube,
      actualAdvectionField (fun x ↦ velocity x t.1) x c * velocity x t.1 c) = 0 := by
    rw [← integral_finsetSum _ hint]
    refine Eq.trans ?_ hzero
    apply setIntegral_congr_fun hcubeCompact.measurableSet
    intro x _hx
    simp only [actualAdvectionField, PiLp.inner_apply, RCLike.inner_apply, RCLike.conj_to_real]
    exact Finset.sum_congr rfl fun c _ ↦ by ring
  rw [hcalc] at hsum
  exact hsum

theorem summable_transfer : Summable (transfer solution t) := (hasSum_transfer solution t).summable

theorem tsum_transfer : ∑' k, transfer solution t k = 0 := (hasSum_transfer solution t).tsum_eq

/-- **The band–tail budget**: the transfer into any finite family is the negative of the transfer
into its complement. -/
theorem sum_transfer_add_tsum_compl (F : Finset SpatialFrequency) :
    ∑ k ∈ F, transfer solution t k + ∑' k : ↑((↑F : Set SpatialFrequency)ᶜ), transfer solution t k = 0 := by
  rw [(summable_transfer solution t).sum_add_tsum_compl, tsum_transfer]

theorem tsum_compl_transfer_eq_neg (F : Finset SpatialFrequency) :
    ∑' k : ↑((↑F : Set SpatialFrequency)ᶜ), transfer solution t k = -∑ k ∈ F, transfer solution t k := by
  have := sum_transfer_add_tsum_compl solution t F
  linarith

section Audit

#print axioms hasSum_re_conj_mul_smoothSliceFourierL2
#print axioms hasSum_transfer
#print axioms tsum_compl_transfer_eq_neg

end Audit

end Soma.Holonics.Millennium.NavierStokesFourierKirchhoff
