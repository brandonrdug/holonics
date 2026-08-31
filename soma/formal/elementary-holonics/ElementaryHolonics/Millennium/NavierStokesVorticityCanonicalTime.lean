import ElementaryHolonics.Millennium.NavierStokesVorticityCanonicalModulus
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Topology.CompactOpen

/-!
# Time transport of the canonical vorticity modulus

**[proved-derived]** The canonical spatial derivative population varies continuously throughout
the strict-interior lifespan.  The proof starts from the admitted joint space--time smoothness,
restricts its derivative to the fixed spatial port, and then curries the compact radius-three
chart.  Thus the canonical norm is a continuous receiver of the complete spatial derivative
population, not a timewise selected witness.

The terminal face is deliberately not included: continuity on every compact subinterval of
`(0,T)` does not by itself supply integrability up to `T`.
-/

noncomputable section

open ContDiff MeasureTheory Set
open scoped Interval NNReal

namespace Soma.Holonics.Millennium.NavierStokesVorticityCanonicalTime

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalModulus

/-- The actual slice-defined vorticity is jointly smooth on the strict-interior cylinder of an
open periodic solution. -/
theorem openPeriodicSolutionOn_vorticityField_contDiffOn_interior
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    ContDiffOn ℝ ∞ (Function.uncurry (vorticityField velocity))
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) T) := by
  let interiorCylinder : Set (Space × ℝ) := Set.univ ×ˢ Set.Ioo (0 : ℝ) T
  have hopen : IsOpen interiorCylinder := isOpen_univ.prod isOpen_Ioo
  have hvelocity : ContDiffOn ℝ ∞ (Function.uncurry velocity) interiorCylinder := by
    apply solution.velocitySmooth.mono
    rintro ⟨x, t⟩ ⟨_hx, ht⟩
    exact ⟨Set.mem_univ x, ht.1.le, ht.2⟩
  have hderivative : ContDiffOn ℝ ∞
      (fderiv ℝ (Function.uncurry velocity)) interiorCylinder :=
    hvelocity.fderiv_of_isOpen hopen (by simp)
  have hjoint : ContDiffOn ℝ ∞ (Function.uncurry (jointVorticityField velocity))
      interiorCylinder := by
    have hcurl := jointSpatialCurlLinearMap.contDiff.comp_contDiffOn hderivative
    apply hcurl.congr
    rintro ⟨x, t⟩ hxt
    rfl
  apply hjoint.congr
  rintro ⟨x, t⟩ hxt
  have hvelocityAt : ContDiffAt ℝ 1 (Function.uncurry velocity) (x, t) :=
    (hvelocity.contDiffAt (hopen.mem_nhds hxt)).of_le (by norm_num)
  exact (jointVorticityField_eq_vorticityField_of_contDiffAt
    velocity x t hvelocityAt).symm

/-- At every strict-interior event, the derivative of the spatial vorticity slice is exactly the
joint derivative restricted to the fixed spatial inclusion. -/
theorem openPeriodic_fderiv_vorticity_slice_eq_jointSpatialDerivative
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (x : Space) (t : Set.Ioo (0 : ℝ) T) :
    fderiv ℝ (fun y ↦ vorticityField velocity y t.1) x =
      (fderiv ℝ (Function.uncurry (vorticityField velocity)) (x, t.1)).comp
        spatialInclusion := by
  let interiorCylinder : Set (Space × ℝ) := Set.univ ×ˢ Set.Ioo (0 : ℝ) T
  have hopen : IsOpen interiorCylinder := isOpen_univ.prod isOpen_Ioo
  have hvorticityAt : ContDiffAt ℝ 1
      (Function.uncurry (vorticityField velocity)) (x, t.1) :=
    ((openPeriodicSolutionOn_vorticityField_contDiffOn_interior solution).contDiffAt
      (hopen.mem_nhds ⟨Set.mem_univ x, t.2⟩)).of_le (by norm_num)
  have hjoint : DifferentiableAt ℝ
      (Function.uncurry (vorticityField velocity)) (x, t.1) :=
    hvorticityAt.differentiableAt (by norm_num)
  have hslice := hjoint.hasFDerivAt.comp x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t.1)
  simpa [Function.comp_def, spatialInclusion] using hslice.fderiv

/-- The joint spatial derivative of vorticity is continuous on the complete strict-interior
cylinder. -/
theorem openPeriodic_jointSpatialVorticityDerivative_continuousOn_interior
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    ContinuousOn
      (fun z : Space × ℝ ↦
        (fderiv ℝ (Function.uncurry (vorticityField velocity)) z).comp spatialInclusion)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) T) := by
  let interiorCylinder : Set (Space × ℝ) := Set.univ ×ˢ Set.Ioo (0 : ℝ) T
  have hopen : IsOpen interiorCylinder := isOpen_univ.prod isOpen_Ioo
  have hderivative : ContDiffOn ℝ ∞
      (fderiv ℝ (Function.uncurry (vorticityField velocity))) interiorCylinder :=
    (openPeriodicSolutionOn_vorticityField_contDiffOn_interior solution).fderiv_of_isOpen
      hopen (by simp)
  have hrestrict :=
    ((ContinuousLinearMap.compL ℝ Space (Space × ℝ) Space).flip spatialInclusion).contDiff
      |>.comp_contDiffOn hderivative
  simpa [interiorCylinder, Function.comp_def] using hrestrict.continuousOn

/-- Currying the compact chart returns a continuous time section valued in the complete
continuous derivative population. -/
theorem openPeriodicVorticityDerivativeChart_continuous
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    Continuous (openPeriodicVorticityDerivativeChart solution) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  let swap : Set.Ioo (0 : ℝ) T × Metric.closedBall (0 : Space) 3 → Space × ℝ :=
    fun z ↦ (z.2.1, z.1.1)
  have hswap : Continuous swap :=
    (continuous_subtype_val.comp continuous_snd).prodMk
      (continuous_subtype_val.comp continuous_fst)
  have hswapMem : ∀ z, swap z ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) T := by
    rintro ⟨t, x⟩
    exact ⟨Set.mem_univ x.1, t.2⟩
  have hjoint : Continuous (fun z :
      Set.Ioo (0 : ℝ) T × Metric.closedBall (0 : Space) 3 ↦
      (fderiv ℝ (Function.uncurry (vorticityField velocity)) (z.2.1, z.1.1)).comp
        spatialInclusion) := by
    simpa [swap, Function.comp_def] using
      (openPeriodic_jointSpatialVorticityDerivative_continuousOn_interior solution)
        |>.comp_continuous hswap hswapMem
  apply hjoint.congr
  rintro ⟨t, x⟩
  exact (openPeriodic_fderiv_vorticity_slice_eq_jointSpatialDerivative
    solution x.1 t).symm

/-- The canonical compact-chart derivative norm is continuous throughout the strict-interior
lifespan. -/
theorem openPeriodicCanonicalVorticityLipschitzConstant_continuous
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    Continuous (openPeriodicCanonicalVorticityLipschitzConstant solution) := by
  exact continuous_nnnorm.comp
    (openPeriodicVorticityDerivativeChart_continuous solution)

/-- Kinetic energy is continuous when read along the strict-interior time receiver. -/
theorem openPeriodic_periodicKineticEnergy_continuous
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    Continuous (fun t : Set.Ioo (0 : ℝ) T ↦ periodicKineticEnergy velocity t.1) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hvelocityInterior : ContDiffOn ℝ ∞ (Function.uncurry velocity)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) T) := by
    apply solution.velocitySmooth.mono
    rintro ⟨x, s⟩ ⟨_hx, hs⟩
    exact ⟨Set.mem_univ x, hs.1.le, hs.2⟩
  have hderiv := hasDerivAt_periodicKineticEnergy_eq_timeWork_of_contDiffOn_openSlab
    velocity hvelocityInterior t.2.1 t.2.2
  exact hderiv.continuousAt.comp continuous_subtype_val.continuousAt

/-- The fully composed canonical enstrophy coefficient is a continuous strict-interior time
receiver. -/
theorem openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient_continuous
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    Continuous
      (openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient solution) := by
  unfold openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient
  have henergy := openPeriodic_periodicKineticEnergy_continuous solution
  have hlipschitz := openPeriodicCanonicalVorticityLipschitzConstant_continuous solution
  exact
    (continuous_const.mul
      (Real.continuous_sqrt.comp (continuous_const.mul henergy))).add
      ((continuous_const.mul (NNReal.continuous_coe.comp hlipschitz)).mul continuous_const)

/-! ## Compact-interior return and terminal separator -/

/-- Every compact interval strictly inside the lifespan sees an integrable canonical coefficient.
This is the strongest direct time consequence of strict-interior smoothness. -/
theorem openPeriodicCanonicalVorticityDirectionEnstrophyRate_intervalIntegrable
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {a b : ℝ} (ha : 0 < a) (habOrder : a ≤ b) (hb : b < T) :
    IntervalIntegrable
      (openPeriodicCanonicalVorticityDirectionEnstrophyRate solution) volume a b := by
  have hcoeff :=
    openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient_continuous solution
  have hab : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  let lift : Set.Icc a b → Set.Ioo (0 : ℝ) T :=
    fun s ↦ ⟨s.1, hab s.2⟩
  have hlift : Continuous lift :=
    continuous_subtype_val.subtype_mk _
  have hrestricted : Continuous
      (fun s : Set.Icc a b ↦
        openPeriodicCanonicalVorticityDirectionEnstrophyRate solution s.1) := by
    have hcomposed := hcoeff.comp hlift
    apply hcomposed.congr
    intro s
    exact (openPeriodicCanonicalVorticityDirectionEnstrophyRate_eq
      solution (hab s.2)).symm
  have hcontinuousOn : ContinuousOn
      (openPeriodicCanonicalVorticityDirectionEnstrophyRate solution) (Set.Icc a b) := by
    rw [continuousOn_iff_continuous_restrict]
    simpa only [Set.restrict_def] using hrestricted
  have huIcc : ContinuousOn
      (openPeriodicCanonicalVorticityDirectionEnstrophyRate solution) [[a, b]] := by
    simpa [uIcc_of_le habOrder] using hcontinuousOn
  exact huIcc.intervalIntegrable

/-- A nonnegative exact terminal-pole population used to test what the strict-interior receiver
can and cannot conclude. -/
def terminalPolePopulation (t : ℝ) : ℝ :=
  ‖(t - 1)⁻¹‖

/-- The terminal-pole population is continuous at every strict-interior occurrence. -/
theorem terminalPolePopulation_continuousOn :
    ContinuousOn terminalPolePopulation (Set.Ioo (0 : ℝ) 1) := by
  unfold terminalPolePopulation
  exact ((continuousOn_id.sub continuousOn_const).inv₀ (by
    intro t ht
    exact sub_ne_zero.mpr (ne_of_lt ht.2))).norm

/-- The same population is not integrable through its terminal face. -/
theorem terminalPolePopulation_not_intervalIntegrable :
    ¬ IntervalIntegrable terminalPolePopulation volume 0 1 := by
  intro hpole
  have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ (t - 1)⁻¹)
      (volume.restrict (Ι 0 1)) := by
    exact (measurable_id.sub_const 1).inv.aestronglyMeasurable
  have hinv : IntervalIntegrable (fun t : ℝ ↦ (t - 1)⁻¹) volume 0 1 :=
    (IntervalIntegrable.intervalIntegrable_norm_iff hmeas).mp hpole
  have hcases : (0 : ℝ) = 1 ∨ (1 : ℝ) ∉ [[(0 : ℝ), 1]] :=
    intervalIntegrable_sub_inv_iff.mp hinv
  norm_num at hcases

/-- **[counterexample; formal-checked]** Nonnegativity plus strict-interior continuity does not
factor through the terminal interval-integrability receiver.  A new quantitative PDE law is
therefore required at the terminal face. -/
theorem strictInteriorContinuousNonnegative_not_sufficient_for_terminalIntegrability :
    ∃ f : ℝ → ℝ,
      ContinuousOn f (Set.Ioo (0 : ℝ) 1) ∧
      (∀ t, 0 ≤ f t) ∧
      ¬ IntervalIntegrable f volume 0 1 := by
  exact ⟨terminalPolePopulation, terminalPolePopulation_continuousOn,
    fun t ↦ norm_nonneg _, terminalPolePopulation_not_intervalIntegrable⟩

section Audit

#print axioms openPeriodicSolutionOn_vorticityField_contDiffOn_interior
#print axioms openPeriodic_fderiv_vorticity_slice_eq_jointSpatialDerivative
#print axioms openPeriodic_jointSpatialVorticityDerivative_continuousOn_interior
#print axioms openPeriodicVorticityDerivativeChart_continuous
#print axioms openPeriodicCanonicalVorticityLipschitzConstant_continuous
#print axioms openPeriodic_periodicKineticEnergy_continuous
#print axioms openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient_continuous
#print axioms openPeriodicCanonicalVorticityDirectionEnstrophyRate_intervalIntegrable
#print axioms terminalPolePopulation_continuousOn
#print axioms terminalPolePopulation_not_intervalIntegrable
#print axioms strictInteriorContinuousNonnegative_not_sufficient_for_terminalIntegrability

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityCanonicalTime
