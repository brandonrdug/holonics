import ElementaryHolonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
import ElementaryHolonics.Millennium.NavierStokesTerminalFourier
import Mathlib.Topology.Order.IsLocallyClosed

/-!
# Boundary-inclusive spatial derivative continuity

The open carrier includes the initial face `Ico 0 T`.  Joint `ContDiffOn` therefore supplies a
continuous within-derivative on the whole slab, including time zero.  Composing that derivative
with the spatial inclusion recovers the ordinary spatial derivative of each fixed-time slice.
The second theorem applies the result to the literal advective field `Du(u)`.
-/

noncomputable section

open ContDiff Set Filter Topology
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesInitialSpatialContinuity

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesTerminalFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier

def initialSpatialSlab (T : ℝ) : Set (Space × ℝ) :=
  Set.univ ×ˢ openTimeSlab T

theorem continuousOn_initialSpatialFDeriv
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure) :
    ContinuousOn
      (fun z : Space × ℝ ↦ fderiv ℝ (fun y : Space ↦ velocity y z.2) z.1)
      (initialSpatialSlab T) := by
  let slab : Set (Space × ℝ) := initialSpatialSlab T
  have hslab : slab = openSpaceTimeSlab T := by
    rfl
  have hslabUnique : UniqueDiffOn ℝ slab := by
    rw [hslab]
    dsimp [openSpaceTimeSlab, openTimeSlab]
    exact uniqueDiffOn_univ.prod (uniqueDiffOn_Ico 0 T)
  have hjointContinuous : ContinuousOn
      (fderivWithin ℝ (Function.uncurry velocity) slab) slab := by
    rw [hslab]
    exact solution.velocitySmooth.continuousOn_fderivWithin hslabUnique (by simp)
  have hcomposed : ContinuousOn
      (fun z : Space × ℝ ↦
        (fderivWithin ℝ (Function.uncurry velocity) slab z).comp
          (ContinuousLinearMap.inl ℝ Space ℝ)) slab := by
    exact hjointContinuous.clm_comp continuousOn_const
  apply hcomposed.congr
  intro z hz
  have hz' : z ∈ openSpaceTimeSlab T := by simpa [hslab] using hz
  have hjointDiff : DifferentiableWithinAt ℝ
      (Function.uncurry velocity) slab z := by
    exact solution.velocitySmooth.differentiableOn (by simp) z hz'
  have hsliceDiff : DifferentiableWithinAt ℝ (fun y : Space ↦ (y, z.2)) Set.univ z.1 :=
    (hasFDerivAt_prodMk_left z.1 z.2).differentiableAt.differentiableWithinAt
  have hmaps : MapsTo (fun y : Space ↦ (y, z.2)) Set.univ slab := by
    intro y _hy
    exact ⟨Set.mem_univ y, hz.2⟩
  have hcomposition := fderivWithin_comp' z.1
    hjointDiff hsliceDiff hmaps
      (uniqueDiffWithinAt_univ : UniqueDiffWithinAt ℝ Set.univ z.1)
  have hsliceMap : fderiv ℝ (fun y : Space ↦ (y, z.2)) z.1 =
      ContinuousLinearMap.inl ℝ Space ℝ :=
    (hasFDerivAt_prodMk_left z.1 z.2).fderiv
  simpa [fderivWithin_univ, Function.uncurry_apply_pair, hsliceMap] using hcomposition

theorem continuousOn_initialActualAdvectionField
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure) :
    ContinuousOn
      (fun z : Space × ℝ ↦
        actualAdvectionField (fun y : Space ↦ velocity y z.2) z.1)
      (initialSpatialSlab T) := by
  let slab : Set (Space × ℝ) := initialSpatialSlab T
  have hslab : slab = openSpaceTimeSlab T := by
    rfl
  have hderiv := continuousOn_initialSpatialFDeriv solution
  have hvelocity : ContinuousOn (Function.uncurry velocity) slab := by
    rw [hslab]
    exact solution.velocitySmooth.continuousOn
  have happly := hderiv.clm_apply hvelocity
  apply happly.congr
  intro z hz
  simp only [actualAdvectionField, Function.uncurry_apply_pair]
  rfl

/-! ## Initial-inclusive torus advection and its Fourier receiver -/

def initialTorusActualAdvectionWorldTube
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (hperiodic : ∀ t ∈ openTimeSlab T, IsOnePeriodic (fun x ↦ velocity x t)) :
    C((openTimeSlab T) × SpatialTorus, Space) where
  toFun := fun z ↦ actualAdvectionField
    (fun x ↦ velocity x z.1.1) (euclideanRepresentative z.2)
  continuous_toFun := by
    have hsourceOn : ContinuousOn
        (fun z : Space × ℝ ↦ actualAdvectionField
          (fun x ↦ velocity x z.2) z.1) (initialSpatialSlab T) :=
      continuousOn_initialActualAdvectionField solution
    have hsource : Continuous
        (fun z : (openTimeSlab T) × Space ↦ actualAdvectionField
          (fun x ↦ velocity x z.1.1) z.2) := by
      let map : (openTimeSlab T) × Space → Space × ℝ := fun z ↦ (z.2, z.1)
      have hmap : Continuous map :=
        continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)
      have hmaps : MapsTo map Set.univ (initialSpatialSlab T) := by
        intro z _hz
        exact ⟨Set.mem_univ z.2, z.1.2⟩
      have hcomp := hsourceOn.comp hmap.continuousOn hmaps
      simpa [map, Function.comp_def] using (continuousOn_univ.mp hcomp)
    letI : LocallyCompactSpace (openTimeSlab T) :=
      isLocallyClosed_Ico.locallyCompactSpace
    apply euclideanToSpatialTorus_isOpenQuotientMap.isQuotientMap.continuous_lift_prod_right
    apply hsource.congr
    intro z
    apply isOnePeriodic_eq_of_euclideanToSpatialTorus_eq
      (fun x ↦ actualAdvectionField (fun y ↦ velocity y z.1.1) x)
      (actualAdvectionField_isOnePeriodic (hperiodic z.1.1 z.1.2))
    exact (euclideanToSpatialTorus_representative _).symm

def initialActualAdvectionMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (hperiodic : ∀ t ∈ openTimeSlab T, IsOnePeriodic (fun x ↦ velocity x t))
    (t : openTimeSlab T)
    (k : Soma.Holonics.Millennium.NavierStokesTorusFourier.SpatialFrequency) :
      Soma.Holonics.Millennium.NavierStokesTorusFourier.ComplexVector :=
  continuousTorusVectorFourierCoeff
    ((ContinuousMap.curry (initialTorusActualAdvectionWorldTube solution hperiodic)) t) k

theorem continuous_initialActualAdvectionMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (hperiodic : ∀ t ∈ openTimeSlab T, IsOnePeriodic (fun x ↦ velocity x t))
    (k : Soma.Holonics.Millennium.NavierStokesTorusFourier.SpatialFrequency) :
    Continuous (fun t : openTimeSlab T ↦
      initialActualAdvectionMode solution hperiodic t k) := by
  exact (continuous_continuousTorusVectorFourierCoeff k).comp
    (ContinuousMap.curry (initialTorusActualAdvectionWorldTube solution hperiodic)).continuous

theorem initialActualAdvectionMode_eq_openActualAdvectionMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : Ioo 0 T} (ht : 0 ≤ t.1)
    (k : Soma.Holonics.Millennium.NavierStokesTorusFourier.SpatialFrequency) :
    initialActualAdvectionMode solution.toOpenSmoothSolutionOn
        (fun s hs ↦ solution.velocityPeriodic s hs)
        ⟨t.1, ⟨ht, t.2.2⟩⟩ k =
      openActualAdvectionMode solution t k := by
  unfold initialActualAdvectionMode continuousTorusVectorFourierCoeff
    openActualAdvectionMode
  ext component
  rw [vectorSpatialFourierCoeff_apply]
  rfl

theorem initialActualAdvectionMode_eq_vectorSpatialFourierCoeff
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (hperiodic : ∀ t ∈ openTimeSlab T, IsOnePeriodic (fun x ↦ velocity x t))
    (t : openTimeSlab T)
    (k : Soma.Holonics.Millennium.NavierStokesTorusFourier.SpatialFrequency)
    (hslice : ContDiff ℝ ∞ (fun x : Space ↦ velocity x t.1)) :
    initialActualAdvectionMode solution hperiodic t k =
      vectorSpatialFourierCoeff (actualAdvectionField (fun x : Space ↦ velocity x t.1))
        (actualAdvectionField_contDiff hslice).continuous
        (actualAdvectionField_isOnePeriodic (hperiodic t.1 t.2)) k := by
  ext component
  rw [vectorSpatialFourierCoeff_apply]
  rfl

def initialTorusVelocityWorldTube
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (hperiodic : ∀ t ∈ openTimeSlab T, IsOnePeriodic (fun x ↦ velocity x t)) :
    C((openTimeSlab T) × SpatialTorus, Space) where
  toFun := fun z ↦ velocity (euclideanRepresentative z.2) z.1.1
  continuous_toFun := by
    have hsourceOn : ContinuousOn (Function.uncurry velocity)
        (initialSpatialSlab T) := solution.velocitySmooth.continuousOn
    have hsource : Continuous
        (fun z : (openTimeSlab T) × Space ↦ velocity z.2 z.1.1) := by
      let map : (openTimeSlab T) × Space → Space × ℝ := fun z ↦ (z.2, z.1)
      have hmap : Continuous map :=
        continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)
      have hmaps : MapsTo map Set.univ (initialSpatialSlab T) := by
        intro z _hz
        exact ⟨Set.mem_univ z.2, z.1.2⟩
      have hcomp := hsourceOn.comp hmap.continuousOn hmaps
      simpa [map, Function.comp_def] using (continuousOn_univ.mp hcomp)
    letI : LocallyCompactSpace (openTimeSlab T) :=
      isLocallyClosed_Ico.locallyCompactSpace
    apply euclideanToSpatialTorus_isOpenQuotientMap.isQuotientMap.continuous_lift_prod_right
    apply hsource.congr
    intro z
    apply isOnePeriodic_eq_of_euclideanToSpatialTorus_eq
      (fun x ↦ velocity x z.1.1)
      (hperiodic z.1.1 z.1.2)
    exact (euclideanToSpatialTorus_representative _).symm

def initialVelocityMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (hperiodic : ∀ t ∈ openTimeSlab T, IsOnePeriodic (fun x ↦ velocity x t))
    (t : openTimeSlab T)
    (k : Soma.Holonics.Millennium.NavierStokesTorusFourier.SpatialFrequency) :
      Soma.Holonics.Millennium.NavierStokesTorusFourier.ComplexVector :=
  continuousTorusVectorFourierCoeff
    ((ContinuousMap.curry (initialTorusVelocityWorldTube solution hperiodic)) t) k

theorem continuous_initialVelocityMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (hperiodic : ∀ t ∈ openTimeSlab T, IsOnePeriodic (fun x ↦ velocity x t))
    (k : Soma.Holonics.Millennium.NavierStokesTorusFourier.SpatialFrequency) :
    Continuous (fun t : openTimeSlab T ↦ initialVelocityMode solution hperiodic t k) := by
  exact (continuous_continuousTorusVectorFourierCoeff k).comp
    (ContinuousMap.curry (initialTorusVelocityWorldTube solution hperiodic)).continuous

theorem initialVelocityMode_eq_openPeriodicVelocityFourierMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : Ioo 0 T} (ht : 0 ≤ t.1)
    (k : Soma.Holonics.Millennium.NavierStokesTorusFourier.SpatialFrequency) :
    initialVelocityMode solution.toOpenSmoothSolutionOn
        (fun s hs ↦ solution.velocityPeriodic s hs)
        ⟨t.1, ⟨ht, t.2.2⟩⟩ k =
      openPeriodicVelocityFourierMode solution t k := by
  unfold initialVelocityMode continuousTorusVectorFourierCoeff
    openPeriodicVelocityFourierMode
  ext component
  rw [vectorSpatialFourierCoeff_apply]
  rfl

theorem initialVelocityMode_eq_vectorSpatialFourierCoeff
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (hperiodic : ∀ t ∈ openTimeSlab T, IsOnePeriodic (fun x ↦ velocity x t))
    (t : openTimeSlab T)
    (k : Soma.Holonics.Millennium.NavierStokesTorusFourier.SpatialFrequency)
    (hslice : ContDiff ℝ ∞ (fun x : Space ↦ velocity x t.1)) :
    initialVelocityMode solution hperiodic t k =
      vectorSpatialFourierCoeff (fun x : Space ↦ velocity x t.1)
        hslice.continuous (hperiodic t.1 t.2) k := by
  unfold initialVelocityMode continuousTorusVectorFourierCoeff
  ext component
  rw [vectorSpatialFourierCoeff_apply]
  rfl

section Audit

#print axioms continuousOn_initialSpatialFDeriv
#print axioms continuousOn_initialActualAdvectionField
#print axioms continuous_initialActualAdvectionMode
#print axioms initialActualAdvectionMode_eq_openActualAdvectionMode
#print axioms initialActualAdvectionMode_eq_vectorSpatialFourierCoeff
#print axioms continuous_initialVelocityMode
#print axioms initialVelocityMode_eq_openPeriodicVelocityFourierMode
#print axioms initialVelocityMode_eq_vectorSpatialFourierCoeff

end Audit

end Soma.Holonics.Millennium.NavierStokesInitialSpatialContinuity
