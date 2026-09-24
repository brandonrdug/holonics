import ElementaryHolonics.Millennium.NavierStokesOpenFourierMildIdentity
import ElementaryHolonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
import ElementaryHolonics.Millennium.NavierStokesSharpDuhamelDerivativeInterchange
import ElementaryHolonics.Millennium.NavierStokesWeightedClassicalRestartCarrier

/-!
# The open mild coefficient population reconstructs one spatial field

**[proved-derived]** This owner joins the native mild fixed-point occurrence to the complete
Fourier reconstruction used by the corresponding official open periodic solution.  The equality
is a genuine equality of spatial fields: the continuing velocity is the homogeneous heat return
minus the repository's actual Bochner `weightedDuhamelReturn`.  No finite Fourier aperture or
pointwise coefficient proxy remains in the statement.

The second part identifies the homogeneous field with the independently constructed sharp heat
chart.  It therefore composes the standing sharp Duhamel differentiation theorem with the exact
linear heat derivative on the same actual velocity field.
-/

noncomputable section

open Set
open scoped ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesOpenMildFieldReconstruction

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesSharpDuhamelDerivativeIdentification
open Soma.Holonics.Millennium.NavierStokesSharpDuhamelDerivativeInterchange
open Soma.Holonics.Millennium.NavierStokesSharpDuhamelSecondDerivative
open Soma.Holonics.Millennium.NavierStokesSharpHeatDerivative
open Soma.Holonics.Millennium.NavierStokesSharpHeatDerivativeReconstruction
open Soma.Holonics.Millennium.NavierStokesTerminalFourier
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedClassicalRestartCarrier
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelReturnContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedHeatSemigroup
open Soma.Holonics.Millennium.NavierStokesWeightedLinearPath
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedMildSpacetimeMomentum
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReconstructionContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- Complete reconstruction preserves subtraction. -/
theorem reconstructedVelocity_sub
    (left right : PeriodicVectorWeightedSobolev 3) (x : Space) :
    reconstructedVelocity (left - right) x =
      reconstructedVelocity left x - reconstructedVelocity right x := by
  ext component
  change
    (reconstructedTorusComplexComponent (left - right) component
      (euclideanToSpatialTorus x)).re =
      (reconstructedTorusComplexComponent left component
        (euclideanToSpatialTorus x)).re -
      (reconstructedTorusComplexComponent right component
        (euclideanToSpatialTorus x)).re
  rw [show reconstructedTorusComplexComponent (left - right) component =
      reconstructedTorusComplexComponent left component -
        reconstructedTorusComplexComponent right component by
    exact (reconstructedTorusComplexComponentCLM component).map_sub left right]
  rfl

/-- The actual velocity of the weighted classical carrier is one complete reconstructed mild
field.  The equality is inherited from the native fixed point before spatial evaluation. -/
theorem weightedClassicalRestartVelocity_eq_linearHeat_sub_weightedDuhamel
    {nu cap : ℝ} {hnu : 0 < nu} {hcap : 0 ≤ cap}
    {initial : PeriodicVectorWeightedSobolev 3}
    (carrier : WeightedClassicalRestartCarrier nu cap hnu hcap initial)
    (t : Icc (0 : ℝ) (weightedRestartTimeFromCap nu cap)) (x : Space) :
    weightedClassicalRestartVelocity
        (weightedRestartTimeFromCap_pos hnu hcap).le carrier.path x t.1 =
      reconstructedVelocity
          (weightedLinearHeatPath (Real.toNNReal nu)
            (weightedRestartTimeFromCap_pos hnu hcap).le initial t) x -
        reconstructedVelocity
          (weightedDuhamelReturn (Real.toNNReal nu) (real_toNNReal_pos hnu)
            (weightedRestartTimeFromCap_pos hnu hcap).le carrier.path t.1) x := by
  let hT : 0 ≤ weightedRestartTimeFromCap nu cap :=
    (weightedRestartTimeFromCap_pos hnu hcap).le
  have hfixed :
      carrier.path =
        weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
          hT initial carrier.path := by
    simpa only [weightedMildRestartMap] using carrier.fixed.symm
  have hface := congrArg
    (fun path : WeightedH3Path (weightedRestartTimeFromCap nu cap) ↦ path t) hfixed
  unfold weightedClassicalRestartVelocity weightedReconstructedVelocity
  rw [weightedPathExtension_of_mem hT carrier.path t.2]
  rw [hface]
  change reconstructedVelocity
      (weightedLinearHeatPath (Real.toNNReal nu) hT initial t -
        weightedDuhamelPath (Real.toNNReal nu) (real_toNNReal_pos hnu)
          hT carrier.path t) x = _
  rw [reconstructedVelocity_sub]
  rfl

/-- Promoting the same carrier to the official open-solution receiver makes the independently
derived coefficientwise vorticity mild law apply to this very spatial field.  Thus the open PDE
modal occurrence and the reconstructed native mild occurrence are not separate solutions. -/
theorem weightedClassicalRestartOpenSolution_vorticityMode_mild_identity
    {nu cap : ℝ} {hnu : 0 < nu} {hcap : 0 ≤ cap}
    {initial : PeriodicVectorWeightedSobolev 3}
    (carrier : WeightedClassicalRestartCarrier nu cap hnu hcap initial)
    (upgrade : JointSpacetimeSmoothnessUpgrade carrier.classical)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (ht : t < weightedRestartTimeFromCap nu cap)
    (k : SpatialFrequency) :
    frequencyCurlMultiplier k
        (velocityMode
          (weightedClassicalRestartVelocity
            (weightedRestartTimeFromCap_pos hnu hcap).le carrier.path) k t) =
      heatStokesMultiplier nu (t - s) k •
          frequencyCurlMultiplier k
            (velocityMode
              (weightedClassicalRestartVelocity
                (weightedRestartTimeFromCap_pos hnu hcap).le carrier.path) k s) +
        ∫ tau in s..t,
          compactStokesTransportedVorticityNonlinearMode
            (carrier.toOpenPeriodicSolutionOn upgrade) hs hst ht k tau := by
  exact openPeriodicSolutionOn_vorticityMode_mild_identity
    (carrier.toOpenPeriodicSolutionOn upgrade) hs hst ht k

/-- Restricting the independently constructed positive-time `H3 -> H5` heat lift back to the
zeroth derivative word returns the same complete native `H3` heat occurrence. -/
theorem finiteOrderZero_vectorHeatH3ToH5_eq_periodicVectorWeightedHeat
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (state : PeriodicVectorWeightedSobolev 3) :
    finiteOrderVectorDerivativeToThree 2 0 (by omega) (fun i ↦ Fin.elim0 i)
        (vectorHeatH3ToH5 nu dt h state) =
      periodicVectorWeightedHeat 3 nu dt state := by
  funext component
  rw [← coefficientWeightedRealization_weightedSobolevCoefficients 3
      (finiteOrderVectorDerivativeToThree 2 0 (by omega)
        (fun i ↦ Fin.elim0 i) (vectorHeatH3ToH5 nu dt h state) component),
    ← coefficientWeightedRealization_weightedSobolevCoefficients 3
      (periodicVectorWeightedHeat 3 nu dt state component)]
  congr 1
  apply Subtype.ext
  apply lp.ext
  funext k
  rw [weightedSobolevCoefficients_finiteOrderVectorDerivativeToThree_apply,
    weightedCoefficients_vectorHeatH3ToH5]
  change _ =
    (weightedSobolevCoefficients 3
      (periodicWeightedHeat 3 nu dt (state component))).1 k
  rw [unweighted_periodicWeightedHeat_apply]
  simp [orderedDerivativeMultiplier]

/-- The homogeneous field in the native mild decomposition is exactly the separately founded
sharp heat field, before differentiating it. -/
theorem reconstructedVelocity_weightedLinearHeatPath_eq_reconstructedHeatH3Component
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3)
    (t : Icc (0 : ℝ) T) (htpos : 0 < t.1)
    (component : Fin 3) :
    (fun x : Space ↦ reconstructedVelocity
      (weightedLinearHeatPath nu hT initial t) x component) =
      reconstructedHeatH3Component nu (Real.toNNReal t.1)
        (mul_pos hnu
          (by simpa using htpos)) initial component := by
  have hdt : 0 < ((Real.toNNReal t.1 : ℝ≥0) : ℝ) := by
    simpa using htpos
  have hprod : 0 < (nu : ℝ) * ((Real.toNNReal t.1 : ℝ≥0) : ℝ) :=
    mul_pos hnu hdt
  have hstate := finiteOrderZero_vectorHeatH3ToH5_eq_periodicVectorWeightedHeat
    nu (Real.toNNReal t.1) hprod initial
  funext x
  change
    (reconstructedVelocity
      (periodicVectorWeightedHeat 3 nu (Real.toNNReal t.1) initial) x component) = _
  change
    (reconstructedTorusComplexComponent
      (periodicVectorWeightedHeat 3 nu (Real.toNNReal t.1) initial)
      component (euclideanToSpatialTorus x)).re =
    (reconstructedTorusComplexComponent
      (finiteOrderVectorDerivativeToThree 2 0 (by omega)
        (fun i ↦ Fin.elim0 i)
        (vectorHeatH3ToH5 nu (Real.toNNReal t.1) hprod initial))
      component (euclideanToSpatialTorus x)).re
  rw [hstate]

/-- On every positive addressed face, the actual carrier velocity is the sharp homogeneous heat
field minus the complete physical reconstruction of the native Duhamel return. -/
theorem weightedClassicalRestartVelocity_component_eq_sharpHeat_sub_weightedDuhamel
    {nu cap : ℝ} {hnu : 0 < nu} {hcap : 0 ≤ cap}
    {initial : PeriodicVectorWeightedSobolev 3}
    (carrier : WeightedClassicalRestartCarrier nu cap hnu hcap initial)
    (t : Icc (0 : ℝ) (weightedRestartTimeFromCap nu cap))
    (htpos : 0 < t.1) (component : Fin 3) :
    (fun x : Space ↦ weightedClassicalRestartVelocity
      (weightedRestartTimeFromCap_pos hnu hcap).le carrier.path x t.1 component) =
      (fun x : Space ↦
        reconstructedHeatH3Component (Real.toNNReal nu) (Real.toNNReal t.1)
            (mul_pos (real_toNNReal_pos hnu) (by simpa using htpos))
            initial component x -
          reconstructedVelocity
            (weightedDuhamelReturn (Real.toNNReal nu) (real_toNNReal_pos hnu)
              (weightedRestartTimeFromCap_pos hnu hcap).le carrier.path t.1)
            x component) := by
  let hT : 0 ≤ weightedRestartTimeFromCap nu cap :=
    (weightedRestartTimeFromCap_pos hnu hcap).le
  have hlinear :=
    reconstructedVelocity_weightedLinearHeatPath_eq_reconstructedHeatH3Component
      (Real.toNNReal nu) (real_toNNReal_pos hnu) hT initial t htpos component
  funext x
  have hmild := congrArg (fun v : Space ↦ v component)
    (weightedClassicalRestartVelocity_eq_linearHeat_sub_weightedDuhamel carrier t x)
  change _ =
    reconstructedVelocity
        (weightedLinearHeatPath (Real.toNNReal nu) hT initial t) x component -
      reconstructedVelocity
        (weightedDuhamelReturn (Real.toNNReal nu) (real_toNNReal_pos hnu)
          hT carrier.path t.1) x component at hmild
  rw [congrFun hlinear x] at hmild
  exact hmild

/-- The first addressed spatial derivative of the homogeneous heat field is differentiable: the
complete `H5` lift retains the whole Hessian operator, not only its coordinate values. -/
theorem differentiableAt_firstDirectional_reconstructedHeatH3Component
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (state : PeriodicVectorWeightedSobolev 3)
    (component first : Fin 3) (x : Space) :
    DifferentiableAt ℝ
      (fun y : Space ↦
        fderiv ℝ (reconstructedHeatH3Component nu dt h state component) y
          (EuclideanSpace.single first 1)) x := by
  let lifted := vectorHeatH3ToH5 nu dt h state
  let evalFirst : (Space →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single first 1)
  have hop := hasFDerivAt_reconstructedFiniteOrderRealFDerivCLM
    2 0 (by omega) (fun i ↦ Fin.elim0 i) lifted component x
  have hscalar := evalFirst.hasFDerivAt.comp x hop
  have hfield :
      (fun y : Space ↦
        fderiv ℝ (reconstructedHeatH3Component nu dt h state component) y
          (EuclideanSpace.single first 1)) =
      (fun y : Space ↦ evalFirst
        (reconstructedFiniteOrderRealFDerivCLM 2 0 (by omega)
          (fun i ↦ Fin.elim0 i) lifted component y)) := by
    funext y
    rw [reconstructedFiniteOrderRealFDerivCLM_eq_fderiv]
    rfl
  rw [hfield]
  exact hscalar.differentiableAt

/-- The same first-directional derivative of the actual Duhamel reconstruction is differentiable
under the sharp elapsed-clock hypotheses already used by the dominated interchange owner. -/
theorem differentiableAt_firstDirectional_reconstructedVelocity_weightedDuhamelReturn
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T t : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (ht : t ∈ Icc (0 : ℝ) T) (htpos : 0 < t)
    (hsmall : 2 * (nu : ℝ) * t ≤ 1)
    (component first : Fin 3) (x : Space) :
    DifferentiableAt ℝ
      (fun y : Space ↦ fderiv ℝ
        (fun z : Space ↦ reconstructedVelocity
          (weightedDuhamelReturn nu hnu hT path t) z component) y
        (EuclideanSpace.single first 1)) x := by
  let scalarField : Space → ℝ := fun z ↦ ∫ s in (0 : ℝ)..t,
    sharpDuhamelScalarIntegrand nu hnu t
      (weightedPathExtension hT path) component s z
  have hfield :
      (fun z : Space ↦ reconstructedVelocity
        (weightedDuhamelReturn nu hnu hT path t) z component) = scalarField := by
    funext z
    exact reconstructedVelocity_weightedDuhamelReturn_eq_integral_sharpScalar
      nu hnu hT path component ht z
  have hfirstField :
      (fun y : Space ↦ fderiv ℝ scalarField y
        (EuclideanSpace.single first 1)) =
      (fun y : Space ↦ ∫ s in (0 : ℝ)..t,
        sharpDuhamelFirstFDerivIntegrand nu hnu t
          (weightedPathExtension hT path) component s y
            (EuclideanSpace.single first 1)) := by
    funext y
    dsimp [scalarField]
    rw [(hasFDerivAt_integral_sharpDuhamelScalarIntegrand
      nu hnu hT path ht htpos hsmall component y).fderiv]
    exact ContinuousLinearMap.intervalIntegral_apply
      (intervalIntegrable_sharpDuhamelFirstFDerivIntegrand
        nu hnu hT path ht htpos hsmall component y)
      (EuclideanSpace.single first 1)
  rw [hfield, hfirstField]
  exact (hasFDerivAt_integral_sharpDuhamelFirstDirectionalIntegrand
    nu hnu hT path ht htpos hsmall component first x).differentiableAt

/-- The genuine spatial Hessian of the actual weighted classical velocity is the difference of
the independently reconstructed homogeneous heat Hessian and the exact nonlinear sharp Duhamel
chart.  This is an equality of derivatives of the physical field, not a modal estimate. -/
theorem weightedClassicalRestartVelocity_secondDerivative_eq_sharpHeat_sub_sharpDuhamel
    {nu cap : ℝ} {hnu : 0 < nu} {hcap : 0 ≤ cap}
    {initial : PeriodicVectorWeightedSobolev 3}
    (carrier : WeightedClassicalRestartCarrier nu cap hnu hcap initial)
    (t : Icc (0 : ℝ) (weightedRestartTimeFromCap nu cap))
    (htpos : 0 < t.1) (hsmall : 2 * nu * t.1 ≤ 1)
    (component first second : Fin 3)
    (x : Metric.closedBall (0 : Space) 3) :
    fderiv ℝ (fun y : Space ↦
      fderiv ℝ (fun z : Space ↦ weightedClassicalRestartVelocity
        (weightedRestartTimeFromCap_pos hnu hcap).le carrier.path z t.1 component) y
        (EuclideanSpace.single first 1)) x.1
        (EuclideanSpace.single second 1) =
      reconstructedHeatH3SecondDerivative
          (Real.toNNReal nu) (Real.toNNReal t.1)
          (mul_pos (real_toNNReal_pos hnu) (by simpa using htpos))
          initial component first second x.1 -
        sharpDuhamelSecondDerivativeChart
          (Real.toNNReal nu) (real_toNNReal_pos hnu)
          (weightedRestartTimeFromCap_pos hnu hcap).le carrier.path t.1
          component first second x := by
  let hT : 0 ≤ weightedRestartTimeFromCap nu cap :=
    (weightedRestartTimeFromCap_pos hnu hcap).le
  let nuClock : ℝ≥0 := Real.toNNReal nu
  let nonlinearState : PeriodicVectorWeightedSobolev 3 :=
    weightedDuhamelReturn nuClock (real_toNNReal_pos hnu) hT carrier.path t.1
  let linearField : Space → ℝ :=
    reconstructedHeatH3Component nuClock (Real.toNNReal t.1)
      (mul_pos (real_toNNReal_pos hnu) (by simpa using htpos)) initial component
  let nonlinearField : Space → ℝ := fun z ↦
    reconstructedVelocity nonlinearState z component
  let actualField : Space → ℝ := fun z ↦
    weightedClassicalRestartVelocity hT carrier.path z t.1 component
  have hfield : actualField = fun z ↦ linearField z - nonlinearField z := by
    simpa only [actualField, linearField, nonlinearField, nonlinearState, nuClock, hT] using
      weightedClassicalRestartVelocity_component_eq_sharpHeat_sub_weightedDuhamel
        carrier t htpos component
  have hlinearDiff : ∀ y : Space, DifferentiableAt ℝ linearField y := by
    intro y
    exact (contDiff_one_reconstructedFiniteOrderRealComponent 2 0 (by omega)
      (fun i ↦ Fin.elim0 i)
      (vectorHeatH3ToH5 nuClock (Real.toNNReal t.1)
        (mul_pos (real_toNNReal_pos hnu) (by simpa using htpos)) initial)
      component).differentiable (by norm_num) y
  have hnonlinearDiff : ∀ y : Space, DifferentiableAt ℝ nonlinearField y := by
    intro y
    exact (contDiff_one_reconstructedVelocity_component nonlinearState component).differentiable
      (by norm_num) y
  have hfirstField :
      (fun y : Space ↦ fderiv ℝ actualField y
        (EuclideanSpace.single first 1)) =
      (fun y : Space ↦
        fderiv ℝ linearField y (EuclideanSpace.single first 1) -
          fderiv ℝ nonlinearField y (EuclideanSpace.single first 1)) := by
    funext y
    rw [hfield]
    have hderiv := fderiv_sub (hlinearDiff y) (hnonlinearDiff y)
    have happly := congrArg
      (fun L : Space →L[ℝ] ℝ ↦ L (EuclideanSpace.single first 1)) hderiv
    change (fderiv ℝ (linearField - nonlinearField) y)
      (EuclideanSpace.single first 1) = _
    simpa only [sub_apply] using happly
  have hlinearFirstDiff : DifferentiableAt ℝ
      (fun y : Space ↦ fderiv ℝ linearField y
        (EuclideanSpace.single first 1)) x.1 := by
    exact differentiableAt_firstDirectional_reconstructedHeatH3Component
      nuClock (Real.toNNReal t.1)
        (mul_pos (real_toNNReal_pos hnu) (by simpa using htpos))
      initial component first x.1
  have hnonlinearFirstDiff : DifferentiableAt ℝ
      (fun y : Space ↦ fderiv ℝ nonlinearField y
        (EuclideanSpace.single first 1)) x.1 := by
    exact differentiableAt_firstDirectional_reconstructedVelocity_weightedDuhamelReturn
      nuClock (real_toNNReal_pos hnu) hT carrier.path t.2 htpos
        (by simpa [nuClock, Real.coe_toNNReal _ hnu.le] using hsmall)
      component first x.1
  have hsharp := hasSharpDuhamelSecondDerivativeIdentification
    nuClock (real_toNNReal_pos hnu) hT carrier.path t.2 htpos
      (by simpa [nuClock, Real.coe_toNNReal _ hnu.le] using hsmall)
    component first second x
  change fderiv ℝ (fun y : Space ↦ fderiv ℝ actualField y
      (EuclideanSpace.single first 1)) x.1
      (EuclideanSpace.single second 1) = _
  rw [hfirstField]
  change fderiv ℝ
      ((fun y : Space ↦ fderiv ℝ linearField y
          (EuclideanSpace.single first 1)) -
        (fun y : Space ↦ fderiv ℝ nonlinearField y
          (EuclideanSpace.single first 1))) x.1
      (EuclideanSpace.single second 1) = _
  rw [fderiv_sub hlinearFirstDiff hnonlinearFirstDiff]
  change
    fderiv ℝ (fun y : Space ↦ fderiv ℝ linearField y
      (EuclideanSpace.single first 1)) x.1
        (EuclideanSpace.single second 1) -
      fderiv ℝ (fun y : Space ↦ fderiv ℝ nonlinearField y
        (EuclideanSpace.single first 1)) x.1
        (EuclideanSpace.single second 1) = _
  rw [show fderiv ℝ (fun y : Space ↦ fderiv ℝ linearField y
        (EuclideanSpace.single first 1)) x.1
      (EuclideanSpace.single second 1) =
      reconstructedHeatH3SecondDerivative nuClock (Real.toNNReal t.1)
        (mul_pos (real_toNNReal_pos hnu) (by simpa using htpos))
        initial component first second x.1 by
    exact iterated_fderiv_reconstructedHeatH3Component
      nuClock (Real.toNNReal t.1)
        (mul_pos (real_toNNReal_pos hnu) (by simpa using htpos))
      initial component first second x.1]
  rw [show fderiv ℝ (fun y : Space ↦ fderiv ℝ nonlinearField y
        (EuclideanSpace.single first 1)) x.1
      (EuclideanSpace.single second 1) =
      sharpDuhamelSecondDerivativeChart nuClock (real_toNNReal_pos hnu)
        hT carrier.path t.1 component first second x by exact hsharp]

/-- Quantitative actual-field consequence of the exact decomposition.  The homogeneous and
nonlinear clock populations retain their distinct sharp exponents and are combined only after
both have been identified with derivatives of the same physical velocity field. -/
theorem norm_weightedClassicalRestartVelocity_secondDerivative_le
    {nu cap : ℝ} {hnu : 0 < nu} {hcap : 0 ≤ cap}
    {initial : PeriodicVectorWeightedSobolev 3}
    (carrier : WeightedClassicalRestartCarrier nu cap hnu hcap initial)
    (t : Icc (0 : ℝ) (weightedRestartTimeFromCap nu cap))
    (htpos : 0 < t.1) (hsmall : 2 * nu * t.1 ≤ 1)
    (component first second : Fin 3)
    (x : Metric.closedBall (0 : Space) 3) :
    ‖fderiv ℝ (fun y : Space ↦
      fderiv ℝ (fun z : Space ↦ weightedClassicalRestartVelocity
        (weightedRestartTimeFromCap_pos hnu hcap).le carrier.path z t.1 component) y
        (EuclideanSpace.single first 1)) x.1
        (EuclideanSpace.single second 1)‖ ≤
      sharpHeatSecondDerivativeH3Constant *
          (2 * (nu * t.1)) ^ (-1 / 4 : ℝ) * ‖initial component‖ +
        4 * sharpDuhamelSecondDerivativeConstant *
          nu ^ (-3 / 4 : ℝ) * t.1 ^ (1 / 4 : ℝ) * ‖carrier.path‖ ^ 2 := by
  let hT : 0 ≤ weightedRestartTimeFromCap nu cap :=
    (weightedRestartTimeFromCap_pos hnu hcap).le
  let nuClock : ℝ≥0 := Real.toNNReal nu
  have hclockSmall : 2 * (nuClock : ℝ) * t.1 ≤ 1 := by
    simpa [nuClock, Real.coe_toNNReal _ hnu.le] using hsmall
  have hheatSmall : 2 * ((nuClock : ℝ) * ((Real.toNNReal t.1 : ℝ≥0) : ℝ)) ≤ 1 := by
    simpa [Real.coe_toNNReal _ htpos.le, mul_assoc] using hclockSmall
  have hheatPos : 0 < (nuClock : ℝ) * ((Real.toNNReal t.1 : ℝ≥0) : ℝ) :=
    mul_pos (real_toNNReal_pos hnu) (by simpa using htpos)
  have hlinearPoint :
      ‖reconstructedHeatH3SecondDerivative nuClock (Real.toNNReal t.1)
        hheatPos initial component first second x.1‖ ≤
        sharpHeatSecondDerivativeH3Constant *
          (2 * (nu * t.1)) ^ (-1 / 4 : ℝ) * ‖initial component‖ := by
    calc
      _ = ‖reconstructedHeatH3SecondDerivativeChart nuClock (Real.toNNReal t.1)
          hheatPos initial component first second x‖ := rfl
      _ ≤ ‖reconstructedHeatH3SecondDerivativeChart nuClock (Real.toNNReal t.1)
          hheatPos initial component first second‖ :=
        (reconstructedHeatH3SecondDerivativeChart nuClock (Real.toNNReal t.1)
          hheatPos initial component first second).norm_coe_le_norm x
      _ ≤ sharpHeatSecondDerivativeH3Constant *
          (2 * ((nuClock : ℝ) * ((Real.toNNReal t.1 : ℝ≥0) : ℝ))) ^
            (-1 / 4 : ℝ) * ‖initial component‖ :=
        norm_reconstructedHeatH3SecondDerivativeChart_sharp
          nuClock (Real.toNNReal t.1) hheatPos hheatSmall
          initial component first second
      _ = _ := by
        rw [Real.coe_toNNReal _ hnu.le, Real.coe_toNNReal _ htpos.le]
  have hnonlinearPoint :
      ‖sharpDuhamelSecondDerivativeChart nuClock (real_toNNReal_pos hnu)
        hT carrier.path t.1 component first second x‖ ≤
        4 * sharpDuhamelSecondDerivativeConstant *
          nu ^ (-3 / 4 : ℝ) * t.1 ^ (1 / 4 : ℝ) * ‖carrier.path‖ ^ 2 := by
    calc
      _ ≤ ‖sharpDuhamelSecondDerivativeChart nuClock (real_toNNReal_pos hnu)
          hT carrier.path t.1 component first second‖ :=
        (sharpDuhamelSecondDerivativeChart nuClock (real_toNNReal_pos hnu)
          hT carrier.path t.1 component first second).norm_coe_le_norm x
      _ ≤ 4 * sharpDuhamelSecondDerivativeConstant *
          (nuClock : ℝ) ^ (-3 / 4 : ℝ) * t.1 ^ (1 / 4 : ℝ) *
            ‖carrier.path‖ ^ 2 :=
        norm_sharpDuhamelSecondDerivativeChart_le_path_norm
          nuClock (real_toNNReal_pos hnu) hT carrier.path t.2 htpos hclockSmall
          component first second
      _ = _ := by rw [Real.coe_toNNReal _ hnu.le]
  rw [weightedClassicalRestartVelocity_secondDerivative_eq_sharpHeat_sub_sharpDuhamel
    carrier t htpos hsmall component first second x]
  exact (norm_sub_le _ _).trans (add_le_add hlinearPoint hnonlinearPoint)

section Audit

#print axioms reconstructedVelocity_sub
#print axioms weightedClassicalRestartVelocity_eq_linearHeat_sub_weightedDuhamel
#print axioms weightedClassicalRestartOpenSolution_vorticityMode_mild_identity
#print axioms finiteOrderZero_vectorHeatH3ToH5_eq_periodicVectorWeightedHeat
#print axioms reconstructedVelocity_weightedLinearHeatPath_eq_reconstructedHeatH3Component
#print axioms weightedClassicalRestartVelocity_component_eq_sharpHeat_sub_weightedDuhamel
#print axioms differentiableAt_firstDirectional_reconstructedHeatH3Component
#print axioms differentiableAt_firstDirectional_reconstructedVelocity_weightedDuhamelReturn
#print axioms weightedClassicalRestartVelocity_secondDerivative_eq_sharpHeat_sub_sharpDuhamel
#print axioms norm_weightedClassicalRestartVelocity_secondDerivative_le

end Audit

end Soma.Holonics.Millennium.NavierStokesOpenMildFieldReconstruction
