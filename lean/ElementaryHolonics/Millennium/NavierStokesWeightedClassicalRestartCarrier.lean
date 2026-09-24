import Mathlib.Analysis.Calculus.FDeriv.Extend
import ElementaryHolonics.Millennium.NavierStokesCoordinateNativeMildRestart
import ElementaryHolonics.Millennium.NavierStokesWeightedSmoothClassicalMomentum
import ElementaryHolonics.Millennium.NavierStokesUniformRestart

/-!
# The weighted mild restart as a real classical interior carrier

**[proved-derived]** The smooth-path tower and classical-momentum owners return the exact
componentwise complex Fourier law.  This owner passes that law through the real-coordinate chart
and packages the canonical reconstructed velocity and pressure as an actual real periodic local
carrier.  The velocity is jointly continuous, spatially `C∞`, strongly differentiable in time at
every strict interior event, pointwise incompressible, and has its exact reconstructed initial
face.  The pressure is jointly continuous, spatially `C¹`, periodic, and its jointly continuous
gradient is the one occurring in the momentum equation.

This is deliberately not declared to be an `InteriorPeriodicRestart`.  That owner requires joint
spacetime `C∞` regularity of both fields on `Ico 0 T`; the present return supplies one time
derivative and arbitrary spatial derivatives for velocity, but only the established spatial `C¹`
pressure reconstruction.  The exact remaining upgrade is retained below as a separate regularity
port rather than hidden in the classical momentum statement.
-/

noncomputable section

open Filter Function Set InnerProductSpace
open scoped BigOperators ComplexConjugate ENNReal NNReal Laplacian

namespace Soma.Holonics.Millennium.NavierStokesWeightedClassicalRestartCarrier

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateNativeMildRestart
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesUniformRestart
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFourierDivergenceReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedMildPhysicalSource
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedMildSpacetimeMomentum
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedPressureReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedReconstructionContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothClassicalMomentum
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Canonical real fields -/

/-- The physical velocity field of a weighted restart, with position in the official first slot. -/
def weightedClassicalRestartVelocity
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) : VelocityField :=
  fun x t ↦ weightedReconstructedVelocity hT path t x

/-- The zero-gauge physical pressure field of a weighted restart. -/
def weightedClassicalRestartPressure
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) : PressureField :=
  fun x t ↦ weightedReconstructedPressure hT path t x

/-- The physical initial field reconstructed from the native weighted `H³` face. -/
def weightedClassicalRestartInitial
    (initial : PeriodicVectorWeightedSobolev 3) : InitialVelocity :=
  reconstructedVelocity initial

/-! ## Real and vector-valued momentum passage -/

/-- The actual real Navier--Stokes right-hand side on one weighted path face. -/
def weightedClassicalMomentumRHS
    {T : ℝ} (hT : 0 ≤ T) (nu : ℝ) (path : WeightedH3Path T)
    (t : ℝ) (x : Space) : Space :=
  nu • Δ (weightedReconstructedVelocity hT path t) x -
    fderiv ℝ (weightedReconstructedVelocity hT path t) x
      (weightedReconstructedVelocity hT path t x) -
    gradient (weightedReconstructedPressure hT path t) x

/-- The complexified scalar Laplacian in the Fourier momentum theorem is exactly the
complexification of the corresponding real scalar Laplacian. -/
theorem ofReal_laplacian_weightedReconstructedVelocity_component
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (t : Icc (0 : ℝ) T) (component : Fin 3) (x : Space) :
    ((Δ (fun y : Space ↦
        weightedReconstructedVelocity hT base t.1 y component) x : ℝ) : ℂ) =
      Δ (fun y : Space ↦
        (weightedReconstructedVelocity hT base t.1 y component : ℂ)) x := by
  have hfield :
      weightedReconstructedVelocity hT base t.1 =
        tower.reconstructedVelocity t := by
    rw [tower.reconstructedVelocity_eq_base]
    unfold weightedReconstructedVelocity
    rw [weightedPathExtension_of_mem hT base t.2]
  have hsmooth : ContDiff ℝ 2
      (fun y : Space ↦
        weightedReconstructedVelocity hT base t.1 y component) := by
    rw [hfield]
    have htower : ContDiff ℝ 2 (tower.reconstructedVelocity t) :=
      (tower.contDiff_infty_reconstructedVelocity t).of_le
        (show (2 : WithTop ℕ∞) ≤ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞) by
          change ((↑(2 : ℕ∞)) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
          exact WithTop.coe_le_coe.mpr
            (show (2 : ℕ∞) ≤ ⊤ by exact le_top))
    exact (EuclideanSpace.proj component).contDiff.comp htower
  have hcommute :=
    (hsmooth.contDiffAt (x := x)).laplacian_CLM_comp_left
      (l := Complex.ofRealCLM)
  simpa [Function.comp_def] using hcommute.symm

/-- Taking real parts of the established complex component law returns the standard real
component of the physical Navier--Stokes right-hand side. -/
theorem re_classicalMomentumRHS_complex_eq
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ)
    (t : Icc (0 : ℝ) T) (component : Fin 3) (x : Space) :
    ((nu : ℂ) *
          Δ (fun y : Space ↦
            (weightedReconstructedVelocity hT base t.1 y component : ℂ)) x -
        ∑ coordinate : Fin 3,
          (weightedReconstructedVelocity hT base t.1 x coordinate : ℂ) *
            fderiv ℝ
              (fun y : Space ↦
                (weightedReconstructedVelocity hT base t.1 y component : ℂ)) x
              (EuclideanSpace.single coordinate 1) -
        (weightedReconstructedPressureGradient
          hT base t.1 component x : ℂ)).re =
      weightedClassicalMomentumRHS hT nu base t.1 x component := by
  let u : InitialVelocity := weightedReconstructedVelocity hT base t.1
  let p : Space → ℝ := weightedReconstructedPressure hT base t.1
  have hfield : u = tower.reconstructedVelocity t := by
    dsimp [u]
    rw [tower.reconstructedVelocity_eq_base]
    unfold weightedReconstructedVelocity
    rw [weightedPathExtension_of_mem hT base t.2]
  have hu : ContDiff ℝ 2 u := by
    rw [hfield]
    exact (tower.contDiff_infty_reconstructedVelocity t).of_le
      (show (2 : WithTop ℕ∞) ≤ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞) by
        change ((↑(2 : ℕ∞)) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr
          (show (2 : ℕ∞) ≤ ⊤ by exact le_top))
  have hlaplacian :
      Δ (fun y : Space ↦ (u y component : ℂ)) x =
        (Δ (fun y : Space ↦ u y component) x : ℂ) := by
    have h := ofReal_laplacian_weightedReconstructedVelocity_component
      hT tower t component x
    simpa [u] using h.symm
  have hfderiv : ∀ coordinate : Fin 3,
      fderiv ℝ (fun y : Space ↦ (u y component : ℂ)) x
          (EuclideanSpace.single coordinate 1) =
        (fderiv ℝ (fun y : Space ↦ u y component) x
          (EuclideanSpace.single coordinate 1) : ℂ) := by
    intro coordinate
    have hcomponentSmooth : ContDiff ℝ 2 (fun y : Space ↦ u y component) := by
      simpa [Function.comp_def] using
        (EuclideanSpace.proj component).contDiff.comp hu
    have hcomponent : DifferentiableAt ℝ (fun y : Space ↦ u y component) x :=
      hcomponentSmooth.differentiable (by norm_num) x
    have hcomp := Complex.ofRealCLM.hasFDerivAt.comp x hcomponent.hasFDerivAt
    have happly := congrArg
      (fun L : Space →L[ℝ] ℂ ↦ L (EuclideanSpace.single coordinate 1))
      hcomp.fderiv
    simpa [Function.comp_def] using happly
  have hadvection :
      ∑ coordinate : Fin 3,
          u x coordinate *
            fderiv ℝ (fun y : Space ↦ u y component) x
              (EuclideanSpace.single coordinate 1) =
        fderiv ℝ u x (u x) component := by
    have huDiff : DifferentiableAt ℝ u x :=
      hu.differentiable (by norm_num) x
    have hcomponentFDeriv :=
      (EuclideanSpace.proj component).hasFDerivAt.comp x huDiff.hasFDerivAt
    have hcomponentApply : ∀ coordinate : Fin 3,
        fderiv ℝ (fun y : Space ↦ u y component) x
            (EuclideanSpace.single coordinate 1) =
          fderiv ℝ u x (EuclideanSpace.single coordinate 1) component := by
      intro coordinate
      have happly := congrArg
        (fun L : Space →L[ℝ] ℝ ↦ L (EuclideanSpace.single coordinate 1))
        hcomponentFDeriv.fderiv
      simpa [Function.comp_def] using happly
    simp_rw [hcomponentApply]
    simpa [advectionComponentLine, jacobianComponentLine,
      velocityComponentLine, affineSpatialLine, spatialBasisVector, mul_comm] using
      (advectionComponentLine_eq u x 0 component 0)
  have hlaplacianComponent :
      Δ (fun y : Space ↦ u y component) x = (Δ u x) component := by
    have hcommute :=
      (hu.contDiffAt (x := x)).laplacian_CLM_comp_left
        (l := EuclideanSpace.proj component)
    simpa [Function.comp_def] using hcommute
  have hpDiff : DifferentiableAt ℝ p x :=
    (contDiff_one_weightedReconstructedPressure hT base t.1).differentiable
      (by norm_num) x
  have hpressure :
      weightedReconstructedPressureGradient hT base t.1 component x =
        gradient p x component := by
    rw [← fderiv_weightedReconstructedPressure_apply_single
      hT base t.1 component x]
    rw [← EuclideanSpace.inner_basisFun_real
      (Fin 3) (gradient p x : Space) component]
    simpa [p] using (inner_gradient_left hpDiff :
      inner ℝ (gradient p x)
        (EuclideanSpace.basisFun (Fin 3) ℝ component) = fderiv ℝ p x
          (EuclideanSpace.basisFun (Fin 3) ℝ component)).symm
  change
    ((nu : ℂ) * Δ (fun y : Space ↦ (u y component : ℂ)) x -
        ∑ coordinate : Fin 3,
          (u x coordinate : ℂ) *
            fderiv ℝ (fun y : Space ↦ (u y component : ℂ)) x
              (EuclideanSpace.single coordinate 1) -
        (weightedReconstructedPressureGradient
          hT base t.1 component x : ℂ)).re =
      (nu • Δ u x - fderiv ℝ u x (u x) - gradient p x) component
  rw [hlaplacian]
  simp_rw [hfderiv]
  simp only [Complex.sub_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [hadvection, hpressure]
  rw [hlaplacianComponent]
  rfl

/-! ## Strong real time derivative -/

/-- The complex component momentum law descends to the standard real component equation. -/
theorem CoherentWeightedSmoothPathTower.fixedPoint_hasDerivAt_realClassicalMomentum_component
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (hdivergence : IsWeightedDivergenceFreePath base)
    (component : Fin 3) (x : Space) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun tau : ℝ ↦ weightedReconstructedVelocity hT base tau x component)
      (weightedClassicalMomentumRHS hT (nu : ℝ) base t x component) t := by
  have hcomplex :=
    Soma.Holonics.Millennium.NavierStokesWeightedSmoothClassicalMomentum.CoherentWeightedSmoothPathTower.fixedPoint_hasDerivAt_classicalMomentum_advection
      hT tower nu hnu initial hfixed hreal hdivergence component x ht
  have hrealDerivative :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hcomplex
  have hrealDerivative' : HasDerivAt
      (fun tau : ℝ ↦ weightedReconstructedVelocity hT base tau x component)
      (((nu : ℂ) *
            Δ (fun y : Space ↦
              (weightedReconstructedVelocity hT base t y component : ℂ)) x -
          ∑ coordinate : Fin 3,
            (weightedReconstructedVelocity hT base t x coordinate : ℂ) *
              fderiv ℝ
                (fun y : Space ↦
                  (weightedReconstructedVelocity hT base t y component : ℂ)) x
                (EuclideanSpace.single coordinate 1) -
          (weightedReconstructedPressureGradient
            hT base t component x : ℂ)).re) t := by
    simpa only [Function.comp_def, Complex.reCLM_apply,
      Complex.ofReal_re] using hrealDerivative
  have hrhs :
      ((nu : ℂ) *
            Δ (fun y : Space ↦
              (weightedReconstructedVelocity hT base t y component : ℂ)) x -
          ∑ coordinate : Fin 3,
            (weightedReconstructedVelocity hT base t x coordinate : ℂ) *
              fderiv ℝ
                (fun y : Space ↦
                  (weightedReconstructedVelocity hT base t y component : ℂ)) x
                (EuclideanSpace.single coordinate 1) -
          (weightedReconstructedPressureGradient
            hT base t component x : ℂ)).re =
        weightedClassicalMomentumRHS hT (nu : ℝ) base t x component := by
    simpa using re_classicalMomentumRHS_complex_eq hT tower (nu : ℝ)
      ⟨t, ⟨ht.1.le, ht.2.le⟩⟩ component x
  rw [hrhs] at hrealDerivative'
  exact hrealDerivative'

/-- The three real component derivatives reassemble through the Euclidean chart into one actual
`Space`-valued strong time derivative. -/
theorem CoherentWeightedSmoothPathTower.fixedPoint_hasDerivAt_realClassicalMomentum
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (hdivergence : IsWeightedDivergenceFreePath base)
    (x : Space) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (weightedClassicalRestartVelocity hT base x)
      (weightedClassicalMomentumRHS hT (nu : ℝ) base t x) t := by
  have hcoordinates : HasDerivAt
      (fun tau : ℝ ↦
        fun component : Fin 3 ↦
          weightedReconstructedVelocity hT base tau x component)
      (fun component : Fin 3 ↦
        weightedClassicalMomentumRHS hT (nu : ℝ) base t x component) t :=
    hasDerivAt_pi.mpr (fun component ↦
      CoherentWeightedSmoothPathTower.fixedPoint_hasDerivAt_realClassicalMomentum_component
        hT tower nu hnu initial hfixed hreal hdivergence component x ht)
  have hspace :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.hasFDerivAt.comp_hasDerivAt
      t hcoordinates
  change HasDerivAt
    (fun tau : ℝ ↦ weightedReconstructedVelocity hT base tau x)
    (weightedClassicalMomentumRHS hT (nu : ℝ) base t x) t
  exact hspace

/-! ## Physical pressure gradient and spatial receipts -/

/-- The three addressed pressure-gradient coefficients reassemble as Mathlib's actual metric
gradient of the reconstructed real pressure. -/
theorem vectorOf_weightedReconstructedPressureGradient_eq_gradient
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (t : ℝ) (x : Space) :
    vectorOfCoordinates (fun component : Fin 3 ↦
      weightedReconstructedPressureGradient hT path t component x) =
        gradient (weightedReconstructedPressure hT path t) x := by
  ext component
  rw [vectorOfCoordinates_apply]
  rw [← fderiv_weightedReconstructedPressure_apply_single
    hT path t component x]
  rw [← EuclideanSpace.inner_basisFun_real
    (Fin 3)
    (gradient (weightedReconstructedPressure hT path t) x : Space)
    component]
  have hpDiff : DifferentiableAt ℝ
      (weightedReconstructedPressure hT path t) x :=
    (contDiff_one_weightedReconstructedPressure hT path t).differentiable
      (by norm_num) x
  simpa using (inner_gradient_left hpDiff :
    inner ℝ (gradient (weightedReconstructedPressure hT path t) x)
        (EuclideanSpace.basisFun (Fin 3) ℝ component) =
      fderiv ℝ (weightedReconstructedPressure hT path t) x
        (EuclideanSpace.basisFun (Fin 3) ℝ component)).symm

/-- The physical pressure gradient is jointly continuous on the complete addressed closed
aperture. -/
theorem continuous_joint_gradient_weightedClassicalRestartPressure
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) :
    Continuous (fun z : Space × Icc (0 : ℝ) T ↦
      gradient (weightedReconstructedPressure hT path z.2.1) z.1) := by
  have hcoordinates : Continuous (fun z : Space × Icc (0 : ℝ) T ↦
      fun component : Fin 3 ↦
        weightedReconstructedPressureGradient
          hT path z.2.1 component z.1) :=
    continuous_pi (fun component ↦
      continuous_joint_weightedReconstructedPressureGradient
        hT path component)
  have hvector :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp hcoordinates
  convert hvector using 1
  funext z
  simpa [Function.comp_def, vectorOfCoordinates] using
    (vectorOf_weightedReconstructedPressureGradient_eq_gradient
      hT path z.2.1 z.1).symm

/-! ## Continuity of the classical time derivative -/

/-- At one physical point, the actual complexified scalar Laplacian varies continuously along
the addressed time aperture. -/
theorem CoherentWeightedSmoothPathTower.continuous_time_laplacian_component
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (hreal : IsWeightedFourierRealPath base)
    (component : Fin 3) (x : Space) :
    Continuous (fun t : Icc (0 : ℝ) T ↦
      Δ (fun y : Space ↦
        (weightedReconstructedVelocity hT base t.1 y component : ℂ)) x) := by
  have hsum : Continuous (fun t : Icc (0 : ℝ) T ↦
      ∑ coordinate : Fin 3,
        reconstructedFiniteOrderComplexComponent
          2 2 (by omega) (diagonalSecondWord coordinate)
            (tower.lift 2 t) component x) := by
    apply continuous_finset_sum
    intro coordinate _hcoordinate
    have hjoint := tower.continuous_joint_finiteDerivativeComponent
      2 2 (by omega) (diagonalSecondWord coordinate) component
    have htime := hjoint.comp
      (continuous_id.prodMk
        (continuous_const : Continuous (fun _ : Icc (0 : ℝ) T ↦
          euclideanToSpatialTorus x)))
    exact htime.congr (fun _ ↦ rfl)
  exact hsum.congr (fun t ↦
    (laplacian_weightedReconstructedVelocity_component_eq_secondWords
      hT tower hreal t component x).symm)

/-- One actual complexified spatial partial derivative varies continuously in addressed time. -/
theorem CoherentWeightedSmoothPathTower.continuous_time_fderiv_component_apply_single
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (hreal : IsWeightedFourierRealPath base)
    (component coordinate : Fin 3) (x : Space) :
    Continuous (fun t : Icc (0 : ℝ) T ↦
      fderiv ℝ
        (fun y : Space ↦
          (weightedReconstructedVelocity hT base t.1 y component : ℂ)) x
        (EuclideanSpace.single coordinate 1)) := by
  let emptyWord : Fin 0 → Fin 3 := fun i ↦ Fin.elim0 i
  let oneWord : Fin 1 → Fin 3 := Fin.cons coordinate emptyWord
  have hword : Continuous (fun t : Icc (0 : ℝ) T ↦
      reconstructedFiniteOrderComplexComponent
        1 1 (by omega) oneWord (tower.lift 1 t) component x) := by
    have hjoint := tower.continuous_joint_finiteDerivativeComponent
      1 1 (by omega) oneWord component
    have htime := hjoint.comp
      (continuous_id.prodMk
        (continuous_const : Continuous (fun _ : Icc (0 : ℝ) T ↦
          euclideanToSpatialTorus x)))
    exact htime.congr (fun _ ↦ rfl)
  apply hword.congr
  intro t
  have hzero :
      reconstructedFiniteOrderComplexComponent
          1 0 (by omega) emptyWord (tower.lift 1 t) component =
        (fun y : Space ↦
          (weightedReconstructedVelocity hT base t.1 y component : ℂ)) := by
    funext y
    exact reconstructedFiniteOrderComplexComponent_zero_eq_weightedVelocity
      hT tower hreal 1 t component y
  have hderivative := tower.fderiv_finiteDerivative_apply_single
    1 0 (by omega) emptyWord t component coordinate x
  rw [hzero] at hderivative
  exact hderivative.symm

/-- For one physical receiver, the complete actual real vector momentum right-hand side is
continuous in addressed time. -/
theorem CoherentWeightedSmoothPathTower.continuous_time_weightedClassicalMomentumRHS
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ) (hreal : IsWeightedFourierRealPath base)
    (x : Space) :
    Continuous (fun t : Icc (0 : ℝ) T ↦
      weightedClassicalMomentumRHS hT nu base t.1 x) := by
  have hvelocity : ∀ component : Fin 3,
      Continuous (fun t : Icc (0 : ℝ) T ↦
        (weightedReconstructedVelocity hT base t.1 x component : ℂ)) := by
    intro component
    have hjoint := continuous_joint_weightedReconstructedVelocity hT base
    have htime := hjoint.comp
      (continuous_const.prodMk continuous_id :
        Continuous (fun t : Icc (0 : ℝ) T ↦ (x, t)))
    exact Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj component).continuous.comp htime)
  have hpartial : ∀ component coordinate : Fin 3,
      Continuous (fun t : Icc (0 : ℝ) T ↦
        fderiv ℝ
          (fun y : Space ↦
            (weightedReconstructedVelocity hT base t.1 y component : ℂ)) x
          (EuclideanSpace.single coordinate 1)) :=
    fun component coordinate ↦
      CoherentWeightedSmoothPathTower.continuous_time_fderiv_component_apply_single
        hT tower hreal component coordinate x
  have hlaplacian : ∀ component : Fin 3,
      Continuous (fun t : Icc (0 : ℝ) T ↦
        Δ (fun y : Space ↦
          (weightedReconstructedVelocity hT base t.1 y component : ℂ)) x) :=
    fun component ↦
      CoherentWeightedSmoothPathTower.continuous_time_laplacian_component
        hT tower hreal component x
  have hpressure : ∀ component : Fin 3,
      Continuous (fun t : Icc (0 : ℝ) T ↦
        (weightedReconstructedPressureGradient
          hT base t.1 component x : ℂ)) := by
    intro component
    have hjoint := continuous_joint_weightedReconstructedPressureGradient
      hT base component
    have htime := hjoint.comp
      (continuous_const.prodMk continuous_id :
        Continuous (fun t : Icc (0 : ℝ) T ↦ (x, t)))
    exact Complex.continuous_ofReal.comp htime
  have hcomponent : ∀ component : Fin 3,
      Continuous (fun t : Icc (0 : ℝ) T ↦
        weightedClassicalMomentumRHS hT nu base t.1 x component) := by
    intro component
    have hadvection : Continuous (fun t : Icc (0 : ℝ) T ↦
        ∑ coordinate : Fin 3,
          (weightedReconstructedVelocity hT base t.1 x coordinate : ℂ) *
            fderiv ℝ
              (fun y : Space ↦
                (weightedReconstructedVelocity hT base t.1 y component : ℂ)) x
              (EuclideanSpace.single coordinate 1)) := by
      apply continuous_finset_sum
      intro coordinate _hcoordinate
      exact (hvelocity coordinate).mul (hpartial component coordinate)
    have hcomplex : Continuous (fun t : Icc (0 : ℝ) T ↦
        (nu : ℂ) *
            Δ (fun y : Space ↦
              (weightedReconstructedVelocity hT base t.1 y component : ℂ)) x -
          ∑ coordinate : Fin 3,
            (weightedReconstructedVelocity hT base t.1 x coordinate : ℂ) *
              fderiv ℝ
                (fun y : Space ↦
                  (weightedReconstructedVelocity hT base t.1 y component : ℂ)) x
                (EuclideanSpace.single coordinate 1) -
          (weightedReconstructedPressureGradient
            hT base t.1 component x : ℂ)) :=
      (continuous_const.mul (hlaplacian component)).sub hadvection |>.sub
        (hpressure component)
    have hre := Complex.continuous_re.comp hcomplex
    exact hre.congr (fun t ↦
      re_classicalMomentumRHS_complex_eq hT tower nu t component x)
  have hcoordinates : Continuous (fun t : Icc (0 : ℝ) T ↦
      fun component : Fin 3 ↦
        weightedClassicalMomentumRHS hT nu base t.1 x component) :=
    continuous_pi hcomponent
  have hspace :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp hcoordinates
  simpa [Function.comp_def, vectorOfCoordinates] using hspace

/-- Endpoint projection makes the physical velocity at a fixed spatial receiver a continuous
function of the complete real time word. -/
theorem continuous_weightedClassicalRestartVelocity_time
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) (x : Space) :
    Continuous (weightedClassicalRestartVelocity hT path x) := by
  have hcomponent : ∀ component : Fin 3,
      Continuous (fun t : ℝ ↦
        weightedClassicalRestartVelocity hT path x t component) := by
    intro component
    have hnative : Continuous (fun t : ℝ ↦
        reconstructedTorusComplexComponentCLM component
          (weightedPathExtension hT path t)) :=
      (reconstructedTorusComplexComponentCLM component).continuous.comp
        (weightedPathExtension hT path).continuous
    have heval : Continuous (fun t : ℝ ↦
        reconstructedTorusComplexComponentCLM component
          (weightedPathExtension hT path t)
          (euclideanToSpatialTorus x)) :=
      hnative.eval continuous_const
    have hre := Complex.continuous_re.comp heval
    change Continuous (Complex.re ∘ fun t : ℝ ↦
      reconstructedTorusComplexComponent
        (weightedPathExtension hT path t) component
          (euclideanToSpatialTorus x))
    exact hre
  have hcoordinates : Continuous (fun t : ℝ ↦
      fun component : Fin 3 ↦
        weightedClassicalRestartVelocity hT path x t component) :=
    continuous_pi hcomponent
  have hspace :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp hcoordinates
  simpa [Function.comp_def, vectorOfCoordinates] using hspace

/-- Continuity of the assembled classical right-hand side closes the initial face as an actual
right derivative.  No endpoint PDE premise is added. -/
theorem CoherentWeightedSmoothPathTower.fixedPoint_hasDerivWithinAt_zero_realClassicalMomentum
    {T : ℝ} (hTpos : 0 < T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hTpos.le initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (hdivergence : IsWeightedDivergenceFreePath base)
    (x : Space) :
    HasDerivWithinAt
      (weightedClassicalRestartVelocity hTpos.le base x)
      (weightedClassicalMomentumRHS hTpos.le (nu : ℝ) base 0 x)
      (Ici (0 : ℝ)) 0 := by
  let f : ℝ → Space := weightedClassicalRestartVelocity hTpos.le base x
  let rhsOnAperture : Icc (0 : ℝ) T → Space := fun t ↦
    weightedClassicalMomentumRHS hTpos.le (nu : ℝ) base t.1 x
  let rhsProjected : ℝ → Space := fun t ↦
    rhsOnAperture (Set.projIcc 0 T hTpos.le t)
  have hfContinuous : Continuous f :=
    continuous_weightedClassicalRestartVelocity_time hTpos.le base x
  have hrhsAperture : Continuous rhsOnAperture := by
    exact CoherentWeightedSmoothPathTower.continuous_time_weightedClassicalMomentumRHS
      hTpos.le tower (nu : ℝ) hreal x
  have hrhsProjected : Continuous rhsProjected :=
    hrhsAperture.comp continuous_projIcc
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
      (s := Ioo (0 : ℝ) T)
  · intro t ht
    exact (CoherentWeightedSmoothPathTower.fixedPoint_hasDerivAt_realClassicalMomentum
      hTpos.le tower nu hnu initial hfixed hreal hdivergence x ht).differentiableAt
      |>.differentiableWithinAt
  · exact hfContinuous.continuousWithinAt
  · exact Ioo_mem_nhdsGT hTpos
  · have hlimit : Tendsto rhsProjected (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (weightedClassicalMomentumRHS
          hTpos.le (nu : ℝ) base 0 x)) := by
      have hcontinuousAt := hrhsProjected.continuousAt (x := (0 : ℝ))
      have hzero : rhsProjected 0 =
          weightedClassicalMomentumRHS hTpos.le (nu : ℝ) base 0 x := by
        simp [rhsProjected, rhsOnAperture]
      have htendsto : Tendsto rhsProjected (nhds (0 : ℝ))
          (nhds (rhsProjected 0)) := hcontinuousAt
      rw [hzero] at htendsto
      exact htendsto.mono_left inf_le_left
    apply hlimit.congr'
    filter_upwards [Ioo_mem_nhdsGT hTpos] with t ht
    have hderiv :=
      (CoherentWeightedSmoothPathTower.fixedPoint_hasDerivAt_realClassicalMomentum
        hTpos.le tower nu hnu initial hfixed hreal hdivergence x ht).deriv
    rw [hderiv]
    dsimp [rhsProjected, rhsOnAperture]
    rw [Set.projIcc_of_mem hTpos.le ⟨ht.1.le, ht.2.le⟩]

/-- Every addressed tower face is the canonical reconstructed velocity and hence is pointwise
incompressible on the modewise divergence-free fibre. -/
theorem divergence_weightedClassicalRestartVelocity_eq_zero
    {T : ℝ} (hT : 0 ≤ T) {path : WeightedH3Path T}
    (hdivergence : IsWeightedDivergenceFreePath path)
    (t : Icc (0 : ℝ) T) (x : Space) :
    divergence (fun y ↦ weightedClassicalRestartVelocity hT path y t.1) x = 0 := by
  change divergence
    (reconstructedVelocity (weightedPathExtension hT path t.1)) x = 0
  rw [weightedPathExtension_of_mem hT path t.2]
  exact divergence_reconstructedVelocity_eq_zero (hdivergence t) x

/-- The exact native initial face reconstructs to the exact physical initial field. -/
theorem weightedClassicalRestartVelocity_zero
    {T : ℝ} (hT : 0 ≤ T) {path : WeightedH3Path T}
    {initial : PeriodicVectorWeightedSobolev 3}
    (hinitial : path ⟨0, ⟨le_rfl, hT⟩⟩ = initial) (x : Space) :
    weightedClassicalRestartVelocity hT path x 0 =
      weightedClassicalRestartInitial initial x := by
  change reconstructedVelocity (weightedPathExtension hT path 0) x =
    reconstructedVelocity initial x
  rw [weightedPathExtension_of_mem hT path ⟨le_rfl, hT⟩, hinitial]

/-! ## An honest anisotropic classical local carrier -/

/-- A real periodic local Navier--Stokes carrier with the exact anisotropic regularity currently
returned by the weighted construction: one strong interior time derivative, a spatially `C∞`
velocity, a spatially `C¹` pressure with its actual jointly continuous gradient, and joint
continuity of both fields. -/
structure RealPeriodicClassicalRestartCarrier
    (T nu : ℝ) (initial : InitialVelocity)
    (velocity : VelocityField) (pressure : PressureField) : Prop where
  terminal_pos : 0 < T
  interiorMomentum : ∀ (x : Space) {t : ℝ}, t ∈ Ioo (0 : ℝ) T →
    HasDerivAt (velocity x)
      (nu • Δ (fun y ↦ velocity y t) x -
        fderiv ℝ (fun y ↦ velocity y t) x (velocity x t) -
        gradient (fun y ↦ pressure y t) x) t
  initialMomentum : ∀ x : Space,
    HasDerivWithinAt (velocity x)
      (nu • Δ (fun y ↦ velocity y 0) x -
        fderiv ℝ (fun y ↦ velocity y 0) x (velocity x 0) -
        gradient (fun y ↦ pressure y 0) x)
      (Ici (0 : ℝ)) 0
  incompressible : ∀ (x : Space) (t : Icc (0 : ℝ) T),
    divergence (fun y ↦ velocity y t.1) x = 0
  initial : ∀ x, velocity x 0 = initial x
  velocitySpatialSmooth : ∀ t : Icc (0 : ℝ) T,
    ContDiff ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞) (fun x ↦ velocity x t.1)
  pressureSpatialC1 : ∀ t : Icc (0 : ℝ) T,
    ContDiff ℝ 1 (fun x ↦ pressure x t.1)
  jointVelocity : Continuous (fun z : Space × Icc (0 : ℝ) T ↦
    velocity z.1 z.2.1)
  jointPressure : Continuous (fun z : Space × Icc (0 : ℝ) T ↦
    pressure z.1 z.2.1)
  jointPressureGradient : Continuous (fun z : Space × Icc (0 : ℝ) T ↦
    gradient (fun y ↦ pressure y z.2.1) z.1)
  velocityPeriodic : ∀ t : Icc (0 : ℝ) T,
    IsOnePeriodic (fun x ↦ velocity x t.1)
  pressurePeriodic : ∀ t : Icc (0 : ℝ) T,
    IsOnePeriodic (fun x ↦ pressure x t.1)

/-- The strong time-derivative receipt implies the standard vector momentum equality at every
strict interior event. -/
theorem RealPeriodicClassicalRestartCarrier.interiorMomentumEquation
    {T nu : ℝ} {initial : InitialVelocity}
    {velocity : VelocityField} {pressure : PressureField}
    (carrier : RealPeriodicClassicalRestartCarrier
      T nu initial velocity pressure)
    (x : Space) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    deriv (velocity x) t +
        fderiv ℝ (fun y ↦ velocity y t) x (velocity x t) =
      nu • Δ (fun y ↦ velocity y t) x -
        gradient (fun y ↦ pressure y t) x := by
  rw [(carrier.interiorMomentum x ht).deriv]
  abel

/-- The carrier already satisfies the official within-derivative momentum law at every point of
the half-open lifespan; joint `C∞` regularity is not used here. -/
theorem RealPeriodicClassicalRestartCarrier.momentumEquationOnOpenSlab
    {T nu : ℝ} {initial : InitialVelocity}
    {velocity : VelocityField} {pressure : PressureField}
    (carrier : RealPeriodicClassicalRestartCarrier
      T nu initial velocity pressure)
    (x : Space) {t : ℝ} (ht : t ∈ openTimeSlab T) :
    derivWithin (velocity x) (openTimeSlab T) t +
        fderiv ℝ (fun y ↦ velocity y t) x (velocity x t) =
      nu • Δ (fun y ↦ velocity y t) x -
        gradient (fun y ↦ pressure y t) x := by
  rcases ht.1.eq_or_lt with hzero | htpos
  · subst t
    have hwithin := (carrier.initialMomentum x).mono (show
        openTimeSlab T ⊆ Ici (0 : ℝ) by
      intro tau (htau : tau ∈ openTimeSlab T)
      exact htau.1)
    have hderivative := hwithin.derivWithin
      ((uniqueDiffOn_Ico (0 : ℝ) T).uniqueDiffWithinAt ht)
    rw [hderivative]
    abel
  · have hderivative := (carrier.interiorMomentum x ⟨htpos, ht.2⟩).deriv
    have hopen : openTimeSlab T ∈ nhds t := by
      exact Ico_mem_nhds htpos ht.2
    rw [derivWithin_of_mem_nhds hopen, hderivative]
    abel

/-! ## The exact `InteriorPeriodicRestart` smoothness port -/

/-- The only regularity still absent from the classical carrier but demanded by
`OpenPeriodicSolutionOn`: joint spacetime `C∞` for velocity and pressure on `Ico 0 T`.  The
endpoint momentum equation has already been derived above. -/
structure JointSpacetimeSmoothnessUpgrade
    {T nu : ℝ} {initial : InitialVelocity}
    {velocity : VelocityField} {pressure : PressureField}
    (carrier : RealPeriodicClassicalRestartCarrier
      T nu initial velocity pressure) : Prop where
  velocitySmooth :
    ContDiffOn ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞) (Function.uncurry velocity)
      (Soma.Holonics.Millennium.NavierStokesOpenLifespan.openSpaceTimeSlab T)
  pressureSmooth :
    ContDiffOn ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞) (Function.uncurry pressure)
      (Soma.Holonics.Millennium.NavierStokesOpenLifespan.openSpaceTimeSlab T)

/-- Joint spacetime smoothness promotes the anisotropic carrier to the exact official open
periodic solution type. -/
def RealPeriodicClassicalRestartCarrier.toOpenPeriodicSolutionOn
    {T nu : ℝ} {initial : InitialVelocity}
    {velocity : VelocityField} {pressure : PressureField}
    (carrier : RealPeriodicClassicalRestartCarrier
      T nu initial velocity pressure)
    (upgrade : JointSpacetimeSmoothnessUpgrade carrier) :
    OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure where
  terminal_pos := carrier.terminal_pos
  momentum x t ht := by
    simpa using carrier.momentumEquationOnOpenSlab x ht
  incompressible x t ht :=
    carrier.incompressible x ⟨t, ⟨ht.1, ht.2.le⟩⟩
  initial := carrier.initial
  velocitySmooth := upgrade.velocitySmooth
  pressureSmooth := upgrade.pressureSmooth
  velocityPeriodic t ht :=
    carrier.velocityPeriodic ⟨t, ⟨ht.1, ht.2.le⟩⟩
  pressurePeriodic t ht :=
    carrier.pressurePeriodic ⟨t, ⟨ht.1, ht.2.le⟩⟩

/-- Conversely, an official open periodic solution supplies precisely the missing joint
smoothness receipt. -/
def jointSpacetimeSmoothnessUpgrade_of_openPeriodicSolutionOn
    {T nu : ℝ} {initial : InitialVelocity}
    {velocity : VelocityField} {pressure : PressureField}
    (carrier : RealPeriodicClassicalRestartCarrier
      T nu initial velocity pressure)
    (solution : OpenPeriodicSolutionOn
      T nu initial (0 : VelocityField) velocity pressure) :
    JointSpacetimeSmoothnessUpgrade carrier where
  velocitySmooth := solution.velocitySmooth
  pressureSmooth := solution.pressureSmooth

/-- Thus the exact residual between this carrier and `OpenPeriodicSolutionOn` is the declared
joint spacetime smoothness pair, and no hidden PDE premise. -/
theorem openPeriodicSolutionOn_iff_jointSpacetimeSmoothnessUpgrade
    {T nu : ℝ} {initial : InitialVelocity}
    {velocity : VelocityField} {pressure : PressureField}
    (carrier : RealPeriodicClassicalRestartCarrier
      T nu initial velocity pressure) :
    OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure ↔
      JointSpacetimeSmoothnessUpgrade carrier := by
  constructor
  · exact jointSpacetimeSmoothnessUpgrade_of_openPeriodicSolutionOn carrier
  · exact carrier.toOpenPeriodicSolutionOn

/-- The cap-selected native occurrence together with its coherent spatial tower and its complete
real classical carrier. -/
structure WeightedClassicalRestartCarrier
    (nu cap : ℝ) (hnu : 0 < nu) (hcap : 0 ≤ cap)
    (initial : PeriodicVectorWeightedSobolev 3) where
  path : WeightedH3Path (weightedRestartTimeFromCap nu cap)
  pathNorm : ‖path‖ ≤ weightedRestartRadiusFromCap cap
  fixed : IsFixedPt (weightedMildRestartMap nu cap hnu hcap initial) path
  initialFace :
    path ⟨0, ⟨le_rfl, (weightedRestartTimeFromCap_pos hnu hcap).le⟩⟩ = initial
  fourierReal : IsWeightedFourierRealPath path
  divergenceFree : IsWeightedDivergenceFreePath path
  tower : CoherentWeightedSmoothPathTower path
  classical : RealPeriodicClassicalRestartCarrier
    (weightedRestartTimeFromCap nu cap) nu
    (weightedClassicalRestartInitial initial)
    (weightedClassicalRestartVelocity
      (weightedRestartTimeFromCap_pos hnu hcap).le path)
    (weightedClassicalRestartPressure
      (weightedRestartTimeFromCap_pos hnu hcap).le path)

/-- A native invariant mild restart carrying a coherent all-order lift packages into the honest
real periodic classical carrier above, without adding any PDE or smoothness premise. -/
noncomputable def weightedClassicalRestartCarrierOfNative
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    (initial : PeriodicVectorWeightedSobolev 3)
    (restart : NativeMildRestartAtCap nu cap hnu hcap initial)
    (tower : CoherentWeightedSmoothPathTower restart.path) :
    WeightedClassicalRestartCarrier nu cap hnu hcap initial := by
  let hT : 0 ≤ weightedRestartTimeFromCap nu cap :=
    (weightedRestartTimeFromCap_pos hnu hcap).le
  have hfixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu) hT initial)
      restart.path := by
    simpa only [weightedMildRestartMap] using restart.fixed
  refine
    { path := restart.path
      pathNorm := restart.pathNorm
      fixed := restart.fixed
      initialFace := restart.initialFace
      fourierReal := restart.fourierReal
      divergenceFree := restart.divergenceFree
      tower := tower
      classical := ?_ }
  refine
    { terminal_pos := weightedRestartTimeFromCap_pos hnu hcap
      interiorMomentum := ?_
      initialMomentum := ?_
      incompressible := ?_
      initial := ?_
      velocitySpatialSmooth := ?_
      pressureSpatialC1 := ?_
      jointVelocity := ?_
      jointPressure := ?_
      jointPressureGradient := ?_
      velocityPeriodic := ?_
      pressurePeriodic := ?_ }
  · intro x t ht
    simpa only [weightedClassicalRestartVelocity,
      weightedClassicalRestartPressure, weightedClassicalMomentumRHS,
      Real.coe_toNNReal _ hnu.le] using
      CoherentWeightedSmoothPathTower.fixedPoint_hasDerivAt_realClassicalMomentum
        hT tower (Real.toNNReal nu) (real_toNNReal_pos hnu) initial
        hfixed restart.fourierReal restart.divergenceFree x ht
  · intro x
    simpa only [weightedClassicalRestartVelocity,
      weightedClassicalRestartPressure, weightedClassicalMomentumRHS,
      Real.coe_toNNReal _ hnu.le] using
      CoherentWeightedSmoothPathTower.fixedPoint_hasDerivWithinAt_zero_realClassicalMomentum
        (weightedRestartTimeFromCap_pos hnu hcap) tower
        (Real.toNNReal nu) (real_toNNReal_pos hnu) initial hfixed
        restart.fourierReal restart.divergenceFree x
  · intro x t
    exact divergence_weightedClassicalRestartVelocity_eq_zero
      hT restart.divergenceFree t x
  · intro x
    exact weightedClassicalRestartVelocity_zero
      hT restart.initialFace x
  · intro t
    have hfield :
        (fun x ↦ weightedClassicalRestartVelocity hT restart.path x t.1) =
          tower.reconstructedVelocity t := by
      rw [tower.reconstructedVelocity_eq_base]
      funext x
      change reconstructedVelocity
          (weightedPathExtension hT restart.path t.1) x =
        reconstructedVelocity (restart.path t) x
      rw [weightedPathExtension_of_mem hT restart.path t.2]
    rw [hfield]
    exact tower.contDiff_infty_reconstructedVelocity t
  · intro t
    exact contDiff_one_weightedReconstructedPressure hT restart.path t.1
  · simpa only [weightedClassicalRestartVelocity] using
      continuous_joint_weightedReconstructedVelocity hT restart.path
  · simpa only [weightedClassicalRestartPressure] using
      continuous_joint_weightedReconstructedPressure hT restart.path
  · simpa only [weightedClassicalRestartPressure] using
      continuous_joint_gradient_weightedClassicalRestartPressure
        hT restart.path
  · intro t
    exact isOnePeriodic_weightedReconstructedVelocity hT restart.path t.1
  · intro t
    exact isOnePeriodic_weightedReconstructedPressure hT restart.path t.1

/-! ## Exact derivative-word access and the official smooth upgrade -/

/-- Every finite ordered spatial derivative retained by the carrier is jointly continuous in
time and torus position. -/
theorem WeightedClassicalRestartCarrier.continuous_joint_spatialDerivativeWord
    {nu cap : ℝ} {hnu : 0 < nu} {hcap : 0 ≤ cap}
    {initial : PeriodicVectorWeightedSobolev 3}
    (carrier : WeightedClassicalRestartCarrier nu cap hnu hcap initial)
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3)
    (component : Fin 3) :
    Continuous (fun z :
        Icc (0 : ℝ) (weightedRestartTimeFromCap nu cap) × SpatialTorus ↦
      reconstructedFiniteOrderTorusComplexComponent
        m r hr word (carrier.tower.lift m z.1) component z.2) :=
  carrier.tower.continuous_joint_finiteDerivativeComponent
    m r hr word component

/-- Prepending one coordinate to any retained word is the actual spatial Fréchet derivative at
every addressed face. -/
theorem WeightedClassicalRestartCarrier.fderiv_spatialDerivativeWord_apply_single
    {nu cap : ℝ} {hnu : 0 < nu} {hcap : 0 ≤ cap}
    {initial : PeriodicVectorWeightedSobolev 3}
    (carrier : WeightedClassicalRestartCarrier nu cap hnu hcap initial)
    (m r : ℕ) (hr : r + 1 ≤ m) (word : Fin r → Fin 3)
    (t : Icc (0 : ℝ) (weightedRestartTimeFromCap nu cap))
    (component coordinate : Fin 3) (x : Space) :
    fderiv ℝ
        (reconstructedFiniteOrderComplexComponent
          m r (by omega) word (carrier.tower.lift m t) component) x
        (EuclideanSpace.single coordinate 1) =
      reconstructedFiniteOrderComplexComponent
        m (r + 1) hr (Fin.cons coordinate word)
          (carrier.tower.lift m t) component x :=
  carrier.tower.fderiv_finiteDerivative_apply_single
    m r hr word t component coordinate x

/-- Supplying exactly the missing joint spacetime smoothness pair promotes a weighted carrier to
an official unforced open periodic solution on its native aperture. -/
def WeightedClassicalRestartCarrier.toOpenPeriodicSolutionOn
    {nu cap : ℝ} {hnu : 0 < nu} {hcap : 0 ≤ cap}
    {initial : PeriodicVectorWeightedSobolev 3}
    (carrier : WeightedClassicalRestartCarrier nu cap hnu hcap initial)
    (upgrade : JointSpacetimeSmoothnessUpgrade carrier.classical) :
    OpenPeriodicSolutionOn
      (weightedRestartTimeFromCap nu cap) nu
      (weightedClassicalRestartInitial initial) (0 : VelocityField)
      (weightedClassicalRestartVelocity
        (weightedRestartTimeFromCap_pos hnu hcap).le carrier.path)
      (weightedClassicalRestartPressure
        (weightedRestartTimeFromCap_pos hnu hcap).le carrier.path) :=
  carrier.classical.toOpenPeriodicSolutionOn upgrade

section Audit

#print axioms ofReal_laplacian_weightedReconstructedVelocity_component
#print axioms re_classicalMomentumRHS_complex_eq
#print axioms CoherentWeightedSmoothPathTower.fixedPoint_hasDerivAt_realClassicalMomentum
#print axioms CoherentWeightedSmoothPathTower.continuous_time_weightedClassicalMomentumRHS
#print axioms CoherentWeightedSmoothPathTower.fixedPoint_hasDerivWithinAt_zero_realClassicalMomentum
#print axioms openPeriodicSolutionOn_iff_jointSpacetimeSmoothnessUpgrade
#print axioms weightedClassicalRestartCarrierOfNative
#print axioms WeightedClassicalRestartCarrier.continuous_joint_spatialDerivativeWord
#print axioms WeightedClassicalRestartCarrier.toOpenPeriodicSolutionOn

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedClassicalRestartCarrier
