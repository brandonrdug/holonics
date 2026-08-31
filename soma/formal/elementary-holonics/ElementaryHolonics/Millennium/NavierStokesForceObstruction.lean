import ElementaryHolonics.Millennium.NavierStokesOpenEnstrophy

/-!
# Future-force obstruction to open-lifespan continuation

`OpenPeriodicSolutionOn T` constrains the force only on `Ico 0 T`.  Consequently an interior
critical-control receipt cannot, by itself, imply extension for an arbitrary fixed force.  This
module gives the exact counterexample: velocity and pressure are zero, and the force is zero before
`T`, but at `T` its spatial slice becomes a discontinuous singleton spike.

Any compatible extension would contain `T` as an interior time.  Restricting it to a slightly
longer closed slab and applying `smoothSolutionOn_forceSpatialSmooth` would make that spike `C²`,
contradicting its discontinuity.  Thus future-force admissibility is a material hypothesis of any
continuation theorem; it cannot be recovered from interior vorticity or Jacobian control.
-/

noncomputable section

open ContDiff InnerProductSpace Set
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesForceObstruction

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesVorticity

/-! ## A spatially discontinuous terminal slice -/

/-- A fixed nonzero spatial direction used by the singleton spike. -/
def spikeValue : Space := EuclideanSpace.single (0 : Fin 3) 1

theorem spikeValue_ne_zero : spikeValue ≠ 0 := by
  intro h
  have hcoord := congrArg (fun v : Space => v (0 : Fin 3)) h
  norm_num [spikeValue] at hcoord

/-- A singleton spatial spike: nonzero at the origin and zero everywhere else. -/
def spatialSpike : InitialVelocity := fun x => if x = 0 then spikeValue else 0

@[simp]
theorem spatialSpike_zero : spatialSpike 0 = spikeValue := by
  simp [spatialSpike]

/-- The singleton spike is not continuous.  Two continuous maps agreeing off the origin would
agree everywhere because the punctured Euclidean space is dense. -/
theorem spatialSpike_not_continuous : ¬ Continuous spatialSpike := by
  intro hcontinuous
  have heq : spatialSpike = (0 : InitialVelocity) := by
    apply Continuous.ext_on (dense_compl_singleton (0 : Space))
      hcontinuous continuous_zero
    intro x hx
    have hxne : x ≠ 0 := by simpa using hx
    simp [spatialSpike, hxne]
  have hatZero := congrFun heq (0 : Space)
  exact spikeValue_ne_zero (by simpa using hatZero)

/-- In particular the spike cannot be `C²`. -/
theorem spatialSpike_not_contDiff_two : ¬ ContDiff ℝ 2 spatialSpike := by
  intro hsmooth
  exact spatialSpike_not_continuous hsmooth.continuous

/-! ## The force and its zero interior solution -/

/-- Zero before `T`, then the spatial singleton spike from the terminal face onward. -/
def terminalSpikeForce (T : ℝ) : VelocityField :=
  fun x t => if t < T then 0 else spatialSpike x

@[simp]
theorem terminalSpikeForce_of_lt {T t : ℝ} (ht : t < T) (x : Space) :
    terminalSpikeForce T x t = 0 := by
  simp [terminalSpikeForce, ht]

@[simp]
theorem terminalSpikeForce_at_terminal (T : ℝ) (x : Space) :
    terminalSpikeForce T x T = spatialSpike x := by
  simp [terminalSpikeForce]

/-- The zero velocity and zero pressure solve the open-lifespan equations because the force is
identically zero at every time represented by the carrier. -/
def zeroOpenPeriodicSolution (T nu : ℝ) (hT : 0 < T) :
    OpenPeriodicSolutionOn T nu 0 (terminalSpikeForce T) 0 0 where
  terminal_pos := hT
  momentum x t ht := by
    have hlaplacian : Δ (fun _ : Space => (0 : Space)) x = 0 := by
      simpa using
        (laplacian_smul (f := fun y : Space => y) (x := x) (0 : ℝ)
          contDiff_id.contDiffAt)
    simp [terminalSpikeForce, ht.2, hlaplacian]
  incompressible x t ht := by
    simp [divergence]
  initial x := rfl
  velocitySmooth := by
    change ContDiffOn ℝ ∞ (fun _ : Space × ℝ => (0 : Space))
      (NavierStokesOpenLifespan.openSpaceTimeSlab T)
    exact (contDiff_const : ContDiff ℝ ∞
      (fun _ : Space × ℝ => (0 : Space))).contDiffOn
  pressureSmooth := by
    change ContDiffOn ℝ ∞ (fun _ : Space × ℝ => (0 : ℝ))
      (NavierStokesOpenLifespan.openSpaceTimeSlab T)
    exact (contDiff_const : ContDiff ℝ ∞
      (fun _ : Space × ℝ => (0 : ℝ))).contDiffOn
  velocityPeriodic t ht := by
    intro x i
    rfl
  pressurePeriodic t ht := by
    intro x i
    rfl

/-! ## Exact failure of compatible extension -/

/-- No compatible extension exists: a longer solution would force the spatial force slice at `T`
to be `C²`, while that slice is exactly `spatialSpike`. -/
theorem zeroOpenPeriodicSolution_isMaximal (T nu : ℝ) (hT : 0 < T) :
    (zeroOpenPeriodicSolution T nu hT).IsMaximal := by
  rintro ⟨extension⟩
  let S : ℝ := (T + extension.lifetime) / 2
  have hTS : T < S := by
    dsimp [S]
    linarith [extension.terminal_lt]
  have hSlifetime : S < extension.lifetime := by
    dsimp [S]
    linarith [extension.terminal_lt]
  have hS : 0 < S := hT.trans hTS
  let closed := extension.extendedSolution.toClosedInterior hS hSlifetime
  have hsmooth : ContDiff ℝ 2 (fun x => terminalSpikeForce T x T) :=
    smoothSolutionOn_forceSpatialSmooth closed.toSmoothSolutionOn hT hTS
  apply spatialSpike_not_contDiff_two
  simpa using hsmooth

/-! ## Zero interior critical receivers -/

@[simp]
theorem vorticityField_zero (x : Space) (t : ℝ) :
    vorticityField (0 : VelocityField) x t = 0 := by
  change derivativeCurlLinearMap
      (fderiv ℝ (fun _ : Space => (0 : Space)) x) = 0
  ext i
  fin_cases i <;> simp [derivativeCurlLinearMap_apply, curlFromJacobian,
    jacobianMatrix_apply]

/-- The counterexample has an accumulated Jacobian receiver with envelope, integral budget, and
curl-forcing work all exactly zero on the entire tail `Ico (T/2) T`. -/
def zeroAccumulatedJacobianControl (T nu : ℝ) (hT : 0 < T) (hnu : 0 ≤ nu) :
    OpenAccumulatedJacobianControl T nu (terminalSpikeForce T) 0
      (T / 2) 0 (fun _ => 0) where
  base_pos := by linarith
  base_lt_terminal := by linarith
  viscosity_nonneg := hnu
  envelope_continuous := continuous_const
  jacobian_envelope t ht x hx := by simp
  curlForcing_nonpos t ht := by
    simp [periodicCurlForcingWork]
  accumulated_budget t ht := by simp

/-- **Finite interior critical control does not imply extension for arbitrary fixed force.**

The antecedent is inhabited by `zeroAccumulatedJacobianControl`; the consequent is refuted by the
future-force obstruction.  This is the precise missing hypothesis exposed by the open carrier. -/
theorem finiteInteriorControl_does_not_imply_extension
    (T nu : ℝ) (hT : 0 < T) (hnu : 0 ≤ nu) :
    ¬ (OpenAccumulatedJacobianControl T nu (terminalSpikeForce T) 0
          (T / 2) 0 (fun _ => 0) →
        (zeroOpenPeriodicSolution T nu hT).CanExtendCompatibly) := by
  intro himplies
  exact zeroOpenPeriodicSolution_isMaximal T nu hT
    (himplies (zeroAccumulatedJacobianControl T nu hT hnu))

section Audit

#print axioms spatialSpike_not_continuous
#print axioms zeroOpenPeriodicSolution
#print axioms zeroOpenPeriodicSolution_isMaximal
#print axioms zeroAccumulatedJacobianControl
#print axioms finiteInteriorControl_does_not_imply_extension

end Audit

end Soma.Holonics.Millennium.NavierStokesForceObstruction
