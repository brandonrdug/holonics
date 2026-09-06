import ElementaryHolonics.Millennium.NavierStokesLambCurrentEvolution
import ElementaryHolonics.Millennium.NavierStokesCellLinearReceiver

/-!
# The nonlinear cross-current returns a cell storage/current/source balance

The actual time derivative passes through the compact spatial integral. The boundary is the
existing six-face receiver, and its cancellation is available only under actual periodicity.
-/
noncomputable section
open ContDiff InnerProductSpace Set MeasureTheory Filter Topology
open scoped BigOperators Laplacian

namespace Soma.Holonics.Millennium.NavierStokesLambCurrentCell
open Soma.Holonics.Millennium
open NavierStokes NavierStokesVorticity NavierStokesPeriodicEnergy
open NavierStokesPeriodicEnstrophy NavierStokesPeriodicFlux NavierStokesFiniteTime
open NavierStokesFiniteTimeVorticity NavierStokesOpenLifespan
open NavierStokesLambCurrentEvolution NavierStokesCellCurrentLaw NavierStokesCellLinearReceiver

private theorem current_divergence_continuous (F : InitialVelocity) (hF : ContDiff ℝ 1 F) :
    Continuous (divergence F) := by
  have hsum : Continuous (fun x : Space => ∑ i : Fin 3,
      (fderiv ℝ F x (EuclideanSpace.basisFun (Fin 3) ℝ i)) i) := by
    apply continuous_finset_sum
    intro i hi
    have hd := (hF.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk (continuous_const : Continuous fun _ : Space =>
        EuclideanSpace.basisFun (Fin 3) ℝ i))
    exact (EuclideanSpace.proj i).continuous.comp hd
  apply hsum.congr
  intro x
  have h := sum_coordinate_fderiv_eq_divergence F x
  simp only [ContinuousLinearMap.comp_apply,equiv_symm_single_eq_basisFun] at h
  convert h using 1 <;> rfl

/-- The actual component stored in the declared spatial cell. -/
def cellCurrent (velocity : VelocityField) (i : Fin 3) (t : ℝ) : ℝ :=
  ∫ x in unitCube, velocityVorticityCurrentField velocity x t i

/-- The source rate is the full interior current less its outward six-face flux. -/
theorem smoothSolutionOn_cellCurrent_hasDerivAt
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (i : Fin 3) :
    HasDerivAt (cellCurrent velocity i)
      ((∫ x in unitCube, velocityVorticitySource nu force velocity pressure x t i) -
        faceBalance (currentComponentFlux nu velocity t i)) t := by
  have hu := smoothSolutionOn_velocitySpatialSmooth solution ht0 htT
  have hflux := currentComponentFlux_contDiff_one nu velocity t i
    (hu.of_le (WithTop.coe_le_coe.mpr le_top))
  have hcurrent := smoothSolutionOn_current_contDiffOn solution
  have htime := eulerianTimeJet_continuous_of_contDiffOn_openSlab
    (velocityVorticityCurrentField velocity) hcurrent ht0 htT
  have hcube : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  have hiTime : IntegrableOn
      (fun x => eulerianTimeJet (velocityVorticityCurrentField velocity) x t i) unitCube :=
    ((EuclideanSpace.proj i).continuous.comp htime).continuousOn.integrableOn_compact hcube
  have hiDiv : IntegrableOn (divergence (currentComponentFlux nu velocity t i)) unitCube :=
    (current_divergence_continuous _ hflux).continuousOn.integrableOn_compact hcube
  have hbalance :
      (∫ x in unitCube, eulerianTimeJet (velocityVorticityCurrentField velocity) x t i) +
        faceBalance (currentComponentFlux nu velocity t i) =
      ∫ x in unitCube, velocityVorticitySource nu force velocity pressure x t i := by
    rw [← integral_divergence_unitCube_eq_faceBalance _ hflux,
      ← integral_add hiTime hiDiv]
    apply setIntegral_congr_fun hcube.measurableSet
    intro x hx
    exact smoothSolutionOn_current_component_balance solution ht0 htT x i
  have hderiv := hasDerivAt_cellComponentIntegral_of_contDiffOn_openSlab
    (velocityVorticityCurrentField velocity) hcurrent i ht0 htT
  rw [eq_sub_of_add_eq hbalance] at hderiv
  exact hderiv

/-- Storage change plus outward current is exactly the interior production receiver. -/
theorem smoothSolutionOn_cellCurrent_balance
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (i : Fin 3) :
    deriv (cellCurrent velocity i) t + faceBalance (currentComponentFlux nu velocity t i) =
      ∫ x in unitCube, velocityVorticitySource nu force velocity pressure x t i := by
  rw [(smoothSolutionOn_cellCurrent_hasDerivAt solution ht0 htT i).deriv]
  ring

/-- The open lifespan is retained; only a strictly smaller compact slab is used for the proof. -/
theorem openPeriodicSolutionOn_cellCurrent_balance
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (i : Fin 3) :
    deriv (cellCurrent velocity i) t + faceBalance (currentComponentFlux nu velocity t i) =
      ∫ x in unitCube, velocityVorticitySource nu force velocity pressure x t i := by
  let S := (t+T)/2
  have hS : 0 < S := by dsimp [S];linarith
  have htS : t < S := by dsimp [S];linarith
  have hST : S < T := by dsimp [S];linarith
  exact smoothSolutionOn_cellCurrent_balance
    (solution.toClosedInterior hS hST).toSmoothSolutionOn ht0 htS i

#print axioms smoothSolutionOn_cellCurrent_hasDerivAt
#print axioms openPeriodicSolutionOn_cellCurrent_balance
end Soma.Holonics.Millennium.NavierStokesLambCurrentCell
