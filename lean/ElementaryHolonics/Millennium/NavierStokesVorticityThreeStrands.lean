import ElementaryHolonics.Millennium.NavierStokesFiniteTimeContinuation

/-!
# The three strands of periodic vorticity transport

The vorticity equation has three intrinsic spatial strands: advection transports vorticity,
viscosity diffuses it, and the velocity Jacobian stretches it.  This module composes the existing
finite-slab vorticity and enstrophy owners into one exact periodic balance.  The transport strand
returns zero over a period, the diffusion strand returns minus viscosity times the nonnegative
vorticity-dissipation population, and in the unforced equation vortex stretching is therefore the
only term which can oppose viscous decay.

No estimate of the stretching term is asserted here.  Controlling that surviving receiver by a
critical vorticity norm is the remaining analytic continuation problem.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Real Set
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesVorticityThreeStrands

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesVorticity

/-! ## Addressed scalar receivers for the three strands -/

/-- The periodic receiver for Eulerian vorticity time work. -/
def periodicVorticityTimeWork (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∫ x in unitCube,
    inner ℝ (eulerianTimeJet (vorticityField velocity) x t)
      (vorticityField velocity x t)

/-- The periodic receiver for advection of vorticity by the velocity field. -/
def periodicVorticityTransportStrand (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∫ x in unitCube,
    inner ℝ
      (fderiv ℝ (fun y => vorticityField velocity y t) x (velocity x t))
      (vorticityField velocity x t)

/-- The signed periodic receiver for viscous diffusion of vorticity. -/
def periodicVorticityDiffusionStrand
    (nu : ℝ) (velocity : VelocityField) (t : ℝ) : ℝ :=
  nu * ∫ x in unitCube,
    inner ℝ (Δ (fun y => vorticityField velocity y t) x)
      (vorticityField velocity x t)

/-! ## Exact return of transport and diffusion -/

/-- Periodic incompressible advection returns no net enstrophy work. -/
theorem periodicSolutionOn_transportStrand_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    periodicVorticityTransportStrand velocity t = 0 := by
  exact periodicSolutionOn_integral_vorticityTransport_eq_zero solution ht0 htT

/-- Periodic integration by parts turns the signed diffusion strand into minus viscosity times
the component-gradient-square dissipation population. -/
theorem periodicSolutionOn_diffusionStrand_eq_neg_dissipation
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    periodicVorticityDiffusionStrand nu velocity t =
      -nu * periodicVorticityDissipation velocity t := by
  unfold periodicVorticityDiffusionStrand
  rw [periodicSolutionOn_integral_vorticityLaplacian_eq_neg_dissipation
    solution ht0 htT]
  ring

/-- For nonnegative viscosity, the returned diffusion strand is nonpositive. -/
theorem periodicSolutionOn_diffusionStrand_nonpos
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (hnu : 0 ≤ nu) :
    periodicVorticityDiffusionStrand nu velocity t ≤ 0 := by
  rw [periodicSolutionOn_diffusionStrand_eq_neg_dissipation solution ht0 htT]
  simpa [neg_mul] using neg_nonpos.mpr (mul_nonneg hnu
    (periodicVorticityDissipation_nonneg velocity t
      (periodicSolutionOn_vorticityDissipation_integrable solution ht0 htT)))

/-! ## The composed three-strand balance -/

/-- The exact periodic vorticity-energy balance.  Curl-forcing is retained as an exterior input;
the three intrinsic spatial strands are transport, stretching, and viscous diffusion. -/
theorem periodicSolutionOn_threeStrand_balance
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    periodicVorticityTimeWork velocity t +
        periodicVorticityTransportStrand velocity t =
      periodicVortexStretching velocity t +
        periodicVorticityDiffusionStrand nu velocity t +
          periodicCurlForcingWork force velocity t := by
  have htime := periodicSolutionOn_integral_vorticityTimeWork_eq_enstrophyRate
    solution ht0 htT
  have htransport := periodicSolutionOn_transportStrand_eq_zero solution ht0 htT
  have hdiffusion := periodicSolutionOn_diffusionStrand_eq_neg_dissipation
    solution ht0 htT
  unfold periodicVorticityTimeWork at htime
  unfold periodicEnstrophyRate at htime
  unfold periodicVorticityTimeWork
  rw [htransport, hdiffusion]
  linarith

/-- Pinching the periodic return removes transport and exposes diffusion and stretching, while
retaining curl-forcing as a distinct exterior port. -/
theorem periodicSolutionOn_pinched_balance
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    periodicVorticityTimeWork velocity t =
      periodicVortexStretching velocity t -
        nu * periodicVorticityDissipation velocity t +
          periodicCurlForcingWork force velocity t := by
  have hbalance := periodicSolutionOn_threeStrand_balance solution ht0 htT
  rw [periodicSolutionOn_transportStrand_eq_zero solution ht0 htT,
    periodicSolutionOn_diffusionStrand_eq_neg_dissipation solution ht0 htT]
    at hbalance
  linarith

/-! ## The genuinely unforced obstruction -/

@[simp]
theorem vorticityField_zero (x : Space) (t : ℝ) :
    vorticityField (0 : VelocityField) x t = 0 := by
  change derivativeCurlLinearMap
      (fderiv ℝ (fun _ : Space => (0 : Space)) x) = 0
  ext i
  fin_cases i <;> simp [derivativeCurlLinearMap_apply, curlFromJacobian,
    jacobianMatrix_apply]

@[simp]
theorem periodicCurlForcingWork_zero
    (velocity : VelocityField) (t : ℝ) :
    periodicCurlForcingWork (0 : VelocityField) velocity t = 0 := by
  simp [periodicCurlForcingWork]

/-- In the unforced equation, the pinched balance contains exactly stretching opposed by viscous
dissipation. -/
theorem periodicSolutionOn_unforced_pinched_balance
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    periodicVorticityTimeWork velocity t =
      periodicVortexStretching velocity t -
        nu * periodicVorticityDissipation velocity t := by
  simpa using periodicSolutionOn_pinched_balance solution ht0 htT

/-- The actual enstrophy derivative of an unforced finite-slab solution is stretching minus
viscous dissipation. -/
theorem periodicSolutionOn_unforced_deriv_enstrophy_eq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    deriv (periodicEnstrophy velocity) t =
      periodicVortexStretching velocity t -
        nu * periodicVorticityDissipation velocity t := by
  have hderiv := periodicSolutionOn_hasDerivAt_periodicEnstrophy_fromMomentum
    solution ht0 htT
  rw [hderiv.deriv]
  unfold periodicEnstrophyRate
  simp
  ring

/-- **Stretching is the exact unforced sign obstruction.**  For nonnegative viscosity,
enstrophy is instantaneously nonincreasing exactly when viscosity times the dissipation population
absorbs the surviving vortex-stretching receiver. -/
theorem periodicSolutionOn_unforced_deriv_enstrophy_nonpos_iff_stretching_absorbed
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (_hnu : 0 ≤ nu) :
    deriv (periodicEnstrophy velocity) t ≤ 0 ↔
      periodicVortexStretching velocity t ≤
        nu * periodicVorticityDissipation velocity t := by
  rw [periodicSolutionOn_unforced_deriv_enstrophy_eq solution ht0 htT]
  constructor <;> intro h <;> linarith

section Audit

#print axioms periodicSolutionOn_threeStrand_balance
#print axioms periodicSolutionOn_transportStrand_eq_zero
#print axioms periodicSolutionOn_diffusionStrand_eq_neg_dissipation
#print axioms periodicSolutionOn_unforced_deriv_enstrophy_nonpos_iff_stretching_absorbed

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityThreeStrands
