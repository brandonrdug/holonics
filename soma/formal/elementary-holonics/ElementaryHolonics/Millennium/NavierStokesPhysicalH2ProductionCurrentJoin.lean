import ElementaryHolonics.Millennium.NavierStokesPhysicalH2VelocityCurrentJoin

/-!
# Pointwise physical H2 production-current identification

**[proved-derived; formal-checked]** The complete physical velocity-triad current is identified
at every strict-interior occurrence with the literal coordinate `H2` nonlinear production
current.  The existing physical/Fourier bridge proved the equality through an arbitrary compact
interior chart; taking the singleton chart at the addressed time removes that apparatus face.

No estimate, absolute-value quotient, time integration, absorption, continuation, or terminal
claim is made here.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2ProductionCurrentJoin

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenH2EnergyH3Dissipation
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalFourierH2ProductionBridge
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurrentTriadJoin
open Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityCurrentJoin

/-- The complete physical vorticity-current chart is exactly the coordinate nonlinear
production current at the same strict-interior time occurrence. -/
theorem completePhysicalH2Current_eq_coordinateH2NonlinearProductionCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    completePhysicalH2Current solution t =
      coordinateH2NonlinearProductionCurrent velocity t.1 := by
  have hcompact :=
    compactCofinalH2CurlCompleteAt_eq_completePhysicalH2Current
      solution t.2.1 le_rfl t.2.2 t.1
  have hcoordinate :=
    compactCofinalH2CurlCompleteAt_eq_coordinateH2NonlinearProductionCurrent
      solution t.2.1 le_rfl t.2.2 t.1
  have htime : t.1 ∈ Icc t.1 t.1 := ⟨le_rfl, le_rfl⟩
  have htimeEq : compactInteriorTime t.2.1 le_rfl t.2.2 t.1 = t := by
    apply Subtype.ext
    exact compactInteriorTime_eq t.2.1 le_rfl t.2.2 htime
  rw [htimeEq] at hcompact hcoordinate
  exact hcompact.symm.trans hcoordinate

/-- The velocity-multiplier chart lands in the same literal coordinate production receiver. -/
theorem completePhysicalH2VelocityCurrent_eq_coordinateH2NonlinearProductionCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    completePhysicalH2VelocityCurrent solution t =
      coordinateH2NonlinearProductionCurrent velocity t.1 := by
  rw [← completePhysicalH2Current_eq_velocityCurrent]
  exact completePhysicalH2Current_eq_coordinateH2NonlinearProductionCurrent solution t

section Audit

#print axioms completePhysicalH2Current_eq_coordinateH2NonlinearProductionCurrent
#print axioms completePhysicalH2VelocityCurrent_eq_coordinateH2NonlinearProductionCurrent

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2ProductionCurrentJoin
