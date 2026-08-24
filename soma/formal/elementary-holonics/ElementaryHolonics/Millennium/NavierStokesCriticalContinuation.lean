import ElementaryHolonics.Millennium.NavierStokesLogarithmicGronwall
import ElementaryHolonics.Millennium.NavierStokesUniformRestart

/-!
# Critical-rate continuation factorization

This owner composes two already separate passages without supplying either one's missing analytic
input.

First, a positive high-order receiver `H` on the half-open tail `Ico a T` obeys the logarithmic
differential law

`H' <= K H log H`.

A finite upper budget for the actual accumulated rate `integral_a^t K` then returns the explicit
uniform bound

`H(t) <= exp (log (H(a)) * exp M)`

for every `t < T`.  Second, an independently stated local-existence interface turns that uniform
bound into local restarted solutions with one common positive radius.  The explicit splice law and
overlap uniqueness from `NavierStokesUniformRestart` then cross the terminal face.

The local-existence, splice, and uniqueness interfaces contain no extension receipt.  Conversely,
the logarithmic law does not assert that a Navier--Stokes solution supplies `H`, `H'`, or `K`.
Consequently the final theorem is a conditional factorization, not a proof of the
Beale--Kato--Majda criterion or of Navier--Stokes regularity.  Those analytic attachments remain
visible premises.
-/

noncomputable section

open Real Set
open scoped Interval

namespace Soma.Holonics.Millennium.NavierStokesCriticalContinuation

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesUniformRestart

/-! ## The half-open logarithmic law and its accumulated-rate receiver -/

/-- A logarithmic high-order differential law on the complete tail `Ico a T`.

The coefficient is required to be continuous only on the half-open tail where it is read.  Each
compact consequence uses the frozen-endpoint interval extension from the scalar logarithmic
Grönwall owner, so no terminal value or exterior continuation is invented.  No field-to-`H` or
vorticity-to-`K` attachment is included. -/
structure LifespanLogarithmicHighOrderLaw
    (T a : ℝ) (H H' K : ℝ → ℝ) : Prop where
  base_pos : 0 < a
  base_lt_terminal : a < T
  receiver_derivative : ∀ t ∈ Ico a T, HasDerivAt H (H' t) t
  receiver_one : ∀ t ∈ Ico a T, 1 ≤ H t
  criticalRate_continuousOn : ContinuousOn K (Ico a T)
  differential_law : ∀ t ∈ Ico a T,
    H' t ≤ K t * H t * Real.log (H t)

/-- A finite upper receiver for the accumulated critical rate on every strict tail interval.

The bound `M : ℝ` is supplied separately from the differential law so the two analytic
obligations cannot be conflated. -/
structure OpenAccumulatedCriticalRateBudget
    (T a M : ℝ) (K : ℝ → ℝ) : Prop where
  accumulated_le : ∀ t ∈ Ico a T, (∫ s in a..t, K s) ≤ M

/-- One constant bounds the high-order receiver at every point of the half-open tail. -/
def UniformOpenHighOrderBound
    (T a : ℝ) (H : ℝ → ℝ) (bound : ℝ) : Prop :=
  ∀ t ∈ Ico a T, H t ≤ bound

/-- The logarithmic differential law and accumulated-rate budget return the explicit uniform
double-exponential bound on the complete open tail. -/
theorem LifespanLogarithmicHighOrderLaw.uniformOpenHighOrderBound
    {T a M : ℝ} {H H' K : ℝ → ℝ}
    (law : LifespanLogarithmicHighOrderLaw T a H H' K)
    (budget : OpenAccumulatedCriticalRateBudget T a M K) :
    UniformOpenHighOrderBound T a H
      (Real.exp (Real.log (H a) * Real.exp M)) := by
  intro t ht
  apply le_exp_log_mul_exp_of_integral_budget_of_continuousOn
    (H := H) (H' := H') (K := K) ht.1
  · intro s hs
    exact law.receiver_derivative s
      ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  · intro s hs
    exact law.receiver_one s ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  · exact law.criticalRate_continuousOn.mono (by
      intro s hs
      exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩)
  · intro s hs
    exact law.differential_law s
      ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  · intro s hs
    exact budget.accumulated_le s
      ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  · exact ⟨ht.1, le_rfl⟩

/-! ## A tail-aware local restart supply -/

/-- A common positive local-existence radius at every restart face in `Ico a T`.

Only local restarted patches are returned.  In particular, this structure owns neither an
absolute-time splice nor agreement with the old solution, so it is not an extension hypothesis in
disguise. -/
structure TailUniformInteriorRestartSupply
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (base : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (a : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  restart : ∀ t₀ (_ht₀ : t₀ ∈ Ico a T),
    InteriorPeriodicRestart base t₀ radius

/-- The independent local-existence attachment still owed analytically: any uniform bound for the
chosen high-order receiver supplies a common-radius family of local restarted solutions on the
controlled tail.

Its codomain is `TailUniformInteriorRestartSupply`, not a longer solution.  Dependence of the
radius on the bound remains available inside the returned supply. -/
structure RestartSupplyFromUniformHighOrderBound
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (base : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (a : ℝ) (H : ℝ → ℝ) where
  supply : ∀ {bound : ℝ},
    UniformOpenHighOrderBound T a H bound →
      TailUniformInteriorRestartSupply base a

/-- The complete return of the factorization: the analytically derived uniform receiver and the
addressed compatible extension that it supplies through the restart interface. -/
structure LogarithmicHighOrderContinuationReceipt
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (base : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (a : ℝ) (H : ℝ → ℝ) (bound : ℝ) where
  uniformHighOrderBound : UniformOpenHighOrderBound T a H bound
  extension : CompatibleOpenPeriodicExtension base

/-! ## Tail selection, splice, and continuation -/

/-- A positive controlled tail and a positive restart radius contain an addressed restart face
whose local interval crosses the old terminal face. -/
theorem exists_tail_restart_crossing
    {T a radius : ℝ} (haT : a < T) (hradius : 0 < radius) :
    ∃ t₀ ∈ Ico a T, T < t₀ + radius := by
  let gap : ℝ := min (T - a) radius / 2
  have hspan_pos : 0 < T - a := sub_pos.mpr haT
  have hmin_pos : 0 < min (T - a) radius := lt_min hspan_pos hradius
  have hmin_span : min (T - a) radius ≤ T - a :=
    min_le_left (T - a) radius
  have hmin_radius : min (T - a) radius ≤ radius :=
    min_le_right (T - a) radius
  refine ⟨T - gap, ?_, ?_⟩
  · constructor <;> dsimp [gap]
    · linarith
    · linarith
  · dsimp [gap]
    linarith

/-- Tail-uniform local restart, the explicit seam law, and overlap uniqueness return a fresh
compatible extension past `T`.

This is the order/composition half of continuation.  It consumes only local patches from the tail
supply; agreement on `Ico 0 T` is derived from the separately quantified uniqueness law. -/
def compatibleOpenPeriodicExtension_of_tailRestart_splice_overlapUnique
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (haT : a < T)
    (supply : TailUniformInteriorRestartSupply base a)
    (spliceLaw : OpenPeriodicRestartSpliceLaw base)
    (unique : OpenPeriodicOverlapUniqueness nu initial force) :
    CompatibleOpenPeriodicExtension base := by
  let t₀ : ℝ := T - min (T - a) supply.radius / 2
  have hspan_pos : 0 < T - a := sub_pos.mpr haT
  have hmin_pos : 0 < min (T - a) supply.radius :=
    lt_min hspan_pos supply.radius_pos
  have hmin_span : min (T - a) supply.radius ≤ T - a :=
    min_le_left (T - a) supply.radius
  have hmin_radius : min (T - a) supply.radius ≤ supply.radius :=
    min_le_right (T - a) supply.radius
  have ht₀ : t₀ ∈ Ico a T := by
    constructor <;> dsimp [t₀]
    · linarith
    · linarith
  have hcross : T < t₀ + supply.radius := by
    dsimp [t₀]
    linarith
  let restart := supply.restart t₀ ht₀
  let fresh := spliceLaw.splice restart
  refine
    { lifetime := t₀ + supply.radius
      terminal_lt := hcross
      extendedVelocity := fresh.continuedVelocity
      extendedPressure := fresh.continuedPressure
      extendedSolution := fresh.continuedSolution
      agreesBefore := ?_ }
  exact unique.agreesBefore base fresh.continuedSolution base.terminal_pos
    le_rfl hcross.le

/-- **Exact conditional continuation factorization.**

The first projection is the bound actually derived from `law` and `budget`.  That proof is passed
to `restartFromBound`, whose output consists only of local restarted patches.  The second
projection is then constructed from those patches, the explicit splice law, and overlap
uniqueness.  Thus the accumulated critical-rate budget is on the data path to the returned
extension rather than being a decorative hypothesis.

This theorem remains conditional on four visible analytic attachments: the logarithmic
high-order law, local restart supply from its uniform bound, the splice law, and overlap
uniqueness. -/
def logarithmicHighOrderContinuationFactorization
    {T a M nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {H H' K : ℝ → ℝ}
    {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (law : LifespanLogarithmicHighOrderLaw T a H H' K)
    (budget : OpenAccumulatedCriticalRateBudget T a M K)
    (restartFromBound : RestartSupplyFromUniformHighOrderBound base a H)
    (spliceLaw : OpenPeriodicRestartSpliceLaw base)
    (unique : OpenPeriodicOverlapUniqueness nu initial force) :
    LogarithmicHighOrderContinuationReceipt base a H
      (Real.exp (Real.log (H a) * Real.exp M)) := by
  let uniformBound := law.uniformOpenHighOrderBound budget
  let tailSupply := restartFromBound.supply uniformBound
  exact
    { uniformHighOrderBound := uniformBound
      extension :=
        compatibleOpenPeriodicExtension_of_tailRestart_splice_overlapUnique
          law.base_lt_terminal tailSupply spliceLaw unique }

/-- The continuation projection of the exact factorization.  It is intentionally named after its
conditional logarithmic high-order premises rather than after a solved Navier--Stokes or BKM
theorem. -/
def compatibleOpenPeriodicExtension_of_logarithmicHighOrderFactorization
    {T a M nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {H H' K : ℝ → ℝ}
    {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (law : LifespanLogarithmicHighOrderLaw T a H H' K)
    (budget : OpenAccumulatedCriticalRateBudget T a M K)
    (restartFromBound : RestartSupplyFromUniformHighOrderBound base a H)
    (spliceLaw : OpenPeriodicRestartSpliceLaw base)
    (unique : OpenPeriodicOverlapUniqueness nu initial force) :
    CompatibleOpenPeriodicExtension base :=
  (logarithmicHighOrderContinuationFactorization law budget
    restartFromBound spliceLaw unique).extension

section Audit

#print axioms LifespanLogarithmicHighOrderLaw.uniformOpenHighOrderBound
#print axioms exists_tail_restart_crossing
#print axioms compatibleOpenPeriodicExtension_of_tailRestart_splice_overlapUnique
#print axioms logarithmicHighOrderContinuationFactorization
#print axioms compatibleOpenPeriodicExtension_of_logarithmicHighOrderFactorization

end Audit

end Soma.Holonics.Millennium.NavierStokesCriticalContinuation
