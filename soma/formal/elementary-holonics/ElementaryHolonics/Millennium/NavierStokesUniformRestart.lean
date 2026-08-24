import ElementaryHolonics.Millennium.NavierStokesOpenLifespan

/-!
# Uniform interior restart and open-lifespan gluing

This module isolates the order-theoretic part of finite-time continuation from its analytic input.
At every strict interior time, a `UniformInteriorRestartSupply` returns

* a fresh local periodic solution whose initial velocity is the old velocity trace and whose force
  is the original force shifted to the restart clock.

An explicit and separately named `OpenPeriodicRestartSpliceLaw` is still required to turn that local
patch into an absolute-time solution.  Its splice does **not** assert agreement with the old
solution.  Agreement on the common lifespan is returned separately by
`OpenPeriodicOverlapUniqueness`.  Consequently no premise contains a
`CompatibleOpenPeriodicExtension` or `CanExtendCompatibly` in disguise, and the substantial gluing
premise remains visible.  Selecting an interior `t₀` with `T < t₀ + ρ`, then applying uniqueness,
constructs the addressed extension receipt.

The shifted-force clause is material.  `OpenPeriodicSolutionOn T` alone says nothing about force
regularity after `T`; a uniform restart supply therefore owns the future-force admissibility needed
by a continuation argument.  This file proves only the exact order/composition consequence.
Constructing the supply, the splice law, and overlap uniqueness from a critical vorticity or
high-order bound remains analytic work.
-/

noncomputable section

open Set InnerProductSpace

namespace Soma.Holonics.Millennium.NavierStokesUniformRestart

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan

/-! ## Restarted local data -/

/-- The velocity trace presented as fresh initial data at the restart face. -/
def velocityTrace (velocity : VelocityField) (t₀ : ℝ) : InitialVelocity :=
  fun x => velocity x t₀

/-- An absolute-time field rebased to the local restart clock. -/
def shiftVelocityField (field : VelocityField) (t₀ : ℝ) : VelocityField :=
  fun x τ => field x (t₀ + τ)

/-- A local periodic solution restarted from the old trace at an interior time.

Its force is the shifted original force.  Thus existence of this object for a uniform radius is
where future-force admissibility enters; it is not hidden in the later agreement receipt. -/
structure InteriorPeriodicRestart
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (base : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t₀ radius : ℝ) where
  interior : t₀ ∈ openTimeSlab T
  radius_pos : 0 < radius
  restartVelocity : VelocityField
  restartPressure : PressureField
  restartSolution :
    OpenPeriodicSolutionOn radius nu (velocityTrace velocity t₀)
      (shiftVelocityField force t₀) restartVelocity restartPressure

/-- A splice realization turns one local restarted world-tube into a fresh absolute-time solution.

The after-restart equations retain the addressed local fields and the pressure-gradient gauge.
There is deliberately no old-lifespan agreement field here; that is a consequence of uniqueness,
not part of restart existence. -/
structure RestartSplice
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {t₀ radius : ℝ} (restart : InteriorPeriodicRestart base t₀ radius) where
  continuedVelocity : VelocityField
  continuedPressure : PressureField
  continuedSolution :
    OpenPeriodicSolutionOn (t₀ + radius) nu initial force
      continuedVelocity continuedPressure
  velocityAfter : ∀ x, ∀ τ ∈ openTimeSlab radius,
    continuedVelocity x (t₀ + τ) = restart.restartVelocity x τ
  pressureGradientAfter : ∀ x, ∀ τ ∈ openTimeSlab radius,
    gradient (fun y => continuedPressure y (t₀ + τ)) x =
      gradient (fun y => restart.restartPressure y τ) x

/-- The spliced absolute solution meets the old velocity at the addressed restart face. -/
theorem RestartSplice.velocity_at_restart
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {t₀ radius : ℝ} {restart : InteriorPeriodicRestart base t₀ radius}
    (splice : RestartSplice restart) (x : Space) :
    splice.continuedVelocity x t₀ = velocity x t₀ := by
  have hzero : (0 : ℝ) ∈ openTimeSlab radius :=
    ⟨le_rfl, restart.radius_pos⟩
  exact (by
    simpa using (splice.velocityAfter x 0 hzero).trans
      (restart.restartSolution.initial x))

/-! ## Independent supply and uniqueness interfaces -/

/-- A common positive local-existence radius at every interior face.  Because each local solution
uses `shiftVelocityField force t₀`, this premise owns the necessary availability and admissibility
of the force beyond the old terminal face.  It returns local patches only, not longer absolute-time
solutions. -/
structure UniformInteriorRestartSupply
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (base : OpenPeriodicSolutionOn T nu initial force velocity pressure) where
  radius : ℝ
  radius_pos : 0 < radius
  restart : ∀ t₀ (_ht₀ : t₀ ∈ openTimeSlab T),
    InteriorPeriodicRestart base t₀ radius

/-- The analytic seam law still owed after local restart existence: every addressed local patch can
be spliced into an absolute-time periodic solution.  Its output records the local after-restart
field and pressure-gradient relations but contains no agreement with the base on the old lifespan.

For classical Navier--Stokes this law must ultimately be proved from seam regularity and the PDE;
declaring it separately prevents the order-theoretic theorem below from being mistaken for that
analytic construction. -/
structure OpenPeriodicRestartSpliceLaw
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (base : OpenPeriodicSolutionOn T nu initial force velocity pressure) where
  splice : ∀ {t₀ radius : ℝ} (restart : InteriorPeriodicRestart base t₀ radius),
    RestartSplice restart

/-- Uniqueness on every common positive open lifespan, retaining exact velocity and the physical
pressure-gradient gauge.  This is independent of restart supply and applies to arbitrary pairs of
periodic solutions with the same viscosity, initial data, and force. -/
structure OpenPeriodicOverlapUniqueness
    (nu : ℝ) (initial : InitialVelocity) (force : VelocityField) : Prop where
  agreesBefore :
    ∀ {S R : ℝ} {velocity₁ velocity₂ : VelocityField}
      {pressure₁ pressure₂ : PressureField},
      OpenPeriodicSolutionOn S nu initial force velocity₁ pressure₁ →
      OpenPeriodicSolutionOn R nu initial force velocity₂ pressure₂ →
      ∀ {U : ℝ}, 0 < U → U ≤ S → U ≤ R →
        PeriodicFieldsAgreeBefore U velocity₁ velocity₂ pressure₁ pressure₂

/-! ## The order-theoretic squeeze -/

/-- Every positive open lifespan and positive restart radius contain an interior restart face whose
uniform local interval crosses the old terminal face. -/
theorem exists_interior_restart_crossing
    {T radius : ℝ} (hT : 0 < T) (hradius : 0 < radius) :
    ∃ t₀ ∈ openTimeSlab T, T < t₀ + radius := by
  let gap : ℝ := min T radius / 2
  have hmin_pos : 0 < min T radius := lt_min hT hradius
  have hmin_T : min T radius ≤ T := min_le_left T radius
  have hmin_radius : min T radius ≤ radius := min_le_right T radius
  refine ⟨T - gap, ?_, ?_⟩
  constructor <;> dsimp [openTimeSlab, gap]
  · linarith
  · linarith
  dsimp [gap]
  linarith

/-- **Uniform restart, seam gluing, and overlap uniqueness cross a finite terminal face.**

The returned object is the full addressed `CompatibleOpenPeriodicExtension`: the extending fields
are fresh fields supplied by the selected splice, while agreement with the base velocity and
pressure gradient on all of `Ico 0 T` is derived from the independent uniqueness law. -/
def compatibleOpenPeriodicExtension_of_uniformRestart_splice_overlapUnique
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (supply : UniformInteriorRestartSupply base)
    (spliceLaw : OpenPeriodicRestartSpliceLaw base)
    (unique : OpenPeriodicOverlapUniqueness nu initial force) :
    CompatibleOpenPeriodicExtension base := by
  let t₀ : ℝ := T - min T supply.radius / 2
  have hmin_pos : 0 < min T supply.radius :=
    lt_min base.terminal_pos supply.radius_pos
  have hmin_T : min T supply.radius ≤ T := min_le_left T supply.radius
  have hmin_radius : min T supply.radius ≤ supply.radius :=
    min_le_right T supply.radius
  have ht₀ : t₀ ∈ openTimeSlab T := by
    constructor <;> dsimp [openTimeSlab, t₀]
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

/-- The same construction descends to the existential extension receiver. -/
theorem OpenPeriodicSolutionOn.canExtendCompatibly_of_uniformRestart_splice_overlapUnique
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (supply : UniformInteriorRestartSupply base)
    (spliceLaw : OpenPeriodicRestartSpliceLaw base)
    (unique : OpenPeriodicOverlapUniqueness nu initial force) :
    base.CanExtendCompatibly := by
  exact ⟨compatibleOpenPeriodicExtension_of_uniformRestart_splice_overlapUnique
    supply spliceLaw unique⟩

section Audit

#print axioms RestartSplice.velocity_at_restart
#print axioms exists_interior_restart_crossing
#print axioms compatibleOpenPeriodicExtension_of_uniformRestart_splice_overlapUnique
#print axioms OpenPeriodicSolutionOn.canExtendCompatibly_of_uniformRestart_splice_overlapUnique

end Audit

end Soma.Holonics.Millennium.NavierStokesUniformRestart
