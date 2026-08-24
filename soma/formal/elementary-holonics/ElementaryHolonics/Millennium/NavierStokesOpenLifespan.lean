import ElementaryHolonics.Millennium.NavierStokesFiniteTimeVorticity

/-!
# Open-lifespan periodic Navier--Stokes carriers

The closed carrier `PeriodicSolutionOn T` is useful for estimates on a compact slab, but it is not
an honest maximal-lifespan carrier: it already assumes smoothness at the terminal face `T`.  This
module installs the half-open population `Ico 0 T`.  Its terminal face is absent, while every
strictly interior compact slab still restricts to the existing closed carrier.

Compatible extension is receiver-indexed by the complete old velocity field and by the pressure
gradient (hence modulo the physical pressure gauge) on the whole prior lifespan.  The extending
fields are separately quantified and may differ after `T`.  Extension receipts compose by exact
restriction and transitivity; no same-field continuation is smuggled into the definition.

This is a carrier and gluing law.  It does not supply the local-existence theorem which would
construct a compatible extension from a terminal norm bound.
-/

noncomputable section

open ContDiff Set InnerProductSpace
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesOpenLifespan

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity

/-! ## The half-open lifespan -/

/-- The actual finite lifespan: the initial face is present and the terminal face is absent. -/
def openTimeSlab (T : ℝ) : Set ℝ := Ico 0 T

/-- The spatial carrier over an open lifespan. -/
def openSpaceTimeSlab (T : ℝ) : Set (Space × ℝ) := Set.univ ×ˢ openTimeSlab T

/-- A shorter open lifespan is an exact subpopulation of a longer one. -/
theorem openTimeSlab_mono {S T : ℝ} (hST : S ≤ T) :
    openTimeSlab S ⊆ openTimeSlab T := by
  intro t ht
  exact ⟨ht.1, lt_of_lt_of_le ht.2 hST⟩

/-- Spatial extension preserves inclusion of open lifespans. -/
theorem openSpaceTimeSlab_mono {S T : ℝ} (hST : S ≤ T) :
    openSpaceTimeSlab S ⊆ openSpaceTimeSlab T := by
  rintro ⟨x, t⟩ hxt
  exact ⟨Set.mem_univ x, openTimeSlab_mono hST hxt.2⟩

/-- A smooth solution on the genuine lifespan `Ico 0 T`.

The time derivative is taken within that population.  There is deliberately no value, PDE, or
smoothness assertion at `T`. -/
structure OpenSmoothSolutionOn
    (T nu : ℝ) (initial : InitialVelocity) (force : VelocityField)
    (velocity : VelocityField) (pressure : PressureField) : Prop where
  terminal_pos : 0 < T
  momentum : ∀ x, ∀ t ∈ openTimeSlab T,
    derivWithin (velocity x) (openTimeSlab T) t +
        fderiv ℝ (fun y => velocity y t) x (velocity x t) =
      nu • Δ (fun y => velocity y t) x -
        gradient (fun y => pressure y t) x + force x t
  incompressible : ∀ x, ∀ t ∈ openTimeSlab T,
    divergence (fun y => velocity y t) x = 0
  initial : ∀ x, velocity x 0 = initial x
  velocitySmooth :
    ContDiffOn ℝ ∞ (Function.uncurry velocity) (openSpaceTimeSlab T)
  pressureSmooth :
    ContDiffOn ℝ ∞ (Function.uncurry pressure) (openSpaceTimeSlab T)

/-- The periodic open-lifespan carrier. -/
structure OpenPeriodicSolutionOn
    (T nu : ℝ) (initial : InitialVelocity) (force : VelocityField)
    (velocity : VelocityField) (pressure : PressureField) : Prop
    extends OpenSmoothSolutionOn T nu initial force velocity pressure where
  velocityPeriodic : ∀ t ∈ openTimeSlab T, IsOnePeriodic (fun x => velocity x t)
  pressurePeriodic : ∀ t ∈ openTimeSlab T, IsOnePeriodic (fun x => pressure x t)

/-- A fixed spatial receiver sees a differentiable time section on the open lifespan. -/
theorem openSmoothSolutionOn_velocity_time_differentiableWithinAt
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (x : Space) {t : ℝ} (ht : t ∈ openTimeSlab T) :
    DifferentiableWithinAt ℝ (velocity x) (openTimeSlab T) t := by
  have hsection : ContDiffOn ℝ ∞ (velocity x) (openTimeSlab T) :=
    solution.velocitySmooth.comp (contDiff_prodMk_right x).contDiffOn (by
      intro tau htau
      exact ⟨Set.mem_univ x, htau⟩)
  exact hsection.differentiableOn (by simp) t ht

/-! ## Restriction and compact interior recovery -/

/-- Restriction along `Ico 0 S ⊆ Ico 0 T` preserves the complete open smooth carrier. -/
def OpenSmoothSolutionOn.restrict
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    {S : ℝ} (hS : 0 < S) (hST : S ≤ T) :
    OpenSmoothSolutionOn S nu initial force velocity pressure where
  terminal_pos := hS
  momentum x t ht := by
    have hsubset := openTimeSlab_mono hST
    have hdiff := openSmoothSolutionOn_velocity_time_differentiableWithinAt
      solution x (hsubset ht)
    rw [derivWithin_subset hsubset
      ((uniqueDiffOn_Ico 0 S).uniqueDiffWithinAt ht) hdiff]
    exact solution.momentum x t (hsubset ht)
  incompressible x t ht := solution.incompressible x t (openTimeSlab_mono hST ht)
  initial := solution.initial
  velocitySmooth := solution.velocitySmooth.mono (openSpaceTimeSlab_mono hST)
  pressureSmooth := solution.pressureSmooth.mono (openSpaceTimeSlab_mono hST)

/-- Restriction preserves periodicity as well as the PDE carrier. -/
def OpenPeriodicSolutionOn.restrict
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {S : ℝ} (hS : 0 < S) (hST : S ≤ T) :
    OpenPeriodicSolutionOn S nu initial force velocity pressure where
  toOpenSmoothSolutionOn := solution.toOpenSmoothSolutionOn.restrict hS hST
  velocityPeriodic t ht := solution.velocityPeriodic t (openTimeSlab_mono hST ht)
  pressurePeriodic t ht := solution.pressurePeriodic t (openTimeSlab_mono hST ht)

/-- Open-lifespan restriction composes exactly (the carrier is proof-irrelevant, while its fields
and addressed lifespan remain fixed). -/
theorem OpenPeriodicSolutionOn.restrict_trans
    {R S T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (hR : 0 < R) (hS : 0 < S) (hRS : R ≤ S) (hST : S ≤ T) :
    (solution.restrict hS hST).restrict hR hRS =
      solution.restrict hR (hRS.trans hST) := by
  apply Subsingleton.elim

/-- A closed finite carrier forgets its asserted terminal face to become an open-lifespan
carrier.  This is a one-way weakening; maximal-lifespan reasoning uses the open owner directly. -/
def PeriodicSolutionOn.toOpenPeriodicSolutionOn
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure) :
    OpenPeriodicSolutionOn T nu initial force velocity pressure where
  toOpenSmoothSolutionOn := {
    terminal_pos := solution.terminal_pos
    momentum := fun x t ht => by
      have hsubset : openTimeSlab T ⊆ timeSlab T := fun _ h => ⟨h.1, h.2.le⟩
      have hdiff := smoothSolutionOn_velocity_time_differentiableWithinAt
        solution.toSmoothSolutionOn x (hsubset ht)
      rw [derivWithin_subset hsubset
        ((uniqueDiffOn_Ico 0 T).uniqueDiffWithinAt ht) hdiff]
      exact solution.momentum x t (hsubset ht)
    incompressible := fun x t ht => solution.incompressible x t ⟨ht.1, ht.2.le⟩
    initial := solution.initial
    velocitySmooth := solution.velocitySmooth.mono (by
      rintro ⟨x, t⟩ hxt
      exact ⟨Set.mem_univ x, hxt.2.1, hxt.2.2.le⟩)
    pressureSmooth := solution.pressureSmooth.mono (by
      rintro ⟨x, t⟩ hxt
      exact ⟨Set.mem_univ x, hxt.2.1, hxt.2.2.le⟩) }
  velocityPeriodic t ht := solution.velocityPeriodic t ⟨ht.1, ht.2.le⟩
  pressurePeriodic t ht := solution.pressurePeriodic t ⟨ht.1, ht.2.le⟩

/-- Every compact slab strictly inside an open lifespan recovers the existing closed periodic
carrier.  Thus all closed-slab energy and vorticity estimates can be applied without asserting a
smooth terminal face at the actual lifespan `T`. -/
def OpenPeriodicSolutionOn.toClosedInterior
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {S : ℝ} (hS : 0 < S) (hST : S < T) :
    PeriodicSolutionOn S nu initial force velocity pressure where
  toSmoothSolutionOn := {
    terminal_pos := hS
    momentum := fun x t ht => by
      have hsubset : timeSlab S ⊆ openTimeSlab T := by
        intro tau htau
        exact ⟨htau.1, lt_of_le_of_lt htau.2 hST⟩
      have hdiff := openSmoothSolutionOn_velocity_time_differentiableWithinAt
        solution.toOpenSmoothSolutionOn x (hsubset ht)
      rw [derivWithin_subset hsubset
        ((uniqueDiffOn_Icc hS).uniqueDiffWithinAt ht) hdiff]
      exact solution.momentum x t (hsubset ht)
    incompressible := fun x t ht => by
      exact solution.incompressible x t ⟨ht.1, lt_of_le_of_lt ht.2 hST⟩
    initial := solution.initial
    velocitySmooth := solution.velocitySmooth.mono (by
      rintro ⟨x, t⟩ hxt
      exact ⟨Set.mem_univ x, hxt.2.1, lt_of_le_of_lt hxt.2.2 hST⟩)
    pressureSmooth := solution.pressureSmooth.mono (by
      rintro ⟨x, t⟩ hxt
      exact ⟨Set.mem_univ x, hxt.2.1, lt_of_le_of_lt hxt.2.2 hST⟩) }
  velocityPeriodic t ht :=
    solution.velocityPeriodic t ⟨ht.1, lt_of_le_of_lt ht.2 hST⟩
  pressurePeriodic t ht :=
    solution.pressurePeriodic t ⟨ht.1, lt_of_le_of_lt ht.2 hST⟩

/-- A global periodic solution restricts directly to every open finite lifespan. -/
def PeriodicSolution.toOpenPeriodicSolutionOn
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    {T : ℝ} (hT : 0 < T) :
    OpenPeriodicSolutionOn T nu initial force velocity pressure where
  toOpenSmoothSolutionOn := {
    terminal_pos := hT
    momentum := fun x t ht => by
      have hsubset : openTimeSlab T ⊆ Ici (0 : ℝ) := fun _ h => h.1
      have hdiff := smoothSolution_velocity_time_differentiableWithinAt
        solution.toSmoothSolution x (hsubset ht)
      rw [derivWithin_subset hsubset
        ((uniqueDiffOn_Ico 0 T).uniqueDiffWithinAt ht) hdiff]
      exact solution.momentum x t (hsubset ht)
    incompressible := fun x t ht => solution.incompressible x t ht.1
    initial := solution.initial
    velocitySmooth := solution.velocitySmooth.mono (by
      rintro ⟨x, t⟩ hxt
      exact ⟨Set.mem_univ x, hxt.2.1⟩)
    pressureSmooth := solution.pressureSmooth.mono (by
      rintro ⟨x, t⟩ hxt
      exact ⟨Set.mem_univ x, hxt.2.1⟩) }
  velocityPeriodic t ht := solution.velocityPeriodic t ht.1
  pressurePeriodic t ht := solution.pressurePeriodic t ht.1

/-! ## Gauge-compatible prior-lifespan agreement -/

/-- Two periodic fields represent the same prior-lifespan occurrence when velocity agrees exactly
and the pressure gradients agree.  The latter is the Navier--Stokes pressure gauge quotient. -/
structure PeriodicFieldsAgreeBefore
    (T : ℝ) (velocity₁ velocity₂ : VelocityField)
    (pressure₁ pressure₂ : PressureField) : Prop where
  velocity : ∀ x, ∀ t ∈ openTimeSlab T, velocity₁ x t = velocity₂ x t
  pressureGradient : ∀ x, ∀ t ∈ openTimeSlab T,
    gradient (fun y => pressure₁ y t) x = gradient (fun y => pressure₂ y t) x

/-- Prior-lifespan agreement is reflexive. -/
theorem PeriodicFieldsAgreeBefore.refl
    (T : ℝ) (velocity : VelocityField) (pressure : PressureField) :
    PeriodicFieldsAgreeBefore T velocity velocity pressure pressure := by
  exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- Prior-lifespan agreement is symmetric. -/
theorem PeriodicFieldsAgreeBefore.symm
    {T : ℝ} {velocity₁ velocity₂ : VelocityField}
    {pressure₁ pressure₂ : PressureField}
    (h : PeriodicFieldsAgreeBefore T velocity₁ velocity₂ pressure₁ pressure₂) :
    PeriodicFieldsAgreeBefore T velocity₂ velocity₁ pressure₂ pressure₁ := by
  exact ⟨fun x t ht => (h.velocity x t ht).symm,
    fun x t ht => (h.pressureGradient x t ht).symm⟩

/-- Prior-lifespan agreement is transitive. -/
theorem PeriodicFieldsAgreeBefore.trans
    {T : ℝ} {velocity₁ velocity₂ velocity₃ : VelocityField}
    {pressure₁ pressure₂ pressure₃ : PressureField}
    (h₁₂ : PeriodicFieldsAgreeBefore T velocity₁ velocity₂ pressure₁ pressure₂)
    (h₂₃ : PeriodicFieldsAgreeBefore T velocity₂ velocity₃ pressure₂ pressure₃) :
    PeriodicFieldsAgreeBefore T velocity₁ velocity₃ pressure₁ pressure₃ := by
  exact ⟨fun x t ht => (h₁₂.velocity x t ht).trans (h₂₃.velocity x t ht),
    fun x t ht =>
      (h₁₂.pressureGradient x t ht).trans (h₂₃.pressureGradient x t ht)⟩

/-- Agreement on a longer prior lifespan restricts to every shorter one. -/
theorem PeriodicFieldsAgreeBefore.mono
    {S T : ℝ} {velocity₁ velocity₂ : VelocityField}
    {pressure₁ pressure₂ : PressureField} (hST : S ≤ T)
    (h : PeriodicFieldsAgreeBefore T velocity₁ velocity₂ pressure₁ pressure₂) :
    PeriodicFieldsAgreeBefore S velocity₁ velocity₂ pressure₁ pressure₂ := by
  exact ⟨fun x t ht => h.velocity x t (openTimeSlab_mono hST ht),
    fun x t ht => h.pressureGradient x t (openTimeSlab_mono hST ht)⟩

/-! ## Compatible extension and serial gluing -/

/-- An addressed extension receipt.  The longer solution owns separately quantified fields, while
`agreesBefore` proves that its restriction is the old occurrence modulo pressure gauge. -/
structure CompatibleOpenPeriodicExtension
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (_base : OpenPeriodicSolutionOn T nu initial force velocity pressure) where
  lifetime : ℝ
  terminal_lt : T < lifetime
  extendedVelocity : VelocityField
  extendedPressure : PressureField
  extendedSolution :
    OpenPeriodicSolutionOn lifetime nu initial force extendedVelocity extendedPressure
  agreesBefore : PeriodicFieldsAgreeBefore T velocity extendedVelocity pressure extendedPressure

/-- A longer solution with the same fields is the degenerate extension receipt. -/
def OpenPeriodicSolutionOn.restrictionExtension
    {S T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (longer : OpenPeriodicSolutionOn S nu initial force velocity pressure)
    (hT : 0 < T) (hTS : T < S) :
    CompatibleOpenPeriodicExtension (longer.restrict hT hTS.le) where
  lifetime := S
  terminal_lt := hTS
  extendedVelocity := velocity
  extendedPressure := pressure
  extendedSolution := longer
  agreesBefore := PeriodicFieldsAgreeBefore.refl T velocity pressure

/-- **Compatible restarted extensions glue serially.**  The second extension may use fields
different from the first after its terminal face.  Restriction of its agreement to the original
lifespan and transitivity return one extension receipt from the original occurrence. -/
def CompatibleOpenPeriodicExtension.comp
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (first : CompatibleOpenPeriodicExtension base)
    (second : CompatibleOpenPeriodicExtension first.extendedSolution) :
    CompatibleOpenPeriodicExtension base where
  lifetime := second.lifetime
  terminal_lt := first.terminal_lt.trans second.terminal_lt
  extendedVelocity := second.extendedVelocity
  extendedPressure := second.extendedPressure
  extendedSolution := second.extendedSolution
  agreesBefore := first.agreesBefore.trans
    (second.agreesBefore.mono first.terminal_lt.le)

/-- Existence of a gauge-compatible extension with separately quantified later fields. -/
def OpenPeriodicSolutionOn.CanExtendCompatibly
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) : Prop :=
  Nonempty (CompatibleOpenPeriodicExtension solution)

/-- Maximality is the absence of any compatible longer open-lifespan occurrence, not the absence
of a same-field proof on an already closed terminal slab. -/
def OpenPeriodicSolutionOn.IsMaximal
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) : Prop :=
  ¬ solution.CanExtendCompatibly

/-- Serial composition descends from addressed receipts to the extension-existence receiver. -/
theorem CompatibleOpenPeriodicExtension.canExtendCompatibly_comp
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (first : CompatibleOpenPeriodicExtension base)
    (second : CompatibleOpenPeriodicExtension first.extendedSolution) :
    base.CanExtendCompatibly := by
  exact ⟨first.comp second⟩

/-- A strict restriction of a longer open solution is compatibly extendible. -/
theorem OpenPeriodicSolutionOn.restriction_canExtendCompatibly
    {S T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (longer : OpenPeriodicSolutionOn S nu initial force velocity pressure)
    (hT : 0 < T) (hTS : T < S) :
    (longer.restrict hT hTS.le).CanExtendCompatibly := by
  exact ⟨longer.restrictionExtension hT hTS⟩

section Audit

#print axioms OpenPeriodicSolutionOn.restrict
#print axioms OpenPeriodicSolutionOn.restrict_trans
#print axioms PeriodicSolutionOn.toOpenPeriodicSolutionOn
#print axioms OpenPeriodicSolutionOn.toClosedInterior
#print axioms PeriodicSolution.toOpenPeriodicSolutionOn
#print axioms CompatibleOpenPeriodicExtension.comp
#print axioms OpenPeriodicSolutionOn.restriction_canExtendCompatibly

end Audit

end Soma.Holonics.Millennium.NavierStokesOpenLifespan
