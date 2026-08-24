import ElementaryHolonics.Millennium.NavierStokesOverlapUniqueness

/-!
# Interior restart seams for open periodic Navier--Stokes solutions

This file isolates the analytic seam between an open solution and a locally restarted patch.
Time translation first presents the old solution on the restart clock.  Nonnegative-viscosity
overlap uniqueness then identifies the two velocity fields and their pressure gradients on every
strict common local lifespan.  Exact piecewise gluing is kept separate from that agreement.
-/

noncomputable section

open ContDiff Filter InnerProductSpace Set Topology
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesRestartSeam

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesUniformRestart
open Soma.Holonics.Millennium.NavierStokesOverlapUniqueness

/-- An absolute-time pressure field rebased to the local restart clock. -/
def shiftPressureField (field : PressureField) (t₀ : ℝ) : PressureField :=
  fun x τ => field x (t₀ + τ)

/-- The joint space-time embedding associated to the restart clock. -/
def restartClockEmbedding (t₀ : ℝ) : Space × ℝ → Space × ℝ :=
  fun z => (z.1, t₀ + z.2)

theorem restartClockEmbedding_contDiff (t₀ : ℝ) :
    ContDiff ℝ ∞ (restartClockEmbedding t₀) := by
  exact contDiff_fst.prodMk (contDiff_const.add contDiff_snd)

/-- A local restart-clock time belongs to the old open lifespan after translation. -/
theorem add_mem_openTimeSlab_of_mem_remaining
    {T t₀ τ : ℝ} (ht₀ : t₀ ∈ openTimeSlab T)
    (hτ : τ ∈ openTimeSlab (T - t₀)) :
    t₀ + τ ∈ openTimeSlab T := by
  constructor <;> dsimp [openTimeSlab] at ht₀ hτ ⊢
  · linarith [ht₀.1, hτ.1]
  · linarith [hτ.2]

/-- Translation by an interior time preserves the within-time derivative after the domains are
translated from `Ico 0 (T - t₀)` into `Ico 0 T`. -/
theorem derivWithin_shiftVelocityField_eq
    {T nu t₀ : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (ht₀ : t₀ ∈ openTimeSlab T) (x : Space) {τ : ℝ}
    (hτ : τ ∈ openTimeSlab (T - t₀)) :
    derivWithin (shiftVelocityField velocity t₀ x) (openTimeSlab (T - t₀)) τ =
      derivWithin (velocity x) (openTimeSlab T) (t₀ + τ) := by
  have hshifted := add_mem_openTimeSlab_of_mem_remaining ht₀ hτ
  have houterDiff := openSmoothSolutionOn_velocity_time_differentiableWithinAt
    solution.toOpenSmoothSolutionOn x hshifted
  have houter : HasDerivWithinAt (velocity x)
      (derivWithin (velocity x) (openTimeSlab T) (t₀ + τ))
      (openTimeSlab T) (t₀ + τ) :=
    houterDiff.hasDerivWithinAt
  have hinner : HasDerivWithinAt (fun s : ℝ => t₀ + s) 1
      (openTimeSlab (T - t₀)) τ :=
    ((hasDerivAt_id τ).const_add t₀).hasDerivWithinAt
  have hmaps : MapsTo (fun s : ℝ => t₀ + s)
      (openTimeSlab (T - t₀)) (openTimeSlab T) :=
    fun _ hs => add_mem_openTimeSlab_of_mem_remaining ht₀ hs
  have hcomp := houter.scomp τ hinner hmaps
  have htranslated : HasDerivWithinAt (shiftVelocityField velocity t₀ x)
      (derivWithin (velocity x) (openTimeSlab T) (t₀ + τ))
      (openTimeSlab (T - t₀)) τ := by
    simpa [shiftVelocityField, Function.comp_def] using hcomp
  exact htranslated.derivWithin
    ((uniqueDiffOn_Ico 0 (T - t₀)).uniqueDiffWithinAt hτ)

/-- The old solution, viewed from an interior restart face, is itself an open periodic solution
for exactly the remaining lifespan.  This construction uses only restriction and time translation;
it assumes neither a longer solution nor any splice. -/
def OpenPeriodicSolutionOn.shiftFromInterior
    {T nu t₀ : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (ht₀ : t₀ ∈ openTimeSlab T) :
    OpenPeriodicSolutionOn (T - t₀) nu (velocityTrace velocity t₀)
      (shiftVelocityField force t₀) (shiftVelocityField velocity t₀)
      (shiftPressureField pressure t₀) where
  toOpenSmoothSolutionOn := {
    terminal_pos := sub_pos.mpr ht₀.2
    momentum := fun x τ hτ => by
      have hshifted := add_mem_openTimeSlab_of_mem_remaining ht₀ hτ
      rw [derivWithin_shiftVelocityField_eq solution ht₀ x hτ]
      simpa [shiftVelocityField, shiftPressureField] using
        solution.momentum x (t₀ + τ) hshifted
    incompressible := fun x τ hτ => by
      simpa [shiftVelocityField] using solution.incompressible x (t₀ + τ)
        (add_mem_openTimeSlab_of_mem_remaining ht₀ hτ)
    initial := fun x => by simp [shiftVelocityField, velocityTrace]
    velocitySmooth := by
      have hmaps : MapsTo (restartClockEmbedding t₀)
          (openSpaceTimeSlab (T - t₀)) (openSpaceTimeSlab T) := by
        rintro ⟨x, τ⟩ hxτ
        exact ⟨Set.mem_univ x,
          add_mem_openTimeSlab_of_mem_remaining ht₀ hxτ.2⟩
      have hcomp := solution.velocitySmooth.comp
        (restartClockEmbedding_contDiff t₀).contDiffOn hmaps
      simpa [shiftVelocityField, restartClockEmbedding, Function.comp_def,
        Function.uncurry] using hcomp
    pressureSmooth := by
      have hmaps : MapsTo (restartClockEmbedding t₀)
          (openSpaceTimeSlab (T - t₀)) (openSpaceTimeSlab T) := by
        rintro ⟨x, τ⟩ hxτ
        exact ⟨Set.mem_univ x,
          add_mem_openTimeSlab_of_mem_remaining ht₀ hxτ.2⟩
      have hcomp := solution.pressureSmooth.comp
        (restartClockEmbedding_contDiff t₀).contDiffOn hmaps
      simpa [shiftPressureField, restartClockEmbedding, Function.comp_def,
        Function.uncurry] using hcomp }
  velocityPeriodic := fun τ hτ => by
    simpa [shiftVelocityField] using solution.velocityPeriodic (t₀ + τ)
      (add_mem_openTimeSlab_of_mem_remaining ht₀ hτ)
  pressurePeriodic := fun τ hτ => by
    simpa [shiftPressureField] using solution.pressurePeriodic (t₀ + τ)
      (add_mem_openTimeSlab_of_mem_remaining ht₀ hτ)

/-! ## The overlap returned by uniqueness -/

/-- The complete common lifespan of the shifted old solution and the restarted patch. -/
def restartCommonLifespan
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (_restart : InteriorPeriodicRestart base t₀ radius) : ℝ :=
  min (T - t₀) radius

theorem InteriorPeriodicRestart.restartCommonLifespan_pos
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) :
    0 < restartCommonLifespan restart := by
  exact lt_min (sub_pos.mpr restart.interior.2) restart.radius_pos

/-- Universal nonnegative-viscosity uniqueness identifies the local patch with the old solution
translated to the restart clock throughout their full common open lifespan. -/
theorem InteriorPeriodicRestart.agreesWithShiftedBase
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) (hnu : 0 ≤ nu) :
    PeriodicFieldsAgreeBefore (restartCommonLifespan restart)
      (shiftVelocityField velocity t₀) restart.restartVelocity
      (shiftPressureField pressure t₀) restart.restartPressure := by
  let shiftedBase := OpenPeriodicSolutionOn.shiftFromInterior base restart.interior
  exact (openPeriodicOverlapUniqueness_of_nonnegativeViscosity hnu).agreesBefore
    shiftedBase restart.restartSolution
      (InteriorPeriodicRestart.restartCommonLifespan_pos restart)
      (min_le_left (T - t₀) radius) (min_le_right (T - t₀) radius)

/-! ## Gauge normalization and the candidate piecewise fields -/

/-- Normalize a pressure field at the spatial origin.  This changes no spatial gradient and
chooses a concrete representative of the pressure gauge at each time. -/
def anchoredPressure (field : PressureField) : PressureField :=
  fun x t => field x t - field 0 t

/-- Equal gradients of two smooth scalar fields imply equality after anchoring at the origin. -/
theorem anchored_eq_of_gradient_eq
    (p q : Space → ℝ) (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q)
    (hgradient : ∀ x, gradient p x = gradient q x) :
    ∀ x, p x - p 0 = q x - q 0 := by
  let difference : Space → ℝ := fun x => p x - q x
  have hpDiff : Differentiable ℝ p := hp.differentiable (by norm_num)
  have hqDiff : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hdifference : Differentiable ℝ difference := hpDiff.sub hqDiff
  have hderivative : ∀ x, fderiv ℝ difference x = 0 := by
    intro x
    have hfrechet : fderiv ℝ p x = fderiv ℝ q x := by
      exact (toDual ℝ Space).symm.injective (hgradient x)
    have hsub := fderiv_sub (hpDiff x) (hqDiff x)
    rw [hfrechet, sub_self] at hsub
    simpa only [Pi.sub_apply] using hsub
  intro x
  have hconstant := is_const_of_fderiv_eq_zero hdifference hderivative x 0
  dsimp [difference] at hconstant
  linarith

/-- The pressure gauges of the shifted old solution and the restarted patch coincide pointwise on
their common lifespan after normalization at the spatial origin. -/
theorem InteriorPeriodicRestart.anchoredPressure_eq_shiftedBase
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) (hnu : 0 ≤ nu)
    {τ : ℝ} (hτ : τ ∈ openTimeSlab (restartCommonLifespan restart)) :
    ∀ x,
      anchoredPressure (shiftPressureField pressure t₀) x τ =
        anchoredPressure restart.restartPressure x τ := by
  let shiftedBase := OpenPeriodicSolutionOn.shiftFromInterior base restart.interior
  have hremaining : τ ∈ openTimeSlab (T - t₀) :=
    openTimeSlab_mono (min_le_left (T - t₀) radius) hτ
  have hradius : τ ∈ openTimeSlab radius :=
    openTimeSlab_mono (min_le_right (T - t₀) radius) hτ
  have hp := OpenPeriodicSolutionOn.pressureSpatialSmooth shiftedBase hremaining
  have hq := OpenPeriodicSolutionOn.pressureSpatialSmooth restart.restartSolution hradius
  have hgradient := (InteriorPeriodicRestart.agreesWithShiftedBase restart hnu).pressureGradient
  intro x
  exact anchored_eq_of_gradient_eq
    (fun y => shiftPressureField pressure t₀ y τ)
    (fun y => restart.restartPressure y τ) hp hq
    (fun y => hgradient y τ hτ) x

/-- The exact velocity obtained by using the base before the addressed face and the local restart
at and after it. -/
def restartSpliceVelocity
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) : VelocityField :=
  fun x t => if t < t₀ then velocity x t else restart.restartVelocity x (t - t₀)

/-- The corresponding piecewise pressure uses the anchored gauge on both sides of the seam. -/
def restartSplicePressure
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) : PressureField :=
  fun x t => if t < t₀ then anchoredPressure pressure x t
    else anchoredPressure restart.restartPressure x (t - t₀)

/-- Anchoring changes no pressure gradient wherever the spatial pressure section is
differentiable. -/
theorem gradient_anchoredPressure_eq
    (field : PressureField) (x : Space) (t : ℝ)
    (hfield : DifferentiableAt ℝ (fun y => field y t) x) :
    gradient (fun y => anchoredPressure field y t) x =
      gradient (fun y => field y t) x := by
  have hsub := fderiv_sub hfield (differentiableAt_const (c := field 0 t))
  have hfrechet :
      fderiv ℝ (fun y => field y t - field 0 t) x =
        fderiv ℝ (fun y => field y t) x := by
    have hconst : fderiv ℝ (fun _ : Space => field 0 t) x = 0 :=
      fderiv_const_apply (x := x) (field 0 t)
    rw [hconst, sub_zero] at hsub
    have hfunctions :
        (fun y : Space => field y t) - (fun _ : Space => field 0 t) =
          (fun y => field y t - field 0 t) := by
      funext y
      rfl
    rw [hfunctions] at hsub
    exact hsub
  unfold gradient anchoredPressure
  rw [hfrechet]

/-- The candidate splice is literally the restarted velocity after the addressed face. -/
theorem restartSpliceVelocity_after
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) (x : Space) {τ : ℝ}
    (hτ : τ ∈ openTimeSlab radius) :
    restartSpliceVelocity restart x (t₀ + τ) = restart.restartVelocity x τ := by
  have hnot : ¬t₀ + τ < t₀ := by linarith [hτ.1]
  simp [restartSpliceVelocity, hnot]

/-- The candidate splice has exactly the restarted pressure gradient after the addressed face. -/
theorem restartSplicePressure_gradient_after
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) (x : Space) {τ : ℝ}
    (hτ : τ ∈ openTimeSlab radius) :
    gradient (fun y => restartSplicePressure restart y (t₀ + τ)) x =
      gradient (fun y => restart.restartPressure y τ) x := by
  have hnot : ¬t₀ + τ < t₀ := by linarith [hτ.1]
  have hp := OpenPeriodicSolutionOn.pressureSpatialSmooth restart.restartSolution hτ
  simpa only [restartSplicePressure, if_neg hnot, add_sub_cancel_left] using
    gradient_anchoredPressure_eq restart.restartPressure x τ
      (hp.differentiable (by norm_num) x)

/-- On the old side together with the entire uniqueness overlap, the candidate velocity is exactly
the old velocity.  This equality on a genuine neighbourhood of the seam carries all velocity jets. -/
theorem restartSpliceVelocity_eq_base_on_common
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) (hnu : 0 ≤ nu)
    {t : ℝ} (ht : t ∈ openTimeSlab (t₀ + restartCommonLifespan restart)) :
    ∀ x, restartSpliceVelocity restart x t = velocity x t := by
  intro x
  by_cases hbefore : t < t₀
  · simp [restartSpliceVelocity, hbefore]
  · have hτ : t - t₀ ∈ openTimeSlab (restartCommonLifespan restart) := by
      constructor <;> dsimp [openTimeSlab] at ht ⊢
      · linarith
      · linarith [ht.2]
    have hagree := (InteriorPeriodicRestart.agreesWithShiftedBase restart hnu).velocity
      x (t - t₀) hτ
    rw [restartSpliceVelocity, if_neg hbefore]
    simpa [shiftVelocityField] using hagree.symm

/-- After anchoring, the pressure candidate likewise equals the base representative throughout a
full absolute-time neighbourhood of the seam. -/
theorem restartSplicePressure_eq_base_on_common
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) (hnu : 0 ≤ nu)
    {t : ℝ} (ht : t ∈ openTimeSlab (t₀ + restartCommonLifespan restart)) :
    ∀ x, restartSplicePressure restart x t = anchoredPressure pressure x t := by
  intro x
  by_cases hbefore : t < t₀
  · simp [restartSplicePressure, hbefore]
  · have hτ : t - t₀ ∈ openTimeSlab (restartCommonLifespan restart) := by
      constructor <;> dsimp [openTimeSlab] at ht ⊢
      · linarith
      · linarith [ht.2]
    have hagree := InteriorPeriodicRestart.anchoredPressure_eq_shiftedBase restart hnu hτ x
    rw [restartSplicePressure, if_neg hbefore]
    simpa [shiftPressureField, anchoredPressure] using hagree.symm

/-! ## Smooth pasting across the addressed face -/

/-- The absolute-time carrier of the restarted branch. -/
def absoluteRestartSpaceTimeSlab (t₀ radius : ℝ) : Set (Space × ℝ) :=
  Set.univ ×ˢ Ico t₀ (t₀ + radius)

/-- The time projection of the absolute restarted branch. -/
def absoluteRestartTimeSlab (t₀ radius : ℝ) : Set ℝ :=
  Ico t₀ (t₀ + radius)

/-- The inverse clock embedding used to present a local patch in absolute time. -/
def inverseRestartClockEmbedding (t₀ : ℝ) : Space × ℝ → Space × ℝ :=
  fun z => (z.1, z.2 - t₀)

theorem inverseRestartClockEmbedding_contDiff (t₀ : ℝ) :
    ContDiff ℝ ∞ (inverseRestartClockEmbedding t₀) := by
  exact contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)

/-- Translating the local patch back to absolute time preserves its within-time derivative. -/
theorem derivWithin_absoluteRestart_eq
    {radius nu t₀ : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn radius nu initial force velocity pressure)
    (x : Space) {t : ℝ} (ht : t ∈ absoluteRestartTimeSlab t₀ radius) :
    derivWithin (fun s => velocity x (s - t₀))
        (absoluteRestartTimeSlab t₀ radius) t =
      derivWithin (velocity x) (openTimeSlab radius) (t - t₀) := by
  have hlocal : t - t₀ ∈ openTimeSlab radius := by
    constructor <;> dsimp [absoluteRestartTimeSlab, openTimeSlab] at ht ⊢
    · linarith [ht.1]
    · linarith [ht.2]
  have houterDiff := openSmoothSolutionOn_velocity_time_differentiableWithinAt
    solution.toOpenSmoothSolutionOn x hlocal
  have houter : HasDerivWithinAt (velocity x)
      (derivWithin (velocity x) (openTimeSlab radius) (t - t₀))
      (openTimeSlab radius) (t - t₀) := houterDiff.hasDerivWithinAt
  have hinner : HasDerivWithinAt (fun s : ℝ => s - t₀) 1
      (absoluteRestartTimeSlab t₀ radius) t :=
    ((hasDerivAt_id t).sub_const t₀).hasDerivWithinAt
  have hmaps : MapsTo (fun s : ℝ => s - t₀)
      (absoluteRestartTimeSlab t₀ radius) (openTimeSlab radius) := by
    intro s hs
    constructor <;> dsimp [absoluteRestartTimeSlab, openTimeSlab] at hs ⊢
    · linarith [hs.1]
    · linarith [hs.2]
  have hcomp := houter.scomp t hinner hmaps
  have habsolute : HasDerivWithinAt (fun s => velocity x (s - t₀))
      (derivWithin (velocity x) (openTimeSlab radius) (t - t₀))
      (absoluteRestartTimeSlab t₀ radius) t := by
    simpa [Function.comp_def] using hcomp
  exact habsolute.derivWithin
    ((uniqueDiffOn_Ico t₀ (t₀ + radius)).uniqueDiffWithinAt ht)

/-- Pressure anchoring preserves joint smoothness on any open solution carrier. -/
theorem OpenPeriodicSolutionOn.anchoredPressureSmooth
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    ContDiffOn ℝ ∞ (Function.uncurry (anchoredPressure pressure))
      (openSpaceTimeSlab T) := by
  have hreference : ContDiffOn ℝ ∞ (fun z : Space × ℝ => pressure 0 z.2)
      (openSpaceTimeSlab T) := by
    have hmaps : MapsTo (fun z : Space × ℝ => (0, z.2))
        (openSpaceTimeSlab T) (openSpaceTimeSlab T) := by
      intro z hz
      exact ⟨Set.mem_univ 0, hz.2⟩
    simpa [Function.comp_def, Function.uncurry] using
      solution.pressureSmooth.comp
        (contDiffOn_const.prodMk contDiffOn_snd) hmaps
  simpa [anchoredPressure, Function.uncurry] using
    solution.pressureSmooth.sub hreference

/-- The restarted velocity branch is jointly smooth on its absolute-time carrier. -/
theorem InteriorPeriodicRestart.absoluteVelocitySmooth
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) :
    ContDiffOn ℝ ∞
      (fun z : Space × ℝ => restart.restartVelocity z.1 (z.2 - t₀))
      (absoluteRestartSpaceTimeSlab t₀ radius) := by
  have hmaps : MapsTo (inverseRestartClockEmbedding t₀)
      (absoluteRestartSpaceTimeSlab t₀ radius) (openSpaceTimeSlab radius) := by
    rintro ⟨x, t⟩ hxt
    refine ⟨Set.mem_univ x, ?_⟩
    constructor <;>
      dsimp [absoluteRestartSpaceTimeSlab, openTimeSlab,
        inverseRestartClockEmbedding] at hxt ⊢
    · linarith [hxt.2.1]
    · linarith [hxt.2.2]
  simpa [inverseRestartClockEmbedding, Function.comp_def, Function.uncurry] using
    restart.restartSolution.velocitySmooth.comp
      (inverseRestartClockEmbedding_contDiff t₀).contDiffOn hmaps

/-- The anchored restarted pressure branch is jointly smooth on its absolute-time carrier. -/
theorem InteriorPeriodicRestart.absoluteAnchoredPressureSmooth
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) :
    ContDiffOn ℝ ∞
      (fun z : Space × ℝ => anchoredPressure restart.restartPressure z.1 (z.2 - t₀))
      (absoluteRestartSpaceTimeSlab t₀ radius) := by
  have hmaps : MapsTo (inverseRestartClockEmbedding t₀)
      (absoluteRestartSpaceTimeSlab t₀ radius) (openSpaceTimeSlab radius) := by
    rintro ⟨x, t⟩ hxt
    refine ⟨Set.mem_univ x, ?_⟩
    constructor <;>
      dsimp [absoluteRestartSpaceTimeSlab, openTimeSlab,
        inverseRestartClockEmbedding] at hxt ⊢
    · linarith [hxt.2.1]
    · linarith [hxt.2.2]
  have hsmooth := OpenPeriodicSolutionOn.anchoredPressureSmooth restart.restartSolution
  simpa [inverseRestartClockEmbedding, Function.comp_def, Function.uncurry] using
    hsmooth.comp (inverseRestartClockEmbedding_contDiff t₀).contDiffOn hmaps

/-- A shorter half-open space-time slab has the same local germ as a longer one at each of its
points. -/
theorem openSpaceTimeSlab_eventuallyEq_of_mem_of_le
    {A B : ℝ} {z : Space × ℝ} (hz : z ∈ openSpaceTimeSlab A) (hAB : A ≤ B) :
    openSpaceTimeSlab A =ᶠ[𝓝 z] openSpaceTimeSlab B := by
  have hneighborhood : {w : Space × ℝ | w.2 < A} ∈ 𝓝 z :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds hz.2.2
  filter_upwards [hneighborhood] with w hw
  apply propext
  constructor
  · intro hwA
    exact openSpaceTimeSlab_mono hAB hwA
  · intro hwB
    exact ⟨Set.mem_univ w.1, hwB.2.1, hw⟩

/-- The corresponding local-germ statement for the time projection. -/
theorem openTimeSlab_eventuallyEq_of_mem_of_le
    {A B t : ℝ} (ht : t ∈ openTimeSlab A) (hAB : A ≤ B) :
    openTimeSlab A =ᶠ[𝓝 t] openTimeSlab B := by
  have hneighborhood : {s : ℝ | s < A} ∈ 𝓝 t :=
    (isOpen_Iio : IsOpen (Iio A)).mem_nhds ht.2
  filter_upwards [hneighborhood] with s hs
  apply propext
  constructor
  · intro hsA
    exact openTimeSlab_mono hAB hsA
  · intro hsB
    exact ⟨hsB.1, hs⟩

/-- Away from its lower face, the absolute restart carrier has the same local germ as the complete
candidate lifespan. -/
theorem absoluteRestartSpaceTimeSlab_eventuallyEq
    {t₀ radius : ℝ} {z : Space × ℝ} (ht₀ : 0 ≤ t₀) (hzlower : t₀ < z.2) :
    absoluteRestartSpaceTimeSlab t₀ radius =ᶠ[𝓝 z]
      openSpaceTimeSlab (t₀ + radius) := by
  have hneighborhood : {w : Space × ℝ | t₀ < w.2} ∈ 𝓝 z :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hzlower
  filter_upwards [hneighborhood] with w hw
  apply propext
  constructor
  · intro hwRestart
    exact ⟨Set.mem_univ w.1, ht₀.trans hwRestart.2.1, hwRestart.2.2⟩
  · intro hwFull
    exact ⟨Set.mem_univ w.1, hw.le, hwFull.2.2⟩

/-- The corresponding absolute-restart time germ. -/
theorem absoluteRestartTimeSlab_eventuallyEq
    {t₀ radius t : ℝ} (ht₀ : 0 ≤ t₀) (htlower : t₀ < t) :
    absoluteRestartTimeSlab t₀ radius =ᶠ[𝓝 t]
      openTimeSlab (t₀ + radius) := by
  have hneighborhood : {s : ℝ | t₀ < s} ∈ 𝓝 t :=
    (isOpen_Ioi : IsOpen (Ioi t₀)).mem_nhds htlower
  filter_upwards [hneighborhood] with s hs
  apply propext
  constructor
  · intro hsRestart
    exact ⟨ht₀.trans hsRestart.1, hsRestart.2⟩
  · intro hsFull
    exact ⟨hs.le, hsFull.2⟩

/-- The candidate velocity is smooth on the old carrier enlarged through the complete uniqueness
overlap. -/
theorem InteriorPeriodicRestart.spliceVelocitySmoothOnCommon
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) (hnu : 0 ≤ nu) :
    ContDiffOn ℝ ∞ (Function.uncurry (restartSpliceVelocity restart))
      (openSpaceTimeSlab (t₀ + restartCommonLifespan restart)) := by
  have hlifetime : t₀ + restartCommonLifespan restart ≤ T := by
    dsimp [restartCommonLifespan]
    linarith [min_le_left (T - t₀) radius]
  have hbase := base.velocitySmooth.mono (openSpaceTimeSlab_mono hlifetime)
  exact hbase.congr (by
    rintro ⟨x, t⟩ hxt
    exact restartSpliceVelocity_eq_base_on_common restart hnu hxt.2 x)

/-- The anchored pressure candidate is smooth on the same common carrier. -/
theorem InteriorPeriodicRestart.splicePressureSmoothOnCommon
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) (hnu : 0 ≤ nu) :
    ContDiffOn ℝ ∞ (Function.uncurry (restartSplicePressure restart))
      (openSpaceTimeSlab (t₀ + restartCommonLifespan restart)) := by
  have hlifetime : t₀ + restartCommonLifespan restart ≤ T := by
    dsimp [restartCommonLifespan]
    linarith [min_le_left (T - t₀) radius]
  have hbase := (OpenPeriodicSolutionOn.anchoredPressureSmooth base).mono
    (openSpaceTimeSlab_mono hlifetime)
  exact hbase.congr (by
    rintro ⟨x, t⟩ hxt
    exact restartSplicePressure_eq_base_on_common restart hnu hxt.2 x)

/-- The candidate velocity is smooth on the absolute restarted branch. -/
theorem InteriorPeriodicRestart.spliceVelocitySmoothOnAfter
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) :
    ContDiffOn ℝ ∞ (Function.uncurry (restartSpliceVelocity restart))
      (absoluteRestartSpaceTimeSlab t₀ radius) := by
  exact (InteriorPeriodicRestart.absoluteVelocitySmooth restart).congr (by
    rintro ⟨x, t⟩ hxt
    have hnot : ¬t < t₀ := not_lt.mpr hxt.2.1
    simp [restartSpliceVelocity, hnot, Function.uncurry])

/-- The anchored pressure candidate is smooth on the absolute restarted branch. -/
theorem InteriorPeriodicRestart.splicePressureSmoothOnAfter
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) :
    ContDiffOn ℝ ∞ (Function.uncurry (restartSplicePressure restart))
      (absoluteRestartSpaceTimeSlab t₀ radius) := by
  exact (InteriorPeriodicRestart.absoluteAnchoredPressureSmooth restart).congr (by
    rintro ⟨x, t⟩ hxt
    have hnot : ¬t < t₀ := not_lt.mpr hxt.2.1
    simp [restartSplicePressure, hnot, Function.uncurry])

/-- Smoothness pastes across the seam because uniqueness supplies a nonempty common carrier on
which the candidate is literally the old solution. -/
theorem InteriorPeriodicRestart.restartSpliceVelocitySmooth
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) (hnu : 0 ≤ nu) :
    ContDiffOn ℝ ∞ (Function.uncurry (restartSpliceVelocity restart))
      (openSpaceTimeSlab (t₀ + radius)) := by
  intro z hz
  by_cases hcommon : z.2 < t₀ + restartCommonLifespan restart
  · have hzcommon : z ∈ openSpaceTimeSlab
        (t₀ + restartCommonLifespan restart) :=
      ⟨Set.mem_univ z.1, hz.2.1, hcommon⟩
    have hlocal := InteriorPeriodicRestart.spliceVelocitySmoothOnCommon restart hnu
      z hzcommon
    have hlifetime : t₀ + restartCommonLifespan restart ≤ t₀ + radius := by
      dsimp [restartCommonLifespan]
      linarith [min_le_right (T - t₀) radius]
    exact hlocal.congr_set
      (openSpaceTimeSlab_eventuallyEq_of_mem_of_le hzcommon hlifetime)
  · have hcommonPos := InteriorPeriodicRestart.restartCommonLifespan_pos restart
    have hzlower : t₀ < z.2 := by linarith
    have hzafter : z ∈ absoluteRestartSpaceTimeSlab t₀ radius :=
      ⟨Set.mem_univ z.1, hzlower.le, hz.2.2⟩
    have hlocal := InteriorPeriodicRestart.spliceVelocitySmoothOnAfter restart z hzafter
    exact hlocal.congr_set
      (absoluteRestartSpaceTimeSlab_eventuallyEq restart.interior.1 hzlower)

/-- The same local-germ argument pastes the anchored pressure representative. -/
theorem InteriorPeriodicRestart.restartSplicePressureSmooth
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) (hnu : 0 ≤ nu) :
    ContDiffOn ℝ ∞ (Function.uncurry (restartSplicePressure restart))
      (openSpaceTimeSlab (t₀ + radius)) := by
  intro z hz
  by_cases hcommon : z.2 < t₀ + restartCommonLifespan restart
  · have hzcommon : z ∈ openSpaceTimeSlab
        (t₀ + restartCommonLifespan restart) :=
      ⟨Set.mem_univ z.1, hz.2.1, hcommon⟩
    have hlocal := InteriorPeriodicRestart.splicePressureSmoothOnCommon restart hnu
      z hzcommon
    have hlifetime : t₀ + restartCommonLifespan restart ≤ t₀ + radius := by
      dsimp [restartCommonLifespan]
      linarith [min_le_right (T - t₀) radius]
    exact hlocal.congr_set
      (openSpaceTimeSlab_eventuallyEq_of_mem_of_le hzcommon hlifetime)
  · have hcommonPos := InteriorPeriodicRestart.restartCommonLifespan_pos restart
    have hzlower : t₀ < z.2 := by linarith
    have hzafter : z ∈ absoluteRestartSpaceTimeSlab t₀ radius :=
      ⟨Set.mem_univ z.1, hzlower.le, hz.2.2⟩
    have hlocal := InteriorPeriodicRestart.splicePressureSmoothOnAfter restart z hzafter
    exact hlocal.congr_set
      (absoluteRestartSpaceTimeSlab_eventuallyEq restart.interior.1 hzlower)

/-! ## The piecewise Navier--Stokes carrier -/

/-- Anchoring preserves every spatial unit period. -/
theorem anchoredPressure_isOnePeriodic
    {field : PressureField} {t : ℝ}
    (hperiodic : IsOnePeriodic (fun x => field x t)) :
    IsOnePeriodic (fun x => anchoredPressure field x t) := by
  intro x i
  simp only [anchoredPressure]
  have hp : field (x + EuclideanSpace.single i 1) t = field x t := by
    simpa using hperiodic x i
  rw [hp]

/-- The candidate velocity retains the original initial datum, including the allowed case in which
the addressed restart face is itself `t₀ = 0`. -/
theorem InteriorPeriodicRestart.restartSpliceVelocity_initial
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) (x : Space) :
    restartSpliceVelocity restart x 0 = initial x := by
  rcases eq_or_lt_of_le restart.interior.1 with ht₀zero | ht₀positive
  · subst t₀
    simp [restartSpliceVelocity, restart.restartSolution.initial,
      velocityTrace, base.initial]
  · simp [restartSpliceVelocity, ht₀positive, base.initial]

/-- The candidate velocity is divergence-free throughout its complete absolute lifespan. -/
theorem InteriorPeriodicRestart.restartSpliceVelocity_incompressible
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) (x : Space) {t : ℝ}
    (ht : t ∈ openTimeSlab (t₀ + radius)) :
    divergence (fun y => restartSpliceVelocity restart y t) x = 0 := by
  by_cases hbefore : t < t₀
  · have htbase : t ∈ openTimeSlab T :=
      ⟨ht.1, hbefore.trans restart.interior.2⟩
    simpa [restartSpliceVelocity, hbefore] using base.incompressible x t htbase
  · have hlocal : t - t₀ ∈ openTimeSlab radius := by
      constructor <;> dsimp [openTimeSlab] at ht ⊢
      · linarith
      · linarith [ht.2]
    simpa [restartSpliceVelocity, hbefore] using
      restart.restartSolution.incompressible x (t - t₀) hlocal

/-- The candidate velocity retains spatial periodicity throughout its complete lifespan. -/
theorem InteriorPeriodicRestart.restartSpliceVelocity_periodic
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) {t : ℝ}
    (ht : t ∈ openTimeSlab (t₀ + radius)) :
    IsOnePeriodic (fun x => restartSpliceVelocity restart x t) := by
  by_cases hbefore : t < t₀
  · have htbase : t ∈ openTimeSlab T :=
      ⟨ht.1, hbefore.trans restart.interior.2⟩
    simpa [restartSpliceVelocity, hbefore] using base.velocityPeriodic t htbase
  · have hlocal : t - t₀ ∈ openTimeSlab radius := by
      constructor <;> dsimp [openTimeSlab] at ht ⊢
      · linarith
      · linarith [ht.2]
    simpa [restartSpliceVelocity, hbefore] using
      restart.restartSolution.velocityPeriodic (t - t₀) hlocal

/-- The anchored pressure candidate retains spatial periodicity throughout its lifespan. -/
theorem InteriorPeriodicRestart.restartSplicePressure_periodic
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) {t : ℝ}
    (ht : t ∈ openTimeSlab (t₀ + radius)) :
    IsOnePeriodic (fun x => restartSplicePressure restart x t) := by
  by_cases hbefore : t < t₀
  · have htbase : t ∈ openTimeSlab T :=
      ⟨ht.1, hbefore.trans restart.interior.2⟩
    simpa [restartSplicePressure, hbefore] using
      anchoredPressure_isOnePeriodic (base.pressurePeriodic t htbase)
  · have hlocal : t - t₀ ∈ openTimeSlab radius := by
      constructor <;> dsimp [openTimeSlab] at ht ⊢
      · linarith
      · linarith [ht.2]
    simpa [restartSplicePressure, hbefore] using
      anchoredPressure_isOnePeriodic
        (restart.restartSolution.pressurePeriodic (t - t₀) hlocal)

/-- On the common carrier, the time derivative of the candidate is the derivative of the old
velocity on the shortened old clock. -/
theorem InteriorPeriodicRestart.restartSplice_derivWithin_eq_base
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) (hnu : 0 ≤ nu)
    (x : Space) {t : ℝ}
    (ht : t ∈ openTimeSlab (t₀ + restartCommonLifespan restart)) :
    derivWithin (restartSpliceVelocity restart x) (openTimeSlab (t₀ + radius)) t =
      derivWithin (velocity x)
        (openTimeSlab (t₀ + restartCommonLifespan restart)) t := by
  have hlifetime : t₀ + restartCommonLifespan restart ≤ t₀ + radius := by
    dsimp [restartCommonLifespan]
    linarith [min_le_right (T - t₀) radius]
  calc
    derivWithin (restartSpliceVelocity restart x) (openTimeSlab (t₀ + radius)) t =
        derivWithin (restartSpliceVelocity restart x)
          (openTimeSlab (t₀ + restartCommonLifespan restart)) t :=
      derivWithin_congr_set
        (openTimeSlab_eventuallyEq_of_mem_of_le ht hlifetime).symm
    _ = derivWithin (velocity x)
          (openTimeSlab (t₀ + restartCommonLifespan restart)) t :=
      derivWithin_congr
        (fun s hs => restartSpliceVelocity_eq_base_on_common restart hnu hs x)
        (restartSpliceVelocity_eq_base_on_common restart hnu ht x)

/-- Strictly after the seam, the candidate time derivative is the restarted local derivative. -/
theorem InteriorPeriodicRestart.restartSplice_derivWithin_eq_restart
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) (x : Space) {t : ℝ}
    (ht : t ∈ openTimeSlab (t₀ + radius)) (htlower : t₀ < t) :
    derivWithin (restartSpliceVelocity restart x) (openTimeSlab (t₀ + radius)) t =
      derivWithin (restart.restartVelocity x) (openTimeSlab radius) (t - t₀) := by
  have habsolute : t ∈ absoluteRestartTimeSlab t₀ radius := by
    exact ⟨htlower.le, ht.2⟩
  calc
    derivWithin (restartSpliceVelocity restart x) (openTimeSlab (t₀ + radius)) t =
        derivWithin (restartSpliceVelocity restart x)
          (absoluteRestartTimeSlab t₀ radius) t :=
      derivWithin_congr_set
        (absoluteRestartTimeSlab_eventuallyEq restart.interior.1 htlower).symm
    _ = derivWithin (fun s => restart.restartVelocity x (s - t₀))
          (absoluteRestartTimeSlab t₀ radius) t := by
      apply derivWithin_congr
      · intro s hs
        have hnot : ¬s < t₀ := not_lt.mpr hs.1
        simp [restartSpliceVelocity, hnot]
      · have hnot : ¬t < t₀ := not_lt.mpr htlower.le
        simp [restartSpliceVelocity, hnot]
    _ = derivWithin (restart.restartVelocity x) (openTimeSlab radius) (t - t₀) :=
      derivWithin_absoluteRestart_eq restart.restartSolution x habsolute

/-- The candidate satisfies momentum on the old-plus-overlap carrier. -/
theorem InteriorPeriodicRestart.restartSplice_momentum_on_common
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) (hnu : 0 ≤ nu)
    (x : Space) {t : ℝ}
    (ht : t ∈ openTimeSlab (t₀ + restartCommonLifespan restart)) :
    derivWithin (restartSpliceVelocity restart x) (openTimeSlab (t₀ + radius)) t +
        fderiv ℝ (fun y => restartSpliceVelocity restart y t) x
          (restartSpliceVelocity restart x t) =
      nu • Δ (fun y => restartSpliceVelocity restart y t) x -
        gradient (fun y => restartSplicePressure restart y t) x + force x t := by
  have hcommonPos : 0 < t₀ + restartCommonLifespan restart := by
    linarith [restart.interior.1,
      InteriorPeriodicRestart.restartCommonLifespan_pos restart]
  have hlifetime : t₀ + restartCommonLifespan restart ≤ T := by
    dsimp [restartCommonLifespan]
    linarith [min_le_left (T - t₀) radius]
  let old := base.restrict hcommonPos hlifetime
  have hm := old.momentum x t ht
  have htime := InteriorPeriodicRestart.restartSplice_derivWithin_eq_base
    restart hnu x ht
  have hvelocity :
      (fun y => restartSpliceVelocity restart y t) = (fun y => velocity y t) := by
    funext y
    exact restartSpliceVelocity_eq_base_on_common restart hnu ht y
  have hpoint : restartSpliceVelocity restart x t = velocity x t :=
    restartSpliceVelocity_eq_base_on_common restart hnu ht x
  have hpressure :
      (fun y => restartSplicePressure restart y t) =
        (fun y => anchoredPressure pressure y t) := by
    funext y
    exact restartSplicePressure_eq_base_on_common restart hnu ht y
  have htbase : t ∈ openTimeSlab T := openTimeSlab_mono hlifetime ht
  have hp := OpenPeriodicSolutionOn.pressureSpatialSmooth base htbase
  have hgradient := gradient_anchoredPressure_eq pressure x t
    (hp.differentiable (by norm_num) x)
  rw [htime, hvelocity, hpoint, hpressure, hgradient]
  exact hm

/-- Strictly after the seam, the candidate satisfies the translated restarted momentum equation. -/
theorem InteriorPeriodicRestart.restartSplice_momentum_on_after
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) (x : Space) {t : ℝ}
    (ht : t ∈ openTimeSlab (t₀ + radius)) (htlower : t₀ < t) :
    derivWithin (restartSpliceVelocity restart x) (openTimeSlab (t₀ + radius)) t +
        fderiv ℝ (fun y => restartSpliceVelocity restart y t) x
          (restartSpliceVelocity restart x t) =
      nu • Δ (fun y => restartSpliceVelocity restart y t) x -
        gradient (fun y => restartSplicePressure restart y t) x + force x t := by
  have hlocal : t - t₀ ∈ openTimeSlab radius := by
    constructor <;> dsimp [openTimeSlab] at ht ⊢
    · linarith [htlower]
    · linarith [ht.2]
  have hm := restart.restartSolution.momentum x (t - t₀) hlocal
  have htime := InteriorPeriodicRestart.restartSplice_derivWithin_eq_restart
    restart x ht htlower
  have hnot : ¬t < t₀ := not_lt.mpr htlower.le
  have hvelocity :
      (fun y => restartSpliceVelocity restart y t) =
        (fun y => restart.restartVelocity y (t - t₀)) := by
    funext y
    simp [restartSpliceVelocity, hnot]
  have hpoint : restartSpliceVelocity restart x t =
      restart.restartVelocity x (t - t₀) := by
    simp [restartSpliceVelocity, hnot]
  have hpressure :
      (fun y => restartSplicePressure restart y t) =
        (fun y => anchoredPressure restart.restartPressure y (t - t₀)) := by
    funext y
    simp [restartSplicePressure, hnot]
  have hp := OpenPeriodicSolutionOn.pressureSpatialSmooth
    restart.restartSolution hlocal
  have hgradient := gradient_anchoredPressure_eq restart.restartPressure x (t - t₀)
    (hp.differentiable (by norm_num) x)
  rw [htime, hvelocity, hpoint, hpressure, hgradient]
  simpa [shiftVelocityField] using hm

/-- The momentum equation therefore holds throughout the candidate open lifespan, including the
seam itself via the nonempty uniqueness overlap. -/
theorem InteriorPeriodicRestart.restartSplice_momentum
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) (hnu : 0 ≤ nu)
    (x : Space) {t : ℝ} (ht : t ∈ openTimeSlab (t₀ + radius)) :
    derivWithin (restartSpliceVelocity restart x) (openTimeSlab (t₀ + radius)) t +
        fderiv ℝ (fun y => restartSpliceVelocity restart y t) x
          (restartSpliceVelocity restart x t) =
      nu • Δ (fun y => restartSpliceVelocity restart y t) x -
        gradient (fun y => restartSplicePressure restart y t) x + force x t := by
  by_cases hcommon : t < t₀ + restartCommonLifespan restart
  · exact InteriorPeriodicRestart.restartSplice_momentum_on_common restart hnu x
      ⟨ht.1, hcommon⟩
  · have hcommonPos := InteriorPeriodicRestart.restartCommonLifespan_pos restart
    have htlower : t₀ < t := by linarith
    exact InteriorPeriodicRestart.restartSplice_momentum_on_after restart x ht htlower

/-! ## The closed seam owner -/

/-- Every local restart patch at nonnegative viscosity splices into an absolute-time open periodic
solution.  The construction is genuinely piecewise and assumes neither a pre-existing longer
solution nor compatibility with one. -/
def InteriorPeriodicRestart.toRestartSplice
    {T nu t₀ radius : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {base : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (restart : InteriorPeriodicRestart base t₀ radius) (hnu : 0 ≤ nu) :
    RestartSplice restart where
  continuedVelocity := restartSpliceVelocity restart
  continuedPressure := restartSplicePressure restart
  continuedSolution := {
    toOpenSmoothSolutionOn := {
      terminal_pos := by linarith [restart.interior.1, restart.radius_pos]
      momentum := fun x t ht =>
        InteriorPeriodicRestart.restartSplice_momentum restart hnu x ht
      incompressible := fun x t ht =>
        InteriorPeriodicRestart.restartSpliceVelocity_incompressible restart x ht
      initial := InteriorPeriodicRestart.restartSpliceVelocity_initial restart
      velocitySmooth :=
        InteriorPeriodicRestart.restartSpliceVelocitySmooth restart hnu
      pressureSmooth :=
        InteriorPeriodicRestart.restartSplicePressureSmooth restart hnu }
    velocityPeriodic := fun _ ht =>
      InteriorPeriodicRestart.restartSpliceVelocity_periodic restart ht
    pressurePeriodic := fun _ ht =>
      InteriorPeriodicRestart.restartSplicePressure_periodic restart ht }
  velocityAfter := fun x _ hτ => restartSpliceVelocity_after restart x hτ
  pressureGradientAfter := fun x _ hτ =>
    restartSplicePressure_gradient_after restart x hτ

/-- Nonnegative viscosity supplies the analytic seam law required by uniform-restart continuation. -/
def openPeriodicRestartSpliceLaw_of_nonnegativeViscosity
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (base : OpenPeriodicSolutionOn T nu initial force velocity pressure) (hnu : 0 ≤ nu) :
    OpenPeriodicRestartSpliceLaw base where
  splice := fun restart => InteriorPeriodicRestart.toRestartSplice restart hnu

section Audit

#print axioms OpenPeriodicSolutionOn.shiftFromInterior
#print axioms InteriorPeriodicRestart.agreesWithShiftedBase
#print axioms InteriorPeriodicRestart.restartSpliceVelocitySmooth
#print axioms InteriorPeriodicRestart.toRestartSplice
#print axioms openPeriodicRestartSpliceLaw_of_nonnegativeViscosity

end Audit

end Soma.Holonics.Millennium.NavierStokesRestartSeam
