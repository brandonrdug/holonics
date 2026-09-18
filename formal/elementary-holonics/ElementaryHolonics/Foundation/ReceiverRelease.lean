import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import ElementaryHolonics.Foundation.Receiver

/-!
# Receiver width and release

[definition] This owner states the law the Rust module
`crates/holonic-engine/src/receiver_release.rs` implements. It is receiver **R6** of
`docs/plans/THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT.md`.

For a compatible family `F` — the preimage/observation fibre of
`Foundation/ReceiverAtlas.lean::LocalChart.preimageFibre`, carried here as a `Finset` so the
diameter is attained rather than approached — an exact `h`-step map `Φ` and a receiver reading
`R`, the **width** is

```text
w_R(h) = diam { R (Φ h x u) : x compatible, u admitted }
```

and a face is **released** when that width falls inside the receiver's *declared* tolerance.

## What the width is, and what it is not

[definition] The width is a **structural** reading of an uncertainty, not a scalar confidence: it
is the diameter of an actual image set, so a zero width is the exact statement that `R ∘ Φ h` is
constant on the whole fibre (`width_eq_zero_iff`), and a positive width names how far apart the
compatible answers actually are. Nothing here is a probability and nothing here is fitted.

[project-postulate] AGENTS.md: *"A plural fibre does not impose a universal certainty gate on
generation."* `release_is_receiver_relative_not_a_global_gate` is that clause proved: **one** fibre
carries **one** receiver that releases at every tolerance and **another** receiver that releases at
none. There is therefore no fibre-level predicate "certain enough to generate"; release is a
receiver-relative declared law and this file builds no global gate. `ReleaseLaw` carries the
caller's declared decision as a *field*, and `no_default_among_the_lawful_returns` exhibits two
lawful laws that return different arms on the same reading — the library supplies no default.

## The five lawful non-release returns

[definition] `ReleaseReturn` is `released`, `hold`, `widen`, `ask`, `releaseCoarser` and
`noContinuationBridges`. Exactly the three arms that *name a tolerance* are constrained by this
file, and `every_lawful_return_other_than_hold_ask_or_no_continuation_is_inside_its_tolerance`
collects them: `ReleaseLaw.sound` requires that a law returning `released` has the width inside
the declared tolerance; `ReleaseLaw.widenSound` requires that a named wider tolerance really does
contain the width that provoked it; and the `releaseCoarser` constructor *carries*
`coarserWidth ≤ tolerance` as an argument, so a coarser release outside the declaring law's
tolerance cannot be formed. `hold`, `ask` and `noContinuationBridges` emit nothing and are
unconstrained: which of them a caller takes is the caller's declared law, and `ReleaseLaw` is
parametric in it.

## The three laws of the width

[proved-derived; formal-checked]

* `width_mono` — a narrower fibre has no larger width (monotone under fibre inclusion).
* `width_nonExpansive_factor` — a coarser receiver `g ∘ R` with `g` non-expansive has no larger
  width, and `expansive_factor_increases_width` is the counterexample when `g` is expansive: the
  coarser reading is *not* automatically narrower, only the non-expansive one is.
* `width_eq_zero_iff` and `releasable_at_every_tolerance_iff_width_zero` — width zero, constancy of
  `R ∘ Φ h` on the fibre, and releasability at every tolerance are the same statement.

## The event is future-stable while its timing is not

[proved-derived; formal-checked] `future_stable_event_with_unstable_timing` exhibits an exact
system — the rational doubling recurrence `x ↦ 2 x`, which is
`Foundation/CausalChord.lean::Linearization` with `state = !![2]` and no excitation — a compatible
fibre `{1/8, 1/4}` and horizon `3`, at which the receiver "the event occurs by horizon 3" has width
exactly `0` and the receiver "the time of the event" has width exactly `1`. The event is released at
every tolerance; its timing is released at no tolerance below `1`. `timeOfEvent_is_least` and
`timeOfEvent_crosses` earn the name: the returned step really is the first step of the exact
trajectory at which the threshold is reached, and no earlier step reaches it.

Rust owner: `crates/holonic-engine/src/receiver_release.rs`
(`width` ↔ `width_enumerated` and `width_enclosed`;
`width_mono` ↔ `the_width_is_monotone_under_fibre_inclusion`;
`width_nonExpansive_factor` ↔ `a_non_expansive_coarser_receiver_has_no_larger_width`;
`expansive_factor_increases_width` ↔ `an_expansive_factor_map_widens_the_reading`;
`width_eq_zero_iff` ↔ `ReceiverWidth::is_zero` and `width_zero_releases_at_every_tolerance`;
`ReleaseReturn` ↔ `ReleaseReturn`; `ReleaseLaw` ↔ `DecisionLaw`;
`every_lawful_return_other_than_hold_ask_or_no_continuation_is_inside_its_tolerance` ↔
`release` together with `LawfulOptions::assemble`;
`future_stable_event_with_unstable_timing` ↔
`an_event_is_future_stable_while_its_timing_is_not`).
-/

namespace Soma.Holonics.Foundation.ReceiverRelease

/-! ## The width of a receiver reading over a compatible family -/

/-- [definition] **The width of a receiver reading over a compatible family.** `F` is the compatible
family — the preimage fibre, finite here so the diameter is attained — and `R` the reading, taken
into `ℚ` because every reading this project admits is exact. No float participates.

The reading `R` is the composite `receiver ∘ Φ h` of the plan: the caller supplies the `h`-step map
already composed, because the width law below is indifferent to how the composite was built. -/
def width {X : Type*} (F : Finset X) (hF : F.Nonempty) (R : X → ℚ) : ℚ :=
  F.sup' hF R - F.inf' hF R

/-- [proved-derived; formal-checked] Every compatible reading is at least the infimum. -/
theorem inf'_le_of_mem {X : Type*} {F : Finset X} (hF : F.Nonempty) (R : X → ℚ) {x : X}
    (hx : x ∈ F) : F.inf' hF R ≤ R x :=
  Finset.inf'_le R hx

/-- [proved-derived; formal-checked] And at most the supremum. -/
theorem le_sup'_of_mem {X : Type*} {F : Finset X} (hF : F.Nonempty) (R : X → ℚ) {x : X}
    (hx : x ∈ F) : R x ≤ F.sup' hF R :=
  Finset.le_sup' R hx

/-- [proved-derived; formal-checked] A width is never negative. -/
theorem width_nonneg {X : Type*} (F : Finset X) (hF : F.Nonempty) (R : X → ℚ) :
    0 ≤ width F hF R := by
  obtain ⟨a, ha⟩ := id hF
  have hinf : F.inf' hF R ≤ R a := inf'_le_of_mem hF R ha
  have hsup : R a ≤ F.sup' hF R := le_sup'_of_mem hF R ha
  simp only [width, sub_nonneg]
  linarith

/-- [proved-derived; formal-checked] **Any two compatible readings differ by at most the width.**
This is the sense in which the width is a diameter and not a spread statistic. -/
theorem abs_sub_le_width {X : Type*} {F : Finset X} (hF : F.Nonempty) (R : X → ℚ) {x y : X}
    (hx : x ∈ F) (hy : y ∈ F) : |R x - R y| ≤ width F hF R := by
  have hxs := le_sup'_of_mem hF R hx
  have hys := le_sup'_of_mem hF R hy
  have hxi := inf'_le_of_mem hF R hx
  have hyi := inf'_le_of_mem hF R hy
  rw [abs_sub_le_iff]
  simp only [width]
  constructor <;> linarith

/-- [proved-derived; formal-checked] **The width is bounded by any declared band containing every
compatible reading.** This is how an executable enclosure — the exact zonotope hull the Rust owner
carries — pins a width without enumerating the family. -/
theorem width_le_of_bounds {X : Type*} {F : Finset X} (hF : F.Nonempty) (R : X → ℚ) {lo hi : ℚ}
    (hlo : ∀ x ∈ F, lo ≤ R x) (hhi : ∀ x ∈ F, R x ≤ hi) : width F hF R ≤ hi - lo := by
  have h1 : F.sup' hF R ≤ hi := Finset.sup'_le hF R hhi
  have h2 : lo ≤ F.inf' hF R := Finset.le_inf' hF R hlo
  simp only [width]
  linarith

/-- [proved-derived; formal-checked] **The width is monotone under fibre inclusion.** A narrower
compatible family has no larger width: observing more never widens the returned uncertainty. -/
theorem width_mono {X : Type*} {F G : Finset X} (hFG : F ⊆ G) (hF : F.Nonempty)
    (hG : G.Nonempty) (R : X → ℚ) : width F hF R ≤ width G hG R := by
  have hsup : F.sup' hF R ≤ G.sup' hG R :=
    Finset.sup'_le hF R fun b hb => Finset.le_sup' R (hFG hb)
  have hinf : G.inf' hG R ≤ F.inf' hF R :=
    Finset.le_inf' hF R fun b hb => Finset.inf'_le R (hFG hb)
  simp only [width]
  linarith

/-- [proved-derived; formal-checked] **Width zero is exactly constancy on the fibre.** The receiver
returns one face for every compatible cause, which is the whole content of "the face is
determined". -/
theorem width_eq_zero_iff {X : Type*} (F : Finset X) (hF : F.Nonempty) (R : X → ℚ) :
    width F hF R = 0 ↔ ∀ x ∈ F, ∀ y ∈ F, R x = R y := by
  constructor
  · intro h x hx y hy
    have hxy : |R x - R y| ≤ 0 := h ▸ abs_sub_le_width hF R hx hy
    have hzero : |R x - R y| = 0 := le_antisymm hxy (abs_nonneg _)
    have := abs_eq_zero.mp hzero
    linarith
  · intro h
    obtain ⟨a, ha⟩ := id hF
    have hsup : F.sup' hF R = R a :=
      le_antisymm (Finset.sup'_le hF R fun b hb => (h b hb a ha).le) (Finset.le_sup' R ha)
    have hinf : F.inf' hF R = R a :=
      le_antisymm (Finset.inf'_le R ha) (Finset.le_inf' hF R fun b hb => (h a ha b hb).le)
    simp only [width, hsup, hinf, sub_self]

/-! ## Release is receiver-relative, and the caller declares the law -/

/-- [definition] A face is **releasable** at a declared tolerance when the width falls inside it.
The tolerance belongs to the receiver's declaration; it is not a property of the fibre. -/
def Releasable {X : Type*} (F : Finset X) (hF : F.Nonempty) (R : X → ℚ) (tolerance : ℚ) : Prop :=
  width F hF R ≤ tolerance

/-- [proved-derived; formal-checked] **Releasable at every tolerance is exactly width zero.** The
third face of `width_eq_zero_iff`. -/
theorem releasable_at_every_tolerance_iff_width_zero {X : Type*} (F : Finset X) (hF : F.Nonempty)
    (R : X → ℚ) :
    (∀ tolerance : ℚ, 0 ≤ tolerance → Releasable F hF R tolerance) ↔ width F hF R = 0 := by
  constructor
  · intro h
    exact le_antisymm (by simpa [Releasable] using h 0 le_rfl) (width_nonneg F hF R)
  · intro h tolerance htolerance
    simp only [Releasable, h]
    exact htolerance

/-- [definition] **The five lawful non-release returns, and release.** There is no default among
them: which one a caller takes is declared by that caller's `ReleaseLaw`. `ask` names the probe
that would narrow the fibre most, `releaseCoarser` names the coarser invariant whose width *is*
inside tolerance, and `noContinuationBridges` says no admitted continuation closes the gap at all. -/
inductive ReleaseReturn (Probe Coarser : Type*) (tolerance : ℚ) where
  /-- The width is inside the declared tolerance. -/
  | released : ReleaseReturn Probe Coarser tolerance
  /-- Retain the plural fibre and emit nothing at this receiver. -/
  | hold : ReleaseReturn Probe Coarser tolerance
  /-- Declare a wider tolerance, named. -/
  | widen (widened : ℚ) : ReleaseReturn Probe Coarser tolerance
  /-- Name the input or observation that would narrow the fibre most. -/
  | ask (probe : Probe) : ReleaseReturn Probe Coarser tolerance
  /-- Release only the coarser invariant whose width is inside tolerance. The coarser width and
  the inequality against the *declaring law's own* tolerance are constructor arguments, so a
  `releaseCoarser` return outside tolerance cannot be formed at all — the arm carries its own
  soundness rather than deferring it to a separate check that a caller could route around. -/
  | releaseCoarser (coarser : Coarser) (coarserWidth : ℚ) (inside : coarserWidth ≤ tolerance) :
      ReleaseReturn Probe Coarser tolerance
  /-- No admitted continuation bridges the gap. -/
  | noContinuationBridges : ReleaseReturn Probe Coarser tolerance

/-- [definition] A **declared release law**: the caller's tolerance and the caller's decision, with
the single obligation that a `released` return really does have the width inside the tolerance.
Everything else about the decision is the caller's.

This is the formal content of "no default among them": `decide` is a field, so the law is supplied
and never conferred — the same clause `Foundation/ReceiverAtlas.lean::Capability` states for a
metric. -/
structure ReleaseLaw (X : Type*) (Probe Coarser : Type*) where
  /-- The receiver's declared tolerance. -/
  tolerance : ℚ
  /-- The caller's declared decision. -/
  decide : (F : Finset X) → (hF : F.Nonempty) → (R : X → ℚ) →
    ReleaseReturn Probe Coarser tolerance
  /-- The one obligation: a release is inside the declared tolerance. -/
  sound : ∀ (F : Finset X) (hF : F.Nonempty) (R : X → ℚ),
    decide F hF R = ReleaseReturn.released → Releasable F hF R tolerance
  /-- A named wider tolerance is actually wide enough for the width that provoked it. `widen`
  emits no face, but it *names* a tolerance, and a named tolerance that still would not release
  is not a proposal. -/
  widenSound : ∀ (F : Finset X) (hF : F.Nonempty) (R : X → ℚ) (widened : ℚ),
    decide F hF R = ReleaseReturn.widen widened → Releasable F hF R widened

/-- [definition] The law that holds whatever it cannot release. -/
def holdingLaw (X : Type*) (Probe Coarser : Type*) (tolerance : ℚ) :
    ReleaseLaw X Probe Coarser where
  tolerance := tolerance
  decide := fun F hF R =>
    if width F hF R ≤ tolerance then ReleaseReturn.released else ReleaseReturn.hold
  sound := by
    intro F hF R h
    by_cases hw : width F hF R ≤ tolerance
    · exact hw
    · rw [if_neg hw] at h
      exact absurd h (by intro hcontra; cases hcontra)
  widenSound := by
    intro F hF R widened h
    by_cases hw : width F hF R ≤ tolerance
    · rw [if_pos hw] at h
      exact absurd h (by intro hcontra; cases hcontra)
    · rw [if_neg hw] at h
      exact absurd h (by intro hcontra; cases hcontra)

/-- [definition] The law that proposes a wider tolerance instead of holding. -/
def wideningLaw (X : Type*) (Probe Coarser : Type*) (tolerance : ℚ) :
    ReleaseLaw X Probe Coarser where
  tolerance := tolerance
  decide := fun F hF R =>
    if width F hF R ≤ tolerance then ReleaseReturn.released
    else ReleaseReturn.widen (width F hF R)
  sound := by
    intro F hF R h
    by_cases hw : width F hF R ≤ tolerance
    · exact hw
    · rw [if_neg hw] at h
      exact absurd h (by intro hcontra; cases hcontra)
  widenSound := by
    intro F hF R widened h
    by_cases hw : width F hF R ≤ tolerance
    · rw [if_pos hw] at h
      exact absurd h (by intro hcontra; cases hcontra)
    · rw [if_neg hw] at h
      have hwidened : widened = width F hF R := by
        injection h.symm
      simp only [Releasable, hwidened, le_refl]

/-- [proved-derived; formal-checked] **Every lawful return other than `hold`, `ask` and
`noContinuationBridges` is inside the tolerance it names.** `released` is inside the law's own
declared tolerance by `ReleaseLaw.sound`; `widen w` is inside the tolerance `w` it names by
`ReleaseLaw.widenSound`; and `releaseCoarser` is inside the law's declared tolerance by the
inequality the constructor itself carries, so no separate check can be skipped for it. This is the
statement that a coarser release cannot leave the declared tolerance by being assembled under one
tolerance and released under another.

Rust counterpart: `crates/holonic-engine/src/receiver_release.rs::release`, whose `ReleaseCoarser`
arm recomputes `width ≤ tolerance` against the options' own tolerance, and
`LawfulOptions::assemble`, which refuses a `CoarserRelease` searched under a different tolerance
(`a_coarser_release_searched_under_a_wider_tolerance_is_refused`). -/
theorem every_lawful_return_other_than_hold_ask_or_no_continuation_is_inside_its_tolerance
    {X : Type*} {Probe Coarser : Type*} (law : ReleaseLaw X Probe Coarser)
    (F : Finset X) (hF : F.Nonempty) (R : X → ℚ) :
    (law.decide F hF R = ReleaseReturn.released → width F hF R ≤ law.tolerance) ∧
      (∀ widened : ℚ, law.decide F hF R = ReleaseReturn.widen widened →
        width F hF R ≤ widened) ∧
      (∀ (c : Coarser) (w : ℚ) (hw : w ≤ law.tolerance),
        law.decide F hF R = ReleaseReturn.releaseCoarser c w hw → w ≤ law.tolerance) := by
  refine ⟨law.sound F hF R, ?_, ?_⟩
  · intro widened h
    exact law.widenSound F hF R widened h
  · intro _ _ hw _
    exact hw

/-! ## An exact system whose event is future-stable while its timing is not -/

/-- [definition] The exact `t`-step map of the one-dimensional rational recurrence
`x_{t+1} = 2 x_t`. It is `Foundation/CausalChord.lean::Linearization` with `state = !![2]`, no
excitation and the identity readout: `Φ t x = 2^t x`. Every value is an exact rational. -/
def doubling (t : ℕ) (x : ℚ) : ℚ := 2 ^ t * x

/-- [definition] The **event**: the trajectory reaches the threshold `1`. -/
def Occurs (t : ℕ) (x : ℚ) : Prop := 1 ≤ doubling t x

instance (t : ℕ) (x : ℚ) : Decidable (Occurs t x) := by
  unfold Occurs; infer_instance

/-- [definition] The **time of the event** within the declared horizon `3`, and `4` — one past the
horizon — when the event does not occur by then. This is the receiver "time of event". -/
def timeOfEvent (x : ℚ) : ℕ :=
  if 1 ≤ doubling 0 x then 0
  else if 1 ≤ doubling 1 x then 1
  else if 1 ≤ doubling 2 x then 2
  else if 1 ≤ doubling 3 x then 3
  else 4

/-- [proved-derived; formal-checked] The returned step really is a crossing: whenever
`timeOfEvent x` is inside the horizon, the trajectory has reached the threshold there. The name is
earned, not asserted. -/
theorem timeOfEvent_crosses (x : ℚ) (h : timeOfEvent x ≤ 3) : Occurs (timeOfEvent x) x := by
  unfold timeOfEvent at h ⊢
  split_ifs at h ⊢ with h0 h1 h2 h3
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · omega

/-- [proved-derived; formal-checked] And no earlier step is a crossing: the returned step is the
*first*. -/
theorem timeOfEvent_is_least (x : ℚ) (t : ℕ) (ht : t < timeOfEvent x) : ¬ Occurs t x := by
  unfold timeOfEvent at ht
  split_ifs at ht with h0 h1 h2 h3
  · omega
  · interval_cases t
    · exact h0
  · interval_cases t
    · exact h0
    · exact h1
  · interval_cases t
    · exact h0
    · exact h1
    · exact h2
  · interval_cases t
    · exact h0
    · exact h1
    · exact h2
    · exact h3

/-- [definition] The receiver **"the event occurs by horizon 3"**, read into `ℚ` as `1` or `0` so
one width law serves every reading. -/
def occursByThree (x : ℚ) : ℚ := if timeOfEvent x ≤ 3 then 1 else 0

/-- [definition] The receiver **"the time of the event"**, read into `ℚ`. -/
def timingReading (x : ℚ) : ℚ := (timeOfEvent x : ℚ)

/-- [definition] The declared compatible fibre: two exact rational initial states. -/
def compatibleFibre : Finset ℚ := {1 / 8, 1 / 4}

theorem compatibleFibre_nonempty : compatibleFibre.Nonempty := ⟨1 / 8, by simp [compatibleFibre]⟩

theorem mem_compatibleFibre_eighth : (1 / 8 : ℚ) ∈ compatibleFibre := by simp [compatibleFibre]

theorem mem_compatibleFibre_quarter : (1 / 4 : ℚ) ∈ compatibleFibre := by simp [compatibleFibre]

theorem compatibleFibre_cases {x : ℚ} (hx : x ∈ compatibleFibre) :
    x = 1 / 8 ∨ x = 1 / 4 := by
  rw [compatibleFibre, Finset.mem_insert, Finset.mem_singleton] at hx
  exact hx

theorem timeOfEvent_eighth : timeOfEvent (1 / 8 : ℚ) = 3 := by
  have h0 : ¬ (1 ≤ doubling 0 (1 / 8 : ℚ)) := by unfold doubling; norm_num
  have h1 : ¬ (1 ≤ doubling 1 (1 / 8 : ℚ)) := by unfold doubling; norm_num
  have h2 : ¬ (1 ≤ doubling 2 (1 / 8 : ℚ)) := by unfold doubling; norm_num
  have h3 : (1 : ℚ) ≤ doubling 3 (1 / 8 : ℚ) := by unfold doubling; norm_num
  unfold timeOfEvent
  rw [if_neg h0, if_neg h1, if_neg h2, if_pos h3]

theorem timeOfEvent_quarter : timeOfEvent (1 / 4 : ℚ) = 2 := by
  have h0 : ¬ (1 ≤ doubling 0 (1 / 4 : ℚ)) := by unfold doubling; norm_num
  have h1 : ¬ (1 ≤ doubling 1 (1 / 4 : ℚ)) := by unfold doubling; norm_num
  have h2 : (1 : ℚ) ≤ doubling 2 (1 / 4 : ℚ) := by unfold doubling; norm_num
  unfold timeOfEvent
  rw [if_neg h0, if_neg h1, if_pos h2]

theorem occursByThree_eighth : occursByThree (1 / 8 : ℚ) = 1 := by
  unfold occursByThree
  rw [timeOfEvent_eighth]
  norm_num

theorem occursByThree_quarter : occursByThree (1 / 4 : ℚ) = 1 := by
  unfold occursByThree
  rw [timeOfEvent_quarter]
  norm_num

theorem timingReading_eighth : timingReading (1 / 8 : ℚ) = 3 := by
  unfold timingReading
  rw [timeOfEvent_eighth]
  norm_num

theorem timingReading_quarter : timingReading (1 / 4 : ℚ) = 2 := by
  unfold timingReading
  rw [timeOfEvent_quarter]
  norm_num

/-- [proved-derived; formal-checked] **An event can be future-stable while its timing is not.**
On the exact doubling system, over the compatible fibre `{1/8, 1/4}` and horizon `3`:

* the receiver "the event occurs by horizon 3" has width exactly `0` — it is released at *every*
  tolerance, by `releasable_at_every_tolerance_iff_width_zero`;
* the receiver "the time of the event" has width exactly `1` — it is released at no tolerance
  below `1`.

One fibre, two receivers, two opposite verdicts. This is the plan's clause that uncertainty is
structural rather than a scalar confidence: there is no single number attached to the fibre that
could have produced both answers. -/
theorem future_stable_event_with_unstable_timing :
    width compatibleFibre compatibleFibre_nonempty occursByThree = 0 ∧
      width compatibleFibre compatibleFibre_nonempty timingReading = 1 := by
  constructor
  · rw [width_eq_zero_iff]
    have key : ∀ z ∈ compatibleFibre, occursByThree z = 1 := by
      intro z hz
      rcases compatibleFibre_cases hz with rfl | rfl
      · exact occursByThree_eighth
      · exact occursByThree_quarter
    intro x hx y hy
    rw [key x hx, key y hy]
  · refine le_antisymm ?_ ?_
    · have hband : width compatibleFibre compatibleFibre_nonempty timingReading ≤ (3 : ℚ) - 2 := by
        refine width_le_of_bounds compatibleFibre_nonempty timingReading ?_ ?_
        · intro x hx
          rcases compatibleFibre_cases hx with rfl | rfl
          · rw [timingReading_eighth]; norm_num
          · rw [timingReading_quarter]
        · intro x hx
          rcases compatibleFibre_cases hx with rfl | rfl
          · rw [timingReading_eighth]
          · rw [timingReading_quarter]; norm_num
      linarith
    · have := abs_sub_le_width compatibleFibre_nonempty timingReading
        mem_compatibleFibre_eighth mem_compatibleFibre_quarter
      rw [timingReading_eighth, timingReading_quarter] at this
      norm_num at this
      exact this

/-- [proved-derived; formal-checked] **Release is receiver-relative and this file builds no global
gate.** The same compatible fibre releases one receiver at every tolerance and fails to release
another at any tolerance below `1`. AGENTS.md: *"A plural fibre does not impose a universal
certainty gate on generation."* -/
theorem release_is_receiver_relative_not_a_global_gate :
    (∀ tolerance : ℚ, 0 ≤ tolerance →
        Releasable compatibleFibre compatibleFibre_nonempty occursByThree tolerance) ∧
      ¬ Releasable compatibleFibre compatibleFibre_nonempty timingReading (1 / 2) := by
  obtain ⟨hzero, hone⟩ := future_stable_event_with_unstable_timing
  refine ⟨(releasable_at_every_tolerance_iff_width_zero _ _ _).mpr hzero, ?_⟩
  simp only [Releasable, hone]
  norm_num

/-- [counterexample; formal-checked] **No default among the lawful returns.** Two laws with the
*same* declared tolerance, both discharging the release obligation, return different arms on the
same fibre and the same reading. The library therefore cannot supply the decision; the caller
declares it. -/
theorem no_default_among_the_lawful_returns :
    (holdingLaw ℚ Unit Unit (1 / 2)).decide compatibleFibre compatibleFibre_nonempty
        timingReading ≠
      (wideningLaw ℚ Unit Unit (1 / 2)).decide compatibleFibre compatibleFibre_nonempty
        timingReading := by
  obtain ⟨_, hone⟩ := future_stable_event_with_unstable_timing
  have hnot : ¬ (width compatibleFibre compatibleFibre_nonempty timingReading ≤ 1 / 2) := by
    rw [hone]; norm_num
  simp only [holdingLaw, wideningLaw, if_neg hnot]
  intro h
  cases h

/-! ## A coarser receiver, and when it is actually coarser -/

/-- [definition] A factor map is **non-expansive** when it never increases a difference. A coarser
receiver is `g ∘ R` for such a `g`: the reading factors through `R`, so it is coarser in the sense
of `Foundation/Receiver.lean::Compression`, and the metric statement below is what makes it
narrower as well. -/
def NonExpansive (g : ℚ → ℚ) : Prop := ∀ a b : ℚ, |g a - g b| ≤ |a - b|

/-- [proved-derived; formal-checked] **A coarser receiver with a non-expansive factor map has no
larger width.** -/
theorem width_nonExpansive_factor {X : Type*} (F : Finset X) (hF : F.Nonempty) (R : X → ℚ)
    {g : ℚ → ℚ} (hg : NonExpansive g) : width F hF (g ∘ R) ≤ width F hF R := by
  obtain ⟨hi, hiF, hsup⟩ := Finset.exists_mem_eq_sup' hF (g ∘ R)
  obtain ⟨lo, hloF, hinf⟩ := Finset.exists_mem_eq_inf' hF (g ∘ R)
  have hbound : |g (R hi) - g (R lo)| ≤ |R hi - R lo| := hg _ _
  have hwidth : |R hi - R lo| ≤ width F hF R := abs_sub_le_width hF R hiF hloF
  have hval : width F hF (g ∘ R) = g (R hi) - g (R lo) := by
    unfold width
    rw [hsup, hinf]
    rfl
  rw [hval]
  calc g (R hi) - g (R lo) ≤ |g (R hi) - g (R lo)| := le_abs_self _
    _ ≤ |R hi - R lo| := hbound
    _ ≤ width F hF R := hwidth

/-- [counterexample; formal-checked] **And the hypothesis is needed.** The factor map `q ↦ 2 q` is a
perfectly good coarsening in the sense of factoring through `R` — the composite reading is a
function of `R`'s face and of nothing else — yet it strictly *widens* the reading. "Coarser" alone
does not narrow; non-expansiveness is the dropped hypothesis. -/
theorem expansive_factor_increases_width :
    width compatibleFibre compatibleFibre_nonempty ((fun q => 2 * q) ∘ timingReading) = 2 ∧
      width compatibleFibre compatibleFibre_nonempty timingReading = 1 := by
  obtain ⟨_, hone⟩ := future_stable_event_with_unstable_timing
  refine ⟨le_antisymm ?_ ?_, hone⟩
  · have hband :
        width compatibleFibre compatibleFibre_nonempty ((fun q => 2 * q) ∘ timingReading)
          ≤ (6 : ℚ) - 4 := by
      refine width_le_of_bounds compatibleFibre_nonempty _ ?_ ?_
      · intro x hx
        rcases compatibleFibre_cases hx with rfl | rfl
        · simp only [Function.comp_apply, timingReading_eighth]; norm_num
        · simp only [Function.comp_apply, timingReading_quarter]; norm_num
      · intro x hx
        rcases compatibleFibre_cases hx with rfl | rfl
        · simp only [Function.comp_apply, timingReading_eighth]; norm_num
        · simp only [Function.comp_apply, timingReading_quarter]; norm_num
    linarith
  · have := abs_sub_le_width compatibleFibre_nonempty ((fun q => 2 * q) ∘ timingReading)
      mem_compatibleFibre_eighth mem_compatibleFibre_quarter
    simp only [Function.comp_apply, timingReading_eighth, timingReading_quarter] at this
    norm_num at this
    exact this

/-- [proved-derived; formal-checked] And `q ↦ 2 q` is indeed not non-expansive, so the
counterexample does not contradict `width_nonExpansive_factor`. -/
theorem doubling_factor_not_nonExpansive : ¬ NonExpansive (fun q : ℚ => 2 * q) := by
  intro h
  have := h 1 0
  norm_num at this

/-! ## The coarser receiver really does factor through the finer one -/

/-- [proved-derived; formal-checked] A coarser reading `g ∘ R` factors through `R` in the exact
sense of `Foundation/Receiver.lean`: every pair `R` identifies, `g ∘ R` identifies too. So
`releaseCoarser` is a lawful return and not a change of subject — it releases a strictly weaker
face of the same current. -/
theorem coarser_receiver_factors {X : Type*} (R : X → ℚ) (g : ℚ → ℚ) {x y : X}
    (h : R x = R y) : (g ∘ R) x = (g ∘ R) y := by
  simp only [Function.comp_apply, h]

/-- [definition] The converse fails, which is why `releaseCoarser` is worth returning at all: the
coarser receiver can release a fibre the finer one cannot. On the declared fibre, the coarser
reading "did it happen at all" is constant where the finer reading "when" is not, and
`Foundation/Receiver.lean::ReceiverInsufficiency` is that fact as a witness. -/
def timingInsufficiency :
    Soma.Holonics.ReceiverInsufficiency
      (fun x : compatibleFibre => occursByThree x.1)
      (fun x : compatibleFibre => timingReading x.1) where
  left := ⟨1 / 8, mem_compatibleFibre_eighth⟩
  right := ⟨1 / 4, mem_compatibleFibre_quarter⟩
  sameEntering := by
    simp only [occursByThree_eighth, occursByThree_quarter]
  differentReturned := by
    simp only [timingReading_eighth, timingReading_quarter]
    norm_num

/-- [proved-derived; formal-checked] Hence no receiver-to-receiver transformer carries the released
coarse face back into the unreleased fine one: `releaseCoarser` genuinely drops content, and says
so. Cited from `Foundation/Receiver.lean::ReceiverTransformer.excludesInsufficiency`. -/
theorem no_transformer_from_the_released_coarse_face :
    IsEmpty (Soma.Holonics.ReceiverTransformer
      (fun x : compatibleFibre => occursByThree x.1)
      (fun x : compatibleFibre => timingReading x.1)) :=
  ⟨fun t => t.excludesInsufficiency timingInsufficiency⟩

end Soma.Holonics.Foundation.ReceiverRelease

section Audit
open Soma.Holonics.Foundation.ReceiverRelease

#print axioms width_nonneg
#print axioms abs_sub_le_width
#print axioms width_le_of_bounds
#print axioms width_mono
#print axioms width_eq_zero_iff
#print axioms releasable_at_every_tolerance_iff_width_zero
#print axioms holdingLaw
#print axioms wideningLaw
#print axioms every_lawful_return_other_than_hold_ask_or_no_continuation_is_inside_its_tolerance
#print axioms timeOfEvent_crosses
#print axioms timeOfEvent_is_least
#print axioms future_stable_event_with_unstable_timing
#print axioms release_is_receiver_relative_not_a_global_gate
#print axioms no_default_among_the_lawful_returns
#print axioms width_nonExpansive_factor
#print axioms expansive_factor_increases_width
#print axioms doubling_factor_not_nonExpansive
#print axioms coarser_receiver_factors
#print axioms timingInsufficiency
#print axioms no_transformer_from_the_released_coarse_face
end Audit
