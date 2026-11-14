import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-!
# A founding at zero keeps the forward

The plateau record of November 14 (`research/records/2026-11-14_THE_LINES_PLATEAU_WAS_THE_FACES_WIDTH_…`, §3 and §5; atlas
`tower.face-lane-composition`) founds a lane beside a trained field (`Field::laned`): every read from the lane and every write into the
old coordinates from it stands at zero, the lane's own rows drawn. #410 owes the statement that such a founding keeps every face. In the
chart of the lane's founding the field's state is a pair `(u, v)` of the old coordinates and the lane's; a tick is a map that, with the
reads from the lane at zero, updates `u` from `u` alone and `v` from both (the lane is written by the old coordinates and by itself, its
chart its own power, [`lane_chart`]). This file proves what follows on any types.

[proved-standard; formal-checked] What is proved.

1. **The old orbit is kept** (`old_orbit`): for a step `(u, v) ↦ (f u, g u v)` the old component after `n` steps is `f^[n] u`, whatever
   `g` and the lane's start `v` are.
2. **Every face is kept** (`faces_kept`): a readout that reads only the old component returns, after `n` steps, the old field's face.
3. **Every standing entry's covector is kept** (`standing_covector_kept`): where the old entries `θ` enter the step through `f θ` and a
   readout `r θ` of the old component only, the composite as a function of `θ` is the old field's composite, for every lane start, so its
   derivative in `θ` (any derivative a function of `θ` alone has) is the old one; stated as the equality of the two functions of `θ`.

Limits: the founding's chart is the pair `(old, lane)` with the reads from the lane exactly zero; the realization's widths and releases are
not modelled (the release of a sum with a zero term is the release of the sum, which the host's tests read bit for bit); a tower's level and
glue are a further old component and a further step of the same block-triangular form, not stated separately. The Rust `Field::laned` and the
host's test `a_lane_founded_beside_a_tower_keeps_every_face` are not tied to these statements.

The computational object is the helical pair interaction: the lane is a register beside the pair contacts' face, written by them and read
by none at its founding. Of the winding guide's six general objects this touches the faces and placement (a face read through the old
coordinates) and the tube (the ticks as a clocked span); the helix, pair, cell holonomy and tower thread stay attached.

Consumers: the atlas row `tower.face-lane-composition`; #410's box for a founding at zero.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.FoundingAtZero

variable {U V F Θ : Type*}

/-- [definition] **A tick with the reads from the lane at zero**: the old coordinates step from themselves alone, the lane from both. -/
def tick (f : U → U) (g : U → V → V) (p : U × V) : U × V := (f p.1, g p.1 p.2)

/-- [proved-standard; formal-checked] **The old orbit is kept**: after `n` ticks the old component is `f^[n] u`, whatever the lane does. -/
theorem old_orbit (f : U → U) (g : U → V → V) (u : U) (v : V) (n : ℕ) : ((tick f g)^[n] (u, v)).1 = f^[n] u := by
  induction n generalizing u v with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (f u) (g u v)

/-- [proved-standard; formal-checked] **Every face is kept**: a readout of the old component alone reads the old field's face. -/
theorem faces_kept (f : U → U) (g : U → V → V) (read : U → F) (u : U) (v : V) (n : ℕ) :
    read ((tick f g)^[n] (u, v)).1 = read (f^[n] u) := by
  rw [old_orbit]

/-- [proved-standard; formal-checked] **Every standing entry's covector is kept**: the composite of the laned field as a function of the
old entries `θ` is the old field's composite, for every lane start, so every derivative in `θ` is the old one. -/
theorem standing_covector_kept (f : Θ → U → U) (g : Θ → U → V → V) (read : Θ → U → F) (u : U) (v : V) (n : ℕ) :
    (fun θ => read θ ((tick (f θ) (g θ))^[n] (u, v)).1) = fun θ => read θ ((f θ)^[n] u) := by
  funext θ
  rw [old_orbit]

end Holonics.HNN.FoundingAtZero
