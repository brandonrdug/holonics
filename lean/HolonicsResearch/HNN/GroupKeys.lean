import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import HolonicsResearch.Geometry.Frustration

/-!
# HNN.GroupKeys: phase and rotation keys are located by the holonomy of the menu's closed walks, up to the gauge

[definition] The part of #410's box "Continuous keys: loop-closure inference over continuous configuration spaces
(finite menus are done in `HNN/Keys`)" that configuration spaces which are groups carry. `HNN/ContactFixedPoint`
(#1029) took the linear contacts, whose keys are an affine fibre gauged by the readings' kernel, and left "nonlinear
configuration spaces, curved strands, phase and rotation keys"; this module takes the phase and rotation keys. The
key is the navigators' initial configuration, the Bombe infers it by pairwise loop closure over the menu of contacts,
and learning is locating keys: here the configuration space is a group `G` (the circle of phases `ℝ/ℤ`, the rotations
of `ℝ³`), each contact of the menu carries an element of `G`, and closure is the holonomy of a closed walk.

[definition] The setting. A menu is an incidence `Γ : Contacts V E` of `Geometry/Frustration` (contact `e` runs from
port `Γ.src e` to port `Γ.tgt e`; several contacts may join one pair of ports, and a list of `n` contacts is
`E = Fin n`) with an element `g_e ∈ G` on each contact. A **key** is a configuration `x : V → G` that every contact
transports, `x(tgt e) = g_e x(src e)` (`IsKey`). A step walks a contact along it or against it, carrying `g_e` or
`g_e⁻¹` (`stepElt`); a walk is a list of steps that chain from port to port (`IsWalk`), and its **holonomy** is the
ordered product of its steps' elements, the last step leftmost (`hol`; the order of `HNN/Keys.walkLoop` and
`SurvivorsCycleFibre.transport`). The **gauge** multiplies every port's key on the right by one element,
`x ↦ x·k` (`gauge`); a **change of frame** `h : V → G` at the ports moves each contact to `h(tgt e) g_e h(src e)⁻¹`
(`regauge`). A configuration `x` **produces** the menu `g_e = x(tgt e) x(src e)⁻¹` (`produced`): the contacts that a
true key leaves in the data.

Sources: the box; the closing paragraph of `HNN/Keys`, which leaves nonlinear continuous keys to #410
(`walk_transports`, `contact_menu_closes`, `consistent_unique`, `gauge_fix_unique`); `HNN/SurvivorsCycleFibre` (on the
finite rotor only the fundamental cycles decide, `survives_iff_fundamental`); `HNN/ContactFixedPoint` (its "What is not
claimed"; `keys_eq_orbit`, `gauge_fix_unique`); `Physics/TwoWayField.composes_iff_coboundary` (the same law on the
complete graph of cells, read round its triangles); `Geometry/Frustration` (the incidence, and the frustration of an
additive connection); the record of October 26 that the atlas rows `key.connection-cheeger` and
`key.unique-games-frontier` cite ("Information diffuses in the potential, travels in the turn, and a key is read from
diffusion only to its square root", §0 statement 6: a key is a gauge, the labelling a section of a flat connection,
found by propagating one hypothesis along a tree and checking one holonomy per independent cycle); the atlas rows
`key.continuous-fibre` (whose scope leaves phase and rotation keys unstated), `key.consistent-fibre`, `key.gauge-orbit`,
`key.menu-loop-closure`, `hnn.gauge-fix-unique`, `holonomy.cell-face`, `holonomy.composes-iff-coboundary`,
`holonomy.first-order-cochain` and `curvature.discrete-da-squared`.

What is proved. Items 1 to 5 and the general statements of items 6, 7, 9 and 10 are classical facts of flat
connections on a graph with values in a group (a connection is the coboundary of a frame exactly when every closed walk
closes, and its sections are a torsor of the group) and of the circle's synchronization cost,
[proved-standard; formal-checked]; their readings on keys and the witnesses are [proved-derived; formal-checked], and
the refusals [counterexample; formal-checked].

1. **Walks** (`stepSrc_flip`, `stepTgt_flip`, `stepElt_flip`, `rev_cons`, `isWalk_append`, `hol_append`,
   `isWalk_rev`, `hol_rev`). Walks concatenate, `hol(w ++ w′) = hol(w′) hol(w)`, and reverse, `hol(rev w) = hol(w)⁻¹`.
2. **Keys close every loop** (`key_step`, `key_transports`, `key_closes`, `isKey_produced`, `produced_closes`). A key
   is carried along every walk, `x(end) = hol(walk) x(start)`, so on a menu that has a key every closed walk has
   holonomy `1`. A configuration is a key of the menu it produces, so every loop of the observed menu closes (the
   group-valued `HNN/Keys.contact_menu_closes`).
3. **Closure locates the key up to the gauge** (`Connected`, `Closes`, `walkKey`, `hol_eq_of_closes`, `isKey_walkKey`,
   `exists_key_iff`, `closes_everywhere`, `key_eq_of_base`, `isKey_gauge`, `gauge_injective`, `keys_torsor`,
   `keys_eq_orbit`, `gauge_fix_unique`, `produced_keys`). On a menu whose every port a walk from the base `v₀` reaches,
   keys exist exactly when every closed walk at `v₀` has holonomy `1`; the key is then read off walks from the base,
   `x(v) = hol(any walk v₀ → v)`, and closure at `v₀` is closure at every port. A key is fixed by its value at the
   base; the gauge acts freely and transitively on the keys (`∃! k, y = x·k`), so the keys are one orbit `{x·k}`, and
   fixing `x(v₀) = 1` leaves one key (the form of `HNN/Keys.gauge_fix_unique`). A menu a true key produced has that
   key's orbit as its keys.
4. **Frames conjugate the holonomy** (`hol_rebase`, `stepElt_regauge`, `hol_regauge`, `isKey_regauge`,
   `hol_regauge_comm`). A loop at `u` read from `v₀` along a walk `p` has holonomy `hol(p)⁻¹ hol(γ) hol(p)`. A change of
   frame `h` carries the holonomy of a walk from `u` to `w` to `h(w) hol h(u)⁻¹`, so a closed walk's holonomy is
   conjugated by the frame at its base (`holonomy.cell-face`), and the keys move to `h·x`; on a commutative carrier the
   holonomy is gauge free.
5. **A tree retains nothing to infer** (`Reached`, `Grows`, `Grows.of_append`, `growing_has_keys`, `tree_has_keys`,
   `tree_closes`, `reached_append_one`, `growing_unique`, `tree_reading_decides`). A growing list, each contact of which
   leaves a port the earlier ones reached for a port none reached (`HNN/Keys.TraversalOrdered` with every target new),
   has a configuration that all its contacts transport, at every assignment of elements; so a menu such a list covers
   has keys whatever its contacts carry, and every closed walk of it closes: the only constraints are the cycles.
   What a growing list carries is fixed on the ports it reaches by its base value, so on a menu whose growing list
   reaches every port, keys exist exactly when the tree's reading fits every contact off the list, one closure per
   chord (the group-valued `SurvivorsCycleFibre.survives_iff_fundamental`).
6. **Phase keys** (`Phase`, `phase`, `phaseMenu`, `offset`, `offsetSum`, `phase_zero`, `phase_add`, `phase_neg`,
   `phase_sub`, `phase_eq_one_iff`, `phase_surjective`, `exists_lift`, `stepElt_phaseMenu`, `hol_phaseMenu`,
   `phase_closes_iff`, `phase_keys_iff`, `isKey_phase_iff`, `phase_key_global_phase`). On `ℝ/ℤ` with real offsets
   `ψ_e`, a walk's holonomy is the class mod `1` of the sum of its signed offsets, so a connected phase menu has keys
   exactly when every closed walk at the base sums to an integer. Read through real lifts `θ`, a key asks
   `θ(tgt e) − θ(src e) − ψ_e ∈ ℤ` on every contact; every key has real lifts, and two keys differ by one global phase.
7. **The phase cost** (`phaseCost`, `one_sub_cos_eq_zero_iff`, `phaseCost_nonneg`, `phaseCost_eq_zero_iff`,
   `phaseCost_add_int`, `phaseCost_congr`, `phaseCost_add_const`). The least-squares cost
   `Σ_e (1 − cos 2π(θ(tgt e) − θ(src e) − ψ_e))` of real lifts is nonnegative and vanishes exactly at the keys. It does
   not read the lifts' integer windings, so it is a function on `(ℝ/ℤ)^V`, and the global phase leaves it unchanged.
8. **The triangle of phases** (`triangle`, `roundWalk`, `roundWalk_isWalk`, `triangle_connected`, `third_offsetSum`,
   `third_has_key`, `quarter_offsetSum`, `quarter_no_key`, `quarter_cost_pos`). Offsets `⅓, ⅓, ⅓` round three ports
   sum to `1`, and the triangle has the key `(0, ⅓, ⅔)`; offsets `¼, ¼, ¼` sum to `¾`, the triangle is frustrated, it
   has no key, and its cost is positive at every lift.
9. **Rotation keys** (`double_contact_no_key`, `double_contact_hol`, `Rotation`, `quarterTurnMatrix`,
   `quarterTurnXMatrix`, `quarterTurnMatrix_mem`, `quarterTurnXMatrix_mem`, `quarterTurn`, `quarterTurnX`,
   `quarterTurn_ne_one`, `quarterTurns_noncommute`, `doubleContact`, `doubleContact_connected`,
   `rotation_double_no_key`, `rotation_produced_keys`, `rotation_round_hol`, `rotation_regauge_moves_hol`). Items 2 to
   5 hold for `SO(3)` as for every group. Two contacts on one pair of ports that carry different elements leave no key
   (their loop's holonomy is `g₂⁻¹ g₁ ≠ 1`): the double contact carrying `1` and the quarter-turn about `e₃` has no
   rotation key, while a double contact a true rotation key produced has that key's gauge orbit as its keys. The
   quarter-turns about `e₃` and `e₁` do not commute, and a change of frame by the second moves the triangle's holonomy
   off the first: on a non-commutative carrier only the holonomy's conjugacy class is gauge free.
10. **The frustration vanishes exactly at the keys** (`frustration_eq_zero_iff`). For an additive carrier (`ℤ/k`, `ℤ`,
    a torus) and nonzero weights, the frustration of `Geometry/Frustration` is zero exactly when the menu has a key,
    and so, by item 3, on a connected menu exactly when every closed walk at the base closes.

What is not claimed. Noisy keys: a menu that no key fits, and the cost's minimizers and positive minimum (the frustrated
triangle's cost is shown positive at every lift; its minimum is not read). A deposition law that locates a phase or a
rotation key (a Kuramoto-type descent of the cost and its convergence; the linear case is `HNN/ContactFixedPoint`'s).
Curved strands, the helical pair's nonlinear reading `Δ = x_a(s) − x_b(t)`, and keys on homogeneous spaces that are not
groups (a direction on the sphere, which a rotation moves with a stabilizer): both stay with #410. The count
`|E| − |V| + 1` of the chords and a cycle basis are not formalized; item 5 states the chords' closures for a growing
list that reaches every port. The connection Cheeger bound (`key.connection-cheeger`) is cited and not restated. The
statements are over Mathlib's `ℝ` and its rotation matrices; the precision law's declared widths, releases and
remainders are not modeled. No parity ties these statements to a Rust owner, and nothing here says that the machine's
deposition is this law.

The computational object is the helical pair interaction read on a menu whose contacts carry group elements: each
contact is a pair contact whose transport (a turn of the circle of phases, a rotation of `ℝ³`) carries one port's
configuration to the other's, and a closed walk closes when its transports compose to the identity, the cell holonomy
of a `G`-connection on the menu. Of the winding guide's six general objects this touches the pair (the contacts and
their transports), faces and placement (the keys, their gauge and the base value that fixes it), the cell holonomy (a
closed walk's holonomy, conjugated by a change of frame) and the helix (a phase key's real lift, whose integer winding
the cost does not read); the tube and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.GroupKeys

open Holonics.Geometry.Frustration

/-! ## 1. Keys, walks and their holonomy -/

section Walks

variable {V E G : Type*} [Group G] (Γ : Contacts V E)

/-- [definition] **A key** of the menu `(Γ, g)`: a configuration every contact transports, `x(tgt e) = g_e x(src e)`. -/
def IsKey (g : E → G) (x : V → G) : Prop := ∀ e, x (Γ.tgt e) = g e * x (Γ.src e)

/-- [definition] The port a step leaves: a contact walked along it (`true`) leaves its source, against it its target. -/
def stepSrc : E × Bool → V
  | (e, true) => Γ.src e
  | (e, false) => Γ.tgt e

/-- [definition] The port a step reaches. -/
def stepTgt : E × Bool → V
  | (e, true) => Γ.tgt e
  | (e, false) => Γ.src e

/-- [definition] The element a step carries: `g_e` along its contact, `g_e⁻¹` against it. -/
def stepElt (g : E → G) : E × Bool → G
  | (e, true) => g e
  | (e, false) => (g e)⁻¹

/-- [definition] The step walked the other way. -/
def flipStep (s : E × Bool) : E × Bool := (s.1, !s.2)

/-- [definition] **A walk of the menu** from `u` to `w`: each step leaves the port the step before it reached. -/
def IsWalk : V → List (E × Bool) → V → Prop
  | u, [], w => u = w
  | u, s :: ws, w => stepSrc Γ s = u ∧ IsWalk (stepTgt Γ s) ws w

/-- [definition] **The holonomy of a walk**: its steps' elements multiplied in order, the last step leftmost. -/
def hol (g : E → G) : List (E × Bool) → G
  | [] => 1
  | s :: ws => hol g ws * stepElt g s

/-- [definition] The walk read backwards, each step flipped. -/
def rev (ws : List (E × Bool)) : List (E × Bool) := (ws.map flipStep).reverse

/-- [definition] **The menu a configuration produces**, `g_e = x(tgt e) x(src e)⁻¹`: a true key's data. -/
def produced (x : V → G) : E → G := fun e => x (Γ.tgt e) * (x (Γ.src e))⁻¹

/-- [definition] **The right gauge**: every port's key multiplied on the right by one element `k`. -/
def gauge (x : V → G) (k : G) : V → G := fun v => x v * k

/-- [definition] **A change of frame** `h` at the ports: each contact moves to `h(tgt e) g_e h(src e)⁻¹`. -/
def regauge (h : V → G) (g : E → G) : E → G := fun e => h (Γ.tgt e) * g e * (h (Γ.src e))⁻¹

variable {Γ}

/-- [proved-standard; formal-checked] A flipped step leaves the port the step reached. -/
theorem stepSrc_flip (s : E × Bool) : stepSrc Γ (flipStep s) = stepTgt Γ s := by
  obtain ⟨e, _ | _⟩ := s <;> rfl

/-- [proved-standard; formal-checked] A flipped step reaches the port the step left. -/
theorem stepTgt_flip (s : E × Bool) : stepTgt Γ (flipStep s) = stepSrc Γ s := by
  obtain ⟨e, _ | _⟩ := s <;> rfl

/-- [proved-standard; formal-checked] A flipped step carries the inverse element. -/
theorem stepElt_flip (g : E → G) (s : E × Bool) : stepElt g (flipStep s) = (stepElt g s)⁻¹ := by
  obtain ⟨e, _ | _⟩ := s <;> simp [flipStep, stepElt]

/-- [proved-standard; formal-checked] Reading a walk backwards puts its first step, flipped, last. -/
theorem rev_cons (s : E × Bool) (ws : List (E × Bool)) : rev (s :: ws) = rev ws ++ [flipStep s] := by
  simp [rev]

/-- [proved-standard; formal-checked] Two lists of steps join into a walk exactly when they are walks that meet. -/
theorem isWalk_append {u w : V} {ws ws' : List (E × Bool)} :
    IsWalk Γ u (ws ++ ws') w ↔ ∃ v, IsWalk Γ u ws v ∧ IsWalk Γ v ws' w := by
  induction ws generalizing u with
  | nil => simp [IsWalk]
  | cons s ws ih =>
      simp only [List.cons_append, IsWalk, ih]
      constructor
      · rintro ⟨h1, v, h2, h3⟩
        exact ⟨v, ⟨h1, h2⟩, h3⟩
      · rintro ⟨v, ⟨h1, h2⟩, h3⟩
        exact ⟨h1, v, h2, h3⟩

/-- [proved-standard; formal-checked] **Holonomy composes**: `hol(w ++ w′) = hol(w′) hol(w)`. -/
theorem hol_append (g : E → G) (ws ws' : List (E × Bool)) :
    hol g (ws ++ ws') = hol g ws' * hol g ws := by
  induction ws with
  | nil => simp [hol]
  | cons s ws ih => simp only [List.cons_append, hol, ih, mul_assoc]

/-- [proved-standard; formal-checked] A walk read backwards is a walk from its end to its start. -/
theorem isWalk_rev {u w : V} {ws : List (E × Bool)} (h : IsWalk Γ u ws w) :
    IsWalk Γ w (rev ws) u := by
  induction ws generalizing u with
  | nil =>
      simp only [IsWalk] at h
      subst h
      simp [rev, IsWalk]
  | cons s ws ih =>
      obtain ⟨hs, hrest⟩ := h
      rw [rev_cons, isWalk_append]
      exact ⟨stepTgt Γ s, ih hrest, by simp [IsWalk, stepSrc_flip, stepTgt_flip, hs]⟩

/-- [proved-standard; formal-checked] **A walk read backwards has the inverse holonomy.** -/
theorem hol_rev (g : E → G) (ws : List (E × Bool)) : hol g (rev ws) = (hol g ws)⁻¹ := by
  induction ws with
  | nil => simp [rev, hol]
  | cons s ws ih =>
      rw [rev_cons, hol_append, ih]
      simp [hol, stepElt_flip, mul_inv_rev]

/-- [proved-standard; formal-checked] A key is carried by one step, along its contact or against it. -/
theorem key_step {g : E → G} {x : V → G} (hx : IsKey Γ g x) (s : E × Bool) :
    x (stepTgt Γ s) = stepElt g s * x (stepSrc Γ s) := by
  obtain ⟨e, _ | _⟩ := s
  · simp only [stepTgt, stepSrc, stepElt]
    rw [hx e, inv_mul_cancel_left]
  · exact hx e

/-- [proved-standard; formal-checked] **A key is carried along every walk**: `x(end) = hol(walk) x(start)`. -/
theorem key_transports {g : E → G} {x : V → G} (hx : IsKey Γ g x) :
    ∀ {u w : V} (ws : List (E × Bool)), IsWalk Γ u ws w → x w = hol g ws * x u
  | u, w, [], h => by
      simp only [IsWalk] at h
      subst h
      simp [hol]
  | u, w, s :: ws, h => by
      obtain ⟨hs, hrest⟩ := h
      rw [key_transports hx ws hrest, key_step hx s, hs, hol, mul_assoc]

/-- [proved-standard; formal-checked] **Keys close every loop**: with a key, every closed walk has holonomy `1`. -/
theorem key_closes {g : E → G} {x : V → G} (hx : IsKey Γ g x) {u : V} {ws : List (E × Bool)}
    (h : IsWalk Γ u ws u) : hol g ws = 1 :=
  mul_eq_right.mp (key_transports hx ws h).symm

/-- [proved-derived; formal-checked] A configuration is a key of the menu it produces. -/
theorem isKey_produced (x : V → G) : IsKey Γ (produced Γ x) x := fun e => by
  simp [produced]

/-- [proved-derived; formal-checked] **The observed menu closes**: every loop of a menu a true key produced closes. -/
theorem produced_closes (x : V → G) {u : V} {ws : List (E × Bool)} (h : IsWalk Γ u ws u) :
    hol (produced Γ x) ws = 1 :=
  key_closes (isKey_produced x) h

end Walks

/-! ## 2. Closure locates the key up to the right gauge -/

section Locate

variable {V E G : Type*} [Group G] (Γ : Contacts V E)

/-- [definition] **A connected menu**: a walk from the base `v₀` reaches every port. -/
def Connected (v₀ : V) : Prop := ∀ v, ∃ ws, IsWalk Γ v₀ ws v

/-- [definition] **The menu closes at `v₀`**: every closed walk at `v₀` has holonomy `1`. -/
def Closes (g : E → G) (v₀ : V) : Prop := ∀ ws, IsWalk Γ v₀ ws v₀ → hol g ws = 1

/-- [definition] **The key read off walks from the base**: at each port, the holonomy of a chosen walk from `v₀`. -/
noncomputable def walkKey {v₀ : V} (hc : Connected Γ v₀) (g : E → G) (v : V) : G :=
  hol g (hc v).choose

variable {Γ} {g : E → G} {v₀ : V}

/-- [proved-standard; formal-checked] Under closure at the base, two walks from it to one port carry one holonomy. -/
theorem hol_eq_of_closes (hcl : Closes Γ g v₀) {v : V} {ws ws' : List (E × Bool)}
    (h : IsWalk Γ v₀ ws v) (h' : IsWalk Γ v₀ ws' v) : hol g ws = hol g ws' := by
  have hw : IsWalk Γ v₀ (ws ++ rev ws') v₀ := isWalk_append.mpr ⟨v, h, isWalk_rev h'⟩
  have := hcl _ hw
  rw [hol_append, hol_rev, inv_mul_eq_one] at this
  exact this.symm

/-- [proved-standard; formal-checked] Under closure at the base, the key read off walks from the base is a key. -/
theorem isKey_walkKey (hc : Connected Γ v₀) (hcl : Closes Γ g v₀) : IsKey Γ g (walkKey Γ hc g) := by
  intro e
  have hs := (hc (Γ.src e)).choose_spec
  have ht := (hc (Γ.tgt e)).choose_spec
  have hw : IsWalk Γ v₀ ((hc (Γ.src e)).choose ++ [(e, true)]) (Γ.tgt e) :=
    isWalk_append.mpr ⟨Γ.src e, hs, by simp [IsWalk, stepSrc, stepTgt]⟩
  have := hol_eq_of_closes hcl hw ht
  rw [hol_append] at this
  simp only [walkKey, ← this, hol, stepElt, one_mul]

/-- [proved-standard; formal-checked] **On a connected menu, keys exist exactly when the menu closes at the base.** -/
theorem exists_key_iff (hc : Connected Γ v₀) : (∃ x, IsKey Γ g x) ↔ Closes Γ g v₀ :=
  ⟨fun ⟨_, hx⟩ _ h => key_closes hx h, fun hcl => ⟨_, isKey_walkKey hc hcl⟩⟩

/-- [proved-standard; formal-checked] On a connected menu, closure at the base is closure at every port. -/
theorem closes_everywhere (hc : Connected Γ v₀) (hcl : Closes Γ g v₀) (u : V) : Closes Γ g u := by
  obtain ⟨x, hx⟩ := (exists_key_iff hc).mpr hcl
  exact fun ws h => key_closes hx h

/-- [proved-standard; formal-checked] On a connected menu a key is fixed by its value at the base. -/
theorem key_eq_of_base (hc : Connected Γ v₀) {x y : V → G} (hx : IsKey Γ g x) (hy : IsKey Γ g y)
    (h : x v₀ = y v₀) : x = y := by
  funext v
  obtain ⟨ws, hw⟩ := hc v
  rw [key_transports hx ws hw, key_transports hy ws hw, h]

/-- [proved-standard; formal-checked] The right gauge carries keys to keys. -/
theorem isKey_gauge {x : V → G} (hx : IsKey Γ g x) (k : G) : IsKey Γ g (gauge x k) := fun e => by
  simp only [gauge, hx e, mul_assoc]

/-- [proved-standard; formal-checked] The right gauge acts freely: distinct elements move a configuration apart. -/
theorem gauge_injective [Nonempty V] (x : V → G) : Function.Injective (gauge x) := fun k k' h => by
  have := congrFun h (Classical.arbitrary V)
  simpa [gauge] using this

/-- [proved-standard; formal-checked] **The keys are a torsor**: two keys of a connected menu differ by one gauge. -/
theorem keys_torsor (hc : Connected Γ v₀) {x y : V → G} (hx : IsKey Γ g x) (hy : IsKey Γ g y) :
    ∃! k, y = gauge x k := by
  refine ⟨(x v₀)⁻¹ * y v₀, key_eq_of_base hc hy (isKey_gauge hx _) (by simp [gauge]), ?_⟩
  rintro k rfl
  simp [gauge]

/-- [proved-derived; formal-checked] **A connected menu's keys are one gauge orbit** (cf. `Keys.fibre_eq_orbit`). -/
theorem keys_eq_orbit (hc : Connected Γ v₀) {x : V → G} (hx : IsKey Γ g x) :
    {y | IsKey Γ g y} = Set.range (gauge x) := by
  ext y
  constructor
  · intro hy
    obtain ⟨k, hk, _⟩ := keys_torsor hc hx hy
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, rfl⟩
    exact isKey_gauge hx k

/-- [proved-derived; formal-checked] **Gauge fixing is unique**: exactly one key of a connected menu has `x(v₀) = 1`. -/
theorem gauge_fix_unique (hc : Connected Γ v₀) (hne : ∃ x, IsKey Γ g x) :
    ∃! x, IsKey Γ g x ∧ x v₀ = 1 := by
  obtain ⟨x, hx⟩ := hne
  refine ⟨gauge x (x v₀)⁻¹, ⟨isKey_gauge hx _, by simp [gauge]⟩, ?_⟩
  rintro y ⟨hy, hy₀⟩
  exact key_eq_of_base hc hy (isKey_gauge hx _) (by simp [gauge, hy₀])

/-- [proved-derived; formal-checked] The keys of a connected menu a true key produced are that key's gauge orbit. -/
theorem produced_keys (hc : Connected Γ v₀) (x : V → G) :
    {y | IsKey Γ (produced Γ x) y} = Set.range (gauge x) :=
  keys_eq_orbit hc (isKey_produced x)

/-- [proved-standard; formal-checked] **A change of base conjugates**: along `p` a loop reads `hol(p)⁻¹ hol hol(p)`. -/
theorem hol_rebase {u : V} {p γ : List (E × Bool)} (hp : IsWalk Γ v₀ p u) (hγ : IsWalk Γ u γ u) :
    IsWalk Γ v₀ (p ++ γ ++ rev p) v₀ ∧ hol g (p ++ γ ++ rev p) = (hol g p)⁻¹ * hol g γ * hol g p := by
  refine ⟨isWalk_append.mpr ⟨u, isWalk_append.mpr ⟨u, hp, hγ⟩, isWalk_rev hp⟩, ?_⟩
  rw [hol_append, hol_append, hol_rev, mul_assoc]

/-- [proved-standard; formal-checked] A change of frame moves a step's element by the frames at its two ends. -/
theorem stepElt_regauge (h : V → G) (s : E × Bool) :
    stepElt (regauge Γ h g) s = h (stepTgt Γ s) * stepElt g s * (h (stepSrc Γ s))⁻¹ := by
  obtain ⟨e, _ | _⟩ := s
  · simp only [stepElt, stepTgt, stepSrc, regauge]
    group
  · rfl

/-- [proved-standard; formal-checked] **A change of frame moves a walk's holonomy** to `h(w) hol h(u)⁻¹`. -/
theorem hol_regauge (h : V → G) : ∀ {u w : V} (ws : List (E × Bool)), IsWalk Γ u ws w →
    hol (regauge Γ h g) ws = h w * hol g ws * (h u)⁻¹
  | u, w, [], hw => by
      simp only [IsWalk] at hw
      subst hw
      simp [hol]
  | u, w, s :: ws, hw => by
      obtain ⟨hs, hrest⟩ := hw
      rw [hol, hol, hol_regauge h ws hrest, stepElt_regauge, hs]
      group

/-- [proved-standard; formal-checked] A change of frame `h` carries the keys `x` to `h·x`. -/
theorem isKey_regauge (h : V → G) {x : V → G} :
    IsKey Γ (regauge Γ h g) (fun v => h v * x v) ↔ IsKey Γ g x := by
  refine forall_congr' fun e => ?_
  rw [show regauge Γ h g e * (h (Γ.src e) * x (Γ.src e)) = h (Γ.tgt e) * (g e * x (Γ.src e)) by
    simp only [regauge]; group, mul_right_inj]

/-- [proved-standard; formal-checked] On a commutative carrier a closed walk's holonomy is gauge free. -/
theorem hol_regauge_comm {A : Type*} [CommGroup A] {g : E → A} (h : V → A) {u : V}
    {ws : List (E × Bool)} (hw : IsWalk Γ u ws u) : hol (regauge Γ h g) ws = hol g ws := by
  rw [hol_regauge h ws hw, mul_comm (h u), mul_inv_cancel_right]

end Locate

/-! ## 3. A tree retains nothing to infer, and only the chords decide -/

section Tree

variable {V E G : Type*} [Group G] (Γ : Contacts V E)

/-- [definition] The ports a list of contacts reaches from the base: `v₀` and the contacts' endpoints. -/
def Reached (v₀ : V) (es : List E) (p : V) : Prop :=
  p = v₀ ∨ ∃ e ∈ es, p = Γ.src e ∨ p = Γ.tgt e

/-- [definition] **A growing list**: each contact leaves a port the earlier ones reached for one none reached. -/
def Grows (v₀ : V) (es : List E) : Prop :=
  ∀ pre e suf, es = pre ++ e :: suf → Reached Γ v₀ pre (Γ.src e) ∧ ¬ Reached Γ v₀ pre (Γ.tgt e)

variable {Γ}

/-- [proved-standard; formal-checked] A growing list's prefix grows, and its last contact reaches a new port. -/
theorem Grows.of_append {v₀ : V} {es : List E} {e : E} (h : Grows Γ v₀ (es ++ [e])) :
    Grows Γ v₀ es ∧ Reached Γ v₀ es (Γ.src e) ∧ ¬ Reached Γ v₀ es (Γ.tgt e) :=
  ⟨fun pre e' suf hs => h pre e' (suf ++ [e]) (by rw [hs]; simp), h es e [] rfl⟩

/-- [proved-standard; formal-checked] **Every growing list has a configuration all its contacts transport.** -/
theorem growing_has_keys (g : E → G) (v₀ : V) :
    ∀ es : List E, Grows Γ v₀ es → ∃ x : V → G, ∀ e ∈ es, x (Γ.tgt e) = g e * x (Γ.src e) := by
  intro es
  induction es using List.reverseRecOn with
  | nil => exact fun _ => ⟨fun _ => 1, by simp⟩
  | append_singleton es e ih =>
      intro hg
      classical
      obtain ⟨hg', hsrc, htgt⟩ := hg.of_append
      obtain ⟨x, hx⟩ := ih hg'
      refine ⟨Function.update x (Γ.tgt e) (g e * x (Γ.src e)), fun e' he' => ?_⟩
      have hne : ∀ p, Reached Γ v₀ es p → p ≠ Γ.tgt e := fun p hp hpe => htgt (hpe ▸ hp)
      rcases List.mem_append.mp he' with he' | he'
      · rw [Function.update_of_ne (hne _ (Or.inr ⟨e', he', Or.inr rfl⟩)),
          Function.update_of_ne (hne _ (Or.inr ⟨e', he', Or.inl rfl⟩))]
        exact hx e' he'
      · rw [List.mem_singleton.mp he', Function.update_self, Function.update_of_ne (hne _ hsrc)]

/-- [proved-derived; formal-checked] **A tree retains nothing to infer**: it has keys at every assignment. -/
theorem tree_has_keys {v₀ : V} {es : List E} (hg : Grows Γ v₀ es) (hall : ∀ e, e ∈ es) (g : E → G) :
    ∃ x, IsKey Γ g x := by
  obtain ⟨x, hx⟩ := growing_has_keys g v₀ es hg
  exact ⟨x, fun e => hx e (hall e)⟩

/-- [proved-derived; formal-checked] Every closed walk of a tree closes, whatever its contacts carry. -/
theorem tree_closes {v₀ : V} {es : List E} (hg : Grows Γ v₀ es) (hall : ∀ e, e ∈ es) (g : E → G)
    (u : V) : Closes Γ g u := by
  obtain ⟨x, hx⟩ := tree_has_keys hg hall g
  exact fun ws h => key_closes hx h

/-- [proved-standard; formal-checked] One more contact reaches its two endpoints. -/
theorem reached_append_one {v₀ p : V} {es : List E} {e : E} :
    Reached Γ v₀ (es ++ [e]) p ↔ Reached Γ v₀ es p ∨ p = Γ.src e ∨ p = Γ.tgt e := by
  simp only [Reached, List.mem_append, List.mem_singleton]
  constructor
  · rintro (h | ⟨e', he' | rfl, hp⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨e', he', hp⟩)
    · exact Or.inr hp
  · rintro ((h | ⟨e', he', hp⟩) | hp)
    · exact Or.inl h
    · exact Or.inr ⟨e', Or.inl he', hp⟩
    · exact Or.inr ⟨e, Or.inr rfl, hp⟩

/-- [proved-standard; formal-checked] What a growing list carries is fixed, where it reaches, by the base value. -/
theorem growing_unique {g : E → G} {v₀ : V} :
    ∀ es : List E, Grows Γ v₀ es → ∀ {x y : V → G}, (∀ e ∈ es, x (Γ.tgt e) = g e * x (Γ.src e)) →
      (∀ e ∈ es, y (Γ.tgt e) = g e * y (Γ.src e)) → x v₀ = y v₀ →
        ∀ p, Reached Γ v₀ es p → x p = y p := by
  intro es
  induction es using List.reverseRecOn with
  | nil =>
      intro _ x y _ _ h0 p hp
      rcases hp with rfl | ⟨e, he, _⟩
      · exact h0
      · exact absurd he List.not_mem_nil
  | append_singleton es e ih =>
      intro hg x y hx hy h0 p hp
      obtain ⟨hg', hsrc, _⟩ := hg.of_append
      have ih' := ih hg' (fun e' he' => hx e' (List.mem_append_left _ he'))
        (fun e' he' => hy e' (List.mem_append_left _ he')) h0
      rcases reached_append_one.mp hp with hp | rfl | rfl
      · exact ih' p hp
      · exact ih' _ hsrc
      · rw [hx e (by simp), hy e (by simp), ih' _ hsrc]

/-- [proved-derived; formal-checked] **Only the chords decide**: keys exist iff the tree's reading fits them. -/
theorem tree_reading_decides {g : E → G} {v₀ : V} {es : List E} (hg : Grows Γ v₀ es)
    (hcov : ∀ v, Reached Γ v₀ es v) {xT : V → G} (hT : ∀ e ∈ es, xT (Γ.tgt e) = g e * xT (Γ.src e)) :
    (∃ x, IsKey Γ g x) ↔ ∀ e, e ∉ es → xT (Γ.tgt e) = g e * xT (Γ.src e) := by
  constructor
  · rintro ⟨x, hx⟩ e _
    have hy := isKey_gauge hx ((x v₀)⁻¹ * xT v₀)
    have heq : ∀ p, gauge x ((x v₀)⁻¹ * xT v₀) p = xT p := fun p =>
      growing_unique es hg (fun e' _ => hy e') hT (by simp [gauge]) p (hcov p)
    rw [← heq (Γ.tgt e), ← heq (Γ.src e), hy e]
  · intro hchord
    refine ⟨xT, fun e => ?_⟩
    by_cases he : e ∈ es
    · exact hT e he
    · exact hchord e he

end Tree

/-! ## 4. Phase keys: the circle `ℝ/ℤ` -/

section Phase

variable {V E : Type*} (Γ : Contacts V E)

/-- [definition] **The circle of phases** `ℝ/ℤ`, written multiplicatively as a group of keys. -/
abbrev Phase : Type := Multiplicative (AddCircle (1 : ℝ))

/-- [definition] The phase of a real lift `t`: its class mod `1`. -/
def phase (t : ℝ) : Phase := Multiplicative.ofAdd (t : AddCircle (1 : ℝ))

/-- [definition] **A phase menu**: each contact carries the class of its real offset `ψ_e`. -/
def phaseMenu (ψ : E → ℝ) (e : E) : Phase := phase (ψ e)

/-- [definition] A step's signed offset: `ψ_e` along the contact, `−ψ_e` against it. -/
def offset (ψ : E → ℝ) : E × Bool → ℝ
  | (e, true) => ψ e
  | (e, false) => -ψ e

/-- [definition] **A walk's offset sum**, in `ℝ`: the sum of its steps' signed offsets. -/
def offsetSum (ψ : E → ℝ) : List (E × Bool) → ℝ
  | [] => 0
  | s :: ws => offsetSum ψ ws + offset ψ s

/-- [definition] **The phase cost** of real lifts `θ`: `Σ_e (1 − cos 2π(θ(tgt e) − θ(src e) − ψ_e))`. -/
noncomputable def phaseCost [Fintype E] (ψ : E → ℝ) (θ : V → ℝ) : ℝ :=
  ∑ e, (1 - Real.cos (2 * Real.pi * (θ (Γ.tgt e) - θ (Γ.src e) - ψ e)))

variable {Γ}

/-- [proved-standard; formal-checked] The phase of `0` is the identity. -/
theorem phase_zero : phase 0 = 1 := by simp [phase]

/-- [proved-standard; formal-checked] The phases of real lifts multiply as the lifts add. -/
theorem phase_add (a b : ℝ) : phase (a + b) = phase a * phase b := by
  simp only [phase, AddCircle.coe_add, ofAdd_add]

/-- [proved-standard; formal-checked] The phase of `−a` is the inverse phase. -/
theorem phase_neg (a : ℝ) : phase (-a) = (phase a)⁻¹ := by
  simp only [phase, AddCircle.coe_neg, ofAdd_neg]

/-- [proved-standard; formal-checked] The phase of `a − b` is the quotient of the phases. -/
theorem phase_sub (a b : ℝ) : phase (a - b) = phase a / phase b := by
  rw [sub_eq_add_neg, phase_add, phase_neg, div_eq_mul_inv]

/-- [proved-standard; formal-checked] A real lift has the identity phase exactly when it is an integer. -/
theorem phase_eq_one_iff (t : ℝ) : phase t = 1 ↔ ∃ n : ℤ, t = n := by
  rw [phase, ofAdd_eq_one, AddCircle.coe_eq_zero_iff]
  constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, by simpa [zsmul_eq_mul] using hn.symm⟩

/-- [proved-standard; formal-checked] Every phase has a real lift. -/
theorem phase_surjective : Function.Surjective phase := by
  intro p
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℝ))
    (Multiplicative.toAdd p)
  exact ⟨t, congrArg Multiplicative.ofAdd ht⟩

/-- [proved-standard; formal-checked] Every configuration of phases has real lifts. -/
theorem exists_lift (x : V → Phase) : ∃ θ : V → ℝ, x = fun v => phase (θ v) := by
  choose θ hθ using fun v => phase_surjective (x v)
  exact ⟨θ, funext fun v => (hθ v).symm⟩

/-- [proved-standard; formal-checked] A step of a phase menu carries the phase of its signed offset. -/
theorem stepElt_phaseMenu (ψ : E → ℝ) (s : E × Bool) :
    stepElt (phaseMenu ψ) s = phase (offset ψ s) := by
  obtain ⟨e, _ | _⟩ := s
  · simp only [stepElt, offset, phaseMenu, phase_neg]
  · rfl

/-- [proved-standard; formal-checked] **A walk's phase holonomy is its offset sum mod `1`.** -/
theorem hol_phaseMenu (ψ : E → ℝ) (ws : List (E × Bool)) :
    hol (phaseMenu ψ) ws = phase (offsetSum ψ ws) := by
  induction ws with
  | nil => simp [hol, offsetSum, phase_zero]
  | cons s ws ih => rw [hol, offsetSum, ih, stepElt_phaseMenu, phase_add]

/-- [proved-standard; formal-checked] A walk of a phase menu closes exactly when its offset sum is an integer. -/
theorem phase_closes_iff (ψ : E → ℝ) (ws : List (E × Bool)) :
    hol (phaseMenu ψ) ws = 1 ↔ ∃ n : ℤ, offsetSum ψ ws = n := by
  rw [hol_phaseMenu, phase_eq_one_iff]

/-- [proved-standard; formal-checked] **A connected phase menu has keys exactly when every cycle sum is an integer.** -/
theorem phase_keys_iff {v₀ : V} (hc : Connected Γ v₀) (ψ : E → ℝ) :
    (∃ x, IsKey Γ (phaseMenu ψ) x) ↔ ∀ ws, IsWalk Γ v₀ ws v₀ → ∃ n : ℤ, offsetSum ψ ws = n := by
  rw [exists_key_iff hc]
  simp only [Closes, phase_closes_iff]

/-- [proved-standard; formal-checked] Real lifts are a phase key iff every slip `θ_tgt − θ_src − ψ_e` is in `ℤ`. -/
theorem isKey_phase_iff (ψ : E → ℝ) (θ : V → ℝ) :
    IsKey Γ (phaseMenu ψ) (fun v => phase (θ v)) ↔
      ∀ e, ∃ n : ℤ, θ (Γ.tgt e) - θ (Γ.src e) - ψ e = n := by
  refine forall_congr' fun e => ?_
  rw [← phase_eq_one_iff, phase_sub, phase_sub, phaseMenu, div_div, div_eq_one, mul_comm]

/-- [proved-standard; formal-checked] **Two phase keys of a connected menu differ by one global phase.** -/
theorem phase_key_global_phase {v₀ : V} (hc : Connected Γ v₀) {ψ : E → ℝ} {θ θ' : V → ℝ}
    (hθ : IsKey Γ (phaseMenu ψ) (fun v => phase (θ v)))
    (hθ' : IsKey Γ (phaseMenu ψ) (fun v => phase (θ' v))) :
    ∃ c : ℝ, ∀ v, ∃ n : ℤ, θ' v - θ v - c = n := by
  obtain ⟨k, hk, -⟩ := keys_torsor hc hθ hθ'
  obtain ⟨c, rfl⟩ := phase_surjective k
  refine ⟨c, fun v => ?_⟩
  have hv := congrFun hk v
  simp only [gauge] at hv
  rw [← phase_eq_one_iff, phase_sub, phase_sub, hv, mul_div_right_comm, div_self', one_mul, div_self']

/-- [proved-standard; formal-checked] `1 − cos 2πt` vanishes exactly at the integers. -/
theorem one_sub_cos_eq_zero_iff (t : ℝ) : 1 - Real.cos (2 * Real.pi * t) = 0 ↔ ∃ n : ℤ, t = n := by
  rw [sub_eq_zero, eq_comm, Real.cos_eq_one_iff]
  have h2 : (2 * Real.pi) ≠ 0 := by positivity
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, mul_left_cancel₀ h2 (by linear_combination -hn)⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

variable [Fintype E] {ψ : E → ℝ}

/-- [proved-standard; formal-checked] The phase cost is nonnegative. -/
theorem phaseCost_nonneg (θ : V → ℝ) : 0 ≤ phaseCost Γ ψ θ :=
  Finset.sum_nonneg fun _ _ => sub_nonneg.mpr (Real.cos_le_one _)

/-- [proved-standard; formal-checked] **The phase cost vanishes exactly at the keys.** -/
theorem phaseCost_eq_zero_iff (θ : V → ℝ) :
    phaseCost Γ ψ θ = 0 ↔ IsKey Γ (phaseMenu ψ) (fun v => phase (θ v)) := by
  rw [isKey_phase_iff, phaseCost,
    Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sub_nonneg.mpr (Real.cos_le_one _)]
  simp only [Finset.mem_univ, forall_const, one_sub_cos_eq_zero_iff]

/-- [proved-standard; formal-checked] The phase cost does not read the lifts' integer windings. -/
theorem phaseCost_add_int (θ : V → ℝ) (m : V → ℤ) :
    phaseCost Γ ψ (fun v => θ v + m v) = phaseCost Γ ψ θ := by
  refine Finset.sum_congr rfl fun e _ => ?_
  have h : 2 * Real.pi * (θ (Γ.tgt e) + m (Γ.tgt e) - (θ (Γ.src e) + m (Γ.src e)) - ψ e) =
      2 * Real.pi * (θ (Γ.tgt e) - θ (Γ.src e) - ψ e) +
        ((m (Γ.tgt e) - m (Γ.src e) : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [h, Real.cos_add_int_mul_two_pi]

/-- [proved-standard; formal-checked] **The phase cost is a function on `(ℝ/ℤ)^V`**: two lifts of it cost the same. -/
theorem phaseCost_congr {θ θ' : V → ℝ} (h : ∀ v, phase (θ v) = phase (θ' v)) :
    phaseCost Γ ψ θ = phaseCost Γ ψ θ' := by
  have hm : ∀ v, ∃ n : ℤ, θ' v - θ v = n := fun v => by
    rw [← phase_eq_one_iff, phase_sub, h v, div_self']
  choose m hm using hm
  have : θ' = fun v => θ v + m v := funext fun v => by linarith [hm v]
  rw [this, phaseCost_add_int]

/-- [proved-standard; formal-checked] The phase cost is invariant under the global phase. -/
theorem phaseCost_add_const (θ : V → ℝ) (c : ℝ) :
    phaseCost Γ ψ (fun v => θ v + c) = phaseCost Γ ψ θ := by
  simp only [phaseCost, add_sub_add_right_eq_sub]

end Phase

/-! ### Witnesses: the triangle of phases -/

/-- [definition] **The triangle**: three ports `0 → 1 → 2 → 0`, contact `i` from port `i` to `i + 1`. -/
def triangle : Contacts (Fin 3) (Fin 3) := ⟨fun i => i, fun i => i + 1⟩

/-- [definition] The walk once round the triangle. -/
def roundWalk : List (Fin 3 × Bool) := [(0, true), (1, true), (2, true)]

/-- [proved-derived; formal-checked] The round walk is a closed walk at port `0`. -/
theorem roundWalk_isWalk : IsWalk triangle 0 roundWalk 0 := ⟨rfl, rfl, rfl, rfl⟩

/-- [proved-derived; formal-checked] The triangle is connected from port `0`. -/
theorem triangle_connected : Connected triangle 0 := by
  intro v
  fin_cases v
  · exact ⟨[], rfl⟩
  · exact ⟨[(0, true)], rfl, rfl⟩
  · exact ⟨[(0, true), (1, true)], rfl, rfl, rfl⟩

/-- [proved-derived; formal-checked] Offsets `⅓` round the triangle sum to `1`. -/
theorem third_offsetSum : offsetSum (fun _ : Fin 3 => (1 : ℝ) / 3) roundWalk = 1 := by
  simp only [roundWalk, offsetSum, offset]
  norm_num

/-- [proved-derived; formal-checked] **Offsets `⅓` round the triangle have the key `(0, ⅓, ⅔)`.** -/
theorem third_has_key :
    IsKey triangle (phaseMenu fun _ => (1 : ℝ) / 3) (fun v => phase (![0, 1 / 3, 2 / 3] v)) := by
  rw [isKey_phase_iff]
  intro e
  fin_cases e
  · exact ⟨0, by simp [triangle]⟩
  · exact ⟨0, by simp [triangle]; norm_num⟩
  · exact ⟨-1, by simp [triangle]; norm_num⟩

/-- [proved-derived; formal-checked] Offsets `¼` round the triangle sum to `¾`. -/
theorem quarter_offsetSum : offsetSum (fun _ : Fin 3 => (1 : ℝ) / 4) roundWalk = 3 / 4 := by
  simp only [roundWalk, offsetSum, offset]
  norm_num

/-- [counterexample; formal-checked] **Offsets `¼` round the triangle have no phase key**: `¾` is no integer. -/
theorem quarter_no_key : ¬ ∃ x, IsKey triangle (phaseMenu fun _ => (1 : ℝ) / 4) x := by
  rintro ⟨x, hx⟩
  obtain ⟨n, hn⟩ := (phase_closes_iff _ roundWalk).mp (key_closes hx roundWalk_isWalk)
  rw [quarter_offsetSum] at hn
  have h4 : ((4 * n : ℤ) : ℝ) = 3 := by push_cast; linarith
  have h4' : 4 * n = 3 := by exact_mod_cast h4
  omega

/-- [counterexample; formal-checked] The frustrated triangle's phase cost is positive at every lift. -/
theorem quarter_cost_pos (θ : Fin 3 → ℝ) : 0 < phaseCost triangle (fun _ => (1 : ℝ) / 4) θ :=
  lt_of_le_of_ne (phaseCost_nonneg θ) fun h =>
    quarter_no_key ⟨_, (phaseCost_eq_zero_iff θ).mp h.symm⟩

/-! ## 5. Rotation keys: the rotations of `ℝ³` -/

section Double

variable {V E G : Type*} [Group G] {Γ : Contacts V E} {g : E → G}

/-- [proved-standard; formal-checked] **Two contacts on one pair of ports with different elements leave no key.** -/
theorem double_contact_no_key {e₁ e₂ : E} (hs : Γ.src e₁ = Γ.src e₂) (ht : Γ.tgt e₁ = Γ.tgt e₂)
    (hne : g e₁ ≠ g e₂) : ¬ ∃ x, IsKey Γ g x := by
  rintro ⟨x, hx⟩
  have h1 := hx e₁
  rw [ht, hs, hx e₂] at h1
  exact hne (mul_right_cancel h1).symm

/-- [proved-standard; formal-checked] Their loop, out along one and back against the other, has holonomy `g₂⁻¹ g₁`. -/
theorem double_contact_hol {e₁ e₂ : E} (hs : Γ.src e₁ = Γ.src e₂) (ht : Γ.tgt e₁ = Γ.tgt e₂) :
    IsWalk Γ (Γ.src e₁) [(e₁, true), (e₂, false)] (Γ.src e₁) ∧
      hol g [(e₁, true), (e₂, false)] = (g e₂)⁻¹ * g e₁ := by
  refine ⟨⟨rfl, ht.symm, hs.symm⟩, ?_⟩
  simp [hol, stepElt]

end Double

/-- [definition] **The rotations of `ℝ³`**, `SO(3)`, as Mathlib's special orthogonal group. -/
abbrev Rotation : Type := Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-- [definition] The quarter-turn about `e₃` as a matrix. -/
def quarterTurnMatrix : Matrix (Fin 3) (Fin 3) ℝ := !![0, -1, 0; 1, 0, 0; 0, 0, 1]

/-- [definition] The quarter-turn about `e₁` as a matrix. -/
def quarterTurnXMatrix : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, -1; 0, 1, 0]

/-- [proved-standard; formal-checked] The quarter-turn about `e₃` is orthogonal with determinant `1`. -/
theorem quarterTurnMatrix_mem : quarterTurnMatrix ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [quarterTurnMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [quarterTurnMatrix, Matrix.det_fin_three]

/-- [proved-standard; formal-checked] The quarter-turn about `e₁` is orthogonal with determinant `1`. -/
theorem quarterTurnXMatrix_mem : quarterTurnXMatrix ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [quarterTurnXMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [quarterTurnXMatrix, Matrix.det_fin_three]

/-- [definition] **The quarter-turn about `e₃`**, a rotation. -/
def quarterTurn : Rotation := ⟨quarterTurnMatrix, quarterTurnMatrix_mem⟩

/-- [definition] The quarter-turn about `e₁`, a rotation. -/
def quarterTurnX : Rotation := ⟨quarterTurnXMatrix, quarterTurnXMatrix_mem⟩

/-- [proved-standard; formal-checked] The quarter-turn about `e₃` is not the identity rotation. -/
theorem quarterTurn_ne_one : quarterTurn ≠ 1 := by
  intro h
  have := congrArg (fun A : Rotation => (A : Matrix (Fin 3) (Fin 3) ℝ) 0 0) h
  simp [quarterTurn, quarterTurnMatrix] at this

/-- [proved-standard; formal-checked] **Rotations do not commute**: the quarter-turns about `e₃` and `e₁`. -/
theorem quarterTurns_noncommute : quarterTurn * quarterTurnX ≠ quarterTurnX * quarterTurn := by
  intro h
  have := congrArg (fun A : Rotation => (A : Matrix (Fin 3) (Fin 3) ℝ) 0 2) h
  simp [quarterTurn, quarterTurnX, quarterTurnMatrix, quarterTurnXMatrix] at this

/-- [definition] **The double contact**: two contacts from port `0` to port `1`. -/
def doubleContact : Contacts (Fin 2) (Fin 2) := ⟨fun _ => 0, fun _ => 1⟩

/-- [proved-derived; formal-checked] The double contact is connected from port `0`. -/
theorem doubleContact_connected : Connected doubleContact 0 := by
  intro v
  fin_cases v
  · exact ⟨[], rfl⟩
  · exact ⟨[(0, true)], rfl, rfl⟩

/-- [counterexample; formal-checked] **The double contact carrying `1` and the quarter-turn has no rotation key.** -/
theorem rotation_double_no_key :
    ¬ ∃ x : Fin 2 → Rotation, IsKey doubleContact ![1, quarterTurn] x :=
  double_contact_no_key (e₁ := 0) (e₂ := 1) rfl rfl (by simpa using quarterTurn_ne_one.symm)

/-- [proved-derived; formal-checked] A double contact a true rotation key produced has that key's orbit as keys. -/
theorem rotation_produced_keys (x : Fin 2 → Rotation) :
    {y | IsKey doubleContact (produced doubleContact x) y} = Set.range (gauge x) :=
  produced_keys doubleContact_connected x

/-- [proved-derived; formal-checked] The triangle carrying the quarter-turn on contact `0` has it as holonomy. -/
theorem rotation_round_hol :
    hol (![quarterTurn, 1, 1] : Fin 3 → Rotation) roundWalk = quarterTurn := by
  simp [roundWalk, hol, stepElt]

/-- [counterexample; formal-checked] **A change of frame moves a rotation holonomy**: only its class is gauge free. -/
theorem rotation_regauge_moves_hol :
    hol (regauge triangle (fun _ => quarterTurnX) ![quarterTurn, 1, 1]) roundWalk ≠
      hol (![quarterTurn, 1, 1] : Fin 3 → Rotation) roundWalk := by
  rw [hol_regauge _ roundWalk roundWalk_isWalk, rotation_round_hol]
  intro h
  apply quarterTurns_noncommute
  have := congrArg (· * quarterTurnX) h
  simpa [mul_assoc] using this.symm

/-! ## 6. The frustration of an additive menu vanishes exactly at its keys -/

section Frustration

variable {V E A : Type*} [AddCommGroup A] (Γ : Contacts V E)

/-- [proved-derived; formal-checked] **An additive menu's frustration vanishes exactly when it has a key.** -/
theorem frustration_eq_zero_iff [Fintype E] [DecidableEq A] (w : E → ℕ) (hw : ∀ e, w e ≠ 0)
    (c : E → A) :
    Γ.frustration w c = 0 ↔ ∃ x, IsKey Γ (fun e => Multiplicative.ofAdd (c e)) x := by
  have hcost : ∀ σ : V → A, Γ.cost w c σ = 0 ↔ ∀ e, σ (Γ.tgt e) = σ (Γ.src e) + c e := by
    intro σ
    rw [Contacts.cost, Finset.sum_eq_zero_iff]
    simp only [Finset.mem_univ, true_implies, ite_eq_left_iff]
    exact forall_congr' fun e => ⟨fun h => by_contra fun hn => hw e (h hn), fun h hn => absurd h hn⟩
  have hkey : ∀ σ : V → A, IsKey Γ (fun e => Multiplicative.ofAdd (c e))
      (fun v => Multiplicative.ofAdd (σ v)) ↔ ∀ e, σ (Γ.tgt e) = σ (Γ.src e) + c e := by
    intro σ
    refine forall_congr' fun e => ?_
    rw [← ofAdd_add, Multiplicative.ofAdd.injective.eq_iff, add_comm]
  rw [Contacts.frustration, iInf, Nat.sInf_eq_zero]
  constructor
  · rintro (⟨σ, hσ⟩ | h)
    · exact ⟨_, (hkey σ).mpr ((hcost σ).mp hσ)⟩
    · exact absurd h (Set.range_nonempty _).ne_empty
  · rintro ⟨x, hx⟩
    refine Or.inl ⟨fun v => Multiplicative.toAdd (x v), (hcost _).mpr ((hkey _).mp hx)⟩

end Frustration

end Holonics.HNN.GroupKeys
