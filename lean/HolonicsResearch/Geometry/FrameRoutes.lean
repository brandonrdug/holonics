import Holonics.Aeon.Clock.Groupoid
import Holonics.Foundation.TransportWord
import Holonics.Transport.CellHolonomy
import Holonics.Transport.SerialScrewChain
import HolonicsResearch.Transport.MoveConventions
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Frames joined by declared relations, and the receiver's projections with their rates

A frame is one local chart, joined to other frames by declared invertible relations. A route between
two frames is a chained word of relations, each crossed forward by its map or backward by its
inverse, and two frames are compared by transport along a route. The receiver owns its projection
(a perspective ray, a stereographic chart, an orthographic chart or an isometric chart), read with
its first derivative and refused where its denominator vanishes.

Sources: #410's box "`frame.local-chart-relations`, `frame.receiver-projection` (the motor chart)";
the atlas rows `frame.local-chart-relations` ("a frame is one local chart joined to others by
declared maps; geometry is compared only along a unique route or an explicitly supplied route") and
`frame.receiver-projection` ("projection is a map owned by the receiver; projected rate by the first
derivative; pole/focal-plane crossings are refused rather than differentiated through"), both graded
`definition` with the retired Rust owners alone: `crates/holonics/src/geometry/model.rs` (read at
`d329cb541^`: `LocalChart`, `FrameRelation`, `transport`, which refuses a disconnected pair and
"more than one relation path … an explicit route is required", and `transport_via` along a supplied
route, a relation crossed backwards by its inverse) and `projection.rs` (`ProjectionLaw`,
`project_receiver_point`, `project_receiver_point_rate`, `fiber_statement`; a focal-plane or pole
point is refused); the rows `frame.pullback-naturality`, `frame.cayley-rotations`,
`holonomy.cell-face`, `holonomy.composition-convention`, `holonomy.composes-iff-coboundary`,
`holonomy.block-flat-closed` and `aeon.groupoid`; the open paragraph of `Aeon/Clock/Groupoid`
("Scope: combinatorial words over arbitrary vertex, edge and cell types"), whose words this file
reads in a group, and the scope of `holonomy.composes-iff-coboundary` ("every ordered pair of cells a
contact (a complex with fewer contacts needs its cycle space …)"), which item 2 meets for any group
on any declared relations; the records
`research/records/2026-09-14_THE_RECEIVER_IS_A_PARTICIPATING_HOLON_WITH_MOVING_FACES.md`
("`project_receiver_point_rate` for orthographic, perspective, stereographic and isometric charts")
and
`research/records/2026-09-17_THE_CONTINUING_OBJECT_IS_A_TYPED_COMPUTABLE_TOWER_OF_SITUATED_PRESENTATIONS.md`
§4.1 (a receiver atlas: "a family of local charts with transition maps on overlaps … none of them
the object").

[definition] [proved-standard; formal-checked] [proved-derived; formal-checked] What is proved.

1. **Routes and their transport**, in any group `G`. Frames are the vertices of the owner's
   `ParametricComplex` (`Aeon/Clock/Groupoid`) and relations its edges, with maps `rel : E → G`; a
   route from `a` to `b` is the owner's chained word `Aeon K a b`. A step carries its relation's map
   forward and the inverse backward (`stepMap`, `stepMap_reverseStep`), and a route carries the
   product of its steps in route order (`transport`, `routeTransport`). Transport along a
   concatenation is the composite (`transport_append`, `routeTransport_concat`), along a reversed
   route the inverse (`transport_reverseWord`, `routeTransport_reverse`), along rest the identity
   (`routeTransport_rest`), and along one relation its map (`edgeRoute`, `routeTransport_edgeRoute`).
2. **Routes agree exactly when every holonomy is trivial.** Every two routes with the same ends
   transport alike (`RouteIndependent`) iff every closed route transports by the identity (`Flat`):
   `routeIndependent_iff_flat`. A potential `φ` with `rel e = φ(src e)⁻¹ φ(tgt e)` makes every
   route's transport `φ(a)⁻¹ φ(b)` (`stepMap_of_potential`, `transport_of_potential`,
   `routeTransport_of_potential`, `flat_of_potential`); on frames all reached from one base frame,
   route independence is such a potential (`routeIndependent_iff_potential`), the form of
   `Physics/TwoWayField.composes_iff_coboundary` for declared relations alone. A change of each
   frame's chart, `rel e ↦ k(src)⁻¹ rel e k(tgt)` (the cell owner's `regauge`), conjugates transport
   by the frames at the route's ends (`transport_regauge`) and keeps flatness (`flat_regauge_iff`).
   When each declared cell's boundary transports by `1`, transport is constant on homotopy classes
   (`transport_wordHomotopic`) and is read on the owner's `AeonClass` (`classTransport`).
3. **Conventions and the affine instance.** `G`'s product is read as "then", its first factor
   acting first, as the serial owner's charts compose (`MoveConventions.chart_mul_def`). A group
   that composes right to left is read in its opposite, where transport is the owner's left-to-right
   word (`transport_op`, from `MoveConventions.op_followedByWord`); for permutations transport is
   `Foundation/TransportWord.parallelTransport` of the step word (`transport_perm`). The affine
   instance is `AffineMap3ˣ`, the invertible charts of `Transport/SerialScrewChain` under its ordered
   composition: a relation the retired owner calls singular has no unit, so the type excludes it
   (`translationUnit`).
4. **The triangle and the serial chain.** On three frames with relations `r₀ : 0 → 1`,
   `r₁ : 1 → 2`, `r₂ : 0 → 2` (`triangle`) the closed route `0 → 1 → 2 → 0` transports by the cell
   owner's `triangleHolonomy r₀ r₁ r₂⁻¹` (`triangleLoop_holonomy`), the two routes `0 → 2` by `r₀ r₁`
   and by `r₂` (`twoStepRoute_transport`, `directRoute_transport`), and the triangle is
   route-independent iff `r₀ r₁ = r₂` (`triangle_routeIndependent_iff`). On the serial chain
   `0 → 1 → 2 → ⋯` (`serialChain`), a tree path and the motor chart's route, every route from `a` to
   `b` transports by `φ(a)⁻¹ φ(b)` with `φ(n) = r₀ ⋯ r₍ₙ₋₁₎`, for every choice of relations
   (`chainPotential`, `serialChain_potential`, `serialChain_routeTransport`,
   `serialChain_routeIndependent`): the route is forced.
5. **The receiver's projections over a field.** The perspective ray of focal distance `f`,
   `(x, y, z) ↦ (f x/(f + z), f y/(f + z))` (`perspectiveMap`), is the central projection from the
   focus `(0, 0, −f)` onto the plane `z = 0` (`focus`, `perspective_central`); the stereographic
   chart `(x/(1 − z), y/(1 − z))` (`stereographicMap`) is the ray at `f = −1`, focused at the north
   pole (`northPole`, `stereographicMap_eq_perspectiveMap`); the orthographic chart is `(x, y)`
   (`orthographicMap`). The receiver's `ProjectionLaw.project` refuses (`none`) exactly where the
   law's denominator vanishes (`ProjectionLaw.denom`, `ProjectionLaw.project_eq_none_iff`,
   `ProjectionLaw.project_of_denom_ne_zero`, `orthographic_project`).
6. **Rates by the first derivative**, over `ℝ`. Along a path `(x, y, z)` differentiable at `τ` with
   the denominator nonzero there, the projected path's derivative is the retired owner's rate:
   perspective `f (ẋ (f + z) − x ż)/(f + z)²` in `x` and the same in `y` (`perspectiveRate`,
   `hasDerivAt_perspective`), stereographic `(ẋ (1 − z) + x ż)/(1 − z)²` (`stereographicRate`,
   `stereographicRate_eq_perspectiveRate`, `hasDerivAt_stereographic`), orthographic `(ẋ, ẏ)`
   (`hasDerivAt_orthographic`) and isometric the chart of the rate (`hasDerivAt_isometric`). The
   retired owner's test values `(−3/8, 15/16)` and `(7, 5)` are read over `ℚ` (`retired_rate_values`).
7. **A crossing is refused, not differentiated through.** For `f ≠ 0` and `(x₀, y₀) ≠ 0`, along the
   ray `(x₀, y₀, −f + t)` the norm of the perspective image tends to infinity as `t → 0`
   (`perspective_norm_tendsto_atTop`), so no map continuous at `(x₀, y₀, −f)` agrees with the ray off
   the focal plane (`perspective_no_continuous_extension`); likewise at the stereographic chart's
   pole plane `z = 1` (`stereographic_norm_tendsto_atTop`, `stereographic_no_continuous_extension`)
   and at the north pole along the sphere, where the image's squared length is `(1 + z)/(1 − z)`
   (`stereographic_sq_on_sphere`, `stereographic_unbounded_near_pole`).
8. **Fibres.** For `f ≠ 0` and both denominators nonzero, two points have one perspective image iff
   `q − F = c (p − F)` for some `c ≠ 0`, `F = (0, 0, −f)`: they lie on one line through the focus
   (`perspective_fibre`). The stereographic fibre is a line through the north pole
   (`stereographic_fibre`), the orthographic fibre `p + span{(0, 0, 1)}` (`orthographic_fibre`) and
   the isometric fibre `p + span{(1, 1, 1)}` (`isometric_fibre`).
9. **The sphere and the isometric chart.** Over an ordered field the inverse chart
   `(2u, 2v, u² + v² − 1)/(u² + v² + 1)` lands on the sphere less the north pole, and the two charts
   undo each other there, so the stereographic chart is injective on it (`inverseStereographic`,
   `puncturedSphere`, `inverseStereographic_mem`, `stereographic_inverseStereographic`,
   `inverseStereographic_stereographic`, `stereographic_injOn`). The isometric chart
   `((x − z)/√2, (x + z − 2y)/√6)` (`isometricMap`) scales each source axis by squared length `2/3`
   and pairs two distinct axes at `−1/3` (`isometric_axes`).

[counterexample; formal-checked] **Two routes that disagree.** With each relation of the triangle
the translation by `e₁` in `AffineMap3ˣ` (`shiftRel`), the route through frame `1` carries `2e₁` and
the direct route `e₁`; the closed route's holonomy is not the identity and the triangle is not
route-independent (`shift_routes_disagree`). This is the retired owner's "ambiguous" case with a
holonomy that separates the routes.

What is not claimed. The retired `transport` refuses by counting simple paths, not by reading
holonomy: it refuses a cycle whose holonomy is the identity, where item 2 gives one value along every
route; this file states the law (flatness) and not that combinatorial test. Route independence of
every assignment of relations is proved for the serial chain alone; no general tree theorem is
stated, and a finite chain of frames is not restated apart from it. The local chart's origin, basis,
Gram matrix and orientation (`LocalChart`), the hinge relations and their Cayley rotations
(`frame.cayley-rotations`), the receiver's orientation by spins, its gauge, the moving-frame rate
`L ṗ + L̇ p + ḃ` (`project_point_with_motion`), the conics, the hinges and the crossing diagrams
(`frame.receiver-topology`) are not stated. Continuous paths and the smooth fundamental groupoid
stay outside, as in the owner. Item 7 carries `f ≠ 0`: at `f = 0` the ray is `0` everywhere and
nothing is unbounded. At the focal-plane point `(0, 0, −f)` the image along the axis is `0`, and no
statement is made there. No refusal of the isometric chart is read (it has none), and no jet past the
first derivative is stated.

The computational object is the helical pair interaction read on frames and on the receiver: each
declared relation is a pair contact between two frames, carrying a move from one chart to the other
across it; a route is a word of contacts crossed each way, and the face a closed word reads is its
holonomy, so the frames glue into one chart exactly when every such face is `1` and a nonzero face
obstructs the gluing. The receiver's projection reads a point as a face of its own chart: the rate
is the face's first jet, the fibre (the line through the focus) is the kernel the receiver does not
distinguish, and the refused plane is where the face has no finite value. Of the winding guide's six
general objects this touches the cell holonomy (items 1 to 4), the tower thread (local charts glued
along declared relations, the gluing unique or obstructed by a holonomy), the faces and placement
(items 5 to 9: a receiver's face, its rate and its fibre) and the tube (the serial chain's ordered
transfer between charts); the helix and the pair's modular address stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

open Filter Topology

namespace Holonics.Geometry.FrameRoutes

open Holonics.Aeon.Clock.Groupoid
open Holonics.Transport.CellHolonomy (triangleHolonomy regauge)
open Holonics.Transport.MoveConventions (followedByWord op_followedByWord chart_mul_def)
open Holonics.Transport.SerialScrewChain (AffineMap3 translationChart translationChart_compose)
open Holonics.Foundation.TransportWord (parallelTransport)
open MulOpposite

/-! ## 1. Routes between frames and their transport -/

section Routes

variable {V E F : Type*} {G : Type*} [Group G]

/-- [definition] The map a signed step carries: a relation's map crossed forward, its inverse crossed
backward. -/
def stepMap (rel : E → G) (s : E × Bool) : G := if s.2 then rel s.1 else (rel s.1)⁻¹

/-- [definition] Transport along a word of signed relations: the product of its steps' maps in route
order. -/
def transport (rel : E → G) (w : List (E × Bool)) : G := (w.map (stepMap rel)).prod

variable (rel : E → G)

/-- [proved-standard; formal-checked] The empty word transports by the identity. -/
@[simp] theorem transport_nil : transport rel [] = 1 := rfl

/-- [proved-standard; formal-checked] A word transports by its first step, then the rest. -/
theorem transport_cons (s : E × Bool) (w : List (E × Bool)) :
    transport rel (s :: w) = stepMap rel s * transport rel w := by
  simp [transport]

/-- [proved-standard; formal-checked] Transport along a concatenation is the composite. -/
theorem transport_append (p q : List (E × Bool)) :
    transport rel (p ++ q) = transport rel p * transport rel q := by
  simp [transport]

/-- [proved-standard; formal-checked] A step crossed the other way carries the inverse map. -/
theorem stepMap_reverseStep (s : E × Bool) : stepMap rel (reverseStep s) = (stepMap rel s)⁻¹ := by
  rcases s with ⟨e, _ | _⟩ <;> simp [stepMap, reverseStep]

/-- [proved-standard; formal-checked] Transport along a reversed word is the inverse. -/
theorem transport_reverseWord (w : List (E × Bool)) :
    transport rel (reverseWord w) = (transport rel w)⁻¹ := by
  induction w with
  | nil => simp
  | cons s w ih =>
    rw [reverseWord_cons, transport_append, ih, transport_cons, transport_cons, transport_nil,
      stepMap_reverseStep, mul_one, mul_inv_rev]

variable {K : ParametricComplex V E F}

/-- [definition] Transport along a route of the frame complex: a route from frame `a` to frame `b`
is the owner's chained word of signed relations, `Aeon K a b`. -/
def routeTransport {a b : V} (γ : Aeon K a b) : G := transport rel γ.steps

/-- [proved-standard; formal-checked] The motionless route transports by the identity. -/
@[simp] theorem routeTransport_rest (a : V) : routeTransport rel (Aeon.rest (K := K) a) = 1 := rfl

/-- [proved-standard; formal-checked] Transport along a concatenation of routes is the composite. -/
theorem routeTransport_concat {a b c : V} (γ : Aeon K a b) (δ : Aeon K b c) :
    routeTransport rel (γ.concat δ) = routeTransport rel γ * routeTransport rel δ :=
  transport_append rel _ _

/-- [proved-standard; formal-checked] Transport along a reversed route is the inverse. -/
theorem routeTransport_reverse {a b : V} (γ : Aeon K a b) :
    routeTransport rel γ.reverse = (routeTransport rel γ)⁻¹ :=
  transport_reverseWord rel _

/-- [definition] Route independence: every two routes from one frame to another transport alike. -/
def RouteIndependent (K : ParametricComplex V E F) (rel : E → G) : Prop :=
  ∀ (a b : V) (γ δ : Aeon K a b), routeTransport rel γ = routeTransport rel δ

/-- [definition] Flatness: every closed route's transport, its holonomy, is the identity. -/
def Flat (K : ParametricComplex V E F) (rel : E → G) : Prop :=
  ∀ (a : V) (γ : Aeon K a a), routeTransport rel γ = 1

/-- [proved-standard; formal-checked] **Routes agree exactly when every holonomy is trivial.** -/
theorem routeIndependent_iff_flat : RouteIndependent K rel ↔ Flat K rel := by
  constructor
  · intro h a γ
    exact h a a γ (Aeon.rest a)
  · intro h a b γ δ
    have := h a (γ.concat δ.reverse)
    rw [routeTransport_concat, routeTransport_reverse] at this
    exact mul_inv_eq_one.mp this

/-- [proved-standard; formal-checked] For a potential `φ` with `rel e = φ(src e)⁻¹ φ(tgt e)`, each step
carries `φ(start)⁻¹ φ(finish)`. -/
theorem stepMap_of_potential (φ : V → G) (hφ : ∀ e, rel e = (φ (K.src e))⁻¹ * φ (K.tgt e))
    (s : E × Bool) : stepMap rel s = (φ (K.start s))⁻¹ * φ (K.finish s) := by
  rcases s with ⟨e, _ | _⟩ <;>
    simp [stepMap, ParametricComplex.start, ParametricComplex.finish, hφ]

/-- [proved-standard; formal-checked] A chained word's transport telescopes against a potential. -/
theorem transport_of_potential (φ : V → G) (hφ : ∀ e, rel e = (φ (K.src e))⁻¹ * φ (K.tgt e))
    {a b : V} {w : List (E × Bool)} (hw : K.Chained a w b) :
    transport rel w = (φ a)⁻¹ * φ b := by
  induction w generalizing a with
  | nil =>
    rw [ParametricComplex.chained_nil] at hw
    subst hw
    simp
  | cons s w ih =>
    obtain ⟨h1, h2⟩ := hw
    rw [transport_cons, ih h2, stepMap_of_potential rel φ hφ, h1]
    group

/-- [proved-standard; formal-checked] **A potential makes every route's transport the comparison of
its ends**, `φ(a)⁻¹ φ(b)`. -/
theorem routeTransport_of_potential (φ : V → G)
    (hφ : ∀ e, rel e = (φ (K.src e))⁻¹ * φ (K.tgt e)) {a b : V} (γ : Aeon K a b) :
    routeTransport rel γ = (φ a)⁻¹ * φ b :=
  transport_of_potential rel φ hφ γ.chained

/-- [proved-standard; formal-checked] Relations given by a potential are flat. -/
theorem flat_of_potential (φ : V → G) (hφ : ∀ e, rel e = (φ (K.src e))⁻¹ * φ (K.tgt e)) :
    Flat K rel := by
  intro a γ
  rw [routeTransport_of_potential rel φ hφ, inv_mul_cancel]

/-- [definition] The one-step route along a relation. -/
def edgeRoute (K : ParametricComplex V E F) (e : E) : Aeon K (K.src e) (K.tgt e) :=
  ⟨[(e, true)], by simp [ParametricComplex.start, ParametricComplex.finish]⟩

/-- [proved-standard; formal-checked] The one-step route transports by its relation's map. -/
@[simp] theorem routeTransport_edgeRoute (e : E) : routeTransport rel (edgeRoute K e) = rel e := by
  simp [edgeRoute, routeTransport, transport, stepMap]

/-- [proved-standard; formal-checked] **On frames all reached from one base frame, route independence
is a potential** `rel e = φ(src)⁻¹ φ(tgt)`. -/
theorem routeIndependent_iff_potential (o : V) (hconn : ∀ v, Nonempty (Aeon K o v)) :
    RouteIndependent K rel ↔ ∃ φ : V → G, ∀ e, rel e = (φ (K.src e))⁻¹ * φ (K.tgt e) := by
  constructor
  · intro h
    refine ⟨fun v => routeTransport rel (hconn v).some, fun e => ?_⟩
    have := h o (K.tgt e) ((hconn (K.src e)).some.concat (edgeRoute K e)) (hconn (K.tgt e)).some
    rw [routeTransport_concat, routeTransport_edgeRoute] at this
    show rel e = (routeTransport rel (hconn (K.src e)).some)⁻¹ * routeTransport rel (hconn (K.tgt e)).some
    rw [← this, inv_mul_cancel_left]
  · rintro ⟨φ, hφ⟩
    exact (routeIndependent_iff_flat rel).mpr (flat_of_potential rel φ hφ)

/-- [proved-standard; formal-checked] **A change of each frame's chart conjugates transport** by the
frames at the route's ends, `k(a)⁻¹ T k(b)`. -/
theorem transport_regauge (k : V → G) {a b : V} {w : List (E × Bool)} (hw : K.Chained a w b) :
    transport (fun e => regauge (k (K.src e)) (k (K.tgt e)) (rel e)) w
      = (k a)⁻¹ * transport rel w * k b := by
  induction w generalizing a with
  | nil =>
    rw [ParametricComplex.chained_nil] at hw
    subst hw
    simp
  | cons s w ih =>
    obtain ⟨h1, h2⟩ := hw
    rw [transport_cons, transport_cons, ih h2, ← h1]
    rcases s with ⟨e, _ | _⟩ <;>
      simp only [stepMap, regauge, ParametricComplex.start, ParametricComplex.finish] <;>
      simp only [Bool.false_eq_true, ↓reduceIte, mul_inv_rev, inv_inv] <;> group

/-- [proved-standard; formal-checked] Flatness does not depend on the frames' charts. -/
theorem flat_regauge_iff (k : V → G) :
    Flat K (fun e => regauge (k (K.src e)) (k (K.tgt e)) (rel e)) ↔ Flat K rel := by
  constructor
  · intro h a γ
    have := h a γ
    rw [routeTransport, transport_regauge rel k γ.chained] at this
    have h2 : routeTransport rel γ = k a * ((k a)⁻¹ * transport rel γ.steps * k a) * (k a)⁻¹ := by
      rw [routeTransport]; group
    rw [h2, this]
    group
  · intro h a γ
    rw [routeTransport, transport_regauge rel k γ.chained]
    have := h a γ
    rw [routeTransport] at this
    rw [this]
    group

/-- [proved-standard; formal-checked] **Transport descends to homotopy classes** when every declared
cell's boundary transports by the identity. -/
theorem transport_wordHomotopic (hcell : ∀ f, transport rel (K.boundary f) = 1)
    {p q : List (E × Bool)} (h : WordHomotopic K p q) : transport rel p = transport rel q := by
  induction h with
  | rel x y hxy =>
    cases hxy with
    | backtrack a b s =>
      simp [transport_append, transport_cons, stepMap_reverseStep]
    | face a b f => simp [transport_append, hcell]
    | faceReversed a b f => simp [transport_append, transport_reverseWord, hcell]
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- [definition] Transport read on a homotopy class of routes, for flat declared cells. -/
def classTransport (hcell : ∀ f, transport rel (K.boundary f) = 1) {a b : V} :
    AeonClass K a b → G :=
  Quotient.lift (fun γ : Aeon K a b => routeTransport rel γ)
    (fun _ _ h => transport_wordHomotopic rel hcell h)

/-- [proved-standard; formal-checked] In a group whose product composes right to left, the route
order is read in the opposite group: transport there is the owner's left-to-right word. -/
theorem transport_op (w : List (E × Bool)) :
    transport (fun e => op (rel e)) w = op (followedByWord (w.map (stepMap rel))) := by
  rw [op_followedByWord, List.map_map]
  unfold transport
  congr 1
  apply List.map_congr_left
  intro s _
  rcases s with ⟨e, _ | _⟩ <;> simp [stepMap]

end Routes

/-- [proved-standard; formal-checked] For permutations, transport is the owner's `parallelTransport`
of the step word. -/
theorem transport_perm {E X : Type*} (rel : E → Equiv.Perm X) (w : List (E × Bool)) :
    transport rel w = parallelTransport (w.map (stepMap rel)) := by
  induction w with
  | nil => rfl
  | cons s w ih => rw [transport_cons, ih]; rfl

/-! ## 2. The triangle, the affine instance and the serial chain -/

/-- [definition] The triangle of frames `0, 1, 2` with relations `r₀ : 0 → 1`, `r₁ : 1 → 2`,
`r₂ : 0 → 2` and no declared cell. -/
def triangle : ParametricComplex (Fin 3) (Fin 3) Empty where
  src := ![0, 1, 0]
  tgt := ![1, 2, 2]
  base := Empty.elim
  boundary := Empty.elim

/-- [definition] The one-step route `0 → 1` along `r₀`. -/
def edge01 : Aeon triangle 0 1 := edgeRoute triangle 0

/-- [definition] The one-step route `1 → 2` along `r₁`. -/
def edge12 : Aeon triangle 1 2 := edgeRoute triangle 1

/-- [definition] The direct route `0 → 2` along `r₂`. -/
def directRoute : Aeon triangle 0 2 := edgeRoute triangle 2

/-- [definition] The route `0 → 1 → 2` along `r₀`, then `r₁`. -/
def twoStepRoute : Aeon triangle 0 2 := edge01.concat edge12

/-- [definition] The closed route `0 → 1 → 2 → 0`: `r₀`, `r₁`, then `r₂` crossed backward. -/
def triangleLoop : Aeon triangle 0 0 := twoStepRoute.concat directRoute.reverse

section Triangle

variable {G : Type*} [Group G] (rel : Fin 3 → G)

/-- [proved-standard; formal-checked] The two routes `0 → 2` transport by `r₀ r₁` and by `r₂`. -/
theorem twoStepRoute_transport : routeTransport rel twoStepRoute = rel 0 * rel 1 :=
  (routeTransport_concat rel edge01 edge12).trans
    (congrArg₂ (· * ·) (routeTransport_edgeRoute rel 0) (routeTransport_edgeRoute rel 1))

/-- [proved-standard; formal-checked] The direct route transports by `r₂`. -/
theorem directRoute_transport : routeTransport rel directRoute = rel 2 :=
  routeTransport_edgeRoute rel 2

/-- [proved-standard; formal-checked] The closed route's holonomy is the cell owner's
`triangleHolonomy` of `r₀`, `r₁`, `r₂⁻¹`. -/
theorem triangleLoop_holonomy :
    routeTransport rel triangleLoop = triangleHolonomy (rel 0) (rel 1) (rel 2)⁻¹ := by
  rw [triangleLoop, routeTransport_concat, routeTransport_reverse, twoStepRoute_transport,
    directRoute_transport, triangleHolonomy]

/-- [proved-standard; formal-checked] **The triangle's routes agree exactly when `r₀ r₁ = r₂`**, that is,
when its cell reads `1`. -/
theorem triangle_routeIndependent_iff : RouteIndependent triangle rel ↔ rel 0 * rel 1 = rel 2 := by
  constructor
  · intro h
    have := h 0 2 twoStepRoute directRoute
    rwa [twoStepRoute_transport, directRoute_transport] at this
  · intro h
    apply (routeIndependent_iff_flat rel).mpr
    refine flat_of_potential rel ![1, rel 0, rel 2] ?_
    intro e
    fin_cases e <;> simp [triangle, ← h]

end Triangle

open Holonics.Geometry.ScrewGeometry (Vec)

/-- [definition] The translation chart `x ↦ x + t` as an invertible chart, a unit of the serial
owner's chart monoid under "then". -/
def translationUnit (t : Vec) : AffineMap3ˣ where
  val := translationChart t
  inv := translationChart (-t)
  val_inv := by
    rw [chart_mul_def, translationChart_compose, add_neg_cancel]; rfl
  inv_val := by
    rw [chart_mul_def, translationChart_compose, neg_add_cancel]; rfl

/-- [definition] Every relation of the triangle is the translation by `e₁`. -/
def shiftRel : Fin 3 → AffineMap3ˣ := fun _ => translationUnit ![1, 0, 0]

/-- [counterexample; formal-checked] **Two routes disagree**: the route through frame `1` carries `2e₁`,
the direct route `e₁`, and the closed route's holonomy is not the identity. -/
theorem shift_routes_disagree :
    routeTransport shiftRel twoStepRoute ≠ routeTransport shiftRel directRoute
      ∧ routeTransport shiftRel triangleLoop ≠ 1
      ∧ ¬ RouteIndependent triangle shiftRel := by
  have hne : shiftRel 0 * shiftRel 1 ≠ shiftRel 2 := by
    intro h
    have := congrFun (congrArg (fun u : AffineMap3ˣ => (u : AffineMap3).translation) h) 0
    simp [shiftRel, translationUnit, chart_mul_def, translationChart_compose] at this
    norm_num [translationChart] at this
  refine ⟨?_, ?_, fun h => hne ((triangle_routeIndependent_iff shiftRel).mp h)⟩
  · intro h
    apply hne
    rwa [twoStepRoute_transport, directRoute_transport] at h
  · rw [triangleLoop_holonomy, triangleHolonomy]
    intro h
    apply hne
    rw [mul_inv_eq_one] at h
    exact h

/-- [definition] The serial chain of frames `0 → 1 → 2 → ⋯`: relation `n` joins frame `n` to frame
`n + 1`, a tree path with no declared cell. -/
def serialChain : ParametricComplex ℕ ℕ Empty where
  src := id
  tgt := Nat.succ
  base := Empty.elim
  boundary := Empty.elim

section Serial

variable {G : Type*} [Group G] (rel : ℕ → G)

/-- [definition] The transport from frame `0` to frame `n` along the chain: `r₀ r₁ ⋯ r₍ₙ₋₁₎`. -/
def chainPotential (n : ℕ) : G := ((List.range n).map rel).prod

/-- [proved-standard; formal-checked] Each chain relation is its potential's comparison. -/
theorem serialChain_potential (e : ℕ) :
    rel e = (chainPotential rel (serialChain.src e))⁻¹ * chainPotential rel (serialChain.tgt e) := by
  simp [serialChain, chainPotential, List.range_succ]

/-- [proved-standard; formal-checked] **On a tree path the route is forced**: every route from `a` to
`b` transports by `φ(a)⁻¹ φ(b)`. -/
theorem serialChain_routeTransport {a b : ℕ} (γ : Aeon serialChain a b) :
    routeTransport rel γ = (chainPotential rel a)⁻¹ * chainPotential rel b :=
  routeTransport_of_potential rel (chainPotential rel) (serialChain_potential rel) γ

/-- [proved-standard; formal-checked] The serial chain is route-independent for every choice of
relations. -/
theorem serialChain_routeIndependent : RouteIndependent serialChain rel := fun a b γ δ => by
  rw [serialChain_routeTransport, serialChain_routeTransport]

end Serial

/-! ## 3. The receiver's projections -/

section Projection

variable {𝕜 : Type*} [Field 𝕜]

/-- [definition] The perspective ray of focal distance `f`: `(x, y, z) ↦ (f x/(f + z), f y/(f + z))`,
read where `f + z ≠ 0`. -/
def perspectiveMap (f : 𝕜) (p : 𝕜 × 𝕜 × 𝕜) : 𝕜 × 𝕜 :=
  (f * p.1 / (f + p.2.2), f * p.2.1 / (f + p.2.2))

/-- [definition] Stereographic projection from the north pole: `(x, y, z) ↦ (x/(1 − z), y/(1 − z))`,
read where `z ≠ 1`. -/
def stereographicMap (p : 𝕜 × 𝕜 × 𝕜) : 𝕜 × 𝕜 := (p.1 / (1 - p.2.2), p.2.1 / (1 - p.2.2))

/-- [definition] Orthographic projection: `(x, y, z) ↦ (x, y)`. -/
def orthographicMap (p : 𝕜 × 𝕜 × 𝕜) : 𝕜 × 𝕜 := (p.1, p.2.1)

/-- [definition] The focus of the perspective ray, `(0, 0, −f)`. -/
def focus (f : 𝕜) : 𝕜 × 𝕜 × 𝕜 := (0, 0, -f)

/-- [definition] The receiver's projection laws over a field (the isometric chart, whose
coefficients are `1/√2` and `1/√6`, is read over `ℝ` below). -/
inductive ProjectionLaw (𝕜 : Type*) where
  | orthographic
  | perspective (f : 𝕜)
  | stereographic

/-- [definition] The denominator whose vanishing the receiver refuses: `f + z` for the perspective
ray, `1 − z` for the stereographic chart, and `1` (nothing refused) for the orthographic chart. -/
def ProjectionLaw.denom : ProjectionLaw 𝕜 → 𝕜 × 𝕜 × 𝕜 → 𝕜
  | .orthographic, _ => 1
  | .perspective f, p => f + p.2.2
  | .stereographic, p => 1 - p.2.2

/-- [definition] The receiver's map of each law. -/
def ProjectionLaw.map : ProjectionLaw 𝕜 → 𝕜 × 𝕜 × 𝕜 → 𝕜 × 𝕜
  | .orthographic => orthographicMap
  | .perspective f => perspectiveMap f
  | .stereographic => stereographicMap

/-- [proved-standard; formal-checked] **The perspective ray is the central projection from its focus onto
`z = 0`**: the image `(u, v, 0)` lies on the line through `(0, 0, −f)` and `p`. -/
theorem perspective_central (f : 𝕜) {p : 𝕜 × 𝕜 × 𝕜} (hp : f + p.2.2 ≠ 0) :
    ((perspectiveMap f p).1, (perspectiveMap f p).2, (0 : 𝕜)) - focus f
      = (f / (f + p.2.2)) • (p - focus f) := by
  obtain ⟨px, py, pz⟩ := p
  simp only at hp
  simp only [perspectiveMap, focus, Prod.mk_sub_mk, Prod.smul_mk, smul_eq_mul, sub_zero,
    sub_neg_eq_add, Prod.mk.injEq]
  refine ⟨by ring, by ring, ?_⟩
  rw [div_mul_eq_mul_div, eq_div_iff hp]
  ring

/-- [proved-standard; formal-checked] **The stereographic chart is the perspective ray of focal
distance `−1`**, whose focus is the north pole `(0, 0, 1)`. -/
theorem stereographicMap_eq_perspectiveMap (p : 𝕜 × 𝕜 × 𝕜) :
    stereographicMap p = perspectiveMap (-1) p := by
  unfold stereographicMap perspectiveMap
  rw [show (-1 : 𝕜) + p.2.2 = -(1 - p.2.2) by ring, neg_one_mul, neg_one_mul, neg_div_neg_eq,
    neg_div_neg_eq]

/-- [definition] The perspective rate, the first derivative of the ray at `p` along `v`:
`f (ẋ (f + z) − x ż)/(f + z)²` and the same in `y`. -/
def perspectiveRate (f : 𝕜) (p v : 𝕜 × 𝕜 × 𝕜) : 𝕜 × 𝕜 :=
  (f * (v.1 * (f + p.2.2) - p.1 * v.2.2) / (f + p.2.2) ^ 2,
    f * (v.2.1 * (f + p.2.2) - p.2.1 * v.2.2) / (f + p.2.2) ^ 2)

/-- [definition] The stereographic rate: `(ẋ (1 − z) + x ż)/(1 − z)²` and the same in `y`. -/
def stereographicRate (p v : 𝕜 × 𝕜 × 𝕜) : 𝕜 × 𝕜 :=
  ((v.1 * (1 - p.2.2) + p.1 * v.2.2) / (1 - p.2.2) ^ 2,
    (v.2.1 * (1 - p.2.2) + p.2.1 * v.2.2) / (1 - p.2.2) ^ 2)

/-- [proved-standard; formal-checked] The stereographic rate is the perspective rate at `f = −1`. -/
theorem stereographicRate_eq_perspectiveRate (p v : 𝕜 × 𝕜 × 𝕜) :
    stereographicRate p v = perspectiveRate (-1) p v := by
  unfold stereographicRate perspectiveRate
  congr 1 <;> ring

/-- [proved-standard; formal-checked] **Fibre of the perspective ray**: two points have one image exactly
when they lie on one line through the focus `(0, 0, −f)`. -/
theorem perspective_fibre (f : 𝕜) (hf : f ≠ 0) {p q : 𝕜 × 𝕜 × 𝕜} (hp : f + p.2.2 ≠ 0)
    (hq : f + q.2.2 ≠ 0) :
    perspectiveMap f p = perspectiveMap f q ↔ ∃ c : 𝕜, c ≠ 0 ∧ q - focus f = c • (p - focus f) := by
  obtain ⟨px, py, pz⟩ := p
  obtain ⟨qx, qy, qz⟩ := q
  simp only at hp hq
  simp only [perspectiveMap, focus, Prod.mk.injEq, Prod.mk_sub_mk, Prod.smul_mk, smul_eq_mul,
    sub_zero, sub_neg_eq_add]
  constructor
  · rintro ⟨h1, h2⟩
    rw [div_eq_div_iff hp hq] at h1 h2
    refine ⟨(f + qz) / (f + pz), div_ne_zero hq hp, ?_, ?_, ?_⟩
    · rw [div_mul_eq_mul_div, eq_div_iff hp]
      apply mul_left_cancel₀ hf
      linear_combination -h1
    · rw [div_mul_eq_mul_div, eq_div_iff hp]
      apply mul_left_cancel₀ hf
      linear_combination -h2
    · rw [div_mul_eq_mul_div, eq_div_iff hp]
      ring
  · rintro ⟨c, -, h1, h2, h3⟩
    have hq' : f + qz = c * (f + pz) := by linear_combination h3
    have hc : c * (f + pz) ≠ 0 := hq' ▸ hq
    rw [h1, h2, hq', div_eq_div_iff hp hc, div_eq_div_iff hp hc]
    constructor <;> ring

/-- [definition] The north pole `(0, 0, 1)`, the stereographic chart's focus. -/
def northPole : 𝕜 × 𝕜 × 𝕜 := (0, 0, 1)

/-- [proved-standard; formal-checked] **Fibre of the stereographic chart**: off the pole plane, two
points have one image exactly when they lie on one line through the north pole. -/
theorem stereographic_fibre {p q : 𝕜 × 𝕜 × 𝕜} (hp : p.2.2 ≠ 1) (hq : q.2.2 ≠ 1) :
    stereographicMap p = stereographicMap q ↔
      ∃ c : 𝕜, c ≠ 0 ∧ q - northPole = c • (p - northPole) := by
  have hp' : (-1 : 𝕜) + p.2.2 ≠ 0 := fun h => hp (by linear_combination h)
  have hq' : (-1 : 𝕜) + q.2.2 ≠ 0 := fun h => hq (by linear_combination h)
  rw [stereographicMap_eq_perspectiveMap, stereographicMap_eq_perspectiveMap,
    perspective_fibre (-1) (neg_ne_zero.mpr one_ne_zero) hp' hq']
  simp [focus, northPole]

/-- [proved-standard; formal-checked] **Fibre of the orthographic chart**: the line `p + span{(0, 0, 1)}`. -/
theorem orthographic_fibre (p q : 𝕜 × 𝕜 × 𝕜) :
    orthographicMap p = orthographicMap q ↔ ∃ t : 𝕜, q = p + t • ((0, 0, 1) : 𝕜 × 𝕜 × 𝕜) := by
  obtain ⟨px, py, pz⟩ := p
  obtain ⟨qx, qy, qz⟩ := q
  simp only [orthographicMap, Prod.mk.injEq, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, mul_zero,
    add_zero, mul_one]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨qz - pz, rfl, rfl, by ring⟩
  · rintro ⟨t, h1, h2, -⟩
    exact ⟨h1.symm, h2.symm⟩

variable [DecidableEq 𝕜]

/-- [definition] The receiver's projection: refused (`none`) on the focal plane or the pole plane,
the projected point otherwise. -/
def ProjectionLaw.project (law : ProjectionLaw 𝕜) (p : 𝕜 × 𝕜 × 𝕜) : Option (𝕜 × 𝕜) :=
  if law.denom p = 0 then none else some (law.map p)

/-- [proved-derived; formal-checked] A projection is refused exactly where its denominator vanishes. -/
theorem ProjectionLaw.project_eq_none_iff (law : ProjectionLaw 𝕜) (p : 𝕜 × 𝕜 × 𝕜) :
    law.project p = none ↔ law.denom p = 0 := by
  unfold ProjectionLaw.project
  split_ifs with h <;> simp [h]

/-- [proved-derived; formal-checked] Off the refused plane the receiver returns the law's image. -/
theorem ProjectionLaw.project_of_denom_ne_zero (law : ProjectionLaw 𝕜) {p : 𝕜 × 𝕜 × 𝕜}
    (h : law.denom p ≠ 0) : law.project p = some (law.map p) := by
  simp [ProjectionLaw.project, h]

/-- [proved-derived; formal-checked] The orthographic chart refuses no point. -/
theorem orthographic_project (p : 𝕜 × 𝕜 × 𝕜) :
    (ProjectionLaw.orthographic : ProjectionLaw 𝕜).project p = some (orthographicMap p) := by
  simp [ProjectionLaw.project, ProjectionLaw.denom, ProjectionLaw.map]

end Projection

/-- [proved-derived; formal-checked] The retired owner's test values: rates `(−3/8, 15/16)` (focal distance
`3`, at `(2, 1, 1)`) and `(7, 5)` (stereographic, at `(2, 1, 0)`), both along `(1, 2, 3)`. -/
theorem retired_rate_values :
    perspectiveRate (3 : ℚ) (2, 1, 1) (1, 2, 3) = (-3 / 8, 15 / 16)
      ∧ stereographicRate ((2, 1, 0) : ℚ × ℚ × ℚ) (1, 2, 3) = (7, 5) := by
  constructor <;> norm_num [perspectiveRate, stereographicRate]

section Rates

variable {x y z : ℝ → ℝ} {x' y' z' τ : ℝ}

/-- [proved-standard; formal-checked] **The perspective rate is the first derivative** of the projected
path where `f + z(τ) ≠ 0`. -/
theorem hasDerivAt_perspective (f : ℝ) (hx : HasDerivAt x x' τ) (hy : HasDerivAt y y' τ)
    (hz : HasDerivAt z z' τ) (hd : f + z τ ≠ 0) :
    HasDerivAt (fun t => perspectiveMap f (x t, y t, z t))
      (perspectiveRate f (x τ, y τ, z τ) (x', y', z')) τ := by
  have hden : HasDerivAt (fun t => f + z t) z' τ := hz.const_add f
  have h := ((hx.const_mul f).div hden hd).prodMk ((hy.const_mul f).div hden hd)
  show HasDerivAt (fun t => (f * x t / (f + z t), f * y t / (f + z t))) _ τ
  convert h using 1
  · rfl
  · simp only [perspectiveRate, Prod.mk.injEq]
    constructor <;> ring

/-- [proved-standard; formal-checked] **The stereographic rate is the first derivative** where
`z(τ) ≠ 1`. -/
theorem hasDerivAt_stereographic (hx : HasDerivAt x x' τ) (hy : HasDerivAt y y' τ)
    (hz : HasDerivAt z z' τ) (hd : z τ ≠ 1) :
    HasDerivAt (fun t => stereographicMap (x t, y t, z t))
      (stereographicRate (x τ, y τ, z τ) (x', y', z')) τ := by
  have hd' : (-1 : ℝ) + z τ ≠ 0 := fun h => hd (by linear_combination h)
  simp only [stereographicMap_eq_perspectiveMap, stereographicRate_eq_perspectiveRate]
  exact hasDerivAt_perspective (-1) hx hy hz hd'

/-- [proved-standard; formal-checked] The orthographic rate is `(ẋ, ẏ)`. -/
theorem hasDerivAt_orthographic (hx : HasDerivAt x x' τ) (hy : HasDerivAt y y' τ) :
    HasDerivAt (fun t => orthographicMap (x t, y t, z t)) (x', y') τ :=
  hx.prodMk hy

end Rates

/-! ### A crossing is refused, not differentiated through -/

/-- [proved-standard; formal-checked] **The perspective image is unbounded at the focal plane**: along
`(x₀, y₀, −f + t)` its norm tends to infinity as `t → 0`, `t ≠ 0`. -/
theorem perspective_norm_tendsto_atTop (f x₀ y₀ : ℝ) (hf : f ≠ 0) (hxy : (x₀, y₀) ≠ (0, 0)) :
    Tendsto (fun t : ℝ => ‖perspectiveMap f (x₀, y₀, -f + t)‖) (𝓝[≠] 0) atTop := by
  have key : ∀ t : ℝ, perspectiveMap f (x₀, y₀, -f + t) = (f * x₀ * t⁻¹, f * y₀ * t⁻¹) := by
    intro t
    simp only [perspectiveMap]
    rw [show f + (-f + t) = t by ring, div_eq_mul_inv, div_eq_mul_inv]
  have hinv := tendsto_norm_inv_nhdsNE_zero_atTop (α := ℝ)
  by_cases hx : x₀ = 0
  · have hy : y₀ ≠ 0 := by
      rintro rfl
      exact hxy (by rw [hx])
    have hc : 0 < ‖f * y₀‖ := norm_pos_iff.mpr (mul_ne_zero hf hy)
    refine tendsto_atTop_mono (fun t => ?_) (hinv.const_mul_atTop hc)
    rw [key, ← norm_mul]
    exact norm_snd_le ((f * x₀ * t⁻¹, f * y₀ * t⁻¹) : ℝ × ℝ)
  · have hc : 0 < ‖f * x₀‖ := norm_pos_iff.mpr (mul_ne_zero hf hx)
    refine tendsto_atTop_mono (fun t => ?_) (hinv.const_mul_atTop hc)
    rw [key, ← norm_mul]
    exact norm_fst_le ((f * x₀ * t⁻¹, f * y₀ * t⁻¹) : ℝ × ℝ)

/-- [proved-standard; formal-checked] **No continuous extension across the focal plane** at
`(x₀, y₀, −f)`. -/
theorem perspective_no_continuous_extension (f x₀ y₀ : ℝ) (hf : f ≠ 0) (hxy : (x₀, y₀) ≠ (0, 0)) :
    ¬ ∃ g : ℝ × ℝ × ℝ → ℝ × ℝ, ContinuousAt g (x₀, y₀, -f) ∧
      ∀ p : ℝ × ℝ × ℝ, f + p.2.2 ≠ 0 → g p = perspectiveMap f p := by
  rintro ⟨g, hg, hgp⟩
  have hray : Tendsto (fun t : ℝ => ((x₀, y₀, -f + t) : ℝ × ℝ × ℝ)) (𝓝[≠] 0) (𝓝 (x₀, y₀, -f)) := by
    have hc : Continuous (fun t : ℝ => ((x₀, y₀, -f + t) : ℝ × ℝ × ℝ)) := by fun_prop
    have h0 := hc.tendsto 0
    simp only [add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun t : ℝ => ‖g (x₀, y₀, -f + t)‖) (𝓝[≠] 0) (𝓝 ‖g (x₀, y₀, -f)‖) :=
    (hg.tendsto.comp hray).norm
  have heq : (fun t : ℝ => ‖perspectiveMap f (x₀, y₀, -f + t)‖) =ᶠ[𝓝[≠] 0]
      (fun t : ℝ => ‖g (x₀, y₀, -f + t)‖) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hgp]
    show f + (-f + t) ≠ 0
    rw [show f + (-f + t) = t by ring]
    exact ht
  exact not_tendsto_atTop_of_tendsto_nhds hlim
    ((perspective_norm_tendsto_atTop f x₀ y₀ hf hxy).congr' heq)

/-- [proved-standard; formal-checked] **The stereographic image is unbounded at the pole plane**: along
`(x₀, y₀, 1 + t)` its norm tends to infinity as `t → 0`. -/
theorem stereographic_norm_tendsto_atTop (x₀ y₀ : ℝ) (hxy : (x₀, y₀) ≠ (0, 0)) :
    Tendsto (fun t : ℝ => ‖stereographicMap (x₀, y₀, 1 + t)‖) (𝓝[≠] 0) atTop := by
  have := perspective_norm_tendsto_atTop (-1) x₀ y₀ (by norm_num) hxy
  simpa only [neg_neg, stereographicMap_eq_perspectiveMap] using this

/-- [proved-standard; formal-checked] No continuous extension across the stereographic pole plane. -/
theorem stereographic_no_continuous_extension (x₀ y₀ : ℝ) (hxy : (x₀, y₀) ≠ (0, 0)) :
    ¬ ∃ g : ℝ × ℝ × ℝ → ℝ × ℝ, ContinuousAt g (x₀, y₀, 1) ∧
      ∀ p : ℝ × ℝ × ℝ, p.2.2 ≠ 1 → g p = stereographicMap p := by
  rintro ⟨g, hg, hgp⟩
  refine perspective_no_continuous_extension (-1) x₀ y₀ (by norm_num) hxy ⟨g, ?_, fun p hp => ?_⟩
  · simpa only [neg_neg] using hg
  · rw [hgp p (fun h => hp (by rw [h]; ring)), stereographicMap_eq_perspectiveMap]

/-! ### The unit sphere less the north pole -/

section Sphere

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- [definition] The inverse stereographic chart `(u, v) ↦ (2u, 2v, u² + v² − 1)/(u² + v² + 1)`. -/
def inverseStereographic (w : 𝕜 × 𝕜) : 𝕜 × 𝕜 × 𝕜 :=
  (2 * w.1 / (w.1 ^ 2 + w.2 ^ 2 + 1), 2 * w.2 / (w.1 ^ 2 + w.2 ^ 2 + 1),
    (w.1 ^ 2 + w.2 ^ 2 - 1) / (w.1 ^ 2 + w.2 ^ 2 + 1))

/-- [definition] The unit sphere less the north pole. -/
def puncturedSphere : Set (𝕜 × 𝕜 × 𝕜) := {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = 1 ∧ p.2.2 ≠ 1}

/-- [proved-standard; formal-checked] On the sphere the stereographic image has squared length
`(1 + z)/(1 − z)`. -/
theorem stereographic_sq_on_sphere {p : 𝕜 × 𝕜 × 𝕜} (hs : p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = 1)
    (hz : p.2.2 ≠ 1) :
    (stereographicMap p).1 ^ 2 + (stereographicMap p).2 ^ 2 = (1 + p.2.2) / (1 - p.2.2) := by
  have h1 : (1 : 𝕜) - p.2.2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  simp only [stereographicMap]
  rw [div_pow, div_pow, ← add_div, show p.1 ^ 2 + p.2.1 ^ 2 = (1 - p.2.2) * (1 + p.2.2) by
    linear_combination hs]
  field_simp

/-- [proved-standard; formal-checked] The inverse chart lands on the sphere less the north pole. -/
theorem inverseStereographic_mem (w : 𝕜 × 𝕜) : inverseStereographic w ∈ puncturedSphere := by
  have hs : w.1 ^ 2 + w.2 ^ 2 + 1 ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · simp only [inverseStereographic]
    field_simp
    ring
  · simp only [inverseStereographic]
    rw [Ne, div_eq_one_iff_eq hs]
    intro h
    linarith

/-- [proved-standard; formal-checked] The stereographic chart undoes the inverse chart. -/
theorem stereographic_inverseStereographic (w : 𝕜 × 𝕜) :
    stereographicMap (inverseStereographic w) = w := by
  have hs : w.1 ^ 2 + w.2 ^ 2 + 1 ≠ 0 := by positivity
  have h1 : 1 - (w.1 ^ 2 + w.2 ^ 2 - 1) / (w.1 ^ 2 + w.2 ^ 2 + 1) = 2 / (w.1 ^ 2 + w.2 ^ 2 + 1) := by
    field_simp
    ring
  simp only [stereographicMap, inverseStereographic, h1]
  field_simp

/-- [proved-standard; formal-checked] The inverse chart undoes the stereographic chart on the sphere
less the north pole. -/
theorem inverseStereographic_stereographic {p : 𝕜 × 𝕜 × 𝕜} (hp : p ∈ puncturedSphere) :
    inverseStereographic (stereographicMap p) = p := by
  obtain ⟨hs, hz⟩ := hp
  have h1 : (1 : 𝕜) - p.2.2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hsq := stereographic_sq_on_sphere hs hz
  have h2 : (1 + p.2.2) / (1 - p.2.2) + 1 = 2 / (1 - p.2.2) := by
    field_simp
    ring
  have h3 : (1 + p.2.2) / (1 - p.2.2) - 1 = 2 * p.2.2 / (1 - p.2.2) := by
    field_simp
    ring
  simp only [inverseStereographic]
  rw [hsq, h2, h3]
  obtain ⟨px, py, pz⟩ := p
  simp only [stereographicMap] at h1 ⊢
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp

/-- [proved-standard; formal-checked] **Stereographic projection is injective on the sphere less the
north pole**, with the rational inverse `inverseStereographic`. -/
theorem stereographic_injOn : Set.InjOn stereographicMap (puncturedSphere : Set (𝕜 × 𝕜 × 𝕜)) := by
  intro p hp q hq h
  rw [← inverseStereographic_stereographic hp, h, inverseStereographic_stereographic hq]

/-- [proved-standard; formal-checked] **The image is unbounded near the north pole**: every bound is
passed on a cap `1 − δ < z < 1` of the sphere. -/
theorem stereographic_unbounded_near_pole (B : 𝕜) :
    ∃ δ : 𝕜, 0 < δ ∧ ∀ p : 𝕜 × 𝕜 × 𝕜, p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = 1 → 1 - δ < p.2.2 →
      p.2.2 < 1 → B < (stereographicMap p).1 ^ 2 + (stereographicMap p).2 ^ 2 := by
  have hB : 0 < |B| + 1 := by positivity
  refine ⟨1 / (|B| + 1), by positivity, fun p hs hlo hhi => ?_⟩
  rw [stereographic_sq_on_sphere hs hhi.ne]
  have hδ : 1 / (|B| + 1) ≤ 1 := by
    rw [div_le_one hB]
    linarith [abs_nonneg B]
  have hz0 : 0 ≤ p.2.2 := by linarith
  have hpos : 0 < 1 - p.2.2 := by linarith
  have hlt : 1 - p.2.2 < 1 / (|B| + 1) := by linarith
  have key : |B| + 1 < 1 / (1 - p.2.2) := by
    rw [lt_div_iff₀ hpos]
    rw [lt_div_iff₀ hB] at hlt
    nlinarith [abs_nonneg B]
  have hle : 1 / (1 - p.2.2) ≤ (1 + p.2.2) / (1 - p.2.2) :=
    div_le_div_of_nonneg_right (by linarith) hpos.le
  linarith [le_abs_self B]

end Sphere

/-! ### The isometric chart -/

/-- [definition] The isometric chart `(x, y, z) ↦ ((x − z)/√2, (x + z − 2y)/√6)`. -/
noncomputable def isometricMap (p : ℝ × ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 - p.2.2) / √2, (p.1 + p.2.2 - 2 * p.2.1) / √6)

/-- [proved-standard; formal-checked] **The isometric chart scales each source axis by squared length
`2/3`**, and pairs two distinct axes at `−1/3`. -/
theorem isometric_axes :
    (isometricMap (1, 0, 0)).1 ^ 2 + (isometricMap (1, 0, 0)).2 ^ 2 = 2 / 3
      ∧ (isometricMap (0, 1, 0)).1 ^ 2 + (isometricMap (0, 1, 0)).2 ^ 2 = 2 / 3
      ∧ (isometricMap (0, 0, 1)).1 ^ 2 + (isometricMap (0, 0, 1)).2 ^ 2 = 2 / 3
      ∧ (isometricMap (1, 0, 0)).1 * (isometricMap (0, 1, 0)).1
          + (isometricMap (1, 0, 0)).2 * (isometricMap (0, 1, 0)).2 = -1 / 3
      ∧ (isometricMap (1, 0, 0)).1 * (isometricMap (0, 0, 1)).1
          + (isometricMap (1, 0, 0)).2 * (isometricMap (0, 0, 1)).2 = -1 / 3
      ∧ (isometricMap (0, 1, 0)).1 * (isometricMap (0, 0, 1)).1
          + (isometricMap (0, 1, 0)).2 * (isometricMap (0, 0, 1)).2 = -1 / 3 := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h2' : √2 ≠ 0 := by positivity
  have h6' : √6 ≠ 0 := by positivity
  simp only [isometricMap]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> rw [h2, h6] <;> norm_num

/-- [proved-standard; formal-checked] **Fibre of the isometric chart**: the line `p + span{(1, 1, 1)}`. -/
theorem isometric_fibre (p q : ℝ × ℝ × ℝ) :
    isometricMap p = isometricMap q ↔ ∃ t : ℝ, q = p + t • ((1, 1, 1) : ℝ × ℝ × ℝ) := by
  have h2' : √2 ≠ 0 := by positivity
  have h6' : √6 ≠ 0 := by positivity
  obtain ⟨px, py, pz⟩ := p
  obtain ⟨qx, qy, qz⟩ := q
  simp only [isometricMap, Prod.mk.injEq, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, mul_one,
    div_left_inj' h2', div_left_inj' h6']
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨qx - px, by ring, by linarith, by linarith⟩
  · rintro ⟨t, h1, h2, h3⟩
    subst h1 h2 h3
    constructor <;> ring

/-- [proved-standard; formal-checked] The isometric rate is the chart applied to the rate. -/
theorem hasDerivAt_isometric {x y z : ℝ → ℝ} {x' y' z' τ : ℝ} (hx : HasDerivAt x x' τ)
    (hy : HasDerivAt y y' τ) (hz : HasDerivAt z z' τ) :
    HasDerivAt (fun t => isometricMap (x t, y t, z t)) (isometricMap (x', y', z')) τ :=
  ((hx.sub hz).div_const √2).prodMk (((hx.add hz).sub (hy.const_mul 2)).div_const √6)

end Holonics.Geometry.FrameRoutes
