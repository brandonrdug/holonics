import Holonics.Geometry.Motion
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Data.Set.Card
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The chase consumer: the move pair, capture and viability, the phase lock, the expected capture and the grain

[proved-derived; formal-checked] The source is #410's box on the chase consumer
(`holarchy::terrain::chase`): "the move pair `(v, v′)`; capture and viability recursions on a finite
terrain; phase viability `φ̇ = δ − K sin φ`; the … expected-capture recursion `(U, S, W)`; a finer
grain never raises the least capture". The retired owner of these laws is the October library's
`holarchy::terrain::pursuit` (held at `d5ed4adc1`, beside the terrain `holarchy::terrain::chase`
and the move `geometry::motion::Move`), whose open paragraph reads the chase's action phase as "the
chaser moves, and cornering is read as the runner's robust viability kernel": the capture reach,
the runner's viable tube, the capture basin over a fibre of candidates and its expected reading,
and the chaser's move set as a declared variant with the truth-only least capture under it. The
records are `2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_…` (§6, §13 and §14.4) and
`2026-09-28_THE_OPTIMAL_POLICY_IS_THE_GEODESIC_NAVIGATOR_THE_CHASE_IS_RETROGRADE_ANALYSIS_…` (§1 and
§2: the capture basin is retrograde analysis, and the distances depend on which moves are
elementary). Atlas rows served: `motion.move-pair`, `motion.traction-disk` (on the lattice, through
`Geometry/Motion`), `pursuit.capture-viability-recursions`, `pursuit.capture-basin-fibre` (its
one-step recursion, on one candidate), `pursuit.viable-tube` (the recursion it specializes),
`pursuit.capture-is-not-lock`, `pursuit.constant-bearing-lock`, `lock.phase-viability`,
`pursuit.expected-capture` and `pursuit.move-set`.

What is proved.

1. [proved-derived; formal-checked] **The move pair on `ℤ[i]`** (`MovePair`, its `change` and
   `ratio`; `dot`, `det`, `quadrance`). The pairing's faces are the power and the signed turn,
   `v̄·w = ⟨v, w⟩ + i·det(v, w)` (`pairing_faces`); `|v′|² − |v|² = 2⟨v, Δv⟩ + |Δv|²`
   (`quadrance_after_sub_before`). For `v ≠ 0` and `k = v′/v`: `v̄·Δv = |v|²(k − 1)`
   (`pairing_is_ratio`) and the traction disk `|Δv|² = |k − 1|²|v|²` (`traction_disk_lattice`,
   consuming `Motion.traction_move_ratio`). The traction test reads the floored bound
   (`traction_floor`) and the change alone (`change_shift`). The kinds are decided on the integers:
   the turn `2⟨v, Δv⟩ + |Δv|² = 0 ⇔ |k| = 1`, with `|Δv|² = (2 − 2 Re k)|v|²` there (`turn_test`,
   consuming `Motion.turn_distance_from_one`); the boost `det(v, Δv) = 0 ∧ |v|² + ⟨v, Δv⟩ > 0 ⇔ k`
   real and positive (`boost_test`); free fall `Δv = 0 ⇔ k = 1` and the stop `v′ = 0 ⇔ k = 0`
   (`fall_and_stop_test`).
2. [proved-standard; formal-checked] **Capture and viability on a finite terrain.** With the robust
   predecessor `Pre S = {z | ∃ u, ∀ w, T z u w ∈ S}` (`Pre`, monotone: `pre_mono`), the capture
   basins `C₀ = target`, `C_(n+1) = C_n ∪ Pre C_n` (`captureBasin`) increase
   (`captureBasin_mono`) and stand from `|Z|` ticks on (`captureBasin_stands`, through the chain
   lemmas `chain_stands`, `chain_repeats`, `chain_stands_by`); their union is `C_|Z|`
   (`iUnion_captureBasin`), the least set over the target closed under `Pre`
   (`captureBasin_isLeast`) and a fixed point `target ∪ Pre C = C` (`captureBasin_fixed`). The
   viability kernels `K_(n+1) = K_n ∩ Pre K_n` (`viabilityKernel`) decrease
   (`viabilityKernel_anti`), stand from `|Z|` ticks on (`viabilityKernel_stands`,
   `iInter_viabilityKernel`), and the limit is the largest `S ⊆ K₀` with `S ⊆ Pre S`
   (`viabilityKernel_isGreatest`, `viabilityKernel_fixed`): membership promises a next viable move,
   not capture (`viabilityKernel_next_move`). The complement of the robust predecessor is the dual
   predecessor `{z | ∀ u, ∃ w, …}` of the complement (`compl_pre`), so the states not captured
   within `n` ticks are the dual kernel of the target's complement (`compl_captureBasin`): the
   barrier. The admitted-move form (a mover that can always stop, a replier that always has a
   reply) is this `Pre` read through a total transition (`admitted`, `pre_admitted`).
3. [proved-standard; formal-checked] **The least capture time** (`leastCapture`, in `ℕ∞`) reads
   the basins, `τ z ≤ n ⇔ z ∈ C_n` (`leastCapture_le_iff`); it is `0` on the target
   (`leastCapture_target`) and off it satisfies the one-step recursion of retrograde analysis
   `τ z = 1 + min_u max_w τ (T z u w)` (`leastCapture_step`, through `mem_captureBasin_succ`); on a
   finite terrain it is finite on `C_|Z|` and only there, and then at most `|Z|`
   (`leastCapture_lt_top_iff`).
4. [proved-derived; formal-checked] **Capture is not lock; the bearing's lock.** On the lattice tick
   `r_(t+1) = r_t + ṙ_t`, zero relative velocity keeps a pair outside the capture disk forever
   (`capture_is_not_lock`) and a capture crossing has nonzero relative velocity
   (`capture_crossing_moves`); in an open arena a runner moving straight away, `⟨r₀, d⟩ ≥ 0`, never
   comes nearer (`open_arena_escape`). Along a differentiable displacement off the cut,
   `d/dt arg r = det(r, ṙ)/|r|²` (`bearing_rate`) and `d/dt ⟨r, r⟩ = 2⟨r, ṙ⟩` (`quadrance_rate`):
   constant bearing nulls the first and permits radial slip, and approach needs `⟨r, ṙ⟩ < 0`.
5. [proved-standard; formal-checked] **Phase viability, Adler's equation** `φ̇ = δ − K sin φ`
   (`adlerRate`, of slope `−K cos φ`: `hasDerivAt_adlerRate`). For `K > 0` a rest point exists iff
   `|δ| ≤ K` (`adler_rest_iff`). Inside the tongue, `|δ| < K`, the rest points are
   `arcsin(δ/K) + 2πn` (stable, `K cos φ* > 0`) and `π − arcsin(δ/K) + 2πn` (unstable,
   `K cos φ* < 0`), two in each turn (`adler_two_rest_points`, `stablePhase`, `unstablePhase`); at
   the edge `|δ| = K` a rest point has `cos φ* = 0`, the saddle-node (`adler_edge`). Outside,
   `|δ| > K`, the rate never vanishes and keeps the sign of `δ`, with `|φ̇| ≥ |δ| − K`
   (`adler_no_rest`), so a solution is strictly monotone and slips at least `(|δ| − K)` a unit of
   time through every turn (`adler_slip`, `adler_slip_neg`): the lock is lost. With bounded control
   `|u| ≤ U` and disturbance `|w| ≤ d`, an interval's ends admit robust inward control iff
   `F(a) + U − d ≥ 0` and `F(b) − U + d ≤ 0` (`phase_inward`): `Pre`'s quantifiers at the ends.
6. [proved-derived; formal-checked] **The expected-capture triple** (`ExpectedCapture`: members
   uncaptured `U`, the captured members' tick sum `S`, their greatest tick `W`). Its sum
   `(U, S, W) ⊕ (U′, S′, W′) = (U + U′, S + S′, max(W, W′))` is associative and commutative with
   unit `(0, 0, 0)` (`plus_assoc`, `plus_comm`, `zero_plus`; the `AddCommMonoid` instance). The shift
   by one tick for a class of `n`, `shift(U, S, W) = (U, S + (n − U), W + 1 if U < n else 0)`
   (`shift`), keeps a class's readings (`Fits`, `fits_plus`, `fits_shift`) and distributes over
   `⊕`, `shift_(n+n′)(a ⊕ b) = shift_n a ⊕ shift_n′ b` (`shift_plus`, and over many classes
   `shift_sum`). Under a fixed strategy a fibre's reading (`reading`) is `(0, b, b)` for a member
   captured at `b` and `(1, 0, 0)` for one not captured (`reading_singleton`); the reading of a union
   of disjoint fibres is the `⊕` of their readings (`reading_union`, `reading_empty`), so a fibre
   reads the `⊕` of its members (`reading_eq_sum`); the shift is the reading of the ticks one later
   (`reading_shift`); readings fit their class (`fits_singleton`, `reading_fits`); and `U = 0`
   when and only when every member is captured (`reading_uncaptured_eq_zero`). In the
   lexicographic order (`key`, `le_iff`) `⊕` and the shift are monotone (`plus_le_plus_right`,
   `shift_le_shift`), so the least `⊕` of two independent classes' choices is the `⊕` of their
   leasts (`isLeast_plus`): the recursion's step is an equality, not a bound.
7. [proved-derived; formal-checked] **A finer grain never raises the least capture.** If the coarse
   states and moves embed into the fine terrain (`e`, `ι`), capture is read alike, and every fine
   reply to an embedded move is the embedding of a coarse reply, the coarse basins embed level by
   level (`finer_grain_basin`) and `τ_f (e z) ≤ τ_c z` (`finer_grain_least_capture`); on one terrain
   more moves never raise it (`more_moves_least_capture`). The lattice's embedding `g ↦ kg` meets
   these hypotheses' bounds: `k²⌊b⌋ ≤ ⌊k²b⌋` (`grain_floor_scale`), `⟨kV, kV⟩ = k²⟨V, V⟩`
   (`quadrance_scale`), every floored quadrance bound is kept (`grain_bound_scale`), the cell and
   the walls are kept (`grain_cell_scale`), and the move's change and its kind's integer tests
   scale (`grain_move_scale`).

What is not claimed. No terrain is built: the arena, the friction field, the runner's navigator
and slip law, the chaser's port and the controls stay the retired owner's, and the hypothesis of
item 7 that the runner reads an embedded chaser alike at every grain (the plane's law,
`Runner::cell_at_grain`) is carried, never derived; "finer" means a grain `kg` with `k ≥ 1`, whose
lattice holds the coarse one (`(1/2)ℤ` does not lie in `(1/3)ℤ`). The time-expanded viable tube
(`K_k = F_k ∩ Pre K_(k+1)`) is the stationary recursion on the state `(r, k)` and is not restated;
the capture reach and the observation classes of a fibre are not built, so the expected-capture
recursion's value over adaptive strategies is not formed here, only its algebra (the triple, `⊕`,
the shift, the reading of a fibre and the monotonicity that makes the step an equality). Membership
in a basin is a game value under the order "the mover commits, then the reply": no strategy object,
no partial observation and no continuous Hamilton–Jacobi–Isaacs reading enter. Adler's equation is
read through its rate: no solution is constructed, and the tongue's scaling and the Stern–Brocot
code are not joined. Every bound is a stated integer, rational or real; no width or register is
declared.

The computational object is the helical pair interaction read on the chase: the runner and the
chaser are a pair whose contact quadrance `Q = ⟨r, r⟩` the chaser closes, capture is a receiver set
on that quadrance, and the move pair is the pairing `v̄·Δv`, whose real face is the power (the
boost) and whose imaginary face is the signed turn. Of the winding guide's six general objects this
touches five: the **helix** (Adler's phase on its circle, which outside the tongue slips through
every turn: circle plus carry), the **pair** (the contact's quadrance, capture, the bearing's lock
and the pairing's faces), **faces and placement** (the floored lattice bounds and the grain's
embedding), the **tube** (the basins and kernels tick by tick, and the shift by one tick) and the
**tower thread** (a fibre split into disjoint classes, read as the `⊕` of its parts, and the
restriction between grains). The **cell holonomy** (the three channels' loop closure of
`holarchy::terrain::sensing`) stays attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Geometry.ChaseConsumer

open Complex

/-! ## 1. The move pair on the lattice -/

section Moves

/-- [definition] **The move pair**: a mover's velocity before and after one tick on the lattice
`ℤ[i]`, carried undivided (never as its ratio). -/
structure MovePair where
  before : GaussianInt
  after : GaussianInt

namespace MovePair

/-- [definition] The velocity change `Δv = v′ − v`. -/
def change (m : MovePair) : GaussianInt := m.after - m.before

/-- [definition] The move ratio `k = v′/v` read in the complex chart (meaningful for `v ≠ 0`). -/
noncomputable def ratio (m : MovePair) : ℂ :=
  GaussianInt.toComplex m.after / GaussianInt.toComplex m.before

end MovePair

/-- [definition] The pairing's real face `⟨a, b⟩`: the power, the effort along the motion. -/
def dot (a b : GaussianInt) : ℤ := a.re * b.re + a.im * b.im

/-- [definition] The pairing's imaginary face `det(a, b)`: the signed turn, the effort across. -/
def det (a b : GaussianInt) : ℤ := a.re * b.im - a.im * b.re

/-- [definition] The quadrance `⟨a, a⟩`. -/
def quadrance (a : GaussianInt) : ℤ := dot a a

/-- [proved-standard; formal-checked] **The pairing's two faces:** `v̄·w = ⟨v, w⟩ + i·det(v, w)`,
the power and the signed turn. -/
theorem pairing_faces (v w : GaussianInt) :
    (star v * w).re = dot v w ∧ (star v * w).im = det v w := by
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star, dot, det]
  constructor <;> ring

/-- [proved-standard; formal-checked] **The energy change of a move:**
`|v′|² − |v|² = 2⟨v, Δv⟩ + |Δv|²`. -/
theorem quadrance_after_sub_before (m : MovePair) :
    quadrance m.after - quadrance m.before = 2 * dot m.before m.change + quadrance m.change := by
  simp only [quadrance, dot, MovePair.change, Zsqrtd.re_sub, Zsqrtd.im_sub]
  ring

/-- [proved-standard; formal-checked] The quadrance is the lattice norm of `ℤ[i]`. -/
theorem quadrance_eq_norm (a : GaussianInt) : quadrance a = a.norm := by
  rw [quadrance, dot, Zsqrtd.norm_def]
  ring

/-- [proved-standard; formal-checked] The quadrance is the complex chart's `normSq`. -/
theorem quadrance_cast (a : GaussianInt) :
    ((quadrance a : ℤ) : ℝ) = normSq (GaussianInt.toComplex a) := by
  rw [quadrance_eq_norm]
  exact GaussianInt.intCast_real_norm a

/-- [proved-standard; formal-checked] The chart keeps a nonzero lattice velocity nonzero. -/
theorem toComplex_ne_zero {a : GaussianInt} (ha : a ≠ 0) : GaussianInt.toComplex a ≠ 0 := by
  intro h
  exact ha (GaussianInt.toComplex_injective (by rw [h, map_zero]))

/-- [proved-derived; formal-checked] **The pairing is the move ratio's distance from one, scaled:**
for `v ≠ 0`, `v̄·Δv = |v|²(k − 1)` in the complex chart. -/
theorem pairing_is_ratio (m : MovePair) (hv : m.before ≠ 0) :
    GaussianInt.toComplex (star m.before * m.change) =
      (normSq (GaussianInt.toComplex m.before) : ℂ) * (m.ratio - 1) := by
  have h0 := toComplex_ne_zero hv
  rw [map_mul, GaussianInt.toComplex_star, MovePair.change, map_sub, MovePair.ratio,
    ← mul_conj, mul_comm (GaussianInt.toComplex m.before)]
  field_simp

/-- [proved-derived; formal-checked] **The traction disk on the lattice** (consuming
`Geometry/Motion.traction_move_ratio`): for `v ≠ 0`, `|Δv|² = |k − 1|²|v|²`, so the bound
`|Δv|² ≤ r²` is a disk of admitted move ratios about `1` that shrinks as the speed grows. -/
theorem traction_disk_lattice (m : MovePair) (hv : m.before ≠ 0) :
    ((quadrance m.change : ℤ) : ℝ) = normSq (m.ratio - 1) * ((quadrance m.before : ℤ) : ℝ) := by
  rw [quadrance_cast, quadrance_cast, MovePair.change, map_sub, MovePair.ratio]
  exact Holonics.Geometry.Motion.traction_move_ratio (toComplex_ne_zero hv) _

/-- [proved-standard; formal-checked] **The lattice traction test needs no division:** an integer
quadrance meets a declared bound `b` when and only when it meets `⌊b⌋`. -/
theorem traction_floor {α : Type*} [Ring α] [LinearOrder α] [FloorRing α] (q : ℤ) (b : α) :
    q ≤ ⌊b⌋ ↔ (q : α) ≤ b :=
  Int.le_floor

/-- [proved-standard; formal-checked] The move's change is unchanged by a common shift of both
velocities, `(v, v′) ↦ (v + u, v′ + u)`: the traction test reads the change alone. -/
theorem change_shift (m : MovePair) (u : GaussianInt) :
    (MovePair.mk (m.before + u) (m.after + u)).change = m.change := by
  simp only [MovePair.change, add_sub_add_right_eq_sub]

/-- [proved-derived; formal-checked] **A lattice turn, decided on the integers:** for `v ≠ 0`,
`2⟨v, Δv⟩ + |Δv|² = 0` when and only when `|k| = 1`, and then (consuming
`Geometry/Motion.turn_distance_from_one`) `|Δv|² = (2 − 2 Re k)|v|²`. -/
theorem turn_test (m : MovePair) (hv : m.before ≠ 0) :
    (2 * dot m.before m.change + quadrance m.change = 0 ↔ normSq m.ratio = 1) ∧
      (normSq m.ratio = 1 →
        ((quadrance m.change : ℤ) : ℝ) = (2 - 2 * m.ratio.re) * ((quadrance m.before : ℤ) : ℝ)) := by
  have h0 := toComplex_ne_zero hv
  have hpos : 0 < normSq (GaussianInt.toComplex m.before) := normSq_pos.mpr h0
  have hq : ((quadrance m.after : ℤ) : ℝ) = normSq m.ratio * ((quadrance m.before : ℤ) : ℝ) := by
    rw [quadrance_cast, quadrance_cast, MovePair.ratio, normSq_div]
    field_simp
  constructor
  · rw [← quadrance_after_sub_before, sub_eq_zero]
    constructor
    · intro h
      have h' : ((quadrance m.after : ℤ) : ℝ) = ((quadrance m.before : ℤ) : ℝ) := by rw [h]
      rw [hq, quadrance_cast] at h'
      exact mul_right_cancel₀ hpos.ne' (h'.trans (one_mul _).symm)
    · intro h
      rw [h, one_mul] at hq
      exact_mod_cast hq
  · intro h
    rw [traction_disk_lattice m hv, Holonics.Geometry.Motion.turn_distance_from_one h]

/-- [proved-derived; formal-checked] **A lattice boost, decided on the integers:** for `v ≠ 0`,
`det(v, Δv) = 0` and `|v|² + ⟨v, Δv⟩ > 0` when and only when `k` is real and positive. -/
theorem boost_test (m : MovePair) (hv : m.before ≠ 0) :
    (det m.before m.change = 0 ∧ 0 < quadrance m.before + dot m.before m.change) ↔
      (m.ratio.im = 0 ∧ 0 < m.ratio.re) := by
  have h0 := toComplex_ne_zero hv
  have hpos : 0 < normSq (GaussianInt.toComplex m.before) := normSq_pos.mpr h0
  have hp := pairing_is_ratio m hv
  have hre : ((dot m.before m.change : ℤ) : ℝ) =
      normSq (GaussianInt.toComplex m.before) * (m.ratio.re - 1) := by
    rw [← (pairing_faces _ _).1, GaussianInt.intCast_re, hp]
    simp
  have him : ((det m.before m.change : ℤ) : ℝ) =
      normSq (GaussianInt.toComplex m.before) * m.ratio.im := by
    rw [← (pairing_faces _ _).2, GaussianInt.intCast_im, hp]
    simp
  have hqb : ((quadrance m.before : ℤ) : ℝ) = normSq (GaussianInt.toComplex m.before) :=
    quadrance_cast _
  constructor
  · rintro ⟨hd, hs⟩
    have hd' : ((det m.before m.change : ℤ) : ℝ) = 0 := by rw [hd]; simp
    rw [hd'] at him
    have hs' : (0 : ℝ) < ((quadrance m.before + dot m.before m.change : ℤ) : ℝ) := by
      exact_mod_cast hs
    push_cast at hs'
    rw [hre, hqb] at hs'
    refine ⟨?_, ?_⟩
    · rcases mul_eq_zero.mp him.symm with h | h
      · exact absurd h hpos.ne'
      · exact h
    · nlinarith
  · rintro ⟨hi, hr⟩
    refine ⟨?_, ?_⟩
    · have : ((det m.before m.change : ℤ) : ℝ) = 0 := by rw [him, hi, mul_zero]
      exact_mod_cast this
    · have : (0 : ℝ) < ((quadrance m.before + dot m.before m.change : ℤ) : ℝ) := by
        push_cast
        rw [hre, hqb]
        nlinarith
      exact_mod_cast this

/-- [proved-standard; formal-checked] **Free fall and stop, decided on the integers:** for
`v ≠ 0`, `Δv = 0` when and only when `k = 1`, and `v′ = 0` when and only when `k = 0`. -/
theorem fall_and_stop_test (m : MovePair) (hv : m.before ≠ 0) :
    (m.change = 0 ↔ m.ratio = 1) ∧ (m.after = 0 ↔ m.ratio = 0) := by
  have h0 := toComplex_ne_zero hv
  constructor
  · rw [MovePair.change, sub_eq_zero, MovePair.ratio, div_eq_one_iff_eq h0]
    exact ⟨fun h => by rw [h], fun h => GaussianInt.toComplex_injective h⟩
  · rw [MovePair.ratio, div_eq_zero_iff, or_iff_left h0]
    exact ⟨fun h => by rw [h, map_zero], fun h => GaussianInt.toComplex_injective (by rw [h, map_zero])⟩

end Moves

/-! ## 2. Capture and viability on a finite terrain -/

section Chains

/-- [proved-standard; formal-checked] **A chain driven by a step stands once it repeats:** if
`c (n + 1) = F (c n)` and `c (n + 1) = c n`, then `c m = c n` for every `m ≥ n`. -/
theorem chain_stands {β : Type*} {c : ℕ → β} (F : β → β) (hc : ∀ n, c (n + 1) = F (c n)) {n : ℕ}
    (h : c (n + 1) = c n) : ∀ m, n ≤ m → c m = c n := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m _ ih => rw [hc, ih, ← hc, h]

/-- [proved-standard; formal-checked] **A chain whose measure rises at every strict step repeats
by its bound:** if `μ (c n) ≤ B` always and `μ` rises strictly wherever `c (n + 1) ≠ c n`, some
`n ≤ B` has `c (n + 1) = c n`. -/
theorem chain_repeats {β : Type*} {c : ℕ → β} (μ : β → ℕ) (B : ℕ) (hB : ∀ n, μ (c n) ≤ B)
    (hrise : ∀ n, c (n + 1) ≠ c n → μ (c n) < μ (c (n + 1))) : ∃ n ≤ B, c (n + 1) = c n := by
  by_contra hne
  push Not at hne
  have key : ∀ n, n ≤ B + 1 → n ≤ μ (c n) := by
    intro n hn
    induction n with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have h1 := hrise k (hne k (by omega))
      have h2 := ih (by omega)
      omega
  have h1 := key (B + 1) le_rfl
  have h2 := hB (B + 1)
  omega

/-- [proved-standard; formal-checked] **The bound at which a stepped chain stands:** under the
hypotheses of `chain_repeats`, `c m = c B` for every `m ≥ B`. -/
theorem chain_stands_by {β : Type*} {c : ℕ → β} (F : β → β) (hc : ∀ n, c (n + 1) = F (c n))
    (μ : β → ℕ) (B : ℕ) (hB : ∀ n, μ (c n) ≤ B)
    (hrise : ∀ n, c (n + 1) ≠ c n → μ (c n) < μ (c (n + 1))) : ∀ m, B ≤ m → c m = c B := by
  obtain ⟨n, hn, h⟩ := chain_repeats μ B hB hrise
  intro m hm
  rw [chain_stands F hc h m (hn.trans hm), chain_stands F hc h B hn]

end Chains

section Recursions

variable {Z U W : Type*}

/-- [definition] **The robust predecessor** (the record's §14.4):
`Pre S = {z | ∃ u, ∀ w, T z u w ∈ S}`, the states from which some move `u` lands in `S` whatever
the other's reply `w` (the mover commits before the disturbance). -/
def Pre (T : Z → U → W → Z) (S : Set Z) : Set Z := {z | ∃ u, ∀ w, T z u w ∈ S}

/-- [definition] **The dual predecessor** `{z | ∀ u, ∃ w, T z u w ∈ S}`: the replying side's
quantifiers. -/
def PreDual (T : Z → U → W → Z) (S : Set Z) : Set Z := {z | ∀ u, ∃ w, T z u w ∈ S}

/-- [proved-standard; formal-checked] The robust predecessor is monotone. -/
theorem pre_mono (T : Z → U → W → Z) : Monotone (Pre T) := by
  intro S S' h z ⟨u, hu⟩
  exact ⟨u, fun w => h (hu w)⟩

/-- [proved-standard; formal-checked] The dual predecessor is monotone. -/
theorem preDual_mono (T : Z → U → W → Z) : Monotone (PreDual T) := by
  intro S S' h z hz u
  obtain ⟨w, hw⟩ := hz u
  exact ⟨w, h hw⟩

/-- [proved-standard; formal-checked] **The barrier's duality:** the complement of the robust
predecessor is the dual predecessor of the complement. -/
theorem compl_pre (T : Z → U → W → Z) (S : Set Z) : (Pre T S)ᶜ = PreDual T Sᶜ := by
  ext z
  simp only [Pre, PreDual, Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_forall]

/-- [definition] **The admitted moves read through a total transition** (agent-inferred encoding):
a move `u` not admitted at `z` is read as the stop `stop z`, and a reply `w` not admitted after the
read move as the declared reply `reply z u`. -/
noncomputable def admitted (A : Z → U → Prop) (stop : Z → U) (B : Z → U → W → Prop)
    (reply : Z → U → W) (T : Z → U → W → Z) : Z → U → W → Z := by
  classical
  exact fun z u w =>
    if B z (if A z u then u else stop z) w then T z (if A z u then u else stop z) w
    else T z (if A z u then u else stop z) (reply z (if A z u then u else stop z))

/-- [proved-derived; formal-checked] **The robust predecessor holds the admitted form:** when the mover
can always stop (`A z (stop z)`) and the replier always has an admitted reply, the robust
predecessor of the total transition is `{z | ∃ u admitted, ∀ w admitted, T z u w ∈ S}`. -/
theorem pre_admitted (A : Z → U → Prop) (stop : Z → U) (B : Z → U → W → Prop)
    (reply : Z → U → W) (T : Z → U → W → Z) (hstop : ∀ z, A z (stop z))
    (hreply : ∀ z u, B z u (reply z u)) (S : Set Z) :
    Pre (admitted A stop B reply T) S = {z | ∃ u, A z u ∧ ∀ w, B z u w → T z u w ∈ S} := by
  classical
  ext z
  simp only [Pre, admitted, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨if A z u then u else stop z, ?_, fun w hw => ?_⟩
    · split_ifs with h
      · exact h
      · exact hstop z
    · have := hu w
      rwa [if_pos hw] at this
  · rintro ⟨u, hA, hu⟩
    refine ⟨u, fun w => ?_⟩
    simp only [if_pos hA]
    split_ifs with hw
    · exact hu w hw
    · exact hu _ (hreply z u)

/-- [definition] **The capture basins** (the record's §14.4): `C₀ = target`,
`C_(n+1) = C_n ∪ P C_n`, read with the robust predecessor `P = Pre T`. -/
def captureBasin (P : Set Z → Set Z) (target : Set Z) : ℕ → Set Z
  | 0 => target
  | n + 1 => captureBasin P target n ∪ P (captureBasin P target n)

/-- [definition] **The viability kernels** (the record's §14.4): `K₀` given,
`K_(n+1) = K_n ∩ P K_n`. -/
def viabilityKernel (P : Set Z → Set Z) (K₀ : Set Z) : ℕ → Set Z
  | 0 => K₀
  | n + 1 => viabilityKernel P K₀ n ∩ P (viabilityKernel P K₀ n)

/-- [proved-standard; formal-checked] The capture basins increase. -/
theorem captureBasin_mono (P : Set Z → Set Z) (target : Set Z) :
    Monotone (captureBasin P target) :=
  monotone_nat_of_le_succ fun _ => Set.subset_union_left

/-- [proved-standard; formal-checked] The viability kernels decrease. -/
theorem viabilityKernel_anti (P : Set Z → Set Z) (K₀ : Set Z) :
    Antitone (viabilityKernel P K₀) :=
  antitone_nat_of_succ_le fun _ => Set.inter_subset_left

/-- [proved-standard; formal-checked] **The capture basins stand after at most as many ticks as
there are states:** on a finite terrain, `C_m = C_|Z|` for every `m ≥ |Z|`. -/
theorem captureBasin_stands [Finite Z] (P : Set Z → Set Z) (target : Set Z) :
    ∀ m, Nat.card Z ≤ m → captureBasin P target m = captureBasin P target (Nat.card Z) := by
  refine chain_stands_by (fun S => S ∪ P S) (fun _ => rfl) Set.ncard (Nat.card Z)
    (fun n => Set.ncard_le_card _) (fun n hne => ?_)
  exact Set.ncard_lt_ncard (LE.le.ssubset_of_ne Set.subset_union_left hne.symm)

/-- [proved-standard; formal-checked] **The viability kernels stand after at most as many ticks as
there are states:** on a finite terrain, `K_m = K_|Z|` for every `m ≥ |Z|`. -/
theorem viabilityKernel_stands [Finite Z] (P : Set Z → Set Z) (K₀ : Set Z) :
    ∀ m, Nat.card Z ≤ m → viabilityKernel P K₀ m = viabilityKernel P K₀ (Nat.card Z) := by
  refine chain_stands_by (fun S => S ∩ P S) (fun _ => rfl) (fun S => Set.ncard Sᶜ) (Nat.card Z)
    (fun n => Set.ncard_le_card _) (fun n hne => ?_)
  refine Set.ncard_lt_ncard ?_
  exact compl_lt_compl_iff_lt.mpr (LE.le.ssubset_of_ne Set.inter_subset_left hne)

/-- [proved-standard; formal-checked] On a finite terrain the union of the capture basins is the
basin at `|Z|` ticks. -/
theorem iUnion_captureBasin [Finite Z] (P : Set Z → Set Z) (target : Set Z) :
    ⋃ n, captureBasin P target n = captureBasin P target (Nat.card Z) := by
  apply subset_antisymm
  · refine Set.iUnion_subset fun n => ?_
    rcases le_total n (Nat.card Z) with h | h
    · exact captureBasin_mono P target h
    · exact (captureBasin_stands P target n h).subset
  · exact Set.subset_iUnion (captureBasin P target) _

/-- [proved-standard; formal-checked] On a finite terrain the intersection of the viability
kernels is the kernel at `|Z|` ticks. -/
theorem iInter_viabilityKernel [Finite Z] (P : Set Z → Set Z) (K₀ : Set Z) :
    ⋂ n, viabilityKernel P K₀ n = viabilityKernel P K₀ (Nat.card Z) := by
  apply subset_antisymm
  · exact Set.iInter_subset (viabilityKernel P K₀) _
  · refine Set.subset_iInter fun n => ?_
    rcases le_total n (Nat.card Z) with h | h
    · exact viabilityKernel_anti P K₀ h
    · exact (viabilityKernel_stands P K₀ n h).symm.subset

/-- [proved-standard; formal-checked] **The capture basin is the least closed set over the
target:** on a finite terrain and for a monotone predecessor `P`, `C_|Z|` contains the target, is
closed under `P`, and lies inside every set that contains the target and is closed under `P`. -/
theorem captureBasin_isLeast [Finite Z] {P : Set Z → Set Z} (hP : Monotone P) (target : Set Z) :
    IsLeast {S | target ⊆ S ∧ P S ⊆ S} (captureBasin P target (Nat.card Z)) := by
  refine ⟨⟨?_, ?_⟩, fun S ⟨hT, hS⟩ => ?_⟩
  · exact captureBasin_mono P target (Nat.zero_le _)
  · have h := captureBasin_stands P target (Nat.card Z + 1) (Nat.le_succ _)
    intro z hz
    rw [← h]
    exact Or.inr hz
  · suffices ∀ n, captureBasin P target n ⊆ S from this _
    intro n
    induction n with
    | zero => exact hT
    | succ n ih => exact Set.union_subset ih ((hP ih).trans hS)

/-- [proved-standard; formal-checked] **The viability kernel is the largest viable set inside
`K₀`:** on a finite terrain and for a monotone predecessor `P`, `K_|Z| ⊆ K₀`, `K_|Z| ⊆ P K_|Z|`, and
every `S ⊆ K₀` with `S ⊆ P S` lies inside it. -/
theorem viabilityKernel_isGreatest [Finite Z] {P : Set Z → Set Z} (hP : Monotone P) (K₀ : Set Z) :
    IsGreatest {S | S ⊆ K₀ ∧ S ⊆ P S} (viabilityKernel P K₀ (Nat.card Z)) := by
  refine ⟨⟨?_, ?_⟩, fun S ⟨hK, hS⟩ => ?_⟩
  · exact viabilityKernel_anti P K₀ (Nat.zero_le _)
  · have h := viabilityKernel_stands P K₀ (Nat.card Z + 1) (Nat.le_succ _)
    intro z hz
    rw [← h] at hz
    exact hz.2
  · suffices ∀ n, S ⊆ viabilityKernel P K₀ n from this _
    intro n
    induction n with
    | zero => exact hK
    | succ n ih => exact Set.subset_inter ih (hS.trans (hP ih))

/-- [proved-standard; formal-checked] **The capture basin is a fixed point over the target:** on a
finite terrain and for a monotone `P`, `target ∪ P C_|Z| = C_|Z|`. -/
theorem captureBasin_fixed [Finite Z] {P : Set Z → Set Z} (hP : Monotone P) (target : Set Z) :
    target ∪ P (captureBasin P target (Nat.card Z)) = captureBasin P target (Nat.card Z) := by
  have hl := (captureBasin_isLeast hP target).1
  refine subset_antisymm (Set.union_subset hl.1 hl.2) ?_
  suffices ∀ n, captureBasin P target n ⊆ target ∪ P (captureBasin P target n) from this _
  intro n
  induction n with
  | zero => exact Set.subset_union_left
  | succ n ih =>
    have hmono := hP (captureBasin_mono P target (Nat.le_succ n))
    exact Set.union_subset (ih.trans (Set.union_subset_union_right _ hmono))
      (hmono.trans Set.subset_union_right)

/-- [proved-standard; formal-checked] **The viability kernel is a fixed point inside `K₀`:** on a
finite terrain and for a monotone `P`, `K₀ ∩ P K_|Z| = K_|Z|`. -/
theorem viabilityKernel_fixed [Finite Z] {P : Set Z → Set Z} (hP : Monotone P) (K₀ : Set Z) :
    K₀ ∩ P (viabilityKernel P K₀ (Nat.card Z)) = viabilityKernel P K₀ (Nat.card Z) := by
  have hg := (viabilityKernel_isGreatest hP K₀).1
  refine subset_antisymm ?_ (Set.subset_inter hg.1 hg.2)
  suffices ∀ n, K₀ ∩ P (viabilityKernel P K₀ n) ⊆ viabilityKernel P K₀ n from this _
  intro n
  induction n with
  | zero => exact Set.inter_subset_left
  | succ n ih =>
    have hmono := hP (viabilityKernel_anti P K₀ (Nat.le_succ n))
    exact Set.subset_inter ((Set.inter_subset_inter_right _ hmono).trans ih)
      (Set.inter_subset_right.trans hmono)

/-- [proved-derived; formal-checked] **Kernel membership promises a next viable move, not
capture:** a state of the robust viability kernel has a move whose every reply stays in it. -/
theorem viabilityKernel_next_move [Finite Z] (T : Z → U → W → Z) (K₀ : Set Z) {z : Z}
    (hz : z ∈ viabilityKernel (Pre T) K₀ (Nat.card Z)) :
    ∃ u, ∀ w, T z u w ∈ viabilityKernel (Pre T) K₀ (Nat.card Z) :=
  (viabilityKernel_isGreatest (pre_mono T) K₀).1.2 hz

/-- [proved-standard; formal-checked] **Escape is the dual kernel of the complement:** the states
not captured within `n` ticks are the viability kernel of the target's complement under the dual
quantifiers, at every `n`. -/
theorem compl_captureBasin (T : Z → U → W → Z) (target : Set Z) (n : ℕ) :
    (captureBasin (Pre T) target n)ᶜ = viabilityKernel (PreDual T) targetᶜ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [captureBasin, viabilityKernel, Set.compl_union, compl_pre, ih]

end Recursions

section LeastCapture

variable {Z U W : Type*}

open Classical in
/-- [definition] **The least capture time** of `z`: the least `n` with `z ∈ C_n`, and `⊤` when no
basin holds it. -/
noncomputable def leastCapture (T : Z → U → W → Z) (target : Set Z) (z : Z) : ℕ∞ :=
  if h : ∃ n, z ∈ captureBasin (Pre T) target n then (Nat.find h : ℕ∞) else ⊤

/-- [proved-standard; formal-checked] **The least capture reads the basins:**
`τ z ≤ n ⇔ z ∈ C_n`. -/
theorem leastCapture_le_iff (T : Z → U → W → Z) (target : Set Z) (z : Z) (n : ℕ) :
    leastCapture T target z ≤ n ↔ z ∈ captureBasin (Pre T) target n := by
  classical
  unfold leastCapture
  split_ifs with h
  · rw [Nat.cast_le, Nat.find_le_iff]
    exact ⟨fun ⟨m, hm, hz⟩ => captureBasin_mono _ _ hm hz, fun hz => ⟨n, le_rfl, hz⟩⟩
  · simp only [top_le_iff, ENat.natCast_ne_top, false_iff]
    exact fun hz => h ⟨n, hz⟩

/-- [proved-standard; formal-checked] Two extended naturals that meet every natural bound alike
are equal. -/
private theorem eq_of_le_natCast_iff {a b : ℕ∞} (h : ∀ n : ℕ, a ≤ n ↔ b ≤ n) : a = b := by
  induction a using ENat.recTopCoe with
  | top =>
    induction b using ENat.recTopCoe with
    | top => rfl
    | coe m => exact absurd ((h m).2 le_rfl) (by simp)
  | coe k =>
    have hb := (h k).1 le_rfl
    induction b using ENat.recTopCoe with
    | top => simp at hb
    | coe m =>
      have ha := (h m).2 le_rfl
      exact_mod_cast le_antisymm (by exact_mod_cast ha) (by exact_mod_cast hb)

/-- [proved-standard; formal-checked] Off the target, the basin one tick later is the robust
predecessor of the basin: `z ∉ target ⇒ (z ∈ C_(n+1) ⇔ z ∈ Pre C_n)`. -/
theorem mem_captureBasin_succ (T : Z → U → W → Z) (target : Set Z) {z : Z} (hz : z ∉ target)
    (n : ℕ) : z ∈ captureBasin (Pre T) target (n + 1) ↔ z ∈ Pre T (captureBasin (Pre T) target n) := by
  constructor
  · induction n with
    | zero =>
      rintro (h | h)
      · exact absurd h hz
      · exact h
    | succ n ih =>
      rintro (h | h)
      · exact pre_mono T (captureBasin_mono _ _ (Nat.le_succ n)) (ih h)
      · exact h
  · exact fun h => Or.inr h

/-- [proved-standard; formal-checked] **The least capture is zero on the target.** -/
theorem leastCapture_target (T : Z → U → W → Z) {target : Set Z} {z : Z} (hz : z ∈ target) :
    leastCapture T target z = 0 := by
  have := (leastCapture_le_iff T target z 0).2 hz
  simpa using this

/-- [proved-standard; formal-checked] **The one-step recursion of the least capture** (retrograde
analysis): off the target, `τ z = 1 + min_u max_w τ (T z u w)`, the minimum and maximum read in
`ℕ∞` (`⊤` where no move captures). -/
theorem leastCapture_step (T : Z → U → W → Z) (target : Set Z) {z : Z} (hz : z ∉ target) :
    leastCapture T target z = 1 + ⨅ u, ⨆ w, leastCapture T target (T z u w) := by
  apply eq_of_le_natCast_iff
  intro n
  rcases n with _ | n
  · rw [leastCapture_le_iff]
    simp only [captureBasin, Nat.cast_zero, nonpos_iff_eq_zero, add_eq_zero, one_ne_zero,
      false_and, iff_false]
    exact hz
  · rw [leastCapture_le_iff, mem_captureBasin_succ T target hz, Nat.cast_add, Nat.cast_one,
      add_comm (1 : ℕ∞), ENat.add_le_add_iff_right ENat.one_ne_top,
      ← ENat.lt_add_one_iff (ENat.natCast_ne_top n), iInf_lt_iff]
    simp only [Pre, Set.mem_ofPred_eq]
    refine exists_congr fun u => ?_
    rw [ENat.lt_add_one_iff (ENat.natCast_ne_top n), iSup_le_iff]
    exact forall_congr' fun w => (leastCapture_le_iff T target _ n).symm

/-- [proved-standard; formal-checked] **A finite least capture is at most the number of states:**
on a finite terrain, `τ z < ⊤ ⇔ z ∈ C_|Z| ⇔ τ z ≤ |Z|`. -/
theorem leastCapture_lt_top_iff [Finite Z] (T : Z → U → W → Z) (target : Set Z) (z : Z) :
    (leastCapture T target z < ⊤ ↔ z ∈ captureBasin (Pre T) target (Nat.card Z)) ∧
      (leastCapture T target z < ⊤ ↔ leastCapture T target z ≤ Nat.card Z) := by
  have h1 : leastCapture T target z < ⊤ ↔ ∃ m : ℕ, leastCapture T target z ≤ m := by
    constructor
    · intro h
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h.ne
      exact ⟨m, hm.symm.le⟩
    · rintro ⟨m, hm⟩
      exact lt_of_le_of_lt hm (ENat.natCast_lt_top m)
  have key : leastCapture T target z < ⊤ ↔ z ∈ captureBasin (Pre T) target (Nat.card Z) := by
    rw [h1, ← iUnion_captureBasin, Set.mem_iUnion]
    exact exists_congr fun m => leastCapture_le_iff T target z m
  exact ⟨key, key.trans (leastCapture_le_iff T target z _).symm⟩

end LeastCapture

/-! ## 3. Capture is not lock; the bearing's lock -/

section Lock

/-- [counterexample; formal-checked] **Capture is not lock:** on the lattice tick
`r_(t+1) = r_t + ṙ_t`, zero relative velocity at every tick keeps the relative position, so a pair
outside the capture disk (`⟨r₀, r₀⟩ > c`) is never captured. -/
theorem capture_is_not_lock (r rate : ℕ → GaussianInt) (hstep : ∀ t, r (t + 1) = r t + rate t)
    (hlock : ∀ t, rate t = 0) {c : ℤ} (hout : c < quadrance (r 0)) : ∀ t, c < quadrance (r t) := by
  have hr : ∀ t, r t = r 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [hstep, hlock, add_zero, ih]
  intro t
  rw [hr]
  exact hout

/-- [counterexample; formal-checked] **A capture crossing has nonzero relative velocity:** if the
pair is outside the disk at `t` and inside at `t + 1`, then `ṙ_t ≠ 0`. -/
theorem capture_crossing_moves (r rate : ℕ → GaussianInt) (hstep : ∀ t, r (t + 1) = r t + rate t)
    {c : ℤ} {t : ℕ} (hout : c < quadrance (r t)) (hin : quadrance (r (t + 1)) ≤ c) : rate t ≠ 0 := by
  intro h
  rw [hstep, h, add_zero] at hin
  omega

/-- [counterexample; formal-checked] **In an open arena a runner moving straight away is never
caught** (the record's §14.4): along `r_t = r₀ + t·d` with `⟨r₀, d⟩ ≥ 0` the quadrance never falls
below `⟨r₀, r₀⟩`. -/
theorem open_arena_escape (r₀ d : GaussianInt) (haway : 0 ≤ dot r₀ d) (t : ℕ) :
    quadrance r₀ ≤ quadrance (r₀ + (t : GaussianInt) * d) := by
  have ht : (0 : ℤ) ≤ t := Int.natCast_nonneg t
  have hq : 0 ≤ dot d d := by unfold dot; nlinarith [sq_nonneg d.re, sq_nonneg d.im]
  have e : quadrance (r₀ + (t : GaussianInt) * d) =
      quadrance r₀ + 2 * t * dot r₀ d + (t : ℤ) ^ 2 * dot d d := by
    simp only [quadrance, dot, Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_mul, Zsqrtd.im_mul,
      Zsqrtd.re_natCast, Zsqrtd.im_natCast]
    ring
  rw [e]
  have h1 : 0 ≤ 2 * (t : ℤ) * dot r₀ d := by positivity
  have h2 : 0 ≤ (t : ℤ) ^ 2 * dot d d := by positivity
  linarith

/-- [proved-derived; formal-checked] **The bearing receiver's rate** (atlas
`pursuit.constant-bearing-lock`): along a differentiable relative displacement `r` off the cut,
`d/dt arg r = det(r, dr)/|r|²`. Constant bearing is the lock `det(r, dr) = 0`. -/
theorem bearing_rate {r : ℝ → ℂ} {dr : ℂ} {t : ℝ} (h : HasDerivAt r dr t) (hr : r t ∈ slitPlane) :
    HasDerivAt (fun s => arg (r s)) (((r t).re * dr.im - (r t).im * dr.re) / normSq (r t)) t := by
  have hlog := h.clog_real hr
  have him := (Complex.imCLM.hasFDerivAt (x := Complex.log (r t))).comp_hasDerivAt t hlog
  have e : (fun s => arg (r s)) = Complex.imCLM ∘ fun s => Complex.log (r s) := by
    funext s
    simp [Complex.log_im]
  rw [e]
  refine him.congr_deriv ?_
  simp only [Complex.imCLM_apply, Complex.div_im]
  ring

/-- [proved-standard; formal-checked] **The contact's rate:** `d/dt ⟨r, r⟩ = 2⟨r, dr⟩`, so a
constant bearing approaches only where `⟨r, dr⟩ < 0`: the bearing's lock permits radial slip. -/
theorem quadrance_rate {r : ℝ → ℂ} {dr : ℂ} {t : ℝ} (h : HasDerivAt r dr t) :
    HasDerivAt (fun s => normSq (r s)) (2 * ((r t).re * dr.re + (r t).im * dr.im)) t := by
  have hre := (Complex.reCLM.hasFDerivAt (x := r t)).comp_hasDerivAt t h
  have him := (Complex.imCLM.hasFDerivAt (x := r t)).comp_hasDerivAt t h
  have e : (fun s => normSq (r s)) =
      fun s => (Complex.reCLM ∘ r) s * (Complex.reCLM ∘ r) s +
        (Complex.imCLM ∘ r) s * (Complex.imCLM ∘ r) s := by
    funext s
    simp [normSq_apply]
  rw [e]
  refine ((hre.mul hre).add (him.mul him)).congr_deriv ?_
  simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
  ring

end Lock

/-! ## 4. Phase viability: Adler's equation -/

section Adler

open Real

/-- [definition] **Adler's phase rate** `φ̇ = δ − K sin φ`: detuning `δ`, coupling `K`. -/
noncomputable def adlerRate (δ K φ : ℝ) : ℝ := δ - K * Real.sin φ

/-- [proved-standard; formal-checked] The rate's slope is `−K cos φ`, so in the linear reading a
rest point with `K cos φ* > 0` attracts and one with `K cos φ* < 0` repels. -/
theorem hasDerivAt_adlerRate (δ K φ : ℝ) :
    HasDerivAt (adlerRate δ K) (-(K * Real.cos φ)) φ := by
  have := (hasDerivAt_const φ δ).sub ((Real.hasDerivAt_sin φ).const_mul K)
  refine this.congr_deriv ?_
  ring

/-- [proved-standard; formal-checked] **The phase can rest iff the detuning is within the
coupling:** for `K > 0`, `∃ φ, δ − K sin φ = 0 ⇔ |δ| ≤ K`. -/
theorem adler_rest_iff {δ K : ℝ} (hK : 0 < K) : (∃ φ, adlerRate δ K φ = 0) ↔ |δ| ≤ K := by
  constructor
  · rintro ⟨φ, hφ⟩
    have hs : δ = K * Real.sin φ := by unfold adlerRate at hφ; linarith
    rw [hs, abs_mul, abs_of_pos hK]
    exact mul_le_of_le_one_right hK.le (abs_sin_le_one φ)
  · intro h
    have h1 : -1 ≤ δ / K := by rw [le_div_iff₀ hK]; linarith [neg_abs_le δ]
    have h2 : δ / K ≤ 1 := by rw [div_le_iff₀ hK]; linarith [le_abs_self δ]
    refine ⟨arcsin (δ / K), ?_⟩
    rw [adlerRate, sin_arcsin h1 h2]
    field_simp
    ring

/-- [definition] The stable rest phase `arcsin(δ/K)`. -/
noncomputable def stablePhase (δ K : ℝ) : ℝ := arcsin (δ / K)

/-- [definition] The unstable rest phase `π − arcsin(δ/K)`. -/
noncomputable def unstablePhase (δ K : ℝ) : ℝ := π - arcsin (δ / K)

/-- [proved-standard; formal-checked] **Inside the tongue there are two rest points in each turn,
one stable and one unstable:** for `|δ| < K`, the rest points are
`arcsin(δ/K) + 2πn` and `π − arcsin(δ/K) + 2πn`; the first has `K cos φ* > 0`, the second
`K cos φ* < 0`; and `φ_s < φ_u < φ_s + 2π`. -/
theorem adler_two_rest_points {δ K : ℝ} (hK : 0 < K) (hδ : |δ| < K) :
    (∀ φ, adlerRate δ K φ = 0 ↔
        ∃ n : ℤ, φ = stablePhase δ K + 2 * n * π ∨ φ = unstablePhase δ K + 2 * n * π) ∧
      0 < K * Real.cos (stablePhase δ K) ∧ K * Real.cos (unstablePhase δ K) < 0 ∧
      stablePhase δ K < unstablePhase δ K ∧ unstablePhase δ K < stablePhase δ K + 2 * π := by
  have h1 : -1 < δ / K := by rw [lt_div_iff₀ hK]; linarith [neg_abs_le δ]
  have h2 : δ / K < 1 := by rw [div_lt_iff₀ hK]; linarith [le_abs_self δ]
  have hlo := neg_pi_div_two_lt_arcsin.mpr h1
  have hhi := arcsin_lt_pi_div_two.mpr h2
  have hcos : 0 < Real.cos (stablePhase δ K) := by
    rw [stablePhase, cos_arcsin]
    apply Real.sqrt_pos.mpr
    nlinarith
  refine ⟨fun φ => ?_, mul_pos hK hcos, ?_, ?_, ?_⟩
  · have hrest : adlerRate δ K φ = 0 ↔ Real.sin (stablePhase δ K) = Real.sin φ := by
      rw [stablePhase, sin_arcsin h1.le h2.le, adlerRate, sub_eq_zero]
      constructor
      · intro h; field_simp; linarith
      · intro h; rw [← h]; field_simp
    rw [hrest, Real.sin_eq_sin_iff, unstablePhase]
    unfold stablePhase
    refine exists_congr fun n => or_congr ?_ ?_
    · constructor <;> intro h <;> linarith
    · constructor <;> intro h <;> linarith
  · rw [unstablePhase, Real.cos_pi_sub]
    have : Real.cos (arcsin (δ / K)) = Real.cos (stablePhase δ K) := rfl
    rw [this]
    nlinarith
  · rw [stablePhase, unstablePhase]
    linarith
  · rw [stablePhase, unstablePhase]
    linarith

/-- [proved-standard; formal-checked] **At the tongue's edge the rest point is a saddle-node:**
for `|δ| = K > 0`, every rest point has `cos φ* = 0`. -/
theorem adler_edge {δ K : ℝ} (hK : 0 < K) (hδ : |δ| = K) {φ : ℝ} (hφ : adlerRate δ K φ = 0) :
    Real.cos φ = 0 := by
  have hs : δ = K * Real.sin φ := by unfold adlerRate at hφ; linarith
  have h1 : |Real.sin φ| = 1 := by
    rw [hs, abs_mul, abs_of_pos hK] at hδ
    exact mul_left_cancel₀ hK.ne' (hδ.trans (mul_one K).symm)
  have h2 : Real.sin φ ^ 2 = 1 := by rw [← sq_abs, h1, one_pow]
  have h3 := Real.sin_sq_add_cos_sq φ
  have h4 : Real.cos φ ^ 2 = 0 := by linarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4

/-- [proved-standard; formal-checked] **Outside the tongue the phase never rests and keeps the
detuning's sign:** for `K ≥ 0` and `|δ| > K`, `δ · φ̇ > 0` and `|φ̇| ≥ |δ| − K` at every phase. -/
theorem adler_no_rest {δ K : ℝ} (hK : 0 ≤ K) (hδ : K < |δ|) (φ : ℝ) :
    0 < δ * adlerRate δ K φ ∧ |δ| - K ≤ |adlerRate δ K φ| := by
  have hs1 := neg_one_le_sin φ
  have hs2 := sin_le_one φ
  have hKs1 : -K ≤ K * Real.sin φ := by nlinarith
  have hKs2 : K * Real.sin φ ≤ K := by nlinarith
  rcases lt_or_ge δ 0 with hneg | hpos
  · rw [abs_of_neg hneg] at hδ
    have hr : adlerRate δ K φ ≤ δ + K := by unfold adlerRate; linarith
    have hr0 : adlerRate δ K φ < 0 := by linarith
    refine ⟨mul_pos_of_neg_of_neg hneg hr0, ?_⟩
    rw [abs_of_neg hneg, abs_of_neg hr0]
    linarith
  · rw [abs_of_nonneg hpos] at hδ
    have hr : δ - K ≤ adlerRate δ K φ := by unfold adlerRate; linarith
    have hr0 : 0 < adlerRate δ K φ := by linarith
    refine ⟨mul_pos (by linarith) hr0, ?_⟩
    rw [abs_of_nonneg hpos, abs_of_pos hr0]
    exact hr

/-- [proved-standard; formal-checked] **The lock is lost: a solution slips through every turn.**
For `K ≥ 0` and `δ > K`, a solution of `φ̇ = δ − K sin φ` is strictly increasing and gains at
least `(δ − K)(t − s)` over `[s, t]`. -/
theorem adler_slip {δ K : ℝ} (hK : 0 ≤ K) (hδ : K < δ) {φ : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ (adlerRate δ K (φ t)) t) :
    StrictMono φ ∧ ∀ s t, s ≤ t → (δ - K) * (t - s) ≤ φ t - φ s := by
  have hδ' : K < |δ| := by rw [abs_of_pos (hK.trans_lt hδ)]; exact hδ
  have hlow : ∀ t, δ - K ≤ deriv φ t := by
    intro t
    rw [(hφ t).deriv]
    have := (adler_no_rest hK hδ' (φ t)).2
    rw [abs_of_pos (hK.trans_lt hδ)] at this
    exact this.trans (le_of_eq (abs_of_pos (by
      have h0 := (adler_no_rest hK hδ' (φ t)).1
      exact pos_of_mul_pos_right h0 (hK.trans_lt hδ).le)))
  refine ⟨strictMono_of_deriv_pos fun t => lt_of_lt_of_le (by linarith) (hlow t), ?_⟩
  intro s t hst
  exact mul_sub_le_image_sub_of_le_deriv (fun t => (hφ t).differentiableAt) hlow hst

/-- [proved-standard; formal-checked] **The lock is lost below too:** for `K ≥ 0` and `δ < −K`, a
solution is strictly decreasing and loses at least `(|δ| − K)(t − s)` over `[s, t]` (the slip of
`−φ`, which solves the equation with detuning `−δ`). -/
theorem adler_slip_neg {δ K : ℝ} (hK : 0 ≤ K) (hδ : δ < -K) {φ : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ (adlerRate δ K (φ t)) t) :
    StrictAnti φ ∧ ∀ s t, s ≤ t → (-δ - K) * (t - s) ≤ φ s - φ t := by
  have hψ : ∀ t, HasDerivAt (fun s => -φ s) (adlerRate (-δ) K (-φ t)) t := by
    intro t
    refine (hφ t).neg.congr_deriv ?_
    simp only [adlerRate, Real.sin_neg]
    ring
  obtain ⟨hmono, hgain⟩ := adler_slip hK (by linarith) hψ
  refine ⟨fun a b hab => by simpa using hmono hab, fun s t hst => ?_⟩
  have := hgain s t hst
  linarith

/-- [proved-derived; formal-checked] **Robust inward control at an interval's ends** (atlas
`lock.phase-viability`): with the control bounded by `U ≥ 0` and the disturbance by `d ≥ 0`, the
lower end `a` admits a control pushing inward against every disturbance iff `F(a) + U − d ≥ 0`, and
the upper end `b` iff `F(b) − U + d ≤ 0`: the robust predecessor's quantifiers read at the ends. -/
theorem phase_inward {U d : ℝ} (hU : 0 ≤ U) (hd : 0 ≤ d) (Fa Fb : ℝ) :
    ((∃ u, |u| ≤ U ∧ ∀ w, |w| ≤ d → 0 ≤ Fa + u + w) ↔ 0 ≤ Fa + U - d) ∧
      ((∃ u, |u| ≤ U ∧ ∀ w, |w| ≤ d → Fb + u + w ≤ 0) ↔ Fb - U + d ≤ 0) := by
  constructor
  · constructor
    · rintro ⟨u, hu, hw⟩
      have h1 := hw (-d) (by rw [abs_neg, abs_of_nonneg hd])
      have h2 := (abs_le.mp hu).2
      linarith
    · intro h
      refine ⟨U, by rw [abs_of_nonneg hU], fun w hw => ?_⟩
      have := (abs_le.mp hw).1
      linarith
  · constructor
    · rintro ⟨u, hu, hw⟩
      have h1 := hw d (by rw [abs_of_nonneg hd])
      have h2 := (abs_le.mp hu).1
      linarith
    · intro h
      refine ⟨-U, by rw [abs_neg, abs_of_nonneg hU], fun w hw => ?_⟩
      have := (abs_le.mp hw).2
      linarith

end Adler

/-! ## 5. The expected-capture triple `(U, S, W)` -/

section Expected

/-- [definition] **A fibre's expected-capture reading** (atlas `pursuit.expected-capture`): the
members left uncaptured within the horizon `U`, the sum `S` of the captured members' capture
ticks, and the greatest of those ticks `W` (the strategy's own worst case). -/
@[ext]
structure ExpectedCapture where
  uncaptured : ℕ
  ticks : ℕ
  worst : ℕ

namespace ExpectedCapture

/-- [definition] **The sum of two classes' readings** `⊕`: counts and ticks add, the worst case is
the greater. -/
instance : Add ExpectedCapture :=
  ⟨fun a b => ⟨a.uncaptured + b.uncaptured, a.ticks + b.ticks, max a.worst b.worst⟩⟩

/-- [definition] The unit `(0, 0, 0)`. -/
instance : Zero ExpectedCapture := ⟨⟨0, 0, 0⟩⟩

/-- [definition] The uncaptured counts add under `⊕`. -/
@[simp] theorem add_uncaptured (a b : ExpectedCapture) :
    (a + b).uncaptured = a.uncaptured + b.uncaptured := rfl
/-- [definition] The tick sums add under `⊕`. -/
@[simp] theorem add_ticks (a b : ExpectedCapture) : (a + b).ticks = a.ticks + b.ticks := rfl
/-- [definition] The worst case of `⊕` is the greater. -/
@[simp] theorem add_worst (a b : ExpectedCapture) : (a + b).worst = max a.worst b.worst := rfl
/-- [definition] The unit leaves no member uncaptured. -/
@[simp] theorem zero_uncaptured : (0 : ExpectedCapture).uncaptured = 0 := rfl
/-- [definition] The unit's tick sum is zero. -/
@[simp] theorem zero_ticks : (0 : ExpectedCapture).ticks = 0 := rfl
/-- [definition] The unit's worst case is zero. -/
@[simp] theorem zero_worst : (0 : ExpectedCapture).worst = 0 := rfl

/-- [proved-derived; formal-checked] `⊕` is associative. -/
theorem plus_assoc (a b c : ExpectedCapture) : a + b + c = a + (b + c) := by
  ext <;> simp [Nat.add_assoc, max_assoc]

/-- [proved-derived; formal-checked] `⊕` is commutative. -/
theorem plus_comm (a b : ExpectedCapture) : a + b = b + a := by
  ext <;> simp [Nat.add_comm, max_comm]

/-- [proved-derived; formal-checked] `(0, 0, 0)` is the unit of `⊕`. -/
theorem zero_plus (a : ExpectedCapture) : 0 + a = a := by
  ext <;> simp

/-- [proved-derived; formal-checked] **The readings form a commutative monoid under `⊕`.** -/
instance : AddCommMonoid ExpectedCapture where
  add_assoc := plus_assoc
  zero_add := zero_plus
  add_zero a := by rw [plus_comm]; exact zero_plus a
  add_comm := plus_comm
  nsmul := nsmulRec

/-- [definition] **The shift by one tick** for a class of `n` members: every captured member pays
the move's tick, `shift(U, S, W) = (U, S + (n − U), W + 1 if U < n else 0)`. -/
def shift (n : ℕ) (e : ExpectedCapture) : ExpectedCapture :=
  ⟨e.uncaptured, e.ticks + (n - e.uncaptured), if e.uncaptured < n then e.worst + 1 else 0⟩

/-- [definition] **A reading of a class of `n` members:** at most `n` uncaptured, and no worst case
when none is captured. -/
def Fits (n : ℕ) (e : ExpectedCapture) : Prop := e.uncaptured ≤ n ∧ (e.uncaptured = n → e.worst = 0)

/-- [proved-derived; formal-checked] The sum of two classes' readings is a reading of their union. -/
theorem fits_plus {n n' : ℕ} {a b : ExpectedCapture} (ha : Fits n a) (hb : Fits n' b) :
    Fits (n + n') (a + b) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨by simp only [add_uncaptured]; omega, fun h => ?_⟩
  simp only [add_uncaptured] at h
  have h1 := ha2 (by omega)
  have h2 := hb2 (by omega)
  simp [h1, h2]

/-- [proved-derived; formal-checked] The shift keeps a reading of its class. -/
theorem fits_shift {n : ℕ} {a : ExpectedCapture} (ha : Fits n a) : Fits n (shift n a) := by
  refine ⟨ha.1, fun h => ?_⟩
  simp only [shift] at h ⊢
  rw [if_neg (by omega)]

/-- [proved-derived; formal-checked] **The shift distributes over `⊕`:** for readings of classes of
`n` and `n′` members, `shift_(n+n′)(a ⊕ b) = shift_n a ⊕ shift_n′ b`. -/
theorem shift_plus {n n' : ℕ} {a b : ExpectedCapture} (ha : Fits n a) (hb : Fits n' b) :
    shift (n + n') (a + b) = shift n a + shift n' b := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  ext
  · simp [shift]
  · simp only [shift, add_ticks, add_uncaptured]
    omega
  · simp only [shift, add_worst, add_uncaptured]
    by_cases h1 : a.uncaptured < n <;> by_cases h2 : b.uncaptured < n'
    · rw [if_pos (by omega), if_pos h1, if_pos h2]
      omega
    · have hb0 := hb2 (by omega)
      rw [if_pos (by omega), if_pos h1, if_neg h2, hb0]
      omega
    · have ha0 := ha2 (by omega)
      rw [if_pos (by omega), if_neg h1, if_pos h2, ha0]
      omega
    · rw [if_neg (by omega), if_neg h1, if_neg h2]
      rfl

/-- [definition] **The reading of a fibre under a fixed strategy**: each member's capture tick
`τ a` (`none` when it is not captured within the horizon), read as
`(#uncaptured, Σ ticks, max tick)`. -/
def reading {ι : Type*} (τ : ι → Option ℕ) (A : Finset ι) : ExpectedCapture :=
  ⟨(A.filter fun a => τ a = none).card, ∑ a ∈ A, (τ a).getD 0, A.sup fun a => (τ a).getD 0⟩

/-- [proved-derived; formal-checked] **A member alone** reads `(0, b, b)` when captured at `b`
and `(1, 0, 0)` when not. -/
theorem reading_singleton {ι : Type*} (τ : ι → Option ℕ) (a : ι) :
    reading τ {a} = match τ a with
      | some b => ⟨0, b, b⟩
      | none => ⟨1, 0, 0⟩ := by
  classical
  unfold reading
  rcases h : τ a with _ | b
  · simp [Finset.filter_singleton, h]
  · simp [Finset.filter_singleton, h]

/-- [proved-derived; formal-checked] The empty fibre reads `(0, 0, 0)`. -/
theorem reading_empty {ι : Type*} (τ : ι → Option ℕ) : reading τ ∅ = 0 := by
  ext <;> simp [reading]

/-- [proved-derived; formal-checked] **The reading of a union of disjoint fibres is the `⊕` of
their readings.** -/
theorem reading_union {ι : Type*} [DecidableEq ι] (τ : ι → Option ℕ) {A B : Finset ι}
    (h : Disjoint A B) : reading τ (A ∪ B) = reading τ A + reading τ B := by
  ext
  · simp only [reading, add_uncaptured, Finset.filter_union]
    exact Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)
  · simp only [reading, add_ticks]
    exact Finset.sum_union h
  · simp only [reading, add_worst]
    rw [Finset.sup_union]

/-- [proved-derived; formal-checked] **A fibre's reading is the `⊕` of its members' readings.** -/
theorem reading_eq_sum {ι : Type*} [DecidableEq ι] (τ : ι → Option ℕ) (A : Finset ι) :
    reading τ A = ∑ a ∈ A, reading τ {a} := by
  induction A using Finset.induction_on with
  | empty => rw [reading_empty, Finset.sum_empty]
  | insert a A ha ih =>
    rw [Finset.sum_insert ha, ← ih, Finset.insert_eq,
      reading_union τ (Finset.disjoint_singleton_left.mpr ha)]

/-- [proved-derived; formal-checked] A member's reading fits a class of one. -/
theorem fits_singleton {ι : Type*} (τ : ι → Option ℕ) (a : ι) : Fits 1 (reading τ {a}) := by
  rw [reading_singleton]
  rcases τ a with _ | b
  · exact ⟨le_rfl, fun _ => rfl⟩
  · exact ⟨Nat.zero_le _, fun h => absurd h (by norm_num)⟩

/-- [proved-derived; formal-checked] **The shift distributes over a `⊕` of many classes.** -/
theorem shift_sum {ι : Type*} [DecidableEq ι] (A : Finset ι) (n : ι → ℕ) (e : ι → ExpectedCapture)
    (he : ∀ a ∈ A, Fits (n a) (e a)) :
    Fits (∑ a ∈ A, n a) (∑ a ∈ A, e a) ∧
      shift (∑ a ∈ A, n a) (∑ a ∈ A, e a) = ∑ a ∈ A, shift (n a) (e a) := by
  induction A using Finset.induction_on with
  | empty =>
    refine ⟨⟨le_rfl, fun _ => rfl⟩, ?_⟩
    ext <;> simp [shift]
  | insert a A ha ih =>
    have hA := ih fun b hb => he b (Finset.mem_insert_of_mem hb)
    have hea := he a (Finset.mem_insert_self a A)
    simp only [Finset.sum_insert ha]
    exact ⟨fits_plus hea hA.1, by rw [shift_plus hea hA.1, hA.2]⟩

/-- [proved-derived; formal-checked] **The shift is the reading of the shifted ticks:** if every
captured member is captured one tick later, the fibre's reading is
`shift_|A|` of its reading. -/
theorem reading_shift {ι : Type*} [DecidableEq ι] (τ : ι → Option ℕ) (A : Finset ι) :
    reading (fun a => (τ a).map (· + 1)) A = shift A.card (reading τ A) := by
  rw [reading_eq_sum, reading_eq_sum τ A, Finset.card_eq_sum_ones,
    (shift_sum A (fun _ => 1) (fun a => reading τ {a}) fun a _ => fits_singleton τ a).2]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [reading_singleton, reading_singleton]
  rcases τ a with _ | b
  · rfl
  · ext <;> simp [shift]

/-- [proved-derived; formal-checked] A fibre's reading fits its class. -/
theorem reading_fits {ι : Type*} [DecidableEq ι] (τ : ι → Option ℕ) (A : Finset ι) :
    Fits A.card (reading τ A) := by
  rw [reading_eq_sum, Finset.card_eq_sum_ones]
  exact (shift_sum A (fun _ => 1) (fun a => reading τ {a}) fun a _ => fits_singleton τ a).1

/-- [proved-derived; formal-checked] **No member is left uncaptured iff every member is
captured:** `U = 0 ⇔ ∀ a ∈ A, τ a ≠ none`. -/
theorem reading_uncaptured_eq_zero {ι : Type*} (τ : ι → Option ℕ) (A : Finset ι) :
    (reading τ A).uncaptured = 0 ↔ ∀ a ∈ A, τ a ≠ none := by
  simp only [reading, Finset.card_eq_zero, Finset.filter_eq_empty_iff, ne_eq]

/-! The lexicographic order: most members captured, then the least tick sum, then the least
worst case. -/

/-- [definition] The lexicographic key `(U, (S, W))`. -/
def key (e : ExpectedCapture) : Lex (ℕ × Lex (ℕ × ℕ)) :=
  toLex (e.uncaptured, toLex (e.ticks, e.worst))

/-- [proved-standard; formal-checked] The key is injective, so the order is linear. -/
theorem key_injective : Function.Injective key := by
  intro a b h
  simp only [key, toLex_inj, Prod.mk.injEq] at h
  ext
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- [definition] **The order of readings is lexicographic** in `(U, S, W)`. -/
instance : LinearOrder ExpectedCapture := LinearOrder.lift' key key_injective

/-- [proved-derived; formal-checked] The order unfolded. -/
theorem le_iff (a b : ExpectedCapture) :
    a ≤ b ↔ a.uncaptured < b.uncaptured ∨ a.uncaptured = b.uncaptured ∧
      (a.ticks < b.ticks ∨ a.ticks = b.ticks ∧ a.worst ≤ b.worst) := by
  change key a ≤ key b ↔ _
  simp only [key, Prod.Lex.toLex_le_toLex]

/-- [proved-derived; formal-checked] **`⊕` is monotone in the lexicographic order.** -/
theorem plus_le_plus_right {a b : ExpectedCapture} (h : a ≤ b) (c : ExpectedCapture) :
    a + c ≤ b + c := by
  rw [le_iff] at h ⊢
  simp only [add_uncaptured, add_ticks, add_worst]
  rcases h with h | ⟨h1, h | ⟨h2, h3⟩⟩
  · left; omega
  · right; exact ⟨by omega, Or.inl (by omega)⟩
  · right; exact ⟨by omega, Or.inr ⟨by omega, max_le_max h3 le_rfl⟩⟩

/-- [proved-derived; formal-checked] **The shift is monotone in the lexicographic order.** -/
theorem shift_le_shift (n : ℕ) {a b : ExpectedCapture} (h : a ≤ b) : shift n a ≤ shift n b := by
  rw [le_iff] at h ⊢
  simp only [shift]
  rcases h with h | ⟨h1, h | ⟨h2, h3⟩⟩
  · left; exact h
  · right; exact ⟨h1, Or.inl (by omega)⟩
  · right
    refine ⟨h1, Or.inr ⟨by omega, ?_⟩⟩
    rw [h1]
    split_ifs
    · omega
    · exact le_rfl

/-- [proved-derived; formal-checked] **The recursion's step is an equality:** the least `⊕` of two
independent classes' choices is the `⊕` of each class's least. -/
theorem isLeast_plus {A B : Set ExpectedCapture} {a b : ExpectedCapture} (ha : IsLeast A a)
    (hb : IsLeast B b) : IsLeast (Set.image2 (· + ·) A B) (a + b) := by
  refine ⟨Set.mem_image2_of_mem ha.1 hb.1, ?_⟩
  rintro _ ⟨x, hx, y, hy, rfl⟩
  calc a + b ≤ x + b := plus_le_plus_right (ha.2 hx) b
    _ = b + x := plus_comm _ _
    _ ≤ y + x := plus_le_plus_right (hb.2 hy) x
    _ = x + y := plus_comm _ _

end ExpectedCapture

end Expected

/-! ## 6. A finer grain never raises the least capture -/

section Grain

variable {Zc Zf Uc Uf Wc Wf : Type*}

/-- [proved-derived; formal-checked] **The coarse basins embed level by level.** Let `e` embed the
coarse states and `ι` the coarse moves into the fine terrain, so that capture is read alike
(`z ∈ target_c ⇒ e z ∈ target_f`) and every fine reply to an embedded move is the embedding of a
coarse reply (`∀ w′, ∃ w, T_f (e z) (ι u) w′ = e (T_c z u w)`). Then `e(C_n^c) ⊆ C_n^f` at
every `n`. -/
theorem finer_grain_basin (Tc : Zc → Uc → Wc → Zc) (Tf : Zf → Uf → Wf → Zf) {targetc : Set Zc}
    {targetf : Set Zf} (e : Zc → Zf) (ι : Uc → Uf) (htarget : ∀ z ∈ targetc, e z ∈ targetf)
    (hmove : ∀ z u w', ∃ w, Tf (e z) (ι u) w' = e (Tc z u w)) :
    ∀ n, ∀ z ∈ captureBasin (Pre Tc) targetc n, e z ∈ captureBasin (Pre Tf) targetf n := by
  intro n
  induction n with
  | zero => exact htarget
  | succ n ih =>
    rintro z (hz | ⟨u, hu⟩)
    · exact Or.inl (ih z hz)
    · refine Or.inr ⟨ι u, fun w' => ?_⟩
      obtain ⟨w, hw⟩ := hmove z u w'
      rw [hw]
      exact ih _ (hu w)

/-- [proved-derived; formal-checked] **A finer grain never raises the least capture** (atlas
`pursuit.move-set`): under the embedding hypotheses of `finer_grain_basin`,
`τ_f (e z) ≤ τ_c z` at every coarse state. -/
theorem finer_grain_least_capture (Tc : Zc → Uc → Wc → Zc) (Tf : Zf → Uf → Wf → Zf)
    {targetc : Set Zc} {targetf : Set Zf} (e : Zc → Zf) (ι : Uc → Uf)
    (htarget : ∀ z ∈ targetc, e z ∈ targetf)
    (hmove : ∀ z u w', ∃ w, Tf (e z) (ι u) w' = e (Tc z u w)) (z : Zc) :
    leastCapture Tf targetf (e z) ≤ leastCapture Tc targetc z := by
  induction h : leastCapture Tc targetc z using ENat.recTopCoe with
  | top => exact le_top
  | coe m =>
    rw [leastCapture_le_iff]
    exact finer_grain_basin Tc Tf e ι htarget hmove m z
      ((leastCapture_le_iff Tc targetc z m).1 h.le)

/-- [proved-derived; formal-checked] **More moves never raise the least capture** (the record of
September 28, "the diameter depends on which moves are elementary"): on one terrain, if the moves
`Uc` embed into `Uf` with the same transitions, `τ_f z ≤ τ_c z`. -/
theorem more_moves_least_capture {Z : Type*} (Tc : Z → Uc → Wc → Z) (Tf : Z → Uf → Wc → Z)
    (target : Set Z) (ι : Uc → Uf) (hmove : ∀ z u w, Tf z (ι u) w = Tc z u w) (z : Z) :
    leastCapture Tf target z ≤ leastCapture Tc target z :=
  finer_grain_least_capture Tc Tf id ι (fun _ h => h) (fun z u w => ⟨w, hmove z u w⟩) z

/-! The lattice's embedding `g ↦ k·g`: a motion `(X, V)` at grain `g` goes to `(kX, kV)`, and every
bound the move set reads scales by `k²` with `k²⌊b⌋ ≤ ⌊k²b⌋`. -/

/-- [proved-standard; formal-checked] **A floored bound scales under the floor:**
`k²⌊b⌋ ≤ ⌊k²b⌋`. -/
theorem grain_floor_scale {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    [FloorRing α] (k : ℤ) (b : α) : k ^ 2 * ⌊b⌋ ≤ ⌊(k : α) ^ 2 * b⌋ := by
  rw [Int.le_floor]
  push_cast
  exact mul_le_mul_of_nonneg_left (Int.floor_le b) (sq_nonneg _)

/-- [proved-standard; formal-checked] The quadrance scales by `k²`: `⟨kV, kV⟩ = k²⟨V, V⟩`. -/
theorem quadrance_scale (k : ℤ) (a : GaussianInt) :
    quadrance ((k : GaussianInt) * a) = k ^ 2 * quadrance a := by
  simp only [quadrance, dot, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
  ring

/-- [proved-derived; formal-checked] **The embedding keeps every quadrance bound** of the move set
(the speed cap, the traction disk on a class, the capture disk): if `⟨V, V⟩ ≤ ⌊g²b⌋` at grain `g`
then `⟨kV, kV⟩ ≤ ⌊(kg)²b⌋` at grain `kg`. -/
theorem grain_bound_scale {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    [FloorRing α] (k g : ℤ) (b : α) {a : GaussianInt}
    (h : quadrance a ≤ ⌊(g : α) ^ 2 * b⌋) :
    quadrance ((k : GaussianInt) * a) ≤ ⌊((k * g : ℤ) : α) ^ 2 * b⌋ := by
  rw [quadrance_scale]
  calc k ^ 2 * quadrance a ≤ k ^ 2 * ⌊(g : α) ^ 2 * b⌋ :=
        mul_le_mul_of_nonneg_left h (sq_nonneg k)
    _ ≤ ⌊(k : α) ^ 2 * ((g : α) ^ 2 * b)⌋ := grain_floor_scale k _
    _ = ⌊((k * g : ℤ) : α) ^ 2 * b⌋ := by push_cast; ring_nf

/-- [proved-standard; formal-checked] **The embedding keeps the cell and the walls:** for `k > 0`,
the class read at `⌊kX/(kg)⌋` is the one read at `⌊X/g⌋`, and `0 ≤ X ≤ gL` gives
`0 ≤ kX ≤ (kg)L`. -/
theorem grain_cell_scale {k : ℤ} (hk : 0 < k) (X g L : ℤ) :
    k * X / (k * g) = X / g ∧ (0 ≤ X → X ≤ g * L → 0 ≤ k * X ∧ k * X ≤ k * g * L) := by
  refine ⟨Int.mul_ediv_mul_of_pos X g hk, fun h0 h1 => ⟨mul_nonneg hk.le h0, ?_⟩⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 hk.le

/-- [proved-standard; formal-checked] **The embedding keeps the move's change and its kind's
integer tests:** `(kV′) − (kV) = k(V′ − V)`, `⟨kv, kΔ⟩ = k²⟨v, Δ⟩`, `det(kv, kΔ) = k² det(v, Δ)`. -/
theorem grain_move_scale (k : ℤ) (m : MovePair) :
    (MovePair.mk ((k : GaussianInt) * m.before) ((k : GaussianInt) * m.after)).change =
        (k : GaussianInt) * m.change ∧
      dot ((k : GaussianInt) * m.before) ((k : GaussianInt) * m.change) =
        k ^ 2 * dot m.before m.change ∧
      det ((k : GaussianInt) * m.before) ((k : GaussianInt) * m.change) =
        k ^ 2 * det m.before m.change := by
  refine ⟨by simp only [MovePair.change, mul_sub], ?_, ?_⟩ <;>
  · simp only [dot, det, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
    ring

end Grain

end Holonics.Geometry.ChaseConsumer
