import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import Holonics.Foundation.ContinuingTower

/-!
# The topological receiver: a filtration, its persistence pairing, and linking from an embedding

[definition] This owner states the laws the Rust module
`crates/holonic-engine/src/topological_receiver.rs` implements. It is receiver **R5** of
`docs/plans/THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT.md` and the topological share of
**B7** in `docs/plans/THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md`. Four things are stated,
in this order.

1. **A filtration is a functor from an ordered index to subcomplexes, and it *is* a `Tower` — on
   the order dual.** `Filtration` is a monotone family of subsets; `Filtration.toTower` exhibits it
   as a `ContinuingTower.Tower` over `Indexᵒᵈ` whose `restrict` is the inclusion of an earlier
   subcomplex into a later one. **It does not fit on the index order itself**, and the reason is
   structural rather than notational: `Tower.restrict` transports a *finer* face to a *coarser*
   one, contravariantly in the index, while a filtration's only transport is the inclusion, which
   is covariant. Reversing the index is exactly the coercion that makes the two agree, and it is
   not free of content — under it the induced maps on homology run from the coarse index to the
   fine one, which is why `PersistenceModule` below is stated on the filtration's own order and
   not on the tower's.

2. **Induced maps on homology are functorial, and the persistent rank shrinks along the order.**
   `PersistenceModule` carries the transport with `map_id` and `map_comp`;
   `persistentRange_comp`, `persistentRange_le_left` and `persistentRange_le_right` are the two
   monotonicities as submodule inclusions, and `persistentRank_le_left` / `persistentRank_le_right`
   are their finite-dimensional numeric shadows.

3. **The pairing is determined by the persistent ranks** — the elder-rule uniqueness this file can
   prove. `multiplicity_eq` is the exact inclusion–exclusion

   ```text
   μ(b,d) = β^{b+1,d} − β^{b,d} − β^{b+1,d+1} + β^{b,d+1}
   ```

   over a finite bar population, and `multiplicity_eq_of_rank_eq` and `bornAt_eq_of_rank_eq` draw
   the consequence: **two pairings with the same persistent ranks are the same pairing**, so the
   pairing a reduction returns is independent of the reduction, of its pivot choices and of every
   tie-break inside it. That is the content of the elder rule that does not depend on the interval
   decomposition theorem, which this file does not prove.

4. **Linking from an embedding, with what is proved separated from what is not.** A crossing
   carries the two tangents and which strand is over; its sign is the classical
   `sgn det[t_over, t_under, w]`. Proved here:

   * `linkingTotal_comm` — `lk(a,b) = lk(b,a)`, unconditionally, because the sign does not read
     which curve was named first;
   * `linkingOver_add_linkingUnder` — the two half-sums partition the total;
   * `Crossing.sign_neg_direction` and `linkingTotal_neg_direction` — viewing the diagram from the
     other side swaps every over and under *and* negates every determinant, so **every sign is
     unmoved**;
   * `Crossing.sign_smul_direction` and `linkingTotal_smul_direction` — a positive rescaling of the
     declared direction moves nothing;
   * `HalvesAgree → linkingNumber = linkingOver` (`linking_is_an_integer`) and
     `HalvesAgree → Even linkingTotal` (`linkingTotal_even_of_halvesAgree`).

   Not proved here, and said so: `HalvesAgree` itself is the classical evenness of the signed
   crossing count between two components (Seifert), and `LinkingIsProjectionInvariant` is the
   classical invariance under a change of admissible projection. Both are `Prop`s, neither is an
   `axiom`, and the Rust owner **discharges the first computationally at every reading** —
   `TopologicalError::LinkingHalvesDisagree` names both half-sums if it ever fails — and **tests
   the second** across a declared candidate family.

   [counterexample] The projected writhe is given **no** invariance statement, and
   `projectedWrithe_is_not_projection_invariant` says why: the would-be invariance is false, with a
   finite exact witness — one direction under which a single positive self-crossing stands and one
   under which the curve presents none, so the projected writhes are `1` and `0`.
   `topological_receiver/tests.rs::the_projected_writhe_is_not_projection_invariant` is the same
   counterexample carried by an explicit closed polygon with exact rational vertices, where the two
   crossing populations are *computed* from two admissible directions rather than declared. The
   averaged writhe is a different object and neither owner claims it.

[definition] `HolonicsResearch/Millennium/Crossings.lean` already owns the *combinatorial* arm:
a finite table of addressed signed crossings with `net`, `total` and `linkingNet`, and its own
boundary clause — *"No link appears either. The crossing population is a finite table of addressed
signed crossings. This file builds no planar diagram … no projection of any curve in `ℚ³` is
computed anywhere in this file."* This file supplies exactly that missing half: the sign of a
crossing **derived from an embedding and a declared rational projection direction**. Nothing here
duplicates `net`, `total` or the blindness theorems, which remain that file's.

Rust owner: `crates/holonic-engine/src/topological_receiver.rs`
(`ApertureFiltration`, `FiltrationOrder`, `OrderLaw`, `persistence`, `PersistenceReading`,
`persistent_rank`, `community_persistence`, `integral_profile`, `Crossing`, `linking_number`,
`projected_writhe`, `contact_loops`, `knot_like_reading`).
-/

noncomputable section

namespace Holonics.Foundation.TopologicalReceiver

open Finset

universe u v w

/-! ## 1. The filtration, and the tower it is -/

/-- [definition] A **filtration**: a monotone family of subsets of a cell population, indexed by an
ordered index. The order is the exact aperture order; the subsets are the sublevel subcomplexes.

Rust counterpart: `topological_receiver.rs::ApertureFiltration` together with
`FiltrationOrder`, whose `support_before` is `carrier` at one index. -/
structure Filtration (Index : Type u) [Preorder Index] (Cell : Type v) where
  /-- The subcomplex standing at one index. -/
  carrier : Index → Set Cell
  /-- Nothing ever leaves: the family is monotone in the index. -/
  mono : ∀ {i j : Index}, i ≤ j → carrier i ⊆ carrier j

namespace Filtration

variable {Index : Type u} [Preorder Index] {Cell : Type v}

/-- [definition] Every sublevel set is closed under taking faces, which is what makes it a
subcomplex rather than a set of cells. `face c` is the face set of `c`.

Rust counterpart: `FiltrationOrder::found`'s refusal
`TopologicalError::OrderIsNotAFiltration`, which names the cell and the face that was not
earlier. -/
def FaceClosed (F : Filtration Index Cell) (face : Cell → Set Cell) : Prop :=
  ∀ (i : Index) (c : Cell), c ∈ F.carrier i → face c ⊆ F.carrier i

/-- [proved-derived; formal-checked] **A filtration is a `ContinuingTower.Tower` on the order
dual, with `restrict` the inclusion.**

`Tower.restrict` carries a face at a *finer* index to the coarser index it presents, which is
contravariant in the index; a filtration's only transport is the inclusion of an earlier
subcomplex into a later one, which is covariant. Dualizing the index is exactly the coercion
between the two, and with it the two laws hold on the nose. -/
def toTower (F : Filtration Index Cell) :
    ContinuingTower.Tower.{u, v} (OrderDual Index) where
  Face := fun i => {c : Cell // c ∈ F.carrier (OrderDual.ofDual i)}
  restrict := fun {_ _} h x => ⟨x.1, F.mono h x.2⟩
  restrict_refl := fun _ _ => rfl
  restrict_trans := fun _ _ _ => rfl

/-- [proved-derived; formal-checked] The tower's transport really is the inclusion: it moves no
cell. -/
@[simp]
theorem toTower_restrict (F : Filtration Index Cell) {i j : OrderDual Index} (h : i ≤ j)
    (x : (F.toTower).Face j) : ((F.toTower).restrict h x).1 = x.1 := rfl

/-- [proved-derived; formal-checked] The inclusion is injective, so no cell is lost or merged by
the transport. This is the sense in which a filtration is a tower of *subobjects* and not merely a
tower. -/
theorem toTower_restrict_injective (F : Filtration Index Cell) {i j : OrderDual Index}
    (h : i ≤ j) : Function.Injective ((F.toTower).restrict h) := by
  intro x y hxy
  apply Subtype.ext
  have left := toTower_restrict F h x
  have right := toTower_restrict F h y
  rw [← left, ← right, hxy]

end Filtration

/-! ## 2. Persistence modules: functoriality and the persistent rank -/

/-- [definition] A **persistence module** over a field: a family of subspaces of one ambient space
together with the transport the filtration induces, and the two functoriality laws. The homology
of a filtration at one grade is such a family; nothing below needs it to be homology.

Rust counterpart: `topological_receiver.rs::PersistenceReading`, whose `persistent_rank` is
`persistentRank` below. -/
structure PersistenceModule (K : Type u) [Field K] (Index : Type v) [Preorder Index]
    (M : Type w) [AddCommGroup M] [Module K M] where
  /-- The space standing at one index. -/
  space : Index → Submodule K M
  /-- The map the inclusion of subcomplexes induces. -/
  map : ∀ {i j : Index}, i ≤ j → space i →ₗ[K] space j
  /-- Transporting along the identity refinement changes nothing. -/
  map_id : ∀ (i : Index) (x : space i), map (le_refl i) x = x
  /-- Transporting twice is transporting once along the composite. -/
  map_comp : ∀ {i j k : Index} (hij : i ≤ j) (hjk : j ≤ k) (x : space i),
    map hjk (map hij x) = map (le_trans hij hjk) x

namespace PersistenceModule

variable {K : Type u} [Field K] {Index : Type v} [Preorder Index]
variable {M : Type w} [AddCommGroup M] [Module K M] (P : PersistenceModule K Index M)

/-- [definition] The image of the transport from `i` to `j`: the classes born at or before `i` and
still alive at `j`. Its dimension is the persistent Betti number `β^{i,j}`. -/
def persistentRange {i j : Index} (h : i ≤ j) : Submodule K (P.space j) :=
  LinearMap.range (P.map h)

/-- [proved-derived; formal-checked] **Functoriality, as a statement about the images.** The
transport from `i` to `k` factors through the transport from `i` to `j`, so its image is the image
of the latter carried forward. -/
theorem persistentRange_comp {i j k : Index} (hij : i ≤ j) (hjk : j ≤ k) :
    P.persistentRange (le_trans hij hjk)
      = (P.persistentRange hij).map (P.map hjk) := by
  ext x
  simp only [persistentRange, LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨P.map hij y, ⟨y, rfl⟩, P.map_comp hij hjk y⟩
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, (P.map_comp hij hjk z).symm⟩

/-- [proved-derived; formal-checked] **A longer transport lands inside a later one.** Starting
earlier cannot reach further: the image from `i` to `k` sits inside the image from `j` to `k`. -/
theorem persistentRange_le_right {i j k : Index} (hij : i ≤ j) (hjk : j ≤ k) :
    P.persistentRange (le_trans hij hjk) ≤ P.persistentRange hjk := by
  rintro x ⟨y, rfl⟩
  exact ⟨P.map hij y, P.map_comp hij hjk y⟩

/-- [proved-derived; formal-checked] The image at `i` is everything, so the persistent range of the
identity refinement is the whole space. -/
theorem persistentRange_self (i : Index) :
    P.persistentRange (le_refl i) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  exact ⟨x, P.map_id i x⟩

variable [FiniteDimensional K M]

/-- [definition] The **persistent Betti number** `β^{i,j} = rank(H(K_i) → H(K_j))`. -/
def persistentRank {i j : Index} (h : i ≤ j) : ℕ :=
  Module.finrank K (P.persistentRange h)

/-- [proved-derived; formal-checked] **The rank never grows along the order.** Carrying the image
further forward can only lose dimension. -/
theorem persistentRank_le_left {i j k : Index} (hij : i ≤ j) (hjk : j ≤ k) :
    P.persistentRank (le_trans hij hjk) ≤ P.persistentRank hij := by
  have : P.persistentRank (le_trans hij hjk)
      = Module.finrank K ((P.persistentRange hij).map (P.map hjk)) := by
    rw [persistentRank, P.persistentRange_comp hij hjk]
  rw [this]
  exact Submodule.finrank_map_le _ _

/-- [proved-derived; formal-checked] **Starting earlier never reaches more.** -/
theorem persistentRank_le_right {i j k : Index} (hij : i ≤ j) (hjk : j ≤ k) :
    P.persistentRank (le_trans hij hjk) ≤ P.persistentRank hjk :=
  Submodule.finrank_mono (P.persistentRange_le_right hij hjk)

end PersistenceModule

/-! ## 3. The pairing is determined by the persistent ranks -/

/-- [definition] One **bar** of a barcode: born at an index, dead at an index, or essential.

Rust counterpart: `topological_receiver.rs::PersistencePair`, whose `death_position` is `none`
exactly for an essential class. -/
structure Bar where
  /-- The index at which the class appears. -/
  birth : ℕ
  /-- The index at which it is killed, or `none` when it is never killed. -/
  death : Option ℕ
  deriving DecidableEq

namespace Bar

/-- Still alive at the index `t`: an essential bar always is. -/
def alive (b : Bar) (t : ℕ) : Bool :=
  match b.death with
  | none => true
  | some d => t ≤ d

@[simp] theorem alive_none (β t : ℕ) : (Bar.mk β none).alive t = true := rfl

@[simp] theorem alive_some (β d t : ℕ) :
    (Bar.mk β (some d)).alive t = decide (t ≤ d) := rfl

@[simp] theorem alive_zero (b : Bar) : b.alive 0 = true := by
  obtain ⟨β, δ⟩ := b
  cases δ <;> simp

end Bar

variable {ι : Type*} [Fintype ι]

/-- [definition] The **persistent Betti number of a barcode**: how many bars are born before `s`
and alive at `t`. This is the reading a persistence module's `persistentRank` returns, expressed
on the bars themselves.

Rust counterpart: `PersistenceReading::persistent_rank`. -/
def rank (bar : ι → Bar) (s t : ℕ) : ℕ :=
  (univ.filter fun i => (bar i).birth < s ∧ (bar i).alive t).card

/-- [definition] How many bars are born exactly at `b` and are still alive at `t`. -/
def bornAtAlive (bar : ι → Bar) (b t : ℕ) : ℕ :=
  (univ.filter fun i => (bar i).birth = b ∧ (bar i).alive t).card

/-- [definition] How many bars are born exactly at `b` and die exactly at `d`. -/
def multiplicity (bar : ι → Bar) (b d : ℕ) : ℕ :=
  (univ.filter fun i => (bar i).birth = b ∧ (bar i).death = some d).card

/-- [definition] How many bars are born exactly at `b`, essential or not. -/
def bornAt (bar : ι → Bar) (b : ℕ) : ℕ :=
  (univ.filter fun i => (bar i).birth = b).card

/-- A finite population splitting into two disjoint conditions splits its count. -/
private theorem card_split {p q r : ι → Prop} [DecidablePred p] [DecidablePred q]
    [DecidablePred r] (hsplit : ∀ i, p i ↔ (q i ∨ r i)) (hdisj : ∀ i, ¬ (q i ∧ r i)) :
    (univ.filter p).card = (univ.filter q).card + (univ.filter r).card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext i
    simp only [mem_union, mem_filter, mem_univ, true_and]
    exact hsplit i
  · rw [Finset.disjoint_left]
    intro i hi hj
    simp only [mem_filter, mem_univ, true_and] at hi hj
    exact hdisj i ⟨hi, hj⟩

/-- [proved-derived; formal-checked] **Raising the birth cut by one admits exactly the bars born
there.** -/
theorem rank_succ (bar : ι → Bar) (b t : ℕ) :
    rank bar (b + 1) t = rank bar b t + bornAtAlive bar b t := by
  classical
  refine card_split (fun i => ?_) (fun i => ?_)
  · by_cases h : (bar i).alive t = true
    · simp only [h, and_true]
      omega
    · simp [h]
  · rintro ⟨⟨h1, _⟩, ⟨h2, _⟩⟩
    omega

/-- [proved-derived; formal-checked] **Among the bars born at one index, raising the death cut by
one removes exactly those that die there.** An essential bar is alive at both cuts and cancels. -/
theorem bornAtAlive_succ (bar : ι → Bar) (b d : ℕ) :
    bornAtAlive bar b d = multiplicity bar b d + bornAtAlive bar b (d + 1) := by
  classical
  refine card_split (fun i => ?_) (fun i => ?_)
  · rcases hb : bar i with ⟨β, δ⟩
    cases δ with
    | none => simp
    | some dd => simp; omega
  · rcases hb : bar i with ⟨β, δ⟩
    cases δ with
    | none => simp
    | some dd => simp; omega

/-- [proved-derived; formal-checked] **The pairing is an inclusion–exclusion of four persistent
ranks.** Stated without subtraction, so it is an identity of natural numbers:

```text
β^{b+1,d} + β^{b,d+1} = β^{b,d} + β^{b+1,d+1} + μ(b,d)
```

The first difference isolates the bars born exactly at `b`; the second isolates, among those, the
ones whose death is exactly `d`, with an essential bar cancelling in both terms. Nothing about the
algorithm that produced the bars enters. -/
theorem rank_pairing (bar : ι → Bar) (b d : ℕ) :
    rank bar (b + 1) d + rank bar b (d + 1)
      = rank bar b d + rank bar (b + 1) (d + 1) + multiplicity bar b d := by
  have first := rank_succ bar b d
  have second := rank_succ bar b (d + 1)
  have third := bornAtAlive_succ bar b d
  omega

/-- [proved-derived; formal-checked] The same identity written as the classical signed
inclusion–exclusion

```text
μ(b,d) = β^{b+1,d} − β^{b,d} − β^{b+1,d+1} + β^{b,d+1}.
```
-/
theorem multiplicity_eq (bar : ι → Bar) (b d : ℕ) :
    (multiplicity bar b d : ℤ)
      = (rank bar (b + 1) d : ℤ) - (rank bar b d : ℤ)
        - (rank bar (b + 1) (d + 1) : ℤ) + (rank bar b (d + 1) : ℤ) := by
  have := rank_pairing bar b d
  omega

/-- [proved-derived; formal-checked] **Births are determined by the persistent ranks too.**
Every bar is alive at index `0`, so the difference of two ranks at `t = 0` counts births. -/
theorem bornAt_eq (bar : ι → Bar) (b : ℕ) :
    bornAt bar b + rank bar b 0 = rank bar (b + 1) 0 := by
  classical
  have step := rank_succ bar b 0
  have same : bornAtAlive bar b 0 = bornAt bar b := by
    unfold bornAtAlive bornAt
    congr 1
    ext i
    simp
  omega

/-- [proved-derived; formal-checked] **Pairing uniqueness.** Two barcodes with the same persistent
rank function have the same pairing, bar for bar.

This is the elder rule at the level that does not need the interval decomposition theorem: the
reduction may choose its pivots however it likes, and it may break an exact tie however it likes,
because the multiset of pairs it returns is a function of the persistent ranks alone. -/
theorem multiplicity_eq_of_rank_eq {ι' : Type*} [Fintype ι']
    (bar : ι → Bar) (bar' : ι' → Bar)
    (h : ∀ s t, rank bar s t = rank bar' s t) (b d : ℕ) :
    multiplicity bar b d = multiplicity bar' b d := by
  have first := rank_pairing bar b d
  have second := rank_pairing bar' b d
  rw [h, h, h, h] at first
  omega

/-- [proved-derived; formal-checked] And the same for the births. -/
theorem bornAt_eq_of_rank_eq {ι' : Type*} [Fintype ι']
    (bar : ι → Bar) (bar' : ι' → Bar)
    (h : ∀ s t, rank bar s t = rank bar' s t) (b : ℕ) :
    bornAt bar b = bornAt bar' b := by
  have first := bornAt_eq bar b
  have second := bornAt_eq bar' b
  rw [h, h] at first
  omega


/-! ## 4. Crossings, linking and the projected writhe -/

/-- [definition] A place, or a tangent, in exact rational three-space. -/
abbrev Place := Fin 3 → ℚ

/-- [definition] `det[a b c]`, written out. Over `ℚ` this is the only geometric primitive the sign
of a crossing needs. -/
def det3 (a b c : Place) : ℚ :=
  a 0 * (b 1 * c 2 - b 2 * c 1)
    - a 1 * (b 0 * c 2 - b 2 * c 0)
    + a 2 * (b 0 * c 1 - b 1 * c 0)

theorem det3_swap (a b c : Place) : det3 b a c = - det3 a b c := by
  simp only [det3]; ring

@[simp]
theorem det3_neg_right (a b c : Place) : det3 a b (fun i => - c i) = - det3 a b c := by
  simp only [det3]; ring

@[simp]
theorem det3_smul_right (a b c : Place) (r : ℚ) :
    det3 a b (fun i => r * c i) = r * det3 a b c := by
  simp only [det3]; ring

/-- [definition] The exact sign of a rational. No float and no tolerance. -/
def sgn (x : ℚ) : ℤ := if 0 < x then 1 else if x < 0 then -1 else 0

@[simp] theorem sgn_neg (x : ℚ) : sgn (-x) = - sgn x := by
  unfold sgn
  rcases lt_trichotomy x 0 with h | h | h
  · rw [if_pos (by linarith : (0 : ℚ) < -x), if_neg (by linarith : ¬ (0 : ℚ) < x), if_pos h]
    norm_num
  · subst h; norm_num
  · rw [if_neg (by linarith : ¬ (0 : ℚ) < -x), if_pos (by linarith : -x < 0), if_pos h]

theorem sgn_pos_smul {r : ℚ} (hr : 0 < r) (x : ℚ) : sgn (r * x) = sgn x := by
  unfold sgn
  rcases lt_trichotomy x 0 with h | h | h
  · have : r * x < 0 := mul_neg_of_pos_of_neg hr h
    simp [h, this, not_lt.mpr this.le, not_lt.mpr h.le]
  · simp [h]
  · have : 0 < r * x := mul_pos hr h
    simp [h, this]

/-- [definition] **One crossing of a diagram, read off an embedding.** The tangent of the strand
that passes over, the tangent of the strand that passes under, and which of the two named curves
the over strand belongs to. The last field is the only place a curve's *name* appears, and the
sign below does not read it — which is the whole reason `lk(a,b) = lk(b,a)` is unconditional.

Rust counterpart: `topological_receiver.rs::Crossing`, founded by `crossing_of`, which refuses
every degenerate configuration by name rather than perturbing it. -/
structure Crossing where
  /-- The tangent of the strand nearer the viewer. -/
  overTangent : Place
  /-- The tangent of the strand further from the viewer. -/
  underTangent : Place
  /-- `true` when the first named curve carries the over strand. -/
  firstIsOver : Bool

namespace Crossing

/-- [definition] The classical crossing sign `sgn det[t_over, t_under, w]`. -/
def sign (w : Place) (c : Crossing) : ℤ := sgn (det3 c.overTangent c.underTangent w)

/-- [definition] The same crossing viewed from the other side: over and under exchange, and the
crossing now belongs to the other curve's over-arm. -/
def reverse (c : Crossing) : Crossing :=
  ⟨c.underTangent, c.overTangent, !c.firstIsOver⟩

/-- [definition] The same crossing with the two curves renamed. The geometry is untouched. -/
def swapCurves (c : Crossing) : Crossing :=
  ⟨c.overTangent, c.underTangent, !c.firstIsOver⟩

/-- [proved-derived; formal-checked] **Viewing the diagram from the other side moves no sign.**
Reversing the direction exchanges over and under, which negates the determinant, and negates the
direction, which negates it again. -/
@[simp]
theorem sign_neg_direction (w : Place) (c : Crossing) :
    (c.reverse).sign (fun i => - w i) = c.sign w := by
  show sgn (det3 c.underTangent c.overTangent (fun i => - w i))
      = sgn (det3 c.overTangent c.underTangent w)
  exact congrArg sgn (by simp only [det3]; ring)

/-- [proved-derived; formal-checked] **A positive rescaling of the declared direction moves
nothing.** The direction is a direction and not a length. -/
theorem sign_smul_direction {r : ℚ} (hr : 0 < r) (w : Place) (c : Crossing) :
    c.sign (fun i => r * w i) = c.sign w := by
  show sgn (det3 c.overTangent c.underTangent (fun i => r * w i))
      = sgn (det3 c.overTangent c.underTangent w)
  rw [show det3 c.overTangent c.underTangent (fun i => r * w i)
      = r * det3 c.overTangent c.underTangent w from by simp only [det3]; ring]
  exact sgn_pos_smul hr _

/-- [proved-derived; formal-checked] Renaming the curves does not move the sign: the sign never
reads `firstIsOver`. -/
@[simp]
theorem sign_swapCurves (w : Place) (c : Crossing) : (c.swapCurves).sign w = c.sign w := rfl

end Crossing

variable {κ : Type*} [Fintype κ]

/-- [definition] The **total signed crossing count** between two curves under one declared
direction.

Rust counterpart: `LinkingReading::total_signed`. -/
def linkingTotal (cross : κ → Crossing) (w : Place) : ℤ :=
  ∑ k, (cross k).sign w

/-- [definition] The signed count over the crossings at which the **first** curve passes over. -/
def linkingOver (cross : κ → Crossing) (w : Place) : ℤ :=
  ∑ k ∈ univ.filter fun k => (cross k).firstIsOver, (cross k).sign w

/-- [definition] The signed count over the crossings at which the **second** curve passes over. -/
def linkingUnder (cross : κ → Crossing) (w : Place) : ℤ :=
  ∑ k ∈ univ.filter fun k => ¬ (cross k).firstIsOver, (cross k).sign w

/-- [proved-derived; formal-checked] **The two half-sums partition the total.** -/
theorem linkingOver_add_linkingUnder (cross : κ → Crossing) (w : Place) :
    linkingOver cross w + linkingUnder cross w = linkingTotal cross w := by
  classical
  simpa [linkingOver, linkingUnder, linkingTotal] using
    Finset.sum_filter_add_sum_filter_not univ (fun k => (cross k).firstIsOver)
      (fun k => (cross k).sign w)

/-- [proved-derived; formal-checked] **`lk(a,b) = lk(b,a)`.** Renaming the two curves changes only
`firstIsOver`, which the sign does not read, so the total is literally the same sum. -/
theorem linkingTotal_comm (cross : κ → Crossing) (w : Place) :
    linkingTotal (fun k => (cross k).swapCurves) w = linkingTotal cross w := by
  simp [linkingTotal]

/-- [proved-derived; formal-checked] Renaming the curves exchanges the two half-sums, which is the
sense in which they are *halves* of one reading. -/
theorem linkingOver_swapCurves (cross : κ → Crossing) (w : Place) :
    linkingOver (fun k => (cross k).swapCurves) w = linkingUnder cross w := by
  simp [linkingOver, linkingUnder, Crossing.swapCurves, Crossing.sign]

/-- [proved-derived; formal-checked] **The total is unmoved by viewing the diagram from the other
side.** -/
theorem linkingTotal_neg_direction (cross : κ → Crossing) (w : Place) :
    linkingTotal (fun k => (cross k).reverse) (fun i => - w i) = linkingTotal cross w := by
  simp [linkingTotal]

/-- [proved-derived; formal-checked] **The total is unmoved by a positive rescaling of the declared
direction.** -/
theorem linkingTotal_smul_direction {r : ℚ} (hr : 0 < r) (cross : κ → Crossing) (w : Place) :
    linkingTotal cross (fun i => r * w i) = linkingTotal cross w := by
  simp [linkingTotal, Crossing.sign_smul_direction hr]

/-- [definition] **The classical agreement of the two half-sums.** For two closed curves in general
position this holds — it is the statement that the signed crossing count between two components is
even, equivalently that each half-sum computes the linking number — and it is **not proved here**:
this file builds no Seifert surface and no homology of a complement.

The Rust owner discharges it *computationally at every reading*: `linking_number` computes both
half-sums separately and refuses with `TopologicalError::LinkingHalvesDisagree`, naming both, if
they ever part. So the hypothesis of `linking_is_an_integer` is checked on every actual reading
rather than assumed. -/
def HalvesAgree (cross : κ → Crossing) (w : Place) : Prop :=
  linkingOver cross w = linkingUnder cross w

/-- [definition] The linking number as a rational: half the total signed crossing count. -/
def linkingNumber (cross : κ → Crossing) (w : Place) : ℚ :=
  (linkingTotal cross w : ℚ) / 2

/-- [proved-derived; formal-checked] **`lk(a,b) = lk(b,a)`, unconditionally.** -/
theorem linkingNumber_comm (cross : κ → Crossing) (w : Place) :
    linkingNumber (fun k => (cross k).swapCurves) w = linkingNumber cross w := by
  simp [linkingNumber, linkingTotal_comm]

/-- [conditional; formal-checked] **The linking number is an integer** — exactly the half-sum at
which the first curve passes over — whenever the two half-sums agree. -/
theorem linking_is_an_integer (cross : κ → Crossing) (w : Place)
    (h : HalvesAgree cross w) :
    linkingNumber cross w = (linkingOver cross w : ℚ) := by
  have total : linkingTotal cross w = 2 * linkingOver cross w := by
    rw [← linkingOver_add_linkingUnder cross w, ← h]; ring
  rw [linkingNumber, total]
  push_cast
  ring

/-- [conditional; formal-checked] Equivalently, the total signed crossing count is even. -/
theorem linkingTotal_even_of_halvesAgree (cross : κ → Crossing) (w : Place)
    (h : HalvesAgree cross w) : Even (linkingTotal cross w) := by
  refine ⟨linkingOver cross w, ?_⟩
  rw [← linkingOver_add_linkingUnder cross w, ← h]

/-- [open] **Invariance of the linking number under a change of admissible projection.**

Classically true; this file constructs no isotopy, no Reidemeister move and no diagram calculus,
so it is stated as a `Prop` and left unproved rather than assumed as an `axiom`. The Rust owner
tests it at every reading: `linking_under_directions` returns the reading under every declared
admissible candidate and `LinkingAcrossDirections::agree` says on the actual data whether they
agree, with the degenerate candidates returned by name rather than silently skipped. -/
def LinkingIsProjectionInvariant {κ' : Type*} [Fintype κ']
    (cross : κ → Crossing) (w : Place) (cross' : κ' → Crossing) (w' : Place) : Prop :=
  linkingTotal cross w = linkingTotal cross' w'

/-- [definition] **The projected writhe**: the same signed sum, taken over the self-crossings of
one closed curve under one declared direction. It is an exact integer *for that direction*.

No invariance statement accompanies it, and that omission is the content. The averaged writhe —
the mean of this count over the sphere of directions — is a real number and a different object,
and neither owner computes or claims it.
`topological_receiver/tests.rs::the_projected_writhe_is_not_projection_invariant` exhibits one
closed polygon with exact rational vertices whose projected writhes under two admissible
directions are `1` and `0`. -/
def projectedWrithe (self : κ → Crossing) (w : Place) : ℤ := linkingTotal self w

/-- [proved-derived; formal-checked] The projected writhe does inherit the two invariances the
sign itself has — reversal of the viewing side and positive rescaling — and no others. -/
theorem projectedWrithe_neg_direction (self : κ → Crossing) (w : Place) :
    projectedWrithe (fun k => (self k).reverse) (fun i => - w i) = projectedWrithe self w :=
  linkingTotal_neg_direction self w

/-- [counterexample; formal-checked] **The projected writhe is not invariant under a change of
admissible projection direction.**

The crossing population is itself a function of the declared direction: turning the diagram can
destroy a self-crossing outright, so the would-be invariance is not merely unproved here — it is
false, and the witness is finite and exact. One direction carries a single positive self-crossing
and another carries none at all, giving projected writhes `1` and `0`.

This is why the `LinkingIsProjectionInvariant`-shaped statement above has no writhe companion.

Rust counterpart:
`topological_receiver/tests.rs::the_projected_writhe_is_not_projection_invariant`, where the same
two values come from one explicit closed polygon with exact rational vertices whose crossing
populations are *computed* under two admissible directions rather than declared. -/
theorem projectedWrithe_is_not_projection_invariant :
    ∃ (w w' : Place) (self : Fin 1 → Crossing) (self' : Fin 0 → Crossing),
      projectedWrithe self w ≠ projectedWrithe self' w' := by
  refine ⟨![0, 0, 1], ![1, 0, 0], fun _ => ⟨![1, 0, 0], ![0, 1, 0], true⟩, Fin.elim0, ?_⟩
  simp [projectedWrithe, linkingTotal, Crossing.sign, det3, sgn]

/-! ## Kernel receipt

[definition] Every theorem this owner claims, checked against the kernel. Only `propext`,
`Classical.choice` and `Quot.sound` are acceptable; no `sorryAx` appears anywhere below. -/

section Audit

#print axioms Filtration.toTower
#print axioms Filtration.toTower_restrict
#print axioms Filtration.toTower_restrict_injective
#print axioms PersistenceModule.persistentRange_comp
#print axioms PersistenceModule.persistentRange_le_right
#print axioms PersistenceModule.persistentRange_self
#print axioms PersistenceModule.persistentRank_le_left
#print axioms PersistenceModule.persistentRank_le_right
#print axioms rank_succ
#print axioms bornAtAlive_succ
#print axioms rank_pairing
#print axioms multiplicity_eq
#print axioms bornAt_eq
#print axioms multiplicity_eq_of_rank_eq
#print axioms bornAt_eq_of_rank_eq
#print axioms det3_swap
#print axioms sgn_pos_smul
#print axioms Crossing.sign_neg_direction
#print axioms Crossing.sign_smul_direction
#print axioms Crossing.sign_swapCurves
#print axioms linkingOver_add_linkingUnder
#print axioms linkingTotal_comm
#print axioms linkingOver_swapCurves
#print axioms linkingTotal_neg_direction
#print axioms linkingTotal_smul_direction
#print axioms linkingNumber_comm
#print axioms linking_is_an_integer
#print axioms linkingTotal_even_of_halvesAgree
#print axioms projectedWrithe_neg_direction
#print axioms projectedWrithe_is_not_projection_invariant

end Audit

end Holonics.Foundation.TopologicalReceiver
