import Holonics.Foundation.HodgeReceiver
import Holonics.Foundation.Lineage

/-!
# The junction law: the tangential part is continuous, the normal part jumps, and the jump is the
source that lives on the joint

[definition] This owner states the law the Rust module
`crates/holonic-engine/src/junction_law.rs` implements. It is the junction half of item **T7** of
`docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`.

Nothing here founds a complex, a metric, a coboundary or a codifferential. Every statement is made
over `Foundation/HodgeReceiver.lean::WeightedComplex` — three consecutive grades of a finite
cochain complex over `ℚ` with a declared positive rational weight per cell — and over
`Foundation/Lineage.lean::AddressedPassage`, whose `Join` is the pullback this file identifies
with the joint of two charts.

## What a joint is, in each picture

* **Tower.** The joint of two charts is the pullback of their occurrence populations over the
  shared boundary. `join_is_exactly_the_compatible_pairs` proves that `AddressedPassage.Join` is
  *exactly* the set of compatible pairs — no more, and no fewer. Where the two charts share no
  boundary face at all the join is empty (`noSharedBoundary_isEmpty_join`); the span-level form of
  that statement is `Transport/WorldTube.lean::openGap_has_no_joined_occurrence` and the
  no-common-refinement case is `Foundation/ContinuingTower.lean::twoCharts_no_common_refinement`,
  whose connection is a `Transport/ContinuingTube.lean::Wormhole`.
* **Tube.** A valence-2 station is a serial join — `Transport/WorldTube.lean::ClockedSpan.comp`,
  whose occurrence type *is* `AddressedPassage.Join`. A **junction** is a station of valence ≥ 3.
* **Staircase.** A joint is a spline knot whose order is the lowest derivative that jumps. That
  object belongs to the jet tower of T8 and is not built here.

## The one law

With `d₀ : C^(k−1) → C^k` the coboundary and `codiff₀ = W₀⁻¹ d₀ᵀ W₁` its metric adjoint:

* **Tangential/intrinsic half.** `[[ι* u]] = 0`. Two side fields descend to one field on the union
  exactly when their jump on the shared cells vanishes (`descend_restricts_left`,
  `descend_restricts_right`, `no_descent_of_nonzero_jump`). Continuity of the pullback is not an
  extra hypothesis: it *is* being one cochain on the glued complex.
* **Normal/extrinsic half.** `[[n·flux]] = σ`. Splitting the flux cells into the two sides splits
  the divergence into the two sides' outward normal fluxes, and their sum — the jump — is exactly
  `codiff₀` of the whole flux (`normalJump_eq_divergence`). So the junction condition
  `Balanced` is exactly `codiff₀ f = σ` (`balanced_iff_divergence`).

Both halves are therefore `d₀` and its adjoint read at the interface, and nothing else.

`discrete_gauss` is the summation-by-parts identity the balance is integrated by, and `tellegen`
is that identity at a potential and a balanced flux: the junction's exact energy ledger. The
codimension-2 compatibility is `codiff_comp_zero` — `δ ∘ δ = 0` — and a source that does not close
around a vertex admits no interface flux at all (`no_interface_flux_for_a_nonclosing_source`); the
obstruction is returned, never repaired.

## Valence, Euler characteristic and the orientation bit

`chi_glue_along_zero` is `χ(A ∪_{S¹} B) = χ(A) + χ(B)` for any gluing locus of vanishing Euler
characteristic, and `each_junction_costs_one_euler` is its consequence: a surface assembled from
`n` pieces of `χ = −1` has `χ = −n`. Orientability is the extra `ℤ/2`:
`walkHolonomy_telescopes` proves that a consistent sign assignment forces holonomy `1` on every
closed dual walk, the obstruction is `Objects/Orientation.reversing_closed_walk_has_no_orientation`, and
`orientation_reversing_iff_odd` is the determinant `(−1)^k` of a circuit of `k` reflections. The
tube-level form of the same obstruction is
`Transport/ContinuingTube.lean::flipCircuit_carries_no_invariant_end`: no invariant end, hence no
global section, hence non-orientable.

## The instances

`snell_squared`, `no_transmitted_covector_beyond_the_critical_angle` (a finite Maxwell-type
interface: rational wave covectors, tangential continuity, the dispersion relation with declared
rational `n²`), `rankine_hugoniot_speed` with `lax_admissible_iff` (a scalar conservation law with
the exact polynomial Burgers flux) and `three_conormals_balance_iff` with
`four_conormals_balance_of_pairwise` (Plateau's tension balance at a junction line and at a
vertex). Each is exact over `ℚ`; none claims anything beyond its declared model.

Rust owner: `crates/holonic-engine/src/junction_law.rs`.
-/

noncomputable section

namespace Holonics.Transport.JunctionLaw

open Holonics.Foundation.HodgeReceiver
open Matrix Finset

universe u v w

/-! ## 1. The joint of two charts is the pullback of compatible pairs -/

section Joint

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- [definition] The compatible pairs of two addressed passages: a predecessor occurrence and a
successor occurrence whose shared boundary faces agree. -/
def CompatiblePairs (P : Holonics.AddressedPassage X Y)
    (Q : Holonics.AddressedPassage Y Z) : Type _ :=
  { pair : P.Occurrence × Q.Occurrence // P.target pair.1 = Q.source pair.2 }

/-- [proved-derived; formal-checked] **The joint of two charts is exactly the compatible pairs.**
`Foundation/Lineage.lean::AddressedPassage.Join` is the pullback: it carries no pair that fails the
joining equality, and it omits no pair that satisfies it. This is the tower picture's joint, and
`Transport/WorldTube.lean::ClockedSpan.comp` is the tube picture's valence-2 station built on the
same type. -/
def join_is_exactly_the_compatible_pairs (P : Holonics.AddressedPassage X Y)
    (Q : Holonics.AddressedPassage Y Z) :
    Holonics.AddressedPassage.Join P Q ≃ CompatiblePairs P Q where
  toFun joined := ⟨(joined.left, joined.right), joined.joins⟩
  invFun pair := ⟨pair.1.1, pair.1.2, pair.2⟩
  left_inv := by rintro ⟨left, right, joins⟩; rfl
  right_inv := by rintro ⟨⟨left, right⟩, joins⟩; rfl

/-- [proved-derived; formal-checked] **An open gap has no joint.** When no predecessor target is
any successor source the pullback is empty, so the comparison across the gap is undefined rather
than default. The span-level form is
`Transport/WorldTube.lean::openGap_has_no_joined_occurrence`; this is the statement one level down,
at the addressed passage the span is built from. -/
theorem noSharedBoundary_isEmpty_join (P : Holonics.AddressedPassage X Y)
    (Q : Holonics.AddressedPassage Y Z)
    (gap : ∀ predecessor successor, P.target predecessor ≠ Q.source successor) :
    IsEmpty (Holonics.AddressedPassage.Join P Q) := by
  constructor
  intro joined
  exact gap joined.left joined.right joined.joins

/-- [definition] The **valence** of a station: how many passages meet at it. A valence-2 station is
a serial join; a **junction** is a station of valence at least three. -/
def IsJunction (valence : ℕ) : Prop := 3 ≤ valence

theorem serial_station_is_not_a_junction : ¬ IsJunction 2 := by simp [IsJunction]

theorem trivalent_station_is_a_junction : IsJunction 3 := by simp [IsJunction]

end Joint

/-! ## 2. The interface, and the two halves of the junction law -/

section Interface

variable {p q r : ℕ}

/-- [definition] A flux cochain restricted to one side of the interface. -/
def restrictTo (S : Finset (Fin q)) (f : Fin q → ℚ) : Fin q → ℚ :=
  fun e => if e ∈ S then f e else 0

/-- [definition] **A declared codimension-1 interface**: the flux-carrying cells split into the two
sides it separates. The interface itself is the population of lower-grade cells at which the two
sides' normal fluxes are read; it is not a third side. -/
structure SideSplit (q : ℕ) where
  /-- The flux cells lying on one side. -/
  left : Finset (Fin q)
  /-- The flux cells lying on the other. -/
  right : Finset (Fin q)
  /-- No cell lies on both sides. -/
  disjoint : Disjoint left right
  /-- Every cell lies on one. -/
  covers : left ∪ right = Finset.univ

namespace SideSplit

variable (I : SideSplit q)

/-- [proved-derived; formal-checked] The two sides' restrictions of a flux recombine to it
exactly. -/
theorem restrict_add (f : Fin q → ℚ) :
    restrictTo I.left f + restrictTo I.right f = f := by
  funext e
  have hmem : e ∈ I.left ∪ I.right := by rw [I.covers]; exact Finset.mem_univ e
  rcases Finset.mem_union.mp hmem with hleft | hright
  · have hright : e ∉ I.right := fun h => (Finset.disjoint_left.mp I.disjoint hleft) h
    simp [restrictTo, hleft, hright]
  · have hleft : e ∉ I.left := fun h => (Finset.disjoint_left.mp I.disjoint h) hright
    simp [restrictTo, hleft, hright]

end SideSplit

variable (C : WeightedComplex p q r)

/-- [definition] **The outward normal flux one side delivers to the interface**: the divergence of
the flux carried by that side's cells alone. -/
def sideNormalFlux (S : Finset (Fin q)) (f : Fin q → ℚ) : Fin p → ℚ :=
  C.codiff₀ *ᵥ restrictTo S f

/-- [definition] **The jump of the normal flux across the interface**: the sum of the two sides'
outward normal fluxes. -/
def normalJump (I : SideSplit q) (f : Fin q → ℚ) : Fin p → ℚ :=
  sideNormalFlux C I.left f + sideNormalFlux C I.right f

/-- [proved-derived; formal-checked] **The normal jump is the codifferential.** Splitting the flux
by sides splits the divergence, so the jump across the interface is exactly `δ f` and nothing
else. This is the extrinsic half of the junction law identified with the adjoint of `d`. -/
theorem normalJump_eq_divergence (I : SideSplit q) (f : Fin q → ℚ) :
    normalJump C I f = C.codiff₀ *ᵥ f := by
  rw [normalJump, sideNormalFlux, sideNormalFlux, ← Matrix.mulVec_add, I.restrict_add]

/-- [definition] **The junction law's normal half**: the jump equals the source living on the
joint. -/
def Balanced (I : SideSplit q) (f : Fin q → ℚ) (σ : Fin p → ℚ) : Prop :=
  normalJump C I f = σ

/-- [definition] The residual a reading returns when the balance fails. It is the complete
cochain, not a norm of one. -/
def balanceResidual (I : SideSplit q) (f : Fin q → ℚ) (σ : Fin p → ℚ) : Fin p → ℚ :=
  normalJump C I f - σ

/-- [proved-derived; formal-checked] **`[[n·flux]] = σ` is `δ f = σ`.** -/
theorem balanced_iff_divergence (I : SideSplit q) (f : Fin q → ℚ) (σ : Fin p → ℚ) :
    Balanced C I f σ ↔ C.codiff₀ *ᵥ f = σ := by
  rw [Balanced, normalJump_eq_divergence]

/-- [proved-derived; formal-checked] The balance holds exactly when the returned residual is the
zero cochain. -/
theorem balanced_iff_residual_zero (I : SideSplit q) (f : Fin q → ℚ) (σ : Fin p → ℚ) :
    Balanced C I f σ ↔ balanceResidual C I f σ = 0 := by
  constructor
  · intro h; rw [balanceResidual, h]; exact sub_self σ
  · intro h
    have := sub_eq_zero.mp h
    exact this

end Interface

/-! ## 3. The tangential half: a jump is exactly the obstruction to being one field -/

section Tangential

variable {q : ℕ}

/-- [definition] The jump of two side fields across the cells they share. -/
def jump (a b : Fin q → ℚ) (Γ : Finset (Fin q)) : Fin q → ℚ :=
  fun e => if e ∈ Γ then a e - b e else 0

/-- [definition] Tangential continuity: the pullbacks to the shared cells agree. -/
def Glues (a b : Fin q → ℚ) (Γ : Finset (Fin q)) : Prop := jump a b Γ = 0

theorem glues_iff_agree (a b : Fin q → ℚ) (Γ : Finset (Fin q)) :
    Glues a b Γ ↔ ∀ e ∈ Γ, a e = b e := by
  constructor
  · intro h e he
    have := congrFun h e
    simp only [jump, he, if_pos, Pi.zero_apply] at this
    exact sub_eq_zero.mp this
  · intro h
    funext e
    by_cases he : e ∈ Γ
    · simp [jump, he, h e he]
    · simp [jump, he]

/-- [definition] The field on the union built from two side fields. -/
def descend (L : Finset (Fin q)) (a b : Fin q → ℚ) : Fin q → ℚ :=
  fun e => if e ∈ L then a e else b e

theorem descend_restricts_left (L : Finset (Fin q)) (a b : Fin q → ℚ) :
    ∀ e ∈ L, descend L a b e = a e := by
  intro e he; simp [descend, he]

/-- [proved-derived; formal-checked] **A vanishing jump is exactly what lets the two sides descend
to one field.** -/
theorem descend_restricts_right (L R : Finset (Fin q)) (a b : Fin q → ℚ)
    (h : Glues a b (L ∩ R)) : ∀ e ∈ R, descend L a b e = b e := by
  intro e he
  by_cases hL : e ∈ L
  · have : a e = b e := (glues_iff_agree a b (L ∩ R)).mp h e (Finset.mem_inter.mpr ⟨hL, he⟩)
    simp [descend, hL, this]
  · simp [descend, hL]

/-- [counterexample; formal-checked] **And a nonzero jump is exactly the obstruction.** No field on
the union restricts to both sides when the pullbacks disagree anywhere on the shared cells, so
tangential continuity is not an extra law imposed on a junction: it *is* being one cochain across
it. -/
theorem no_descent_of_nonzero_jump (L R : Finset (Fin q)) (a b : Fin q → ℚ)
    (h : ¬ Glues a b (L ∩ R)) :
    ¬ ∃ u : Fin q → ℚ, (∀ e ∈ L, u e = a e) ∧ (∀ e ∈ R, u e = b e) := by
  rintro ⟨u, hL, hR⟩
  refine h ((glues_iff_agree a b (L ∩ R)).mpr ?_)
  intro e he
  obtain ⟨heL, heR⟩ := Finset.mem_inter.mp he
  rw [← hL e heL, hR e heR]

end Tangential

/-! ## 4. Discrete Gauss, Tellegen, and the vertex closure -/

section Balance

variable {p q r : ℕ} (C : WeightedComplex p q r)

/-- [definition] The indicator cochain of a declared region of base cells. -/
def indicator (A : Finset (Fin p)) : Fin p → ℚ := fun i => if i ∈ A then 1 else 0

/-- [proved-derived; formal-checked] **The discrete Gauss statement.** The total source inside a
declared region equals the pairing of the flux with the coboundary of that region's indicator —
which is supported on the cells crossing its boundary. This is
`Foundation/HodgeReceiver.lean::codiff₀_adjoint` read at an indicator, cited and not rebuilt. -/
theorem discrete_gauss (A : Finset (Fin p)) (f : Fin q → ℚ) :
    ip C.w₀ (indicator A) (C.codiff₀ *ᵥ f) = ip C.w₁ (C.d₀ *ᵥ indicator A) f :=
  (C.codiff₀_adjoint (indicator A) f).symm

/-- [proved-derived; formal-checked] **Only the cells that cross the region's boundary carry
flux.** Under the declared row-sum law — every flux cell's coboundary row sums to zero, which is
what makes `d₀` a difference operator — a cell all of whose base cells lie inside the region, or
all of whose base cells lie outside it, contributes nothing. -/
theorem interior_cell_carries_no_boundary_flux
    (rowSum : ∀ e : Fin q, ∑ i, C.d₀ e i = 0) (A : Finset (Fin p)) (e : Fin q)
    (uniform : (∀ i, C.d₀ e i ≠ 0 → i ∈ A) ∨ (∀ i, C.d₀ e i ≠ 0 → i ∉ A)) :
    (C.d₀ *ᵥ indicator A) e = 0 := by
  simp only [Matrix.mulVec, dotProduct, indicator]
  rcases uniform with hin | hout
  · have : ∀ i ∈ Finset.univ, C.d₀ e i * (if i ∈ A then (1 : ℚ) else 0) = C.d₀ e i := by
      intro i _
      by_cases h : C.d₀ e i = 0
      · simp [h]
      · simp [hin i h]
    rw [Finset.sum_congr rfl this, rowSum e]
  · have : ∀ i ∈ Finset.univ, C.d₀ e i * (if i ∈ A then (1 : ℚ) else 0) = 0 := by
      intro i _
      by_cases h : C.d₀ e i = 0
      · simp [h]
      · simp [hout i h]
    rw [Finset.sum_congr rfl this, Finset.sum_const_zero]

/-- [proved-derived; formal-checked] **Tellegen's theorem: the junction's exact energy ledger.**
For any potential `v` and any flux `f` whose divergence is the declared source `σ`, the pairing of
the drops with the flux equals the pairing of the potential with the source. Power delivered at the
junctions is power dissipated along the branches, exactly, with no tolerance and no limit. -/
theorem tellegen (v : Fin p → ℚ) (f : Fin q → ℚ) (σ : Fin p → ℚ)
    (balance : C.codiff₀ *ᵥ f = σ) :
    ip C.w₁ (C.d₀ *ᵥ v) f = ip C.w₀ v σ := by
  rw [C.codiff₀_adjoint v f, balance]

/-- [proved-derived; formal-checked] **`δ ∘ δ = 0`: the codimension-2 compatibility.** The junction
laws carried on the codimension-1 strata around a vertex must close, and this is the exact sense in
which they do: a source that is the interface flux of any 2-cochain has vanishing divergence at
every vertex. -/
theorem codiff_comp_zero (x : Fin r → ℚ) : C.codiff₀ *ᵥ (C.codiff₁ *ᵥ x) = 0 := by
  set z := C.codiff₀ *ᵥ (C.codiff₁ *ᵥ x) with hz
  have key : ∀ y : Fin p → ℚ, ip C.w₀ y z = 0 := by
    intro y
    rw [hz, ← C.codiff₀_adjoint y (C.codiff₁ *ᵥ x), ip_symm, C.codiff₁_adjoint,
      Matrix.mulVec_mulVec, C.dd, Matrix.zero_mulVec]
    simp [ip]
  have hzz : ip C.w₀ z z = 0 := key z
  exact ip_eq_zero C.w₀pos hzz

/-- [definition] The source a declared 2-cochain deposits on the codimension-1 strata. -/
def interfaceSource (F : Fin r → ℚ) : Fin q → ℚ := C.codiff₁ *ᵥ F

/-- [proved-derived; formal-checked] **The sum of the jumps around a vertex link vanishes.** -/
theorem vertex_closure (F : Fin r → ℚ) : C.codiff₀ *ᵥ interfaceSource C F = 0 :=
  codiff_comp_zero C F

/-- [counterexample; formal-checked] **And a source that does not close is an obstruction, not a
repair.** No 2-cochain deposits a codimension-1 source whose vertex divergence is nonzero. -/
theorem no_interface_flux_for_a_nonclosing_source (σ : Fin q → ℚ)
    (open_vertex : C.codiff₀ *ᵥ σ ≠ 0) : ¬ ∃ F : Fin r → ℚ, interfaceSource C F = σ := by
  rintro ⟨F, rfl⟩
  exact open_vertex (vertex_closure C F)

end Balance


/-! ## 5. Valence, Euler characteristic, and what one junction costs -/

section EulerCharacteristic

variable {Cell : Type u} [DecidableEq Cell] (grade : Cell → ℕ)

/-- [definition] The Euler characteristic of a finite population of graded cells: the alternating
sum of its cell counts, written cell by cell. -/
def chi (S : Finset Cell) : ℤ := ∑ c ∈ S, (-1) ^ grade c

/-- [proved-derived; formal-checked] Inclusion–exclusion, exactly. -/
theorem chi_union_add_inter (A B : Finset Cell) :
    chi grade (A ∪ B) + chi grade (A ∩ B) = chi grade A + chi grade B :=
  Finset.sum_union_inter

/-- [proved-derived; formal-checked] **`χ(A ∪_Γ B) = χ(A) + χ(B)` whenever the gluing locus has
vanishing Euler characteristic** — a circle, for example, which is why gluing tubes along their
boundary circles is additive. -/
theorem chi_glue_along_zero {A B : Finset Cell} (hΓ : chi grade (A ∩ B) = 0) :
    chi grade (A ∪ B) = chi grade A + chi grade B := by
  have := chi_union_add_inter grade A B
  rw [hΓ, add_zero] at this
  exact this

/-- [definition] The union of a finite list of pieces. -/
def unionOf : List (Finset Cell) → Finset Cell
  | [] => ∅
  | piece :: rest => piece ∪ unionOf rest

/-- [definition] Each piece meets everything assembled after it in a locus of vanishing Euler
characteristic — the boundary circles along which tubes are glued. -/
def GluedAlongZero : List (Finset Cell) → Prop
  | [] => True
  | piece :: rest => chi grade (piece ∩ unionOf rest) = 0 ∧ GluedAlongZero rest

/-- [proved-derived; formal-checked] **Euler characteristic is additive over such an assembly.** -/
theorem chi_unionOf : ∀ pieces : List (Finset Cell), GluedAlongZero grade pieces →
    chi grade (unionOf pieces) = (pieces.map (chi grade)).sum
  | [], _ => by simp [unionOf, chi]
  | piece :: rest, h => by
      obtain ⟨hcircle, hrest⟩ := h
      rw [unionOf, chi_glue_along_zero grade hcircle, chi_unionOf rest hrest]
      simp

/-- [proved-derived; formal-checked] **Each junction costs one unit of Euler characteristic.** A
surface assembled from `n` pieces of Euler characteristic `−1` — the pair of pants and the Möbius
shorts are both such a piece — glued along circles has Euler characteristic `−n`. Orientability is
not decided by this count: it is the extra `ℤ/2` of section 6. -/
theorem sum_of_unit_costs (pieces : List (Finset Cell))
    (each : ∀ piece ∈ pieces, chi grade piece = -1) :
    (pieces.map (chi grade)).sum = -(pieces.length : ℤ) := by
  induction pieces with
  | nil => simp
  | cons piece rest ih =>
      have hhead : chi grade piece = -1 := each piece (by simp)
      have hrest : ∀ p ∈ rest, chi grade p = -1 := fun p hp => each p (by simp [hp])
      simp only [List.map_cons, List.sum_cons, List.length_cons, hhead, ih hrest]
      push_cast
      ring

theorem each_junction_costs_one_euler (pieces : List (Finset Cell))
    (assembled : GluedAlongZero grade pieces)
    (each : ∀ piece ∈ pieces, chi grade piece = -1) :
    chi grade (unionOf pieces) = -(pieces.length : ℤ) := by
  rw [chi_unionOf grade pieces assembled]
  exact sum_of_unit_costs grade pieces each

end EulerCharacteristic

/-! ## 6. The orientation bit is a `ℤ/2` holonomy -/

section Orientation

variable {Face : Type u}

/-- [definition] The holonomy of a declared dual walk under a sign assignment: the product of the
required sign relations along it. Each interior interface of a triangulated surface requires
`ε_right = −h_left h_right ε_left`, so the relation carried on that dual edge is the product of the
two endpoint signs. -/
def walkHolonomy (sign : Face → ℤ) : List Face → ℤ
  | [] => 1
  | [_] => 1
  | first :: second :: rest => (sign first * sign second) * walkHolonomy sign (second :: rest)

/-- [proved-derived; formal-checked] **A consistent sign assignment telescopes.** The holonomy of
any dual walk depends only on its two ends. -/
theorem walkHolonomy_telescopes (sign : Face → ℤ) (unit : ∀ f, sign f * sign f = 1) :
    ∀ (first : Face) (rest : List Face),
      walkHolonomy sign (first :: rest)
        = sign first * sign ((first :: rest).getLast (List.cons_ne_nil first rest))
  | first, [] => by simp [walkHolonomy, unit first]
  | first, second :: rest => by
      rw [walkHolonomy, walkHolonomy_telescopes sign unit second rest]
      have hlast : (first :: second :: rest).getLast (List.cons_ne_nil _ _)
          = (second :: rest).getLast (List.cons_ne_nil _ _) := List.getLast_cons _
      rw [hlast, mul_assoc, ← mul_assoc (sign second) (sign second), unit second, one_mul]

/-- [proved-derived; formal-checked] **A closed dual walk of an orientable surface has holonomy
one.** This is the exact content of "the directrix returns unreversed". -/
theorem closed_walk_holonomy_one (sign : Face → ℤ) (unit : ∀ f, sign f * sign f = 1)
    (first : Face) (rest : List Face)
    (closed : (first :: rest).getLast (List.cons_ne_nil first rest) = first) :
    walkHolonomy sign (first :: rest) = 1 := by
  rw [walkHolonomy_telescopes sign unit first rest, closed, unit first]

/-- [historical; formal-checked] Vacuous as stated: `sign () * sign () = −1` is refuted by the unit
clause alone and carries no loop datum (`Objects/Orientation.junction_hypothesis_is_refuted_by_unit_alone`).
The content is `Objects/Orientation.reversing_closed_walk_has_no_orientation`; this is its one-face case
(`junction_statement_from_cycle`). Original heading: **And a reversing loop admits no consistent assignment.** A
dual edge whose required relation is `−1` between a face and itself — the Möbius seam — has no
sign. Non-orientability is exhibited by the closed path, never counted. The tube-level form of the
same obstruction is `Transport/ContinuingTube.lean::flipCircuit_carries_no_invariant_end`. -/
theorem no_consistent_orientation_on_a_reversing_loop :
    ¬ ∃ sign : Unit → ℤ, (∀ f, sign f * sign f = 1) ∧ sign () * sign () = -1 := by
  rintro ⟨sign, unit, reversing⟩
  rw [unit ()] at reversing
  exact absurd reversing (by decide)

/-- [proved-derived; formal-checked] **A circuit of `k` reflections has determinant `(−1)^k`.** -/
theorem reflection_circuit_determinant (k : ℕ) :
    (List.replicate k (-1 : ℤ)).prod = (-1) ^ k := by
  simp

/-- [proved-derived; formal-checked] **Odd means orientation-reversing.** This is `m mod 2` of the
half-twist record: orientability is the parity face of a winding, and `w₁` is that mod-2
reduction. -/
theorem orientation_reversing_iff_odd (k : ℕ) : (-1 : ℤ) ^ k = -1 ↔ Odd k := by
  constructor
  · intro h
    rcases Nat.even_or_odd k with he | ho
    · rw [he.neg_one_pow] at h; exact absurd h (by decide)
    · exact ho
  · intro h; exact h.neg_one_pow

end Orientation

/-! ## 7. The instances, each exact over `ℚ` -/

section Instances

variable {n : ℕ}

/-- [definition] The unit-weight pairing, which is `Foundation/HodgeReceiver.lean::ip` at the unit
metric — the one declaration under which a bare transpose is the codifferential. -/
def innerQ (x y : Fin n → ℚ) : ℚ := ip (fun _ => (1 : ℚ)) x y

theorem innerQ_symm (x y : Fin n → ℚ) : innerQ x y = innerQ y x := ip_symm _ x y

theorem innerQ_add_left (x y z : Fin n → ℚ) :
    innerQ (x + y) z = innerQ x z + innerQ y z := ip_add_left _ x y z

theorem innerQ_add_right (x y z : Fin n → ℚ) :
    innerQ x (y + z) = innerQ x y + innerQ x z := ip_add_right _ x y z

theorem innerQ_sub_left (x y z : Fin n → ℚ) :
    innerQ (x - y) z = innerQ x z - innerQ y z := ip_sub_left _ x y z

theorem innerQ_sub_right (x y z : Fin n → ℚ) :
    innerQ x (y - z) = innerQ x y - innerQ x z := by
  rw [innerQ_symm, innerQ_sub_left, innerQ_symm x y, innerQ_symm x z]

theorem innerQ_smul_left (c : ℚ) (x y : Fin n → ℚ) :
    innerQ (c • x) y = c * innerQ x y := ip_smul_left c _ x y

theorem innerQ_smul_right (c : ℚ) (x y : Fin n → ℚ) :
    innerQ x (c • y) = c * innerQ x y := ip_smul_right c _ x y

theorem innerQ_zero_left (y : Fin n → ℚ) : innerQ 0 y = 0 := ip_zero_left _ y

theorem innerQ_self_nonneg (x : Fin n → ℚ) : 0 ≤ innerQ x x :=
  ip_self_nonneg (fun _ => zero_lt_one) x

/-- [proved-derived; formal-checked] The unit pairing is definite over `ℚ`, cited from the Hodge
owner rather than reproved. -/
theorem innerQ_eq_zero {x : Fin n → ℚ} (h : innerQ x x = 0) : x = 0 :=
  ip_eq_zero (fun _ => zero_lt_one) h

/-! ### Films: Plateau's laws as tension balance at a junction -/

/-- [proved-derived; formal-checked] **Three conormals of equal tension balance exactly when their
pairwise products are `−T/2`.** This is Plateau's `120°` law at a junction *line*, stated in the
squared form that is exact over `ℚ`: the directions themselves need not be rational, and their
inner products are. Both directions are proved; nothing is assumed about the ambient dimension. -/
theorem three_conormals_balance_iff (a b c : Fin n → ℚ) (T : ℚ)
    (ha : innerQ a a = T) (hb : innerQ b b = T) (hc : innerQ c c = T) :
    a + b + c = 0 ↔ (innerQ a b = -T / 2 ∧ innerQ a c = -T / 2 ∧ innerQ b c = -T / 2) := by
  constructor
  · intro h
    have expand : ∀ x : Fin n → ℚ, innerQ a x + innerQ b x + innerQ c x = 0 := by
      intro x
      rw [← innerQ_add_left, ← innerQ_add_left, h, innerQ_zero_left]
    have h1 := expand a
    have h2 := expand b
    have h3 := expand c
    rw [ha, innerQ_symm b a, innerQ_symm c a] at h1
    rw [hb, innerQ_symm c b] at h2
    rw [hc] at h3
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨hab, hac, hbc⟩
    have expand : innerQ (a + b + c) (a + b + c) = 0 := by
      rw [innerQ_add_right, innerQ_add_right, innerQ_add_left, innerQ_add_left,
        innerQ_add_left, innerQ_add_left, innerQ_add_left, innerQ_add_left,
        innerQ_symm b a, innerQ_symm c a, innerQ_symm c b, ha, hb, hc, hab, hac, hbc]
      ring
    exact innerQ_eq_zero expand

/-- [proved-derived; formal-checked] **Four conormals at a tetrahedral vertex.** The converse half
is unconditional: pairwise products `−T/3` force the balance. -/
theorem four_conormals_balance_of_pairwise (a b c d : Fin n → ℚ) (T : ℚ)
    (ha : innerQ a a = T) (hb : innerQ b b = T) (hc : innerQ c c = T) (hd : innerQ d d = T)
    (hab : innerQ a b = -T / 3) (hac : innerQ a c = -T / 3) (had : innerQ a d = -T / 3)
    (hbc : innerQ b c = -T / 3) (hbd : innerQ b d = -T / 3) (hcd : innerQ c d = -T / 3) :
    a + b + c + d = 0 := by
  refine innerQ_eq_zero ?_
  rw [innerQ_add_right, innerQ_add_right, innerQ_add_right,
    innerQ_add_left, innerQ_add_left, innerQ_add_left,
    innerQ_add_left, innerQ_add_left, innerQ_add_left,
    innerQ_add_left, innerQ_add_left, innerQ_add_left,
    innerQ_add_left, innerQ_add_left, innerQ_add_left,
    innerQ_symm b a, innerQ_symm c a, innerQ_symm d a, innerQ_symm c b, innerQ_symm d b,
    innerQ_symm d c, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd]
  ring

/-- [proved-derived; formal-checked] **The balance alone fixes only the sum of the six pairwise
products, not each of them.** This is the exact difference between the junction *line* and the
junction *vertex*: at three conormals the `120°` relation is forced, at four the tetrahedral
relation is an extra declaration. -/
theorem four_conormals_pairwise_sum (a b c d : Fin n → ℚ) (T : ℚ)
    (ha : innerQ a a = T) (hb : innerQ b b = T) (hc : innerQ c c = T) (hd : innerQ d d = T)
    (balance : a + b + c + d = 0) :
    innerQ a b + innerQ a c + innerQ a d + innerQ b c + innerQ b d + innerQ c d = -2 * T := by
  have expand : ∀ x : Fin n → ℚ, innerQ a x + innerQ b x + innerQ c x + innerQ d x = 0 := by
    intro x
    rw [← innerQ_add_left, ← innerQ_add_left, ← innerQ_add_left, balance, innerQ_zero_left]
  have h1 := expand a
  have h2 := expand b
  have h3 := expand c
  have h4 := expand d
  rw [ha, innerQ_symm b a, innerQ_symm c a, innerQ_symm d a] at h1
  rw [hb, innerQ_symm c b, innerQ_symm d b] at h2
  rw [hc, innerQ_symm d c] at h3
  rw [hd] at h4
  linarith

/-! ### Fluids: Rankine–Hugoniot for an exact polynomial flux -/

/-- [definition] The Burgers flux `f(u) = u²/2`, exact over `ℚ`. -/
def burgersFlux (u : ℚ) : ℚ := u ^ 2 / 2

/-- [definition] The shock speed of a Burgers jump. -/
def shockSpeed (uL uR : ℚ) : ℚ := (uL + uR) / 2

/-- [proved-derived; formal-checked] **`s = [[f]] / [[u]]`, exactly rational.** -/
theorem rankine_hugoniot_speed (uL uR : ℚ) (jump : uR ≠ uL) :
    (burgersFlux uR - burgersFlux uL) / (uR - uL) = shockSpeed uL uR := by
  have hne : uR - uL ≠ 0 := sub_ne_zero.mpr jump
  simp only [burgersFlux, shockSpeed]
  field_simp
  ring

/-- [proved-derived; formal-checked] **Mass balance across the joint**, with no division and hence
no hypothesis: `s [[u]] = [[f]]` holds even at a vanishing jump. -/
theorem rankine_hugoniot_balance (uL uR : ℚ) :
    shockSpeed uL uR * (uR - uL) = burgersFlux uR - burgersFlux uL := by
  simp only [shockSpeed, burgersFlux]
  ring

/-- [proved-derived; formal-checked] **The Lax entropy condition is the junction's
irreversibility.** For the Burgers flux `f'(u) = u`, so admissibility reads `uL > s > uR`, and it
holds exactly when the jump is a decrease. Reversing the traversal reverses the verdict: the
one-way reading belongs to the `(junction, direction)` pair and never to the junction alone. -/
theorem lax_admissible_iff (uL uR : ℚ) :
    (shockSpeed uL uR < uL ∧ uR < shockSpeed uL uR) ↔ uR < uL := by
  constructor
  · rintro ⟨h1, _⟩; simp only [shockSpeed] at h1; linarith
  · intro h; constructor <;> (simp only [shockSpeed]; linarith)

/-- [counterexample; formal-checked] **An expansion shock is inadmissible.** -/
theorem expansion_shock_violates_lax (uL uR : ℚ) (rarefaction : uL < uR) :
    ¬ (shockSpeed uL uR < uL ∧ uR < shockSpeed uL uR) := by
  intro h
  have := (lax_admissible_iff uL uR).mp h
  linarith

/-! ### Electromagnetism: a finite interface on rational wave covectors -/

/-- [definition] The tangential part of a covector at a declared interface normal. -/
def tangentialPart (normal x : Fin n → ℚ) : Fin n → ℚ :=
  x - (innerQ x normal / innerQ normal normal) • normal

/-- [proved-derived; formal-checked] The tangential part is orthogonal to the normal. -/
theorem tangentialPart_orthogonal (normal x : Fin n → ℚ) (hn : innerQ normal normal ≠ 0) :
    innerQ (tangentialPart normal x) normal = 0 := by
  rw [tangentialPart, innerQ_sub_left, innerQ_smul_left]
  field_simp
  ring

/-- [proved-derived; formal-checked] The orthogonal decomposition's exact squared length. -/
theorem innerQ_decompose (t v : Fin n → ℚ) (c : ℚ) (horth : innerQ t v = 0) :
    innerQ (t + c • v) (t + c • v) = innerQ t t + c * c * innerQ v v := by
  simp only [innerQ_add_left, innerQ_add_right, innerQ_smul_left, innerQ_smul_right]
  rw [horth, innerQ_symm v t, horth]
  ring

/-- [proved-derived; formal-checked] The exact Pythagorean split of a covector at an interface. -/
theorem innerQ_split (normal x : Fin n → ℚ) (hn : innerQ normal normal ≠ 0) :
    innerQ x x
      = innerQ (tangentialPart normal x) (tangentialPart normal x)
        + (innerQ x normal) ^ 2 / innerQ normal normal := by
  have horth : innerQ (tangentialPart normal x) normal =
      0 := tangentialPart_orthogonal normal x hn
  have hx : tangentialPart normal x
      + (innerQ x normal / innerQ normal normal) • normal = x := by
    simp only [tangentialPart]; abel
  have key := innerQ_decompose (tangentialPart normal x) normal
    (innerQ x normal / innerQ normal normal) horth
  rw [hx] at key
  rw [key]
  field_simp

/-- [definition] `sin²θ` of a wave covector at a declared interface: the ratio of the tangential
squared length to the whole squared length. It is rational whenever the covector is, which is
exactly why Snell's law is exact here in squares and not in sines. -/
def sineSquared (normal k : Fin n → ℚ) : ℚ :=
  innerQ (tangentialPart normal k) (tangentialPart normal k) / innerQ k k

/-- [proved-derived; formal-checked] **Snell's law, exactly, as a rational identity in squares.**
Tangential continuity of the wave covector across a planar interface plus the declared dispersion
relation `|k_j|² = n_j² κ²` gives `n₁² sin²θ₁ = n₂² sin²θ₂` with no square root taken anywhere.
Refraction is the junction law's tangential half. -/
theorem snell_squared (normal k₁ k₂ : Fin n → ℚ) (n₁sq n₂sq κsq : ℚ)
    (dispersion₁ : innerQ k₁ k₁ = n₁sq * κsq) (dispersion₂ : innerQ k₂ k₂ = n₂sq * κsq)
    (hn₁ : n₁sq ≠ 0) (hn₂ : n₂sq ≠ 0) (hκ : κsq ≠ 0)
    (tangential : tangentialPart normal k₁ = tangentialPart normal k₂) :
    n₁sq * sineSquared normal k₁ = n₂sq * sineSquared normal k₂ := by
  simp only [sineSquared, dispersion₁, dispersion₂, tangential]
  field_simp

/-- [proved-derived; formal-checked] **Total internal reflection is an exact sign condition.**
Beyond the critical angle the declared tangential covector admits no transmitted covector at all:
the normal component's square would have to be negative. The reading returns that deficit; it
never returns a square root of a negative number. -/
theorem no_transmitted_covector_beyond_the_critical_angle
    (normal tangent : Fin n → ℚ) (n₂sq κsq : ℚ) (hn : 0 < innerQ normal normal)
    (beyond : n₂sq * κsq < innerQ tangent tangent) :
    ¬ ∃ k : Fin n → ℚ, tangentialPart normal k = tangent ∧ innerQ k k = n₂sq * κsq := by
  rintro ⟨k, htangent, hdispersion⟩
  have hsplit := innerQ_split normal k (ne_of_gt hn)
  rw [htangent, hdispersion] at hsplit
  have hnonneg : 0 ≤ (innerQ k normal) ^ 2 / innerQ normal normal :=
    div_nonneg (sq_nonneg _) hn.le
  linarith

/-- [definition] The typed outcome at an interface: transmitted with the exact squared normal
component, grazing, or totally reflected with the exact deficit. Never a floating-point `NaN`. -/
inductive InterfaceOutcome where
  /-- A transmitted covector exists; the payload is the exact squared normal component. -/
  | transmitted (normalSquared : ℚ) : InterfaceOutcome
  /-- The normal component vanishes exactly. -/
  | grazing : InterfaceOutcome
  /-- No transmitted covector exists; the payload is the exact deficit. -/
  | totallyReflected (deficit : ℚ) : InterfaceOutcome
  deriving DecidableEq

/-- [definition] The classification, decided exactly by a rational comparison. -/
def classifyInterface (tangentSquared n₂sq κsq : ℚ) : InterfaceOutcome :=
  if tangentSquared < n₂sq * κsq then .transmitted (n₂sq * κsq - tangentSquared)
  else if tangentSquared = n₂sq * κsq then .grazing
  else .totallyReflected (tangentSquared - n₂sq * κsq)

/-- [definition] Which outcomes are total reflection. -/
def IsTotallyReflected : InterfaceOutcome → Prop
  | .totallyReflected _ => True
  | _ => False

/-- [proved-derived; formal-checked] The classification is the sign condition and nothing else. -/
theorem totally_reflected_iff (tangentSquared n₂sq κsq : ℚ) :
    IsTotallyReflected (classifyInterface tangentSquared n₂sq κsq)
      ↔ n₂sq * κsq < tangentSquared := by
  unfold classifyInterface
  split_ifs with h1 h2
  · simp only [IsTotallyReflected]
    constructor
    · intro h; exact absurd h (by simp)
    · intro h; linarith
  · simp only [IsTotallyReflected]
    constructor
    · intro h; exact absurd h (by simp)
    · intro h; linarith
  · simp only [IsTotallyReflected]
    constructor
    · intro _; rcases lt_trichotomy tangentSquared (n₂sq * κsq) with h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact h
    · intro _; trivial

end Instances

section Audit

#print axioms join_is_exactly_the_compatible_pairs
#print axioms noSharedBoundary_isEmpty_join
#print axioms serial_station_is_not_a_junction
#print axioms trivalent_station_is_a_junction
#print axioms SideSplit.restrict_add
#print axioms normalJump_eq_divergence
#print axioms balanced_iff_divergence
#print axioms balanced_iff_residual_zero
#print axioms glues_iff_agree
#print axioms descend_restricts_left
#print axioms descend_restricts_right
#print axioms no_descent_of_nonzero_jump
#print axioms discrete_gauss
#print axioms interior_cell_carries_no_boundary_flux
#print axioms tellegen
#print axioms codiff_comp_zero
#print axioms vertex_closure
#print axioms no_interface_flux_for_a_nonclosing_source
#print axioms chi_union_add_inter
#print axioms chi_glue_along_zero
#print axioms chi_unionOf
#print axioms sum_of_unit_costs
#print axioms each_junction_costs_one_euler
#print axioms walkHolonomy_telescopes
#print axioms closed_walk_holonomy_one
#print axioms no_consistent_orientation_on_a_reversing_loop
#print axioms reflection_circuit_determinant
#print axioms orientation_reversing_iff_odd
#print axioms innerQ_self_nonneg
#print axioms innerQ_eq_zero
#print axioms three_conormals_balance_iff
#print axioms four_conormals_balance_of_pairwise
#print axioms four_conormals_pairwise_sum
#print axioms rankine_hugoniot_speed
#print axioms rankine_hugoniot_balance
#print axioms lax_admissible_iff
#print axioms expansion_shock_violates_lax
#print axioms tangentialPart_orthogonal
#print axioms innerQ_decompose
#print axioms innerQ_split
#print axioms snell_squared
#print axioms no_transmitted_covector_beyond_the_critical_angle
#print axioms totally_reflected_iff

end Audit

end Holonics.Transport.JunctionLaw
