import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Abel

/-!
# An apertured graded complex, and what an undecided contact may do to it

[definition] This owner states the law the Rust adapter
`crates/holonic-engine/src/physical_constraint_grading.rs` implements: how an exact aperture
classification whose third class is **undecided** becomes a graded chain complex without that third
class being quietly turned into one of the other two.

Three things are stated, in this order.

1. **The graded complex.** Arbitrary natural grade, integer coefficients, a finitely supported
   boundary chain per cell, grade compatibility, and the boundary law `∂∘∂ = 0` lifted from cells
   to chains. This is the formal counterpart of `algebraic.rs::GradedCausalComplex`, whose
   `found_cell` checks exactly these three conditions at every founding.
2. **The aperture trichotomy.** An exact interval compared against an aperture returns `inside`,
   `outside`, or `openContact` — and an interval that straddles the aperture returns the third. A
   point interval never does, so the open class is produced by genuine width and never by the
   classifier hedging.
3. **The admissibility condition.** An `openContact` is consumed only by a declared
   [`Resolution`]. A decided contact's admission does not move with the resolution
   (`decided_admission_is_resolution_free`), and an open contact's does
   (`openContact_is_plural`) — which is exactly why the adapter returns a family of complexes and
   not one complex. Under every resolution the founded two-cells close on founded one-cells
   (`founded_face_boundary_stands`) and the boundary law holds
   (`constraint_boundary_squared`), with no hypothesis on the aperture, the interval or the
   resolution.

[proved-derived; formal-checked] The boundary law is unconditional. The founded two-cell
`[a,b,c]` carries `∂[a,b,c] = [b,c] − [a,c] + [a,b]` and each one-cell carries
`∂[u,v] = [v] − [u]`, so `∂∂[a,b,c] = ([c]−[b]) − ([c]−[a]) + ([b]−[a]) = 0` telescopes. A
resolution decides **which** cells stand; it never touches the algebra of the cells that do.
-/

noncomputable section

namespace Soma.Holonics.Foundation.AperturedGradedComplex

universe u v

/-! ## The graded complex -/

/-- [definition] One finite oriented chain: integer coefficients on finitely many cells. -/
abbrev GradedChain (Cell : Type u) := Cell →₀ ℤ

/-- [definition] Arbitrary-rank oriented incidence with integer coefficients.

The three fields after `boundary` are the founding conditions
`algebraic.rs::GradedCausalComplex::found_cell` checks: a boundary cell sits exactly one grade
below its carrier, and a grade-zero cell has no boundary. The boundary law itself is a separate
predicate, [`BoundarySquaresToZero`], because a caller may found cells one at a time. -/
structure GradedComplex (Cell : Type u) where
  grade : Cell → ℕ
  boundary : Cell → GradedChain Cell
  boundary_grade : ∀ c d, d ∈ (boundary c).support → grade c = grade d + 1
  ground_has_no_boundary : ∀ c, grade c = 0 → boundary c = 0

namespace GradedComplex

variable {Cell : Type u}

/-- [definition] The boundary map on chains: the unique `ℤ`-linear extension of the cell boundary. -/
def d (K : GradedComplex Cell) : GradedChain Cell →ₗ[ℤ] GradedChain Cell :=
  Finsupp.linearCombination ℤ K.boundary

@[simp]
theorem d_single (K : GradedComplex Cell) (c : Cell) (n : ℤ) :
    K.d (Finsupp.single c n) = n • K.boundary c := by
  simp [d]

end GradedComplex

/-- [definition] The boundary law, stated where it is actually checkable: on cells. -/
def BoundarySquaresToZero {Cell : Type u} (K : GradedComplex Cell) : Prop :=
  ∀ c, K.d (K.boundary c) = 0

/-- [proved-derived; formal-checked] The cell-level boundary law lifts to every chain. -/
theorem d_comp_d {Cell : Type u} (K : GradedComplex Cell) (h : BoundarySquaresToZero K) :
    K.d ∘ₗ K.d = 0 := by
  refine Finsupp.lhom_ext (fun a n => ?_)
  simp [h a]

/-- [proved-derived; formal-checked] The same law read on one chain. -/
theorem d_d_apply {Cell : Type u} (K : GradedComplex Cell) (h : BoundarySquaresToZero K)
    (x : GradedChain Cell) : K.d (K.d x) = 0 := by
  have := d_comp_d K h
  have := congrArg (fun f => (f : GradedChain Cell →ₗ[ℤ] GradedChain Cell) x) this
  simpa using this

/-! ## The aperture and its third class -/

/-- [definition] An exact closed interval, the formal counterpart of
`exact_value.rs::ExactInterval`. -/
structure ExactInterval (K : Type v) [LinearOrder K] where
  lower : K
  upper : K
  ordered : lower ≤ upper

/-- [definition] What an aperture returns. `openContact` is `ContactClass::Open` in
`physical_constraint_complex.rs`: the interval straddles the aperture and no decision is taken. -/
inductive ContactClass where
  | outside
  | inside
  | openContact
  deriving DecidableEq, Repr

variable {K : Type v} [LinearOrder K]

/-- [definition] `physical_constraint_complex.rs::DistanceAperture::classify`. The whole upper
bound at or below the aperture is inside, the whole lower bound strictly above it is outside, and
every overlap stays open. -/
def classify (aperture : K) (d : ExactInterval K) : ContactClass :=
  if d.upper ≤ aperture then ContactClass.inside
  else if aperture < d.lower then ContactClass.outside
  else ContactClass.openContact

theorem classify_eq_inside_iff (aperture : K) (d : ExactInterval K) :
    classify aperture d = ContactClass.inside ↔ d.upper ≤ aperture := by
  unfold classify
  split_ifs with h1 h2
  · simp [h1]
  · simp [h1]
  · simp [h1]

theorem classify_eq_outside_iff (aperture : K) (d : ExactInterval K) :
    classify aperture d = ContactClass.outside ↔ aperture < d.lower := by
  unfold classify
  split_ifs with h1 h2
  · have absent : ¬ aperture < d.lower := not_lt.mpr (le_trans d.ordered h1)
    simp [absent]
  · simp [h2]
  · simp [h2]

theorem classify_eq_openContact_iff (aperture : K) (d : ExactInterval K) :
    classify aperture d = ContactClass.openContact ↔ aperture < d.upper ∧ d.lower ≤ aperture := by
  unfold classify
  split_ifs with h1 h2
  · simp [not_lt.mpr h1]
  · simp [not_le.mpr h2]
  · simp [not_le.mp h1, not_lt.mp h2]

/-- [proved-derived; formal-checked] A degenerate interval is never open: the third class comes
from genuine width and never from the classifier declining to look. -/
theorem classify_point_ne_openContact (aperture : K) (d : ExactInterval K)
    (point : d.lower = d.upper) : classify aperture d ≠ ContactClass.openContact := by
  intro h
  rw [classify_eq_openContact_iff] at h
  exact absurd (point ▸ h.2) (not_le.mpr h.1)

/-! ## The admissibility condition -/

/-- [definition] A declared disposition of every contact. The open class is consumed here and
nowhere else. -/
abbrev Resolution (P : Type u) := P → Bool

variable {P : Type u}

/-- [definition] The admitted contact population under one resolution: `inside` is admitted
whatever the resolution says, `outside` never is, and `openContact` is admitted exactly as the
resolution declares. There is no fourth branch and no default. -/
def admits (klass : P → ContactClass) (r : Resolution P) (p : P) : Bool :=
  match klass p with
  | ContactClass.inside => true
  | ContactClass.outside => false
  | ContactClass.openContact => r p

theorem admits_of_inside {klass : P → ContactClass} {r : Resolution P} {p : P}
    (h : klass p = ContactClass.inside) : admits klass r p = true := by
  simp [admits, h]

theorem not_admits_of_outside {klass : P → ContactClass} {r : Resolution P} {p : P}
    (h : klass p = ContactClass.outside) : admits klass r p = false := by
  simp [admits, h]

theorem admits_openContact {klass : P → ContactClass} {r : Resolution P} {p : P}
    (h : klass p = ContactClass.openContact) : admits klass r p = r p := by
  simp [admits, h]

/-- [proved-derived; formal-checked] **No silent promotion or demotion.** A contact the aperture
decided is admitted the same way under every resolution; a resolution can only speak where the
aperture did not. -/
theorem decided_admission_is_resolution_free {klass : P → ContactClass} {p : P}
    (decided : klass p ≠ ContactClass.openContact) (r s : Resolution P) :
    admits klass r p = admits klass s p := by
  unfold admits
  cases hp : klass p with
  | outside => rfl
  | inside => rfl
  | openContact => exact absurd hp decided

/-- [proved-derived; formal-checked] **An open contact is genuinely plural.** Two resolutions
disagree on it, so no single complex can represent the presentation and the adapter's return is a
family. -/
theorem openContact_is_plural {klass : P → ContactClass} {p : P}
    (h : klass p = ContactClass.openContact) :
    ∃ r s : Resolution P, admits klass r p ≠ admits klass s p := by
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  simp [admits, h]

/-- [proved-derived; formal-checked] With no open contact the family is a singleton: admission does
not depend on the resolution at all. -/
theorem determinate_of_no_openContact {klass : P → ContactClass}
    (h : ∀ p, klass p ≠ ContactClass.openContact) (r s : Resolution P) :
    admits klass r = admits klass s :=
  funext fun p => decided_admission_is_resolution_free (h p) r s

/-! ## The founded constraint complex -/

variable {V : Type u} [LinearOrder V]

/-- [definition] The three cell species the adapter founds: a presented occurrence, a canonical
unordered one-cell, and a two-cell on an ordered triple. -/
inductive ConstraintCell (V : Type u) where
  | vertex : V → ConstraintCell V
  | edge : V → V → ConstraintCell V
  | face : V → V → V → ConstraintCell V
  deriving DecidableEq

def cellGrade : ConstraintCell V → ℕ
  | ConstraintCell.vertex _ => 0
  | ConstraintCell.edge _ _ => 1
  | ConstraintCell.face _ _ _ => 2

/-- [definition] `physical_constraint_complex.rs::ConstraintEdge::new`: the canonical one-cell of an
unordered pair, carrying the hand that relates the presented order to it. -/
def orientedEdge (x y : V) : GradedChain (ConstraintCell V) :=
  if x < y then Finsupp.single (ConstraintCell.edge x y) 1
  else Finsupp.single (ConstraintCell.edge y x) (-1)

/-- [definition] The cell boundary. The two-cell's is the alternating
`∂[a,b,c] = [b,c] − [a,c] + [a,b]` of
`physical_constraint_complex.rs::ConstraintFace::boundary`. -/
def cellBoundary : ConstraintCell V → GradedChain (ConstraintCell V)
  | ConstraintCell.vertex _ => 0
  | ConstraintCell.edge u v =>
      Finsupp.single (ConstraintCell.vertex v) 1 - Finsupp.single (ConstraintCell.vertex u) 1
  | ConstraintCell.face a b c => orientedEdge b c - orientedEdge a c + orientedEdge a b

private theorem mem_support_orientedEdge {x y : V} {d : ConstraintCell V}
    (h : d ∈ (orientedEdge x y).support) :
    d = ConstraintCell.edge x y ∨ d = ConstraintCell.edge y x := by
  unfold orientedEdge at h
  by_cases hlt : x < y
  · rw [if_pos hlt] at h
    exact Or.inl (Finset.mem_singleton.mp (Finsupp.support_single_subset h))
  · rw [if_neg hlt] at h
    exact Or.inr (Finset.mem_singleton.mp (Finsupp.support_single_subset h))

private theorem mem_support_cellBoundary_face {a b c : V} {d : ConstraintCell V}
    (h : d ∈ (cellBoundary (ConstraintCell.face a b c)).support) :
    (d = ConstraintCell.edge b c ∨ d = ConstraintCell.edge c b) ∨
      (d = ConstraintCell.edge a c ∨ d = ConstraintCell.edge c a) ∨
      (d = ConstraintCell.edge a b ∨ d = ConstraintCell.edge b a) := by
  unfold cellBoundary at h
  rcases Finset.mem_union.mp (Finsupp.support_add h) with h | h
  · rcases Finset.mem_union.mp (Finsupp.support_sub h) with h | h
    · exact Or.inl (mem_support_orientedEdge h)
    · exact Or.inr (Or.inl (mem_support_orientedEdge h))
  · exact Or.inr (Or.inr (mem_support_orientedEdge h))

/-- [definition] The adapter's target: the graded complex the constraint cells carry. -/
def constraintComplex : GradedComplex (ConstraintCell V) where
  grade := cellGrade
  boundary := cellBoundary
  boundary_grade := by
    rintro (x | ⟨u, v⟩ | ⟨a, b, c⟩) d h
    · simp [cellBoundary] at h
    · rcases Finset.mem_union.mp (Finsupp.support_sub h) with h | h <;>
        · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]
          rfl
    · rcases mem_support_cellBoundary_face h with (rfl | rfl) | (rfl | rfl) | (rfl | rfl) <;> rfl
  ground_has_no_boundary := by
    rintro (x | ⟨u, v⟩ | ⟨a, b, c⟩) h
    · rfl
    · simp [cellGrade] at h
    · simp [cellGrade] at h

/-- [definition] The boundary map on constraint chains: the complex's own `d`, named so the
calculations below never pass through a structure projection. -/
def dConstraint : GradedChain (ConstraintCell V) →ₗ[ℤ] GradedChain (ConstraintCell V) :=
  Finsupp.linearCombination ℤ (cellBoundary (V := V))

theorem constraintComplex_d : (constraintComplex (V := V)).d = dConstraint := rfl

@[simp]
theorem dConstraint_single (c : ConstraintCell V) (n : ℤ) :
    dConstraint (Finsupp.single c n) = n • cellBoundary c := by
  simp [dConstraint]

/-- [proved-derived; formal-checked] Every one-cell of the pair `{x,y}`, taken with the hand the
canonical orientation demands, has boundary `[y] − [x]`. No distinctness is needed: a collapsed
pair returns zero on both sides. -/
theorem d_orientedEdge (x y : V) :
    dConstraint (orientedEdge x y) =
      Finsupp.single (ConstraintCell.vertex y) 1 -
        Finsupp.single (ConstraintCell.vertex x) 1 := by
  unfold orientedEdge
  by_cases hlt : x < y
  · rw [if_pos hlt, dConstraint_single]
    simp [cellBoundary]
  · rw [if_neg hlt, dConstraint_single]
    simp only [cellBoundary, neg_smul, one_smul, neg_sub]

/-- [proved-derived; formal-checked] **The boundary law of the founded complex, unconditionally.**
No hypothesis on the aperture, the interval, the resolution, or even the distinctness of the
triple. -/
theorem constraint_boundary_squared :
    BoundarySquaresToZero (constraintComplex (V := V)) := by
  show ∀ c : ConstraintCell V, dConstraint (cellBoundary c) = 0
  rintro (x | ⟨u, v⟩ | ⟨a, b, c⟩)
  · simp [cellBoundary]
  · simp [cellBoundary]
  · unfold cellBoundary
    rw [map_add, map_sub, d_orientedEdge, d_orientedEdge, d_orientedEdge]
    abel

/-- [proved-derived; formal-checked] The lifted law: `∂∘∂ = 0` on every chain of the founded
complex. -/
theorem constraint_d_comp_d :
    (constraintComplex (V := V)).d ∘ₗ (constraintComplex (V := V)).d = 0 :=
  d_comp_d _ constraint_boundary_squared

/-! ## The founding law under one resolution -/

variable (polygonal : V → V → Prop) (contact : V → V → P) (klass : P → ContactClass)
  (r : Resolution P)

/-- [definition] A one-cell stands when the presentation carries it as a polygonal step or when the
contact at that pair is admitted under the resolution. Standing is a property of the unordered
pair. -/
def Stands (x y : V) : Prop :=
  polygonal x y ∨ polygonal y x ∨
    admits klass r (contact x y) = true ∨ admits klass r (contact y x) = true

omit [LinearOrder V] in
theorem stands_symm {x y : V} (h : Stands polygonal contact klass r x y) :
    Stands polygonal contact klass r y x := by
  unfold Stands at h ⊢
  tauto

/-- [definition] The founding condition for a two-cell: all three of its one-faces stand. This is
`physical_constraint_complex.rs:408` and `physical_constraint_grading.rs`'s replay of it. -/
def FaceStands (a b c : V) : Prop :=
  Stands polygonal contact klass r a b ∧ Stands polygonal contact klass r b c ∧
    Stands polygonal contact klass r a c

/-- [proved-derived; formal-checked] **Closure under every resolution.** A founded two-cell's
boundary is supported on founded one-cells, for every resolution of the open class. This is the
condition `GradedCausalComplex::found_cell` enforces, and it is what makes the whole family — not
one privileged member — a family of chain complexes. -/
theorem founded_face_boundary_stands {a b c : V}
    (founded : FaceStands polygonal contact klass r a b c)
    {d : ConstraintCell V} (hd : d ∈ (cellBoundary (ConstraintCell.face a b c)).support) :
    ∃ x y, d = ConstraintCell.edge x y ∧ Stands polygonal contact klass r x y := by
  obtain ⟨hab, hbc, hac⟩ := founded
  rcases mem_support_cellBoundary_face hd with (rfl | rfl) | (rfl | rfl) | (rfl | rfl)
  · exact ⟨b, c, rfl, hbc⟩
  · exact ⟨c, b, rfl, stands_symm _ _ _ _ hbc⟩
  · exact ⟨a, c, rfl, hac⟩
  · exact ⟨c, a, rfl, stands_symm _ _ _ _ hac⟩
  · exact ⟨a, b, rfl, hab⟩
  · exact ⟨b, a, rfl, stands_symm _ _ _ _ hab⟩

/-- [proved-derived; formal-checked] **The adapter's contract.** For every resolution of the open
class: the founded two-cells close on founded one-cells, and the boundary law holds on every
chain. The second component does not mention the resolution — which is the precise sense in which
the open class changes the complex and not its algebra.

Rust owner: `crates/holonic-engine/src/physical_constraint_grading.rs`
(`graded_constraint_family`, `graded_constraint_member`, `OpenContactLaw`). -/
theorem adapter_contract :
    (∀ a b c : V, FaceStands polygonal contact klass r a b c →
        ∀ d ∈ (cellBoundary (ConstraintCell.face a b c)).support,
          ∃ x y, d = ConstraintCell.edge x y ∧ Stands polygonal contact klass r x y) ∧
      (constraintComplex (V := V)).d ∘ₗ (constraintComplex (V := V)).d = 0 :=
  ⟨fun _ _ _ founded _ hd => founded_face_boundary_stands _ _ _ _ founded hd,
    constraint_d_comp_d⟩

/-! ## The within-component contact family

[definition] A contact family is founded under one of two population laws. The cross law reads
every pair of two **distinct** components; it cannot express a pair of one component, because at
the diagonal the one-cell collapses. The **within-component** law reads the unordered pairs
`i < j` of one component's own chain whose positions differ by at least a declared sequence
separation `k`. Rust owner:
`crates/holonic-engine/src/physical_constraint_complex.rs::found_within_component_contact_family`
and `within_component_pair_count`.

Chain positions are counted from zero here and from one in Rust; the population and its cardinality
are the same set under `i ↦ i + 1`.
-/

/-- [definition] The within-component pair family of a component of extent `n` under a declared
sequence separation `k`: the pairs `i < j` of chain positions with `j − i ≥ k`, written without
truncated subtraction as `i + k ≤ j`. -/
def withinComponentPairs (n k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n ×ˢ Finset.range n).filter fun p => p.1 + k ≤ p.2

theorem mem_withinComponentPairs {n k : ℕ} {p : ℕ × ℕ} :
    p ∈ withinComponentPairs n k ↔ p.1 < n ∧ p.2 < n ∧ p.1 + k ≤ p.2 := by
  simp [withinComponentPairs, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- [proved-derived; formal-checked] A declared separation of at least one makes the family a
family of **unordered** pairs: `i < j` for every member. At `k = 1` that is all it says, which is
why the Rust owner refuses any declaration below two — separation one names the covalent chain
step, which is a one-cell of the presentation and not a contact. -/
theorem withinComponentPairs_lt {n k : ℕ} (hk : 1 ≤ k) {p : ℕ × ℕ}
    (h : p ∈ withinComponentPairs n k) : p.1 < p.2 := by
  rw [mem_withinComponentPairs] at h
  omega

/-- [counterexample; formal-checked] **Why the declared separation has a lower bound at all.** At
`k = 0` the family is `{(i, j) : i ≤ j}` and contains the whole diagonal, so it is not a family of
unordered pairs and its cardinality is `C(n + 1, 2)` rather than `C(n, 2)`. `withinComponentPairs_lt`
therefore carries `1 ≤ k` and the Rust owner's `within_component_pair_count` declares the domain
`k ≥ 2` — the contact reading's own domain — and answers `None` below it rather than returning a
number for a family nobody may found. -/
theorem withinComponentPairs_zero_contains_the_diagonal {n i : ℕ}
    (hi : i < n) : (i, i) ∈ withinComponentPairs n 0 := by
  rw [mem_withinComponentPairs]
  exact ⟨hi, hi, by omega⟩

/-- [proved-derived; formal-checked] A declared separation of at least two excludes the covalent
step: no member of the family is a pair of consecutive chain positions. -/
theorem withinComponentPairs_not_covalent {n k : ℕ} (hk : 2 ≤ k) {p : ℕ × ℕ}
    (h : p ∈ withinComponentPairs n k) : p.1 + 1 ≠ p.2 := by
  rw [mem_withinComponentPairs] at h
  omega

private theorem withinComponentPairs_eq_biUnion (n k : ℕ) :
    withinComponentPairs n k
      = (Finset.range n).biUnion fun j => (Finset.range (j + 1 - k)).image fun i => (i, j) := by
  ext p
  obtain ⟨a, b⟩ := p
  simp only [mem_withinComponentPairs, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨b, h2, a, by omega, rfl, rfl⟩
  · rintro ⟨j, hj, i, hi, rfl, rfl⟩
    exact ⟨by omega, hj, by omega⟩

private theorem choose_two_succ (m : ℕ) : (m + 1).choose 2 = m.choose 2 + m := by
  have := Nat.choose_succ_succ m 1
  simpa [Nat.choose_one_right, Nat.add_comm] using this

private theorem sum_range_succ_sub_eq_choose (n k : ℕ) (hk : 1 ≤ k) :
    ∑ j ∈ Finset.range n, (j + 1 - k) = (n + 1 - k).choose 2 := by
  induction n with
  | zero =>
      have : 0 + 1 - k = 0 := by omega
      simp [this]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases h : k ≤ m + 1
      · have step : m + 1 + 1 - k = (m + 1 - k) + 1 := by omega
        rw [step, choose_two_succ]
      · have h0 : m + 1 - k = 0 := by omega
        have h1 : m + 1 + 1 - k = 0 := by omega
        simp [h0, h1]

/-- [proved-derived; formal-checked] **The exact population of the within-component family.**
`C(n − k + 1, 2)`, written without truncated subtraction as `C(n + 1 − k, 2)`, which agrees with it
at every `n` and `k` and is the value the Rust owner's `within_component_pair_count` returns. It is
`0` as soon as `n ≤ k`.

Rust owner: `physical_constraint_complex.rs::within_component_pair_count`, checked against the
enumeration it counts by `the_within_component_population_is_n_minus_k_plus_one_choose_two`. The
Rust owner declares the narrower domain `k ≥ 2` — the contact reading's own — and answers `None`
below it (`the_within_component_population_is_undefined_below_the_declared_separation`); the
hypothesis `1 ≤ k` here and `withinComponentPairs_zero_contains_the_diagonal` are why. -/
theorem withinComponentPairs_card (n k : ℕ) (hk : 1 ≤ k) :
    (withinComponentPairs n k).card = (n + 1 - k).choose 2 := by
  classical
  have hinj : ∀ j : ℕ, Function.Injective fun i : ℕ => (i, j) := by
    intro j a b hab
    exact congrArg Prod.fst hab
  have hdisj : ∀ x ∈ Finset.range n, ∀ y ∈ Finset.range n, x ≠ y →
      Disjoint ((Finset.range (x + 1 - k)).image fun i => (i, x))
        ((Finset.range (y + 1 - k)).image fun i => (i, y)) := by
    intro x _ y _ hxy
    refine Finset.disjoint_left.mpr fun p hp hq => ?_
    simp only [Finset.mem_image] at hp hq
    obtain ⟨a, -, ha⟩ := hp
    obtain ⟨b, -, hb⟩ := hq
    exact hxy (congrArg Prod.snd (ha.trans hb.symm))
  rw [withinComponentPairs_eq_biUnion, Finset.card_biUnion hdisj,
    ← sum_range_succ_sub_eq_choose n k hk]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.card_image_of_injective _ (hinj j), Finset.card_range]

/-! ### Disjointness from the cross families -/

section Families

variable {W : Type u} {C : Type v}

/-- [definition] The cross family of an ordered pair of components: the pairs whose first
occurrence lies in `a` and whose second lies in `b`. -/
def crossPairs (comp : W → C) (a b : C) : Set (W × W) :=
  {p | comp p.1 = a ∧ comp p.2 = b}

/-- [definition] The within-component family of one component, at the level of which pairs it
reads. -/
def withinPairs (comp : W → C) (a : C) : Set (W × W) :=
  {p | comp p.1 = a ∧ comp p.2 = a}

theorem withinPairs_eq_crossPairs_self (comp : W → C) (a : C) :
    withinPairs comp a = crossPairs comp a a := rfl

/-- [proved-derived; formal-checked] Two cross families addressed differently are disjoint. -/
theorem crossPairs_disjoint (comp : W → C) {a b c d : C} (h : a ≠ c ∨ b ≠ d) :
    Disjoint (crossPairs comp a b) (crossPairs comp c d) := by
  rw [Set.disjoint_left]
  rintro p ⟨hp1, hp2⟩ ⟨hq1, hq2⟩
  rcases h with h | h
  · exact h (hp1.symm.trans hq1)
  · exact h (hp2.symm.trans hq2)

/-- [proved-derived; formal-checked] **The within-component family of `a` is disjoint from every
cross family that mentions `a` and any other component.** The two laws read different populations;
neither is a special case of the other, and nothing is read twice. -/
theorem withinPairs_disjoint_crossPairs (comp : W → C) {a b : C} (h : a ≠ b) :
    Disjoint (withinPairs comp a) (crossPairs comp a b) ∧
      Disjoint (withinPairs comp a) (crossPairs comp b a) :=
  ⟨crossPairs_disjoint comp (Or.inr h), crossPairs_disjoint comp (Or.inl h)⟩

end Families

/-! ## The covalent chain, and the cycle one contact closes

[definition] The presented chain's own steps are a **covalent** one-cell class: they are founded by
the presentation and stand in every member of the apertured family, whatever any aperture or
resolution says (`physical_constraint_grading.rs::EdgeProvenance::Polygonal`, whose predicate is
`is_covalent_backbone`). A within-component contact `(i, j)` therefore closes the chain segment
between its endpoints into a genuine `1`-cycle of `j − i + 1` one-cells: `j − i` covalent steps and
the one contact.

The three statements below are what "b₁ = 1" means here, with no `2`-cell in sight: the chain is a
cycle, it is not zero, and **every** cycle supported on those one-cells is an integer multiple of
it. The cycle module of the segment is therefore free of rank one, and since no `2`-cell has any of
these edges in its boundary, `H₁` of the segment is that module.
-/

section Segment

/-- [definition] The covalent one-cells of the chain segment from `i` to `j`. -/
def segmentEdges (i j : ℕ) : Finset (ConstraintCell ℕ) :=
  (Finset.Ico i j).image fun t => ConstraintCell.edge t (t + 1)

/-- [definition] The one-cell of the contact that closes the segment. -/
def contactEdge (i j : ℕ) : ConstraintCell ℕ := ConstraintCell.edge i j

/-- [definition] Every one-cell of the closed loop: the covalent segment and the one contact. -/
def loopEdges (i j : ℕ) : Finset (ConstraintCell ℕ) :=
  insert (contactEdge i j) (segmentEdges i j)

/-- [definition] The covalent path chain from `i` to `j`. -/
def backbonePath (i j : ℕ) : GradedChain (ConstraintCell ℕ) :=
  ∑ t ∈ Finset.Ico i j, Finsupp.single (ConstraintCell.edge t (t + 1)) (1 : ℤ)

/-- [definition] The cycle a within-component contact `(i, j)` closes over the covalent segment. -/
def backboneContactCycle (i j : ℕ) : GradedChain (ConstraintCell ℕ) :=
  backbonePath i j - Finsupp.single (contactEdge i j) 1

private theorem edge_step_injective :
    Function.Injective fun t : ℕ => ConstraintCell.edge t (t + 1) := by
  intro a b hab
  simp only [ConstraintCell.edge.injEq] at hab
  exact hab.1

theorem segmentEdges_card (i j : ℕ) : (segmentEdges i j).card = j - i := by
  rw [segmentEdges, Finset.card_image_of_injective _ edge_step_injective, Nat.card_Ico]

theorem contactEdge_not_mem_segmentEdges {i j : ℕ} (h : i + 2 ≤ j) :
    contactEdge i j ∉ segmentEdges i j := by
  intro hmem
  simp only [segmentEdges, Finset.mem_image, Finset.mem_Ico] at hmem
  obtain ⟨t, ⟨hti, htj⟩, heq⟩ := hmem
  simp only [contactEdge, ConstraintCell.edge.injEq] at heq
  omega


/-- [proved-derived; formal-checked] **The loop has `j − i + 1` one-cells**: the `j − i` covalent
steps of the chain segment and the one contact that closes it. A separation of at least two is what
makes the contact a cell the segment does not already carry. -/
theorem loopEdges_card {i j : ℕ} (h : i + 2 ≤ j) : (loopEdges i j).card = j - i + 1 := by
  rw [loopEdges, Finset.card_insert_of_notMem (contactEdge_not_mem_segmentEdges h),
    segmentEdges_card]

/-- [proved-derived; formal-checked] The covalent path's boundary is its two ends. -/
theorem d_backbonePath {i j : ℕ} (h : i ≤ j) :
    dConstraint (backbonePath i j) =
      Finsupp.single (ConstraintCell.vertex j) (1 : ℤ) -
        Finsupp.single (ConstraintCell.vertex i) 1 := by
  induction j, h using Nat.le_induction with
  | base => simp [backbonePath]
  | succ n hn ih =>
      rw [backbonePath, Finset.sum_Ico_succ_top hn, map_add, ← backbonePath, ih,
        dConstraint_single, one_smul]
      simp only [cellBoundary]
      abel

/-- [proved-derived; formal-checked] **The contact closes a cycle.** No hypothesis beyond
`i ≤ j`. -/
theorem backboneContactCycle_is_cycle {i j : ℕ} (h : i ≤ j) :
    dConstraint (backboneContactCycle i j) = 0 := by
  rw [backboneContactCycle, map_sub, d_backbonePath h, dConstraint_single, one_smul]
  simp only [contactEdge, cellBoundary]
  abel

private theorem backbonePath_apply_contactEdge {i j : ℕ} (h : i + 2 ≤ j) :
    backbonePath i j (contactEdge i j) = 0 := by
  rw [backbonePath, Finset.sum_apply']
  refine Finset.sum_eq_zero fun t ht => ?_
  rw [Finsupp.single_apply, if_neg]
  rw [Finset.mem_Ico] at ht
  simp only [contactEdge, ConstraintCell.edge.injEq, not_and]
  omega

/-- [proved-derived; formal-checked] The cycle is not zero: its coefficient on the closing contact
is `−1`. -/
theorem backboneContactCycle_ne_zero {i j : ℕ} (h : i + 2 ≤ j) :
    backboneContactCycle i j ≠ 0 := by
  intro hzero
  have := congrArg (fun c : GradedChain (ConstraintCell ℕ) => c (contactEdge i j)) hzero
  simp only [backboneContactCycle, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same,
    backbonePath_apply_contactEdge h, Finsupp.coe_zero, Pi.zero_apply] at this
  omega

theorem backbonePath_support (i j : ℕ) :
    (backbonePath i j).support ⊆ segmentEdges i j := by
  classical
  intro e he
  rw [backbonePath] at he
  obtain ⟨t, ht, hte⟩ := Finsupp.mem_support_finsetSum e he
  have : e = ConstraintCell.edge t (t + 1) :=
    Finset.mem_singleton.mp (Finsupp.support_single_subset hte)
  subst this
  exact Finset.mem_image_of_mem _ ht

theorem backboneContactCycle_support (i j : ℕ) :
    (backboneContactCycle i j).support ⊆ loopEdges i j := by
  classical
  intro e he
  rw [backboneContactCycle] at he
  have hmem := Finset.mem_of_subset (Finsupp.support_sub) he
  rw [Finset.mem_union] at hmem
  rcases hmem with he | he
  · exact Finset.mem_insert_of_mem (backbonePath_support i j he)
  · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset he)]
    exact Finset.mem_insert_self _ _

/-- The coefficient reading of `dConstraint` at one cell. -/
theorem dConstraint_apply (c : GradedChain (ConstraintCell ℕ)) (x : ConstraintCell ℕ) :
    dConstraint c x = ∑ e ∈ c.support, c e * (cellBoundary e) x := by
  classical
  rw [dConstraint, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply']
  exact Finset.sum_congr rfl fun e _ => by rw [Finsupp.smul_apply, smul_eq_mul]

/-- [proved-derived; formal-checked] **A cycle carried by the covalent segment alone is zero.**
A path carries no cycle; this is the half of the rank-one statement that the closing contact
supplies the other half of. -/
theorem segment_cycle_is_zero {i : ℕ} :
    ∀ j, i ≤ j → ∀ c : GradedChain (ConstraintCell ℕ),
      c.support ⊆ segmentEdges i j → dConstraint c = 0 → c = 0 := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base =>
      intro c hsupport _
      rw [segmentEdges, Finset.Ico_self, Finset.image_empty, Finset.subset_empty] at hsupport
      exact Finsupp.support_eq_empty.mp hsupport
  | succ n hn ih =>
      intro c hsupport hcycle
      -- The top vertex `n + 1` is carried by the top covalent step and by nothing else, so the
      -- vanishing boundary reads that step's coefficient off directly.
      have htop : c (ConstraintCell.edge n (n + 1)) = 0 := by
        have := congrArg (fun d : GradedChain (ConstraintCell ℕ) =>
          d (ConstraintCell.vertex (n + 1))) hcycle
        rw [dConstraint_apply] at this
        simp only [Finsupp.coe_zero, Pi.zero_apply] at this
        rw [Finset.sum_eq_single (ConstraintCell.edge n (n + 1))] at this
        · by_cases hmem : ConstraintCell.edge n (n + 1) ∈ c.support
          · simpa [cellBoundary, Finsupp.single_apply] using this
          · exact Finsupp.notMem_support_iff.mp hmem
        · intro e he hne
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (hsupport he)
          rw [Finset.mem_Ico] at ht
          have htn : t ≠ n := by
            rintro rfl
            exact hne rfl
          simp only [cellBoundary, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply,
            ConstraintCell.vertex.injEq]
          rw [if_neg (by omega), if_neg (by omega)]
          ring
        · intro hmem
          simp [Finsupp.notMem_support_iff.mp hmem]
      refine ih c ?_ hcycle
      intro e he
      have hin := hsupport he
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hin
      rw [Finset.mem_Ico] at ht
      have : t ≠ n := by
        rintro rfl
        exact (Finsupp.mem_support_iff.mp he) htop
      exact Finset.mem_image_of_mem _ (Finset.mem_Ico.mpr ⟨ht.1, by omega⟩)

/-- [proved-derived; formal-checked] **`b₁` of the covalent segment plus one contact is one.**
Every cycle supported on the loop's one-cells is an integer multiple of `backboneContactCycle`,
which is itself a cycle and is nonzero. The cycle module is therefore free of rank one; no `2`-cell
of the constraint complex has any of these one-cells in its boundary in this segment, so that
module is `H₁`.

Rust owner: the reading taken through
`crates/holonic-engine/src/physical_constraint_grading.rs::graded_constraint_family` and
`rebase_invariants`, measured by
`an_open_intra_chain_contact_is_the_difference_between_a_path_and_a_cycle`. -/
theorem segment_cycles_are_multiples {i j : ℕ} (h : i + 2 ≤ j)
    (c : GradedChain (ConstraintCell ℕ)) (hsupport : c.support ⊆ loopEdges i j)
    (hcycle : dConstraint c = 0) :
    ∃ a : ℤ, c = a • backboneContactCycle i j := by
  classical
  set a : ℤ := c (contactEdge i j) with ha
  refine ⟨-a, ?_⟩
  have hcyc := backboneContactCycle_is_cycle (i := i) (j := j) (by omega)
  set d : GradedChain (ConstraintCell ℕ) := c + a • backboneContactCycle i j with hd
  have hdcycle : dConstraint d = 0 := by rw [hd, map_add, hcycle, map_smul, hcyc, smul_zero,
    add_zero]
  have hdcontact : d (contactEdge i j) = 0 := by
    have hcoeff : (backboneContactCycle i j) (contactEdge i j) = -1 := by
      simp only [backboneContactCycle, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same,
        backbonePath_apply_contactEdge h]
      ring
    rw [hd]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, hcoeff,
      smul_eq_mul, ← ha]
    ring
  have hdsupport : d.support ⊆ segmentEdges i j := by
    intro e he
    have hloop : e ∈ loopEdges i j := by
      have := Finsupp.support_add (g₁ := c) (g₂ := a • backboneContactCycle i j)
      rw [hd] at he
      have hmem := Finset.mem_of_subset this he
      rw [Finset.mem_union] at hmem
      rcases hmem with hmem | hmem
      · exact hsupport hmem
      · exact backboneContactCycle_support i j
          (Finset.mem_of_subset Finsupp.support_smul hmem)
    rcases Finset.mem_insert.mp hloop with rfl | hmem
    · exact absurd (Finsupp.mem_support_iff.mp he) (by rw [hdcontact]; simp)
    · exact hmem
  have hzero := segment_cycle_is_zero (i := i) j (by omega) d hdsupport hdcycle
  rw [hd] at hzero
  have hc : c = -(a • backboneContactCycle i j) := by
    rw [← sub_eq_zero, sub_neg_eq_add]
    exact hzero
  rw [hc, neg_smul]

end Segment

section Audit

#print axioms d_comp_d
#print axioms d_d_apply
#print axioms classify_eq_inside_iff
#print axioms classify_eq_outside_iff
#print axioms classify_eq_openContact_iff
#print axioms classify_point_ne_openContact
#print axioms decided_admission_is_resolution_free
#print axioms openContact_is_plural
#print axioms determinate_of_no_openContact
#print axioms d_orientedEdge
#print axioms constraintComplex_d
#print axioms constraint_boundary_squared
#print axioms constraint_d_comp_d
#print axioms founded_face_boundary_stands
#print axioms adapter_contract

#print axioms withinComponentPairs_zero_contains_the_diagonal
#print axioms withinComponentPairs_lt
#print axioms withinComponentPairs_not_covalent
#print axioms withinComponentPairs_card
#print axioms crossPairs_disjoint
#print axioms withinPairs_disjoint_crossPairs
#print axioms loopEdges_card
#print axioms d_backbonePath
#print axioms backboneContactCycle_is_cycle
#print axioms backboneContactCycle_ne_zero
#print axioms segment_cycle_is_zero
#print axioms segment_cycles_are_multiples

end Audit

end Soma.Holonics.Foundation.AperturedGradedComplex
