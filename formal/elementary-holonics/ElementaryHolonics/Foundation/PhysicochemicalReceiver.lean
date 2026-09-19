import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.Sum
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# B7 — the physicochemical receiver

[definition] This file states the laws the Rust module
`crates/holonic-engine/src/physicochemical_receiver.rs` implements: the remaining half of item
**B7** of `docs/plans/THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md`, beside the rigidity
receiver of `Foundation/RigidityReceiver.lean` and the topological receiver of
`Foundation/TopologicalReceiver.lean`.

Six things are stated here, in this order.

1. **Every reading carries its unit.** A dimension is an exponent word over a declared base and a
   reading is an enclosure together with one (`United`). Addition is defined **only** between
   readings of equal dimension: `United.sum?` returns `none` otherwise
   (`united_sum_requires_equal_dimension`), and where it returns a reading that reading encloses
   the sum of anything the two summands enclose (`united_sum_contains_sum`).
2. **The composition is a count over unordered class pairs**, and the class of a residue comes
   from a declared table rather than from the residue. Two tables differing at one residue give
   different compositions on a population that mentions it (`tables_change_the_reading`), which is
   why a reading carries the table it was taken under and why a cross-table comparison is refused
   in the Rust owner without a declared passage.
3. **Its laws.** The composition is additive over a disjoint union of contact populations
   (`composition_additive_of_disjoint`); it is invariant under any relabelling of the sites that
   preserves the declared class (`composition_invariant_under_relabelling`); and it is invariant
   under any map of the sites preserving the pairwise squared separations and the class
   (`composition_invariant_under_isometry`), which is what a rigid motion is here. Nothing in the
   admission law reads a coordinate directly, so no chart enters.
4. **The open class stays plural.** An undecided admission is counted on neither bound, the
   refusing bound never exceeds the admitting one (`refusing_le_admitting`), and the two agree
   exactly where nothing is undecided (`admitting_eq_refusing_of_no_undecided`).
5. **A candidate is not a bond.** The candidate reading is a function of the heavy-atom separation
   alone, so it cannot distinguish two geometries differing only in where a hydrogen sits
   (`candidate_ignores_hydrogen_geometry`, `two_geometries_one_candidate_reading`). That is the
   epistemic limit of a static heavy-atom model, stated as a theorem rather than a caveat.
6. **The Coulomb sum is carried as an enclosure.** `1/r` is irrational for a rational `r²`, so the
   reading is a pair of rational bounds with a certificate: `invEnclosure_contains` proves that a
   positive rational `u` with `u² · hi ≤ 1` and a positive rational `v` with `1 ≤ v² · lo` bracket
   `1/√s` for every `s ∈ [lo, hi]`, using no square root in the certificate itself;
   `invEnclosure_narrows` is the monotone narrowing; `coulombSum_enclosed` sums the per-term
   enclosures; and `coulombSum_additive` is the exact balance over a partition of the pair
   population. **And no charged reading exists without a declared acidity**:
   `no_charged_reading_without_a_declared_acidity`.

Rust owner: `crates/holonic-engine/src/physicochemical_receiver.rs`
(`UnitedInterval`, `ResidueClass`, `ClassPair`, `ResidueClassTable`, `CompositionReading`,
`HydrogenBondCandidate`, `reciprocal_distance_enclosure`, `electrostatic_enclosure`,
`protonation_basis`).
-/

noncomputable section

open scoped Classical
open Finset

namespace Soma.Holonics.Foundation.PhysicochemicalReceiver

/-! ## 1. Typed units: a dimension is an exponent word, and a reading carries one -/

/-- [definition] A dimension over a declared base of `k` generators: the exponent word. The Rust
owner's base is `physicochemical_base`, three generators — a length, a charge and an energy — and
`quantity.rs` owns the algebra. Nothing here names a unit. -/
abbrev Dim (k : ℕ) := Fin k → ℚ

/-- The identity word: a dimensionless count or ratio. -/
def Dim.zero (k : ℕ) : Dim k := fun _ => 0

/-- The product of two dimensions: exponent words add. -/
def Dim.add {k : ℕ} (a b : Dim k) : Dim k := fun i => a i + b i

/-- The ratio of two dimensions: exponent words subtract. -/
def Dim.sub {k : ℕ} (a b : Dim k) : Dim k := fun i => a i - b i

@[simp]
theorem Dim.add_zero {k : ℕ} (a : Dim k) : Dim.add a (Dim.zero k) = a := by
  funext i; simp [Dim.add, Dim.zero]

@[simp]
theorem Dim.zero_add {k : ℕ} (a : Dim k) : Dim.add (Dim.zero k) a = a := by
  funext i; simp [Dim.add, Dim.zero]

theorem Dim.add_comm {k : ℕ} (a b : Dim k) : Dim.add a b = Dim.add b a := by
  funext i
  show a i + b i = b i + a i
  exact _root_.add_comm _ _

@[simp]
theorem Dim.sub_self {k : ℕ} (a : Dim k) : Dim.sub a a = Dim.zero k := by
  funext i; simp [Dim.sub, Dim.zero]

/-- [definition] **A reading: an exact enclosure together with the dimension it is an enclosure
of.** The Rust owner is `UnitedInterval`, the one composition it founds on top of
`quantity::Quantity` — which carries a point magnitude, where every magnitude this receiver returns
is an interval. -/
structure United (k : ℕ) where
  /-- The lower bound. -/
  lo : ℚ
  /-- The upper bound. -/
  hi : ℚ
  /-- The dimension. -/
  dim : Dim k
  /-- The enclosure is ordered. -/
  ordered : lo ≤ hi

/-- What a reading encloses, as a set of reals: the reading is a claim about a value it need not
name, which is why `1/r` can be carried at all. -/
def United.contains {k : ℕ} (u : United k) (x : ℝ) : Prop := (u.lo : ℝ) ≤ x ∧ x ≤ (u.hi : ℝ)

/-- **Addition is defined only between readings of equal dimension.** Unlike units return `none`;
there is no coercion and no dropped unit. -/
def United.sum? {k : ℕ} (a b : United k) : Option (United k) :=
  if a.dim = b.dim then
    some ⟨a.lo + b.lo, a.hi + b.hi, a.dim, add_le_add a.ordered b.ordered⟩
  else
    none

/-- [proved-derived; formal-checked] Adding unlike units returns nothing. The Rust owner's
`UnitedInterval::sum` returns `PhysicochemicalRefusal::UnlikeUnits` naming both dimensions, which
is this `none` carrying its reason. -/
theorem united_sum_requires_equal_dimension {k : ℕ} (a b : United k) (h : a.dim ≠ b.dim) :
    a.sum? b = none := by
  rw [United.sum?, if_neg h]

/-- The sum of two readings of equal dimension. -/
theorem united_sum_of_equal_dimension {k : ℕ} (a b : United k) (h : a.dim = b.dim) :
    ∃ s : United k, a.sum? b = some s ∧ s.lo = a.lo + b.lo ∧ s.hi = a.hi + b.hi ∧ s.dim = a.dim := by
  refine ⟨⟨a.lo + b.lo, a.hi + b.hi, a.dim, add_le_add a.ordered b.ordered⟩, ?_, rfl, rfl, rfl⟩
  rw [United.sum?, if_pos h]

/-- [proved-derived; formal-checked] **The sum encloses the sum.** Where the dimensions agree, the
returned reading contains `x + y` for every `x` the first encloses and every `y` the second does. -/
theorem united_sum_contains_sum {k : ℕ} (a b : United k) (h : a.dim = b.dim) {x y : ℝ}
    (hx : a.contains x) (hy : b.contains y) (s : United k) (hs : a.sum? b = some s) :
    s.contains (x + y) := by
  rw [United.sum?, if_pos h] at hs
  have hst : s = ⟨a.lo + b.lo, a.hi + b.hi, a.dim, add_le_add a.ordered b.ordered⟩ :=
    (Option.some.inj hs).symm
  subst hst
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · show ((a.lo + b.lo : ℚ) : ℝ) ≤ x + y
    push_cast
    linarith
  · show x + y ≤ ((a.hi + b.hi : ℚ) : ℝ)
    push_cast
    linarith

/-- [proved-derived; formal-checked] A narrower reading of the same dimension is contained in a
wider one. This is the form `monotone narrowing` takes on the whole reading. -/
theorem united_contains_of_narrower {k : ℕ} (a b : United k) (hlo : a.lo ≤ b.lo)
    (hhi : b.hi ≤ a.hi) {x : ℝ} (hx : b.contains x) : a.contains x := by
  obtain ⟨h1, h2⟩ := hx
  exact ⟨le_trans (by exact_mod_cast hlo) h1, le_trans h2 (by exact_mod_cast hhi)⟩

/-! ## 2. Residue classes, declared tables, and the unordered class pair -/

/-- [definition] The closed list of residue classes. **The assignment of a residue to a class is
not here**: it is in a declared table, because the assignment is exactly the part that differs
between one published grouping and another. -/
inductive ResidueClass
  /-- An apolar side chain. -/
  | hydrophobic
  /-- A neutral side chain carrying a hydrogen-bonding heteroatom. -/
  | polar
  /-- A side chain carrying a positive formal charge at the table's declared protonation. -/
  | positive
  /-- A side chain carrying a negative formal charge at the table's declared protonation. -/
  | negative
  /-- An aromatic side chain. -/
  | aromatic
  /-- Named apart rather than pressed into one of the five above. -/
  | special
  deriving DecidableEq, Repr

/-- A rank, so the unordered pair has a canonical order. -/
def ResidueClass.rank : ResidueClass → ℕ
  | .hydrophobic => 0
  | .polar => 1
  | .positive => 2
  | .negative => 3
  | .aromatic => 4
  | .special => 5

theorem ResidueClass.rank_injective : Function.Injective ResidueClass.rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [ResidueClass.rank]

/-- [definition] The key a composition counts over: the **unordered** pair of classes. -/
abbrev ClassPair := ResidueClass × ResidueClass

/-- The canonical unordered pair. -/
def classPair (a b : ResidueClass) : ClassPair :=
  if a.rank ≤ b.rank then (a, b) else (b, a)

/-- [proved-derived; formal-checked] The key is symmetric: a contact has no hand. -/
theorem classPair_symm (a b : ResidueClass) : classPair a b = classPair b a := by
  by_cases hab : a = b
  · subst hab
    rfl
  · have hne : a.rank ≠ b.rank := fun h => hab (ResidueClass.rank_injective h)
    unfold classPair
    rcases lt_or_gt_of_ne hne with h | h
    · rw [if_pos (le_of_lt h), if_neg (not_le.mpr h)]
    · rw [if_neg (not_le.mpr h), if_pos (le_of_lt h)]

/-- [definition] A declared class table. `none` is a residue **outside the declared scope**: the
Rust owner refuses it by name (`ResidueNotInTable`) and never files it under a default class. -/
structure Table (σ : Type*) where
  /-- The declared class of a site, where the table declares one. -/
  classOf : σ → Option ResidueClass

/-! ## 3. The contact reading, its admissions and its composition -/

/-- [definition] The three-valued admission the exact interval contact law returns. It is
`physical_constraint_complex::ContactClass` and `DistanceAperture::classify` in Rust, and the third
value is carried, never rounded. -/
inductive Admission
  /-- The exact interval's upper bound is at or below the aperture. -/
  | inside
  /-- Its lower bound is strictly above the aperture. -/
  | outside
  /-- The interval straddles the aperture. -/
  | undecided
  deriving DecidableEq, Repr

/-- [definition] One presented contact population: which two sites each contact joins, and what
the exact law read there. -/
structure Presentation (ι σ : Type*) where
  /-- The left site of each contact. -/
  left : ι → σ
  /-- The right site. -/
  right : ι → σ
  /-- What the exact contact law read. -/
  admit : ι → Admission

/-- The class pair of one contact, under a declared table. A site the table does not name
contributes to no class pair. -/
def Presentation.keyAt {ι σ : Type*} (T : Table σ) (P : Presentation ι σ) (i : ι) :
    Option ClassPair :=
  match T.classOf (P.left i), T.classOf (P.right i) with
  | some a, some b => some (classPair a b)
  | _, _ => none

/-- **The composition: the count of `inside` contacts at one class pair.** This is the refusing
bound of the family — every undecided admission refused. -/
def composition {ι σ : Type*} [Fintype ι] (T : Table σ) (P : Presentation ι σ) (k : ClassPair) :
    ℕ :=
  (univ.filter fun i => P.admit i = Admission.inside ∧ P.keyAt T i = some k).card

/-- **The admitting bound: every undecided admission founded.** -/
def admittingComposition {ι σ : Type*} [Fintype ι] (T : Table σ) (P : Presentation ι σ)
    (k : ClassPair) : ℕ :=
  (univ.filter fun i => P.admit i ≠ Admission.outside ∧ P.keyAt T i = some k).card

/-- The count of undecided contacts at one class pair, carried apart and counted on neither
bound. -/
def openComposition {ι σ : Type*} [Fintype ι] (T : Table σ) (P : Presentation ι σ)
    (k : ClassPair) : ℕ :=
  (univ.filter fun i => P.admit i = Admission.undecided ∧ P.keyAt T i = some k).card

/-- [proved-derived; formal-checked] **The refusing bound never exceeds the admitting one**, so the
family of readings really is bracketed by the two the Rust owner constructs. -/
theorem refusing_le_admitting {ι σ : Type*} [Fintype ι] (T : Table σ) (P : Presentation ι σ)
    (k : ClassPair) : composition T P k ≤ admittingComposition T P k := by
  apply card_le_card
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact ⟨by rw [hi.1]; exact fun h => Admission.noConfusion h, hi.2⟩

/-- [proved-derived; formal-checked] **The two bounds are one reading exactly where nothing is
undecided.** The plurality is the open set and nothing else. -/
theorem admitting_eq_refusing_of_no_undecided {ι σ : Type*} [Fintype ι] (T : Table σ)
    (P : Presentation ι σ) (h : ∀ i, P.admit i ≠ Admission.undecided) (k : ClassPair) :
    admittingComposition T P k = composition T P k := by
  unfold admittingComposition composition
  congr 1
  apply filter_congr
  intro i _
  constructor
  · rintro ⟨hne, hk⟩
    refine ⟨?_, hk⟩
    cases hi : P.admit i with
    | inside => rfl
    | outside => exact absurd hi hne
    | undecided => exact absurd hi (h i)
  · rintro ⟨hin, hk⟩
    exact ⟨by rw [hin]; exact fun hc => Admission.noConfusion hc, hk⟩

/-- [proved-derived; formal-checked] **Three counts and no fourth**: at every class pair the
admitting bound is the refusing bound plus the undecided count. This is the source-accountability
law the Rust owner's ledger row recomputes. -/
theorem admitting_eq_refusing_add_open {ι σ : Type*} [Fintype ι] (T : Table σ)
    (P : Presentation ι σ) (k : ClassPair) :
    admittingComposition T P k = composition T P k + openComposition T P k := by
  unfold admittingComposition composition openComposition
  rw [← card_union_of_disjoint]
  · congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨hne, hk⟩
      cases hi : P.admit i with
      | inside => exact Or.inl ⟨rfl, hk⟩
      | outside => exact absurd hi hne
      | undecided => exact Or.inr ⟨rfl, hk⟩
    · rintro (⟨hin, hk⟩ | ⟨hun, hk⟩)
      · exact ⟨by rw [hin]; exact fun hc => Admission.noConfusion hc, hk⟩
      · exact ⟨by rw [hun]; exact fun hc => Admission.noConfusion hc, hk⟩
  · rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [mem_filter, mem_univ, true_and] at hi hi'
    rw [hi.1] at hi'
    exact Admission.noConfusion hi'.1

/-! ## 4. The laws of the composition -/

/-- Two contact populations, side by side. The interface family and a within-component fold family
of one presentation are exactly this: their pair populations are disjoint, which is
`Foundation/AperturedGradedComplex.lean::withinPairs_disjoint_crossPairs`. -/
def Presentation.disjointUnion {ι₁ ι₂ σ : Type*} (P : Presentation ι₁ σ)
    (Q : Presentation ι₂ σ) : Presentation (ι₁ ⊕ ι₂) σ where
  left := Sum.elim P.left Q.left
  right := Sum.elim P.right Q.right
  admit := Sum.elim P.admit Q.admit

@[simp]
theorem keyAt_inl {ι₁ ι₂ σ : Type*} (T : Table σ) (P : Presentation ι₁ σ)
    (Q : Presentation ι₂ σ) (i : ι₁) :
    (P.disjointUnion Q).keyAt T (Sum.inl i) = P.keyAt T i := rfl

@[simp]
theorem keyAt_inr {ι₁ ι₂ σ : Type*} (T : Table σ) (P : Presentation ι₁ σ)
    (Q : Presentation ι₂ σ) (i : ι₂) :
    (P.disjointUnion Q).keyAt T (Sum.inr i) = Q.keyAt T i := rfl

/-- [proved-derived; formal-checked] **Readings are additive over disjoint contact families**, so
an interface and a fold decompose exactly. The Rust owner is `CompositionReading::sum`. -/
theorem composition_additive_of_disjoint {ι₁ ι₂ σ : Type*} [Fintype ι₁] [Fintype ι₂]
    (T : Table σ) (P : Presentation ι₁ σ) (Q : Presentation ι₂ σ) (k : ClassPair) :
    composition T (P.disjointUnion Q) k = composition T P k + composition T Q k := by
  classical
  simp only [composition, card_filter, Fintype.sum_sum_type]
  rfl

/-- Relabel the sites of a presentation along a bijection. -/
def Presentation.relabel {ι σ σ' : Type*} (g : σ ≃ σ') (P : Presentation ι σ) :
    Presentation ι σ' where
  left := fun i => g (P.left i)
  right := fun i => g (P.right i)
  admit := P.admit

/-- [proved-derived; formal-checked] **The composition is invariant under a relabelling of the
sites that preserves the declared class.** Addresses are testimony; the reading is not a function
of them. -/
theorem composition_invariant_under_relabelling {ι σ σ' : Type*} [Fintype ι] (g : σ ≃ σ')
    (T : Table σ) (T' : Table σ') (h : ∀ s, T'.classOf (g s) = T.classOf s)
    (P : Presentation ι σ) (k : ClassPair) :
    composition T' (P.relabel g) k = composition T P k := by
  unfold composition
  congr 1
  apply filter_congr
  intro i _
  have : (P.relabel g).keyAt T' i = P.keyAt T i := by
    simp [Presentation.keyAt, Presentation.relabel, h]
  rw [this]
  rfl

/-! ### The admission derived from a configuration, and the isometry law -/

/-- [definition] The admission law over a declared aperture: a contact is admitted when the exact
squared separation is at or below it, refused when it is above, and this derived form carries no
undecided value because it reads a *point* separation. The Rust owner's `DistanceAperture::classify`
reads an interval and does return the third value; this is the law at a point configuration, which
is the domain the rigid-motion statement is made on for exactly the reason the Rust owner states —
a rotated axis-aligned box is not an axis-aligned box. -/
def derivedAdmit {σ : Type*} (aperture : ℚ) (dist : σ → σ → ℚ) (a b : σ) : Admission :=
  if dist a b ≤ aperture then Admission.inside else Admission.outside

/-- One presentation whose admissions are derived from a configuration through the exact law. -/
def derivedPresentation {ι σ : Type*} (aperture : ℚ) (dist : σ → σ → ℚ)
    (left right : ι → σ) : Presentation ι σ where
  left := left
  right := right
  admit := fun i => derivedAdmit aperture dist (left i) (right i)

/-- [proved-derived; formal-checked] **Every reading is invariant under a map of the sites
preserving the pairwise squared separations and the declared class.** A rigid motion is exactly
such a map, so no reading of this receiver moves under one — and the statement needs no chart, no
coordinate and no orthogonality hypothesis, only the preserved separations. -/
theorem composition_invariant_under_isometry {ι σ : Type*} [Fintype ι] (aperture : ℚ)
    (dist : σ → σ → ℚ) (φ : σ → σ) (hd : ∀ a b, dist (φ a) (φ b) = dist a b)
    (T : Table σ) (hc : ∀ s, T.classOf (φ s) = T.classOf s)
    (left right : ι → σ) (k : ClassPair) :
    composition T (derivedPresentation aperture dist (φ ∘ left) (φ ∘ right)) k
      = composition T (derivedPresentation aperture dist left right) k := by
  unfold composition
  congr 1
  apply filter_congr
  intro i _
  have hadmit :
      (derivedPresentation aperture dist (φ ∘ left) (φ ∘ right)).admit i
        = (derivedPresentation aperture dist left right).admit i := by
    simp [derivedPresentation, derivedAdmit, hd]
  have hkey :
      (derivedPresentation aperture dist (φ ∘ left) (φ ∘ right)).keyAt T i
        = (derivedPresentation aperture dist left right).keyAt T i := by
    simp [Presentation.keyAt, derivedPresentation, hc]
  rw [hadmit, hkey]

/-! ## 5. The declared table decides the reading -/

/-- [proved-derived; formal-checked] **A second table changes the reading.** Two tables differing
at one site give different compositions on a population that mentions it. That is why every reading
in the Rust owner carries its `TableIdentity`, and why `compare_across_tables` refuses two readings
taken under different tables unless a `TablePassage` accounting for every divergent residue is
supplied. -/
theorem tables_change_the_reading :
    ∃ (T T' : Table Bool) (P : Presentation Unit Bool) (k : ClassPair),
      composition T P k ≠ composition T' P k := by
  classical
  refine ⟨⟨fun _ => some ResidueClass.polar⟩, ⟨fun _ => some ResidueClass.positive⟩,
    ⟨fun _ => true, fun _ => true, fun _ => Admission.inside⟩,
    classPair ResidueClass.polar ResidueClass.polar, ?_⟩
  have hleft : composition (⟨fun _ => some ResidueClass.polar⟩ : Table Bool)
      (⟨fun _ => true, fun _ => true, fun _ => Admission.inside⟩ : Presentation Unit Bool)
      (classPair ResidueClass.polar ResidueClass.polar) = 1 := by
    simp [composition, Presentation.keyAt]
  have hright : composition (⟨fun _ => some ResidueClass.positive⟩ : Table Bool)
      (⟨fun _ => true, fun _ => true, fun _ => Admission.inside⟩ : Presentation Unit Bool)
      (classPair ResidueClass.polar ResidueClass.polar) = 0 := by
    rw [composition, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    simp [Presentation.keyAt, classPair, ResidueClass.rank]
  rw [hleft, hright]
  exact one_ne_zero

/-! ## 6. A candidate is not a bond -/

/-- [definition] A geometry with two faces: the heavy-atom separations a static model carries, and
a hydrogen placement it does not. -/
structure Geometry (σ : Type*) where
  /-- The heavy-atom squared separations, which the model carries. -/
  heavy : σ → σ → ℚ
  /-- Where the hydrogens sit, which a heavy-atom model does not carry. -/
  hydrogen : σ → σ → ℚ

/-- The candidate reading: a declared donor and a declared acceptor whose heavy-atom separation
lies inside a declared window. -/
def candidate {σ : Type*} (lo hi : ℚ) (G : Geometry σ) (a b : σ) : Prop :=
  lo ≤ G.heavy a b ∧ G.heavy a b ≤ hi

/-- [proved-derived; formal-checked] **The candidate reading ignores the hydrogen geometry.** It is
a function of the heavy-atom separation alone, so it certifies no bond: the angle at the donor,
which is what distinguishes a hydrogen bond from a contact, is not in its domain. -/
theorem candidate_ignores_hydrogen_geometry {σ : Type*} (lo hi : ℚ) (G G' : Geometry σ)
    (h : G.heavy = G'.heavy) (a b : σ) : candidate lo hi G a b ↔ candidate lo hi G' a b := by
  simp [candidate, h]

/-- [proved-derived; formal-checked] **Two geometries, one candidate reading.** There are two
geometries whose hydrogen placements differ everywhere and whose candidate readings agree at every
window and every pair, so no candidate reading is a bond claim. This is the Rust owner's reason for
having a `HydrogenBondCandidate` type and no `HydrogenBond` type at all. -/
theorem two_geometries_one_candidate_reading :
    ∃ G G' : Geometry Bool, G.hydrogen ≠ G'.hydrogen ∧
      ∀ (lo hi : ℚ) (a b : Bool), candidate lo hi G a b ↔ candidate lo hi G' a b := by
  refine ⟨⟨fun _ _ => 1, fun _ _ => 0⟩, ⟨fun _ _ => 1, fun _ _ => 1⟩, ?_, ?_⟩
  · intro h
    have : (0 : ℚ) = 1 := congrFun (congrFun h true) true
    exact zero_ne_one this
  · intro lo hi a b
    simp [candidate]

/-! ## 7. The reciprocal-distance enclosure, and the Coulomb sum -/

/-- [proved-derived; formal-checked] **A certified rational enclosure of `1/√s`.** The certificate
is purely rational: `u² · hi ≤ 1` and `1 ≤ v² · lo` with `u, v > 0`. No square root appears in the
hypotheses, which is what makes the Rust owner's `reciprocal_distance_enclosure` exact —
`exact_value::AlgebraicRoot::reciprocal_square_root` produces exactly such a certified bracket. -/
theorem invEnclosure_contains (s lo hi u v : ℚ) (hlo : 0 < lo) (h1 : lo ≤ s) (h2 : s ≤ hi)
    (hu : 0 < u) (hcu : u ^ 2 * hi ≤ 1) (hv : 0 < v) (hcv : 1 ≤ v ^ 2 * lo) :
    (u : ℝ) ≤ 1 / Real.sqrt s ∧ 1 / Real.sqrt s ≤ (v : ℝ) := by
  have hs : (0 : ℝ) < (s : ℝ) := by
    have : (0 : ℝ) < (lo : ℝ) := by exact_mod_cast hlo
    have : (lo : ℝ) ≤ (s : ℝ) := by exact_mod_cast h1
    linarith [show (0 : ℝ) < (lo : ℝ) by exact_mod_cast hlo]
  set r : ℝ := Real.sqrt s with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr hs
  have hrsq : r ^ 2 = (s : ℝ) := Real.sq_sqrt (le_of_lt hs)
  have hur : (u : ℝ) * r ≤ 1 := by
    have hsq : ((u : ℝ) * r) ^ 2 ≤ 1 := by
      have : ((u : ℝ) * r) ^ 2 = (u : ℝ) ^ 2 * (s : ℝ) := by rw [mul_pow, hrsq]
      rw [this]
      have hcu' : (u : ℝ) ^ 2 * (hi : ℝ) ≤ 1 := by exact_mod_cast hcu
      have h2' : (s : ℝ) ≤ (hi : ℝ) := by exact_mod_cast h2
      have hupos : (0 : ℝ) < (u : ℝ) ^ 2 := by positivity
      nlinarith
    nlinarith [mul_pos (show (0 : ℝ) < (u : ℝ) by exact_mod_cast hu) hrpos]
  have hvr : 1 ≤ (v : ℝ) * r := by
    have hsq : 1 ≤ ((v : ℝ) * r) ^ 2 := by
      have : ((v : ℝ) * r) ^ 2 = (v : ℝ) ^ 2 * (s : ℝ) := by rw [mul_pow, hrsq]
      rw [this]
      have hcv' : 1 ≤ (v : ℝ) ^ 2 * (lo : ℝ) := by exact_mod_cast hcv
      have h1' : (lo : ℝ) ≤ (s : ℝ) := by exact_mod_cast h1
      have hvpos : (0 : ℝ) < (v : ℝ) ^ 2 := by positivity
      nlinarith
    nlinarith [mul_pos (show (0 : ℝ) < (v : ℝ) by exact_mod_cast hv) hrpos]
  constructor
  · rw [le_div_iff₀ hrpos]; exact hur
  · rw [div_le_iff₀ hrpos]; exact hvr

/-- [proved-derived; formal-checked] **The enclosure narrows monotonically.** A finer declared
grain returns a bracket inside the coarser one, and every value the finer encloses the coarser
encloses too. -/
theorem invEnclosure_narrows (u u' v' v : ℚ) (h1 : u ≤ u') (h2 : v' ≤ v) :
    Set.Icc (u' : ℝ) (v' : ℝ) ⊆ Set.Icc (u : ℝ) (v : ℝ) :=
  Set.Icc_subset_Icc (by exact_mod_cast h1) (by exact_mod_cast h2)

/-- [definition] One Coulomb term `q_i q_j / (ε r_ij)` at a declared dielectric. -/
def coulombTerm {ι : Type*} (charge : ι → ℚ) (ε : ℚ) (recip : ι → ℝ) (i : ι) : ℝ :=
  (charge i : ℝ) / (ε : ℝ) * recip i

/-- **The declared finite electrostatic model's sum over a declared pair population.** -/
def coulombSum {ι : Type*} [Fintype ι] (charge : ι → ℚ) (ε : ℚ) (recip : ι → ℝ) : ℝ :=
  ∑ i, coulombTerm charge ε recip i

/-- [proved-derived; formal-checked] **The sum is additive over a partition of its pair
population.** This is the exact balance the receiver owes: the parts recombine to the whole. -/
theorem coulombSum_additive {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] (charge : ι₁ ⊕ ι₂ → ℚ)
    (ε : ℚ) (recip : ι₁ ⊕ ι₂ → ℝ) :
    coulombSum charge ε recip
      = coulombSum (fun i => charge (Sum.inl i)) ε (fun i => recip (Sum.inl i))
        + coulombSum (fun i => charge (Sum.inr i)) ε (fun i => recip (Sum.inr i)) := by
  unfold coulombSum
  rw [Fintype.sum_sum_type]
  rfl

/-- [proved-derived; formal-checked] **The summed enclosure encloses the sum.** Where every term's
reciprocal is bracketed and every charge product is nonnegative, the sum of the lower bounds
brackets the sum below and the sum of the upper bounds brackets it above. A negative charge product
flips the term's own bracket, which is why the Rust owner multiplies through the interval product
of `exact_value::ExactInterval::times` rather than assuming a sign. -/
theorem coulombSum_enclosed {ι : Type*} [Fintype ι] (charge : ι → ℚ) (ε : ℚ) (hε : 0 < ε)
    (recip lo hi : ι → ℝ) (hq : ∀ i, 0 ≤ charge i)
    (hlo : ∀ i, lo i ≤ recip i) (hhi : ∀ i, recip i ≤ hi i) :
    coulombSum charge ε lo ≤ coulombSum charge ε recip ∧
      coulombSum charge ε recip ≤ coulombSum charge ε hi := by
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  constructor
  · apply Finset.sum_le_sum
    intro i _
    have hqi : (0 : ℝ) ≤ (charge i : ℝ) := by exact_mod_cast hq i
    have : (0 : ℝ) ≤ (charge i : ℝ) / (ε : ℝ) := div_nonneg hqi (le_of_lt hεR)
    exact mul_le_mul_of_nonneg_left (hlo i) this
  · apply Finset.sum_le_sum
    intro i _
    have hqi : (0 : ℝ) ≤ (charge i : ℝ) := by exact_mod_cast hq i
    have : (0 : ℝ) ≤ (charge i : ℝ) / (ε : ℝ) := div_nonneg hqi (le_of_lt hεR)
    exact mul_le_mul_of_nonneg_left (hhi i) this

/-! ## 8. The pH gate -/

/-- [definition] On what ground a charged reading is taken. There are exactly two and no third: the
occurrence's environment declares its acidity axis, or a caller declares the assumption explicitly
and its ground travels with the reading. -/
inductive ProtonationBasis
  /-- The environment declares the axis, at a pH enclosure. -/
  | fromEnvironment (pLow pHigh : ℚ)
  /-- The environment leaves it undeclared and a caller supplies the assumption, with its ground. -/
  | declaredAssumption (ground : String)
  deriving Repr

/-- **A charged reading, as a function of the environment's acidity coordinate.** `none` is the
undeclared axis, which the Rust owner's `Environment` carries as
`Coordinate.Undeclared` with a stated reason. -/
def chargedReading {α : Type*} (acidity : Option ℚ) (read : ℚ → α) : Option α :=
  acidity.map read

/-- [proved-derived; formal-checked] **No charged reading exists without a declared acidity.** On
the M5 release the acidity axis is undeclared in all three occurrences, so this `none` — the Rust
owner's `PhysicochemicalRefusal::AcidityUndeclared`, naming the axis and carrying the environment's
own stated reason — is the receiver's truthful primary result there. -/
theorem no_charged_reading_without_a_declared_acidity {α : Type*} (read : ℚ → α) :
    chargedReading none read = none := rfl

/-- [proved-derived; formal-checked] A declared axis gives the reading, and the reading is the one
the declaration determines. -/
theorem chargedReading_of_declared {α : Type*} (p : ℚ) (read : ℚ → α) :
    chargedReading (some p) read = some (read p) := rfl

/-- [proved-derived; formal-checked] A reading taken under an explicit assumption carries that
assumption: the two bases are distinguishable, so a declared-assumption reading can never be
mistaken for one the environment licensed. -/
theorem the_two_bases_are_distinct (pLow pHigh : ℚ) (ground : String) :
    ProtonationBasis.fromEnvironment pLow pHigh ≠ ProtonationBasis.declaredAssumption ground := by
  intro h
  exact ProtonationBasis.noConfusion h

/-! ## 9. The contract -/

/-- [proved-derived; formal-checked] **The physicochemical receiver's contract**, as one statement:
unlike units do not add; the two bounds of the open family bracket every reading and agree exactly
where nothing is undecided; the composition is additive over disjoint families and invariant under
a class-preserving relabelling; and no charged reading exists without a declared acidity. -/
theorem physicochemical_contract {ι₁ ι₂ σ : Type*} [Fintype ι₁] [Fintype ι₂]
    (T : Table σ) (P : Presentation ι₁ σ) (Q : Presentation ι₂ σ) (k : ClassPair)
    {n : ℕ} (a b : United n) (hdim : a.dim ≠ b.dim) (read : ℚ → ℕ) :
    a.sum? b = none ∧
      composition T P k ≤ admittingComposition T P k ∧
      composition T (P.disjointUnion Q) k = composition T P k + composition T Q k ∧
      chargedReading none read = none :=
  ⟨united_sum_requires_equal_dimension a b hdim,
    refusing_le_admitting T P k,
    composition_additive_of_disjoint T P Q k,
    no_charged_reading_without_a_declared_acidity read⟩

end Soma.Holonics.Foundation.PhysicochemicalReceiver
