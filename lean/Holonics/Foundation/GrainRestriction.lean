import Holonics.Foundation.ContinuingTower
import Holonics.Foundation.AperturedGradedComplex

/-!
# Grain restriction, the coarse receiver's standing, and why the open class is not a residual

[definition] This file states the law behind
`docs/plans/THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md` item **B0**: what a coarse receiver
at a declared aperture actually preserves when a finer grain is available, and what it drops.

It is the first *physical* instance of carrier item **C4**
(`docs/plans/THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md`), and it is built from the two owners
deposited with C4 rather than beside them:

* `Foundation/ContinuingTower.lean` supplies `Tower`, `Transition`, `reopen_apply`,
  `laterReceiverFactors` and `residual_separates`. Nothing here reproves them.
* `Foundation/AperturedGradedComplex.lean` supplies `ContactClass`, `classify`, `Resolution`,
  `admits`, `decided_admission_is_resolution_free` and `openContact_is_plural`. Nothing here
  reproves them either.

## Rust counterpart

[definition] The paired executable owner is `crates/holonic-engine/src/grain_tower.rs`, which names
this file and every declaration below. The correspondence, both directions:

| Lean | Rust |
|---|---|
| `Grain`, `Grain.rank`, the `Preorder` instance | `grain_tower.rs::Grain`, `Grain::refines`, `Grain::rank` |
| `classRank`, `classJoin`, `classJoin_comm`, `classJoin_assoc`, `classJoin_idem`, `classJoin_outside` | `grain_tower.rs::{contact_class_rank, join_contact_class}` |
| `classJoin_eq_inside_iff`, `foldr_classJoin_eq_inside_iff` | `grain_tower.rs::GrainFace::restricted` |
| `FineInside`, `FineAdmissible` | the `Inside` / non-`Outside` arms of `GrainFace::restricted` |
| `selectionReading` | `impl Transition for GrainSelection`'s `apply` |
| `selection_inside_implies_fine_inside` | `GrainCensus::coarse_only_inside`, checked to be `0` |
| `equal_aperture_is_not_lawful` | `GrainCensus::fine_only_inside`, measured `> 0` |
| `selectionTower` | `impl Tower for GrainTower` and `check_restriction_laws` |
| `selectionTransition`, `grain_residual_reopens_the_source` | `GrainSelection`, `check_grain_reopen` |
| `fineReading_factors` | `GrainSelection::reopen_fine_reading` |
| `residual_separates_fineOnly` | `Transition::separating_residuals` on `GrainFace::without` |
| `PseudoDistance`, `GrainRadius`, `coarse_distance_le_fine_aperture_add_radii` | `CoarseReading::{lower_grain_radius, upper_grain_radius}`, `certified_coarse_aperture_squared` |
| `ApertureRelation` | `grain_tower.rs::ApertureRelation` |
| `inflated_carries_every_fine_contact` | `InflationWitness::{measure, check_declared}` |
| `independent_is_mutual_insufficiency` | `IndependenceDeclaration::declare` |
| `nativeFine_refusal_is_a_residual_difference` | `FineNativeDeclaration::admit_coarse` |
| `open_admission_is_not_a_residual`, `residual_does_not_close_an_open_reading`, `narrower_interval_decides` | the residual/open verdict in `grain_tower.rs`'s header |

## The measured fact this states the law for

[established-bounded; measured] `crates/holonic-life/examples/m5/cif.rs::REPRESENTATIVE` filters intake to `CA`
rows, so no atom-grain face is ever founded and the atom→residue restriction is asserted by the act
of selection. Over the 70,632 residue pairs the M5 deed classified, at an equal 8 Å aperture in
exact rational arithmetic, the alpha-carbon receiver returns 301 `Inside` where the complete
atom-grain restriction returns 1,397, with 0 pairs in the other direction. The 0 is
`selection_inside_implies_fine_inside`; the 1,096 is `equal_aperture_is_not_lawful`. The least
coarse aperture that carries every fine contact on that data is `116656202097359145/10^14`, that is
34.1550 Å or 4.2694 times the fine aperture, attained where a CUL1 residue's own carbonyl oxygen
sits 27.6 Å from its alpha carbon — a grain radius large enough that
`coarse_distance_le_fine_aperture_add_radii` forces exactly that inflation. Exhibiting the witness
is what makes the number a measurement and not a safety factor. Both open
readings — one at each grain — are at different pairs, which is
`residual_does_not_close_an_open_reading` and `narrower_interval_decides` together: the `Open` class
lives on the precision axis of the index and the tower's `restrict` has no component along it.
-/

namespace Holonics.Foundation.GrainRestriction

open Holonics
open Holonics.Foundation.ContinuingTower
open Holonics.Foundation.AperturedGradedComplex

universe u v w

/-! ## The grain axis of the index -/

/-- [definition] The grain axis of the carrier's index. `component` is coarsest and `atom` finest.

Rust counterpart: `crates/holonic-engine/src/grain_tower.rs::Grain`. -/
inductive Grain where
  /-- One presented chain, entity or component. -/
  | component
  /-- One monomer of a component. -/
  | residue
  /-- One atom of a monomer. -/
  | atom
  deriving DecidableEq, Repr

/-- [definition] The refinement rank. Rust counterpart: `Grain::rank`. -/
def Grain.rank : Grain → ℕ
  | .component => 0
  | .residue => 1
  | .atom => 2

/-- [definition] The refinement order: `component ≤ residue ≤ atom`, so that a face at the finer
grain restricts to a face at the coarser one, exactly as `Tower.restrict` demands. -/
instance : Preorder Grain where
  le a b := a.rank ≤ b.rank
  le_refl _ := Nat.le_refl _
  le_trans _ _ _ := Nat.le_trans

/-- [proved-derived; formal-checked] The chain the physical instance uses. -/
theorem grain_chain : (Grain.component ≤ Grain.residue) ∧ (Grain.residue ≤ Grain.atom) :=
  ⟨by decide, by decide⟩

/-- [proved-derived; formal-checked] The order is strict: the atom grain does not refine into the
residue grain. -/
theorem atom_does_not_refine_downwards : ¬ (Grain.atom ≤ Grain.residue) := by decide

/-! ## The contact-class join

`Foundation/AperturedGradedComplex.lean` owns `ContactClass` and its aperture trichotomy. The
restriction to a coarser grain takes the join over the block in the order
`outside < openContact < inside`. -/

/-- [definition] `outside = 0 < openContact = 1 < inside = 2`.

Rust counterpart: `grain_tower.rs::contact_class_rank`. -/
def classRank : ContactClass → ℕ
  | .outside => 0
  | .openContact => 1
  | .inside => 2

/-- [definition] The join of the class order: a coarse cell is `inside` when some fine member is,
`openContact` when none is `inside` and some is open, and `outside` only when every member is.

Rust counterpart: `grain_tower.rs::join_contact_class`. -/
def classJoin : ContactClass → ContactClass → ContactClass
  | .inside, _ => .inside
  | _, .inside => .inside
  | .openContact, _ => .openContact
  | _, .openContact => .openContact
  | .outside, .outside => .outside

@[simp] theorem classJoin_idem (a : ContactClass) : classJoin a a = a := by
  cases a <;> rfl

theorem classJoin_comm (a b : ContactClass) : classJoin a b = classJoin b a := by
  cases a <;> cases b <;> rfl

theorem classJoin_assoc (a b c : ContactClass) :
    classJoin (classJoin a b) c = classJoin a (classJoin b c) := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp] theorem classJoin_outside (a : ContactClass) : classJoin a ContactClass.outside = a := by
  cases a <;> rfl

@[simp] theorem outside_classJoin (a : ContactClass) : classJoin ContactClass.outside a = a := by
  cases a <;> rfl

/-- [proved-derived; formal-checked] The join is `inside` exactly when one side is. This is the
`Inside` arm of the Rust owner's `GrainFace::restricted`. -/
@[simp] theorem classJoin_eq_inside_iff (a b : ContactClass) :
    classJoin a b = ContactClass.inside ↔ a = ContactClass.inside ∨ b = ContactClass.inside := by
  cases a <;> cases b <;> simp [classJoin]

/-- [proved-derived; formal-checked] The join is `outside` exactly when both sides are. -/
theorem classJoin_eq_outside_iff (a b : ContactClass) :
    classJoin a b = ContactClass.outside ↔
      a = ContactClass.outside ∧ b = ContactClass.outside := by
  cases a <;> cases b <;> simp [classJoin]

/-- [proved-derived; formal-checked] The join over a whole block is `inside` exactly when some
member of the block is. The Rust owner folds this join over each coarse pair's block, so this is
the equation that identifies its return with the existential `FineInside` below. -/
theorem foldr_classJoin_eq_inside_iff (block : List ContactClass) :
    block.foldr classJoin ContactClass.outside = ContactClass.inside ↔
      ContactClass.inside ∈ block := by
  induction block with
  | nil => simp
  | cons head tail ih =>
    rw [List.foldr_cons, List.mem_cons, classJoin_eq_inside_iff, ih]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

/-! ## The two readings a coarse grain admits -/

variable {FineCell : Type u} {CoarseCell : Type v}

/-- [definition] The coarse pair `(i,j)` is `inside` for the fine face `φ` when *some* fine pair
over it is. This is the `Inside` arm of the join restriction, stated without a finiteness
hypothesis.

Rust counterpart: `grain_tower.rs::GrainFace::restricted`. -/
def FineInside (π : FineCell → CoarseCell) (φ : FineCell → FineCell → ContactClass)
    (i j : CoarseCell) : Prop :=
  ∃ a b, π a = i ∧ π b = j ∧ φ a b = ContactClass.inside

/-- [definition] The coarse pair is *admissible* when some fine pair over it is not `outside`. -/
def FineAdmissible (π : FineCell → CoarseCell) (φ : FineCell → FineCell → ContactClass)
    (i j : CoarseCell) : Prop :=
  ∃ a b, π a = i ∧ π b = j ∧ φ a b ≠ ContactClass.outside

/-- [proved-derived; formal-checked] An `inside` fine pair is admissible. -/
theorem fineAdmissible_of_fineInside {π : FineCell → CoarseCell}
    {φ : FineCell → FineCell → ContactClass} {i j : CoarseCell} (h : FineInside π φ i j) :
    FineAdmissible π φ i j := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  exact ⟨a, b, ha, hb, by rw [hab]; exact fun h => ContactClass.noConfusion h⟩

/-- [definition] The **selection reading**: the coarse pair carries the class of one declared
representative fine pair. This is the receiver `crates/holonic-life/examples/m5/cif.rs::REPRESENTATIVE` enacts
by discarding every non-`CA` row before anything is founded.

Rust counterpart: `impl Transition for GrainSelection`'s `apply`. -/
def selectionReading (sel : CoarseCell → FineCell) (φ : FineCell → FineCell → ContactClass)
    (i j : CoarseCell) : ContactClass :=
  φ (sel i) (sel j)

/-- [proved-derived; formal-checked] **Coarse implies fine.** A selected pair is a fine pair, so
every contact the coarse receiver admits is a contact the fine restriction admits. This is the
theorem the Rust owner *checks* rather than assumes: `GrainCensus::coarse_only_inside` is measured
and must be `0`. -/
theorem selection_inside_implies_fine_inside (π : FineCell → CoarseCell)
    (sel : CoarseCell → FineCell) (hsec : ∀ i, π (sel i) = i)
    (φ : FineCell → FineCell → ContactClass) {i j : CoarseCell}
    (h : selectionReading sel φ i j = ContactClass.inside) : FineInside π φ i j :=
  ⟨sel i, sel j, hsec i, hsec j, h⟩

/-- [definition] The smallest presentation that separates the two readings: two fine cells over one
coarse cell, where the *unselected* pair is the contact. -/
def twoCellFace : Bool → Bool → ContactClass :=
  fun a b => if a && b then ContactClass.inside else ContactClass.outside

/-- [counterexample; formal-checked] **At an equal aperture the converse fails.** The fine
restriction admits a contact that the selection reading does not, so the selection is not the
restriction and no `ApertureRelation` arm may be assumed by default.

Rust counterpart: the measured `GrainCensus::fine_only_inside`, which is 1,096 of 1,397 over the
M5 fixture. -/
theorem equal_aperture_is_not_lawful :
    FineInside (fun _ : Bool => ()) twoCellFace () () ∧
      selectionReading (fun _ : Unit => false) twoCellFace () () ≠ ContactClass.inside := by
  refine ⟨⟨true, true, rfl, rfl, rfl⟩, ?_⟩
  intro h
  exact ContactClass.noConfusion h

/-- [counterexample; formal-checked] The same statement as a `Foundation/Receiver.lean`
insufficiency: the selection reading merges what the fine restriction separates. -/
def selection_is_insufficient_for_the_fine_reading :
    ReceiverInsufficiency
      (fun φ : Bool → Bool → ContactClass => selectionReading (fun _ : Unit => false) φ)
      (fun φ : Bool → Bool → ContactClass => FineInside (fun _ : Bool => ()) φ) where
  left := twoCellFace
  right := fun _ _ => ContactClass.outside
  sameEntering := by
    funext i j
    rfl
  differentReturned := by
    intro h
    have h' : FineInside (fun _ : Bool => ()) twoCellFace () () ↔
        FineInside (fun _ : Bool => ()) (fun _ _ => ContactClass.outside) () () := by
      rw [h]
    obtain ⟨_, _, _, _, hcontact⟩ := h'.mp ⟨true, true, rfl, rfl, rfl⟩
    exact ContactClass.noConfusion hcontact

/-! ## The grain tower

A selection is a *lawful* `Tower`: `restrict_refl` and `restrict_trans` both hold for it. That is
exactly the trap this file exists to name. Being a tower does not make the selection the
restriction, and nothing in the tower's laws can detect the difference — only the
`ApertureRelation` below can. -/

/-- [definition] The grain tower whose restriction is a declared selection: the face at a grain is
the classification of its pairs, and the coarser face reads the finer one at each coarse cell's
representative.

Rust counterpart: `impl Tower for GrainTower` in `crates/holonic-engine/src/grain_tower.rs`, whose
`restrict_refl`/`restrict_trans` are returned as a `RestrictionReceipt` by
`continuing_tower.rs::check_restriction_laws`. -/
def selectionTower (Cell : Grain → Type w)
    (sel : ∀ {i j : Grain}, i ≤ j → Cell i → Cell j)
    (sel_refl : ∀ (i : Grain) (x : Cell i), sel (le_refl i) x = x)
    (sel_trans : ∀ {i j k : Grain} (hij : i ≤ j) (hjk : j ≤ k) (x : Cell i),
      sel hjk (sel hij x) = sel (le_trans hij hjk) x) :
    Tower.{0, w} Grain where
  Face := fun g => Cell g → Cell g → ContactClass
  restrict := fun {_ _} h φ a b => φ (sel h a) (sel h b)
  restrict_refl := by
    intro i φ
    funext a b
    rw [sel_refl, sel_refl]
  restrict_trans := by
    intro i j k hij hjk φ
    funext a b
    show φ (sel hjk (sel hij a)) (sel hjk (sel hij b)) =
      φ (sel (le_trans hij hjk) a) (sel (le_trans hij hjk) b)
    rw [sel_trans, sel_trans]

/-- [proved-derived; formal-checked] The selection tower's restriction *is* the selection reading.
The two vocabularies name one map. -/
theorem selectionTower_restrict (Cell : Grain → Type w) (sel sel_refl sel_trans)
    {i j : Grain} (h : i ≤ j) (φ : Cell j → Cell j → ContactClass) (a b : Cell i) :
    (selectionTower Cell sel sel_refl sel_trans).restrict h φ a b = φ (sel h a) (sel h b) :=
  rfl

/-! ## The selection as a non-invertible transition carrying its residual -/

variable [DecidableEq FineCell]

/-- [definition] The selection receiver as a `Foundation/ContinuingTower.lean::Transition`. `apply`
is the coarse reading, `residual` is the fine face the reading never looked at, and `reopen` uses
the coarse face exactly where the coarse face can speak — on pairs of representatives — and the
residual everywhere else.

Rust counterpart: `impl Transition for GrainSelection` in
`crates/holonic-engine/src/grain_tower.rs`, with `check_grain_reopen` as the executable receipt. -/
def selectionTransition (π : FineCell → CoarseCell) (sel : CoarseCell → FineCell) :
    Transition (FineCell → FineCell → ContactClass) (CoarseCell → CoarseCell → ContactClass) where
  Residual := FineCell → FineCell → ContactClass
  apply := fun φ i j => φ (sel i) (sel j)
  residual := fun φ => φ
  reopen := fun t ρ a b => if sel (π a) = a ∧ sel (π b) = b then t (π a) (π b) else ρ a b
  reopen_apply := by
    intro φ
    funext a b
    by_cases h : sel (π a) = a ∧ sel (π b) = b
    · rw [if_pos h]
      show φ (sel (π a)) (sel (π b)) = φ a b
      rw [h.1, h.2]
    · rw [if_neg h]

@[simp] theorem selectionTransition_apply (π : FineCell → CoarseCell) (sel : CoarseCell → FineCell)
    (φ : FineCell → FineCell → ContactClass) (i j : CoarseCell) :
    (selectionTransition π sel).apply φ i j = selectionReading sel φ i j := rfl

/-- [proved-derived; formal-checked] **The grain residual is a function of the source, and it
reopens the source exactly.** This is the half of the residual/open verdict that holds.

Rust counterpart: `grain_tower.rs::check_grain_reopen`, which returns this equation as a receipt on
the measured presentation. -/
theorem grain_residual_reopens_the_source (π : FineCell → CoarseCell) (sel : CoarseCell → FineCell)
    (φ : FineCell → FineCell → ContactClass) :
    (selectionTransition π sel).reopen ((selectionTransition π sel).apply φ)
        ((selectionTransition π sel).residual φ) = φ :=
  (selectionTransition π sel).reopen_apply φ

/-- [proved-derived; formal-checked] **The coarse face together with the residual returns the fine
reading.** This is `Foundation/ContinuingTower.lean::Transition.laterReceiverFactors` at the grain
transition — not a second proof — and it is the deliverable equation the Rust owner checks on the
measured presentation.

Rust counterpart: `grain_tower.rs::GrainSelection::reopen_fine_reading`. -/
theorem fineReading_factors (π : FineCell → CoarseCell) (sel : CoarseCell → FineCell) :
    ∃ recover : (CoarseCell → CoarseCell → ContactClass) →
        (FineCell → FineCell → ContactClass) → (CoarseCell → CoarseCell → Prop),
      ∀ φ, recover ((selectionTransition π sel).apply φ)
          ((selectionTransition π sel).residual φ) = fun i j => FineInside π φ i j :=
  (selectionTransition π sel).laterReceiverFactors (fun φ i j => FineInside π φ i j)

/-- [proved-derived; formal-checked] **The residual carries the disagreement.** Two fine faces with
one coarse face whose fine readings differ must have different residuals. This is
`Transition.residual_separates`, and the Rust owner instantiates it on measured data by deleting
exactly the fine-only contacts from the atom-grain face: the coarse face is unchanged, the fine
reading is not, and the two residuals therefore differ.

Rust counterpart: `Transition::separating_residuals` applied to `GrainFace::without`. -/
theorem residual_separates_fineOnly (π : FineCell → CoarseCell) (sel : CoarseCell → FineCell)
    {φ ψ : FineCell → FineCell → ContactClass}
    (hsame : (selectionTransition π sel).apply φ = (selectionTransition π sel).apply ψ)
    (hdiff : (fun i j => FineInside π φ i j) ≠ fun i j => FineInside π ψ i j) :
    (selectionTransition π sel).residual φ ≠ (selectionTransition π sel).residual ψ :=
  (selectionTransition π sel).residual_separates
    (fun χ : FineCell → FineCell → ContactClass => fun i j => FineInside π χ i j) hsame hdiff

/-! ## What an inflated coarse aperture preserves

The inflation is not a safety factor. It is forced by the *grain radius* — the distance from a
coarse cell's representative to its own farthest member — through the triangle inequality, and the
Rust owner measures that radius rather than assuming one. -/

section Inflation

omit [DecidableEq FineCell]

variable {Scale : Type w} {Point : Type u}
variable [AddCommGroup Scale] [LinearOrder Scale] [IsOrderedAddMonoid Scale]

/-- [definition] The distance structure the inflation needs: symmetry and the triangle inequality.
Nothing else — no completeness, no positivity, no field. Exact rationals satisfy it.

Rust counterpart: `grain_tower.rs::ScaledAperture::squared_distance`, whose comparisons are exact
`i128` on one declared denominator. -/
structure PseudoDistance (d : Point → Point → Scale) : Prop where
  /-- The distance does not depend on the order of its arguments. -/
  symm : ∀ x y, d x y = d y x
  /-- The triangle inequality. -/
  triangle : ∀ x y z, d x z ≤ d x y + d y z

/-- [definition] `r i` bounds the distance from the representative of coarse cell `i` to every fine
member of `i`. This is the inflation's **witness**: the number the Rust owner measures.

Rust counterpart: `CoarseReading::lower_grain_radius` and `upper_grain_radius`, computed by
`rational_root_upper_bound` from the measured squared radius. -/
def GrainRadius (d : Point → Point → Scale) (π : FineCell → CoarseCell)
    (sel : CoarseCell → FineCell) (pos : FineCell → Point) (r : CoarseCell → Scale) : Prop :=
  ∀ a : FineCell, d (pos (sel (π a))) (pos a) ≤ r (π a)

/-- [proved-derived; formal-checked] **The inflation theorem.** A fine contact within the fine
aperture forces the two representatives no further apart than the fine aperture plus the two grain
radii. The inflation is therefore determined by the presentation and is never a guess.

Rust counterpart: `grain_tower.rs::certified_coarse_aperture_squared`, which
`InflationWitness::measure` checks against the attained maximum and refuses with
`GrainRefusal::CertificateBelowMeasurement` when a supplied radius is not an upper bound. -/
theorem coarse_distance_le_fine_aperture_add_radii {d : Point → Point → Scale}
    (hd : PseudoDistance d) {π : FineCell → CoarseCell} {sel : CoarseCell → FineCell}
    {pos : FineCell → Point} {r : CoarseCell → Scale}
    (hr : GrainRadius d π sel pos r) (α : Scale) {a b : FineCell}
    (h : d (pos a) (pos b) ≤ α) :
    d (pos (sel (π a))) (pos (sel (π b))) ≤ r (π a) + (α + r (π b)) := by
  have outer : d (pos (sel (π a))) (pos (sel (π b)))
      ≤ d (pos (sel (π a))) (pos a) + d (pos a) (pos (sel (π b))) := hd.triangle _ _ _
  have inner : d (pos a) (pos (sel (π b)))
      ≤ d (pos a) (pos b) + d (pos b) (pos (sel (π b))) := hd.triangle _ _ _
  have returning : d (pos b) (pos (sel (π b))) ≤ r (π b) := by
    have carried := hr b
    rwa [hd.symm (pos (sel (π b))) (pos b)] at carried
  exact le_trans outer
    (add_le_add (hr a) (le_trans inner (add_le_add h returning)))

/-- [proved-derived; formal-checked] **An inflated coarse aperture carries every fine contact.**
The hypothesis is exactly what the Rust owner measures and checks; nothing is assumed about the
geometry beyond the triangle inequality. -/
theorem inflated_carries_every_fine_contact {d : Point → Point → Scale}
    (hd : PseudoDistance d) {π : FineCell → CoarseCell} {sel : CoarseCell → FineCell}
    {pos : FineCell → Point} {r : CoarseCell → Scale}
    (hr : GrainRadius d π sel pos r) (α β : Scale)
    (hβ : ∀ i j : CoarseCell, r i + (α + r j) ≤ β) {a b : FineCell}
    (h : d (pos a) (pos b) ≤ α) : d (pos (sel (π a))) (pos (sel (π b))) ≤ β :=
  le_trans (coarse_distance_le_fine_aperture_add_radii hd hr α h) (hβ _ _)

end Inflation

/-! ## The three lawful relations -/

/-- [definition] What relation a coarse receiver stands in to the fine one. These are the only three
lawful values; there is no fourth, no default and no inference from the data. A coarse reading with
no declared relation is not a reading.

Rust counterpart: `crates/holonic-engine/src/grain_tower.rs::ApertureRelation`, which has no
`Default` and which `GrainTower::found` demands. -/
inductive ApertureRelation (Scale : Type w) where
  /-- The coarse receiver runs at an inflated aperture that carries every fine contact, with the
  inflation exhibited. What it preserves is `inflated_carries_every_fine_contact`. -/
  | inflatedCoarse (fineAperture coarseAperture : Scale)
  /-- The two grains are separate receivers; neither restricts the other. What it asserts is
  `independent_is_mutual_insufficiency`. -/
  | declaredIndependent
  /-- The fine grain is the receiver; a coarse reading that disagrees is refused. What it enforces
  is `nativeFine_refusal_is_a_residual_difference`. -/
  | nativeFineWithRefusal (fineAperture : Scale)
  deriving Repr

/-- [definition] Two receivers are *independent* when neither factors through the other: each has a
`Foundation/Receiver.lean::ReceiverInsufficiency` witness against the other.

Rust counterpart: `grain_tower.rs::IndependenceDeclaration`, whose `declare` refuses unless a
separation was measured in at least one direction. -/
def MutuallyInsufficient {Source Left Right : Type*} (f : Source → Left) (g : Source → Right) :
    Prop :=
  Nonempty (ReceiverInsufficiency f g) ∧ Nonempty (ReceiverInsufficiency g f)

/-- [proved-derived; formal-checked] Declared independence has a witness: two coordinate receivers
on one source, neither of which determines the other. -/
theorem independent_is_mutual_insufficiency :
    MutuallyInsufficient (Prod.fst : Bool × Bool → Bool) (Prod.snd : Bool × Bool → Bool) := by
  constructor
  · exact ⟨{ left := (true, true)
             right := (true, false)
             sameEntering := rfl
             differentReturned := by decide }⟩
  · exact ⟨{ left := (true, true)
             right := (false, true)
             sameEntering := rfl
             differentReturned := by decide }⟩

/-- [proved-derived; formal-checked] Under a native-fine declaration a disagreement is not a
reading: it is exactly a residual difference, by
`Foundation/ContinuingTower.lean::Transition.residual_separates_insufficiency`.

Rust counterpart: `grain_tower.rs::FineNativeDeclaration::admit_coarse`, which returns
`GrainRefusal::CoarseReadingDisagrees` at the first such pair. -/
theorem nativeFine_refusal_is_a_residual_difference {Source Target Finer : Type*}
    (f : Transition Source Target) {finer : Source → Finer}
    (witness : ReceiverInsufficiency f.apply finer) :
    f.residual witness.left ≠ f.residual witness.right :=
  f.residual_separates_insufficiency witness

/-! ## The grain residual and the open class are two objects

Both are content a coarse receiver fails to carry. They are not instances of one object, and the
difference is stated here rather than asserted. -/

/-- [definition] A family of returns indexed by a declaration that is **not** in the source. This is
what `crates/holonic-engine/src/physical_constraint_grading.rs` returns for the open class:
`Resolution → GradedConstraintComplex`, never one complex. -/
structure DeclaredFamily (Source Target Param : Type*) where
  /-- The return under one declaration. -/
  member : Param → Source → Target

/-- [definition] The family genuinely branches at this source. -/
def DeclaredFamily.PluralAt {Source Target Param : Type*}
    (F : DeclaredFamily Source Target Param) (x : Source) : Prop :=
  ∃ p q, F.member p x ≠ F.member q x

/-- [proved-derived; formal-checked] **No function of the source realizes a plural family.** A
`Transition` supplies `apply` and `residual` as functions of the source; a declared family that
branches admits neither. -/
theorem no_function_realizes_a_plural_family {Source Target Param : Type*}
    (F : DeclaredFamily Source Target Param) {x : Source} (h : F.PluralAt x)
    (g : Source → Target) : ∃ p, F.member p x ≠ g x := by
  obtain ⟨p, q, hpq⟩ := h
  by_cases hp : F.member p x = g x
  · exact ⟨q, fun hq => hpq (hp.trans hq.symm)⟩
  · exact ⟨p, hp⟩

/-- [definition] The open class as a declared family, built from
`Foundation/AperturedGradedComplex.lean::admits`. -/
def openAdmissionFamily {Contact : Type*} (klass : Contact → ContactClass) :
    DeclaredFamily Contact Bool (Resolution Contact) :=
  ⟨fun r p => admits klass r p⟩

/-- [proved-derived; formal-checked] It branches exactly at an open contact — which is
`openContact_is_plural`, read through this family. -/
theorem openAdmissionFamily_pluralAt {Contact : Type*} {klass : Contact → ContactClass}
    {p : Contact} (h : klass p = ContactClass.openContact) :
    (openAdmissionFamily klass).PluralAt p := by
  obtain ⟨r, s, hrs⟩ := openContact_is_plural (klass := klass) h
  exact ⟨r, s, hrs⟩

/-- [proved-derived; formal-checked] **The open class is not a residual.** A residual is a function
of the source; the admission of an open contact is not. Whatever decision a caller proposes as a
function of the presentation, some resolution disagrees with it. -/
theorem open_admission_is_not_a_residual {Contact : Type*} {klass : Contact → ContactClass}
    {p : Contact} (h : klass p = ContactClass.openContact) (g : Contact → Bool) :
    ∃ r : Resolution Contact, admits klass r p ≠ g p :=
  no_function_realizes_a_plural_family (openAdmissionFamily klass)
    (openAdmissionFamily_pluralAt h) g

/-- [proved-derived; formal-checked] **The exact structural difference, in one statement.** The
grain residual is a function of the source and reopens it exactly; the open contact's admission is
not a function of the source at all. -/
theorem grain_residual_and_open_class_are_two_objects (π : FineCell → CoarseCell)
    (sel : CoarseCell → FineCell) {Contact : Type*} {klass : Contact → ContactClass} {p : Contact}
    (hopen : klass p = ContactClass.openContact) :
    (∀ φ, (selectionTransition π sel).reopen ((selectionTransition π sel).apply φ)
        ((selectionTransition π sel).residual φ) = φ) ∧
      (∀ g : Contact → Bool, ∃ r : Resolution Contact, admits klass r p ≠ g p) :=
  ⟨grain_residual_reopens_the_source π sel, fun g => open_admission_is_not_a_residual hopen g⟩

/-- [proved-derived; formal-checked] **A residual cannot close an open reading.** Reopening returns
the source, open readings included. Retaining more of the grain axis never decides a pair the
aperture left undecided. -/
theorem residual_does_not_close_an_open_reading (π : FineCell → CoarseCell)
    (sel : CoarseCell → FineCell) (φ : FineCell → FineCell → ContactClass) {a b : FineCell}
    (hopen : φ a b = ContactClass.openContact) :
    (selectionTransition π sel).reopen ((selectionTransition π sel).apply φ)
        ((selectionTransition π sel).residual φ) a b = ContactClass.openContact := by
  rw [grain_residual_reopens_the_source π sel φ]
  exact hopen

/-- [proved-derived; formal-checked] **What closes an open reading is a narrower interval**, which
is a different source on the *precision* axis of the carrier's index — not a residual on the grain
axis. `classify_eq_inside_iff` is the whole content: the tower's `restrict` has no component along
the precision axis, which is exactly why the open class does not transport between grains. -/
theorem narrower_interval_decides {Scale : Type w} [LinearOrder Scale] (aperture : Scale)
    (wide narrow : ExactInterval Scale)
    (_wasOpen : classify aperture wide = ContactClass.openContact)
    (hnarrow : narrow.upper ≤ aperture) : classify aperture narrow = ContactClass.inside :=
  (classify_eq_inside_iff aperture narrow).mpr hnarrow

/-- [proved-derived; formal-checked] And the same reading is unmoved by any resolution once the
aperture has decided it — `decided_admission_is_resolution_free`, cited rather than reproved. The
open class is therefore the *only* place a declaration may speak, and the grain residual is never
one of those places. -/
theorem decided_reading_is_resolution_free {Contact : Type*} {klass : Contact → ContactClass}
    {p : Contact} (decided : klass p ≠ ContactClass.openContact) (r s : Resolution Contact) :
    admits klass r p = admits klass s p :=
  decided_admission_is_resolution_free decided r s

end Holonics.Foundation.GrainRestriction

section Audit
open Holonics.Foundation.GrainRestriction

#print axioms grain_chain
#print axioms atom_does_not_refine_downwards
#print axioms classJoin_idem
#print axioms classJoin_comm
#print axioms classJoin_assoc
#print axioms classJoin_outside
#print axioms outside_classJoin
#print axioms classJoin_eq_inside_iff
#print axioms classJoin_eq_outside_iff
#print axioms foldr_classJoin_eq_inside_iff
#print axioms fineAdmissible_of_fineInside
#print axioms selection_inside_implies_fine_inside
#print axioms equal_aperture_is_not_lawful
#print axioms selection_is_insufficient_for_the_fine_reading
#print axioms selectionTower
#print axioms selectionTower_restrict
#print axioms selectionTransition
#print axioms selectionTransition_apply
#print axioms grain_residual_reopens_the_source
#print axioms fineReading_factors
#print axioms residual_separates_fineOnly
#print axioms coarse_distance_le_fine_aperture_add_radii
#print axioms inflated_carries_every_fine_contact
#print axioms independent_is_mutual_insufficiency
#print axioms nativeFine_refusal_is_a_residual_difference
#print axioms no_function_realizes_a_plural_family
#print axioms openAdmissionFamily_pluralAt
#print axioms open_admission_is_not_a_residual
#print axioms grain_residual_and_open_class_are_two_objects
#print axioms residual_does_not_close_an_open_reading
#print axioms narrower_interval_decides
#print axioms decided_reading_is_resolution_free
end Audit
