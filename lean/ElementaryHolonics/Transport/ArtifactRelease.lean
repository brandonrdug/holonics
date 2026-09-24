import ElementaryHolonics.Foundation.ReceiverRelease
import ElementaryHolonics.Foundation.RelationLadder
import ElementaryHolonics.Transport.ContinuingTube

/-!
# Release over an edited artifact family

[definition] This file is the formal owner of item **T3** of
`docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`. Its former executable
counterpart was retired in R1 after its laws were transferred here. It founds no second width, no
second release law and no second circuit machinery: `Foundation/ReceiverRelease.lean` owns the
width and the lawful returns, `Transport/ContinuingTube.lean` owns the two axes, the square and
the circuit, and `Foundation/RelationLadder.lean` owns the rungs. What is new here is the
**edited artifact family** as a tube, and what release means over it.

## The object

[definition] An `Artifact n` is a total assignment of tokens to `n` declared positions; a `Region`
is a `Finset` of positions and `π_B` is the region tower's own `restrict`. A family `F_k` is a
`Finset` of artifacts. With `g` a swing or edit and `C` an admitted receiver constraint,

```text
F_{k+1} = T_{g_k}(F_k) ∩ C_k
```

is `step` (single-valued transport) or `stepMulti` (a swing with sub-swings, carrying each artifact
to the finite family of admitted results): **longitudinal transport followed by transverse
restriction**. The visible draft is one member of `F_k`, never the state.

[proved-derived; formal-checked] **The cross-section shrinks and widens.** `restriction_never_widens`
is `width_mono` at the constraint, cited: pure restriction is monotone. `width_is_not_monotone_along_edits`
is the other half, by instance: the name swing carries one artifact to two admitted artifacts, the
name region's width is `0` before and nonzero after, and `the_swing_enlarges_the_family` records the
cardinalities `1` and `2`. Width is monotone along restriction only.

## Release, and what a later edit can and cannot do to it

[definition] `Releasable F B` is `∀ a a' ∈ F, π_B(a) = π_B(a')`, and
`releasable_iff_every_coordinate_width_is_zero` proves it **is**
`ReceiverRelease.width … = 0` at every coordinate of the region — the width owner is cited, not
rebuilt, and the tolerance form is that owner's `Releasable`.

[proved-derived; formal-checked] `release_preserved_by_edit_supported_off` and
`release_preserved_by_swing_supported_off`: an edit whose support misses `B` commutes with `π_B`,
so a released region stays released. The sharper statement is
`an_edit_supported_off_a_released_region_cannot_change_its_face`: over a *family*, such an edit
cannot change the released face at all. Therefore
**`reopening_from_outside_is_an_emptying`**: after an edit supported off a released region, either
the family is empty or the released face still stands. A released region is never silently
rewritten from elsewhere; it is refuted, and
`only_an_edit_touching_the_region_can_change_its_face` names the contrapositive.

[counterexample; formal-checked] That refutation is the entangled move. Over the six-slot role
frame below, `familyZero` has its pronoun released at `it`; `the_name_edit_empties_the_family`
shows that the name pivot `⟶ Hermes`, which is supported off the pronoun, leaves
`T_g(F) ∩ C = ∅` under the declared gender agreement. `the_correction_restores_the_family` shows
the resolution requires an edit supported **on** the released region — the correction. So release
of a region is lawful only against a declared future edit-and-constraint family.

## Independence and entanglement are three different relations

[established-bounded; formal-checked] The plan's single sentence conflates three:

1. **Commuting on the family.** `the_noun_and_frame_edits_commute`,
   `the_noun_and_name_edits_commute`: order of application is immaterial.
2. **Chartwise locality** — the two-axis square of `ContinuingTube`. `positionwise` edits are
   chartwise migrations of `regionTower`; `the_entangled_edit_is_not_chartwise` proves that an
   edit rewriting one position from another admits **no** chartwise migration agreeing with it at
   the full chart, because the restricted chart cannot see its trigger.
3. **Constraint entanglement.** `commuting_does_not_separate_the_independent_from_the_entangled`:
   `dog ⟶ cat` and `is ⟶ why` are both positionwise substitutions at distinct slots, so both
   commute; only intersecting with the receiver's admitted role constraint separates them — the
   noun edit keeps the family, the frame edit empties it.

Commutation is therefore not the discriminator Brandon's `dog ⟶ cat` / `is ⟶ why` pair needs; the
admitted constraint is.

## The revision cycle is a declared circuit

[proved-derived; formal-checked] `the_rotation_tube_carries_no_holonomy` cites
`ContinuingTube.tube_circuit_has_no_defect` at the rotation tube: a functorial tube has no
holonomy, so draft–observe–revise is a **declared** circuit — a `ChartwiseMigration` of the region
tower into itself — and its holonomy is `ChartwiseMigration.HasDefect`, whose obstruction is the
atlas's own `CocycleDefect`. `the_commutator_circuit_has_a_defect` exhibits one: the commutator of
the position-0 rotation and the shear is exactly the translation `y ↦ y − 1`
(`the_commutator_of_the_entangled_pair_is_a_translation`), which is positionwise and therefore a
lawful declared circuit with nontrivial holonomy.

[established-bounded; formal-checked] **A bounded search refutes and never affirms.**
`no_defect_on_a_declared_face_is_not_cancellation` exhibits a circuit returning one declared face
and moving another: "no defect on the declared faces" is its own return and is not the identity
holonomy. Cancellation is affirmed only by an exhibited identity at the declared receivers.

## Periplus and the revision loop

[definition] `periplus outward returning = returning ∘ outward` is `P = R F`, and
`periplusResidual P x` is `(P − I)x` as the finite set of positions that did not return, with
`residual_empty_iff_the_draft_returns` the identification.
`the_visible_face_returns_while_the_residual_is_nonzero` is the exact instance of Brandon's third
case: the visible region returns while an interior binding has changed. `CircuitOutcome` types the
three outcomes and the bounded return.

## The typed disposition

[definition] `Disposition` composes `ReceiverRelease.ReleaseReturn` and adds exactly the two arms
that owner does not carry — `reframe` (an incompatible declared chart) and `refuse` (an empty
preimage fibre or an obstructed transport). `dispositionOf` is a **function of the family and the
declared receivers**: `the_disposition_is_a_function_of_the_family_and_receivers`,
`an_empty_family_is_a_refusal`, `the_entangled_step_returns_a_refusal`, and
`no_candidate_carries_the_disposition` — one artifact lies in two families whose dispositions
differ, so no member of the candidate set carries it and no `NONE` candidate competes under a
normalization.

## Two media, typed differently

[definition] `EditableDraft` may be revised; `IrrevocableUtterance` carries a committed prefix and
an appended correction and has **no** operation that changes the committed part. There is no
coercion between them. `a_correction_never_changes_the_committed_boundary`,
`no_sequence_of_corrections_retracts` and
`the_committed_boundary_is_a_prefix_of_every_later_emission` are the formal content of *speech
cannot retract, only correct*.

## Tori

[proved-derived; formal-checked] `windingCircuit a b` rotates position `0` by the exact rational
angle `a/3` of a turn and position `1` by `b/4`, inside the twelfth-turn alphabet `ZMod 12`. The two
circuits commute (`the_two_edit_circuits_commute`) and compose to the joint one
(`the_composite_of_the_two_circuits_is_the_joint_one`); three turns of the first and four of the
second return every face while one and two turns of the first do not. So the edit phases form the
finite two-torus `ZMod 3 × ZMod 4` exactly, and a cycle returning the visible face with winding
`(3, 0) ≠ (0, 0)` is the torus reading.

[interpretation] That the artifact is *embedded on interlinked tori* is Brandon's picture and is
graded as interpretation here. What is proved is finite and exact: two commuting edit circuits of
orders three and four, a nontrivial winding whose visible face returns, and one entangled pair
whose commutator is a nontrivial holonomy — so the entangled pair does **not** span a torus.

## Rungs

[definition] `draftRung` states the rung every relation between two drafts stands on: identity when
the artifacts coincide, receiver equality (rung 4) when they agree on the declared region, and
continuation (rung 2) otherwise. Progress is a continuation and is **not** receiver equality
(`progress_is_a_continuation_and_not_receiver_equality`), and a neutral rechart does not ascend to
identity.

## This is an illustration of the law, not a language model

[definition] The six-slot object below is a **role frame**: six declared positions, a handful of
exact token codes and two decidable role-agreement constraints. It illustrates the law and is not
a model of English, of grammar or of meaning. No statistic, corpus or learned parameter appears
anywhere in this file.
-/

namespace Soma.Holonics.Transport.ArtifactRelease

open Soma.Holonics
open Soma.Holonics.Foundation.ContinuingTower
open Soma.Holonics.Transport.ContinuingTube

abbrev Artifact (n : ℕ) := Fin n → ℕ
abbrev Region (n : ℕ) := Finset (Fin n)

def AgreeOn {n : ℕ} (B : Region n) (a b : Artifact n) : Prop := ∀ i ∈ B, a i = b i

def Releasable {n : ℕ} (F : Finset (Artifact n)) (B : Region n) : Prop :=
  ∀ a ∈ F, ∀ b ∈ F, AgreeOn B a b

instance {n : ℕ} (B : Region n) (a b : Artifact n) : Decidable (AgreeOn B a b) := by
  unfold AgreeOn; infer_instance

instance {n : ℕ} (F : Finset (Artifact n)) (B : Region n) : Decidable (Releasable F B) := by
  unfold Releasable; infer_instance

def step {n : ℕ} (g : Artifact n → Artifact n) (C : Artifact n → Prop) [DecidablePred C]
    (F : Finset (Artifact n)) : Finset (Artifact n) :=
  (F.image g).filter C

def SupportedOff {n : ℕ} (g : Artifact n → Artifact n) (B : Region n) : Prop :=
  ∀ (a : Artifact n), ∀ i ∈ B, g a i = a i

theorem mem_step {n : ℕ} {g : Artifact n → Artifact n} {C : Artifact n → Prop} [DecidablePred C]
    {F : Finset (Artifact n)} {y : Artifact n} :
    y ∈ step g C F ↔ (∃ x ∈ F, g x = y) ∧ C y := by
  simp [step, Finset.mem_filter, Finset.mem_image]

theorem release_preserved_by_edit_supported_off {n : ℕ} {g : Artifact n → Artifact n}
    {B : Region n} {C : Artifact n → Prop} [DecidablePred C] {F : Finset (Artifact n)}
    (hg : SupportedOff g B) (hF : Releasable F B) : Releasable (step g C F) B := by
  intro a ha b hb i hi
  obtain ⟨⟨x, hx, rfl⟩, -⟩ := mem_step.mp ha
  obtain ⟨⟨y, hy, rfl⟩, -⟩ := mem_step.mp hb
  rw [hg x i hi, hg y i hi]
  exact hF x hx y hy i hi

theorem an_edit_supported_off_a_released_region_cannot_change_its_face {n : ℕ}
    {g : Artifact n → Artifact n} {B : Region n} {C : Artifact n → Prop} [DecidablePred C]
    {F : Finset (Artifact n)} (hg : SupportedOff g B) (hF : Releasable F B)
    {a : Artifact n} (ha : a ∈ F) {y : Artifact n} (hy : y ∈ step g C F) : AgreeOn B y a := by
  obtain ⟨⟨x, hx, rfl⟩, -⟩ := mem_step.mp hy
  intro i hi
  rw [hg x i hi]
  exact hF x hx a ha i hi

/-! ## The cross-section shrinks and widens -/

/-- A **swing with sub-swings**: one edit carrying each artifact to the finite family of admitted
results. A single-valued edit is the singleton case; a swing that opens alternatives is why the
tube's cross-section can widen. -/
def stepMulti {n : ℕ} (g : Artifact n → Finset (Artifact n)) (C : Artifact n → Prop)
    [DecidablePred C] (F : Finset (Artifact n)) : Finset (Artifact n) :=
  (F.biUnion g).filter C

def SupportedOffMulti {n : ℕ} (g : Artifact n → Finset (Artifact n)) (B : Region n) : Prop :=
  ∀ (a : Artifact n), ∀ y ∈ g a, ∀ i ∈ B, y i = a i

theorem stepMulti_singleton {n : ℕ} (g : Artifact n → Artifact n) (C : Artifact n → Prop)
    [DecidablePred C] (F : Finset (Artifact n)) :
    stepMulti (fun a => {g a}) C F = step g C F := by
  ext y
  simp only [stepMulti, step, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hC⟩
    exact ⟨⟨a, ha, rfl⟩, hC⟩
  · rintro ⟨⟨a, ha, rfl⟩, hC⟩
    exact ⟨⟨a, ha, rfl⟩, hC⟩

theorem release_preserved_by_swing_supported_off {n : ℕ} {g : Artifact n → Finset (Artifact n)}
    {B : Region n} {C : Artifact n → Prop} [DecidablePred C] {F : Finset (Artifact n)}
    (hg : SupportedOffMulti g B) (hF : Releasable F B) : Releasable (stepMulti g C F) B := by
  intro y hy z hz i hi
  simp only [stepMulti, Finset.mem_filter, Finset.mem_biUnion] at hy hz
  obtain ⟨⟨x, hx, hyx⟩, -⟩ := hy
  obtain ⟨⟨w, hw, hzw⟩, -⟩ := hz
  rw [hg x y hyx i hi, hg w z hzw i hi]
  exact hF x hx w hw i hi

/-- [proved-derived; formal-checked] **Pure restriction never widens the section.** Intersecting a
family with an admitted constraint is a subset, so every receiver width is monotone along it —
`width_mono`, cited. -/
theorem restriction_never_widens {n : ℕ} (F : Finset (Artifact n)) (C : Artifact n → Prop)
    [DecidablePred C] (hsub : (F.filter C).Nonempty) (hF : F.Nonempty) (R : Artifact n → ℚ) :
    Foundation.ReceiverRelease.width (F.filter C) hsub R
      ≤ Foundation.ReceiverRelease.width F hF R :=
  Foundation.ReceiverRelease.width_mono (Finset.filter_subset _ _) hsub hF R

/-! ## The width citation -/

def coordinateReading {n : ℕ} (i : Fin n) : Artifact n → ℚ := fun a => (a i : ℚ)

theorem releasable_iff_every_coordinate_width_is_zero {n : ℕ} (F : Finset (Artifact n))
    (hF : F.Nonempty) (B : Region n) :
    Releasable F B ↔
      ∀ i ∈ B, Foundation.ReceiverRelease.width F hF (coordinateReading i) = 0 := by
  constructor
  · intro h i hi
    refine (Foundation.ReceiverRelease.width_eq_zero_iff F hF _).mpr ?_
    intro x hx y hy
    simp only [coordinateReading]
    exact_mod_cast congrArg (Nat.cast (R := ℚ)) (h x hx y hy i hi)
  · intro h a ha b hb i hi
    have := (Foundation.ReceiverRelease.width_eq_zero_iff F hF (coordinateReading i)).mp (h i hi)
      a ha b hb
    simpa [coordinateReading] using this

/-! ## The six-slot role frame -/

def role (token : ℕ) : ℕ := if token = 61 then 1 else 0

def genderAgrees (a : Artifact 6) : Prop := a 4 = 51 → a 0 = 11

instance : DecidablePred genderAgrees := fun a => by unfold genderAgrees; infer_instance

def frameRoleHolds (a : Artifact 6) : Prop := role (a 5) = 0

instance : DecidablePred frameRoleHolds := fun a => by unfold frameRoleHolds; infer_instance

def Admitted (a : Artifact 6) : Prop := genderAgrees a ∧ frameRoleHolds a

instance : DecidablePred Admitted := fun a => by unfold Admitted; infer_instance

def draft (noun : ℕ) : Artifact 6 := ![10, 20, 30, noun, 50, 60]

def familyZero : Finset (Artifact 6) := {draft 40, draft 41}

def pronounRegion : Region 6 := {0}

def nounEdit (a : Artifact 6) : Artifact 6 := Function.update a 3 41
def nameEdit (a : Artifact 6) : Artifact 6 := Function.update a 4 51
def pronounEdit (a : Artifact 6) : Artifact 6 := Function.update a 0 11
def frameEdit (a : Artifact 6) : Artifact 6 := Function.update a 5 61

theorem the_pronoun_is_released_in_the_initial_family : Releasable familyZero pronounRegion := by
  decide

theorem the_noun_edit_is_supported_off_the_pronoun : SupportedOff nounEdit pronounRegion := by
  intro a i hi
  have : i = 0 := by simpa [pronounRegion] using hi
  subst this
  simp [nounEdit, Function.update]

theorem the_name_edit_is_supported_off_the_pronoun : SupportedOff nameEdit pronounRegion := by
  intro a i hi
  have : i = 0 := by simpa [pronounRegion] using hi
  subst this
  simp [nameEdit, Function.update]

theorem the_frame_edit_is_supported_off_the_pronoun : SupportedOff frameEdit pronounRegion := by
  intro a i hi
  have : i = 0 := by simpa [pronounRegion] using hi
  subst this
  simp [frameEdit, Function.update]

theorem the_noun_edit_keeps_the_family_and_the_release :
    (step nounEdit Admitted familyZero).Nonempty ∧
      Releasable (step nounEdit Admitted familyZero) pronounRegion := by
  refine ⟨?_, ?_⟩ <;> decide

theorem the_name_edit_empties_the_family : step nameEdit Admitted familyZero = ∅ := by
  decide

theorem the_frame_edit_empties_the_family : step frameEdit Admitted familyZero = ∅ := by
  decide

theorem the_correction_restores_the_family :
    (step nameEdit Admitted (step pronounEdit Admitted familyZero)).Nonempty := by
  decide

theorem the_noun_and_frame_edits_commute (a : Artifact 6) :
    nounEdit (frameEdit a) = frameEdit (nounEdit a) := by
  funext i
  fin_cases i <;> simp [nounEdit, frameEdit, Function.update]

theorem the_noun_and_name_edits_commute (a : Artifact 6) :
    nounEdit (nameEdit a) = nameEdit (nounEdit a) := by
  funext i
  fin_cases i <;> simp [nounEdit, nameEdit, Function.update]

theorem commuting_does_not_separate_the_independent_from_the_entangled :
    (∀ a : Artifact 6, nounEdit (frameEdit a) = frameEdit (nounEdit a)) ∧
      (step nounEdit Admitted familyZero).Nonempty ∧
      step frameEdit Admitted familyZero = ∅ :=
  ⟨the_noun_and_frame_edits_commute, the_noun_edit_keeps_the_family_and_the_release.1,
    the_frame_edit_empties_the_family⟩

theorem reopening_from_outside_is_an_emptying {n : ℕ} {g : Artifact n → Artifact n}
    {B : Region n} {C : Artifact n → Prop} [DecidablePred C] {F : Finset (Artifact n)}
    (hg : SupportedOff g B) (hF : Releasable F B) {a : Artifact n} (ha : a ∈ F) :
    step g C F = ∅ ∨ ∀ y ∈ step g C F, AgreeOn B y a := by
  by_cases h : step g C F = ∅
  · exact Or.inl h
  · exact Or.inr fun y hy =>
      an_edit_supported_off_a_released_region_cannot_change_its_face hg hF ha hy

theorem only_an_edit_touching_the_region_can_change_its_face {n : ℕ}
    {g : Artifact n → Artifact n} {B : Region n} {C : Artifact n → Prop} [DecidablePred C]
    {F : Finset (Artifact n)} (hF : Releasable F B) {a : Artifact n} (ha : a ∈ F)
    {y : Artifact n} (hy : y ∈ step g C F) (hdiff : ¬ AgreeOn B y a) : ¬ SupportedOff g B :=
  fun hg => hdiff (an_edit_supported_off_a_released_region_cannot_change_its_face hg hF ha hy)

def maleDraft : Artifact 6 := ![11, 20, 30, 40, 50, 60]

def nameSwing (a : Artifact 6) : Finset (Artifact 6) := {a, Function.update a 4 51}

def nameRegion : Region 6 := {4}

theorem the_swing_enlarges_the_family :
    ({maleDraft} : Finset (Artifact 6)).card = 1 ∧
      (stepMulti nameSwing Admitted {maleDraft}).card = 2 := by
  refine ⟨?_, ?_⟩ <;> decide

theorem the_name_region_is_released_before_the_swing :
    Releasable ({maleDraft} : Finset (Artifact 6)) nameRegion := by decide

theorem the_name_region_is_not_released_after_the_swing :
    ¬ Releasable (stepMulti nameSwing Admitted {maleDraft}) nameRegion := by decide

theorem stepped_family_nonempty : (stepMulti nameSwing Admitted {maleDraft}).Nonempty := by decide

theorem width_is_not_monotone_along_edits :
    Foundation.ReceiverRelease.width ({maleDraft} : Finset (Artifact 6))
        ⟨maleDraft, Finset.mem_singleton_self _⟩ (coordinateReading 4) = 0 ∧
      Foundation.ReceiverRelease.width (stepMulti nameSwing Admitted {maleDraft})
        stepped_family_nonempty (coordinateReading 4) ≠ 0 := by
  constructor
  · exact (releasable_iff_every_coordinate_width_is_zero _ _ nameRegion).mp
      the_name_region_is_released_before_the_swing 4 (by decide)
  · intro h
    refine the_name_region_is_not_released_after_the_swing
      ((releasable_iff_every_coordinate_width_is_zero _ stepped_family_nonempty nameRegion).mpr
        ?_)
    intro i hi
    have hI : i = 4 := Finset.mem_singleton.mp hi
    subst hI
    exact h

/-! ## The region tower and the two axes -/

/-- The **transverse** ladder of an artifact: the face at a region is the assignment on that
region, and `restrict` is `π_B`. -/
def regionTower (n : ℕ) (T : Type) : Tower.{0, 0} (Region n) where
  Face B := {i // i ∈ B} → T
  restrict h f := fun i => f ⟨i.1, h i.2⟩
  restrict_refl _ _ := rfl
  restrict_trans _ _ _ := rfl

/-- Any **positionwise** edit is a chartwise migration of the region tower. -/
def positionwise {n : ℕ} {T : Type} (p : Fin n → T → T) : Circuit (regionTower n T) where
  face _ f := fun i => p i.1 (f i)
  naturality _ _ := rfl

/-- The **longitudinal** axis: a tube whose station `s` has rotated every position `s` times. -/
def rotationTube (n m : ℕ) (turn : Fin n → ZMod m) : Tube.{0, 0, 0} ℕ (Region n) where
  station _ := regionTower n (ZMod m)
  transport {s t} _ :=
    { face := fun _ f => fun i => f i + (t - s) • turn i.1
      naturality := fun _ _ => rfl }
  transport_refl := by
    intro s i x
    funext k
    simp
  transport_trans := by
    intro s t r hst htr i x
    funext k
    have h1 : (t - s) + (r - t) = r - s := by omega
    show x k + (t - s) • turn k.1 + (r - t) • turn k.1 = x k + (r - s) • turn k.1
    rw [add_assoc, ← add_nsmul, h1]

/-- **A functorial tube carries no holonomy**, cited at the rotation tube: the draft-observe-revise
cycle is therefore a *declared* circuit and never a consequence of the tube's own transport. -/
theorem the_rotation_tube_carries_no_holonomy (n m : ℕ) (turn : Fin n → ZMod m) {s t : ℕ}
    (hst : s ≤ t) (hts : t ≤ s) :
    ¬ (ChartwiseMigration.comp ((rotationTube n m turn).transport hts)
        ((rotationTube n m turn).transport hst)).HasDefect :=
  tube_circuit_has_no_defect _ hst hts

/-! ## The entangled edit fails the two-axis square -/

def topIndex (i : Fin 2) : {j // j ∈ (Finset.univ : Region 2)} := ⟨i, Finset.mem_univ i⟩

/-- The entangled edit read on the transverse ladder: position 1 is rewritten using position 0. -/
def shearFace (f : (regionTower 2 (ZMod 3)).Face Finset.univ) :
    (regionTower 2 (ZMod 3)).Face Finset.univ :=
  fun i => if i.1 = 1 then f i + f (topIndex 0) else f i

theorem the_entangled_edit_is_not_chartwise :
    ¬ ∃ M : Circuit (regionTower 2 (ZMod 3)), ∀ f, M.face Finset.univ f = shearFace f := by
  rintro ⟨M, hM⟩
  have hsub : ({1} : Region 2) ≤ (Finset.univ : Region 2) := Finset.subset_univ _
  let f0 : (regionTower 2 (ZMod 3)).Face Finset.univ := fun i => if i.1 = 0 then 0 else 0
  let f1 : (regionTower 2 (ZMod 3)).Face Finset.univ := fun i => if i.1 = 0 then 1 else 0
  have hres : (regionTower 2 (ZMod 3)).restrict hsub f0
      = (regionTower 2 (ZMod 3)).restrict hsub f1 := by
    funext k
    have hk : k.1 = 1 := Finset.mem_singleton.mp k.2
    simp [regionTower, f0, f1, hk]
  have h0 := M.naturality hsub f0
  have h1 := M.naturality hsub f1
  rw [hM] at h0 h1
  rw [hres] at h0
  have hcontra := congrFun (h0.trans h1.symm) ⟨1, Finset.mem_singleton_self 1⟩
  simp [regionTower, shearFace, topIndex, f0, f1] at hcontra

/-! ## Independent and entangled edits: the commutator -/

def rotate0 (a : Fin 2 → ZMod 3) : Fin 2 → ZMod 3 := fun i => if i = 0 then a i + 1 else a i
def rotate0Inv (a : Fin 2 → ZMod 3) : Fin 2 → ZMod 3 := fun i => if i = 0 then a i - 1 else a i
def shear (a : Fin 2 → ZMod 3) : Fin 2 → ZMod 3 := fun i => if i = 1 then a 1 + a 0 else a i
def shearInv (a : Fin 2 → ZMod 3) : Fin 2 → ZMod 3 := fun i => if i = 1 then a 1 - a 0 else a i

theorem rotate0Inv_rotate0 (a : Fin 2 → ZMod 3) : rotate0Inv (rotate0 a) = a := by
  funext i; fin_cases i <;> simp [rotate0, rotate0Inv]

theorem shearInv_shear (a : Fin 2 → ZMod 3) : shearInv (shear a) = a := by
  funext i; fin_cases i <;> simp [shear, shearInv]

theorem the_commutator_of_the_entangled_pair_is_a_translation (a : Fin 2 → ZMod 3) :
    rotate0Inv (shearInv (rotate0 (shear a))) = fun i => if i = 1 then a i - 1 else a i := by
  funext i
  fin_cases i
  all_goals simp [rotate0, rotate0Inv, shear, shearInv]
  all_goals ring

def commutatorCircuit : Circuit (regionTower 2 (ZMod 3)) :=
  positionwise (fun i x => if i = 1 then x - 1 else x)

theorem commutator_moves_the_zero_face :
    commutatorCircuit.face Finset.univ (fun _ => (0 : ZMod 3)) ≠ (fun _ => (0 : ZMod 3)) := by
  intro h
  have := congrFun h (topIndex 1)
  simp [commutatorCircuit, positionwise, topIndex] at this

theorem the_commutator_circuit_has_a_defect : commutatorCircuit.HasDefect :=
  ⟨Finset.univ, fun _ => 0, commutator_moves_the_zero_face⟩

/-! ## Two independent edit circuits: a two-torus of edit phases -/

def windingCircuit (a b : ℕ) : Circuit (regionTower 2 (ZMod 12)) :=
  positionwise (fun i x => if i = 0 then x + (a : ZMod 12) * 4 else x + (b : ZMod 12) * 3)

theorem the_two_edit_circuits_commute (a b : ℕ) (B : Region 2)
    (f : (regionTower 2 (ZMod 12)).Face B) :
    (windingCircuit a 0).face B ((windingCircuit 0 b).face B f)
      = (windingCircuit 0 b).face B ((windingCircuit a 0).face B f) := by
  funext k
  by_cases hk : (k.1 : Fin 2) = 0 <;> simp [windingCircuit, positionwise, hk]

theorem the_composite_of_the_two_circuits_is_the_joint_one (a b : ℕ) (B : Region 2)
    (f : (regionTower 2 (ZMod 12)).Face B) :
    (windingCircuit a 0).face B ((windingCircuit 0 b).face B f) = (windingCircuit a b).face B f := by
  funext k
  by_cases hk : (k.1 : Fin 2) = 0 <;> simp [windingCircuit, positionwise, hk]

theorem three_turns_of_the_first_circuit_return_every_face (B : Region 2)
    (f : (regionTower 2 (ZMod 12)).Face B) : (windingCircuit 3 0).face B f = f := by
  funext k
  by_cases hk : (k.1 : Fin 2) = 0
  all_goals simp [windingCircuit, positionwise, hk]
  all_goals decide

theorem four_turns_of_the_second_circuit_return_every_face (B : Region 2)
    (f : (regionTower 2 (ZMod 12)).Face B) : (windingCircuit 0 4).face B f = f := by
  funext k
  by_cases hk : (k.1 : Fin 2) = 0
  all_goals simp [windingCircuit, positionwise, hk]
  all_goals decide

theorem one_turn_of_the_first_circuit_has_a_defect : (windingCircuit 1 0).HasDefect := by
  refine ⟨Finset.univ, fun _ => 0, ?_⟩
  intro h
  have := congrFun h (topIndex 0)
  simp [windingCircuit, positionwise, topIndex] at this
  exact absurd this (by decide)

theorem two_turns_of_the_first_circuit_has_a_defect : (windingCircuit 2 0).HasDefect := by
  refine ⟨Finset.univ, fun _ => 0, ?_⟩
  intro h
  have := congrFun h (topIndex 0)
  simp [windingCircuit, positionwise, topIndex] at this
  exact absurd this (by decide)

/-! ## The region ladder is the transverse index of the two-axis horizon -/

/-- [definition] **A region's distance through the transverse index**: how many positions `π_B`
drops relative to the whole-artifact chart. This is the `k` coordinate of
`Foundation/ReceiverRelease.lean::Horizon`, T5's second axis, read on an artifact — so release over
an edited family is a reading at a *pair* `(h, k)` and not at a number. -/
def indexDistance {n : ℕ} (B : Region n) : ℕ := n - B.card

/-- [proved-derived; formal-checked] The whole-artifact chart sits at index zero, which is the
horizon `ReceiverRelease.Horizon.longitudinalOnly` reads at. -/
theorem the_whole_chart_is_at_index_zero (n : ℕ) :
    indexDistance (Finset.univ : Region n) = 0 := by
  simp [indexDistance]

/-- [proved-derived; formal-checked] A coarser region sits no nearer the whole chart: the index
distance is antitone in the region, which is the direction `twoAxisWidth_mono_index` needs. -/
theorem indexDistance_antitone {n : ℕ} {B C : Region n} (h : B ⊆ C) :
    indexDistance C ≤ indexDistance B := by
  have : B.card ≤ C.card := Finset.card_le_card h
  simp only [indexDistance]
  omega

/-! ## Periplus: the outward edit, the returning observation, and the residual -/

def periplus {n : ℕ} (outward returning : Artifact n → Artifact n) : Artifact n → Artifact n :=
  returning ∘ outward

def periplusResidual {n : ℕ} (P : Artifact n → Artifact n) (x : Artifact n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => P x i ≠ x i)

theorem residual_empty_iff_the_draft_returns {n : ℕ} (P : Artifact n → Artifact n)
    (x : Artifact n) : periplusResidual P x = ∅ ↔ P x = x := by
  constructor
  · intro h
    funext i
    by_contra hne
    have : i ∈ periplusResidual P x := by simp [periplusResidual, hne]
    simp [h] at this
  · intro h
    ext i
    simp [periplusResidual, h]

def visibleRegion : Region 6 := {0, 1, 2, 4, 5}
def interiorRegion : Region 6 := {3}

def returningObservation (a : Artifact 6) : Artifact 6 :=
  Function.update (Function.update a 4 50) 3 41

def revisionPeriplus : Artifact 6 → Artifact 6 := periplus nameEdit returningObservation

theorem the_visible_face_returns_while_the_residual_is_nonzero :
    AgreeOn visibleRegion (revisionPeriplus (draft 40)) (draft 40) ∧
      periplusResidual revisionPeriplus (draft 40) = {3} := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## The three outcomes of a declared revision circuit -/

inductive CircuitOutcome (n : ℕ) where
  | progress (receiver : Fin n) (before after : ℕ)
  | neutralRechart (rung : Foundation.RelationLadder.Rung)
  | revisionLoop (routeClass : List ℕ) (residual : Finset (Fin n))
  | noDefectWithinBound (bound : ℕ)

theorem no_defect_on_a_declared_face_is_not_cancellation :
    ∃ (c : Circuit (regionTower 2 (ZMod 3))) (B : Region 2)
      (probe other : (regionTower 2 (ZMod 3)).Face B),
      c.face B probe = probe ∧ c.face B other ≠ other := by
  refine ⟨positionwise (fun _ x => if x = 0 then 0 else x + 1), Finset.univ,
    (fun _ => 0), (fun _ => 1), ?_, ?_⟩
  · funext k; simp [positionwise]
  · intro h
    have := congrFun h (topIndex 0)
    simp [positionwise, topIndex] at this

/-! ## The typed disposition -/

inductive ChartChange where
  | requiredChart (name : String)
  deriving DecidableEq, Repr

inductive Obstruction where
  | emptyPreimageFibre
  | obstructedTransport (name : String)
  deriving DecidableEq, Repr

inductive Disposition (Probe Coarser : Type) (tolerance : ℚ) where
  | release (r : Foundation.ReceiverRelease.ReleaseReturn Probe Coarser tolerance)
  | reframe (change : ChartChange)
  | refuse (obstruction : Obstruction)

def dispositionOf {n : ℕ} (F : Finset (Artifact n)) (B : Region n) (chartAgrees : Bool)
    (Probe Coarser : Type) (tolerance : ℚ) : Disposition Probe Coarser tolerance :=
  if F = ∅ then .refuse .emptyPreimageFibre
  else if chartAgrees = false then .reframe (.requiredChart "declared receiver chart")
  else if Releasable F B then .release .released
  else .release .hold

theorem the_disposition_is_a_function_of_the_family_and_receivers {n : ℕ}
    (F G : Finset (Artifact n)) (B : Region n) (c : Bool) (P C : Type) (t : ℚ) (h : F = G) :
    dispositionOf F B c P C t = dispositionOf G B c P C t := by rw [h]

theorem an_empty_family_is_a_refusal :
    dispositionOf (∅ : Finset (Artifact 6)) pronounRegion true Unit Unit 0
      = .refuse .emptyPreimageFibre := by simp [dispositionOf]

theorem the_entangled_step_returns_a_refusal :
    dispositionOf (step nameEdit Admitted familyZero) pronounRegion true Unit Unit 0
      = .refuse .emptyPreimageFibre := by
  rw [the_name_edit_empties_the_family]; simp [dispositionOf]

def widerFamily : Finset (Artifact 6) := insert (Function.update (draft 40) 0 11) familyZero

theorem no_candidate_carries_the_disposition :
    draft 40 ∈ familyZero ∧ draft 40 ∈ widerFamily ∧
      dispositionOf familyZero pronounRegion true Unit Unit 0
        ≠ dispositionOf widerFamily pronounRegion true Unit Unit 0 := by
  have hz : familyZero ≠ ∅ := by decide
  have hw : widerFamily ≠ ∅ := by decide
  have hrz : Releasable familyZero pronounRegion := by decide
  have hrw : ¬ Releasable widerFamily pronounRegion := by decide
  refine ⟨by decide, by decide, ?_⟩
  simp only [dispositionOf, hz, hw, hrz, hrw, if_false]
  intro h
  injection h with h'
  cases h'

/-! ## Two media, typed differently, with no coercion -/

structure EditableDraft (n : ℕ) where
  artifact : Artifact n

def EditableDraft.revise {n : ℕ} (d : EditableDraft n) (g : Artifact n → Artifact n) :
    EditableDraft n := ⟨g d.artifact⟩

structure IrrevocableUtterance where
  committed : List ℕ
  appended : List ℕ

def IrrevocableUtterance.emitted (u : IrrevocableUtterance) : List ℕ := u.committed ++ u.appended

def IrrevocableUtterance.correct (u : IrrevocableUtterance) (c : List ℕ) : IrrevocableUtterance :=
  ⟨u.committed, u.appended ++ c⟩

theorem a_correction_never_changes_the_committed_boundary (u : IrrevocableUtterance)
    (c : List ℕ) : (u.correct c).committed = u.committed := rfl

theorem a_correction_only_appends (u : IrrevocableUtterance) (c : List ℕ) :
    (u.correct c).emitted = u.emitted ++ c := by
  simp [IrrevocableUtterance.emitted, IrrevocableUtterance.correct, List.append_assoc]

theorem no_sequence_of_corrections_retracts (u : IrrevocableUtterance) (cs : List (List ℕ)) :
    (cs.foldl IrrevocableUtterance.correct u).committed = u.committed := by
  induction cs generalizing u with
  | nil => rfl
  | cons c rest ih => exact ih (u.correct c)

theorem the_committed_boundary_is_a_prefix_of_every_later_emission (u : IrrevocableUtterance)
    (c : List ℕ) : u.emitted <+: (u.correct c).emitted :=
  ⟨c, (a_correction_only_appends u c).symm⟩

/-! ## Every relation between two drafts states its rung -/

def draftRung {n : ℕ} (B : Region n) (before after : Artifact n) :
    Foundation.RelationLadder.Rung :=
  if before = after then .identity
  else if AgreeOn B before after then .receiverEqual
  else .continuation

theorem the_noun_edit_is_a_continuation_at_the_noun_receiver :
    draftRung {3} (draft 40) (nounEdit (draft 40)) = .continuation := by decide

theorem the_noun_edit_is_receiver_equal_at_the_pronoun :
    draftRung pronounRegion (draft 40) (nounEdit (draft 40)) = .receiverEqual := by decide

theorem a_neutral_rechart_does_not_ascend_to_identity :
    Foundation.RelationLadder.Rung.receiverEqual ≠ Foundation.RelationLadder.Rung.identity := by
  decide

theorem progress_is_a_continuation_and_not_receiver_equality :
    Foundation.RelationLadder.Rung.continuation.entails
      Foundation.RelationLadder.Rung.receiverEqual = false := by decide

/-! ## Audit

[definition] Every headline declaration's axiom dependencies, printed by the kernel. Only
`propext`, `Classical.choice` and `Quot.sound` are acceptable; `sorryAx` appears nowhere. -/

namespace Audit

#print axioms release_preserved_by_edit_supported_off
#print axioms release_preserved_by_swing_supported_off
#print axioms an_edit_supported_off_a_released_region_cannot_change_its_face
#print axioms reopening_from_outside_is_an_emptying
#print axioms only_an_edit_touching_the_region_can_change_its_face
#print axioms restriction_never_widens
#print axioms stepMulti_singleton
#print axioms releasable_iff_every_coordinate_width_is_zero
#print axioms the_pronoun_is_released_in_the_initial_family
#print axioms the_noun_edit_keeps_the_family_and_the_release
#print axioms the_name_edit_empties_the_family
#print axioms the_frame_edit_empties_the_family
#print axioms the_correction_restores_the_family
#print axioms commuting_does_not_separate_the_independent_from_the_entangled
#print axioms the_swing_enlarges_the_family
#print axioms width_is_not_monotone_along_edits
#print axioms regionTower
#print axioms positionwise
#print axioms rotationTube
#print axioms the_rotation_tube_carries_no_holonomy
#print axioms the_entangled_edit_is_not_chartwise
#print axioms the_commutator_of_the_entangled_pair_is_a_translation
#print axioms the_commutator_circuit_has_a_defect
#print axioms the_two_edit_circuits_commute
#print axioms the_composite_of_the_two_circuits_is_the_joint_one
#print axioms three_turns_of_the_first_circuit_return_every_face
#print axioms four_turns_of_the_second_circuit_return_every_face
#print axioms one_turn_of_the_first_circuit_has_a_defect
#print axioms two_turns_of_the_first_circuit_has_a_defect
#print axioms the_whole_chart_is_at_index_zero
#print axioms indexDistance_antitone
#print axioms residual_empty_iff_the_draft_returns
#print axioms the_visible_face_returns_while_the_residual_is_nonzero
#print axioms no_defect_on_a_declared_face_is_not_cancellation
#print axioms the_disposition_is_a_function_of_the_family_and_receivers
#print axioms an_empty_family_is_a_refusal
#print axioms the_entangled_step_returns_a_refusal
#print axioms no_candidate_carries_the_disposition
#print axioms a_correction_never_changes_the_committed_boundary
#print axioms a_correction_only_appends
#print axioms no_sequence_of_corrections_retracts
#print axioms the_committed_boundary_is_a_prefix_of_every_later_emission
#print axioms the_noun_edit_is_a_continuation_at_the_noun_receiver
#print axioms the_noun_edit_is_receiver_equal_at_the_pronoun
#print axioms a_neutral_rechart_does_not_ascend_to_identity
#print axioms progress_is_a_continuation_and_not_receiver_equality

end Audit

/-! ## Independent coordinate families: the exact enclosure specialization -/

/-- An independent product family, indexed by every declared coordinate. -/
def ProductFamily {n : ℕ} (A : Fin n → Finset ℕ) : Finset (∀ i : Fin n, i ∈ Finset.univ → ℕ) :=
  Finset.univ.pi A

def ProductRestriction {n : ℕ} (A C : Fin n → Finset ℕ) : Fin n → Finset ℕ :=
  fun i => A i ∩ C i

theorem product_family_cardinality {n : ℕ} (A : Fin n → Finset ℕ) :
    (ProductFamily A).card = ∏ i : Fin n, (A i).card := by
  simp [ProductFamily, Finset.card_pi]

theorem product_family_nonempty_iff {n : ℕ} (A : Fin n → Finset ℕ) :
    (ProductFamily A).Nonempty ↔ ∀ i : Fin n, (A i).Nonempty := by
  simp [ProductFamily, Finset.pi_nonempty]

theorem product_restriction_is_coordinate_intersection {n : ℕ}
    (A C : Fin n → Finset ℕ) :
    ProductFamily (ProductRestriction A C) =
      (ProductFamily A).filter (fun x => ∀ i : Fin n, x i (Finset.mem_univ i) ∈ C i) := by
  classical
  ext x
  simp only [ProductFamily, ProductRestriction, Finset.mem_pi, Finset.mem_filter, Finset.mem_inter]
  constructor
  · intro h
    constructor
    · intro i hi
      exact (h i hi).1
    · intro i
      exact (h i (Finset.mem_univ i)).2
  · rintro ⟨ha, hc⟩ i hi
    exact ⟨ha i hi, hc i⟩

/-- Agreement on a product region is T3 `Releasable` specialized to product members. -/
def ProductReleasable {n : ℕ} (A : Fin n → Finset ℕ) (B : Region n) : Prop :=
  ∀ x ∈ ProductFamily A, ∀ y ∈ ProductFamily A, ∀ i ∈ B,
    x i (Finset.mem_univ i) = y i (Finset.mem_univ i)

def productArtifact {n : ℕ} (x : ∀ i : Fin n, i ∈ Finset.univ → ℕ) : Artifact n :=
  fun i => x i (Finset.mem_univ i)

def productArtifacts {n : ℕ} (A : Fin n → Finset ℕ) : Finset (Artifact n) :=
  (ProductFamily A).image productArtifact

theorem productArtifact_injective {n : ℕ} : Function.Injective (@productArtifact n) := by
  intro x y h
  funext i
  funext hi
  have hxi : x i hi = x i (Finset.mem_univ i) := by congr 1
  have hyi : y i hi = y i (Finset.mem_univ i) := by congr 1
  have hval : x i (Finset.mem_univ i) = y i (Finset.mem_univ i) := by
    simpa [productArtifact] using congrFun h i
  rw [hxi, hyi, hval]

theorem product_artifacts_cardinality {n : ℕ} (A : Fin n → Finset ℕ) :
    (productArtifacts A).card = ∏ i : Fin n, (A i).card := by
  rw [productArtifacts, Finset.card_image_of_injective (ProductFamily A) productArtifact_injective,
    product_family_cardinality]

theorem product_releasable_iff_T3_releasable {n : ℕ} (A : Fin n → Finset ℕ)
    (B : Region n) : ProductReleasable A B ↔ Releasable (productArtifacts A) B := by
  constructor
  · intro h a ha b hb i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    exact h x hx y hy i hi
  · intro h x hx y hy i hi
    exact h (productArtifact x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      (productArtifact y) (Finset.mem_image.mpr ⟨y, hy, rfl⟩) i hi

theorem product_releasable_of_singleton_coordinates {n : ℕ} (A : Fin n → Finset ℕ)
    (B : Region n) (hs : ∀ i ∈ B, (A i).card = 1) : ProductReleasable A B := by
  intro x hx y hy i hi
  have hxmem := (Finset.mem_pi.mp hx) i (Finset.mem_univ i)
  have hymem := (Finset.mem_pi.mp hy) i (Finset.mem_univ i)
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hs i hi)
  rw [ha] at hxmem hymem
  simp only [Finset.mem_singleton] at hxmem hymem
  exact hxmem.trans hymem.symm

/-- A nonempty product releases exactly its singleton coordinate factors. -/
theorem product_releasable_iff_singleton_coordinates {n : ℕ} (A : Fin n → Finset ℕ)
    (B : Region n) (hn : (ProductFamily A).Nonempty) :
    ProductReleasable A B ↔ ∀ i ∈ B, (A i).card = 1 := by
  constructor
  · intro h i hi
    have hAi : (A i).Nonempty := (Finset.pi_nonempty.mp hn) i (Finset.mem_univ i)
    have xmem := (Finset.mem_pi.mp (Classical.choose_spec hn)) i (Finset.mem_univ i)
    let x₀ := Classical.choose hn
    let a := x₀ i (Finset.mem_univ i)
    have ha : a ∈ A i := by simpa [a, x₀] using xmem
    by_contra hnot
    have hpos : 0 < (A i).card := Finset.card_pos.mpr hAi
    have hcard : 1 < (A i).card := by omega
    obtain ⟨b, hb, hba⟩ : ∃ b ∈ A i, b ≠ a := by
      by_contra! h
      have : A i = {a} := Finset.eq_singleton_iff_unique_mem.mpr ⟨ha, h⟩
      simp [this] at hcard
    let x := Classical.choose hn
    have hx : x ∈ ProductFamily A := Classical.choose_spec hn
    let y : (j : Fin n) → j ∈ Finset.univ → ℕ := Function.update x i (fun _ => b)
    have hy : y ∈ ProductFamily A := by
      apply Finset.mem_pi.mpr
      intro j hj
      by_cases e : j = i
      · subst j
        simpa [y] using hb
      · have hfun : Function.update x i (fun _ => b) j = x j :=
          Function.update_of_ne e (fun _ => b) x
        have hyval : y j hj = x j hj := congrFun hfun hj
        rw [hyval]
        exact (Finset.mem_pi.mp hx) j hj
    have hxy := h x hx y hy i hi
    have hval : y i (Finset.mem_univ i) = b := by simp [y]
    have hbase : x i (Finset.mem_univ i) = a := rfl
    rw [hbase, hval] at hxy
    exact hba hxy.symm
  · exact product_releasable_of_singleton_coordinates A B

theorem product_restriction_empty_of_empty_factor {n : ℕ} (A C : Fin n → Finset ℕ)
    (i : Fin n) (h : A i ∩ C i = ∅) :
    ProductFamily (ProductRestriction A C) = ∅ := by
  classical
  ext x
  simp only [ProductFamily, ProductRestriction, Finset.mem_pi]
  constructor
  · intro hx
    have hi := hx i (Finset.mem_univ i)
    rw [h] at hi
    simp at hi
  · intro hx
    simp at hx

#print axioms product_family_cardinality
#print axioms product_artifacts_cardinality
#print axioms productArtifact_injective
#print axioms product_family_nonempty_iff
#print axioms product_restriction_is_coordinate_intersection
#print axioms product_restriction_empty_of_empty_factor
#print axioms product_releasable_iff_T3_releasable
#print axioms product_releasable_iff_singleton_coordinates

end Soma.Holonics.Transport.ArtifactRelease
