import ElementaryHolonics.Foundation.ExteriorIntake

/-!
# The environment index, situated occurrences, and what a contact edge's status actually is

[definition] This owner states the law behind items **B3** and **B4** of
`docs/plans/THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md`, and it is the formal half of
`crates/holonic-engine/src/physical_occurrence.rs`.

`Foundation/ExteriorIntake.lean` already established that no occurrence is founded without an
environment index. That index is a *presented* one: the arrays the released wire happens to carry.
This file builds the **typed** environment on top of it and states the two laws the typed version
makes available.

Four things are stated, in this order.

1. **A coordinate is declared with a ground or explicitly undeclared, and never defaulted.**
   [`Coordinate`] has exactly two constructors and no `Inhabited` instance. Agreement between two
   coordinates requires a declaration on *both* sides ([`Coordinate.agreement_is_declared_on_both_sides`]),
   so an undeclared coordinate never contributes agreement — not even with itself
   ([`disagreement_self_is_exactly_the_undeclared`]).
2. **The environment index is a product of optioned coordinates with a disagreement set.**
   [`EnvironmentIndex`] is a dependent product over the finite coordinate name type, and
   [`disagreement`] is the exact set of coordinates at which two indices are not certified to
   agree. Occurrences are a **dependent family over it**: [`Occurrence`] is `Σ e, Face e`, so an
   occurrence's environment is a projection and cannot be absent.
3. **No silent transport.** A comparison at one environment needs nothing ([`compareHere`]); a
   comparison across two exists only given a [`Passage`] ([`compareAcross`] takes it as an
   argument), and a passage cannot be built without accounting for every coordinate in the
   disagreement set ([`Passage.complete`]). The value-level comparison [`compareReadings`] returns
   a typed refusal naming exactly the differing coordinates.
4. **A contact edge's status is not a boolean, and the static law reaches only three of its
   states.** [`ContactStatus`] has six constructors. [`staticStatus`] — the exact interval
   classification of `AperturedGradedComplex.classify` — lands in exactly
   `{formed, excluded, openContact}`, attains all three, and reaches none of the other three
   ([`static_law_reaches_exactly_three`]). `kineticallyInaccessible` carries an
   [`ExteriorGround`] whose statement is a proof-carrying nonempty field, so the variant cannot
   exist without an exterior declaration. `environmentDependent` is the value of
   [`acrossEnvironments`] on a family of readings. And nothing here factors through a
   symmetrization of a directional reading ([`symmetrization_merges_a_distinguishable_pair`]).

## Rust counterpart

[definition] The paired executable owner is `crates/holonic-engine/src/physical_occurrence.rs`,
which names this file and every declaration below. The correspondence, both directions:

| Lean | Rust |
|---|---|
| `Coordinate`, `Coordinate.declared`, `Coordinate.undeclared` | `physical_occurrence.rs::Coordinate` with its two checked constructors |
| `Coordinate.agrees`, `agrees_iff` | `Coordinate::agrees` |
| `Coordinate.agreement_is_declared_on_both_sides` | `Coordinate::agrees` returning `false` whenever either side is `Undeclared` |
| `Coordinate.no_third_state` | `Coordinate` has two variants and no `Default` |
| `CoordinateName`, `allCoordinates`, `mem_allCoordinates` | `CoordinateName`, `CoordinateName::ALL` |
| `CoordinateType` | `CoordinateValue`, whose `name` is the coordinate it belongs to |
| `EnvironmentIndex` | `Environment`, whose `found` refuses unless every name is present exactly once |
| `disagreement`, `mem_disagreement_iff`, `disagreement_eq_nil_iff` | `Environment::disagreement` |
| `disagreement_self_is_exactly_the_undeclared` | `Environment::disagreement` against itself |
| `Occurrence`, `Occurrence.environment` | `Occurrence`, whose `environment` accessor is total |
| `Passage`, `Passage.complete` | `EnvironmentPassage::declare`, which refuses an unaccounted coordinate |
| `compareHere` | `compare_here` |
| `compareAcross` | `compare_through`, which takes the passage by reference |
| `compareReadings`, `compareReadings_refuses_naming_the_coordinates` | `TransportRefusal::EnvironmentsDiffer` |
| `passage_accounts_for_the_refusal` | `EnvironmentPassage::accounts_for` |
| `ContactStatus` | `ContactStatus` |
| `staticStatus`, `staticStatusOfInterval` | `static_status` |
| `static_law_reaches_exactly_three` | `physical_occurrence/tests.rs::the_static_exact_law_reaches_exactly_three_states` |
| `ExteriorGround`, `kinetic_requires_exterior_ground` | `ExteriorDeclaration`, whose fields are private and whose `declare` refuses an empty statement |
| `acrossEnvironments`, `acrossEnvironments_constant`, `acrossEnvironments_dependent_of_two_classes` | `VerticalFamily::status_across` |
| `valenceCompetition`, `competing_iff_contenders_exceed_valence` | `site_occupancy`, `Competition` |
| `DirectionalReading`, `swap`, `FactorsThroughSymmetrization` | `DirectionalUncertainty`, `DirectionalUncertainty::transposed` |
| `forward_does_not_factor_through_symmetrization` | the absence of any symmetrizing accessor |
| `symmetrization_merges_a_distinguishable_pair` | `physical_occurrence/tests.rs` on the real PAE arrays |
| `occurrence_contract` | the whole `physical_occurrence` module contract |

## The measured facts this states the law for

[established-bounded; measured] The three M5 RBX1 presentations — the designed structure, the
Protenix free prediction at seed 2, and the Protenix CUL1-bound prediction at seed 0 — are three
occurrences at three *different* environment indices: they disagree in target conformation,
oligomeric state, cofactor complement, intended partners and assay format. Their contact readings
over the same 10,368 addressed pairs are therefore three claims at three sites, and the comparison
that does not name a passage is a refusal. The Protenix PAE arrays are directional: the free
prediction's `<f2` array of extent 207 and the Boltz-2 `<f4` array of extent 330 both carry ordered
pairs whose two cells differ, which is why nothing in this file or its Rust owner factors through a
symmetrization.
-/

namespace Soma.Holonics.Foundation.PhysicalOccurrence

open Soma.Holonics.Foundation.AperturedGradedComplex

universe u

/-! ## 1. The typed coordinate: declared with a ground, or explicitly undeclared -/

/-- [definition] One environment coordinate. There are exactly two states and there is no third:
a value **declared together with the ground that licenses it**, or an explicit statement that the
coordinate was not declared at all. There is deliberately no `Inhabited` instance, so nothing can
produce a coordinate by default.

Rust counterpart: `crates/holonic-engine/src/physical_occurrence.rs::Coordinate`, whose two
constructors both refuse an empty ground. -/
inductive Coordinate (α : Type u) where
  /-- A declared value, carrying the ground that licenses the declaration. -/
  | declared (value : α) (ground : String)
  /-- Explicitly not declared, carrying the statement of why. -/
  | undeclared (why : String)
  deriving Repr

namespace Coordinate

variable {α : Type u}

/-- [definition] Whether this coordinate was declared at all. -/
def isDeclared : Coordinate α → Bool
  | declared _ _ => true
  | undeclared _ => false

/-- [definition] The declared value, when there is one. -/
def value? : Coordinate α → Option α
  | declared v _ => some v
  | undeclared _ => none

/-- [definition] Two coordinates agree when both are declared and the declared values are equal.
Two undeclared coordinates do **not** agree: neither states anything, so nothing licenses the claim
that they are the same. -/
def agrees [DecidableEq α] : Coordinate α → Coordinate α → Bool
  | declared v _, declared w _ => decide (v = w)
  | _, _ => false

/-- [proved-derived; formal-checked] Agreement is exactly a shared declared value. -/
theorem agrees_iff [DecidableEq α] (a b : Coordinate α) :
    agrees a b = true ↔ ∃ v ga gb, a = declared v ga ∧ b = declared v gb := by
  cases a with
  | undeclared wa => simp [agrees]
  | declared va ga =>
      cases b with
      | undeclared wb => simp [agrees]
      | declared vb gb =>
          constructor
          · intro h
            have : va = vb := by simpa [agrees] using h
            exact ⟨va, ga, gb, rfl, by rw [this]⟩
          · rintro ⟨v, ga', gb', hva, hvb⟩
            have h1 : va = v := by injection hva
            have h2 : vb = v := by injection hvb
            simp [agrees, h1, h2]

/-- [proved-derived; formal-checked] **Agreement requires a declaration on both sides.** -/
theorem agreement_is_declared_on_both_sides [DecidableEq α] {a b : Coordinate α}
    (h : agrees a b = true) : a.isDeclared = true ∧ b.isDeclared = true := by
  cases a with
  | undeclared wa => simp [agrees] at h
  | declared va ga =>
      cases b with
      | undeclared wb => simp [agrees] at h
      | declared vb gb => exact ⟨rfl, rfl⟩

/-- [proved-derived; formal-checked] An undeclared coordinate agrees with nothing, on either side. -/
theorem undeclared_never_agrees [DecidableEq α] (why : String) (b : Coordinate α) :
    agrees (undeclared why) b = false ∧ agrees b (undeclared why) = false := by
  refine ⟨by cases b <;> rfl, by cases b <;> rfl⟩

/-- [proved-derived; formal-checked] **No third state and no default.** -/
theorem no_third_state (c : Coordinate α) :
    (∃ v g, c = declared v g) ∨ ∃ w, c = undeclared w := by
  cases c with
  | declared v g => exact Or.inl ⟨v, g, rfl⟩
  | undeclared w => exact Or.inr ⟨w, rfl⟩

end Coordinate

/-! ## 2. The environment index as a product of optioned coordinates -/

/-- [definition] The declared coordinate axes of the environment. Each one is a separate typed
coordinate; the list is closed, so an environment cannot quietly acquire an axis. -/
inductive CoordinateName where
  /-- Species and homolog of the target. -/
  | species
  /-- Which conformational form of the target was presented. -/
  | conformation
  /-- The oligomeric state, as an exact per-entity copy count. -/
  | oligomericState
  /-- pH, with the protonation assumption that reading depends on. -/
  | acidity
  /-- Membrane or soluble context. -/
  | solvation
  /-- Cofactors and ligands present, with exact copy counts. -/
  | cofactors
  /-- The assay or prediction format the reading was taken in. -/
  | assay
  /-- Intended and unintended partners. -/
  | partners
  deriving DecidableEq, Repr

/-- [definition] Every coordinate axis, once. -/
def allCoordinates : List CoordinateName :=
  [CoordinateName.species, CoordinateName.conformation, CoordinateName.oligomericState,
    CoordinateName.acidity, CoordinateName.solvation, CoordinateName.cofactors,
    CoordinateName.assay, CoordinateName.partners]

/-- [proved-derived; formal-checked] The list is complete. -/
theorem mem_allCoordinates (n : CoordinateName) : n ∈ allCoordinates := by
  cases n <;> decide

/-- [definition] Species and homolog. -/
structure SpeciesHomolog where
  /-- The species the target was taken from. -/
  species : String
  /-- The homolog or isoform within that species. -/
  homolog : String
  deriving DecidableEq, Repr

/-- [definition] pH together with the protonation assumption. The pH is an exact rational
enclosure, never a float: `pHLower` and `pHUpper` are the declared bounds. -/
structure Acidity where
  /-- The lower bound of the declared pH enclosure. -/
  pHLower : ℚ
  /-- The upper bound of the declared pH enclosure. -/
  pHUpper : ℚ
  /-- The protonation assumption the reading was taken under. -/
  protonationAssumption : String
  deriving DecidableEq, Repr

/-- [definition] The enclosure is ordered. Stated as a predicate rather than a field so the
structure carries `DecidableEq`; the Rust owner enforces it at construction through
`exact_value::ExactInterval::new`. -/
def Acidity.Ordered (a : Acidity) : Prop := a.pHLower ≤ a.pHUpper

/-- [definition] Membrane or soluble context. -/
inductive Solvation where
  /-- Soluble, in a declared buffer. -/
  | soluble (buffer : String)
  /-- Embedded in a declared lipid environment. -/
  | membraneEmbedded (lipid : String)
  /-- Associated with a declared leaflet without being embedded. -/
  | membraneAssociated (leaflet : String)
  deriving DecidableEq, Repr

/-- [definition] The format the reading was taken in. A prediction and a binding assay are
different formats, and the difference is carried rather than erased. -/
inductive AssayFormat where
  /-- A structure predictor at a declared seed. -/
  | inSilicoPrediction (predictor : String) (seed : String)
  /-- A surface measurement with a declared immobilization and analyte valency. -/
  | surfaceMeasurement (immobilization : String) (analyteValency : ℕ)
  /-- Any other format, named. -/
  | declaredFormat (description : String)
  deriving DecidableEq, Repr

/-- [definition] Intended and unintended partners, kept apart: a partner one designed against and a
partner one must not bind are different testimony. -/
structure Partners where
  /-- Partners the occurrence was intended to engage. -/
  intended : List String
  /-- Partners the occurrence must not engage, declared. -/
  unintended : List String
  deriving DecidableEq, Repr

/-- [definition] The carrier of each coordinate axis. This is what makes the environment index a
**typed** product rather than a bag of strings. -/
def CoordinateType : CoordinateName → Type
  | CoordinateName.species => SpeciesHomolog
  | CoordinateName.conformation => String
  | CoordinateName.oligomericState => List (String × ℕ)
  | CoordinateName.acidity => Acidity
  | CoordinateName.solvation => Solvation
  | CoordinateName.cofactors => List (String × ℕ)
  | CoordinateName.assay => AssayFormat
  | CoordinateName.partners => Partners

instance instDecidableEqCoordinateType :
    (n : CoordinateName) → DecidableEq (CoordinateType n)
  | CoordinateName.species => inferInstanceAs (DecidableEq SpeciesHomolog)
  | CoordinateName.conformation => inferInstanceAs (DecidableEq String)
  | CoordinateName.oligomericState => inferInstanceAs (DecidableEq (List (String × ℕ)))
  | CoordinateName.acidity => inferInstanceAs (DecidableEq Acidity)
  | CoordinateName.solvation => inferInstanceAs (DecidableEq Solvation)
  | CoordinateName.cofactors => inferInstanceAs (DecidableEq (List (String × ℕ)))
  | CoordinateName.assay => inferInstanceAs (DecidableEq AssayFormat)
  | CoordinateName.partners => inferInstanceAs (DecidableEq Partners)

/-- [definition] **The environment index**: a dependent product of optioned coordinates. Every axis
carries a value, and that value is either a declaration with a ground or an explicit statement that
the axis was not declared. There is no partial index and no default one.

Rust counterpart: `physical_occurrence.rs::Environment`, whose `found` refuses unless every name in
`CoordinateName::ALL` is present exactly once. -/
structure EnvironmentIndex where
  /-- The coordinate at each axis. -/
  coordinate : (n : CoordinateName) → Coordinate (CoordinateType n)

/-- [definition] **The disagreement set**: the coordinates at which two indices are not certified to
agree. A coordinate that either side left undeclared is in the set, because nothing licenses the
claim that the two readings were taken under the same condition there.

Rust counterpart: `physical_occurrence.rs::Environment::disagreement`. -/
def disagreement (e f : EnvironmentIndex) : List CoordinateName :=
  allCoordinates.filter fun n => ! Coordinate.agrees (e.coordinate n) (f.coordinate n)

/-- [proved-derived; formal-checked] Membership in the disagreement set is exactly non-agreement. -/
theorem mem_disagreement_iff (e f : EnvironmentIndex) (n : CoordinateName) :
    n ∈ disagreement e f ↔ Coordinate.agrees (e.coordinate n) (f.coordinate n) = false := by
  constructor
  · intro h
    have h2 := (List.mem_filter.mp h).2
    simpa using h2
  · intro h
    exact List.mem_filter.mpr ⟨mem_allCoordinates n, by simp [h]⟩

/-- [proved-derived; formal-checked] The set is empty exactly when every coordinate agrees. -/
theorem disagreement_eq_nil_iff (e f : EnvironmentIndex) :
    disagreement e f = [] ↔ ∀ n, Coordinate.agrees (e.coordinate n) (f.coordinate n) = true := by
  constructor
  · intro h n
    by_cases hn : Coordinate.agrees (e.coordinate n) (f.coordinate n) = true
    · exact hn
    · have : n ∈ disagreement e f :=
        (mem_disagreement_iff e f n).mpr (by simpa using hn)
      rw [h] at this
      simp at this
  · intro h
    rcases hd : disagreement e f with _ | ⟨n, ns⟩
    · rfl
    · have hn : n ∈ disagreement e f := by rw [hd]; exact List.mem_cons_self ..
      have := (mem_disagreement_iff e f n).mp hn
      rw [h n] at this
      exact absurd this (by simp)

/-- [proved-derived; formal-checked] **An undeclared coordinate does not agree even with itself.**
The disagreement of an index with itself is exactly its undeclared axes, so a comparison that
crosses nothing at all still names what nobody stated. -/
theorem disagreement_self_is_exactly_the_undeclared (e : EnvironmentIndex) (n : CoordinateName) :
    n ∈ disagreement e e ↔ (e.coordinate n).isDeclared = false := by
  rw [mem_disagreement_iff]
  cases h : e.coordinate n with
  | undeclared w => simp [Coordinate.agrees, Coordinate.isDeclared]
  | declared v g => simp [Coordinate.agrees, Coordinate.isDeclared]

/-! ## 3. Occurrences as a dependent family, and the no-silent-transport law -/

/-- [definition] **An occurrence is a structure face situated at one environment index**, as a
dependent pair. The environment is the first projection, so it is total by construction and an
occurrence with no environment is not a well-typed value.

Rust counterpart: `physical_occurrence.rs::Occurrence`, whose one constructor takes the environment
by value and whose `environment` accessor is total. -/
def Occurrence (Face : EnvironmentIndex → Type u) : Type u := Σ e : EnvironmentIndex, Face e

namespace Occurrence

variable {Face : EnvironmentIndex → Type u}

/-- [definition] The environment this occurrence is situated at. Total. -/
def environment (o : Occurrence Face) : EnvironmentIndex := o.1

/-- [definition] The structure face, typed at that environment and nowhere else. -/
def face (o : Occurrence Face) : Face o.environment := o.2

end Occurrence

/-- [proved-derived; formal-checked] Every occurrence has an environment index. -/
theorem occurrence_environment_total {Face : EnvironmentIndex → Type u} (o : Occurrence Face) :
    ∃ e : EnvironmentIndex, o.environment = e := ⟨o.environment, rfl⟩

/-- [definition] **A typed passage between two environment indices.** It carries a stated ground,
and it must account for every coordinate the two indices disagree in. A passage that omits one is
not a value of this type.

Rust counterpart: `physical_occurrence.rs::EnvironmentPassage::declare`, which returns
`TransportRefusal::CoordinateUnaccounted` naming the omitted coordinate. -/
structure Passage (e f : EnvironmentIndex) where
  /-- The stated ground on which the passage is admitted. -/
  ground : String
  /-- The ground is actually stated. -/
  ground_stated : ground ≠ ""
  /-- The coordinates this passage claims to carry a reading across. -/
  accounted : List CoordinateName
  /-- Every coordinate the two indices disagree in is accounted for. -/
  complete : ∀ n ∈ disagreement e f, n ∈ accounted

/-- [definition] **The comparison that needs no passage**: both faces read at the *same* index. -/
def compareHere {Face : EnvironmentIndex → Type u} (cmp : ∀ e, Face e → Face e → Prop)
    (o p : Occurrence Face) (h : o.environment = p.environment) : Prop :=
  cmp p.environment (h ▸ o.face) p.face

/-- [definition] **The comparison across two indices exists only given a passage.** The passage is
an argument, so there is no way to call this function without supplying one: no-silent-transport is
a typing fact here, not a runtime check. -/
def compareAcross {Face : EnvironmentIndex → Type u}
    (carry : ∀ {e f : EnvironmentIndex}, Passage e f → Face e → Face f)
    (cmp : ∀ e, Face e → Face e → Prop) (o p : Occurrence Face)
    (π : Passage o.environment p.environment) : Prop :=
  cmp p.environment (carry π o.face) p.face

/-- [definition] One reading situated at the index it was taken at. -/
structure SituatedReading where
  /-- Where the reading was taken. -/
  environment : EnvironmentIndex
  /-- What was read there. -/
  reading : ContactClass

/-- [definition] What a value-level comparison returns: either a verdict at one shared environment,
or a typed refusal naming the coordinates the two environments differ in. -/
inductive Comparison where
  /-- The two readings are at one environment; the verdict is whether they agree. -/
  | atOneEnvironment (agree : Bool)
  /-- The two readings are at different environments; these coordinates differ. -/
  | refused (differing : List CoordinateName)
  deriving DecidableEq, Repr

/-- [definition] Comparing two situated readings with no passage supplied.

Rust counterpart: `physical_occurrence.rs::compare_here`, whose `Err` arm is
`TransportRefusal::EnvironmentsDiffer`. -/
def compareReadings (a b : SituatedReading) : Comparison :=
  if disagreement a.environment b.environment = [] then
    Comparison.atOneEnvironment (decide (a.reading = b.reading))
  else Comparison.refused (disagreement a.environment b.environment)

/-- [proved-derived; formal-checked] **The refusal names the coordinates.** When the two
environments are not certified equal, the comparison returns the disagreement set itself — not a
boolean, not a default and not a silently transported verdict. -/
theorem compareReadings_refuses_naming_the_coordinates (a b : SituatedReading)
    (h : disagreement a.environment b.environment ≠ []) :
    compareReadings a b = Comparison.refused (disagreement a.environment b.environment) := by
  simp [compareReadings, h]

/-- [proved-derived; formal-checked] And a verdict is returned exactly when there is no
disagreement. -/
theorem compareReadings_verdict_iff (a b : SituatedReading) :
    (∃ v, compareReadings a b = Comparison.atOneEnvironment v) ↔
      disagreement a.environment b.environment = [] := by
  constructor
  · rintro ⟨v, hv⟩
    by_contra h
    rw [compareReadings_refuses_naming_the_coordinates a b h] at hv
    exact Comparison.noConfusion hv
  · intro h
    exact ⟨decide (a.reading = b.reading), by simp [compareReadings, h]⟩

/-- [proved-derived; formal-checked] **A passage answers exactly the refusal.** Every coordinate a
refusal names is one the passage accounts for; there is no passage that leaves a named coordinate
unanswered. -/
theorem passage_accounts_for_the_refusal {e f : EnvironmentIndex} (π : Passage e f)
    (c d : ContactClass) (ns : List CoordinateName)
    (h : compareReadings ⟨e, c⟩ ⟨f, d⟩ = Comparison.refused ns) :
    ∀ n ∈ ns, n ∈ π.accounted := by
  intro n hn
  by_cases hd : disagreement e f = []
  · rw [compareReadings, if_pos hd] at h
    exact absurd h (by simp)
  · rw [compareReadings_refuses_naming_the_coordinates ⟨e, c⟩ ⟨f, d⟩ hd] at h
    have : ns = disagreement e f := by
      injection h with h'
      exact h'.symm
    exact π.complete n (this ▸ hn)

/-! ## 4. The contact status, and what the static law can and cannot reach -/

/-- [definition] An exterior declaration, with the ground that licenses it. The `statement` field
carries a proof that it is nonempty, so this structure cannot be built from a structure file, from
a distance, or from nothing.

Rust counterpart: `physical_occurrence.rs::ExteriorDeclaration`, whose fields are private and whose
`declare` refuses an empty statement. -/
structure ExteriorGround where
  /-- What is declared. -/
  statement : String
  /-- What apparatus or authority declared it. -/
  apparatus : String
  /-- The statement is actually stated. -/
  stated : statement ≠ ""

/-- [definition] **A contact edge's status.** Six states with six different evidence requirements,
of which the exact static geometry reaches exactly three.

Rust counterpart: `physical_occurrence.rs::ContactStatus`. -/
inductive ContactStatus (E : Type u) where
  /-- The exact interval lies at or below the aperture. -/
  | formed
  /-- The exact interval lies strictly above the aperture. -/
  | excluded
  /-- The exact interval straddles the aperture; the reading stays plural. -/
  | openContact
  /-- Admitted only from an exterior declaration. A static structure cannot produce it. -/
  | kineticallyInaccessible (ground : ExteriorGround)
  /-- The same ordered pair reads differently at different environment indices. -/
  | environmentDependent (formedAt excludedAt openAt : List E)
  /-- The contact competes for a site whose declared valence cannot carry every contender. -/
  | competing (site : ℕ) (valence : ℕ) (contenders : ℕ)

/-- [definition] **The static exact law.** The classification of an exact squared-distance interval
against an aperture, read as a status. Nothing else is available to it. -/
def staticStatus {E : Type u} : ContactClass → ContactStatus E
  | ContactClass.inside => ContactStatus.formed
  | ContactClass.outside => ContactStatus.excluded
  | ContactClass.openContact => ContactStatus.openContact

/-- [definition] The static law read directly off the exact interval and the aperture, composing
`AperturedGradedComplex.classify`. -/
def staticStatusOfInterval {E : Type u} (aperture : ℚ) (d : ExactInterval ℚ) : ContactStatus E :=
  staticStatus (classify aperture d)

/-- [proved-derived; formal-checked] The static law lands in the three geometric states. -/
theorem staticStatus_mem_three {E : Type u} (c : ContactClass) :
    staticStatus (E := E) c = ContactStatus.formed ∨
      staticStatus (E := E) c = ContactStatus.excluded ∨
      staticStatus (E := E) c = ContactStatus.openContact := by
  cases c
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)

/-- [proved-derived; formal-checked] **A static structure never yields kinetic inaccessibility.**
This is the type-level statement of "kinetic inaccessibility is not a geometric fact". -/
theorem staticStatus_never_kinetic {E : Type u} (c : ContactClass) (g : ExteriorGround) :
    staticStatus (E := E) c ≠ ContactStatus.kineticallyInaccessible g := by
  cases c <;> simp [staticStatus]

/-- [proved-derived; formal-checked] Nor environment dependence: one reading at one index cannot
exhibit it. -/
theorem staticStatus_never_environmentDependent {E : Type u} (c : ContactClass)
    (f x o : List E) :
    staticStatus (E := E) c ≠ ContactStatus.environmentDependent f x o := by
  cases c <;> simp [staticStatus]

/-- [proved-derived; formal-checked] Nor competition: one pair's interval says nothing about a
site's valence. -/
theorem staticStatus_never_competing {E : Type u} (c : ContactClass) (s v n : ℕ) :
    staticStatus (E := E) c ≠ ContactStatus.competing s v n := by
  cases c <;> simp [staticStatus]

/-- [proved-derived; formal-checked] All three geometric states are attained by the interval law, so
the image is exactly three states and not fewer. -/
theorem staticStatusOfInterval_attains_all_three {E : Type u} :
    (∃ a d, staticStatusOfInterval (E := E) a d = ContactStatus.formed) ∧
      (∃ a d, staticStatusOfInterval (E := E) a d = ContactStatus.excluded) ∧
      ∃ a d, staticStatusOfInterval (E := E) a d = ContactStatus.openContact := by
  refine ⟨⟨1, ⟨0, 0, le_refl 0⟩, ?_⟩, ⟨0, ⟨1, 1, le_refl 1⟩, ?_⟩, ⟨1, ⟨0, 2, by norm_num⟩, ?_⟩⟩
  · show staticStatus (classify (1 : ℚ) ⟨0, 0, le_refl 0⟩) = ContactStatus.formed
    rw [(classify_eq_inside_iff (1 : ℚ) ⟨0, 0, le_refl 0⟩).mpr (by norm_num)]
    rfl
  · show staticStatus (classify (0 : ℚ) ⟨1, 1, le_refl 1⟩) = ContactStatus.excluded
    rw [(classify_eq_outside_iff (0 : ℚ) ⟨1, 1, le_refl 1⟩).mpr (by norm_num)]
    rfl
  · show staticStatus (classify (1 : ℚ) ⟨0, 2, by norm_num⟩) = ContactStatus.openContact
    rw [(classify_eq_openContact_iff (1 : ℚ) ⟨0, 2, by norm_num⟩).mpr (by norm_num)]
    rfl

/-- [proved-derived; formal-checked] **The static exact law produces exactly
`{formed, excluded, openContact}` and no others.** Both halves: the image is contained in the three
geometric states, all three are attained, and the other three constructors are unreachable. -/
theorem static_law_reaches_exactly_three {E : Type u} :
    (∀ c : ContactClass, staticStatus (E := E) c = ContactStatus.formed ∨
        staticStatus (E := E) c = ContactStatus.excluded ∨
        staticStatus (E := E) c = ContactStatus.openContact) ∧
      ((∃ a d, staticStatusOfInterval (E := E) a d = ContactStatus.formed) ∧
        (∃ a d, staticStatusOfInterval (E := E) a d = ContactStatus.excluded) ∧
        ∃ a d, staticStatusOfInterval (E := E) a d = ContactStatus.openContact) ∧
      (∀ (c : ContactClass) (g : ExteriorGround),
          staticStatus (E := E) c ≠ ContactStatus.kineticallyInaccessible g) ∧
      (∀ (c : ContactClass) (f x o : List E),
          staticStatus (E := E) c ≠ ContactStatus.environmentDependent f x o) ∧
      ∀ (c : ContactClass) (s v n : ℕ), staticStatus (E := E) c ≠ ContactStatus.competing s v n :=
  ⟨staticStatus_mem_three, staticStatusOfInterval_attains_all_three, staticStatus_never_kinetic,
    staticStatus_never_environmentDependent, staticStatus_never_competing⟩

/-- [proved-derived; formal-checked] **Kinetic inaccessibility requires an exterior ground.** The
constructor takes one, and that ground's statement is nonempty by a field of its own type. -/
theorem kinetic_requires_exterior_ground {E : Type u} (s : ContactStatus E) (g : ExteriorGround)
    (_h : s = ContactStatus.kineticallyInaccessible g) : g.statement ≠ "" := g.stated

/-! ### The across-environment status -/

/-- [definition] The single class a family reads, when every member reads the same one. `none` says
the family is empty or its members disagree. -/
def uniformClass {E : Type u} (family : List (E × ContactClass)) : Option ContactClass :=
  match family with
  | [] => none
  | (_, c) :: rest => if rest.all (fun x => x.2 == c) then some c else none

/-- [definition] The environments at which a family read one declared class. -/
def readAt {E : Type u} (family : List (E × ContactClass)) (c : ContactClass) : List E :=
  (family.filter fun x => x.2 == c).map Prod.fst

/-- [proved-derived; formal-checked] A family whose members all read `c` is uniform at `c`. -/
theorem uniformClass_some_of_constant {E : Type u} (family : List (E × ContactClass))
    (c : ContactClass) (hne : family ≠ []) (h : ∀ x ∈ family, x.2 = c) :
    uniformClass family = some c := by
  cases family with
  | nil => exact absurd rfl hne
  | cons a rest =>
      obtain ⟨e₀, c₀⟩ := a
      have hc₀ : c₀ = c := h (e₀, c₀) (List.mem_cons_self ..)
      have hall : (rest.all fun x => x.2 == c₀) = true := by
        rw [List.all_eq_true]
        intro x hx
        have hx2 := h x (List.mem_cons_of_mem _ hx)
        simp [hx2, hc₀]
      show (if (rest.all fun x => x.2 == c₀) = true then some c₀ else none) = some c
      rw [if_pos hall, hc₀]

/-- [proved-derived; formal-checked] A family carrying two different classes is not uniform. -/
theorem uniformClass_none_of_two_classes {E : Type u} (family : List (E × ContactClass))
    (e₁ e₂ : E) (c₁ c₂ : ContactClass) (h₁ : (e₁, c₁) ∈ family) (h₂ : (e₂, c₂) ∈ family)
    (hne : c₁ ≠ c₂) : uniformClass family = none := by
  cases family with
  | nil => simp at h₁
  | cons a rest =>
      obtain ⟨e₀, c₀⟩ := a
      have hall : ¬ ((rest.all fun x => x.2 == c₀) = true) := by
        intro hr
        have hevery : ∀ x ∈ (e₀, c₀) :: rest, x.2 = c₀ := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · rfl
          · have hx2 := (List.all_eq_true.mp hr) x hx
            simpa using hx2
        exact hne ((hevery (e₁, c₁) h₁).trans (hevery (e₂, c₂) h₂).symm)
      show (if (rest.all fun x => x.2 == c₀) = true then some c₀ else none) = none
      rw [if_neg hall]

/-- [definition] **The status of one ordered pair read across a family of environments.** A family
whose readings all agree is that reading; a family whose readings disagree is environment-dependent,
and the three environment lists say exactly where each class was read. An empty family is no
measurement and returns nothing.

Rust counterpart: `physical_occurrence.rs::VerticalFamily::status_across`. -/
def acrossEnvironments {E : Type u} (family : List (E × ContactClass)) :
    Option (ContactStatus E) :=
  if family.isEmpty then none
  else
    match uniformClass family with
    | some c => some (staticStatus c)
    | none =>
        some (ContactStatus.environmentDependent (readAt family ContactClass.inside)
          (readAt family ContactClass.outside) (readAt family ContactClass.openContact))

/-- [proved-derived; formal-checked] An empty family is refused; a nonempty one always returns. -/
theorem acrossEnvironments_isSome_iff {E : Type u} (family : List (E × ContactClass)) :
    (acrossEnvironments family).isSome ↔ family ≠ [] := by
  cases family with
  | nil => simp [acrossEnvironments]
  | cons a rest =>
      cases h : uniformClass (a :: rest) <;> simp [acrossEnvironments, h]

/-- [proved-derived; formal-checked] **A family that agrees everywhere is exactly the static
status.** Reading the same thing at several environments adds no new state. -/
theorem acrossEnvironments_constant {E : Type u} (family : List (E × ContactClass))
    (c : ContactClass) (hne : family ≠ []) (h : ∀ x ∈ family, x.2 = c) :
    acrossEnvironments family = some (staticStatus c) := by
  have hu := uniformClass_some_of_constant family c hne h
  cases family with
  | nil => exact absurd rfl hne
  | cons a rest => simp [acrossEnvironments, hu]

/-- [proved-derived; formal-checked] **Two readings that disagree make the status
environment-dependent.** This is the derivation `physical_occurrence.rs` runs on the three M5
presentations: the same ordered pair, read at three different environment indices, with the classes
not all equal. The three returned lists are exactly where each class was read. -/
theorem acrossEnvironments_dependent_of_two_classes {E : Type u}
    (family : List (E × ContactClass)) (e₁ e₂ : E) (c₁ c₂ : ContactClass)
    (h₁ : (e₁, c₁) ∈ family) (h₂ : (e₂, c₂) ∈ family) (hne : c₁ ≠ c₂) :
    acrossEnvironments family =
      some (ContactStatus.environmentDependent (readAt family ContactClass.inside)
        (readAt family ContactClass.outside) (readAt family ContactClass.openContact)) := by
  have hu := uniformClass_none_of_two_classes family e₁ e₂ c₁ c₂ h₁ h₂ hne
  cases family with
  | nil => simp at h₁
  | cons a rest => simp [acrossEnvironments, hu]

/-! ### Competition at a site with a declared valence -/

/-- [definition] **The exclusion this owner uses is a declared valence at one site.** A site with
declared valence `k` cannot carry more than `k` formed contacts at once, so `contenders > k` is a
competition and `contenders ≤ k` is not. The alternative — steric exclusion derived from the exact
distance law between the two partners — is a different exclusion and is deliberately not what this
function computes; nothing here silently mixes them.

Rust counterpart: `physical_occurrence.rs::site_occupancy`, which returns the formed contenders and
the open ones separately so neither is dropped. -/
def valenceCompetition {E : Type u} (site valence contenders : ℕ) : Option (ContactStatus E) :=
  if valence < contenders then some (ContactStatus.competing site valence contenders) else none

/-- [proved-derived; formal-checked] Competition holds exactly when the formed contenders exceed the
declared valence. -/
theorem competing_iff_contenders_exceed_valence {E : Type u} (site valence contenders : ℕ) :
    (valenceCompetition (E := E) site valence contenders).isSome ↔ valence < contenders := by
  by_cases h : valence < contenders <;> simp [valenceCompetition, h]

/-- [proved-derived; formal-checked] A site whose valence carries every contender exhibits no
competition — the function returns nothing rather than a weakened verdict. -/
theorem no_competition_within_valence {E : Type u} (site valence contenders : ℕ)
    (h : contenders ≤ valence) : valenceCompetition (E := E) site valence contenders = none := by
  simp [valenceCompetition, Nat.not_lt.mpr h]

/-! ## 5. Directional uncertainty is never symmetrized -/

/-- [definition] One ordered pair's directional reading. `PAE(i→j)` and `PAE(j→i)` are two numbers,
and this structure keeps them two.

Rust counterpart: `physical_occurrence.rs::DirectionalUncertainty`. -/
structure DirectionalReading where
  /-- The reading in the presented direction. -/
  forward : ℚ
  /-- The reading in the opposite direction. -/
  reverse : ℚ
  deriving DecidableEq, Repr

/-- [definition] Swapping the ordered pair. -/
def swap (d : DirectionalReading) : DirectionalReading := ⟨d.reverse, d.forward⟩

/-- [definition] A function **factors through a symmetrization** when it cannot tell an ordered pair
from its transpose. Averaging, taking the minimum, taking the maximum and any other symmetric
summary all have this property. -/
def FactorsThroughSymmetrization {α : Type u} (f : DirectionalReading → α) : Prop :=
  ∀ d, f d = f (swap d)

/-- [definition] A witness that the two directions genuinely differ. -/
def asymmetricReading : DirectionalReading := ⟨1, 2⟩

/-- [proved-derived; formal-checked] It is not its own transpose. -/
theorem asymmetricReading_ne_swap : asymmetricReading ≠ swap asymmetricReading := by
  intro h
  have : (1 : ℚ) = 2 := congrArg DirectionalReading.forward h
  norm_num at this

/-- [proved-derived; formal-checked] **Retaining the pair does not factor through a
symmetrization.** -/
theorem retention_does_not_factor_through_symmetrization :
    ¬ FactorsThroughSymmetrization (α := DirectionalReading) id := by
  intro h
  exact asymmetricReading_ne_swap (h asymmetricReading)

/-- [proved-derived; formal-checked] Neither does reading one direction of it. -/
theorem forward_does_not_factor_through_symmetrization :
    ¬ FactorsThroughSymmetrization DirectionalReading.forward := by
  intro h
  have : (1 : ℚ) = 2 := h asymmetricReading
  norm_num at this

/-- [proved-derived; formal-checked] **A symmetrization merges a distinguishable pair.** Any
function that cannot tell an ordered pair from its transpose identifies two readings the source
kept apart — which is exactly the testimony a symmetrized PAE array destroys. -/
theorem symmetrization_merges_a_distinguishable_pair {α : Type u} (f : DirectionalReading → α)
    (h : FactorsThroughSymmetrization f) (d : DirectionalReading) (hne : d.forward ≠ d.reverse) :
    d ≠ swap d ∧ f d = f (swap d) := by
  refine ⟨fun heq => hne ?_, h d⟩
  have : d.forward = (swap d).forward := congrArg DirectionalReading.forward heq
  simpa [swap] using this

/-! ## 6. B5 — plural fibres and separator sets

[definition] Several predictors, seeds and environments produce a population of faces over one
candidate. This section states the law of that population: **agreement narrows the fibre and does
not prove realization.** Unanimity of a family on a receiver gives `R`-indistinguishability of its
members and never equality of sources; adding a member can only shrink or preserve the unanimous
set; and a single separating contact refutes a proposed merge.

Rust counterpart: `crates/holonic-engine/src/physical_occurrence/plural_fibre.rs`. -/

section PluralFibre

variable {κ : Type}

/-- [definition] A face read at the contact receiver: the class at every addressed contact.

Rust counterpart: the `readings` of `physical_occurrence.rs::SituatedFamily`. -/
abbrev ContactFace (κ : Type) := κ → ContactClass

/-- [definition] **One contact separates two faces** when both decided it and decided it
differently. An open reading on either side separates nothing: the reading stays plural and is
carried rather than counted.

Rust counterpart: `plural_fibre.rs::PluralFibre::separator_between`, whose `DecidedClass::of`
returns `None` on an open reading. -/
def separatesB (c : κ) (f g : ContactFace κ) : Bool :=
  if f c = ContactClass.openContact then false
  else if g c = ContactClass.openContact then false
  else decide (f c ≠ g c)

/-- [proved-derived; formal-checked] A face never separates from itself. -/
theorem separatesB_irrefl (c : κ) (f : ContactFace κ) : separatesB c f f = false := by
  unfold separatesB
  by_cases h : f c = ContactClass.openContact <;> simp [h]

/-- [proved-derived; formal-checked] An open reading separates nothing, on either side. -/
theorem separatesB_of_open (c : κ) (f g : ContactFace κ)
    (h : f c = ContactClass.openContact ∨ g c = ContactClass.openContact) :
    separatesB c f g = false := by
  unfold separatesB
  rcases h with h | h
  · rw [if_pos h]
  · by_cases hf : f c = ContactClass.openContact
    · rw [if_pos hf]
    · rw [if_neg hf, if_pos h]

/-- [definition] **The complete separator set** of two faces over a declared receiver. Every
contact that separates them, not the first one and not a shortest witness.

Rust counterpart: `plural_fibre.rs::PairwiseSeparator::separating`. -/
def separatorSet (R : List κ) (f g : ContactFace κ) : List κ :=
  R.filter fun c => separatesB c f g

/-- [proved-derived; formal-checked] Membership in the separator set is exactly separation. -/
theorem mem_separatorSet_iff (R : List κ) (f g : ContactFace κ) (c : κ) :
    c ∈ separatorSet R f g ↔ c ∈ R ∧ separatesB c f g = true := by
  simp [separatorSet, List.mem_filter]

/-- [definition] Two faces are **`R`-indistinguishable** when no contact of `R` separates them. -/
def Indistinguishable (R : List κ) (f g : ContactFace κ) : Prop :=
  ∀ c ∈ R, separatesB c f g = false

/-- [definition] The decidable reading of the same relation. -/
def indistinguishableB (R : List κ) (f g : ContactFace κ) : Bool :=
  R.all fun c => !separatesB c f g

/-- [proved-derived; formal-checked] The two readings agree. -/
theorem indistinguishableB_iff (R : List κ) (f g : ContactFace κ) :
    indistinguishableB R f g = true ↔ Indistinguishable R f g := by
  simp [indistinguishableB, Indistinguishable, List.all_eq_true]

/-- [proved-derived; formal-checked] A face is indistinguishable from itself. -/
theorem indistinguishableB_refl (R : List κ) (f : ContactFace κ) :
    indistinguishableB R f f = true := by
  simp [indistinguishableB, separatesB_irrefl]

/-- [proved-derived; formal-checked] **Separator-set completeness.** Two faces are
`R`-distinguishable exactly when their separator set is nonempty — equivalently, the separator set
is empty exactly when they are indistinguishable.

Rust counterpart: `plural_fibre.rs::PluralFibre::indistinguishable`, which is
`separator_between(..).separating.is_empty()` and nothing else. -/
theorem separatorSet_eq_nil_iff_indistinguishable (R : List κ) (f g : ContactFace κ) :
    separatorSet R f g = [] ↔ Indistinguishable R f g := by
  constructor
  · intro h c hc
    by_contra hne
    simp only [Bool.not_eq_false] at hne
    have hmem : c ∈ separatorSet R f g := (mem_separatorSet_iff R f g c).mpr ⟨hc, hne⟩
    rw [h] at hmem
    simp at hmem
  · intro h
    rcases hd : separatorSet R f g with _ | ⟨c, cs⟩
    · rfl
    · have hc : c ∈ separatorSet R f g := by rw [hd]; exact List.mem_cons_self ..
      obtain ⟨hcR, hcs⟩ := (mem_separatorSet_iff R f g c).mp hc
      rw [h c hcR] at hcs
      exact absurd hcs (by simp)

/-! ### Unanimity and its monotonicity -/

/-- [definition] A contact is **unanimous** across a family when the first member decided it and
every other member read the same class. An open reading is never unanimous.

Rust counterpart: `plural_fibre.rs::FibrePartition::unanimous`. -/
def unanimousAt (family : List (ContactFace κ)) (c : κ) : Bool :=
  match family with
  | [] => false
  | f :: rest =>
      !decide (f c = ContactClass.openContact) && rest.all fun g => decide (g c = f c)

/-- [definition] The unanimous set over a declared receiver. -/
def unanimous (R : List κ) (family : List (ContactFace κ)) : List κ :=
  R.filter (unanimousAt family)

/-- [proved-derived; formal-checked] **Monotonicity: adding a member can only shrink or preserve
the unanimous set.** The hypothesis that the family is already nonempty is not decoration — adding
the *first* member enlarges the unanimous set from nothing, which is why
`plural_fibre.rs::PluralFibre::over_one_candidate` refuses a population of fewer than two and
`adjoin` only ever enlarges an existing fibre. -/
theorem unanimousAt_antitone (family : List (ContactFace κ)) (g : ContactFace κ) (c : κ)
    (hne : family ≠ []) (h : unanimousAt (family ++ [g]) c = true) :
    unanimousAt family c = true := by
  cases family with
  | nil => exact absurd rfl hne
  | cons f rest =>
      simp only [List.cons_append, unanimousAt, List.all_append, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, h.2.1⟩

/-- [proved-derived; formal-checked] The same statement at the unanimous set itself. -/
theorem unanimous_antitone (R : List κ) (family : List (ContactFace κ)) (g : ContactFace κ)
    (hne : family ≠ []) (c : κ) (h : c ∈ unanimous R (family ++ [g])) :
    c ∈ unanimous R family := by
  rw [unanimous, List.mem_filter] at h ⊢
  exact ⟨h.1, unanimousAt_antitone family g c hne h.2⟩

/-! ### Sources, the preimage fibre, and what agreement does not buy -/

/-- [definition] A **source**: a face together with the environment index it was read at. Two
sources carrying the same face at two environments are two sources, and no receiver reading only
the face can tell them apart.

Rust counterpart: `physical_occurrence.rs::SituatedFamily`, whose `environment` is retained beside
its `readings`. -/
structure Source (κ : Type) where
  /-- The face the receiver reads. -/
  face : ContactFace κ
  /-- The environment index it was read at. -/
  environment : EnvironmentIndex

/-- [definition] **The preimage fibre** of a source at a receiver: every member of the declared
population the receiver cannot tell from it.

Rust counterpart: `plural_fibre.rs::PluralFibre`, whose members are the retained sources and are
never collapsed to a representative. -/
def preimageFibre (R : List κ) (population : List (Source κ)) (s : Source κ) : List (Source κ) :=
  population.filter fun t => indistinguishableB R s.face t.face

/-- [proved-derived; formal-checked] **Agreement leaves the preimage fibre plural.** Two distinct
sources no contact of the receiver separates are both in the fibre over either of them, and they
are still two. -/
theorem fibre_stays_plural (R : List κ) (population : List (Source κ)) (s t : Source κ)
    (hs : s ∈ population) (ht : t ∈ population) (hne : s ≠ t)
    (hind : Indistinguishable R s.face t.face) :
    s ∈ preimageFibre R population s ∧ t ∈ preimageFibre R population s ∧ s ≠ t := by
  refine ⟨List.mem_filter.mpr ⟨hs, indistinguishableB_refl R s.face⟩, ?_, hne⟩
  exact List.mem_filter.mpr ⟨ht, (indistinguishableB_iff R s.face t.face).mpr hind⟩

/-- [definition] An environment index that declares nothing. -/
def silentIndex : EnvironmentIndex :=
  ⟨fun _ => Coordinate.undeclared "this index declares nothing"⟩

/-- [definition] An environment index that declares its species with a ground. -/
def statedIndex : EnvironmentIndex where
  coordinate
    | CoordinateName.species =>
        Coordinate.declared ⟨"Homo sapiens", "RBX1"⟩ "the release names its target"
    | CoordinateName.conformation => Coordinate.undeclared "not declared here"
    | CoordinateName.oligomericState => Coordinate.undeclared "not declared here"
    | CoordinateName.acidity => Coordinate.undeclared "not declared here"
    | CoordinateName.solvation => Coordinate.undeclared "not declared here"
    | CoordinateName.cofactors => Coordinate.undeclared "not declared here"
    | CoordinateName.assay => Coordinate.undeclared "not declared here"
    | CoordinateName.partners => Coordinate.undeclared "not declared here"

/-- [proved-derived; formal-checked] They are two environments. -/
theorem silentIndex_ne_statedIndex : silentIndex ≠ statedIndex := by
  intro h
  have hc : silentIndex.coordinate CoordinateName.species
      = statedIndex.coordinate CoordinateName.species := by rw [h]
  simp [silentIndex, statedIndex] at hc

/-- [proved-derived; formal-checked] **Agreement does not prove realization.** There are two
sources the receiver cannot tell apart and that are nevertheless not equal, so no amount of
unanimity at a receiver is a proof that two occurrences are one realized source.

Rust counterpart: `plural_fibre.rs::RealizationProof`, an **uninhabited** enum, so
`UnanimityReceipt::realization_proof` is `None` by type rather than by policy. -/
theorem agreement_does_not_prove_realization (R : List κ) :
    ∃ s t : Source κ, Indistinguishable R s.face t.face ∧ s ≠ t := by
  refine ⟨⟨fun _ => ContactClass.inside, silentIndex⟩,
    ⟨fun _ => ContactClass.inside, statedIndex⟩, ?_, ?_⟩
  · intro c _
    simp [separatesB]
  · intro h
    exact silentIndex_ne_statedIndex (congrArg Source.environment h)

/-- [proved-derived; formal-checked] **One separating contact refutes a proposed merge.** A source
the receiver separates from `s` at even one contact is not in the fibre over `s`.

Rust counterpart: `plural_fibre.rs::PluralFibre::refutes_merge`. -/
theorem one_separating_contact_refutes_the_merge (R : List κ) (population : List (Source κ))
    (s t : Source κ) (c : κ) (hc : c ∈ R) (h : separatesB c s.face t.face = true) :
    t ∉ preimageFibre R population s := by
  intro hmem
  have hall := (indistinguishableB_iff R s.face t.face).mp (List.mem_filter.mp hmem).2 c hc
  rw [h] at hall
  exact absurd hall (by simp)

/-! ### The minimal separating sets -/

/-- [definition] A receiver **hits** a separator set when it contains one of its contacts. -/
def Hits (receiver : List κ) (S : List κ) : Prop := ∃ c ∈ receiver, c ∈ S

/-- [definition] A receiver **separates every pair** of a declared list of face pairs. -/
def SeparatesAll (receiver : List κ) (pairs : List (ContactFace κ × ContactFace κ)) : Prop :=
  ∀ p ∈ pairs, ∃ c ∈ receiver, separatesB c p.1 p.2 = true

/-- [proved-derived; formal-checked] **Any hitting set separates all pairs.** This is the
correctness of the reduction `plural_fibre.rs::PluralFibre::minimal_separating_sets` performs: a
receiver that distinguishes every member of the fibre is exactly a hitting set of the pairwise
separator sets.

Rust counterpart: `plural_fibre.rs::PluralFibre::separates_every_pair`. -/
theorem hittingSet_separates_all (R : List κ) (receiver : List κ)
    (pairs : List (ContactFace κ × ContactFace κ))
    (h : ∀ p ∈ pairs, Hits receiver (separatorSet R p.1 p.2)) :
    SeparatesAll receiver pairs := by
  intro p hp
  obtain ⟨c, hcR, hcS⟩ := h p hp
  exact ⟨c, hcR, ((mem_separatorSet_iff R p.1 p.2 c).mp hcS).2⟩

/-- [definition] A **minimum** hitting set of a family of separator sets: it hits every set, and no
receiver that hits every set is shorter.

Rust counterpart: the `MinimalSeparation::Minimum` arm, which returns **every** receiver of that
size rather than a representative. -/
structure MinimumHittingSet (receiver : List κ) (sets : List (List κ)) : Prop where
  /-- It hits every separator set. -/
  hits : ∀ S ∈ sets, ∃ c ∈ receiver, c ∈ S
  /-- Nothing that hits every separator set is shorter. -/
  minimal : ∀ other : List κ, (∀ S ∈ sets, ∃ c ∈ other, c ∈ S) → receiver.length ≤ other.length

/-- [proved-derived; formal-checked] A minimum hitting set of the pairwise separator sets separates
every pair. -/
theorem minimum_hittingSet_separates_all (R : List κ) (receiver : List κ)
    (pairs : List (ContactFace κ × ContactFace κ))
    (h : MinimumHittingSet receiver (pairs.map fun p => separatorSet R p.1 p.2)) :
    SeparatesAll receiver pairs := by
  refine hittingSet_separates_all R receiver pairs ?_
  intro p hp
  exact h.hits (separatorSet R p.1 p.2) (List.mem_map.mpr ⟨p, hp, rfl⟩)

/-- [proved-derived; formal-checked] Minimality, as stated: no hitting set is shorter. -/
theorem minimum_no_smaller (receiver other : List κ) (sets : List (List κ))
    (h : MinimumHittingSet receiver sets)
    (ho : ∀ S ∈ sets, ∃ c ∈ other, c ∈ S) : receiver.length ≤ other.length :=
  h.minimal other ho

/-- [proved-derived; formal-checked] **The predicate is inhabited**: a one-contact receiver is the
minimum hitting set of a single one-contact separator set, so `MinimumHittingSet` is not vacuous. -/
theorem minimumHittingSet_witness : MinimumHittingSet [true] [[true]] := by
  constructor
  · intro S hS
    simp only [List.mem_singleton] at hS
    subst hS
    exact ⟨true, by simp, by simp⟩
  · intro other ho
    obtain ⟨c, hc, hcS⟩ := ho [true] (by simp)
    simp only [List.mem_singleton] at hcS
    subst hcS
    have hpos : 0 < other.length := List.length_pos_of_mem hc
    simp only [List.length_singleton]
    exact hpos

/-- [proved-derived; formal-checked] **And it is not universal**: a receiver that hits every
separator set can still fail minimality, so the second field is a real condition and not a
restatement of the first. -/
theorem not_minimumHittingSet_of_redundant : ¬ MinimumHittingSet [true, true] [[true]] := by
  intro h
  have hle := h.minimal [true] (by
    intro S hS
    simp only [List.mem_singleton] at hS
    subst hS
    exact ⟨true, by simp, by simp⟩)
  simp at hle

/-- [proved-derived; formal-checked] **A member pair no contact separates makes the family
unseparable.** An empty separator set is hit by nothing, so there is no hitting set at all — and
the fibre stays plural however many contacts are read.

Rust counterpart: the `MinimalSeparation::Unseparable` arm, which names the two members rather than
returning an empty receiver. -/
theorem no_hittingSet_of_empty_separator_set (sets : List (List κ)) (h : [] ∈ sets) :
    ¬ ∃ receiver : List κ, ∀ S ∈ sets, ∃ c ∈ receiver, c ∈ S := by
  rintro ⟨receiver, hr⟩
  obtain ⟨c, _, hc⟩ := hr [] h
  simp at hc

/-- [proved-derived; formal-checked] **The B5 contract.** The separator set is complete and decides
distinguishability; agreement leaves the fibre plural and proves no realization; one separating
contact refutes a merge; the unanimous set is antitone; and any hitting set of the pairwise
separator sets separates every pair while an empty separator set admits none. -/
theorem fibre_contract (R : List κ) :
    (∀ f g : ContactFace κ, separatorSet R f g = [] ↔ Indistinguishable R f g) ∧
      (∃ s t : Source κ, Indistinguishable R s.face t.face ∧ s ≠ t) ∧
      (∀ (family : List (ContactFace κ)) (g : ContactFace κ), family ≠ [] →
        ∀ c ∈ unanimous R (family ++ [g]), c ∈ unanimous R family) ∧
      (∀ (receiver : List κ) (pairs : List (ContactFace κ × ContactFace κ)),
        (∀ p ∈ pairs, Hits receiver (separatorSet R p.1 p.2)) → SeparatesAll receiver pairs) ∧
      ∀ sets : List (List κ), [] ∈ sets →
        ¬ ∃ receiver : List κ, ∀ S ∈ sets, ∃ c ∈ receiver, c ∈ S :=
  ⟨separatorSet_eq_nil_iff_indistinguishable R, agreement_does_not_prove_realization R,
    fun family g hne c h => unanimous_antitone R family g hne c h,
    hittingSet_separates_all R, no_hittingSet_of_empty_separator_set⟩

end PluralFibre

/-! ## 7. B6 — passages

[definition] `(K,Theta)_{t+} = Phi_e((K,Theta)_{t-})` as a first-class typed event. Environment
change, binding, protonation and mutation are passages carrying receipts rather than
reparameterizations. Mutation changes the object itself, so it is a **horizontal** move and is
typed apart from the three vertical ones; the axis is an index of the passage type, so there is no
coercion between them.

Rust counterpart: `crates/holonic-engine/src/physical_occurrence/passage.rs`. -/

section Passages

/-- [definition] The axis a passage moves along. There are exactly two.

Rust counterpart: the marker types `passage.rs::Vertical` and `passage.rs::Horizontal`, which index
`Passage` and between which no `From`, `Into`, `Deref` or trait object exists. -/
inductive PassageAxis where
  /-- The environment moves around one object. -/
  | vertical
  /-- The object itself changes. -/
  | horizontal
  deriving DecidableEq, Repr

/-- [proved-derived; formal-checked] The two axes are two values. -/
theorem vertical_ne_horizontal : PassageAxis.vertical ≠ PassageAxis.horizontal := by decide

/-- [definition] The event `e`. Each kind carries its own evidence in the Rust owner; here only the
axis it moves along is needed.

Rust counterpart: `passage.rs::PassageEvent`. -/
inductive PassageEvent where
  /-- The environment index changes and nothing else is claimed. -/
  | environmentChange
  /-- A partner enters the oligomeric state. -/
  | binding (partner : String)
  /-- The protonation assumption changes with the pH it depends on. -/
  | protonation
  /-- The object itself changes at one site. -/
  | mutation (site : ℕ)
  deriving DecidableEq, Repr

/-- [definition] Which axis an event moves along. -/
def PassageEvent.axis : PassageEvent → PassageAxis
  | environmentChange => PassageAxis.vertical
  | binding _ => PassageAxis.vertical
  | protonation => PassageAxis.vertical
  | mutation _ => PassageAxis.horizontal

/-- [proved-derived; formal-checked] **Mutation is horizontal.** -/
theorem mutation_is_horizontal (s : ℕ) :
    (PassageEvent.mutation s).axis = PassageAxis.horizontal := rfl

/-- [proved-derived; formal-checked] And the other three are vertical. -/
theorem the_other_three_are_vertical (p : String) :
    PassageEvent.environmentChange.axis = PassageAxis.vertical ∧
      (PassageEvent.binding p).axis = PassageAxis.vertical ∧
      PassageEvent.protonation.axis = PassageAxis.vertical :=
  ⟨rfl, rfl, rfl⟩

/-! ### The exact delta in `K` -/

/-- [definition] **The exact typed delta in the constraint complex `K`**: at every addressed
contact, the class before and the class after.

Rust counterpart: `passage.rs::ConstraintDelta`, whose `PairTransition` carries exactly this pair
and whose `formed`, `broken`, `opened`, `closed` and `census` are projections of it. -/
def Delta (κ : Type) := κ → ContactClass × ContactClass

namespace Delta

variable {κ : Type}

/-- The source classes the delta records. -/
def before (d : Delta κ) : ContactFace κ := fun c => (d c).1

/-- The target classes it records. -/
def after (d : Delta κ) : ContactFace κ := fun c => (d c).2

/-- [definition] Two deltas compose when the second starts, contact by contact, where the first
ends.

Rust counterpart: `passage.rs::PassageRefusal::DeltaEndpointsDisagree`, which names the contact at
which they part. -/
def Composable (d e : Delta κ) : Prop := ∀ c, d.after c = e.before c

/-- [definition] Exact serial composition: keep the first delta's source class and the second's
target class. -/
def comp (d e : Delta κ) : Delta κ := fun c => ((d c).1, (e c).2)

/-- [proved-derived; formal-checked] **Delta composition is associative, exactly.** -/
theorem comp_assoc (d e f : Delta κ) : (d.comp e).comp f = d.comp (e.comp f) := rfl

/-- [proved-derived; formal-checked] The composite leaves where the first leaves. -/
theorem comp_before (d e : Delta κ) : (d.comp e).before = d.before := rfl

/-- [proved-derived; formal-checked] And arrives where the second arrives. -/
theorem comp_after (d e : Delta κ) : (d.comp e).after = e.after := rfl

/-- [proved-derived; formal-checked] Composability is preserved by composition. -/
theorem comp_composable {d e f : Delta κ} (h : e.Composable f) : (d.comp e).Composable f := by
  intro c
  exact h c

/-- [definition] The delta that moves nothing at one face.

Rust counterpart: `passage.rs::ConstraintDelta::identity_on`. -/
def idOn (f : ContactFace κ) : Delta κ := fun c => (f c, f c)

/-- [proved-derived; formal-checked] The left identity law, on composable deltas. -/
theorem idOn_comp (f : ContactFace κ) (d : Delta κ) (h : (idOn f).Composable d) :
    (idOn f).comp d = d := by
  funext c
  have hc : f c = (d c).1 := h c
  show (f c, (d c).2) = d c
  rw [hc]

/-- [proved-derived; formal-checked] The right identity law. -/
theorem comp_idOn (d : Delta κ) (f : ContactFace κ) (h : d.Composable (idOn f)) :
    d.comp (idOn f) = d := by
  funext c
  have hc : (d c).2 = f c := h c
  show ((d c).1, f c) = d c
  rw [← hc]

end Delta

/-! ### The passage, its two axes, and their composition -/

/-- [definition] **A passage typed at one axis.** The axis is an index of the type, so a vertical
passage is not a horizontal one and no function turns one into the other without changing the
index. Every step is an event on that axis, and the step list is nonempty.

Rust counterpart: `passage.rs::Passage`, named `TypedPassage` here because this namespace already
carries B3's `Passage` between two environment indices, whose axis is a sealed type parameter and whose step list
is private. -/
structure TypedPassage (κ : Type) (a : PassageAxis) where
  /-- The steps, in order. A serial composition concatenates them. -/
  steps : List PassageEvent
  /-- A passage has at least one step. -/
  steps_nonempty : steps ≠ []
  /-- Every step is an event on this passage's axis. -/
  steps_on_axis : ∀ e ∈ steps, e.axis = a
  /-- What changed in `K`. -/
  delta : Delta κ

/-- [proved-derived; formal-checked] **No vertical passage carries a mutation.** This is the
no-coercion statement in its sharp form: the axis index is not a label, it excludes the other
axis's events from the step list.

Rust counterpart: `Passage::mutation` exists only on `impl Passage<Horizontal>`, and `then`
concatenates only within one axis. -/
theorem no_vertical_passage_carries_a_mutation {κ : Type}
    (p : TypedPassage κ PassageAxis.vertical) (s : ℕ) : PassageEvent.mutation s ∉ p.steps := by
  intro h
  have hax := p.steps_on_axis _ h
  rw [mutation_is_horizontal] at hax
  exact vertical_ne_horizontal hax.symm

/-- [proved-derived; formal-checked] And no horizontal passage carries an environment change. -/
theorem no_horizontal_passage_carries_an_environment_change {κ : Type}
    (p : TypedPassage κ PassageAxis.horizontal) :
    PassageEvent.environmentChange ∉ p.steps := by
  intro h
  have hax := p.steps_on_axis _ h
  exact vertical_ne_horizontal hax

/-- [definition] The elementary vertical passage that moves the environment and changes nothing in
`K`. It exists so that `TypedPassage` at the vertical axis is an inhabited type and not a shape
nothing satisfies. -/
def retainingPassage (κ : Type) (f : ContactFace κ) : TypedPassage κ PassageAxis.vertical where
  steps := [PassageEvent.environmentChange]
  steps_nonempty := by simp
  steps_on_axis := by
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    rfl
  delta := Delta.idOn f

/-- [definition] The elementary horizontal passage: one mutation at a declared site. -/
def mutatingPassage (κ : Type) (f : ContactFace κ) (site : ℕ) :
    TypedPassage κ PassageAxis.horizontal where
  steps := [PassageEvent.mutation site]
  steps_nonempty := by simp
  steps_on_axis := by
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    rfl
  delta := Delta.idOn f

/-- [proved-derived; formal-checked] Both axes are inhabited, and the vertical one still carries no
mutation — so `no_vertical_passage_carries_a_mutation` is a statement about a nonempty type. -/
theorem both_axes_are_inhabited {κ : Type} (f : ContactFace κ) (site : ℕ) :
    (retainingPassage κ f).steps = [PassageEvent.environmentChange] ∧
      (mutatingPassage κ f site).steps = [PassageEvent.mutation site] ∧
      PassageEvent.mutation site ∉ (retainingPassage κ f).steps :=
  ⟨rfl, rfl, no_vertical_passage_carries_a_mutation (retainingPassage κ f) site⟩

/-- [definition] **Serial composition** within one axis: concatenate the steps and compose the
deltas.

Rust counterpart: `passage.rs::Passage::then`, which additionally requires the joining occurrence to
be equal as a whole value and retains it. -/
def TypedPassage.comp {κ : Type} {a : PassageAxis} (p q : TypedPassage κ a) : TypedPassage κ a where
  steps := p.steps ++ q.steps
  steps_nonempty := by
    cases hp : p.steps with
    | nil => exact absurd hp p.steps_nonempty
    | cons x xs => simp
  steps_on_axis := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact p.steps_on_axis e h
    · exact q.steps_on_axis e h
  delta := p.delta.comp q.delta

/-- [proved-derived; formal-checked] **Composition is associative**, on the steps and on the delta
together. The step list associates because list concatenation does, and the delta associates by
`Delta.comp_assoc`, which holds by `rfl`.

Rust counterpart: `Passage::then` concatenates one step list, so both bracketings are equal values
and the composite delta and cost receipt are left folds over that one list. -/
theorem TypedPassage.comp_assoc {κ : Type} {a : PassageAxis} (p q r : TypedPassage κ a) :
    ((p.comp q).comp r).steps = (p.comp (q.comp r)).steps ∧
      ((p.comp q).comp r).delta = (p.comp (q.comp r)).delta :=
  ⟨List.append_assoc p.steps q.steps r.steps, Delta.comp_assoc p.delta q.delta r.delta⟩

/-! ### The residual, and why the reverse needs it -/

/-- [definition] **The event's action on `K`**: at each contact, a map of classes. This is `Phi_e`
restricted to the constraint coordinate. -/
def ClassAction (κ : Type) := κ → ContactClass → ContactClass

namespace ClassAction

variable {κ : Type}

/-- What the action transports. -/
def apply (Φ : ClassAction κ) (f : ContactFace κ) : ContactFace κ := fun c => Φ c (f c)

/-- What it drops, retained: the source face itself.

Rust counterpart: `passage.rs::PassageResidual`, which carries the source occurrence, its
environment index, its object identity and its class at every addressed contact. -/
def residual (_Φ : ClassAction κ) (f : ContactFace κ) : ContactFace κ := f

/-- The reopening, from the transported face and the retained residual. -/
def reopen (_Φ : ClassAction κ) (_transported residual : ContactFace κ) : ContactFace κ := residual

/-- [proved-derived; formal-checked] **The retained residual reopens the source exactly.** This is
`Foundation/ContinuingTower.lean::Transition.reopen_apply` at this instance: an equality, not a
bound.

Rust counterpart: the `Transition` impl for `Passage`, with `Transition::check_reopen` as the
receipt. -/
theorem reopen_apply (Φ : ClassAction κ) (f : ContactFace κ) :
    Φ.reopen (Φ.apply f) (Φ.residual f) = f := rfl

/-- [definition] The reverse passage exists **from the transported face alone** exactly when the
action is injective at every contact. -/
def Reversible (Φ : ClassAction κ) : Prop := ∀ c, Function.Injective (Φ c)

/-- [proved-derived; formal-checked] **Traversability is the residual.** The passage is two-way
from the transported face alone exactly when its action is injective at every contact; and whether
or not it is, the retained residual restores the source exactly. This is the passage instance of
`Foundation/ContinuingTower.lean::ResidualMigration.traversability_is_the_residual`.

Rust counterpart: `passage.rs::Passage::reverse_passage`, which returns `continuing_tower`'s own
`ReversePassageReceipt` and names the two merged faces. -/
theorem traversability_is_the_residual [DecidableEq κ] (Φ : ClassAction κ) :
    (Function.Injective Φ.apply ↔ Φ.Reversible) ∧
      ∀ f : ContactFace κ, Φ.reopen (Φ.apply f) (Φ.residual f) = f := by
  refine ⟨⟨?_, ?_⟩, fun f => rfl⟩
  · intro hinj c x y hxy
    have happ : Φ.apply (fun d => if d = c then x else ContactClass.inside)
        = Φ.apply (fun d => if d = c then y else ContactClass.inside) := by
      funext d
      by_cases hd : d = c
      · subst hd
        simpa [ClassAction.apply] using hxy
      · simp [ClassAction.apply, hd]
    have hfun := congrFun (hinj happ) c
    simpa using hfun
  · intro hrev f g hfg
    funext c
    exact hrev c (congrFun hfg c)

/-- [definition] The action that changes nothing at any contact. -/
def retaining (κ : Type) : ClassAction κ := fun _ c => c

/-- [proved-derived; formal-checked] It is reversible, so `Reversible` is inhabited and the
non-invertibility below is a real distinction rather than a property nothing has. -/
theorem retaining_reversible {κ : Type} : (retaining κ).Reversible := fun _ => fun _ _ h => h

/-- [definition] An action that sends every class to `formed` at every contact. -/
def collapsing (κ : Type) : ClassAction κ := fun _ _ => ContactClass.inside

/-- [proved-derived; formal-checked] **A passage is not invertible in general.** The collapsing
action merges two faces, so its transported face determines nothing about its source and there is
no reverse from the face alone. -/
theorem collapsing_merges_two_faces (c : κ) :
    ∃ f g : ContactFace κ, (collapsing κ).apply f = (collapsing κ).apply g ∧ f ≠ g := by
  refine ⟨fun _ => ContactClass.inside, fun _ => ContactClass.outside, rfl, ?_⟩
  intro h
  exact ContactClass.noConfusion (congrFun h c)

/-- [proved-derived; formal-checked] And it is not reversible. -/
theorem collapsing_not_reversible (c : κ) : ¬ (collapsing κ).Reversible := by
  intro h
  exact ContactClass.noConfusion
    (@h c ContactClass.inside ContactClass.outside rfl)

end ClassAction

/-- [proved-derived; formal-checked] **The B6 contract.** Mutation is horizontal and the other three
events are vertical; the two axes are distinct and a vertical passage's step list cannot contain a
mutation; delta composition is associative exactly; passage composition is associative on the steps
and the delta together; the retained residual reopens the source exactly; and a passage is not
invertible in general. -/
theorem passage_contract :
    ((PassageEvent.mutation 0).axis ≠ PassageEvent.environmentChange.axis) ∧
      (∀ (p : TypedPassage Unit PassageAxis.vertical) (s : ℕ),
        PassageEvent.mutation s ∉ p.steps) ∧
      (∀ d e f : Delta Unit, (d.comp e).comp f = d.comp (e.comp f)) ∧
      (∀ p q r : TypedPassage Unit PassageAxis.vertical,
        ((p.comp q).comp r).steps = (p.comp (q.comp r)).steps ∧
          ((p.comp q).comp r).delta = (p.comp (q.comp r)).delta) ∧
      (∀ (Φ : ClassAction Unit) (f : ContactFace Unit),
        Φ.reopen (Φ.apply f) (Φ.residual f) = f) ∧
      ¬ (ClassAction.collapsing Unit).Reversible :=
  ⟨by decide, fun p s => no_vertical_passage_carries_a_mutation p s, fun d e f => Delta.comp_assoc d e f,
    fun p q r => TypedPassage.comp_assoc p q r, fun Φ f => ClassAction.reopen_apply Φ f,
    ClassAction.collapsing_not_reversible ()⟩

end Passages

/-! ## The contract -/

/-- [proved-derived; formal-checked] **What a typed environment index and a typed contact status
buy.** A coordinate agrees only when declared on both sides; a comparison across environments
returns the disagreement set rather than a verdict, and a passage answers exactly that set; the
static exact law reaches exactly the three geometric states and none of the other three; and no
symmetrizing function can be used without merging readings the source kept apart.

Rust owner: `crates/holonic-engine/src/physical_occurrence.rs`. -/
theorem occurrence_contract :
    (∀ {α : Type} [DecidableEq α] (a b : Coordinate α), Coordinate.agrees a b = true →
        a.isDeclared = true ∧ b.isDeclared = true) ∧
      (∀ (a b : SituatedReading), disagreement a.environment b.environment ≠ [] →
        compareReadings a b = Comparison.refused (disagreement a.environment b.environment)) ∧
      (∀ (c : ContactClass) (g : ExteriorGround),
        staticStatus (E := Unit) c ≠ ContactStatus.kineticallyInaccessible g) ∧
      (∀ (f : DirectionalReading → ℚ), FactorsThroughSymmetrization f →
        ∀ d : DirectionalReading, d.forward ≠ d.reverse → d ≠ swap d ∧ f d = f (swap d)) :=
  ⟨fun _a _b h => Coordinate.agreement_is_declared_on_both_sides h,
    compareReadings_refuses_naming_the_coordinates,
    staticStatus_never_kinetic,
    fun f h d hne => symmetrization_merges_a_distinguishable_pair f h d hne⟩

section Audit

#print axioms Coordinate.agrees_iff
#print axioms Coordinate.agreement_is_declared_on_both_sides
#print axioms Coordinate.undeclared_never_agrees
#print axioms Coordinate.no_third_state
#print axioms mem_allCoordinates
#print axioms mem_disagreement_iff
#print axioms disagreement_eq_nil_iff
#print axioms disagreement_self_is_exactly_the_undeclared
#print axioms occurrence_environment_total
#print axioms compareReadings_refuses_naming_the_coordinates
#print axioms compareReadings_verdict_iff
#print axioms passage_accounts_for_the_refusal
#print axioms staticStatus_mem_three
#print axioms staticStatus_never_kinetic
#print axioms staticStatus_never_environmentDependent
#print axioms staticStatus_never_competing
#print axioms staticStatusOfInterval_attains_all_three
#print axioms static_law_reaches_exactly_three
#print axioms kinetic_requires_exterior_ground
#print axioms acrossEnvironments_isSome_iff
#print axioms uniformClass_some_of_constant
#print axioms uniformClass_none_of_two_classes
#print axioms acrossEnvironments_constant
#print axioms acrossEnvironments_dependent_of_two_classes
#print axioms competing_iff_contenders_exceed_valence
#print axioms no_competition_within_valence
#print axioms retention_does_not_factor_through_symmetrization
#print axioms forward_does_not_factor_through_symmetrization
#print axioms symmetrization_merges_a_distinguishable_pair
#print axioms occurrence_contract
#print axioms separatesB_irrefl
#print axioms separatesB_of_open
#print axioms mem_separatorSet_iff
#print axioms indistinguishableB_iff
#print axioms indistinguishableB_refl
#print axioms separatorSet_eq_nil_iff_indistinguishable
#print axioms unanimousAt_antitone
#print axioms unanimous_antitone
#print axioms fibre_stays_plural
#print axioms silentIndex_ne_statedIndex
#print axioms agreement_does_not_prove_realization
#print axioms one_separating_contact_refutes_the_merge
#print axioms hittingSet_separates_all
#print axioms minimum_hittingSet_separates_all
#print axioms minimum_no_smaller
#print axioms no_hittingSet_of_empty_separator_set
#print axioms minimumHittingSet_witness
#print axioms not_minimumHittingSet_of_redundant
#print axioms fibre_contract
#print axioms vertical_ne_horizontal
#print axioms mutation_is_horizontal
#print axioms the_other_three_are_vertical
#print axioms Delta.comp_assoc
#print axioms Delta.comp_before
#print axioms Delta.comp_after
#print axioms Delta.comp_composable
#print axioms Delta.idOn_comp
#print axioms Delta.comp_idOn
#print axioms no_vertical_passage_carries_a_mutation
#print axioms no_horizontal_passage_carries_an_environment_change
#print axioms TypedPassage.comp_assoc
#print axioms both_axes_are_inhabited
#print axioms ClassAction.retaining_reversible
#print axioms ClassAction.reopen_apply
#print axioms ClassAction.traversability_is_the_residual
#print axioms ClassAction.collapsing_merges_two_faces
#print axioms ClassAction.collapsing_not_reversible
#print axioms passage_contract

end Audit

end Soma.Holonics.Foundation.PhysicalOccurrence
