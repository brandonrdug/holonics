import ElementaryHolonics.Foundation.RelationLadder
import ElementaryHolonics.Foundation.PresentationCost
import ElementaryHolonics.Foundation.PhysicalOccurrence

/-!
# B8 — selection and design equivalence

[definition] This file deposits item **B8** of
`docs/plans/THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md`, stated in the vocabulary of
`Foundation/RelationLadder.lean`. It founds no new relation: design equivalence **is** that owner's
`EqualPotential` at a situation whose generators are the admitted typed passages and whose
receivers are the declared receiver family read across the declared environments, and the frontier
stage **is** `Foundation/PresentationCost.lean::IsFrontierPoint`. What is new is the selection
cascade as typed stages and a constructed counterexample for every collapse between them.

## Design equivalence is equal potential, never equal score

[proved-derived] Two designs may be merged only when every declared receiver, every declared
environment and every admitted future transformation agrees. That is exactly
`RelationLadder.EqualPotential` over the design situation, and one separating future receiver
refutes it (`RelationLadder.separatorRefutesEqualPotential`, instantiated here as
`oneSeparatingFutureReceiverRefutesTheMerge`).

Executably a bounded search can only ever return a separator or "not separated within the declared
bound", so **a merge is never licensed by a bounded search**. `MergeVerdict` types that: only
`equivalentBy` licenses a merge (`only_equivalentBy_licenses_merge`), and
`notSeparatedWithinBound_does_not_license_merge` is the statement that the honest bottom never
coerces upward.

Two constructed witnesses bound the claim from below:

* `presentAgreementDoesNotImplyEnvironmentAgreement` — two designs whose every declared receiver
  agrees *now* and which the declared environment family separates.
* `declaredEnvironmentAgreementDoesNotImplyUndeclared` — two designs agreeing at every *declared*
  environment and separated at one the declaration does not carry. The general law is
  `RelationLadder.equalPotentialAntitone`: the relation is antitone in the declaration, so an
  equivalence read at a smaller declaration is never a claim at a larger one.

## The empirical pattern, exactly

[definition] The plan records two observations: two binders within two per cent on final
dissociation constant that differ qualitatively on cross-species binding, and two designs with
near-identical predicted interface receivers that differ about six-fold in affinity. Both are
modelled here on **exact rationals** as `toleranceClosenessAtOneReceiverLicensesNothing` and
`interfaceAgreementWithoutAffinityAgreement`. They are synthetic instances of the recorded pattern
and not measurements: the mounted M5 release carries three presentations of **one** object and no
dissociation constant or cross-species assay of any kind.

## The cascade, as typed stages

1. **Hard constraints**, a typed refusal per violated constraint and never a penalty term:
   `admitted`, `violations`, `violating_design_is_never_admitted`, `theBestDesignIsStillRefused`.
2. **Pareto filtering** over the receiver-reading vector: `PresentationCost.IsFrontierPoint`,
   cited.
3. **Worst-environment ranking**: `worstOver`, with `worst_is_attained`, `worst_is_an_upper_bound`,
   `undeclared_environment_is_absent` and `unread_at_a_declared_environment_refuses`. An
   undeclared environment is absent — neither a best case nor a worst case — and a design unread at
   a *declared* environment is refused for ranking there rather than imputed.
4. **Quality-diversity** keeps the frontier's spread, which is why a scalar may not go first:
   `scalarFirstDiscardsAFrontierDesign` cites `PresentationCost.unsupported_not_minimizer`.
5. **Structural clustering** from the exact separator structure of
   `Foundation/PhysicalOccurrence.lean`'s plural fibre. Openness makes indistinguishability
   intransitive (`indistinguishabilityIsNotTransitive`), so a cluster is a **connected component**
   and not an equivalence class of indistinguishability (`aComponentCanContainASeparatedPair`).

## Rust counterpart

[definition] `crates/holonic-engine/src/design_selection.rs`, with the same names — `MergeVerdict`,
`merge_verdict`, `HardConstraint`, `admitted`, `WorstVerdict`, `worst_over`, `ReceiverReading`,
`structural_clusters` — every theorem below mirrored as a test and every declared size checked
before it is used.
-/

namespace Soma.Holonics.Foundation.DesignSelection

open Soma.Holonics
open Soma.Holonics.Millennium.Chronology
open Soma.Holonics.Foundation.RelationLadder
open Soma.Holonics.Foundation.AperturedGradedComplex (ContactClass)

universe u v w

/-! ## 1. The merge verdict -/

/-- [definition] What a merge question returns. There are exactly three answers and only one of
them licenses a merge.

`refuted` carries a separating `(word, receiver)`; `notSeparatedWithinBound` carries the declared
history-length ceiling the search ran under and is **its own return**, never equal potential; and
`equivalentBy` carries an exhibited equivariant isomorphism of the situation.

Rust counterpart: `design_selection.rs::MergeVerdict`. -/
inductive MergeVerdict (Separator : Type u) (Iso : Type v) where
  /-- A separating `(word, receiver)` refutes the collapse. -/
  | refuted (separator : Separator)
  /-- The declared bound was exhausted without a separator. This licenses nothing. -/
  | notSeparatedWithinBound (historyLength : ℕ)
  /-- An exhibited equivariant isomorphism carrying one design to the other. -/
  | equivalentBy (iso : Iso)

variable {Separator : Type u} {Iso : Type v}

/-- [definition] Whether this verdict licenses a merge. -/
def MergeVerdict.licensesMerge : MergeVerdict Separator Iso → Bool
  | .equivalentBy _ => true
  | _ => false

/-- [proved-derived; formal-checked] **A bounded search never licenses a merge.** Exhausting the
declared history-length ceiling without finding a separator is the honest bottom and does not
coerce upward into equivalence. -/
theorem notSeparatedWithinBound_does_not_license_merge (n : ℕ) :
    (MergeVerdict.notSeparatedWithinBound (Separator := Separator) (Iso := Iso) n).licensesMerge
      = false := rfl

/-- [proved-derived; formal-checked] Neither does a refutation. -/
theorem refuted_does_not_license_merge (s : Separator) :
    (MergeVerdict.refuted (Iso := Iso) s).licensesMerge = false := rfl

/-- [proved-derived; formal-checked] **Only an exhibited isomorphism licenses a merge.** -/
theorem only_equivalentBy_licenses_merge (v : MergeVerdict Separator Iso) :
    v.licensesMerge = true ↔ ∃ i : Iso, v = .equivalentBy i := by
  cases v with
  | refuted s => simp [MergeVerdict.licensesMerge]
  | notSeparatedWithinBound n => simp [MergeVerdict.licensesMerge]
  | equivalentBy i => simp [MergeVerdict.licensesMerge]

/-- [proved-derived; formal-checked] **One separating future receiver refutes the collapse.** This
is `RelationLadder.separatorRefutesEqualPotential` at the design situation, cited and not
rebuilt. -/
theorem oneSeparatingFutureReceiverRefutesTheMerge
    {Generator : Type u} {Receiver : Type v} {Design : Type w} {Face : Type*}
    (S : Situation Generator Receiver Design Face) {x y : Design}
    (receiver : Receiver) (word : List Generator)
    (separates : S.observe receiver (transportWord S.step word x) ≠
      S.observe receiver (transportWord S.step word y)) :
    ¬ EqualPotential S x y :=
  separatorRefutesEqualPotential S receiver word separates

/-! ## 2. The design situation: designs, declared environments, declared receivers

[definition] A design is carried together with the environment it is being read at, and the
admitted future transformations are the typed passages of `Foundation/PhysicalOccurrence.lean` — of
which the environment change is the one that moves this pair, and is vertical for exactly that
reason. A generator therefore carries `(design, η)` to `(design, η')`, and a receiver reads the
pair. That is the whole content of "the situation whose generators are the admitted passages and
whose receivers are the declared receiver family across the declared environments". -/

/-- [definition] Three environments: two the declaration below carries and one it does not. -/
abbrev Env := Fin 3

/-- [definition] Two designs. -/
abbrev Design := Fin 2

/-- [definition] The carrier: a design situated at an environment. -/
abbrev Situated := Design × Env

/-- [definition] The environment-change passage: it moves the environment and never the design. -/
def moveTo (target : Env) (s : Situated) : Situated := (s.1, target)

/-- [definition] One declared receiver's exact reading. The two designs agree at environments `0`
and `1` and separate at environment `2`, which the declaration below does not carry. -/
def reading (s : Situated) : ℕ :=
  match s.2.val, s.1.val with
  | 0, _ => 5
  | 1, _ => 7
  | _, 0 => 11
  | _, _ => 13

/-- [definition] The situation whose generators are the passages to the **two declared**
environments. -/
def declaredSituation : Situation (Fin 2) Unit Situated ℕ where
  observe := fun _ s => reading s
  step := fun g s => moveTo (Fin.castSucc g) s

/-- [definition] The same situation with a third environment declared. -/
def enlargedSituation : Situation (Fin 3) Unit Situated ℕ where
  observe := fun _ s => reading s
  step := moveTo

/-- [definition] The first design, read at the first declared environment. -/
def leftDesign : Situated := (0, 0)

/-- [definition] The second design, at the same environment. -/
def rightDesign : Situated := (1, 0)

/-- [proved-derived; formal-checked] A passage moves the environment and retains the design: that
is what makes the environment axis vertical. -/
theorem designIsRetained (w : List (Fin 2)) (s : Situated) :
    (transportWord declaredSituation.step w s).1 = s.1 := by
  induction w with
  | nil => rfl
  | cons g rest ih =>
    simp only [transportWord_cons]
    simpa [declaredSituation, moveTo] using ih

/-- [proved-derived; formal-checked] A nonempty declared history lands the design at the
environment its head names. -/
theorem declaredTransport (g : Fin 2) (rest : List (Fin 2)) (s : Situated) :
    transportWord declaredSituation.step (g :: rest) s = (s.1, Fin.castSucc g) := by
  simp only [transportWord_cons]
  show moveTo (Fin.castSucc g) (transportWord declaredSituation.step rest s) = (s.1, Fin.castSucc g)
  unfold moveTo
  rw [designIsRetained rest s]

/-- [proved-derived; formal-checked] **Present-receiver agreement does not imply environment
agreement.** Every declared receiver returns the same face now, and the declared environment family
still separates the two designs: the merge is refuted by a future receiver, not by the present
one. -/
theorem presentAgreementDoesNotImplyEnvironmentAgreement :
    PresentAgreement enlargedSituation leftDesign rightDesign ∧
      ¬ EqualPotential enlargedSituation leftDesign rightDesign := by
  refine ⟨fun _ => rfl, ?_⟩
  refine oneSeparatingFutureReceiverRefutesTheMerge enlargedSituation () [2] ?_
  decide

/-- [proved-derived; formal-checked] **Environment agreement at the declared environments does not
imply agreement at an undeclared one.** The two designs have equal potential over the declaration
carrying environments `0` and `1`, and the declaration that also carries environment `2` separates
them. The general law is `RelationLadder.equalPotentialAntitone`. -/
theorem declaredEnvironmentAgreementDoesNotImplyUndeclared :
    EqualPotential declaredSituation leftDesign rightDesign ∧
      ¬ EqualPotential enlargedSituation leftDesign rightDesign := by
  refine ⟨?_, presentAgreementDoesNotImplyEnvironmentAgreement.2⟩
  intro _ word
  cases word with
  | nil => rfl
  | cons g rest =>
    rw [declaredTransport g rest leftDesign, declaredTransport g rest rightDesign]
    fin_cases g <;> rfl

/-! ## 3. The empirical pattern, on exact rationals

[definition] The plan records two observations and this section models both exactly. Neither is a
measurement. -/

/-- [definition] Four designs: two binders and two interface-matched designs. -/
abbrev Binder := Fin 4

/-- [definition] Two assay environments: the species the design was selected in, and another. -/
abbrev Assay := Fin 2

/-- [definition] The carrier of the affinity situation. -/
abbrev SituatedBinder := Binder × Assay

/-- [definition] The predicted interface receiver: a contact count, exact. It separates the two
binders from the two interface-matched designs, so it is not a blind receiver. -/
def interfaceReading (s : SituatedBinder) : ℚ :=
  if s.1.val ≤ 1 then 40 else 41

/-- [definition] The measured dissociation constant, exact, in one declared unit throughout.
Binders `0` and `1` agree to one per cent in the first assay and differ about twelve-fold in the
second; designs `2` and `3` agree exactly at the interface receiver and differ six-fold here. -/
def affinityReading (s : SituatedBinder) : ℚ :=
  match s.1.val, s.2.val with
  | 0, _ => 100
  | 1, 0 => 101
  | 1, _ => 1200
  | 2, _ => 50
  | _, _ => 300

/-- [definition] The declared receiver family: the predicted interface receiver and the measured
affinity receiver. -/
def binderObserve (receiver : Fin 2) (s : SituatedBinder) : ℚ :=
  if receiver.val = 0 then interfaceReading s else affinityReading s

/-- [definition] The situation: two declared receivers, and the assay change as the admitted
passage. -/
def affinitySituation : Situation Assay (Fin 2) SituatedBinder ℚ where
  observe := binderObserve
  step := fun target s => (s.1, target)

/-- [proved-derived; formal-checked] **Tolerance-closeness at a present receiver licenses
nothing.** The two binders' dissociation constants at the first assay lie inside two per cent of
`100` — rung 6 of the ladder at that receiver — and the second assay separates them, so they do not
have equal potential. Closeness at one receiver at one environment is a reading, never an
equivalence. -/
theorem toleranceClosenessAtOneReceiverLicensesNothing :
    WithinTolerance affinityReading 2 ((0 : Binder), (0 : Assay)) ((1 : Binder), (0 : Assay)) ∧
      ¬ EqualPotential affinitySituation ((0 : Binder), (0 : Assay))
        ((1 : Binder), (0 : Assay)) := by
  constructor
  · show |affinityReading ((0 : Binder), (0 : Assay)) -
        affinityReading ((1 : Binder), (0 : Assay))| ≤ 2
    norm_num [affinityReading]
  · refine oneSeparatingFutureReceiverRefutesTheMerge affinitySituation 1 [1] ?_
    simp only [transportWord_cons, transportWord_nil]
    show binderObserve 1 ((0 : Binder), (1 : Assay)) ≠ binderObserve 1 ((1 : Binder), (1 : Assay))
    norm_num [binderObserve, affinityReading]

/-- [proved-derived; formal-checked] **Near-identical predicted interface receivers, six-fold
affinity difference.** The two designs are equal at the interface receiver — rung 4 *at that
receiver* — and the affinity receiver separates them at the same environment, six-fold. A
receiver's agreement is the agreement of that receiver and never of the family. -/
theorem interfaceAgreementWithoutAffinityAgreement :
    ReceiverEqualAt affinitySituation 0 ((2 : Binder), (0 : Assay)) ((3 : Binder), (0 : Assay)) ∧
      ¬ ReceiverEqualAt affinitySituation 1 ((2 : Binder), (0 : Assay))
        ((3 : Binder), (0 : Assay)) ∧
      ¬ EqualPotential affinitySituation ((2 : Binder), (0 : Assay))
        ((3 : Binder), (0 : Assay)) := by
  refine ⟨?_, ?_, ?_⟩
  · show binderObserve 0 ((2 : Binder), (0 : Assay)) = binderObserve 0 ((3 : Binder), (0 : Assay))
    norm_num [binderObserve, interfaceReading]
  · show ¬ binderObserve 1 ((2 : Binder), (0 : Assay)) = binderObserve 1 ((3 : Binder), (0 : Assay))
    norm_num [binderObserve, affinityReading]
  · refine oneSeparatingFutureReceiverRefutesTheMerge affinitySituation 1 [] ?_
    simp only [transportWord_nil]
    show binderObserve 1 ((2 : Binder), (0 : Assay)) ≠ binderObserve 1 ((3 : Binder), (0 : Assay))
    norm_num [binderObserve, affinityReading]

/-! ## 4. Stage one — hard constraints, as typed refusals -/

/-- [definition] A hard constraint: a declared name and a decidable admission test. It is **not** a
weight, and there is no arithmetic anywhere in this section: a violated constraint removes the
design and nothing re-admits it.

Rust counterpart: `design_selection.rs::HardConstraint`. -/
structure HardConstraint (D : Type u) where
  /-- The constraint's declared name, which is what a refusal reports. -/
  name : String
  /-- Whether this design satisfies it. -/
  admits : D → Bool

variable {D : Type u}

/-- [definition] The designs every declared constraint admits. -/
def admitted (constraints : List (HardConstraint D)) (family : List D) : List D :=
  family.filter (fun d => constraints.all (fun c => c.admits d))

/-- [definition] The names of the constraints a design violates: a refusal per violated constraint,
never a total. -/
def violations (constraints : List (HardConstraint D)) (d : D) : List String :=
  (constraints.filter (fun c => !c.admits d)).map HardConstraint.name

/-- [proved-derived; formal-checked] **A violated hard constraint removes the design.** Nothing
downstream sees it, whatever every other receiver says. -/
theorem violating_design_is_never_admitted
    (constraints : List (HardConstraint D)) (family : List D) (d : D)
    (c : HardConstraint D) (mem : c ∈ constraints) (violated : c.admits d = false) :
    d ∉ admitted constraints family := by
  intro contra
  have hall := List.all_eq_true.mp (List.mem_filter.mp contra).2 c mem
  rw [violated] at hall
  exact absurd hall (by simp)

/-- [proved-derived; formal-checked] **The refusal names the constraint.** -/
theorem refusal_names_the_constraint
    (constraints : List (HardConstraint D)) (d : D)
    (c : HardConstraint D) (mem : c ∈ constraints) (violated : c.admits d = false) :
    c.name ∈ violations constraints d :=
  List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨mem, by simp [violated]⟩, rfl⟩

/-- [definition] A constraint the design at index `0` violates. -/
def witnessConstraint : HardConstraint (Fin 3) :=
  { name := "the declared expression host is admitted", admits := fun d => decide (d ≠ 0) }

/-- [proved-derived; formal-checked] **A hard constraint is not a penalty term.** The design at
index `0` is absent from the admitted family however every receiver reads it: no weight makes a
violated constraint survivable, because no weight enters this stage at all. -/
theorem theBestDesignIsStillRefused :
    (0 : Fin 3) ∉ admitted [witnessConstraint] [0, 1, 2] ∧
      admitted [witnessConstraint] [0, 1, 2] = [1, 2] := by
  refine ⟨violating_design_is_never_admitted _ _ _ witnessConstraint (by simp) (by decide), ?_⟩
  decide

/-! ## 5. Stage three — the worst reading over the declared environments -/

/-- [definition] One receiver's reading of one design at one declared environment. `unread` is a
stated absence and is never a value.

Rust counterpart: `design_selection.rs::ReceiverReading`. -/
inductive Reading where
  /-- An exact reading. -/
  | read (value : ℚ)
  /-- The receiver did not read this design here, with the stated reason. -/
  | unread (why : String)
  deriving DecidableEq

/-- [definition] What the worst-environment stage returns.

Rust counterpart: `design_selection.rs::WorstVerdict`. -/
inductive WorstVerdict (E : Type u) where
  /-- The worst exact reading over the declared family, with **every** environment attaining it. -/
  | worst (value : ℚ) (attained : List E)
  /-- The design is unread at this declared environment, so it is refused for ranking there. It is
  not imputed a best case, a worst case or a default. -/
  | unreadAt (environment : E)
  /-- No environment was declared, so there is nothing to be worst over. -/
  | noEnvironmentDeclared

variable {E : Type u}

/-- [definition] One step of the maximum fold. -/
def maxOption : Option ℚ → ℚ → Option ℚ
  | none, v => some v
  | some m, v => some (max v m)

/-- [definition] The maximum of a list of exact readings. Smaller is better throughout this
section, so the *worst* reading is the largest. -/
def maxOf : List ℚ → Option ℚ
  | [] => none
  | v :: rest => maxOption (maxOf rest) v

@[simp] theorem maxOf_nil : maxOf [] = none := rfl

@[simp] theorem maxOf_cons (v : ℚ) (rest : List ℚ) :
    maxOf (v :: rest) = maxOption (maxOf rest) v := rfl

theorem maxOption_ne_none (o : Option ℚ) (v : ℚ) : maxOption o v ≠ none := by
  cases o <;> simp [maxOption]

/-- [proved-derived; formal-checked] A list has no maximum exactly when it is empty. -/
theorem maxOf_eq_none_iff : ∀ l : List ℚ, maxOf l = none ↔ l = []
  | [] => by simp
  | x :: rest => by
    refine ⟨fun h => absurd (maxOf_cons x rest ▸ h) (maxOption_ne_none _ _), fun h => by simp at h⟩

/-- [proved-derived; formal-checked] **The maximum is attained**: it is one of the readings and
never an interpolation between them. -/
theorem maxOf_mem : ∀ (l : List ℚ) (v : ℚ), maxOf l = some v → v ∈ l
  | [], _, h => by simp at h
  | x :: rest, v, h => by
    rw [maxOf_cons] at h
    cases hrest : maxOf rest with
    | none =>
      rw [hrest] at h
      simp only [maxOption, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    | some m =>
      rw [hrest] at h
      simp only [maxOption, Option.some.injEq] at h
      subst h
      rcases max_choice x m with hc | hc
      · rw [hc]; exact List.mem_cons_self
      · rw [hc]; exact List.mem_cons_of_mem _ (maxOf_mem rest m hrest)

/-- [proved-derived; formal-checked] **The maximum bounds every reading.** -/
theorem le_maxOf : ∀ (l : List ℚ) (v x : ℚ), maxOf l = some v → x ∈ l → x ≤ v
  | [], _, _, h, _ => by simp at h
  | y :: rest, v, x, h, hx => by
    rw [maxOf_cons] at h
    cases hrest : maxOf rest with
    | none =>
      rw [hrest] at h
      simp only [maxOption, Option.some.injEq] at h
      subst h
      have hnil : rest = [] := (maxOf_eq_none_iff rest).mp hrest
      subst hnil
      simp only [List.mem_singleton] at hx
      subst hx
      exact le_refl _
    | some m =>
      rw [hrest] at h
      simp only [maxOption, Option.some.injEq] at h
      subst h
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact le_max_left _ _
      · exact le_trans (le_maxOf rest m x hrest hmem) (le_max_right _ _)

/-- [definition] The first declared environment the design is unread at, if any. -/
def firstUnread (read : E → Reading) : List E → Option E
  | [] => none
  | e :: rest =>
    match read e with
    | .unread _ => some e
    | .read _ => firstUnread read rest

/-- [definition] The exact readings over the declared environment family, in declaration order. -/
def values (read : E → Reading) : List E → List ℚ
  | [] => []
  | e :: rest =>
    match read e with
    | .read v => v :: values read rest
    | .unread _ => values read rest

/-- [definition] Every declared environment at which the reading is exactly `v`. -/
def attaining (read : E → Reading) (v : ℚ) : List E → List E
  | [] => []
  | e :: rest =>
    if read e = Reading.read v then e :: attaining read v rest else attaining read v rest

/-- [definition] **The worst reading over a declared finite environment family.** Smaller is
better, so this is the maximum.

An environment that is not in `envs` is **absent**: it contributes nothing and is neither a best
case nor a worst case. A design unread at a *declared* environment is **refused for ranking**
there and never imputed a value.

Rust counterpart: `design_selection.rs::worst_over`. -/
def worstOver (read : E → Reading) (envs : List E) : WorstVerdict E :=
  match firstUnread read envs with
  | some e => .unreadAt e
  | none =>
    match maxOf (values read envs) with
    | none => .noEnvironmentDeclared
    | some v => .worst v (attaining read v envs)

/-- [proved-derived; formal-checked] **The worst reading is attained at a declared environment.**
It is one of the declared readings and never an aggregate of them. -/
theorem worst_is_attained (read : E → Reading) (envs : List E) (v : ℚ) (attained : List E)
    (h : worstOver read envs = .worst v attained) : v ∈ values read envs := by
  unfold worstOver at h
  cases hfirst : firstUnread read envs with
  | some e => rw [hfirst] at h; exact absurd h (by simp)
  | none =>
    rw [hfirst] at h
    cases hmax : maxOf (values read envs) with
    | none => rw [hmax] at h; exact absurd h (by simp)
    | some m =>
      rw [hmax] at h
      simp only [WorstVerdict.worst.injEq] at h
      exact h.1 ▸ maxOf_mem _ m hmax

/-- [proved-derived; formal-checked] **The worst reading bounds every declared reading.** -/
theorem worst_is_an_upper_bound (read : E → Reading) (envs : List E) (v : ℚ) (attained : List E)
    (h : worstOver read envs = .worst v attained) (x : ℚ) (hx : x ∈ values read envs) : x ≤ v := by
  unfold worstOver at h
  cases hfirst : firstUnread read envs with
  | some e => rw [hfirst] at h; exact absurd h (by simp)
  | none =>
    rw [hfirst] at h
    cases hmax : maxOf (values read envs) with
    | none => rw [hmax] at h; exact absurd h (by simp)
    | some m =>
      rw [hmax] at h
      simp only [WorstVerdict.worst.injEq] at h
      exact h.1 ▸ le_maxOf _ m x hmax hx

theorem firstUnread_congr (read read' : E → Reading) :
    ∀ envs : List E, (∀ e ∈ envs, read e = read' e) →
      firstUnread read envs = firstUnread read' envs
  | [], _ => rfl
  | e :: rest, agree => by
    have he : read e = read' e := agree e (List.mem_cons_self)
    have hrest := firstUnread_congr read read' rest
      (fun x hx => agree x (List.mem_cons_of_mem _ hx))
    simp only [firstUnread, he, hrest]

theorem values_congr (read read' : E → Reading) :
    ∀ envs : List E, (∀ e ∈ envs, read e = read' e) → values read envs = values read' envs
  | [], _ => rfl
  | e :: rest, agree => by
    have he : read e = read' e := agree e (List.mem_cons_self)
    have hrest := values_congr read read' rest (fun x hx => agree x (List.mem_cons_of_mem _ hx))
    simp only [values, he, hrest]

theorem attaining_congr (read read' : E → Reading) (v : ℚ) :
    ∀ envs : List E, (∀ e ∈ envs, read e = read' e) →
      attaining read v envs = attaining read' v envs
  | [], _ => rfl
  | e :: rest, agree => by
    have he : read e = read' e := agree e (List.mem_cons_self)
    have hrest := attaining_congr read read' v rest
      (fun x hx => agree x (List.mem_cons_of_mem _ hx))
    simp only [attaining, he, hrest]

/-- [proved-derived; formal-checked] **An undeclared environment is absent.** Two readings agreeing
on the declared family return the same verdict however they differ elsewhere: an environment the
declaration does not carry is neither a best case nor a worst case, it simply is not there. -/
theorem undeclared_environment_is_absent (read read' : E → Reading) (envs : List E)
    (agree : ∀ e ∈ envs, read e = read' e) : worstOver read envs = worstOver read' envs := by
  have hfirst := firstUnread_congr read read' envs agree
  have hvalues := values_congr read read' envs agree
  have hattaining : ∀ v : ℚ, attaining read v envs = attaining read' v envs :=
    fun v => attaining_congr read read' v envs agree
  simp only [worstOver, hfirst, hvalues, hattaining]

/-- [proved-derived; formal-checked] **An unread declared environment is a refusal.** The verdict
is `unreadAt`, so ranking there is declined rather than carried out on an imputed value. -/
theorem unread_at_a_declared_environment_refuses (read : E → Reading) :
    ∀ (envs : List E) (e : E), e ∈ envs → (∃ why, read e = .unread why) →
      ∃ e', worstOver read envs = .unreadAt e'
  | [], _, hmem, _ => by simp at hmem
  | x :: rest, e, hmem, hunread => by
    cases hx : read x with
    | unread w => exact ⟨x, by simp only [worstOver, firstUnread, hx]⟩
    | read value =>
      rcases List.mem_cons.mp hmem with rfl | hrest
      · obtain ⟨why, hwhy⟩ := hunread
        rw [hx] at hwhy
        exact absurd hwhy (by simp)
      · obtain ⟨e', he'⟩ :=
          unread_at_a_declared_environment_refuses read rest e hrest hunread
        refine ⟨e', ?_⟩
        cases hf : firstUnread read rest with
        | some e'' =>
          simp only [worstOver, firstUnread, hx, hf] at he' ⊢
          exact he'
        | none =>
          exfalso
          simp only [worstOver, hf] at he'
          cases hm : maxOf (values read rest) with
          | none => simp only [hm] at he'; exact absurd he' (by simp)
          | some v => simp only [hm] at he'; exact absurd he' (by simp)

/-! ## 6. Stage four — quality-diversity, and why a scalar may not go first -/

/-- [proved-derived; formal-checked] **A scalar-first cascade discards a frontier design that every
stage above it keeps.** The three-point family of `Foundation/PresentationCost.lean::chordFamily`
is an antichain: all three are frontier points, so the hard-constraint stage admits all three, the
frontier stage keeps all three, and quality-diversity keeps a representative of each. Yet for every
weighting putting positive weight on either varying axis, one of the two corners scores strictly
lower than the balanced design, so a cascade that ranks by that scalar first loses it.

This cites `PresentationCost.unsupported_isFrontierPoint` and
`PresentationCost.unsupported_not_minimizer`; it rebuilds neither. -/
theorem scalarFirstDiscardsAFrontierDesign (q : PresentationCost.Weighting)
    (weighs : 0 < q.weight .bytes ∨ 0 < q.weight .decodeWork) :
    PresentationCost.IsFrontierPoint PresentationCost.chordFamily PresentationCost.chordCost
        .balanced ∧
      ∃ j ∈ PresentationCost.chordFamily,
        q.objective (PresentationCost.chordCost j) <
          q.objective (PresentationCost.chordCost .balanced) :=
  ⟨PresentationCost.unsupported_isFrontierPoint,
    PresentationCost.unsupported_not_minimizer q weighs⟩

/-! ## 7. Stage five — structural clustering from the exact separator structure -/

open Soma.Holonics.Foundation.PhysicalOccurrence

/-- [definition] The decided-inside face over one contact. -/
def insideFace : ContactFace Unit := fun _ => ContactClass.inside

/-- [definition] The undecided face. -/
def openFace : ContactFace Unit := fun _ => ContactClass.openContact

/-- [definition] The decided-outside face. -/
def outsideFace : ContactFace Unit := fun _ => ContactClass.outside

/-- [proved-derived; formal-checked] **Indistinguishability is not transitive once a reading is
open.** A contact one face leaves open enters no separator set of a pair that reads it open, so the
open face is indistinguishable from both decided faces while those two separate each other. A
structural cluster is therefore a **connected component** of the indistinguishability graph and not
an equivalence class of it — which is why the clustering stage returns components computed from the
exact separator structure and never a float embedding's neighbourhoods. -/
theorem indistinguishabilityIsNotTransitive :
    Indistinguishable [()] insideFace openFace ∧
      Indistinguishable [()] openFace outsideFace ∧
      ¬ Indistinguishable [()] insideFace outsideFace := by
  refine ⟨fun c _ => by simp [separatesB, insideFace, openFace],
    fun c _ => by simp [separatesB, openFace], fun contra => ?_⟩
  have := contra () (by simp)
  simp [separatesB, insideFace, outsideFace] at this

/-- [proved-derived; formal-checked] **A component can contain a pair the receiver separates.**
That is the honest content of a structural cluster: it is *generated by* indistinguishability and
is not itself indistinguishability, so a cluster is reported as a component and never as a
merge. -/
theorem aComponentCanContainASeparatedPair :
    Relation.ReflTransGen (Indistinguishable (κ := Unit) [()]) insideFace outsideFace ∧
      ¬ Indistinguishable [()] insideFace outsideFace := by
  obtain ⟨first, second, apart⟩ := indistinguishabilityIsNotTransitive
  exact ⟨Relation.ReflTransGen.head first (Relation.ReflTransGen.single second), apart⟩

/-! ## 8. The B8 contract -/

/-- [proved-derived; formal-checked] **The B8 contract.** A bounded search never licenses a merge
and only an exhibited isomorphism does; present-receiver agreement does not imply environment
agreement and agreement at the declared environments does not imply agreement at an undeclared
one; a violated hard constraint removes a design whatever every receiver says; the worst reading
over the declared environments is attained and bounds the declared readings, and an unread declared
environment refuses it; and a structural cluster is a component, not an equivalence class of
indistinguishability. -/
theorem selection_contract :
    (∀ n : ℕ,
        (MergeVerdict.notSeparatedWithinBound (Separator := Unit) (Iso := Unit) n).licensesMerge
          = false) ∧
      (∀ v : MergeVerdict Unit Unit, v.licensesMerge = true ↔ ∃ i : Unit, v = .equivalentBy i) ∧
      (PresentAgreement enlargedSituation leftDesign rightDesign ∧
        ¬ EqualPotential enlargedSituation leftDesign rightDesign) ∧
      (EqualPotential declaredSituation leftDesign rightDesign ∧
        ¬ EqualPotential enlargedSituation leftDesign rightDesign) ∧
      (∀ (constraints : List (HardConstraint (Fin 3))) (family : List (Fin 3)) (d : Fin 3)
        (c : HardConstraint (Fin 3)), c ∈ constraints → c.admits d = false →
        d ∉ admitted constraints family) ∧
      (∀ (read : Fin 3 → Reading) (envs : List (Fin 3)) (v : ℚ) (attained : List (Fin 3)),
        worstOver read envs = .worst v attained → v ∈ values read envs) ∧
      (∀ (read : Fin 3 → Reading) (envs : List (Fin 3)) (e : Fin 3), e ∈ envs →
        (∃ why, read e = .unread why) → ∃ e', worstOver read envs = .unreadAt e') ∧
      (Relation.ReflTransGen (Indistinguishable (κ := Unit) [()]) insideFace outsideFace ∧
        ¬ Indistinguishable [()] insideFace outsideFace) :=
  ⟨notSeparatedWithinBound_does_not_license_merge,
    only_equivalentBy_licenses_merge,
    presentAgreementDoesNotImplyEnvironmentAgreement,
    declaredEnvironmentAgreementDoesNotImplyUndeclared,
    fun constraints family d c mem violated =>
      violating_design_is_never_admitted constraints family d c mem violated,
    fun read envs v attained h => worst_is_attained read envs v attained h,
    fun read envs e hmem hunread =>
      unread_at_a_declared_environment_refuses read envs e hmem hunread,
    aComponentCanContainASeparatedPair⟩

/-! ## 9. B10 — the cost cascade, and when a cheap stage may discard

[definition] The selection cascade of section 7 and the cost cascade of item **B10** are **one
cascade with two readings**: what is decided, and what it costs. This section states the law that
makes the cheap reading admissible at all. A stage runs a cheap test and stands in for an expensive
receiver; it may discard only where the expensive receiver would also discard. A hard constraint is
the degenerate case — the cheap test *is* the expensive one — and a **certified bound** is the
general one: the cheap reading provably refuses only where the expensive one does.

The worked physical instance is in `Foundation/GrainRestriction.lean`: at the *inflated* coarse
aperture, `inflated_carries_every_fine_contact` says every non-`outside` fine contact is carried, so
a coarse `outside` reading certifies a fine `outside` reading and the cheap stage's discard is
sound. At the **equal** aperture it is not — `equal_aperture_is_not_lawful` — and the Rust owner
measures the loss on the M5 material. -/

/-- [definition] **One stage of the cascade**: the cheap reading it actually runs, and the expensive
receiver it stands in for.

Rust counterpart: `design_selection.rs::CascadeStage`. -/
structure CascadeStage (D : Type u) where
  /-- The stage's declared name, which is what a discard reports. -/
  name : String
  /-- The cheap reading the stage runs on every candidate that reaches it. -/
  cheap : D → Bool
  /-- The expensive receiver it stands in for. -/
  expensive : D → Bool

/-- [definition] **A certified bound**: the cheap reading refuses only where the expensive receiver
also refuses. This is the whole content of "the cheap reading bounds the expensive one in the
discarding direction".

Rust counterpart: `design_selection.rs::DiscardLaw::CertifiedBound`. -/
def Certified {D : Type u} (s : CascadeStage D) : Prop :=
  ∀ d, s.cheap d = false → s.expensive d = false

/-- [definition] A hard constraint read as a stage: the cheap test **is** the expensive one. -/
def hardConstraintStage {D : Type u} (name : String) (admits : D → Bool) : CascadeStage D where
  name := name
  cheap := admits
  expensive := admits

/-- [proved-derived; formal-checked] A hard constraint is certified, trivially: every later stage
issues the same refusal. -/
theorem hardConstraintStage_is_certified {D : Type u} (name : String) (admits : D → Bool) :
    Certified (hardConstraintStage name admits) := fun _ h => h

/-- [definition] **What the cascade keeps**: a candidate that survives the cheap filter of every
stage and the expensive receiver of every stage it thereby reaches. -/
def cascadeSurvivors {D : Type u} (stages : List (CascadeStage D)) (population : List D) :
    List D :=
  population.filter (fun d => stages.all (fun s => s.cheap d && s.expensive d))

/-- [definition] **What the full evaluation keeps**: every expensive receiver run on everything. -/
def fullSurvivors {D : Type u} (stages : List (CascadeStage D)) (population : List D) : List D :=
  population.filter (fun d => stages.all (fun s => s.expensive d))

/-- The per-candidate step of the equality below. -/
theorem all_cheap_and_expensive {D : Type u} (stages : List (CascadeStage D))
    (certified : ∀ s ∈ stages, Certified s) (d : D) :
    stages.all (fun s => s.cheap d && s.expensive d) = stages.all (fun s => s.expensive d) := by
  induction stages with
  | nil => rfl
  | cons s rest ih =>
      have head : Certified s := certified s (by simp)
      have tail : ∀ t ∈ rest, Certified t := fun t ht => certified t (by simp [ht])
      simp only [List.all_cons]
      rw [ih tail]
      cases hc : s.cheap d
      · have expensive_refuses : s.expensive d = false := head d hc
        simp [expensive_refuses]
      · simp

/-- [proved-derived; formal-checked] **With certified filters the cascade's frontier equals the full
evaluation's frontier.** The cheap stages change what is *computed*, never what is *kept*. -/
theorem certified_cascade_preserves_the_frontier {D : Type u} (stages : List (CascadeStage D))
    (certified : ∀ s ∈ stages, Certified s) (population : List D) :
    cascadeSurvivors stages population = fullSurvivors stages population := by
  unfold cascadeSurvivors fullSurvivors
  have step : (fun d => stages.all (fun s => s.cheap d && s.expensive d))
      = (fun d => stages.all (fun s => s.expensive d)) :=
    funext (all_cheap_and_expensive stages certified)
  rw [step]

/-- A cheap scalar proxy with no certificate: it refuses `false`, which the expensive receiver
admits. -/
def proxyStage : CascadeStage Bool where
  name := "a cheap scalar proxy standing in for an expensive receiver, with no certificate"
  cheap := fun d => d
  expensive := fun _ => true

/-- [proved-derived; formal-checked] It is not a certified bound. -/
theorem proxyStage_is_not_certified : ¬ Certified proxyStage := by
  intro certified
  have refuses := certified false rfl
  simp [proxyStage] at refuses

/-- [proved-derived; formal-checked] **An uncertified proxy loses a design the full evaluation
keeps.** This is the constructed instance; its design-level form is
`scalarFirstDiscardsAFrontierDesign`, which cites `PresentationCost.unsupported_not_minimizer`. -/
theorem uncertified_proxy_loses_a_frontier_design :
    cascadeSurvivors [proxyStage] [false, true] ≠ fullSurvivors [proxyStage] [false, true] := by
  decide

/-- A certified cheap stage: the coarse contact receiver at the inflated aperture, whose `outside`
reading certifies the fine receiver's `outside` reading. -/
def certifiedStage : CascadeStage Bool where
  name := "the coarse contact receiver at the inflated aperture"
  cheap := fun d => d
  expensive := fun d => d

/-- [proved-derived; formal-checked] It is a certified bound. -/
theorem certifiedStage_is_certified : Certified certifiedStage := fun _ h => h

/-- [definition] How many candidates the expensive receiver of a stage is run on when the cheap
filter runs first: the survivors of the cheap filter, and nothing else. -/
def expensiveWork {D : Type u} (s : CascadeStage D) (population : List D) : Nat :=
  (population.filter (fun d => s.cheap d)).length

/-- [proved-derived; formal-checked] The expensive receiver is never run more often than the
population. -/
theorem expensiveWork_le_population {D : Type u} (s : CascadeStage D) (population : List D) :
    expensiveWork s population ≤ population.length := by
  unfold expensiveWork
  exact List.length_filter_le _ _

/-- [proved-derived; formal-checked] And on this population the certified cheap stage strictly
saves: the expensive receiver runs once where the full evaluation runs it twice, and by
`certified_cascade_preserves_the_frontier` the answer is the same. -/
theorem the_certified_filter_saves_expensive_work :
    expensiveWork certifiedStage [false, true] < ([false, true] : List Bool).length := by decide

/-- [proved-derived; formal-checked] **The B10 cascade contract.** A hard constraint is certified; a
cascade of certified stages returns exactly the full evaluation's survivors; an uncertified proxy
does not, with the loss exhibited; and the expensive receiver runs only on the cheap filter's
survivors. -/
theorem cost_cascade_contract :
    (∀ (name : String) (admits : Bool → Bool), Certified (hardConstraintStage name admits)) ∧
      (∀ (stages : List (CascadeStage Bool)), (∀ s ∈ stages, Certified s) →
        ∀ population, cascadeSurvivors stages population = fullSurvivors stages population) ∧
      (¬ Certified proxyStage ∧
        cascadeSurvivors [proxyStage] [false, true] ≠ fullSurvivors [proxyStage] [false, true]) ∧
      (∀ (s : CascadeStage Bool) (population : List Bool),
        expensiveWork s population ≤ population.length) :=
  ⟨hardConstraintStage_is_certified,
    fun stages certified population =>
      certified_cascade_preserves_the_frontier stages certified population,
    ⟨proxyStage_is_not_certified, uncertified_proxy_loses_a_frontier_design⟩,
    expensiveWork_le_population⟩

section Audit

#print axioms notSeparatedWithinBound_does_not_license_merge
#print axioms refuted_does_not_license_merge
#print axioms only_equivalentBy_licenses_merge
#print axioms oneSeparatingFutureReceiverRefutesTheMerge
#print axioms designIsRetained
#print axioms declaredTransport
#print axioms presentAgreementDoesNotImplyEnvironmentAgreement
#print axioms declaredEnvironmentAgreementDoesNotImplyUndeclared
#print axioms toleranceClosenessAtOneReceiverLicensesNothing
#print axioms interfaceAgreementWithoutAffinityAgreement
#print axioms violating_design_is_never_admitted
#print axioms refusal_names_the_constraint
#print axioms theBestDesignIsStillRefused
#print axioms maxOf_eq_none_iff
#print axioms maxOf_mem
#print axioms le_maxOf
#print axioms worst_is_attained
#print axioms worst_is_an_upper_bound
#print axioms undeclared_environment_is_absent
#print axioms unread_at_a_declared_environment_refuses
#print axioms scalarFirstDiscardsAFrontierDesign
#print axioms indistinguishabilityIsNotTransitive
#print axioms aComponentCanContainASeparatedPair
#print axioms selection_contract
#print axioms hardConstraintStage_is_certified
#print axioms all_cheap_and_expensive
#print axioms certified_cascade_preserves_the_frontier
#print axioms proxyStage_is_not_certified
#print axioms uncertified_proxy_loses_a_frontier_design
#print axioms certifiedStage_is_certified
#print axioms expensiveWork_le_population
#print axioms the_certified_filter_saves_expensive_work
#print axioms cost_cascade_contract

end Audit

end Soma.Holonics.Foundation.DesignSelection
