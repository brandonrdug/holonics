import Holonics.Foundation.Standing.Law
import Holonics.Objects.Retention
import Holonics.Compression.Landmark.Context.Birth
import HolonicsResearch.Foundation.SeparationDepth
import Mathlib.Tactic

/-!
# The minimal retention quotient

Object 8 of `docs/ELEMENTARY_OBJECTS.md` and the retention contract: retention is a quotient of the
present sufficient for the admitted future, never a record of what shaped it.
`Foundation/Standing/Law` proved that a retention carries a lawful `StandingLaw` exactly when every
admitted future observation factors through it (`standingLaw_exists_iff_future_factors`), and
`Objects/Deposition` proved that the constitution is such a retention but not a minimal one
(`constitutionStanding`, `constitution_is_not_minimal`). `Objects/Retention` found the minimal
retention of the square-law parallel pair. This module characterizes the minimal
future-sufficient quotient in general (#410, "the minimal retention quotient").

[proved-standard; formal-checked] What is proved.

1. **What minimal means** (`IsMinimal`, `IsMinimal.retain_eq_iff`,
   `isMinimal_iff_every_retained_difference_is_read`). A standing is minimal when it merges every
   two presents the admitted future does not separate. Equivalently its retention kernel is exactly
   the future agreement of `Foundation/CausalRelevance`, and equivalently every difference it
   retains is read by some admitted receiver after some admitted history: it keeps no dead weight.
2. **It exists, as the Nerode machine of the admitted future** (`minimalStanding`,
   `minimalStanding_isMinimal`). The retained value is the future-agreement class `[x]`; the
   transports descend to the classes (`minimalMove`, `[T_g x] = T̄_g [x]`) and so do the receivers
   (`minimalFace`), and the standing reopens a future by running the descended machine, with no
   choice and no record. `canonicalStanding` (the causal signature) is minimal too
   (`canonicalStanding_isMinimal`).
3. **It is least, unique, and a machine** (`IsMinimal.retain_eq_of_retain_eq`,
   `IsMinimal.retain_eq_iff_retain_eq`, `IsMinimal.relabel`, `IsMinimal.retain_transport`). Every
   standing of the same medium refines every minimal one; two minimal standings merge the same
   presents, so their retained values correspond by a bijection that commutes with retention; and a
   minimal standing's kernel is a right congruence, each transport carries merged presents to merged
   presents (Myhill–Nerode).
4. **Every depositing medium** (`futureAgreement_iff_constitution`,
   `depositionMinimalStanding_isMinimal`, `constitutionStanding_isMinimal_iff`). For every
   deposition law, every incidence and every solver, two presents share their future exactly when
   their constitutions share it under the constitution-only machine (`stepConstitution`,
   `observeConstitution`). So the minimal retention is the class of the constitution
   (`depositionMinimalStanding`): neither the flux record nor the solver's gauge enters it, and the
   constitution is minimal exactly when no two distinct constitutions share a future. Under the
   square law on the parallel pair they do (`constitutionStanding_not_isMinimal`), and
   `Objects/Retention.minimalRetain` is that pair's minimal retention in closed form
   (`parallel_minimalRetain_isMinimal`).
5. **The linear chart: the founded encoding is minimal** (Kalman). For linear transports `T_a` and
   receiving forms `ρ_c` on a finite-dimensional chart, Birth's founded forms are the span of the
   transported readings, `founded = span {ρ_c ∘ T_w}` (`founded_eq_span_wordForms`); two states
   share their future exactly when every founded form agrees on them
   (`futureAgreement_iff_founded`), exactly when Birth's encoding `E x = (φ_i x)_i` on a basis of
   the founded forms agrees (`encode_eq_iff_futureAgreement`); so `E` is a minimal standing
   (`founded_encoding_isMinimal`), the observability quotient. Words of length at most
   `dim X − dim span{ρ_c}` already decide it (`futureAgreement_iff_agreeUpTo_finrank`), the linear
   counterpart of `Foundation/SeparationDepth`'s count of states.

[open] The explicit classes of the square law's minimal retention on a general weighted graph
(`Objects/Retention`'s open item): item 4 characterizes them as constitution future agreement and
computes them only on the parallel pair.

The computational object is the helical pair interaction read by its admitted futures: a receiver
reads a contact after an ordered word of navigator moves, and the minimal retention keeps exactly
the differences some such reading separates. Of the winding guide's six general objects this
touches the tube (histories as clocked words and the founding ladder over them) and the tower thread
(the minimal quotient is what the next level reads); the helix, the pair, faces and placement and
the cell holonomy stay attached.

Consumers: the atlas rows `retention.minimal-standing`, `deposition.minimal-retention-general`,
`retention.linear-minimal-chart`, `tower.minimal-realization` and `encoding.minimal-realization`,
and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Foundation.MinimalRetention

open Holonics.Foundation.Chronology
open Holonics.Foundation.CausalRelevance.NonLinear
open Holonics.Foundation.Standing

/-! ## 1. Minimal standings -/

section Abstract

variable {Generator Receiver Source Retained Retained' Face : Type*}

/-- [definition] **A minimal standing** merges every two presents that the admitted future does not
separate. -/
def IsMinimal (L : StandingLaw Generator Receiver Source Retained Face) : Prop :=
  ∀ left right, futureAgreement L.observe L.transport left right → L.retain left = L.retain right

/-- [proved-standard; formal-checked] **The kernel of a minimal standing is the future agreement.** -/
theorem IsMinimal.retain_eq_iff {L : StandingLaw Generator Receiver Source Retained Face}
    (hL : IsMinimal L) {left right : Source} :
    L.retain left = L.retain right ↔ futureAgreement L.observe L.transport left right :=
  ⟨L.futureAgreement_of_retain_eq, hL left right⟩

/-- [proved-standard; formal-checked] **A minimal standing keeps no dead weight**: a standing is
minimal exactly when every difference it retains is read by some admitted receiver after some
admitted history. -/
theorem isMinimal_iff_every_retained_difference_is_read
    (L : StandingLaw Generator Receiver Source Retained Face) :
    IsMinimal L ↔ ∀ left right,
      (∀ receiver word, L.reopen receiver word (L.retain left) =
        L.reopen receiver word (L.retain right)) → L.retain left = L.retain right := by
  constructor
  · intro hL left right hread
    refine hL left right fun receiver word => ?_
    rw [← L.sufficient, ← L.sufficient]
    exact hread receiver word
  · intro hread left right hagree
    refine hread left right fun receiver word => ?_
    rw [L.sufficient, L.sufficient]
    exact hagree receiver word

/-- [proved-standard; formal-checked] **A minimal standing is least**: every standing of the same
medium refines it. -/
theorem IsMinimal.retain_eq_of_retain_eq {L : StandingLaw Generator Receiver Source Retained Face}
    (hL : IsMinimal L) (L' : StandingLaw Generator Receiver Source Retained' Face)
    (htransport : L'.transport = L.transport) (hobserve : L'.observe = L.observe)
    {left right : Source} (h : L'.retain left = L'.retain right) :
    L.retain left = L.retain right := by
  have hagree := L'.futureAgreement_of_retain_eq h
  rw [htransport, hobserve] at hagree
  exact hL left right hagree

/-- [proved-standard; formal-checked] **Two minimal standings of one medium merge the same
presents.** -/
theorem IsMinimal.retain_eq_iff_retain_eq {L : StandingLaw Generator Receiver Source Retained Face}
    {L' : StandingLaw Generator Receiver Source Retained' Face} (hL : IsMinimal L)
    (hL' : IsMinimal L') (htransport : L'.transport = L.transport)
    (hobserve : L'.observe = L.observe) (left right : Source) :
    L.retain left = L.retain right ↔ L'.retain left = L'.retain right := by
  rw [hL.retain_eq_iff, hL'.retain_eq_iff, htransport, hobserve]

/-- [proved-standard; formal-checked] **The minimal standing is unique up to relabeling**: the
retained values of two minimal standings of one medium correspond by a bijection that carries the
retention of each present to the retention of the same present. -/
theorem IsMinimal.relabel {L : StandingLaw Generator Receiver Source Retained Face}
    {L' : StandingLaw Generator Receiver Source Retained' Face} (hL : IsMinimal L)
    (hL' : IsMinimal L') (htransport : L'.transport = L.transport)
    (hobserve : L'.observe = L.observe) :
    ∃ e : Set.range L.retain ≃ Set.range L'.retain,
      ∀ x, e ⟨L.retain x, x, rfl⟩ = ⟨L'.retain x, x, rfl⟩ := by
  have hiff := hL.retain_eq_iff_retain_eq hL' htransport hobserve
  refine ⟨(Setoid.quotientKerEquivRange L.retain).symm.trans
    ((Quotient.congrRight (r := Setoid.ker L.retain) (r' := Setoid.ker L'.retain)
      (fun a b => hiff a b)).trans (Setoid.quotientKerEquivRange L'.retain)), fun x => ?_⟩
  have h₁ : (Setoid.quotientKerEquivRange L.retain).symm ⟨L.retain x, x, rfl⟩ =
      Quotient.mk (Setoid.ker L.retain) x :=
    (Equiv.symm_apply_eq _).mpr (Subtype.ext rfl)
  rw [Equiv.trans_apply, Equiv.trans_apply, h₁]
  exact Subtype.ext rfl

/-- [proved-standard; formal-checked] **A minimal standing is a machine** (Myhill–Nerode): its
kernel is a right congruence, each admitted transport carries merged presents to merged presents. -/
theorem IsMinimal.retain_transport {L : StandingLaw Generator Receiver Source Retained Face}
    (hL : IsMinimal L) {left right : Source} (h : L.retain left = L.retain right)
    (generator : Generator) :
    L.retain (L.transport generator left) = L.retain (L.transport generator right) :=
  hL _ _ (futureAgreement_preserved_by_step _ _ (L.futureAgreement_of_retain_eq h) generator)

variable (observe : Receiver → Source → Face) (transport : Generator → Source → Source)

/-- [proved-standard; formal-checked] **The causal signature is a minimal standing.** -/
theorem canonicalStanding_isMinimal : IsMinimal (canonicalStanding observe transport) :=
  fun left right h => (causalSignature_eq_iff_futureAgreement observe transport left right).mpr h

/-- [definition] Future agreement as a setoid. -/
def futureSetoid : Setoid Source :=
  ⟨futureAgreement observe transport, futureAgreement_equivalence observe transport⟩

/-- [definition] **The descended move**: a transport acting on future-agreement classes,
`T̄_g [x] = [T_g x]` (`futureAgreement_preserved_by_step`). -/
def minimalMove (generator : Generator) :
    Quotient (futureSetoid observe transport) → Quotient (futureSetoid observe transport) :=
  Quotient.lift (fun x => Quotient.mk (futureSetoid observe transport) (transport generator x))
    (fun _ _ h => Quotient.sound (futureAgreement_preserved_by_step observe transport h generator))

/-- [definition] **The descended face**: a receiver reading a future-agreement class. -/
def minimalFace (receiver : Receiver) : Quotient (futureSetoid observe transport) → Face :=
  Quotient.lift (observe receiver) (fun _ _ h => h receiver [])

/-- [definition] **The minimal standing**: retain the future-agreement class, and reopen an
admitted future by running the descended machine and reading the descended face. -/
def minimalStanding :
    StandingLaw Generator Receiver Source (Quotient (futureSetoid observe transport)) Face where
  transport := transport
  observe := observe
  retain := Quotient.mk (futureSetoid observe transport)
  reopen receiver word standing :=
    minimalFace observe transport receiver
      (transportWord (minimalMove observe transport) word standing)
  sufficient receiver word source :=
    (congrArg (minimalFace observe transport receiver)
      (generatorEquivarianceExtendsToEveryTransportWord transport (minimalMove observe transport)
        (Quotient.mk (futureSetoid observe transport)) (fun _ _ => rfl) word source)).symm

/-- [proved-standard; formal-checked] **The minimal standing is minimal.** -/
theorem minimalStanding_isMinimal : IsMinimal (minimalStanding observe transport) :=
  fun _ _ h => Quotient.sound h

end Abstract

/-! ## 2. Every depositing medium: the minimal retention is a class of the constitution -/

section Deposition

open Holonics.Objects.Deposition

variable {p q : ℕ} (L : DepositionLaw q) {d : Matrix (Fin q) (Fin p) ℚ}

/-- [proved-derived; formal-checked] **Two presents share their future exactly when their
constitutions do**, under the constitution-only machine, for every law, incidence and solver: the
flux record and the solver's gauge never enter. -/
theorem futureAgreement_iff_constitution (S : Solver d) (left right : DepositState q) :
    futureAgreement (observe S) (step L S) left right ↔
      futureAgreement (observeConstitution d) (stepConstitution L d) left.constitution
        right.constitution := by
  constructor
  · intro h σ word
    have hword := h σ word
    rwa [observe_eq_observeConstitution, observe_eq_observeConstitution,
      transportWord_constitution, transportWord_constitution] at hword
  · intro h σ word
    rw [observe_eq_observeConstitution, observe_eq_observeConstitution,
      transportWord_constitution, transportWord_constitution]
    exact h σ word

/-- [definition] **The minimal retention of a depositing medium**: the future-agreement class of
the constitution under the constitution-only machine. The retention does not mention the solver. -/
noncomputable def depositionMinimalStanding (S : Solver d) :
    StandingLaw (Fin p → ℚ) (Fin p → ℚ) (DepositState q)
      (Quotient (futureSetoid (observeConstitution d) (stepConstitution L d)))
      (Option (Fin q → ℚ)) where
  transport := step L S
  observe := observe S
  retain state := Quotient.mk _ state.constitution
  reopen := (minimalStanding (observeConstitution d) (stepConstitution L d)).reopen
  sufficient σ word state := by
    rw [observe_eq_observeConstitution, transportWord_constitution]
    exact (minimalStanding (observeConstitution d) (stepConstitution L d)).sufficient σ word
      state.constitution

/-- [proved-derived; formal-checked] **The class of the constitution is the minimal retention** of
every depositing medium. -/
theorem depositionMinimalStanding_isMinimal (S : Solver d) :
    IsMinimal (depositionMinimalStanding L S) :=
  fun left right h => Quotient.sound ((futureAgreement_iff_constitution L S left right).mp h)

/-- [proved-derived; formal-checked] **The constitution is minimal exactly when no two distinct
constitutions share a future.** -/
theorem constitutionStanding_isMinimal_iff (S : Solver d) :
    IsMinimal (constitutionStanding L S) ↔
      ∀ Θ Θ', futureAgreement (observeConstitution d) (stepConstitution L d) Θ Θ' → Θ = Θ' := by
  constructor
  · intro hL Θ Θ' h
    exact hL ⟨Θ, []⟩ ⟨Θ', []⟩ ((futureAgreement_iff_constitution L S ⟨Θ, []⟩ ⟨Θ', []⟩).mpr h)
  · intro h left right hagree
    exact h _ _ ((futureAgreement_iff_constitution L S left right).mp hagree)

/-- [counterexample; formal-checked] **The constitution suffices but is not minimal**: under the
square law on the parallel pair, for every solver. -/
theorem constitutionStanding_not_isMinimal (S : Solver parallel) :
    ¬ IsMinimal (constitutionStanding squareLaw S) := by
  intro hL
  obtain ⟨hne, hagree⟩ := constitution_is_not_minimal S [] []
  exact hne (hL _ _ hagree)

/-- [proved-derived; formal-checked] **`minimalRetain` is the parallel pair's minimal retention**:
the lawful standing that retains it is minimal. -/
theorem parallel_minimalRetain_isMinimal (S : Solver parallel) :
    ∃ L : StandingLaw (Fin 2 → ℚ) (Fin 2 → ℚ) (DepositState 2) (Option (Constitution 2))
        (Option (Fin 2 → ℚ)),
      L.transport = step squareLaw S ∧ L.observe = observe S ∧
        L.retain = Objects.Retention.minimalRetain ∧ IsMinimal L := by
  obtain ⟨L, htransport, hobserve, hretain⟩ := Objects.Retention.minimalStanding_exists S
  refine ⟨L, htransport, hobserve, hretain, fun left right h => ?_⟩
  rw [htransport, hobserve] at h
  rw [hretain]
  exact (Objects.Retention.minimalRetain_eq_iff_futureAgreement S left right).mpr h

end Deposition

/-! ## 3. The linear chart: the founded encoding is the minimal retention -/

section Linear

open Module
open Holonics.Compression.Landmark.Context.Birth
open Holonics.Foundation.SeparationDepth

variable {K X ι C κ : Type*} [Field K] [AddCommGroup X] [Module K X]

/-- [definition] The linear map a word of transports performs, the rightmost letter first. -/
def wordMap (T : ι → X →ₗ[K] X) : List ι → X →ₗ[K] X
  | [] => LinearMap.id
  | a :: word => T a ∘ₗ wordMap T word

theorem wordMap_apply (T : ι → X →ₗ[K] X) (word : List ι) (x : X) :
    wordMap T word x = transportWord (fun a x => T a x) word x := by
  induction word with
  | nil => rfl
  | cons a word ih =>
    show T a (wordMap T word x) = T a (transportWord (fun a x => T a x) word x)
    rw [ih]

theorem wordMap_append_single (T : ι → X →ₗ[K] X) (word : List ι) (a : ι) :
    wordMap T (word ++ [a]) = wordMap T word ∘ₗ T a := by
  ext x
  rw [LinearMap.comp_apply, wordMap_apply, wordMap_apply]
  exact transportWord_append (fun a x => T a x) word [a] x

/-- [definition] The forms that agree on two states. -/
def agreeingForms (left right : X) : Submodule K (Dual K X) :=
  LinearMap.ker (Module.Dual.eval K X (left - right))

theorem mem_agreeingForms {left right : X} {φ : Dual K X} :
    φ ∈ agreeingForms left right ↔ φ left = φ right := by
  rw [agreeingForms, LinearMap.mem_ker, Module.Dual.eval_apply, map_sub, sub_eq_zero]

variable [FiniteDimensional K X]

/-- A founded form read after any word of transports is founded. -/
theorem comp_wordMap_mem_founded (T : ι → X →ₗ[K] X) (V₀ : Submodule K (Dual K X))
    (word : List ι) {ψ : Dual K X} (hψ : ψ ∈ founded (fun a => (T a).dualMap) V₀) :
    ψ ∘ₗ wordMap T word ∈ founded (fun a => (T a).dualMap) V₀ := by
  induction word generalizing ψ with
  | nil => simpa [wordMap] using hψ
  | cons a word ih =>
    have ha : (T a).dualMap ψ ∈ founded (fun a => (T a).dualMap) V₀ :=
      founded_invariant (fun a => (T a).dualMap) V₀ a (Submodule.mem_map_of_mem hψ)
    have hword := ih ha
    rw [LinearMap.dualMap_apply', LinearMap.comp_assoc] at hword
    exact hword

/-- [proved-standard; formal-checked] **Birth's founded forms are the span of the transported
readings**: `founded = span {ρ ∘ T_w : ρ ∈ V₀, w a word}`. -/
theorem founded_eq_span_wordForms (T : ι → X →ₗ[K] X) (V₀ : Submodule K (Dual K X)) :
    founded (fun a => (T a).dualMap) V₀ =
      Submodule.span K {ψ | ∃ ρ ∈ V₀, ∃ word : List ι, ψ = ρ ∘ₗ wordMap T word} := by
  apply le_antisymm
  · apply founded_le
    · intro ρ hρ
      exact Submodule.subset_span ⟨ρ, hρ, [], (LinearMap.comp_id ρ).symm⟩
    · intro a
      rw [Submodule.map_span_le]
      rintro _ ⟨ρ, hρ, word, rfl⟩
      refine Submodule.subset_span ⟨ρ, hρ, word ++ [a], ?_⟩
      show (T a).dualMap (ρ ∘ₗ wordMap T word) = ρ ∘ₗ wordMap T (word ++ [a])
      rw [wordMap_append_single, LinearMap.dualMap_apply', LinearMap.comp_assoc]
  · rw [Submodule.span_le]
    rintro _ ⟨ρ, hρ, word, rfl⟩
    exact comp_wordMap_mem_founded T V₀ word (le_founded _ V₀ hρ)

/-- [proved-standard; formal-checked] **Future agreement is agreement of the founded forms**: two
states share every reading of every receiving form after every word exactly when every founded
form agrees on them. -/
theorem futureAgreement_iff_founded (T : ι → X →ₗ[K] X) (read : C → Dual K X)
    (left right : X) :
    futureAgreement (fun c x => read c x) (fun a x => T a x) left right ↔
      ∀ φ ∈ founded (fun a => (T a).dualMap) (Submodule.span K (Set.range read)),
        φ left = φ right := by
  constructor
  · intro h
    have hmem : ∀ φ : Dual K X,
        φ ∈ (⨅ word : List ι, agreeingForms (wordMap T word left) (wordMap T word right)) ↔
          ∀ word, φ (wordMap T word left) = φ (wordMap T word right) := by
      intro φ
      simp only [Submodule.mem_iInf, mem_agreeingForms]
    have hle : founded (fun a => (T a).dualMap) (Submodule.span K (Set.range read)) ≤
        ⨅ word : List ι, agreeingForms (wordMap T word left) (wordMap T word right) := by
      apply founded_le
      · rw [Submodule.span_le]
        rintro _ ⟨c, rfl⟩
        rw [SetLike.mem_coe, hmem]
        intro word
        rw [wordMap_apply, wordMap_apply]
        exact h c word
      · intro a φ hφ
        obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.mp hφ
        rw [hmem] at hψ ⊢
        intro word
        exact hψ (a :: word)
    intro φ hφ
    exact (hmem φ).mp (hle hφ) []
  · intro h c word
    have hmem := comp_wordMap_mem_founded T (Submodule.span K (Set.range read)) word
      (le_founded (fun a => (T a).dualMap) (Submodule.span K (Set.range read))
        (Submodule.subset_span ⟨c, rfl⟩))
    have hagree := h _ hmem
    simpa only [LinearMap.comp_apply, wordMap_apply] using hagree

/-- [proved-standard; formal-checked] **The founded encoding separates exactly what the future
separates** (Kalman's observability quotient): on any basis `φ_i` of the founded forms,
`E x = E y` exactly when `x` and `y` share their future. -/
theorem encode_eq_iff_futureAgreement [Fintype κ] (T : ι → X →ₗ[K] X) (read : C → Dual K X)
    (b : Basis κ K (founded (fun a => (T a).dualMap) (Submodule.span K (Set.range read))))
    (left right : X) :
    encode (fun i => (b i : Dual K X)) left = encode (fun i => (b i : Dual K X)) right ↔
      futureAgreement (fun c x => read c x) (fun a x => T a x) left right := by
  rw [futureAgreement_iff_founded]
  constructor
  · intro h φ hφ
    have hle : Submodule.span K (Set.range b) ≤ (agreeingForms left right).comap
        (founded (fun a => (T a).dualMap) (Submodule.span K (Set.range read))).subtype := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.subtype_apply, mem_agreeingForms]
      exact congrFun h i
    have htop : (⟨φ, hφ⟩ : founded (fun a => (T a).dualMap) (Submodule.span K (Set.range read)))
        ∈ Submodule.span K (Set.range b) := by
      rw [b.span_eq]
      exact Submodule.mem_top
    have hφ' := hle htop
    rwa [Submodule.mem_comap, Submodule.subtype_apply, mem_agreeingForms] at hφ'
  · intro h
    funext i
    exact h _ (b i).2

/-- [proved-standard; formal-checked] **The founded encoding is a minimal standing**: it carries a
lawful `StandingLaw` for the linear medium, and that standing is minimal. -/
theorem founded_encoding_isMinimal [Fintype κ] (T : ι → X →ₗ[K] X) (read : C → Dual K X)
    (b : Basis κ K (founded (fun a => (T a).dualMap) (Submodule.span K (Set.range read)))) :
    ∃ L : StandingLaw ι C X (κ → K) K,
      L.transport = (fun a x => T a x) ∧ L.observe = (fun c x => read c x) ∧
        L.retain = encode (fun i => (b i : Dual K X)) ∧ IsMinimal L := by
  obtain ⟨L, htransport, hobserve, hretain⟩ :=
    (standingLaw_exists_iff_future_factors (fun c x => read c x) (fun a x => T a x)
      (encode (fun i => (b i : Dual K X)))).mpr fun left right h =>
        (causalSignature_eq_iff_futureAgreement _ _ _ _).mpr
          ((encode_eq_iff_futureAgreement T read b left right).mp h)
  refine ⟨L, htransport, hobserve, hretain, fun left right h => ?_⟩
  rw [htransport, hobserve] at h
  rw [hretain]
  exact (encode_eq_iff_futureAgreement T read b left right).mpr h

omit [FiniteDimensional K X] in
/-- Agreement on every word of at most `n` moves makes every form of the `n`-th rung agree. -/
theorem ladder_le_agreeingForms (T : ι → X →ₗ[K] X) (read : C → Dual K X) (n : ℕ)
    (left right : X)
    (h : agreeUpTo (fun c x => read c x) (fun a x => T a x) n left right) :
    ladder (fun a => (T a).dualMap) (Submodule.span K (Set.range read)) n ≤
      agreeingForms left right := by
  induction n generalizing left right with
  | zero =>
    rw [ladder_zero, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, mem_agreeingForms]
    exact h c [] (Nat.zero_le _)
  | succ n ih =>
    rw [ladder_succ, closeStep]
    refine sup_le (ih left right (agreeUpTo_mono _ _ (Nat.le_succ n) h)) (iSup_le fun a => ?_)
    rw [Submodule.map_le_iff_le_comap]
    intro φ hφ
    rw [Submodule.mem_comap, mem_agreeingForms, LinearMap.dualMap_apply,
      LinearMap.dualMap_apply]
    have hih := mem_agreeingForms.mp
      (ih _ _ (agreeUpTo_transport (fun c x => read c x) (fun a x => T a x) [a] h) hφ)
    simpa only [transportWord_cons, transportWord_nil] using hih

/-- [proved-standard; formal-checked] **The linear depth bound**: two states share their future
exactly when they agree on every word of at most `dim X − dim span{ρ_c}` moves, the dimension the
receiving forms leave unread. -/
theorem futureAgreement_iff_agreeUpTo_finrank (T : ι → X →ₗ[K] X) (read : C → Dual K X)
    (left right : X) :
    futureAgreement (fun c x => read c x) (fun a x => T a x) left right ↔
      agreeUpTo (fun c x => read c x) (fun a x => T a x)
        (finrank K X - finrank K (Submodule.span K (Set.range read))) left right := by
  refine ⟨fun h => (futureAgreement_iff_forall_agreeUpTo _ _ left right).mp h _, fun h => ?_⟩
  obtain ⟨n, hn, hstable⟩ :=
    ladder_stabilizes (fun a => (T a).dualMap) (Submodule.span K (Set.range read))
  rw [Subspace.dual_finrank_eq] at hn
  have hrung : founded (fun a => (T a).dualMap) (Submodule.span K (Set.range read)) ≤
      ladder (fun a => (T a).dualMap) (Submodule.span K (Set.range read)) n :=
    founded_le _ _ (ladder_mono _ _ (Nat.zero_le n))
      (invariant_of_stable _ (V := ladder (fun a => (T a).dualMap)
        (Submodule.span K (Set.range read)) n) hstable)
  rw [futureAgreement_iff_founded]
  intro φ hφ
  exact mem_agreeingForms.mp (ladder_le_agreeingForms T read n left right
    (agreeUpTo_mono _ _ (by omega) h) (hrung hφ))

end Linear

end Holonics.Foundation.MinimalRetention
