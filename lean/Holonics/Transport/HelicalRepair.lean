import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Forall2
import Mathlib.Data.NNRat.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# The repair family: its carried support and the diameter equation of its class

[definition] This module states the two laws that the first native consumer of the helical code,
`compression::keys::duplex` (`crates/holonics/src/compression/keys/duplex.rs`, accepted at
`02658c6c2`; receipt
`research/records/receipts/2026-10-09-helical-duplex/native-v2/HANDOFF.md`), owes to #62: the exact
carried support of the independent repair family together with its size bound, and the equation
that the diameter of the family's class is the maximum over the class's coordinates of each
coordinate's diameter read on its support. The record is
`research/records/2026-10-08_THE_HELICAL_CODE_IS_HOW_HOLONS_HOLARCHIES_EPOCHS_AND_AEONS_ENCODE.md`,
§5 item 4 ("The repair family, exact and carried", "Release"). The native owners are
`Decoder::support` (the supports `X_0, …, X_n`), `Decoder::coordinate` (one coordinate of the
class across the supported alternatives), `Decoder::member` (an actual member through a supported
state) and `Decoder::decode` (the maximum over the coordinates, committed at tolerance zero). This
module is a statement of an object, not a decoder: the alphabet, the advances, the readings and the
distances are arbitrary, and nothing here reads, parses or classifies a particular language.

[definition] **The object.** An alphabet `α` with advances `A : α → ℕ`, an opening lift `x₀ : ℕ`, and
a list of finite factors `F = [F_0, …, F_(n−1)]`, `F_j` the letters admitted at position `j`.
- A *member* is a word `w` with `|w| = n` and `w_j ∈ F_j` for every `j` (`IsMember F w`, a
  `List.Forall₂`; `isMember_iff_getElem` states the pointwise reading). The *family* is the set of
  members (`members F`, of size `∏_j |F_j|`, `card_members`).
- Along a word the helix carries the unreduced lift `ℓ_k = x₀ + Σ_(j<k) A(w_j)` (`prefixLift`). Its
  phase `ℓ mod D` and its whole winding `ℓ div D` are readings of this one integer; the quotient is
  taken only by a reading `r`, after the support is formed.
- The *carried support* is `X_0 = {x₀}`, `X_(k+1) = {x + A(a) : x ∈ X_k, a ∈ F_k}` (`reach`,
  `reach_zero`, `reach_succ`), kept at full carried positions, never reduced modulo `D`.

[proved-derived; formal-checked] **Part one, the carried support** (§§3–4), each with its
hypotheses.
- *Support exactness* (`mem_reach_iff`, `reach_eq_image_members`, `exists_member_through`), for
  every factor nonempty (`hne`) and `k ≤ n`: the lifts at position `k` of the members are exactly
  `X_k`. Every supported state therefore extends to an actual member (the law behind
  `Decoder::member`), and the member readings at position `k` are exactly the reading of the
  support (`readings_eq_image_reach`). Nonemptiness is used and necessary: for `F = [{a, b}, ∅]`
  there is no member, while `X_1 = {x₀ + A a, x₀ + A b}`.
- *The bound*, for every `k` and with no hypothesis on the factors (`card_reach_le_prod`):
  `|X_k| ≤ ∏_(j<k) |F_j|`, and `|X_n|` is at most the number of members
  (`card_reach_le_card_members`). If moreover `A a < D` for every letter (`reach_subset_Icc`,
  `card_reach_le`), every step moves a lift by at most `D − 1`, so `X_k ⊆ [x₀, x₀ + k(D − 1)]` and
  `|X_k| ≤ k(D − 1) + 1`; together (`card_reach_le_min`) `|X_k| ≤ min(∏_(j<k) |F_j|, k(D − 1) + 1)`
  whatever the number of slipped contacts. No `D ≥ 1` hypothesis is needed: a letter with `A a < D`
  forces it, and with no letters every factor is empty, so `X_k = ∅` for `k ≥ 1`.

[proved-derived; formal-checked] **Part two, the diameter equation** (§§5–7). A *distance* takes
values in a join-semilattice with bottom `R`; `ℚ≥0` is the exact instance (`⊥ = 0`, nonnegativity is
the type), and `ℕ` is another. The diameter of a finite family `S` under `δ` is the iterated
supremum of `δ` over ordered pairs (`diam`; the empty family has diameter `⊥`). A class has
coordinates `i ∈ I` (a finite set), each with a level `lev i ≤ n` (the position whose lift it
reads), a reading `r i : ℕ → Y i` of the lift and a distance `d i` on `Y i`; the tuple distance is
the maximum over the coordinates (`tupleDist`), the supremum norm.
- (a) *No pooling* (`diam_tuple_eq_max`), for any finite family and any finite coordinate set, with
  no hypothesis on `d`: the diameter of the class tuples is the maximum over the coordinates of the
  per-coordinate diameters of the member readings. This is two suprema commuted.
- (b) *Through the support* (`diam_tuple_eq_max_support`, then `diam_family_eq_max_support`): if the
  state a coordinate reads maps the family onto a finite set `T i` (the support), the family's
  diameter is the maximum over the coordinates of the diameter of `r i` on `T i`. For the
  independent family `members F`, with every factor nonempty and `lev i ≤ n`, the support is
  `reach x₀ A F (lev i)` by part one, so the diameter is computed on the carried supports without
  enumerating the `∏ |F_j|` members. The decoder's tuple, positions `0..=n` and the terminal carry
  coordinate `n + 1` reading the terminal lift, is the instance `lev i = min i n` on
  `Finset.range (n + 2)` (`diam_class_eq_max_support`).
- (c) *Release* (`diam_family_eq_bot_iff`, `diam_class_eq_bot_iff`, and over `ℚ≥0` with `0`:
  `diam_family_eq_zero_iff`), given `d i v v = ⊥` and `d i v w = ⊥ → v = w`: the diameter is `⊥`
  exactly when every coordinate's reading is constant on its support (at most one value). The
  decoder additionally requires the family to be nonempty (`exists_member`).

[agent-inferred] The choices, with their reasons.
- `diam` is the iterated `Finset.sup` into a semilattice with bottom, not `Finset.sup'` over `ℚ`:
  there are no nonemptiness side conditions in (a) and (b), and `ℚ≥0` makes nonnegativity a property
  of the type. The decoder's own nonempty-family test is not repeated.
- `reach` peels the first factor (`reachFrom`, with a set of openings): this is the recursion the
  induction of §3 needs, and `reach_succ` is the consumer's own recursion
  `X_(k+1) = {x + A(a) : x ∈ X_k, a ∈ F_k}` for `k < n`. Past the last factor the support is empty,
  since no word has a position there; this makes the bounds unconditional in `k`, and support
  exactness is stated for `k ≤ n`.
- Coordinates carry a level, so the decoder's `n + 2` coordinates and any other reading of
  prefix lifts are one statement.

[open] Not claimed here, with what each needs.
- **Fit-constrained (coupled) families** (`Fit::Transport`). Fitting keeps a transition from `x` by
  `a` only when the transport emits `a` at `x`; the family is then not the product `∏ F_j`, and the
  supports need a backward pass that keeps the states extending to a complete member. `reach` is a
  forward pass without the guard and is not their support. What this module supplies for them is
  (b) at its source, `diam_tuple_eq_max_support`: it holds for any finite family whose supports are
  exact (`hmaps`, `hsurj`). What is owed (#62) is that exactness for the pruned supports.
- **Channel coverage**: that the truth is a member of the family, that release returns the truth's
  class, and the absorbed and residual counts of coordinated substitutions. Here the family is any
  product of finite factors, and its relation to a damaged duplex is not stated.
- **A receiver quotient**: the readings `r i` and distances `d i` are arbitrary. The founding of `E`,
  its kernel, the absorption law and the width owner's coherence checks are not constructed.
- **Witnesses**: that a nonconstant family has two actual members attaining the diameter with
  differing classes (`Decoder::decode`, held). It needs a linear order on the distances and
  `Finset.exists_mem_eq_sup` on the two suprema; `exists_member_through` supplies the extension.
- **Work and memory** (`Σ_(k<n) |X_k||F_k|` transitions) and the machine word (`u64` lifts and the
  refusal on overflow): `ℕ` is unbounded here.

Written without a compiler: the `formal-checked` tag on each statement stands once the validation
queue's kernel receipt exists.

[established-bounded; formal-checked] Scope: finite lists, finite sets of naturals, finite suprema
in a join-semilattice with bottom. No float, no tape or journal, no `axiom`, no `sorry`, no
`native_decide`.
-/

namespace Holonics.Transport.HelicalRepair

variable {α : Type*}

/-! ## 1. The family: one admitted letter at each position -/

/-- [definition] A member of the factor list `F = [F_0, …, F_(n−1)]`: a word `w` of length `n` whose
letter at position `j` is admitted by `F_j`. The encoding is `List.Forall₂ (· ∈ ·) w F`;
`isMember_iff_getElem` is the pointwise reading, `|w| = |F|` and `w_j ∈ F_j`. -/
def IsMember (F : List (Finset α)) (w : List α) : Prop :=
  List.Forall₂ (fun (a : α) (s : Finset α) => a ∈ s) w F

/-- [proved-derived; formal-checked] Nothing is a member of the empty factor list but the empty
word. -/
theorem isMember_nil (w : List α) : IsMember ([] : List (Finset α)) w ↔ w = [] := by
  first
    | exact List.forall₂_nil_right_iff
    | (unfold IsMember; exact List.forall₂_nil_right_iff)

/-- [proved-derived; formal-checked] A member of `s :: F` is a letter of `s` followed by a member of
`F`. -/
theorem isMember_cons {s : Finset α} {F : List (Finset α)} {w : List α} :
    IsMember (s :: F) w ↔ ∃ a u, a ∈ s ∧ IsMember F u ∧ w = a :: u := by
  first
    | exact List.forall₂_cons_right_iff
    | (unfold IsMember; exact List.forall₂_cons_right_iff)

/-- [proved-derived; formal-checked] A member has one letter for each factor. -/
theorem isMember_length {F : List (Finset α)} {w : List α} (h : IsMember F w) :
    w.length = F.length :=
  List.Forall₂.length_eq h

/-- [proved-derived; formal-checked] **The encoding is the pointwise reading**: a word is a member
exactly when it has one letter for each factor and its letter at position `j` is admitted by
`F_j`. -/
theorem isMember_iff_getElem {F : List (Finset α)} {w : List α} :
    IsMember F w ↔
      w.length = F.length ∧ ∀ (j : ℕ) (h1 : j < w.length) (h2 : j < F.length), w[j] ∈ F[j] := by
  constructor
  · intro h
    exact ⟨List.Forall₂.length_eq h, fun j h1 h2 => List.Forall₂.get h h1 h2⟩
  · rintro ⟨hl, h⟩
    exact List.forall₂_of_length_eq_of_get hl (fun j h1 h2 => h j h1 h2)

/-- [proved-derived; formal-checked] **A family with every factor nonempty has a member.** -/
theorem exists_member :
    ∀ F : List (Finset α), (∀ s ∈ F, s.Nonempty) → ∃ w, IsMember F w
  | [], _ => ⟨[], (isMember_nil []).mpr rfl⟩
  | s :: F, h => by
    obtain ⟨a, ha⟩ := h s (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨w, hw⟩ := exists_member F (fun t ht => h t (List.mem_cons.mpr (Or.inr ht)))
    exact ⟨a :: w, isMember_cons.mpr ⟨a, w, ha, hw, rfl⟩⟩

/-- [definition] The cons embedding `(a, u) ↦ a :: u`: a letter and a word determine the word they
make, and conversely. -/
def consEmb : α × List α ↪ List α :=
  ⟨fun p => p.1 :: p.2, by
    rintro ⟨a, u⟩ ⟨b, v⟩ h
    first
      | (simp only [List.cons.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
      | (injection h with h1 h2; subst h1; subst h2; rfl)⟩

/-- [definition] The family of the factor list as a finite set of words: the product of the factors,
built by choosing the first letter and then a member of the rest. `mem_members` states that it is
the set of members, and `card_members` that it has `∏_j |F_j|` of them. -/
def members : List (Finset α) → Finset (List α)
  | [] => {[]}
  | s :: F => (s ×ˢ members F).map consEmb

theorem members_nil : members ([] : List (Finset α)) = {[]} := by
  first
    | rfl
    | simp [members]

theorem members_cons (s : Finset α) (F : List (Finset α)) :
    members (s :: F) = (s ×ˢ members F).map consEmb := by
  first
    | rfl
    | simp [members]

/-- [proved-derived; formal-checked] **The finite family is the set of members.** -/
theorem mem_members : ∀ (F : List (Finset α)) (w : List α), w ∈ members F ↔ IsMember F w
  | [], w => by
    rw [members_nil, Finset.mem_singleton]
    exact (isMember_nil w).symm
  | s :: F, w => by
    rw [members_cons, Finset.mem_map]
    constructor
    · rintro ⟨⟨a, u⟩, hp, rfl⟩
      rw [Finset.mem_product] at hp
      exact isMember_cons.mpr ⟨a, u, hp.1, (mem_members F u).mp hp.2, rfl⟩
    · intro h
      obtain ⟨a, u, ha, hu, rfl⟩ := isMember_cons.mp h
      exact ⟨(a, u), Finset.mem_product.mpr ⟨ha, (mem_members F u).mpr hu⟩, rfl⟩

/-- [proved-derived; formal-checked] **The member count is the product of the factor sizes**,
`|members F| = ∏_j |F_j|`. -/
theorem card_members :
    ∀ F : List (Finset α), (members F).card = (F.map Finset.card).prod
  | [] => by
    rw [members_nil]
    simp
  | s :: F => by
    rw [members_cons, Finset.card_map, Finset.card_product, card_members F, List.map_cons,
      List.prod_cons]

/-! ## 2. The carried lift of a word -/

/-- [definition] The lift after `k` letters of the word `w` from the opening `x₀`:
`ℓ_k = x₀ + Σ_(j<k) A(w_j)`, an unreduced natural number (a phase and a whole winding together). For
`k` beyond the length of `w` it is the total. -/
def prefixLift (x₀ : ℕ) (A : α → ℕ) (w : List α) (k : ℕ) : ℕ :=
  x₀ + ((w.take k).map A).sum

/-- [proved-derived; formal-checked] No letter has been read at position zero. -/
theorem prefixLift_zero (x₀ : ℕ) (A : α → ℕ) (w : List α) : prefixLift x₀ A w 0 = x₀ := by
  simp [prefixLift]

/-- [proved-derived; formal-checked] **Peeling the first letter moves the opening**: the lift after
`k + 1` letters of `a :: w` from `x` is the lift after `k` letters of `w` from `x + A a`. -/
theorem prefixLift_cons_succ (x : ℕ) (A : α → ℕ) (a : α) (w : List α) (k : ℕ) :
    prefixLift x A (a :: w) (k + 1) = prefixLift (x + A a) A w k := by
  unfold prefixLift
  rw [List.take_succ_cons, List.map_cons, List.sum_cons]
  omega

/-! ## 3. The carried support is exactly the set of lifts of the members -/

/-- [definition] One transition of the carried support: from the set `X` of lifts, every admitted
letter `a ∈ s` advances every lift `x ∈ X` to `x + A a`. -/
def advanceBy (A : α → ℕ) (s : Finset α) (X : Finset ℕ) : Finset ℕ :=
  X.biUnion fun x => s.image fun a => x + A a

/-- [proved-derived; formal-checked] Membership in a transition. -/
theorem mem_advanceBy (A : α → ℕ) (s : Finset α) (X : Finset ℕ) (y : ℕ) :
    y ∈ advanceBy A s X ↔ ∃ x ∈ X, ∃ a ∈ s, x + A a = y := by
  unfold advanceBy
  first
    | (simp only [Finset.mem_biUnion, Finset.mem_image]; done)
    | simp

/-- [definition; agent-inferred] The carried support after `k` letters, from a set `X` of openings
and through the factors `F`: peel the first factor, advance by it, and continue (`reachFrom_zero`,
`reachFrom_cons_succ`). Past the last factor the support is empty (`reachFrom_nil_succ`): no word
has a position there. A set of openings is the generality the induction of
`mem_reachFrom_iff` needs; `reach` is the single opening. -/
def reachFrom (A : α → ℕ) : List (Finset α) → Finset ℕ → ℕ → Finset ℕ
  | [], X, 0 => X
  | [], _, _ + 1 => ∅
  | _ :: _, X, 0 => X
  | s :: F, X, k + 1 => reachFrom A F (advanceBy A s X) k

theorem reachFrom_zero (A : α → ℕ) (F : List (Finset α)) (X : Finset ℕ) :
    reachFrom A F X 0 = X := by
  first
    | (cases F <;> rfl)
    | (cases F <;> simp [reachFrom])

theorem reachFrom_nil_succ (A : α → ℕ) (X : Finset ℕ) (k : ℕ) :
    reachFrom A ([] : List (Finset α)) X (k + 1) = ∅ := by
  first
    | rfl
    | simp [reachFrom]

theorem reachFrom_cons_succ (A : α → ℕ) (s : Finset α) (F : List (Finset α)) (X : Finset ℕ)
    (k : ℕ) : reachFrom A (s :: F) X (k + 1) = reachFrom A F (advanceBy A s X) k := by
  first
    | rfl
    | simp [reachFrom]

/-- [definition] **The carried support** `X_k` of the repair family: `X_0 = {x₀}` and
`X_(k+1) = {x + A a : x ∈ X_k, a ∈ F_k}` (`reach_zero`, `reach_succ`). The lifts are absolute,
never reduced modulo the period. -/
def reach (x₀ : ℕ) (A : α → ℕ) (F : List (Finset α)) (k : ℕ) : Finset ℕ :=
  reachFrom A F {x₀} k

/-- [proved-derived; formal-checked] The support before any letter is the opening. -/
theorem reach_zero (x₀ : ℕ) (A : α → ℕ) (F : List (Finset α)) : reach x₀ A F 0 = {x₀} :=
  reachFrom_zero A F {x₀}

/-- [proved-derived; formal-checked] **The recursion of the consumer**: for `k < n`,
`X_(k+1) = {x + A a : x ∈ X_k, a ∈ F_k}` (`advanceBy` is the stated biUnion of images). This is
`Decoder::support`'s forward step, and the definition `reachFrom` agrees with it at every position
that has a factor. -/
theorem reachFrom_succ (A : α → ℕ) (F : List (Finset α)) :
    ∀ (X : Finset ℕ) (k : ℕ) (hk : k < F.length),
      reachFrom A F X (k + 1) = advanceBy A (F[k]'hk) (reachFrom A F X k) := by
  induction F with
  | nil =>
    intro X k hk
    first
      | exact absurd hk (by simp)
      | exact absurd hk (Nat.not_lt_zero k)
  | cons s F ih =>
    intro X k hk
    cases k with
    | zero =>
      first
        | (simp only [reachFrom_cons_succ, reachFrom_zero]; rfl)
        | simp [reachFrom_cons_succ, reachFrom_zero]
    | succ k =>
      have hk' : k < F.length := by
        first
          | exact Nat.lt_of_succ_lt_succ hk
          | simpa using hk
      rw [reachFrom_cons_succ, reachFrom_cons_succ, ih (advanceBy A s X) k hk']
      try (first | rfl | simp)

/-- [proved-derived; formal-checked] **The consumer's recursion, stated on the single opening**: for
`k < n`, `X_(k+1) = ⋃_(x ∈ X_k) {x + A a : a ∈ F_k}`. -/
theorem reach_succ (x₀ : ℕ) (A : α → ℕ) (F : List (Finset α)) {k : ℕ} (hk : k < F.length) :
    reach x₀ A F (k + 1) = (reach x₀ A F k).biUnion fun x => (F[k]'hk).image fun a => x + A a :=
  reachFrom_succ A F {x₀} k hk

/-- [proved-derived; formal-checked] **Support exactness, from a set of openings.** If every factor
is nonempty, then for `k ≤ n` a number `y` is in the carried support after `k` letters exactly when
some opening `x ∈ X` and some member `w` of `F` give `y` as the lift after `k` letters of `w` from
`x`. -/
theorem mem_reachFrom_iff (A : α → ℕ) :
    ∀ (F : List (Finset α)), (∀ s ∈ F, s.Nonempty) → ∀ (X : Finset ℕ) (k : ℕ),
      k ≤ F.length → ∀ y : ℕ,
        y ∈ reachFrom A F X k ↔ ∃ x ∈ X, ∃ w : List α, IsMember F w ∧ prefixLift x A w k = y := by
  intro F
  induction F with
  | nil =>
    intro _ X k hk y
    have hk0 : k = 0 := by
      have h0 : k ≤ 0 := hk
      omega
    subst hk0
    rw [reachFrom_zero]
    constructor
    · intro hy
      exact ⟨y, hy, [], (isMember_nil []).mpr rfl, prefixLift_zero y A []⟩
    · rintro ⟨x, hx, w, hw, rfl⟩
      rw [prefixLift_zero]
      exact hx
  | cons s F ih =>
    intro hne X k hk y
    have hneF : ∀ t ∈ F, t.Nonempty := fun t ht => hne t (List.mem_cons.mpr (Or.inr ht))
    cases k with
    | zero =>
      have hs : s.Nonempty := hne s (List.mem_cons.mpr (Or.inl rfl))
      rw [reachFrom_zero]
      constructor
      · intro hy
        obtain ⟨w, hw⟩ := exists_member F hneF
        obtain ⟨a, ha⟩ := hs
        exact ⟨y, hy, a :: w, isMember_cons.mpr ⟨a, w, ha, hw, rfl⟩, prefixLift_zero y A (a :: w)⟩
      · rintro ⟨x, hx, w, hw, rfl⟩
        rw [prefixLift_zero]
        exact hx
    | succ k =>
      have hk' : k ≤ F.length := by
        first
          | exact Nat.le_of_succ_le_succ hk
          | simpa using hk
      rw [reachFrom_cons_succ, ih hneF (advanceBy A s X) k hk' y]
      constructor
      · rintro ⟨x', hx', w, hw, rfl⟩
        obtain ⟨x, hx, a, ha, rfl⟩ := (mem_advanceBy A s X x').mp hx'
        exact ⟨x, hx, a :: w, isMember_cons.mpr ⟨a, w, ha, hw, rfl⟩,
          prefixLift_cons_succ x A a w k⟩
      · rintro ⟨x, hx, w, hw, rfl⟩
        obtain ⟨a, u, ha, hu, rfl⟩ := isMember_cons.mp hw
        exact ⟨x + A a, (mem_advanceBy A s X (x + A a)).mpr ⟨x, hx, a, ha, rfl⟩, u, hu,
          (prefixLift_cons_succ x A a u k).symm⟩

/-- [proved-derived; formal-checked] **Support exactness, pointwise.** If every factor is nonempty
and `k ≤ n`, a lift `y` is in the carried support `X_k` exactly when it is the lift after `k`
letters of some member of the family. -/
theorem mem_reach_iff (x₀ : ℕ) (A : α → ℕ) (F : List (Finset α)) (hne : ∀ s ∈ F, s.Nonempty)
    {k : ℕ} (hk : k ≤ F.length) (y : ℕ) :
    y ∈ reach x₀ A F k ↔ ∃ w, IsMember F w ∧ prefixLift x₀ A w k = y := by
  show y ∈ reachFrom A F {x₀} k ↔ _
  rw [mem_reachFrom_iff A F hne {x₀} k hk y]
  constructor
  · rintro ⟨x, hx, w, hw, rfl⟩
    rw [Finset.mem_singleton] at hx
    subst hx
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨x₀, Finset.mem_singleton_self x₀, w, hw, rfl⟩

/-- [proved-derived; formal-checked] **Support exactness** (the set form): if every factor is
nonempty and `k ≤ n`, the lifts at position `k` of the members of the family are exactly the
carried support, `{ℓ_k(w) : w a member} = X_k`. -/
theorem reach_eq_image_members (x₀ : ℕ) (A : α → ℕ) (F : List (Finset α))
    (hne : ∀ s ∈ F, s.Nonempty) {k : ℕ} (hk : k ≤ F.length) :
    ((reach x₀ A F k : Finset ℕ) : Set ℕ)
      = (fun w => prefixLift x₀ A w k) '' {w : List α | IsMember F w} := by
  ext y
  constructor
  · intro hy
    obtain ⟨w, hw, rfl⟩ := (mem_reach_iff x₀ A F hne hk y).mp (Finset.mem_coe.mp hy)
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact Finset.mem_coe.mpr ((mem_reach_iff x₀ A F hne hk _).mpr ⟨w, hw, rfl⟩)

/-- [proved-derived; formal-checked] **Every supported state extends to an actual member.** If every
factor is nonempty, `k ≤ n` and `y ∈ X_k`, some member `w` of the family has lift `y` after `k`
letters. This is the law behind `Decoder::member`. -/
theorem exists_member_through (x₀ : ℕ) (A : α → ℕ) (F : List (Finset α))
    (hne : ∀ s ∈ F, s.Nonempty) {k : ℕ} (hk : k ≤ F.length) {y : ℕ} (hy : y ∈ reach x₀ A F k) :
    ∃ w, IsMember F w ∧ prefixLift x₀ A w k = y :=
  (mem_reach_iff x₀ A F hne hk y).mp hy

/-- [proved-derived; formal-checked] **The member readings at position `k` are the reading of the
support.** For a reading `r` of lifts, if every factor is nonempty and `k ≤ n`, the set of
`r (ℓ_k(w))` over the members `w` is the image `r '' X_k`. -/
theorem readings_eq_image_reach {V : Type*} (x₀ : ℕ) (A : α → ℕ) (F : List (Finset α))
    (hne : ∀ s ∈ F, s.Nonempty) {k : ℕ} (hk : k ≤ F.length) (r : ℕ → V) :
    (fun w => r (prefixLift x₀ A w k)) '' {w : List α | IsMember F w}
      = r '' ((reach x₀ A F k : Finset ℕ) : Set ℕ) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨prefixLift x₀ A w k,
      Finset.mem_coe.mpr ((mem_reach_iff x₀ A F hne hk _).mpr ⟨w, hw, rfl⟩), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨w, hw, rfl⟩ := (mem_reach_iff x₀ A F hne hk x).mp (Finset.mem_coe.mp hx)
    exact ⟨w, hw, rfl⟩

/-! ## 4. The size of the carried support -/

/-- [proved-derived; formal-checked] A transition has at most as many results as there are pairs of a
lift and an admitted letter. -/
theorem card_advanceBy_le (A : α → ℕ) (s : Finset α) (X : Finset ℕ) :
    (advanceBy A s X).card ≤ X.card * s.card := by
  unfold advanceBy
  refine Finset.card_biUnion_le_card_mul X _ s.card (fun x _ => ?_)
  exact Finset.card_image_le

/-- [definition] `∏_(j<k) |F_j|`: the number of ways to choose a letter at each of the first `k`
positions. -/
def choiceCount (F : List (Finset α)) (k : ℕ) : ℕ :=
  ((F.take k).map Finset.card).prod

/-- [proved-derived; formal-checked] The count through every position is the member count. -/
theorem choiceCount_length (F : List (Finset α)) :
    choiceCount F F.length = (F.map Finset.card).prod := by
  unfold choiceCount
  rw [List.take_length]

/-- [proved-derived; formal-checked] **The product bound, from a set of openings**: for every list of
factors, every set of openings and every `k`, `|reachFrom F X k| ≤ |X| · ∏_(j<k) |F_j|`. No
hypothesis on the factors. -/
theorem card_reachFrom_le (A : α → ℕ) :
    ∀ (F : List (Finset α)) (X : Finset ℕ) (k : ℕ),
      (reachFrom A F X k).card ≤ X.card * ((F.take k).map Finset.card).prod := by
  intro F
  induction F with
  | nil =>
    intro X k
    cases k with
    | zero =>
      rw [reachFrom_zero]
      simp
    | succ k =>
      rw [reachFrom_nil_succ]
      first
        | exact Nat.zero_le _
        | simp
  | cons s F ih =>
    intro X k
    cases k with
    | zero =>
      rw [reachFrom_zero]
      simp
    | succ k =>
      rw [reachFrom_cons_succ, List.take_succ_cons, List.map_cons, List.prod_cons]
      calc (reachFrom A F (advanceBy A s X) k).card
          ≤ (advanceBy A s X).card * ((F.take k).map Finset.card).prod := ih _ k
        _ ≤ (X.card * s.card) * ((F.take k).map Finset.card).prod :=
            Nat.mul_le_mul_right _ (card_advanceBy_le A s X)
        _ = X.card * (s.card * ((F.take k).map Finset.card).prod) := Nat.mul_assoc _ _ _

/-- [proved-derived; formal-checked] **The product bound**: for every `k` and with no hypothesis on
the factors, `|X_k| ≤ ∏_(j<k) |F_j|`. -/
theorem card_reach_le_prod (x₀ : ℕ) (A : α → ℕ) (F : List (Finset α)) (k : ℕ) :
    (reach x₀ A F k).card ≤ choiceCount F k := by
  have h := card_reachFrom_le A F {x₀} k
  rw [Finset.card_singleton, Nat.one_mul] at h
  exact h

/-- [proved-derived; formal-checked] **The terminal support has at most as many states as the family
has members**, `|X_n| ≤ ∏_j |F_j| = |members F|`. No hypothesis on the factors. -/
theorem card_reach_le_card_members (x₀ : ℕ) (A : α → ℕ) (F : List (Finset α)) :
    (reach x₀ A F F.length).card ≤ (members F).card := by
  rw [card_members, ← choiceCount_length]
  exact card_reach_le_prod x₀ A F F.length

/-- [proved-derived; formal-checked] **Each step moves a lift by at most `E`**: if `A a ≤ E` for
every letter, every lift of the support after `k` letters from an opening in `[lo, hi]` lies in
`[lo, hi + kE]`. -/
theorem reachFrom_bounds (A : α → ℕ) (E lo : ℕ) (hA : ∀ a, A a ≤ E) :
    ∀ (F : List (Finset α)) (X : Finset ℕ) (hi : ℕ), (∀ x ∈ X, lo ≤ x ∧ x ≤ hi) →
      ∀ (k y : ℕ), y ∈ reachFrom A F X k → lo ≤ y ∧ y ≤ hi + k * E := by
  intro F
  induction F with
  | nil =>
    intro X hi hX k y hy
    cases k with
    | zero =>
      rw [reachFrom_zero] at hy
      have h := hX y hy
      omega
    | succ k =>
      rw [reachFrom_nil_succ] at hy
      first
        | exact absurd hy (Finset.notMem_empty y)
        | simp at hy
  | cons s F ih =>
    intro X hi hX k y hy
    cases k with
    | zero =>
      rw [reachFrom_zero] at hy
      have h := hX y hy
      omega
    | succ k =>
      rw [reachFrom_cons_succ] at hy
      have hX' : ∀ x ∈ advanceBy A s X, lo ≤ x ∧ x ≤ hi + E := by
        intro x hx
        obtain ⟨x₁, hx₁, a, _, rfl⟩ := (mem_advanceBy A s X x).mp hx
        have h1 := hX x₁ hx₁
        have h2 := hA a
        omega
      have h := ih (advanceBy A s X) (hi + E) hX' k y hy
      have e : (k + 1) * E = k * E + E := by ring
      omega

/-- [proved-derived; formal-checked] **The support stays in an interval**: if `A a ≤ E` for every
letter, then `X_k ⊆ [x₀, x₀ + kE]`, for every `k` and with no hypothesis on the factors. -/
theorem reach_subset_Icc_of_le (x₀ : ℕ) (A : α → ℕ) (F : List (Finset α)) (E : ℕ)
    (hA : ∀ a, A a ≤ E) (k : ℕ) : reach x₀ A F k ⊆ Finset.Icc x₀ (x₀ + k * E) := by
  intro y hy
  rw [Finset.mem_Icc]
  exact reachFrom_bounds A E x₀ hA F {x₀} x₀
    (fun x hx => by rw [Finset.mem_singleton] at hx; omega) k y hy

/-- [proved-derived; formal-checked] **The support stays in an interval of width `k(D − 1)`**: if
`A a < D` for every letter (the advances are below the period), then
`X_k ⊆ [x₀, x₀ + k(D − 1)]`, for every `k` and with no hypothesis on the factors. -/
theorem reach_subset_Icc (x₀ : ℕ) (A : α → ℕ) (F : List (Finset α)) (D : ℕ)
    (hA : ∀ a, A a < D) (k : ℕ) : reach x₀ A F k ⊆ Finset.Icc x₀ (x₀ + k * (D - 1)) :=
  reach_subset_Icc_of_le x₀ A F (D - 1) (fun a => by have h := hA a; omega) k

/-- [proved-derived; formal-checked] **The linear bound**: if `A a < D` for every letter then
`|X_k| ≤ k(D − 1) + 1`, for every `k`, however many factors are free. -/
theorem card_reach_le (x₀ : ℕ) (A : α → ℕ) (F : List (Finset α)) (D : ℕ)
    (hA : ∀ a, A a < D) (k : ℕ) : (reach x₀ A F k).card ≤ k * (D - 1) + 1 := by
  have h := Finset.card_le_card (reach_subset_Icc x₀ A F D hA k)
  rw [Nat.card_Icc] at h
  omega

/-- [proved-derived; formal-checked] **Both bounds**: if `A a < D` for every letter, then
`|X_k| ≤ min(∏_(j<k) |F_j|, k(D − 1) + 1)` for every `k`. -/
theorem card_reach_le_min (x₀ : ℕ) (A : α → ℕ) (F : List (Finset α)) (D : ℕ)
    (hA : ∀ a, A a < D) (k : ℕ) :
    (reach x₀ A F k).card ≤ min (choiceCount F k) (k * (D - 1) + 1) := by
  have h1 := card_reach_le_prod x₀ A F k
  have h2 := card_reach_le x₀ A F D hA k
  omega

/-! ## 5. The diameter of the class tuples -/

section Diameter

variable {R : Type*} [SemilatticeSup R] [OrderBot R]

/-- [definition] The diameter of a finite family `S` under a distance `δ`: the supremum of `δ m m'`
over the ordered pairs of `S`, an iterated `Finset.sup` into a join-semilattice with bottom. The
empty family has diameter `⊥`. For `ℚ≥0` this is the exact maximum of a finite set of nonnegative
rationals. -/
def diam {M : Type*} (δ : M → M → R) (S : Finset M) : R :=
  S.sup fun m => S.sup fun m' => δ m m'

/-- [proved-derived; formal-checked] Every pair of the family is within the diameter. -/
theorem le_diam {M : Type*} (δ : M → M → R) {S : Finset M} {m m' : M} (hm : m ∈ S) (hm' : m' ∈ S) :
    δ m m' ≤ diam δ S := by
  have h1 : δ m m' ≤ S.sup (fun b => δ m b) := by
    first
      | exact Finset.le_sup (f := fun b => δ m b) hm'
      | exact Finset.le_sup hm'
  have h2 : S.sup (fun b => δ m b) ≤ S.sup (fun a => S.sup (fun b => δ a b)) := by
    first
      | exact Finset.le_sup (f := fun a => S.sup (fun b => δ a b)) hm
      | exact Finset.le_sup hm
  exact le_trans h1 h2

/-- [proved-derived; formal-checked] The diameter is below a bound exactly when every pair is. -/
theorem diam_le_iff {M : Type*} (δ : M → M → R) (S : Finset M) (c : R) :
    diam δ S ≤ c ↔ ∀ m ∈ S, ∀ m' ∈ S, δ m m' ≤ c := by
  constructor
  · intro h m hm m' hm'
    exact le_trans (le_diam δ hm hm') h
  · intro h
    show S.sup (fun m => S.sup (fun m' => δ m m')) ≤ c
    exact Finset.sup_le fun m hm => Finset.sup_le fun m' hm' => h m hm m' hm'

/-- [proved-derived; formal-checked] The diameter is `⊥` exactly when every pair is at distance
`⊥`. -/
theorem diam_eq_bot_iff {M : Type*} (δ : M → M → R) (S : Finset M) :
    diam δ S = ⊥ ↔ ∀ m ∈ S, ∀ m' ∈ S, δ m m' = ⊥ := by
  first
    | (unfold diam; simp only [Finset.sup_eq_bot_iff]; done)
    | (rw [← le_bot_iff, diam_le_iff]; simp only [le_bot_iff]; done)

/-- [proved-derived; formal-checked] **A map onto the support preserves the diameter.** If `f` sends
the family `S` into `T` and every point of `T` is the image of a point of `S`, then the diameter of
`S` under the pulled-back distance `δ (f m) (f m')` is the diameter of `T` under `δ`. The two
hypotheses are `f '' S = T`; duplicates in `S` that `f` identifies add nothing. -/
theorem diam_comp_of_surj {M N : Type*} (δ : N → N → R) (S : Finset M) (T : Finset N) (f : M → N)
    (hmaps : ∀ m ∈ S, f m ∈ T) (hsurj : ∀ z ∈ T, ∃ m ∈ S, f m = z) :
    diam (fun m m' => δ (f m) (f m')) S = diam δ T := by
  apply le_antisymm
  · rw [diam_le_iff]
    intro m hm m' hm'
    exact le_diam δ (hmaps m hm) (hmaps m' hm')
  · rw [diam_le_iff]
    intro z hz z' hz'
    obtain ⟨m, hm, rfl⟩ := hsurj z hz
    obtain ⟨m', hm', rfl⟩ := hsurj z' hz'
    exact le_diam (fun m m' => δ (f m) (f m')) hm hm'

/-- [definition] The distance of two class tuples in the supremum norm: the maximum over the
coordinates `i ∈ I` of the coordinate distances `d i`. -/
def tupleDist {ι : Type*} {Y : ι → Type*} (I : Finset ι) (d : ∀ i, Y i → Y i → R)
    (t t' : ∀ i, Y i) : R :=
  I.sup fun i => d i (t i) (t' i)

/-- [proved-derived; formal-checked] **No pooling: the diameter of the class tuples is the maximum
over the coordinates of the coordinate diameters.** For any finite family `S`, any finite set `I` of
coordinates, any class map `cls` and any coordinate distances `d` (no hypothesis on them; the empty
family and the empty coordinate set give `⊥` on both sides), the diameter of the family under the
maximum-over-coordinates distance equals the maximum over the coordinates of each coordinate's own
diameter. Readings of different coordinates are never compared with each other. This is two
suprema commuted. -/
theorem diam_tuple_eq_max {M ι : Type*} {Y : ι → Type*} (I : Finset ι) (d : ∀ i, Y i → Y i → R)
    (S : Finset M) (cls : M → ∀ i, Y i) :
    diam (fun m m' => tupleDist I d (cls m) (cls m')) S
      = I.sup fun i => diam (fun m m' => d i (cls m i) (cls m' i)) S := by
  apply le_antisymm
  · rw [diam_le_iff]
    intro m hm m' hm'
    show I.sup (fun i => d i (cls m i) (cls m' i)) ≤ _
    refine Finset.sup_le fun i hi => ?_
    have h1 : d i (cls m i) (cls m' i) ≤ diam (fun m m' => d i (cls m i) (cls m' i)) S :=
      le_diam (fun m m' => d i (cls m i) (cls m' i)) hm hm'
    have h2 : diam (fun m m' => d i (cls m i) (cls m' i)) S
        ≤ I.sup fun j => diam (fun m m' => d j (cls m j) (cls m' j)) S := by
      first
        | exact Finset.le_sup (f := fun j => diam (fun m m' => d j (cls m j) (cls m' j)) S) hi
        | exact Finset.le_sup hi
    exact le_trans h1 h2
  · refine Finset.sup_le fun i hi => ?_
    rw [diam_le_iff]
    intro m hm m' hm'
    have h1 : d i (cls m i) (cls m' i) ≤ I.sup fun j => d j (cls m j) (cls m' j) := by
      first
        | exact Finset.le_sup (f := fun j => d j (cls m j) (cls m' j)) hi
        | exact Finset.le_sup hi
    have h2 : tupleDist I d (cls m) (cls m')
        ≤ diam (fun m m' => tupleDist I d (cls m) (cls m')) S :=
      le_diam (fun m m' => tupleDist I d (cls m) (cls m')) hm hm'
    exact le_trans h1 h2

/-- [proved-derived; formal-checked] **Through the support.** Let each coordinate `i ∈ I` read a
state `st i m` of the member `m ∈ S` through a reading `r i`, and let `T i` be a finite set with
`st i '' S = T i` (`hmaps`: every state of a member is in `T i`; `hsurj`: every point of `T i` is the
state of some member, so every supported state extends to an actual member). Then the diameter of
the family's class tuples is the maximum over the coordinates of the diameter of the reading `r i`
on the support `T i`. No hypothesis on the distances `d`. The family is not required to be a
product: any finite family with exact supports qualifies, which is where a fit-constrained family
enters once its pruned supports are shown exact. -/
theorem diam_tuple_eq_max_support {M Z ι : Type*} {Y : ι → Type*} (I : Finset ι) (S : Finset M)
    (d : ∀ i, Y i → Y i → R) (r : ∀ i, Z → Y i) (st : ι → M → Z) (T : ι → Finset Z)
    (hmaps : ∀ i ∈ I, ∀ m ∈ S, st i m ∈ T i)
    (hsurj : ∀ i ∈ I, ∀ z ∈ T i, ∃ m ∈ S, st i m = z) :
    diam (fun m m' => tupleDist I d (fun i => r i (st i m)) (fun i => r i (st i m'))) S
      = I.sup fun i => diam (fun z z' => d i (r i z) (r i z')) (T i) := by
  refine (diam_tuple_eq_max I d S (fun m i => r i (st i m))).trans ?_
  refine Finset.sup_congr rfl fun i hi => ?_
  exact diam_comp_of_surj (fun z z' => d i (r i z) (r i z')) S (T i) (st i) (hmaps i hi)
    (hsurj i hi)

/-- [definition] The class tuple of a word `w`: coordinate `i` is the reading `r i` of the lift of `w`
at the level `lev i`. -/
def classTuple {ι : Type*} {Y : ι → Type*} (x₀ : ℕ) (A : α → ℕ) (lev : ι → ℕ)
    (r : ∀ i, ℕ → Y i) (w : List α) : ∀ i, Y i :=
  fun i => r i (prefixLift x₀ A w (lev i))

/-- [proved-derived; formal-checked] **The diameter equation of the independent family.** If every
factor is nonempty and every coordinate's level is at most `n`, the diameter of the class tuples of
the family `members F` under the supremum norm is the maximum over the coordinates of the diameter
of the coordinate's reading `r i` on the carried support `X_(lev i)`:
`diameter(class(F)) = max_i diameter(r_i '' X_(lev i))`. No hypothesis on the distances. The
`∏_j |F_j|` members are never enumerated on the right. -/
theorem diam_family_eq_max_support {ι : Type*} {Y : ι → Type*} (x₀ : ℕ) (A : α → ℕ)
    (F : List (Finset α)) (hne : ∀ s ∈ F, s.Nonempty) (I : Finset ι) (lev : ι → ℕ)
    (hlev : ∀ i ∈ I, lev i ≤ F.length) (d : ∀ i, Y i → Y i → R) (r : ∀ i, ℕ → Y i) :
    diam (fun w w' => tupleDist I d (classTuple x₀ A lev r w) (classTuple x₀ A lev r w'))
        (members F)
      = I.sup fun i => diam (fun x y => d i (r i x) (r i y)) (reach x₀ A F (lev i)) := by
  refine diam_tuple_eq_max_support I (members F) d r (fun i w => prefixLift x₀ A w (lev i))
    (fun i => reach x₀ A F (lev i)) ?_ ?_
  · intro i hi w hw
    exact (mem_reach_iff x₀ A F hne (hlev i hi) (prefixLift x₀ A w (lev i))).mpr
      ⟨w, (mem_members F w).mp hw, rfl⟩
  · intro i hi z hz
    obtain ⟨w, hw, rfl⟩ := (mem_reach_iff x₀ A F hne (hlev i hi) z).mp hz
    exact ⟨w, (mem_members F w).mpr hw, rfl⟩

/-- [proved-derived; formal-checked] **Release: the diameter is `⊥` exactly when every coordinate is
constant on its support.** Assume every factor is nonempty, every level is at most `n`, `d i v v = ⊥`
and `d i v w = ⊥ → v = w`. Then the diameter of the class tuples of `members F` is `⊥` exactly when,
for every coordinate `i ∈ I`, the reading `r i` takes at most one value on the carried support
`X_(lev i)`. -/
theorem diam_family_eq_bot_iff {ι : Type*} {Y : ι → Type*} (x₀ : ℕ) (A : α → ℕ)
    (F : List (Finset α)) (hne : ∀ s ∈ F, s.Nonempty) (I : Finset ι) (lev : ι → ℕ)
    (hlev : ∀ i ∈ I, lev i ≤ F.length) (d : ∀ i, Y i → Y i → R) (r : ∀ i, ℕ → Y i)
    (hrefl : ∀ i v, d i v v = ⊥) (hsep : ∀ i v w, d i v w = ⊥ → v = w) :
    diam (fun w w' => tupleDist I d (classTuple x₀ A lev r w) (classTuple x₀ A lev r w'))
        (members F) = ⊥
      ↔ ∀ i ∈ I, ∀ x ∈ reach x₀ A F (lev i), ∀ y ∈ reach x₀ A F (lev i), r i x = r i y := by
  rw [diam_family_eq_max_support x₀ A F hne I lev hlev d r, Finset.sup_eq_bot_iff]
  constructor
  · intro h i hi x hx y hy
    have h1 : d i (r i x) (r i y) = ⊥ := (diam_eq_bot_iff _ _).mp (h i hi) x hx y hy
    exact hsep i _ _ h1
  · intro h i hi
    rw [diam_eq_bot_iff]
    intro x hx y hy
    show d i (r i x) (r i y) = ⊥
    rw [h i hi x hx y hy]
    exact hrefl i _

/-! ## 6. The decoder's tuple: positions `0..=n` and the terminal carry -/

/-- [proved-derived; formal-checked] **The decoder's equation.** The class of a repair word is the
tuple of the readings `r i` of its lifts at positions `0..=n` together with, as coordinate `n + 1`,
a reading of the terminal lift (the whole winding `ℓ_n div D`): coordinate `i` reads the lift at
level `min i n`. If every factor is nonempty,

`diameter(class(F)) = max_(i ≤ n+1) diameter(r_i '' X_(min(i, n)))`,

with the supremum norm on the class, for any readings `r` and any distances `d`. This is
`Decoder::decode`'s aggregate `max(diam E(X_0), …, diam E(X_n), diam winding(X_n))`. -/
theorem diam_class_eq_max_support {V : Type*} (x₀ : ℕ) (A : α → ℕ) (F : List (Finset α))
    (hne : ∀ s ∈ F, s.Nonempty) (d : ℕ → V → V → R) (r : ℕ → ℕ → V) :
    diam (fun w w' => tupleDist (Y := fun _ => V) (Finset.range (F.length + 2)) d
          (classTuple (Y := fun _ => V) x₀ A (fun i => min i F.length) r w)
          (classTuple (Y := fun _ => V) x₀ A (fun i => min i F.length) r w'))
        (members F)
      = (Finset.range (F.length + 2)).sup fun i =>
          diam (fun x y => d i (r i x) (r i y)) (reach x₀ A F (min i F.length)) :=
  diam_family_eq_max_support x₀ A F hne (Finset.range (F.length + 2)) (fun i => min i F.length)
    (fun i _ => Nat.min_le_right i F.length) d r

/-- [proved-derived; formal-checked] **The decoder's release.** Under the hypotheses of
`diam_class_eq_max_support` and `d i v v = ⊥`, `d i v w = ⊥ → v = w`, the class of the family has
diameter `⊥` exactly when, for each of the `n + 2` coordinates `i`, the reading `r i` takes at most
one value on the carried support `X_(min(i, n))`. -/
theorem diam_class_eq_bot_iff {V : Type*} (x₀ : ℕ) (A : α → ℕ) (F : List (Finset α))
    (hne : ∀ s ∈ F, s.Nonempty) (d : ℕ → V → V → R) (r : ℕ → ℕ → V)
    (hrefl : ∀ i v, d i v v = ⊥) (hsep : ∀ i v w, d i v w = ⊥ → v = w) :
    diam (fun w w' => tupleDist (Y := fun _ => V) (Finset.range (F.length + 2)) d
          (classTuple (Y := fun _ => V) x₀ A (fun i => min i F.length) r w)
          (classTuple (Y := fun _ => V) x₀ A (fun i => min i F.length) r w'))
        (members F) = ⊥
      ↔ ∀ i ∈ Finset.range (F.length + 2), ∀ x ∈ reach x₀ A F (min i F.length),
          ∀ y ∈ reach x₀ A F (min i F.length), r i x = r i y :=
  diam_family_eq_bot_iff x₀ A F hne (Finset.range (F.length + 2)) (fun i => min i F.length)
    (fun i _ => Nat.min_le_right i F.length) d r (fun i v => hrefl i v)
    (fun i v w h => hsep i v w h)

end Diameter

/-! ## 7. Exact rational distances -/

section Rational

/-- [proved-derived; formal-checked] In the nonnegative rationals the bottom is zero. -/
theorem nnrat_bot_eq_zero : (⊥ : NNRat) = 0 := by
  first
    | rfl
    | exact bot_eq_zero
    | simp

/-- [proved-derived; formal-checked] **Release over the exact nonnegative rationals.** With distances
`d i : Y i → Y i → ℚ≥0` such that `d i v v = 0` and `d i v w = 0 → v = w`, every factor nonempty and
every level at most `n`, the diameter of the class tuples of `members F` is zero exactly when, for
every coordinate, the reading is constant on its carried support. -/
theorem diam_family_eq_zero_iff {ι : Type*} {Y : ι → Type*} (x₀ : ℕ) (A : α → ℕ)
    (F : List (Finset α)) (hne : ∀ s ∈ F, s.Nonempty) (I : Finset ι) (lev : ι → ℕ)
    (hlev : ∀ i ∈ I, lev i ≤ F.length) (d : ∀ i, Y i → Y i → NNRat) (r : ∀ i, ℕ → Y i)
    (hrefl : ∀ i v, d i v v = 0) (hsep : ∀ i v w, d i v w = 0 → v = w) :
    diam (fun w w' => tupleDist I d (classTuple x₀ A lev r w) (classTuple x₀ A lev r w'))
        (members F) = 0
      ↔ ∀ i ∈ I, ∀ x ∈ reach x₀ A F (lev i), ∀ y ∈ reach x₀ A F (lev i), r i x = r i y := by
  have h := diam_family_eq_bot_iff x₀ A F hne I lev hlev d r
    (fun i v => (hrefl i v).trans nnrat_bot_eq_zero.symm)
    (fun i v w hvw => hsep i v w (hvw.trans nnrat_bot_eq_zero))
  first
    | exact h
    | (rw [nnrat_bot_eq_zero] at h; exact h)
    | simpa using h

end Rational

end Holonics.Transport.HelicalRepair
