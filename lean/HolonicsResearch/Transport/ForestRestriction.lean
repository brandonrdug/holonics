import HolonicsResearch.Transport.ArtifactRelease

/-!
# The two-sided restriction on a forest of pair relations is the joint fibre's projection

[definition] A **forest of pair relations** (`PairForest`) on cells `V` with classes in `α`: each
cell has at most one antecedent (`parent`), a rank that strictly increases from antecedent to
consequent (so the incidence is acyclic: a forest, each root's cells a tree), and the edge
`(parent v, v)` carries the relation `rel v b a` between the antecedent's class `b` and the cell's
class `a`. The repair owner's constraint graph is one (`offsetChains`: the edges `(t − δ, t)` join
each residue class of `ℤ/δ` into a chain; Rust `compression::keys::repair`). Each cell starts with
a family `D v` of admitted classes. The **joint fibre** is the family of joint assignments that
take admitted classes and satisfy every edge relation (`jointFibre`); in the artifact chart it is
`ArtifactRelease.step id Sat (Π_v D v)`, the product family restricted by the admitted constraint
(`jointFibre_eq_step`), so no receiver width widens (`jointFibre_width_le`, citing
`restriction_never_widens`). Its **projection** at a cell is the set of that cell's classes over
the fibre (`proj`).

[definition] **The two-sided restriction** (`revise`): each family keeps a class only when the
antecedent's side supplies it, `F_t ∩ R(F_(t−δ))`, and every consequent's side receives it,
`F_t ∩ R⁻¹(F_(t+δ))`, in one step `F_t ← F_t ∩ R(F_s) ∩ R⁻¹(F_u)`. A fixed point of the
restriction is a family in which every class has a support across every edge
(`antecedent_of_fixed`, `consequent_of_fixed`).

[proved-derived; formal-checked] What is proved (#366 §8 item 1; #374 §8 item 5's chain case).
1. **The restriction never widens** (`revise_subset`), is monotone (`revise_mono`), and the
   projection is one of its fixed points (`revise_proj`), so every iterate from `D` keeps the
   projection (`proj_subset_iterate`). The iterates reach a fixed point within `Σ_v |D v|` sweeps
   (`exists_fixed_iterate`, a strict descent of `Σ_v |F_v|`, `mass_revise_lt`).
2. **On a forest every fixed point that keeps a class at each cell lies in the projection**
   (`fixed_subset_proj`). A class `a` at a cell `v` is lifted to the root by its antecedents'
   supports (`exists_guide`, by strong induction on the rank), then completed from the roots down
   by consequent supports that keep the guide wherever it fits (`complete`, `complete_spec`,
   `complete_agrees`): a joint assignment through `(v, a)`.
3. **The restriction is the joint fibre's projection** (`restriction_eq_projection`): when the
   fibre is nonempty, any fixed iterate equals the projection at every cell. **Some family
   empties exactly when the fibre is empty** (`restriction_empties_iff`).
4. **On a tree** (one root, `IsTree`) an emptied family empties every family
   (`fixed_empty_spreads`), so the fixed iterate is the projection with no hypothesis
   (`tree_restriction_eq_projection`). On a forest of several trees an inconsistent tree empties
   only its own families, while the projection of the empty fibre is empty everywhere: the forest
   statement keeps the nonempty-fibre hypothesis for that reason.
5. **The released cell is its truth** (`released_class_is_truth`): if the truth's assignment is in
   the fibre and the fixed family at `v` is one class, that class is the truth's; in the artifact
   chart the fibre is `Releasable` at `{i}` exactly when the fixed family at `i` is one class
   (`releasable_iff_one_class`), the width-zero release of `ReceiverRelease`
   (`ArtifactRelease.releasable_iff_every_coordinate_width_is_zero`).

[counterexample; formal-checked] **Acyclicity is load-bearing** (`triangle_supported_but_empty`):
on the triangle with `≠` on every edge over two classes, every class has a support across every
edge (the full families are fixed), yet no joint assignment exists.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Holonics.Transport.ForestRestriction

/-- [definition] **A forest of pair relations** on the cells `V` with classes in `α`. Each cell has
at most one antecedent `parent v`; the rank increases strictly from antecedent to consequent, so the
incidence is acyclic; the edge `(parent v, v)` carries `rel v b a`, relating the antecedent's class
`b` to the cell's class `a`. -/
structure PairForest (V α : Type*) where
  parent : V → Option V
  rank : V → ℕ
  rank_lt : ∀ {v p : V}, parent v = some p → rank p < rank v
  rel : V → α → α → Prop

namespace PairForest

variable {V α : Type*}

/-- [definition] `u` lies on `v`'s antecedent chain (or is `v`). -/
inductive Anc (T : PairForest V α) (u : V) : V → Prop
  | refl : Anc T u u
  | step {v p : V} : T.parent v = some p → Anc T u p → Anc T u v

theorem Anc.rank_le {T : PairForest V α} {u v : V} (h : T.Anc u v) : T.rank u ≤ T.rank v := by
  induction h with
  | refl => exact le_rfl
  | step hp _ ih => exact ih.trans (T.rank_lt hp).le

theorem Anc.parent_anc {T : PairForest V α} {u v q : V} (h : T.Anc u v)
    (hq : T.parent u = some q) : T.Anc q v := by
  induction h with
  | refl => exact Anc.step hq Anc.refl
  | step hp _ ih => exact Anc.step hp ih

variable (T : PairForest V α)

/-! ## 1. The two-sided restriction -/

/-- [definition] A joint assignment satisfies every edge relation. -/
def Sat (x : V → α) : Prop := ∀ v p, T.parent v = some p → T.rel v (x p) (x v)

/-- [definition] The antecedent's side supplies `a` at `v`: `a ∈ R(F_parent)`. -/
def Supplied (F : V → Finset α) (v : V) (a : α) : Prop :=
  ∀ p, T.parent v = some p → ∃ b ∈ F p, T.rel v b a

/-- [definition] Every consequent's side receives `a` at `v`: `a ∈ R⁻¹(F_child)` for each child. -/
def Received (F : V → Finset α) (v : V) (a : α) : Prop :=
  ∀ c, T.parent c = some v → ∃ a' ∈ F c, T.rel c a a'

/-- [definition] **The two-sided restriction** `F_t ← F_t ∩ R(F_s) ∩ R⁻¹(F_u)`. -/
def revise (F : V → Finset α) : V → Finset α :=
  fun v => (F v).filter fun a => T.Supplied F v a ∧ T.Received F v a

/-- [definition] A fixed point of the restriction. -/
def IsFixed (F : V → Finset α) : Prop := T.revise F = F

variable {T}

theorem mem_revise {F : V → Finset α} {v : V} {a : α} :
    a ∈ T.revise F v ↔ a ∈ F v ∧ T.Supplied F v a ∧ T.Received F v a := by
  simp only [revise, Finset.mem_filter]

variable (T)

/-- [proved-derived; formal-checked] **The restriction never widens** a family. -/
theorem revise_subset (F : V → Finset α) (v : V) : T.revise F v ⊆ F v :=
  Finset.filter_subset _ _

/-- [proved-derived; formal-checked] The restriction is monotone. -/
theorem revise_mono {F G : V → Finset α} (h : ∀ v, F v ⊆ G v) (v : V) :
    T.revise F v ⊆ T.revise G v := by
  intro a ha
  rw [mem_revise] at ha ⊢
  obtain ⟨haF, hsup, hrec⟩ := ha
  refine ⟨h v haF, fun p hp => ?_, fun c hc => ?_⟩
  · obtain ⟨b, hb, hr⟩ := hsup p hp
    exact ⟨b, h p hb, hr⟩
  · obtain ⟨a', ha', hr⟩ := hrec c hc
    exact ⟨a', h c ha', hr⟩

theorem iterate_subset (D : V → Finset α) : ∀ (n : ℕ) (v : V), (T.revise^[n] D) v ⊆ D v
  | 0, _ => le_rfl
  | n + 1, v => by
    rw [Function.iterate_succ_apply']
    exact (T.revise_subset _ v).trans (iterate_subset D n v)

variable {T}

theorem supplied_of_fixed {F : V → Finset α} (hF : T.IsFixed F) {v p : V}
    (hp : T.parent v = some p) {a : α} (ha : a ∈ F v) : ∃ b ∈ F p, T.rel v b a := by
  have ha' : a ∈ T.revise F v := by rw [hF]; exact ha
  exact (mem_revise.mp ha').2.1 p hp

theorem received_of_fixed {F : V → Finset α} (hF : T.IsFixed F) {v p : V}
    (hp : T.parent v = some p) {b : α} (hb : b ∈ F p) : ∃ a ∈ F v, T.rel v b a := by
  have hb' : b ∈ T.revise F p := by rw [hF]; exact hb
  exact (mem_revise.mp hb').2.2 v hp

variable (T)

/-! ## 2. The completion from the roots down -/

/-- [definition] A support of the antecedent's class `b` at `v`, keeping the guide's class `a₀`
when it already fits. -/
def support (F : V → Finset α) (v : V) (b a₀ : α) : α :=
  if T.rel v b a₀ ∧ a₀ ∈ F v then a₀
  else if h : ∃ a ∈ F v, T.rel v b a then h.choose else a₀

theorem support_spec {F : V → Finset α} {v : V} {b : α} (a₀ : α) (h : ∃ a ∈ F v, T.rel v b a) :
    T.support F v b a₀ ∈ F v ∧ T.rel v b (T.support F v b a₀) := by
  unfold support
  split_ifs with h1
  · exact ⟨h1.2, h1.1⟩
  · exact ⟨h.choose_spec.1, h.choose_spec.2⟩

theorem support_keep {F : V → Finset α} {v : V} {b a₀ : α} (hr : T.rel v b a₀) (ha : a₀ ∈ F v) :
    T.support F v b a₀ = a₀ := by
  unfold support
  rw [if_pos ⟨hr, ha⟩]

/-- [definition] **The completion from the roots down**: a root keeps the guide's class; every other
cell takes a support of its antecedent's completed class, keeping the guide's class where it fits. -/
def complete (F : V → Finset α) (y : V → α) (v : V) : α :=
  match _hp : T.parent v with
  | none => y v
  | some p => T.support F v (complete F y p) (y v)
termination_by T.rank v
decreasing_by exact T.rank_lt _hp

theorem complete_of_none {F : V → Finset α} {y : V → α} {v : V} (hp : T.parent v = none) :
    T.complete F y v = y v := by
  rw [complete]
  split <;> simp_all

theorem complete_of_some {F : V → Finset α} {y : V → α} {v p : V} (hp : T.parent v = some p) :
    T.complete F y v = T.support F v (T.complete F y p) (y v) := by
  rw [complete]
  split <;> simp_all

variable {T}

/-- [proved-derived; formal-checked] **The completion is a member of the fibre**: from a fixed
point and any guide in its families, every completed class lies in its family and every edge
relation holds. -/
theorem complete_spec {F : V → Finset α} (hF : T.IsFixed F) {y : V → α} (hy : ∀ w, y w ∈ F w) :
    ∀ v, T.complete F y v ∈ F v ∧
      ∀ p, T.parent v = some p → T.rel v (T.complete F y p) (T.complete F y v) := by
  have key : ∀ n v, T.rank v = n → T.complete F y v ∈ F v ∧
      ∀ p, T.parent v = some p → T.rel v (T.complete F y p) (T.complete F y v) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv
      cases hp : T.parent v with
      | none =>
        rw [T.complete_of_none hp]
        exact ⟨hy v, fun p h => by simp at h⟩
      | some p =>
        have hpF := (ih (T.rank p) (hv ▸ T.rank_lt hp) p rfl).1
        have hs := T.support_spec (y v) (received_of_fixed hF hp hpF)
        rw [T.complete_of_some hp]
        refine ⟨hs.1, fun p' hp' => ?_⟩
        cases hp'
        exact hs.2
  exact fun v => key _ v rfl

/-- [proved-derived; formal-checked] **The completion keeps a consistent guide**: where the guide
satisfies every edge on `v`'s antecedent chain, the completion agrees with it along that chain. -/
theorem complete_agrees {F : V → Finset α} {y : V → α} (hy : ∀ w, y w ∈ F w) {v : V}
    (hchain : ∀ u q, T.Anc u v → T.parent u = some q → T.rel u (y q) (y u)) :
    ∀ u, T.Anc u v → T.complete F y u = y u := by
  have key : ∀ n u, T.rank u = n → T.Anc u v → T.complete F y u = y u := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro u hu hA
      cases hq : T.parent u with
      | none => exact T.complete_of_none hq
      | some q =>
        have hqA := hA.parent_anc hq
        rw [T.complete_of_some hq, ih (T.rank q) (hu ▸ T.rank_lt hq) q rfl hqA]
        exact T.support_keep (hchain u q hA hq) (hy u)
  exact fun u => key _ u rfl

/-- [proved-derived; formal-checked] **The class lifts to the root.** At a fixed point whose
families are nonempty, every class `a` at `v` begins a guide in the families that satisfies every
edge on `v`'s antecedent chain: each antecedent supplies a support. -/
theorem exists_guide {F : V → Finset α} (hF : T.IsFixed F) (hne : ∀ w, (F w).Nonempty) :
    ∀ v, ∀ a ∈ F v, ∃ y : V → α, (∀ w, y w ∈ F w) ∧ y v = a ∧
      ∀ u q, T.Anc u v → T.parent u = some q → T.rel u (y q) (y u) := by
  have key : ∀ n v, T.rank v = n → ∀ a ∈ F v, ∃ y : V → α, (∀ w, y w ∈ F w) ∧ y v = a ∧
      ∀ u q, T.Anc u v → T.parent u = some q → T.rel u (y q) (y u) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv a ha
      cases hp : T.parent v with
      | none =>
        refine ⟨Function.update (fun w => (hne w).choose) v a, fun w => ?_, by simp, ?_⟩
        · by_cases hw : w = v
          · subst hw; simpa using ha
          · simpa [Function.update_of_ne hw] using (hne w).choose_spec
        · intro u q hA hq
          cases hA with
          | refl => rw [hp] at hq; cases hq
          | step hv' _ => rw [hp] at hv'; cases hv'
      | some p =>
        obtain ⟨b, hb, hrel⟩ := supplied_of_fixed hF hp ha
        have hlt : T.rank p < T.rank v := T.rank_lt hp
        obtain ⟨y, hyF, hyp, hchain⟩ := ih (T.rank p) (hv ▸ hlt) p rfl b hb
        have hpv : p ≠ v := fun h => by subst h; exact lt_irrefl _ hlt
        refine ⟨Function.update y v a, fun w => ?_, by simp, ?_⟩
        · by_cases hw : w = v
          · subst hw; simpa using ha
          · simpa [Function.update_of_ne hw] using hyF w
        · intro u q hA hq
          cases hA with
          | refl =>
            rw [hp] at hq
            cases hq
            simpa [Function.update_of_ne hpv, hyp] using hrel
          | step hv' hA' =>
            rw [hp] at hv'
            cases hv'
            have hu : u ≠ v := fun h => by
              subst h; exact absurd hA'.rank_le (not_le.mpr hlt)
            have hq' : q ≠ v := fun h => by
              subst h; exact absurd (hA'.parent_anc hq).rank_le (not_le.mpr hlt)
            rw [Function.update_of_ne hu, Function.update_of_ne hq']
            exact hchain u q hA' hq
  exact fun v => key _ v rfl

variable (T)

/-- [definition] A forest with one root is a tree. -/
def IsTree : Prop := ∃ r, ∀ v, T.parent v = none → v = r

variable {T}

/-- [proved-derived; formal-checked] **On a tree an emptied family empties every family**: the
emptiness climbs each antecedent chain to the root and descends to every cell. -/
theorem fixed_empty_spreads (hT : T.IsTree) {F : V → Finset α} (hF : T.IsFixed F) {v : V}
    (hv : F v = ∅) : ∀ w, F w = ∅ := by
  obtain ⟨r, hr⟩ := hT
  have up : ∀ n v, T.rank v = n → F v = ∅ → F r = ∅ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hvn hv
      cases hp : T.parent v with
      | none => rw [← hr v hp]; exact hv
      | some p =>
        refine ih (T.rank p) (hvn ▸ T.rank_lt hp) p rfl
          (Finset.eq_empty_of_forall_notMem fun b hb => ?_)
        obtain ⟨a, ha, -⟩ := received_of_fixed hF hp hb
        simp [hv] at ha
  have hroot := up _ v rfl hv
  have down : ∀ n w, T.rank w = n → F w = ∅ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro w hwn
      cases hp : T.parent w with
      | none => rw [hr w hp]; exact hroot
      | some p =>
        have hpe := ih (T.rank p) (hwn ▸ T.rank_lt hp) p rfl
        refine Finset.eq_empty_of_forall_notMem fun a ha => ?_
        obtain ⟨b, hb, -⟩ := supplied_of_fixed hF hp ha
        simp [hpe] at hb
  exact fun w => down _ w rfl


/-! ## 3. The joint fibre and its projection -/

variable [Fintype V] [DecidableEq V]

variable (T)

/-- [definition] **The joint fibre**: the joint assignments taking admitted classes and satisfying
every edge relation. -/
def jointFibre (D : V → Finset α) : Finset (V → α) := (Fintype.piFinset D).filter T.Sat

/-- [definition] **The projection** of the joint fibre at a cell: that cell's classes over it. -/
def proj (D : V → Finset α) (v : V) : Finset α := (T.jointFibre D).image fun x => x v

variable {T}

theorem mem_jointFibre {D : V → Finset α} {x : V → α} :
    x ∈ T.jointFibre D ↔ (∀ v, x v ∈ D v) ∧ T.Sat x := by
  simp [jointFibre, Fintype.mem_piFinset]

theorem mem_proj {D : V → Finset α} {v : V} {a : α} :
    a ∈ T.proj D v ↔ ∃ x ∈ T.jointFibre D, x v = a := by
  simp only [proj, Finset.mem_image]

variable (T)

theorem proj_subset (D : V → Finset α) (v : V) : T.proj D v ⊆ D v := by
  intro a ha
  obtain ⟨x, hx, rfl⟩ := mem_proj.mp ha
  exact (mem_jointFibre.mp hx).1 v

/-- [proved-derived; formal-checked] **The projection is a fixed point of the restriction**: every
class a member of the fibre holds is supplied and received by that member's neighbours. -/
theorem revise_proj (D : V → Finset α) : T.revise (T.proj D) = T.proj D := by
  funext v
  refine Finset.Subset.antisymm (T.revise_subset _ v) fun a ha => ?_
  obtain ⟨x, hx, rfl⟩ := mem_proj.mp ha
  have hsat := (mem_jointFibre.mp hx).2
  rw [mem_revise]
  exact ⟨ha, fun p hp => ⟨x p, mem_proj.mpr ⟨x, hx, rfl⟩, hsat v p hp⟩,
    fun c hc => ⟨x c, mem_proj.mpr ⟨x, hx, rfl⟩, hsat c v hc⟩⟩

/-- [proved-derived; formal-checked] Every iterate of the restriction from `D` keeps the
projection. -/
theorem proj_subset_iterate (D : V → Finset α) : ∀ (n : ℕ) (v : V), T.proj D v ⊆ (T.revise^[n] D) v
  | 0, v => T.proj_subset D v
  | n + 1, v => by
    rw [Function.iterate_succ_apply']
    have h := T.revise_mono (proj_subset_iterate D n) v
    rwa [T.revise_proj] at h

/-- [definition] The families' total class count. -/
def mass (F : V → Finset α) : ℕ := ∑ v, (F v).card

omit [DecidableEq V] in
/-- [proved-derived; formal-checked] A restriction that moves a family strictly lowers the total
class count. -/
theorem mass_revise_lt {F : V → Finset α} (h : ¬ T.IsFixed F) : mass (T.revise F) < mass F := by
  unfold mass
  refine Finset.sum_lt_sum (fun v _ => Finset.card_le_card (T.revise_subset F v)) ?_
  by_contra hcon
  push Not at hcon
  exact h (funext fun v =>
    Finset.eq_of_subset_of_card_le (T.revise_subset F v) (hcon v (Finset.mem_univ v)))

omit [DecidableEq V] in
/-- [proved-derived; formal-checked] **The iterates reach a fixed point** within `Σ_v |D v|`
sweeps. -/
theorem exists_fixed_iterate (D : V → Finset α) :
    ∃ n ≤ mass D, T.IsFixed (T.revise^[n] D) := by
  by_contra hcon
  push Not at hcon
  have key : ∀ n ≤ mass D + 1, mass (T.revise^[n] D) + n ≤ mass D := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 := T.mass_revise_lt (hcon n (by omega))
      rw [Function.iterate_succ_apply']
      omega
  have := key (mass D + 1) le_rfl
  omega

variable {T}

/-! ## 4. On a forest a fixed point lies in the projection -/

/-- [proved-derived; formal-checked] **On a forest every fixed point with nonempty families lies in
the projection**: each class at each cell is that cell's class of some member of the fibre. -/
theorem fixed_subset_proj {D F : V → Finset α} (hF : T.IsFixed F) (hFD : ∀ v, F v ⊆ D v)
    (hne : ∀ v, (F v).Nonempty) : ∀ v, F v ⊆ T.proj D v := by
  intro v a ha
  obtain ⟨y, hyF, hyv, hchain⟩ := exists_guide hF hne v a ha
  have hspec := complete_spec hF hyF
  refine mem_proj.mpr ⟨T.complete F y, mem_jointFibre.mpr ⟨fun w => hFD w (hspec w).1,
    fun w p hp => (hspec w).2 p hp⟩, ?_⟩
  rw [complete_agrees hyF hchain v PairForest.Anc.refl, hyv]

/-- [proved-derived; formal-checked] A fixed point with nonempty families has a nonempty fibre. -/
theorem jointFibre_nonempty_of_fixed {D F : V → Finset α} (hF : T.IsFixed F)
    (hFD : ∀ v, F v ⊆ D v) (hne : ∀ v, (F v).Nonempty) : (T.jointFibre D).Nonempty := by
  have hspec := complete_spec hF (fun w => (hne w).choose_spec)
  exact ⟨T.complete F (fun w => (hne w).choose), mem_jointFibre.mpr
    ⟨fun w => hFD w (hspec w).1, fun w p hp => (hspec w).2 p hp⟩⟩

/-! ## 5. The restriction is the joint fibre's projection -/

/-- [proved-derived; formal-checked] **The restriction is the joint fibre's projection.** On a
forest of pair relations with a nonempty joint fibre, every fixed iterate of the two-sided
restriction from `D` is, at every cell, the set of that cell's classes over the fibre. -/
theorem restriction_eq_projection {D : V → Finset α} {n : ℕ} (hfix : T.IsFixed (T.revise^[n] D))
    (hfib : (T.jointFibre D).Nonempty) : T.revise^[n] D = T.proj D := by
  funext v
  refine Finset.Subset.antisymm ?_ (T.proj_subset_iterate D n v)
  refine fixed_subset_proj hfix (T.iterate_subset D n) (fun w => ?_) v
  obtain ⟨x, hx⟩ := hfib
  exact ⟨x w, T.proj_subset_iterate D n w (mem_proj.mpr ⟨x, hx, rfl⟩)⟩

/-- [proved-derived; formal-checked] **Some family empties exactly when the fibre is empty.** -/
theorem restriction_empties_iff {D : V → Finset α} {n : ℕ} (hfix : T.IsFixed (T.revise^[n] D)) :
    (∃ v, T.revise^[n] D v = ∅) ↔ T.jointFibre D = ∅ := by
  constructor
  · rintro ⟨v, hv⟩
    refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
    have h := T.proj_subset_iterate D n v (mem_proj.mpr ⟨x, hx, rfl⟩)
    simp [hv] at h
  · intro hempty
    by_contra hcon
    push Not at hcon
    have hne := jointFibre_nonempty_of_fixed hfix (T.iterate_subset D n)
      hcon
    simp [hempty] at hne

/-- [proved-derived; formal-checked] **On a tree the restriction is the joint fibre's projection**,
with no hypothesis on the fibre. -/
theorem tree_restriction_eq_projection (hT : T.IsTree) {D : V → Finset α} {n : ℕ}
    (hfix : T.IsFixed (T.revise^[n] D)) : T.revise^[n] D = T.proj D := by
  by_cases hfib : (T.jointFibre D).Nonempty
  · exact restriction_eq_projection hfix hfib
  · have hempty : T.jointFibre D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hfib
    obtain ⟨v, hv⟩ := (restriction_empties_iff hfix).mpr hempty
    funext w
    rw [fixed_empty_spreads hT hfix hv w]
    simp [proj, hempty]

/-- [proved-derived; formal-checked] **The released cell is its truth**: when the truth's joint
assignment is in the fibre and a fixed family at `v` is one class, that class is the truth's. -/
theorem released_class_is_truth {D : V → Finset α} {n : ℕ} {x : V → α}
    (hx : x ∈ T.jointFibre D) {v : V} {a : α} (hone : T.revise^[n] D v = {a}) : x v = a := by
  have h := T.proj_subset_iterate D n v (mem_proj.mpr ⟨x, hx, rfl⟩)
  simpa [hone] using h

/-! ## 6. The repair's chains, and the artifact chart -/

/-- [definition] **The repair's forest** (`compression::keys::repair`): on the cells `0 … L−1`, the
relation `R` at offset `δ ≥ 1` joins each cell `t` of the declared span with `δ ≤ t` to its
antecedent `t − δ`; the edges join each residue class of `ℤ/δ` into a chain. -/
def offsetChains (L δ : ℕ) (hδ : 0 < δ) (span : Fin L → Prop) (R : α → α → Prop) :
    PairForest (Fin L) α where
  parent t := if h : δ ≤ t.val ∧ span t then some ⟨t.val - δ, by omega⟩ else none
  rank t := t.val
  rank_lt := by
    intro v p hp
    split at hp
    · cases hp
      simp only
      omega
    · cases hp
  rel _ := R

open Holonics.Transport.ArtifactRelease

/-- [proved-derived; formal-checked] **The joint fibre is a restriction step**: in the artifact
chart it is `ArtifactRelease.step id Sat (Π_v D v)`, the product family restricted by the admitted
constraint. -/
theorem jointFibre_eq_step {n : ℕ} (T : PairForest (Fin n) ℕ) (D : Fin n → Finset ℕ) :
    T.jointFibre D = step id T.Sat (Fintype.piFinset D) := by
  simp [jointFibre, step]

/-- [proved-derived; formal-checked] No receiver width widens from the product family to the joint
fibre (`ArtifactRelease.restriction_never_widens`). -/
theorem jointFibre_width_le {n : ℕ} (T : PairForest (Fin n) ℕ) (D : Fin n → Finset ℕ)
    (hfib : (T.jointFibre D).Nonempty) (hD : (Fintype.piFinset D).Nonempty)
    (R : Artifact n → ℚ) :
    Foundation.ReceiverRelease.width (T.jointFibre D) hfib R ≤
      Foundation.ReceiverRelease.width (Fintype.piFinset D) hD R :=
  restriction_never_widens (Fintype.piFinset D) T.Sat hfib hD R

/-- [proved-derived; formal-checked] **The width-zero release is the one-class family.** On a forest
with a nonempty joint fibre, the fibre is `Releasable` at the cell `i` exactly when the fixed
family at `i` is one class. -/
theorem releasable_iff_one_class {n : ℕ} (T : PairForest (Fin n) ℕ) {D : Fin n → Finset ℕ} {k : ℕ}
    (hfix : T.IsFixed (T.revise^[k] D)) (hfib : (T.jointFibre D).Nonempty) (i : Fin n) :
    Releasable (T.jointFibre D) {i} ↔ (T.revise^[k] D i).card = 1 := by
  rw [restriction_eq_projection hfix hfib]
  constructor
  · intro hrel
    obtain ⟨x, hx⟩ := hfib
    refine Finset.card_eq_one.mpr ⟨x i, Finset.eq_singleton_iff_unique_mem.mpr
      ⟨mem_proj.mpr ⟨x, hx, rfl⟩, fun a ha => ?_⟩⟩
    obtain ⟨y, hy, rfl⟩ := mem_proj.mp ha
    exact hrel y hy x hx i (Finset.mem_singleton_self i)
  · intro hone y hy z hz j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    exact Finset.card_le_one.mp hone.le _ (mem_proj.mpr ⟨y, hy, rfl⟩) _ (mem_proj.mpr ⟨z, hz, rfl⟩)

end PairForest

/-! ## 7. Acyclicity is load-bearing -/

/-- [counterexample; formal-checked] **On a cycle a supported family need not meet the fibre.** On
the triangle with `≠` on every edge over two classes, every class has a support across every edge
in both directions, so the full families are fixed by the two-sided restriction, yet no joint
assignment satisfies the three edges. -/
theorem triangle_supported_but_empty :
    (∀ i j : Fin 3, i ≠ j → ∀ a : Bool, ∃ b : Bool, a ≠ b) ∧
      ¬ ∃ x : Fin 3 → Bool, x 0 ≠ x 1 ∧ x 1 ≠ x 2 ∧ x 2 ≠ x 0 := by
  decide

section Audit

#print axioms PairForest.revise_proj
#print axioms PairForest.exists_fixed_iterate
#print axioms PairForest.fixed_subset_proj
#print axioms PairForest.restriction_eq_projection
#print axioms PairForest.restriction_empties_iff
#print axioms PairForest.fixed_empty_spreads
#print axioms PairForest.tree_restriction_eq_projection
#print axioms PairForest.released_class_is_truth
#print axioms PairForest.jointFibre_eq_step
#print axioms PairForest.jointFibre_width_le
#print axioms PairForest.releasable_iff_one_class
#print axioms triangle_supported_but_empty

end Audit

end Holonics.Transport.ForestRestriction
