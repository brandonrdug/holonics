import Holonics.Physics.Information.ClockJoin
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-!
# Syndrome localization: loop closure locates a defect only where the menu separates it

`holarchy::terrain::sensing` (the chase's observation channels) reads a defect vector `e` on the
edges of a menu of circuits through its syndrome `s = C e`, and claims that defects on at most `k`
edges are located uniquely exactly when no nonzero `v` of support at most `2k` has `C v = 0`; for
the menu of all cycles of a connected graph, `ker C = im d₀` and the condition is that every edge
cut exceeds `2k` (atlas `attribution.syndrome-localization`). The Rust checks the condition by
enumeration over `(ℤ/4)^n` (`ChannelMenu::separation_witness`). #410 owes the Lean statement.

[proved-standard; formal-checked] What is proved.

1. **Location is separation** (`locates_iff_separates`): for any additive map `C` out of the defect
   vectors `ι → A` (`A` any additive group, `ℚ` and `ℤ/4` included), two defects of support at most
   `k` with one syndrome are equal (`Locates C k`) iff no nonzero kernel vector has support at most
   `2k` (`Separates C k`). Two defects with one syndrome differ by a kernel vector of support at
   most `2k`; such a vector splits into two defects of support at most `k` (`exists_split`) whose
   syndromes agree.
2. **A menu of pair circuits** (`menu`): circuit `c` reads `e (a c) − e (b c)`, the Rust circuit
   matrix with `+1` at `a c` and `−1` at `b c`. Over `ℤ/4`, three channels with circuits
   `(0, 1)`, `(0, 2)`, `(1, 2)` locate one defect with its turn (`menuThree_locates`) and do not
   locate two (`menuThree_not_locates_two`, broken by `(1, 1, 1)`); two channels detect one defect
   (`menuTwo_detects`) but do not locate it (`menuTwo_not_locates`, broken by `(1, 1)`).
3. **All cycles of a connected complex** (`cycleReading`, `cycleReading_eq_zero_iff`): on a
   parametric complex (`Aeon/Clock/Groupoid`) whose occurrences are reached by aeons `path v` from
   one occurrence `base`, a defect reads zero on every closed aeon iff it is exact, `ω = dφ`
   (`exactForm`): the existing owner's `Physics/Information/ClockJoin.join_iff_silent`, Stokes and
   its converse.
4. **The min-cut form** (`locates_iff_minCut`, `cycleReading_locates_iff`): for any menu with
   `ker C = im d₀` on such a complex and a nonzero value in `A`, `Locates C k` iff every
   nonempty proper occurrence set `S` has more than `2k` edges with exactly one end in `S`. The
   support of `d₀` of the lift of `S` is its cut (`supp_exactForm_lift`), a nonzero `dφ` contains
   the cut of a level set of `φ` (`cut_level_subset`), and an aeon leaving `S` crosses its cut
   (`exists_cut_edge`).

The computational object is the helical pair interaction: each channel is a pair contact between the
observed frame and the hidden directions, its defect the contact's slip, and the syndrome is the
holonomy of each circuit of the menu, the Bombe's pairwise loop closure over the menu of contacts.
Of the winding guide's six general objects this touches the pair (each contact's slip) and the cell
holonomy (the syndrome on each circuit); the helix, faces and placement, the tube and the tower
thread stay attached.

Consumers: the atlas rows `attribution.syndrome-localization` and `pursuit.channel-menu`, the Rust
owner `holarchy::terrain::sensing::ChannelMenu`, and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Holon.Syndrome

open Finset
open Holonics.Aeon.Clock.Groupoid Holonics.Aeon.Clock.Reading Holonics.Physics.Information

/-! ## 1. Location is separation -/

section Linear

variable {ι A B : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup A] [DecidableEq A]
  [AddCommGroup B]

/-- [definition] The support of a defect vector: the places where it is nonzero. -/
def supp (v : ι → A) : Finset ι := univ.filter fun i => v i ≠ 0

theorem mem_supp {v : ι → A} {i : ι} : i ∈ supp v ↔ v i ≠ 0 := by
  simp [supp]

theorem supp_neg (v : ι → A) : supp (-v) = supp v := by
  ext i
  simp [mem_supp]

theorem supp_sub_subset (v w : ι → A) : supp (v - w) ⊆ supp v ∪ supp w := by
  intro i hi
  rw [mem_supp] at hi
  rw [mem_union, mem_supp, mem_supp]
  by_contra h
  push Not at h
  exact hi (by simp [h.1, h.2])

/-- [definition] The part of `v` on the places `S`. -/
def restrict (v : ι → A) (S : Finset ι) : ι → A := fun i => if i ∈ S then v i else 0

theorem supp_restrict_subset (v : ι → A) (S : Finset ι) : supp (restrict v S) ⊆ S := by
  intro i hi
  by_contra h
  simp [mem_supp, restrict, h] at hi

theorem restrict_add_restrict_sdiff (v : ι → A) (S : Finset ι) :
    restrict v S + restrict v (supp v \ S) = v := by
  funext i
  simp only [Pi.add_apply, restrict, mem_sdiff]
  by_cases hi : i ∈ S
  · simp [hi]
  · by_cases hv : i ∈ supp v
    · simp [hi, hv]
    · have h0 : v i = 0 := by
        by_contra h
        exact hv (mem_supp.mpr h)
      simp [hi, hv, h0]

/-- [proved-standard] A set of at most `2k` places splits into two parts of at most `k`. -/
theorem exists_split {s : Finset ι} {k : ℕ} (h : s.card ≤ 2 * k) :
    ∃ S ⊆ s, S.card ≤ k ∧ (s \ S).card ≤ k := by
  obtain ⟨S, hS, hc⟩ := exists_subset_card_eq (min_le_right k s.card)
  refine ⟨S, hS, by rw [hc]; exact min_le_left _ _, ?_⟩
  rw [card_sdiff_of_subset hS, hc]
  omega

/-- [definition] **Location within `k` defects**: two defect vectors of support at most `k` with one
syndrome are equal. -/
def Locates (C : (ι → A) →+ B) (k : ℕ) : Prop :=
  ∀ e e' : ι → A, (supp e).card ≤ k → (supp e').card ≤ k → C e = C e' → e = e'

/-- [definition] **Separation at `k`**: no nonzero kernel vector has support at most `2k`. -/
def Separates (C : (ι → A) →+ B) (k : ℕ) : Prop :=
  ∀ v : ι → A, C v = 0 → (supp v).card ≤ 2 * k → v = 0

/-- [definition] **Detection within `k` defects**: no nonzero defect of support at most `k` has the
zero syndrome. -/
def Detects (C : (ι → A) →+ B) (k : ℕ) : Prop :=
  ∀ e : ι → A, C e = 0 → (supp e).card ≤ k → e = 0

/-- [proved-standard; formal-checked] **Location is separation**: defects on at most `k` places are
located uniquely by their syndrome iff `ker C` holds no nonzero vector of support at most `2k`. -/
theorem locates_iff_separates (C : (ι → A) →+ B) (k : ℕ) : Locates C k ↔ Separates C k := by
  constructor
  · intro hL v hv hs
    obtain ⟨S, -, h1, h2⟩ := exists_split hs
    have hsplit := restrict_add_restrict_sdiff v S
    have he := hL (restrict v S) (-restrict v (supp v \ S))
      ((card_le_card (supp_restrict_subset v S)).trans h1)
      (by rw [supp_neg]; exact (card_le_card (supp_restrict_subset v _)).trans h2)
      (by rw [map_neg, eq_neg_iff_add_eq_zero, ← map_add, hsplit, hv])
    calc v = restrict v S + restrict v (supp v \ S) := hsplit.symm
      _ = 0 := by rw [he, neg_add_cancel]
  · intro hS e e' he he' hC
    have h0 := hS (e - e') (by rw [map_sub, hC, sub_self])
      ((card_le_card (supp_sub_subset e e')).trans ((card_union_le _ _).trans (by omega)))
    exact sub_eq_zero.mp h0

end Linear

/-! ## 2. A menu of pair circuits -/

section Menu

variable {ι m A : Type*} [AddCommGroup A]

/-- [definition] **A menu of pair circuits**: circuit `c` reads `e (a c) − e (b c)`, the circuit
matrix with `+1` at `a c` and `−1` at `b c`. -/
def menu (a b : m → ι) : (ι → A) →+ (m → A) where
  toFun e := fun c => e (a c) - e (b c)
  map_zero' := by
    funext c
    simp
  map_add' x y := by
    funext c
    simp only [Pi.add_apply]
    abel

theorem menu_apply (a b : m → ι) (e : ι → A) (c : m) : menu a b e c = e (a c) - e (b c) := rfl

end Menu

/-- The three-channel menu's circuits `(0, 1)`, `(0, 2)`, `(1, 2)`: their first ends. -/
def threeSrc : Fin 3 → Fin 3 := ![0, 0, 1]

/-- The three-channel menu's circuits: their second ends. -/
def threeTgt : Fin 3 → Fin 3 := ![1, 2, 2]

/-- The two-channel menu's one circuit `(0, 1)`: its first end. -/
def twoSrc : Fin 1 → Fin 2 := ![0]

/-- The two-channel menu's one circuit: its second end. -/
def twoTgt : Fin 1 → Fin 2 := ![1]

/-- [proved-derived; formal-checked] **Three channels locate one defect with its turn**: over `ℤ/4`
the kernel of the three-channel menu is the common mode `(c, c, c)`, of support `3 > 2`. -/
theorem menuThree_locates : Locates (menu (A := ZMod 4) threeSrc threeTgt) 1 := by
  rw [locates_iff_separates]
  intro v hv hs
  have h01 : v 0 = v 1 := by
    simpa [menu_apply, threeSrc, threeTgt, sub_eq_zero] using congrFun hv 0
  have h02 : v 0 = v 2 := by
    simpa [menu_apply, threeSrc, threeTgt, sub_eq_zero] using congrFun hv 1
  by_cases h0 : v 0 = 0
  · funext i
    fin_cases i <;> simp [← h01, ← h02, h0]
  · exfalso
    have hu : supp v = univ := by
      ext i
      fin_cases i <;> simp [mem_supp, ← h01, ← h02, h0]
    rw [hu, card_univ, Fintype.card_fin] at hs
    omega

/-- [proved-derived; formal-checked] Three channels do not locate two defects: `(1, 1, 1)` is a
kernel vector of support `3 ≤ 4`. -/
theorem menuThree_not_locates_two : ¬ Locates (menu (A := ZMod 4) threeSrc threeTgt) 2 := by
  rw [locates_iff_separates]
  intro h
  have h1 := h (fun _ => 1) (by funext c; simp [menu_apply])
    ((card_le_univ _).trans (by simp))
  have h10 : (1 : ZMod 4) = 0 := congrFun h1 0
  exact absurd h10 (by decide)

/-- [proved-derived; formal-checked] **Two channels detect one defect**: a nonzero defect on one
channel has a nonzero syndrome. -/
theorem menuTwo_detects : Detects (menu (A := ZMod 4) twoSrc twoTgt) 1 := by
  intro e he hs
  have h01 : e 0 = e 1 := by
    simpa [menu_apply, twoSrc, twoTgt, sub_eq_zero] using congrFun he 0
  by_cases h0 : e 0 = 0
  · funext i
    fin_cases i <;> simp [← h01, h0]
  · exfalso
    have hu : supp e = univ := by
      ext i
      fin_cases i <;> simp [mem_supp, ← h01, h0]
    rw [hu, card_univ, Fintype.card_fin] at hs
    omega

/-- [proved-derived; formal-checked] **Two channels do not locate one defect**: `(1, 1)` is a
kernel vector of support `2`. -/
theorem menuTwo_not_locates : ¬ Locates (menu (A := ZMod 4) twoSrc twoTgt) 1 := by
  rw [locates_iff_separates]
  intro h
  have h1 := h (fun _ => 1) (by funext c; simp [menu_apply])
    ((card_le_univ _).trans (by simp))
  have h10 : (1 : ZMod 4) = 0 := congrFun h1 0
  exact absurd h10 (by decide)

/-! ## 3. All cycles of a connected complex -/

section Cycles

variable {V E F : Type*} (K : ParametricComplex V E F) {A : Type*} [AddCommGroup A]

/-- [definition] **The menu of all cycles**: a defect read on every closed aeon. -/
def cycleReading : (E → A) →+ ((Σ u : V, Aeon K u u) → A) where
  toFun ω := fun c => wordReading ω c.2.steps
  map_zero' := by
    funext c
    exact wordReading_zero c.2.steps
  map_add' ω η := by
    funext c
    exact wordReading_add ω η c.2.steps

theorem cycleReading_apply (ω : E → A) (c : Σ u : V, Aeon K u u) :
    cycleReading K ω c = wordReading ω c.2.steps := rfl

variable {K}

/-- [proved-standard; formal-checked] **`ker C = im d₀`** for the menu of all cycles of a complex
whose occurrences are reached by aeons from one occurrence (`ClockJoin.join_iff_silent`). -/
theorem cycleReading_eq_zero_iff (base : V) (path : ∀ v, Aeon K base v) (ω : E → A) :
    cycleReading K ω = 0 ↔ ∃ φ : V → A, ω = exactForm K φ := by
  refine Iff.trans ?_ (ClockJoin.join_iff_silent ω base path).symm
  constructor
  · intro h u γ
    exact (cycleReading_apply K ω ⟨u, γ⟩).symm.trans (congrFun h ⟨u, γ⟩)
  · intro h
    funext c
    rw [cycleReading_apply]
    exact h c.1 c.2

end Cycles

/-! ## 4. The min-cut form -/

section Cut

variable {V E F : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (K : ParametricComplex V E F) {A : Type*} [AddCommGroup A] [DecidableEq A]

/-- [definition] **The cut of an occurrence set** `S`: the edges with exactly one end in `S`. -/
def cut (S : Finset V) : Finset E := univ.filter fun e => ¬(K.src e ∈ S ↔ K.tgt e ∈ S)

variable {K}

theorem mem_cut {S : Finset V} {e : E} : e ∈ cut K S ↔ ¬(K.src e ∈ S ↔ K.tgt e ∈ S) := by
  simp [cut]

/-- [proved-standard] A chained word from inside `S` to outside it crosses the cut of `S`. -/
theorem exists_cut_edge {S : Finset V} {u v : V} {w : List (E × Bool)} (hw : K.Chained u w v)
    (hu : u ∈ S) (hv : v ∉ S) : ∃ e, e ∈ cut K S := by
  induction w generalizing u with
  | nil =>
    rw [ParametricComplex.chained_nil] at hw
    subst hw
    exact absurd hu hv
  | cons s w ih =>
    obtain ⟨h1, h2⟩ := hw
    by_cases hf : K.finish s ∈ S
    · exact ih h2 hf
    · rcases s with ⟨e, _ | _⟩ <;>
        simp [ParametricComplex.start, ParametricComplex.finish] at h1 hf <;>
        subst h1 <;>
        exact ⟨e, mem_cut.mpr (by simp [hu, hf])⟩

/-- [definition] The value `a` on `S` and `0` off it. -/
def lift (S : Finset V) (a : A) : V → A := fun x => if x ∈ S then a else 0

/-- [proved-standard] The support of `d₀` of the lift of `S` is the cut of `S`. -/
theorem supp_exactForm_lift {a : A} (ha : a ≠ 0) (S : Finset V) :
    supp (exactForm K (lift S a)) = cut K S := by
  ext e
  rw [mem_supp, mem_cut]
  simp only [exactForm, lift]
  by_cases hs : K.src e ∈ S <;> by_cases ht : K.tgt e ∈ S <;> simp [hs, ht, ha]

/-- [definition] The level set of `φ` at the value it takes at `b`. -/
def level (φ : V → A) (b : V) : Finset V := univ.filter fun x => φ x = φ b

/-- [proved-standard] The cut of a level set of `φ` lies in the support of `d₀ φ`. -/
theorem cut_level_subset (φ : V → A) (b : V) : cut K (level φ b) ⊆ supp (exactForm K φ) := by
  intro e he
  rw [mem_cut] at he
  rw [mem_supp]
  intro h0
  apply he
  have h : φ (K.tgt e) = φ (K.src e) := sub_eq_zero.mp h0
  simp [level, h]

/-- [proved-standard; formal-checked] **The min-cut form**: for a menu with `ker C = im d₀` on a
complex whose occurrences are reached by aeons from one occurrence, and a nonzero value in `A`,
defects on at most `k` edges are located uniquely iff every nonempty proper occurrence set has more
than `2k` edges in its cut. -/
theorem locates_iff_minCut {B : Type*} [AddCommGroup B] (C : (E → A) →+ B)
    (hker : ∀ ω, C ω = 0 ↔ ∃ φ : V → A, ω = exactForm K φ) (base : V)
    (path : ∀ v, Aeon K base v) {a : A} (ha : a ≠ 0) (k : ℕ) :
    Locates C k ↔ ∀ S : Finset V, S.Nonempty → S ≠ univ → 2 * k < (cut K S).card := by
  rw [locates_iff_separates]
  constructor
  · intro hsep S hS hSu
    by_contra hle
    push Not at hle
    have h0 := hsep (exactForm K (lift S a)) ((hker _).mpr ⟨_, rfl⟩)
      (by rw [supp_exactForm_lift ha]; exact hle)
    obtain ⟨x, hx⟩ := hS
    obtain ⟨y, hy⟩ : ∃ y, y ∉ S := by
      by_contra h
      push Not at h
      exact hSu (eq_univ_of_forall h)
    obtain ⟨e, he⟩ := exists_cut_edge ((path x).reverse.concat (path y)).chained hx hy
    rw [← supp_exactForm_lift ha, h0] at he
    simp [mem_supp] at he
  · intro hcut v hv hs
    obtain ⟨φ, rfl⟩ := (hker v).mp hv
    by_contra hne
    obtain ⟨e, he⟩ : ∃ e, exactForm K φ e ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (funext h)
    have h1 : (level φ (K.src e)).Nonempty := ⟨K.src e, by simp [level]⟩
    have h2 : level φ (K.src e) ≠ univ := by
      intro h
      have ht : K.tgt e ∈ level φ (K.src e) := by
        rw [h]
        exact mem_univ _
      simp only [level, mem_filter, mem_univ, true_and] at ht
      exact he (by simp [exactForm, ht])
    have hgt := hcut _ h1 h2
    have hle := card_le_card (cut_level_subset (K := K) φ (K.src e))
    omega

/-- [proved-standard; formal-checked] **All cycles of a connected complex**: defects on at most `k`
edges are located uniquely by their readings on every closed aeon iff every edge cut has more than
`2k` edges. -/
theorem cycleReading_locates_iff (base : V) (path : ∀ v, Aeon K base v) {a : A} (ha : a ≠ 0)
    (k : ℕ) :
    Locates (cycleReading (A := A) K) k ↔
      ∀ S : Finset V, S.Nonempty → S ≠ univ → 2 * k < (cut K S).card :=
  locates_iff_minCut (cycleReading K) (cycleReading_eq_zero_iff base path) base path ha k

end Cut

end Holonics.Holon.Syndrome
