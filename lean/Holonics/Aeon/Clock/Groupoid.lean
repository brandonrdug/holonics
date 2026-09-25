import Mathlib.CategoryTheory.Groupoid
import Mathlib.Tactic

/-!
# The aeon groupoid

[definition] `docs/ELEMENTARY_OBJECTS.md` §12 and the aeon record (A1). A Holarchy's parametric
orientation is carried by an oriented cell complex up to dimension two, the
`ParametricComplex`: its vertices are **occurrences**, its oriented edges are elementary passages
of the motion, and each two-cell is bounded by a closed word of signed edges (a place where two
passages commute, or any declared circuit). An **aeon** from occurrence `u` to occurrence `v` is a
chained word of signed edges: a 1-chain of the motion that keeps its order, so it retains the
winding a bare endpoint pair forgets. It is not an interval of a privileged clock. The lift of the
navigators' joint clock torus is one such complex (`Aeon/Clock/Winding.clockLift`).

[proved-derived; formal-checked] What is proved.

1. **Composition and reversal.** Aeons compose by concatenation (`Aeon.concat`), associatively and
   with the motionless aeon as unit (`concat_assoc`, `rest_concat`, `concat_rest`); orientation
   reversal is an involution that reverses the order of a composite (`reverse_reverse`,
   `reverse_concat`).
2. **Homotopy.** The elementary moves insert a backtrack `s s⁻¹` or a two-cell boundary (either
   orientation) into a word (`Move`); `Homotopic` is their equivalence closure. It is a congruence
   for concatenation and reversal (`homotopic_concat`, `homotopic_reverse`), and an aeon followed
   by its reversal is homotopic to rest (`concat_reverse_homotopic`,
   `reverse_concat_homotopic`).
3. **The groupoid.** Occurrences are the objects and homotopy classes of aeons the arrows:
   `instGroupoid` is a Mathlib `CategoryTheory.Groupoid` whose composition is concatenation and
   whose inverse is reversal.

Scope: combinatorial words over arbitrary vertex, edge and cell types. Continuous paths,
reparametrization and the smooth fundamental groupoid are outside this module. No `axiom`, no
`sorry`, no `native_decide`.
-/

set_option linter.dupNamespace false

namespace Holonics.Aeon.Clock.Groupoid

/-! ## 1. The parametric complex and its words -/

/-- [definition] The oriented complex carrying a Holarchy's parametric orientation: occurrences
`V`, oriented edges `E` running from `src` to `tgt`, and two-cells `F`, each bounded by a word of
signed edges based at `base`. A signed edge `(e, true)` runs along `e`, `(e, false)` against it. -/
structure ParametricComplex (V E F : Type*) where
  src : E → V
  tgt : E → V
  base : F → V
  boundary : F → List (E × Bool)

variable {V E F : Type*}

/-- [definition] A signed edge traversed the other way. -/
def reverseStep (s : E × Bool) : E × Bool := (s.1, !s.2)

@[simp] theorem reverseStep_reverseStep (s : E × Bool) : reverseStep (reverseStep s) = s := by
  rcases s with ⟨e, b⟩
  simp [reverseStep]

/-- [definition] The reversed word: the steps in reverse order, each traversed the other way. -/
def reverseWord (w : List (E × Bool)) : List (E × Bool) := (w.map reverseStep).reverse

@[simp] theorem reverseWord_nil : reverseWord ([] : List (E × Bool)) = [] := rfl

theorem reverseWord_cons (s : E × Bool) (w : List (E × Bool)) :
    reverseWord (s :: w) = reverseWord w ++ [reverseStep s] := by
  simp [reverseWord]

theorem reverseWord_append (p q : List (E × Bool)) :
    reverseWord (p ++ q) = reverseWord q ++ reverseWord p := by
  simp [reverseWord]

@[simp] theorem reverseWord_reverseWord (w : List (E × Bool)) :
    reverseWord (reverseWord w) = w := by
  simp [reverseWord, List.map_reverse, Function.comp_def]

namespace ParametricComplex

variable (K : ParametricComplex V E F)

/-- [definition] The occurrence a signed edge leaves. -/
def start (s : E × Bool) : V := if s.2 then K.src s.1 else K.tgt s.1

/-- [definition] The occurrence a signed edge reaches. -/
def finish (s : E × Bool) : V := if s.2 then K.tgt s.1 else K.src s.1

@[simp] theorem start_flip (s : E × Bool) : K.start (reverseStep s) = K.finish s := by
  rcases s with ⟨e, _ | _⟩ <;> simp [start, finish, reverseStep]

@[simp] theorem finish_flip (s : E × Bool) : K.finish (reverseStep s) = K.start s := by
  rcases s with ⟨e, _ | _⟩ <;> simp [start, finish, reverseStep]

/-- [definition] A word is chained from `u` to `v`: each step leaves where the previous one
arrived. -/
def Chained : V → List (E × Bool) → V → Prop
  | u, [], v => u = v
  | u, s :: w, v => K.start s = u ∧ Chained (K.finish s) w v

@[simp] theorem chained_nil (u v : V) : K.Chained u [] v ↔ u = v := Iff.rfl

@[simp] theorem chained_cons (u v : V) (s : E × Bool) (w : List (E × Bool)) :
    K.Chained u (s :: w) v ↔ K.start s = u ∧ K.Chained (K.finish s) w v := Iff.rfl

/-- [proved-derived; formal-checked] Chained words concatenate. -/
theorem chained_append {u w v : V} {p q : List (E × Bool)} (hp : K.Chained u p w)
    (hq : K.Chained w q v) : K.Chained u (p ++ q) v := by
  induction p generalizing u with
  | nil =>
    rw [chained_nil] at hp
    subst hp
    simpa using hq
  | cons s p ih =>
    obtain ⟨h1, h2⟩ := hp
    exact ⟨h1, ih h2⟩

/-- [proved-derived; formal-checked] A chained word read backwards is chained the other way. -/
theorem chained_reverseWord {u v : V} {p : List (E × Bool)} (hp : K.Chained u p v) :
    K.Chained v (reverseWord p) u := by
  induction p generalizing u with
  | nil =>
    rw [chained_nil] at hp
    subst hp
    simp
  | cons s p ih =>
    obtain ⟨h1, h2⟩ := hp
    rw [reverseWord_cons]
    refine K.chained_append (ih h2) ?_
    simp [h1]

/-- [definition] Every two-cell boundary is a loop at its base occurrence. -/
def WellFormed : Prop := ∀ f, K.Chained (K.base f) (K.boundary f) (K.base f)

end ParametricComplex

/-! ## 2. Aeons: composition and reversal -/

/-- [definition] An **aeon** from occurrence `u` to occurrence `v`: a chained word of signed edges,
the ordered 1-chain of the motion between two occurrences. -/
@[ext] structure Aeon (K : ParametricComplex V E F) (u v : V) where
  steps : List (E × Bool)
  chained : K.Chained u steps v

namespace Aeon

variable {K : ParametricComplex V E F}

/-- [definition] The motionless aeon at an occurrence. -/
def rest (u : V) : Aeon K u u := ⟨[], rfl⟩

/-- [definition] Concatenation: the first aeon, then the second. -/
def concat {u w v : V} (γ : Aeon K u w) (δ : Aeon K w v) : Aeon K u v :=
  ⟨γ.steps ++ δ.steps, K.chained_append γ.chained δ.chained⟩

/-- [definition] Orientation reversal `Rγ`. -/
def reverse {u v : V} (γ : Aeon K u v) : Aeon K v u :=
  ⟨reverseWord γ.steps, K.chained_reverseWord γ.chained⟩

/-- [proved-derived; formal-checked] Concatenation is associative. -/
theorem concat_assoc {u w x v : V} (γ : Aeon K u w) (δ : Aeon K w x) (ε : Aeon K x v) :
    (γ.concat δ).concat ε = γ.concat (δ.concat ε) := by
  ext1
  simp [concat]

/-- [proved-derived; formal-checked] Rest is a left unit. -/
theorem rest_concat {u v : V} (γ : Aeon K u v) : (rest u).concat γ = γ := by
  ext1
  simp [concat, rest]

/-- [proved-derived; formal-checked] Rest is a right unit. -/
theorem concat_rest {u v : V} (γ : Aeon K u v) : γ.concat (rest v) = γ := by
  ext1
  simp [concat, rest]

/-- [proved-derived; formal-checked] Reversal is an involution. -/
theorem reverse_reverse {u v : V} (γ : Aeon K u v) : γ.reverse.reverse = γ := by
  ext1
  simp [reverse]

/-- [proved-derived; formal-checked] Reversal reverses the order of a composite. -/
theorem reverse_concat {u w v : V} (γ : Aeon K u w) (δ : Aeon K w v) :
    (γ.concat δ).reverse = δ.reverse.concat γ.reverse := by
  ext1
  simp [reverse, concat, reverseWord_append]

/-- [proved-derived; formal-checked] Rest reversed is rest. -/
theorem reverse_rest (u : V) : (rest u : Aeon K u u).reverse = rest u := by
  ext1
  simp [reverse, rest]

end Aeon

/-! ## 3. Homotopy of aeons -/

/-- [definition] The elementary moves: insert a backtrack `s s⁻¹`, or insert the boundary of a
two-cell in either orientation. -/
inductive Move (K : ParametricComplex V E F) : List (E × Bool) → List (E × Bool) → Prop
  | backtrack (a b : List (E × Bool)) (s : E × Bool) :
      Move K (a ++ b) (a ++ s :: reverseStep s :: b)
  | face (a b : List (E × Bool)) (f : F) : Move K (a ++ b) (a ++ K.boundary f ++ b)
  | faceReversed (a b : List (E × Bool)) (f : F) :
      Move K (a ++ b) (a ++ reverseWord (K.boundary f) ++ b)

/-- [definition] Two words are homotopic when the elementary moves connect them. -/
def WordHomotopic (K : ParametricComplex V E F) : List (E × Bool) → List (E × Bool) → Prop :=
  Relation.EqvGen (Move K)

/-- [definition] Two aeons with the same endpoints are **homotopic** when their words are. -/
def Homotopic {K : ParametricComplex V E F} {u v : V} (γ δ : Aeon K u v) : Prop :=
  WordHomotopic K γ.steps δ.steps

section Homotopy

variable {K : ParametricComplex V E F}

/-- [proved-derived; formal-checked] An elementary move survives any surrounding context. -/
theorem move_context {p q : List (E × Bool)} (h : Move K p q) (c d : List (E × Bool)) :
    Move K (c ++ p ++ d) (c ++ q ++ d) := by
  cases h with
  | backtrack a b s =>
    have := Move.backtrack (K := K) (c ++ a) (b ++ d) s
    simpa [List.append_assoc] using this
  | face a b f =>
    have := Move.face (K := K) (c ++ a) (b ++ d) f
    simpa [List.append_assoc] using this
  | faceReversed a b f =>
    have := Move.faceReversed (K := K) (c ++ a) (b ++ d) f
    simpa [List.append_assoc] using this

/-- [proved-derived; formal-checked] Homotopy of words survives any surrounding context. -/
theorem wordHomotopic_context {p q : List (E × Bool)} (h : WordHomotopic K p q)
    (c d : List (E × Bool)) : WordHomotopic K (c ++ p ++ d) (c ++ q ++ d) := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (move_context hxy c d)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- [proved-derived; formal-checked] Reversing a word maps an elementary move to one. -/
theorem move_reverseWord {p q : List (E × Bool)} (h : Move K p q) :
    Move K (reverseWord p) (reverseWord q) := by
  cases h with
  | backtrack a b s =>
    have := Move.backtrack (K := K) (reverseWord b) (reverseWord a) s
    simpa [reverseWord_append, reverseWord_cons, List.append_assoc] using this
  | face a b f =>
    have := Move.faceReversed (K := K) (reverseWord b) (reverseWord a) f
    simpa [reverseWord_append, List.append_assoc] using this
  | faceReversed a b f =>
    have := Move.face (K := K) (reverseWord b) (reverseWord a) f
    simpa [reverseWord_append, List.append_assoc] using this

/-- [proved-derived; formal-checked] Homotopy of words survives reversal. -/
theorem wordHomotopic_reverseWord {p q : List (E × Bool)} (h : WordHomotopic K p q) :
    WordHomotopic K (reverseWord p) (reverseWord q) := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (move_reverseWord hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- [proved-derived; formal-checked] A word followed by its reversal is homotopic to the empty
word: the backtracks cancel from the middle outwards. -/
theorem wordHomotopic_append_reverseWord (w : List (E × Bool)) :
    WordHomotopic K (w ++ reverseWord w) [] := by
  induction w with
  | nil => exact Relation.EqvGen.refl _
  | cons s w ih =>
    have hmid := wordHomotopic_context ih [s] [reverseStep s]
    have hback : WordHomotopic K [s, reverseStep s] [] :=
      Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (by
        simpa using Move.backtrack (K := K) [] [] s))
    have heq : s :: w ++ reverseWord (s :: w) = [s] ++ (w ++ reverseWord w) ++ [reverseStep s] := by
      simp [reverseWord_cons]
    rw [heq]
    exact Relation.EqvGen.trans _ _ _ hmid hback

theorem homotopic_refl {u v : V} (γ : Aeon K u v) : Homotopic γ γ := Relation.EqvGen.refl _

theorem homotopic_symm {u v : V} {γ δ : Aeon K u v} (h : Homotopic γ δ) : Homotopic δ γ :=
  Relation.EqvGen.symm _ _ h

theorem homotopic_trans {u v : V} {γ δ ε : Aeon K u v} (h₁ : Homotopic γ δ)
    (h₂ : Homotopic δ ε) : Homotopic γ ε :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

/-- [proved-derived; formal-checked] Homotopy is a congruence for concatenation. -/
theorem homotopic_concat {u w v : V} {γ γ' : Aeon K u w} {δ δ' : Aeon K w v}
    (hγ : Homotopic γ γ') (hδ : Homotopic δ δ') :
    Homotopic (γ.concat δ) (γ'.concat δ') := by
  have h1 : WordHomotopic K (γ.steps ++ δ.steps) (γ'.steps ++ δ.steps) := by
    simpa using wordHomotopic_context hγ [] δ.steps
  have h2 : WordHomotopic K (γ'.steps ++ δ.steps) (γ'.steps ++ δ'.steps) := by
    simpa using wordHomotopic_context hδ γ'.steps []
  exact Relation.EqvGen.trans _ _ _ h1 h2

/-- [proved-derived; formal-checked] Homotopy is a congruence for reversal. -/
theorem homotopic_reverse {u v : V} {γ δ : Aeon K u v} (h : Homotopic γ δ) :
    Homotopic γ.reverse δ.reverse :=
  wordHomotopic_reverseWord h

/-- [proved-derived; formal-checked] **An aeon followed by its reversal is homotopic to rest.** -/
theorem concat_reverse_homotopic {u v : V} (γ : Aeon K u v) :
    Homotopic (γ.concat γ.reverse) (Aeon.rest u) :=
  wordHomotopic_append_reverseWord γ.steps

/-- [proved-derived; formal-checked] **The reversal followed by the aeon is homotopic to rest.** -/
theorem reverse_concat_homotopic {u v : V} (γ : Aeon K u v) :
    Homotopic (γ.reverse.concat γ) (Aeon.rest v) := by
  have := wordHomotopic_append_reverseWord (K := K) (reverseWord γ.steps)
  simpa [Homotopic, Aeon.concat, Aeon.reverse, Aeon.rest] using this

end Homotopy

/-! ## 4. The groupoid of occurrences and aeon classes -/

/-- [definition] The occurrences of a parametric complex, as the objects of its aeon groupoid. -/
def Occurrence (_K : ParametricComplex V E F) : Type _ := V

/-- [definition] Homotopy as a setoid on the aeons between two occurrences. -/
def homotopySetoid (K : ParametricComplex V E F) (u v : V) : Setoid (Aeon K u v) where
  r := Homotopic
  iseqv := ⟨homotopic_refl, homotopic_symm, homotopic_trans⟩

/-- [definition] An aeon class: an aeon up to homotopy. -/
def AeonClass (K : ParametricComplex V E F) (u v : V) : Type _ :=
  Quotient (homotopySetoid K u v)

/-- [definition] The class of an aeon. -/
def AeonClass.mk {K : ParametricComplex V E F} {u v : V} (γ : Aeon K u v) : AeonClass K u v :=
  Quotient.mk (homotopySetoid K u v) γ

/-- [proved-derived; formal-checked] Two aeons have one class exactly when they are homotopic. -/
theorem AeonClass.mk_eq_mk {K : ParametricComplex V E F} {u v : V} {γ δ : Aeon K u v} :
    AeonClass.mk γ = AeonClass.mk δ ↔ Homotopic γ δ :=
  Quotient.eq (r := homotopySetoid K u v)

open CategoryTheory

/-- [proved-derived; formal-checked] **The aeon groupoid.** Occurrences are the objects, aeon
classes the arrows, concatenation the composition, rest the identity and reversal the inverse. -/
instance instGroupoid (K : ParametricComplex V E F) : Groupoid (Occurrence K) where
  Hom u v := AeonClass K u v
  id u := AeonClass.mk (Aeon.rest u)
  comp {u w v} f g := Quotient.map₂ (sa := homotopySetoid K u w) (sb := homotopySetoid K w v)
    (sc := homotopySetoid K u v) Aeon.concat (fun _ _ h₁ _ _ h₂ => homotopic_concat h₁ h₂) f g
  id_comp {u v} f := by
    induction f using Quotient.inductionOn with
    | h γ => exact congrArg AeonClass.mk (Aeon.rest_concat γ)
  comp_id {u v} f := by
    induction f using Quotient.inductionOn with
    | h γ => exact congrArg AeonClass.mk (Aeon.concat_rest γ)
  assoc {u w x v} f g h := by
    induction f using Quotient.inductionOn with
    | h γ =>
      induction g using Quotient.inductionOn with
      | h δ =>
        induction h using Quotient.inductionOn with
        | h ε => exact congrArg AeonClass.mk (Aeon.concat_assoc γ δ ε)
  inv {u v} f := Quotient.map (sa := homotopySetoid K u v) (sb := homotopySetoid K v u)
    Aeon.reverse (fun _ _ h => homotopic_reverse h) f
  inv_comp {u v} f := by
    induction f using Quotient.inductionOn with
    | h γ => exact AeonClass.mk_eq_mk.mpr (reverse_concat_homotopic γ)
  comp_inv {u v} f := by
    induction f using Quotient.inductionOn with
    | h γ => exact AeonClass.mk_eq_mk.mpr (concat_reverse_homotopic γ)

end Holonics.Aeon.Clock.Groupoid
