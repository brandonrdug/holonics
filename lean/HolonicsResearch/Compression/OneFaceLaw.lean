import Mathlib.Algebra.DualNumber
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Congruence.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Setoid.Basic

/-!
# One face law: a face conserved by an operation is a congruence, and its coarsest conserved refinement is syntactic

Source: #410's box "One face law across operations (#404)", from the record
`2026-10-24_ONE_FACE_LAW_A_FACE_IS_A_CONGRUENCE_SO_LANGUAGE_ARITHMETIC_AND_ANY_OPERATION_ARE_READ_BY_ONE_CONTACT`,
§§1, 2, 3 and 5 (atlas `face.conserved-is-congruence`, `lang.seam-state-carry`, `face.algebra-census`), with the
fibre clause of the association box (`arith.association-is-evaluation`).

A face `q` is a receiver's reading, a map out of what it reads; it is **conserved** by an operation `T` when the
result's face is a function of the operands' faces, `q (T x y) = T_q (q x) (q y)`.

[proved-standard; formal-checked] What is proved.

1. **The law** (§1). For an operation of any arity (`Fin n → α`, and any index type), conservation, the respect of
   `T` on equal faces, the existence of `T_q` with `q ∘ T = T_q ∘ (q ∘ ·)`, and the fibre being one point are one
   condition (`conserved_iff_exists`, `conservedN_iff_exists`, `conserved_iff_fibre`). On a multiplication the kernel
   of a conserved face is a congruence (`faceCon`, Mathlib `Con`), and `q` factors through the quotient algebra by an
   injective map that carries the quotient's product to `T_q` (`factor_through_quotient`).
2. **Closure** (§1, item 2). Conserved faces jointly injective on a window read `T` there: a release in the window
   whose faces agree with `T_q` of the operands' faces is `T x y` (`closure_reads_T`; the integer case is the check
   loop, `Mathematics/CheckLoop.check_loop_decides`).
3. **Language** (§2). Over the letters `{t, h, a}`, "contains `th`" is not conserved by concatenation
   (`th_not_conserved`: `t · h` and `a · h` have equal faces at the operands and differ at the result); carrying the
   seam (ends in `t`, starts with `h`) and the unit conserves it (`th_append`, `seam_conserved`). The two-sided
   (syntactic) congruence of the face has exactly six classes, the empty word, has `th`, and the four `th`-free
   classes by whether the word starts with `h` and ends in `t` (`syntactic_iff`, `card_syntactic`); the right
   congruence a left-to-right reader keeps has three, has `th`, `th`-free ending in `t`, and the rest
   (`right_iff`, `card_right`). Four contexts, `{ε, t} × {ε, h}`, separate every syntactic class, and two suffixes,
   `{ε, h}`, every right class.
4. **Other algebras** (§3). The jet `(f a, f′ a)` is conserved by products: it is a monoid map into the dual numbers
   (`jet_mul`, Leibniz), while the derivative alone is not (`deriv_not_conserved`). `det` is conserved by the matrix
   product and the trace is not, even beside `det` (`trace_not_conserved`, `trace_det_not_conserved`); the trace of a
   product is the pairing `tr(AB) = ⟨A, Bᵀ⟩` of the whole operands (`trace_mul_eq_pairing`). On permutations the sign
   is conserved and the cycle type is not (`cycleType_not_conserved`).

Limits. Birkhoff's subdirect representation for a general algebra is read here only as its consequence on a window
(item 2). The census numbers of the record (784 of 3,025 rectangles with a nonzero four-cycle, the 81 refined face
pairs, 25 of 25 plural trace pairs, 218 of 256 with `det`, 80 of 81 plural derivative pairs) are its receipts, not
proved here: the module proves the laws and one witness of each failure. The derivative is read on functions
`ℝ → ℝ` rather than on the record's integer polynomials read at `2`.

The computational object is the helical pair interaction: a face that is not conserved needs a pair contact at the
seam, and the seam state (the carry in arithmetic, ends-in-`t` and starts-with-`h` in language) is what that contact
carries. Of the winding guide's six general objects this touches faces and placement (the congruence and its
quotient) and the pair (the seam); the helix, the cell holonomy, the tube and the tower thread stay attached.

Consumers: the atlas rows `face.conserved-is-congruence`, `lang.seam-state-carry`, `face.algebra-census` and
`arith.association-is-evaluation`, and the #410 boxes "One face law across operations" and "Association is
evaluation".

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.OneFaceLaw

/-! ## 1. The law -/

section Law

variable {α β : Type*}

/-- [definition] A face `q` is conserved by a binary operation `T` when equal faces of the operands give equal
faces of the result. -/
def Conserved (q : α → β) (T : α → α → α) : Prop :=
  ∀ x x' y y', q x = q x' → q y = q y' → q (T x y) = q (T x' y')

/-- [proved-standard; formal-checked] Conservation is the existence of the face's own operation:
`q ∘ T = T_q ∘ (q × q)`. -/
theorem conserved_iff_exists (q : α → β) (T : α → α → α) :
    Conserved q T ↔ ∃ Tq : β → β → β, ∀ x y, q (T x y) = Tq (q x) (q y) := by
  constructor
  · intro h
    classical
    refine ⟨fun u v => if hu : ∃ x, q x = u then if hv : ∃ y, q y = v then
      q (T hu.choose hv.choose) else u else u, fun x y => ?_⟩
    have hu : ∃ x', q x' = q x := ⟨x, rfl⟩
    have hv : ∃ y', q y' = q y := ⟨y, rfl⟩
    beta_reduce
    rw [dif_pos hu, dif_pos hv]
    exact h _ _ _ _ hu.choose_spec.symm hv.choose_spec.symm
  · rintro ⟨Tq, hT⟩ x x' y y' hx hy
    rw [hT, hT, hx, hy]

/-- [proved-standard; formal-checked] The fibre form (the association box): `q` descends through `T` exactly when,
for every pair of faces, the results of all operands carrying those faces read one face. -/
theorem conserved_iff_fibre (q : α → β) (T : α → α → α) :
    Conserved q T ↔ ∀ f g : β, ∀ r ∈ {z | ∃ x y, q x = f ∧ q y = g ∧ z = q (T x y)},
      ∀ r' ∈ {z | ∃ x y, q x = f ∧ q y = g ∧ z = q (T x y)}, r = r' := by
  constructor
  · rintro h f g _ ⟨x, y, hx, hy, rfl⟩ _ ⟨x', y', hx', hy', rfl⟩
    exact h _ _ _ _ (hx.trans hx'.symm) (hy.trans hy'.symm)
  · intro h x x' y y' hx hy
    exact h (q x) (q y) _ ⟨x, y, rfl, rfl, rfl⟩ _ ⟨x', y', hx.symm, hy.symm, rfl⟩

/-- [definition] Conservation for an operation of any arity, its operands indexed by `ι`. -/
def ConservedN {ι : Type*} (q : α → β) (T : (ι → α) → α) : Prop :=
  ∀ xs ys : ι → α, (∀ i, q (xs i) = q (ys i)) → q (T xs) = q (T ys)

/-- [proved-standard; formal-checked] At any arity, conservation is the existence of `T_q` with
`q ∘ T = T_q ∘ (q ∘ ·)` (a face with at least one value). -/
theorem conservedN_iff_exists {ι : Type*} [Nonempty β] (q : α → β) (T : (ι → α) → α) :
    ConservedN q T ↔ ∃ Tq : (ι → β) → β, ∀ xs, q (T xs) = Tq (q ∘ xs) := by
  constructor
  · intro h
    classical
    refine ⟨fun us => if hu : ∃ xs : ι → α, q ∘ xs = us then q (T hu.choose)
      else Classical.arbitrary β, fun xs => ?_⟩
    have hu : ∃ ys : ι → α, q ∘ ys = q ∘ xs := ⟨xs, rfl⟩
    beta_reduce
    rw [dif_pos hu]
    exact h _ _ fun i => (congrFun hu.choose_spec i).symm
  · rintro ⟨Tq, hT⟩ xs ys h
    rw [hT, hT]
    exact congrArg Tq (funext h)

end Law

/-! ### A conserved face of a product is a congruence -/

section Congruence

variable {M β : Type*} [Mul M]

/-- [definition] The kernel of a face conserved by the product, as a congruence (Mathlib `Con`). -/
def faceCon (q : M → β) (hq : Conserved q (· * ·)) : Con M where
  toSetoid := Setoid.ker q
  mul' := fun {_ _ _ _} h1 h2 => hq _ _ _ _ h1 h2

/-- [proved-standard; formal-checked] Two elements are congruent exactly when their faces agree. -/
theorem faceCon_iff (q : M → β) (hq : Conserved q (· * ·)) (x y : M) :
    faceCon q hq x y ↔ q x = q y := Iff.rfl

/-- [proved-standard; formal-checked] A conserved face factors through the quotient algebra by an injective map,
and that map carries the quotient's product to the face's own operation `T_q`. -/
theorem factor_through_quotient (q : M → β) (hq : Conserved q (· * ·)) {Tq : β → β → β}
    (hT : ∀ x y, q (x * y) = Tq (q x) (q y)) :
    ∃ f : (faceCon q hq).Quotient → β, Function.Injective f ∧ (∀ x : M, f (↑x : (faceCon q hq).Quotient) = q x) ∧
      ∀ a b, f (a * b) = Tq (f a) (f b) := by
  refine ⟨fun a => Quotient.liftOn' a q fun _ _ h => h, ?_, fun _ => rfl, ?_⟩
  · intro a b hab
    induction a using Quotient.inductionOn' with | h x => ?_
    induction b using Quotient.inductionOn' with | h y => ?_
    exact Quotient.sound' hab
  · intro a b
    induction a using Quotient.inductionOn' with | h x => ?_
    induction b using Quotient.inductionOn' with | h y => ?_
    exact hT x y

end Congruence

/-! ## 2. Closure: jointly injective conserved faces read the operation -/

section Closure

variable {α ι : Type*} {β : ι → Type*}

/-- [proved-standard; formal-checked] Conserved faces jointly injective on a window read `T` there: a release `r` in
the window whose every face is `T_q` of the operands' faces is `T x y`. -/
theorem closure_reads_T (q : ∀ i, α → β i) (T : α → α → α) (Tq : ∀ i, β i → β i → β i)
    (hT : ∀ i x y, q i (T x y) = Tq i (q i x) (q i y)) (W : Set α)
    (hinj : ∀ r ∈ W, ∀ r' ∈ W, (∀ i, q i r = q i r') → r = r') {x y r : α} (hr : r ∈ W) (hxy : T x y ∈ W)
    (hcheck : ∀ i, q i r = Tq i (q i x) (q i y)) : r = T x y :=
  hinj r hr _ hxy fun i => (hcheck i).trans (hT i x y).symm

end Closure

/-! ## 3. Language: the seam is concatenation's carry -/

section Language

/-- [definition] The census's three letters. -/
inductive Letter
  | t
  | h
  | a
  deriving DecidableEq

open Letter

/-- [definition] The face "contains `th`". -/
def th : List Letter → Bool
  | [] => false
  | c :: rest => (c == t && rest.head? == some h) || th rest

/-- [definition] The seam's left half: the word ends in `t`. -/
def endsT (w : List Letter) : Bool := w.getLast? == some t

/-- [definition] The seam's right half: the word starts with `h`. -/
def startsH (w : List Letter) : Bool := w.head? == some h

/-- [proved-derived; formal-checked] Concatenation reads `th` from the two operands and the seam:
`th(xy) = th x ∨ th y ∨ (x ends in t ∧ y starts with h)`. -/
theorem th_append (x y : List Letter) : th (x ++ y) = (th x || th y || (endsT x && startsH y)) := by
  induction x with
  | nil => simp [th, endsT]
  | cons c x ih =>
    cases x with
    | nil => cases c <;> simp [th, endsT, startsH] <;> cases y.head? <;> simp [Bool.or_comm]
    | cons d x =>
      simp only [List.cons_append, th] at ih ⊢
      rw [ih]
      simp only [List.head?_cons, endsT, List.getLast?_cons_cons]
      cases (c == t && some d == some h) <;> simp

/-- [proved-derived; formal-checked] "Contains `th`" is not conserved by concatenation: `t` and `a` both lack it,
and so does `h`, while `t · h` has it and `a · h` does not. -/
theorem th_not_conserved : ¬ Conserved th (· ++ ·) := by
  intro hc
  have := hc [t] [a] [h] [h] rfl rfl
  simp [th] at this

/-- [definition] The seam face: the unit, `th`, starts with `h`, ends in `t`. -/
def seamFace (w : List Letter) : Bool × Bool × Bool × Bool := (w.isEmpty, th w, startsH w, endsT w)

/-- [proved-derived; formal-checked] Carrying the seam and the unit conserves the face: the refined face of `xy` is
a function of the refined faces of `x` and `y`. -/
theorem seam_conserved : Conserved seamFace (· ++ ·) := by
  rw [conserved_iff_exists]
  refine ⟨fun ⟨ex, tx, sx, ex'⟩ ⟨ey, ty, sy, ey'⟩ =>
    (ex && ey, tx || ty || (ex' && sy), if ex then sy else sx, if ey then ex' else ey'), fun x y => ?_⟩
  simp only [seamFace, th_append]
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ ?_))
  · cases x <;> cases y <;> rfl
  · cases x <;> simp [startsH]
  · cases y with
    | nil => simp
    | cons d y => simp [endsT, List.getLast?_append]

/-- [definition] The two-sided (syntactic) congruence of `th`: two words are equal in it when no context tells them
apart. -/
def Syn (x y : List Letter) : Prop := ∀ u v, th (u ++ x ++ v) = th (u ++ y ++ v)

/-- [definition] The six classes of the syntactic congruence. -/
inductive SynClass
  | unit
  | hasTH
  | free (startsWithH endsInT : Bool)
  deriving DecidableEq, Fintype

/-- [definition] The class of a word: the empty word, has `th`, or `th`-free by its seam. -/
def syn (w : List Letter) : SynClass :=
  if w = [] then .unit else if th w then .hasTH else .free (startsH w) (endsT w)

/-- [definition] What a context `u · _ · v` reads from a class. -/
def ctx : SynClass → List Letter → List Letter → Bool
  | .unit, u, v => th (u ++ v)
  | .hasTH, _, _ => true
  | .free s e, u, v => th u || th v || (endsT u && s) || (e && startsH v)

/-- [proved-derived; formal-checked] Every context reads a word through its class. -/
theorem th_context (u x v : List Letter) : th (u ++ x ++ v) = ctx (syn x) u v := by
  unfold syn
  by_cases hx : x = []
  · subst hx; simp [ctx]
  · rw [if_neg hx]
    have hend : endsT (u ++ x) = endsT x := by
      simp only [endsT, List.getLast?_append]
      obtain ⟨l, b, rfl⟩ := List.eq_nil_or_concat x |>.resolve_left hx
      simp
    by_cases hth : th x = true
    · rw [if_pos hth]
      simp [hth, ctx, th_append]
    · rw [if_neg hth]
      simp only [ctx]
      rw [th_append, th_append, hend]
      simp only [Bool.not_eq_true] at hth
      simp only [hth, Bool.or_false]
      cases th u <;> cases th v <;> cases endsT u <;> cases startsH x <;> cases endsT x <;>
        cases startsH v <;> rfl

/-- [proved-derived; formal-checked] Four contexts, `{ε, t} × {ε, h}`, tell every two classes apart. -/
theorem classes_separated : ∀ c d : SynClass,
    (ctx c [] [] = ctx d [] [] ∧ ctx c [t] [] = ctx d [t] [] ∧ ctx c [] [h] = ctx d [] [h] ∧
      ctx c [t] [h] = ctx d [t] [h]) → c = d := by
  decide

/-- [proved-derived; formal-checked] The syntactic congruence of "contains `th`" is equality of the six classes. -/
theorem syntactic_iff (x y : List Letter) : Syn x y ↔ syn x = syn y := by
  constructor
  · intro hs
    apply classes_separated
    simp only [← th_context]
    exact ⟨hs [] [], hs [t] [], hs [] [h], hs [t] [h]⟩
  · intro he u v
    rw [th_context, th_context, he]

/-- [proved-derived; formal-checked] Every class is a word's. -/
theorem syn_surjective : Function.Surjective syn := by
  intro c
  rcases c with _ | _ | ⟨_ | _, _ | _⟩
  · exact ⟨[], rfl⟩
  · exact ⟨[t, h], rfl⟩
  · exact ⟨[a], rfl⟩
  · exact ⟨[t], rfl⟩
  · exact ⟨[h], rfl⟩
  · exact ⟨[h, t], rfl⟩

/-- [definition] The syntactic congruence as a setoid. -/
def synSetoid : Setoid (List Letter) where
  r := Syn
  iseqv := ⟨fun _ _ _ => rfl, fun h u v => (h u v).symm, fun h1 h2 u v => (h1 u v).trans (h2 u v)⟩

/-- [proved-derived; formal-checked] The syntactic congruence of "contains `th`" over `{t, h, a}` has six classes. -/
theorem card_syntactic : Nat.card (Quotient synSetoid) = 6 := by
  have hker : synSetoid = Setoid.ker syn := Setoid.ext fun x y => syntactic_iff x y
  rw [hker, Nat.card_congr (Setoid.quotientKerEquivOfSurjective syn syn_surjective), Nat.card_eq_fintype_card]
  decide

/-- [proved-standard; formal-checked] The syntactic congruence is conserved by concatenation: it is a congruence. -/
theorem syn_conserved : Conserved syn (· ++ ·) := by
  intro x x' y y' hx hy
  rw [← syntactic_iff] at hx hy ⊢
  intro u v
  calc th (u ++ (x ++ y) ++ v) = th (u ++ x ++ (y ++ v)) := by simp
    _ = th (u ++ x' ++ (y ++ v)) := hx u (y ++ v)
    _ = th ((u ++ x') ++ y ++ v) := by simp
    _ = th ((u ++ x') ++ y' ++ v) := hy (u ++ x') v
    _ = th (u ++ (x' ++ y') ++ v) := by simp

/-- [proved-standard; formal-checked] It is the coarsest conserved refinement of the face: every face conserved by
concatenation through which `th` factors identifies only syntactically equal words. -/
theorem syn_coarsest {γ : Type*} (q : List Letter → γ) (hq : Conserved q (· ++ ·))
    (hth : ∀ x y, q x = q y → th x = th y) {x y : List Letter} (hxy : q x = q y) : syn x = syn y := by
  rw [← syntactic_iff]
  intro u v
  exact hth _ _ (hq _ _ _ _ (hq _ _ _ _ rfl hxy) rfl)

/-- [definition] The right congruence a left-to-right reader keeps: no suffix tells the two prefixes apart. -/
def Right (x y : List Letter) : Prop := ∀ v, th (x ++ v) = th (y ++ v)

/-- [definition] The right congruence's three classes. -/
inductive RightClass
  | hasTH
  | endT
  | other
  deriving DecidableEq

instance : Fintype RightClass :=
  ⟨{.hasTH, .endT, .other}, by intro c; cases c <;> simp⟩

/-- [definition] A prefix's class: has `th`, `th`-free ending in `t`, or the rest. -/
def rcls (w : List Letter) : RightClass :=
  if th w then .hasTH else if endsT w then .endT else .other

/-- [definition] What a suffix reads from a class. -/
def rctx : RightClass → List Letter → Bool
  | .hasTH, _ => true
  | .endT, v => th v || startsH v
  | .other, v => th v

/-- [proved-derived; formal-checked] A suffix reads a prefix through its class. -/
theorem th_suffix (x v : List Letter) : th (x ++ v) = rctx (rcls x) v := by
  rw [th_append]
  unfold rcls
  cases hth : th x <;> cases he : endsT x <;> simp [rctx]

/-- [proved-derived; formal-checked] The right congruence is equality of the three classes; two suffixes, `ε` and
`h`, tell them apart. -/
theorem right_iff (x y : List Letter) : Right x y ↔ rcls x = rcls y := by
  constructor
  · intro hr
    have h1 := hr []
    have h2 := hr [h]
    rw [th_suffix, th_suffix] at h1 h2
    revert h1 h2
    generalize rcls x = c
    generalize rcls y = d
    revert c d
    decide
  · intro he v
    rw [th_suffix, th_suffix, he]

/-- [proved-derived; formal-checked] Every right class is a prefix's. -/
theorem rcls_surjective : Function.Surjective rcls := by
  intro c
  rcases c with _ | _ | _
  · exact ⟨[t, h], rfl⟩
  · exact ⟨[t], rfl⟩
  · exact ⟨[], rfl⟩

/-- [definition] The right congruence as a setoid. -/
def rightSetoid : Setoid (List Letter) where
  r := Right
  iseqv := ⟨fun _ _ => rfl, fun h v => (h v).symm, fun h1 h2 v => (h1 v).trans (h2 v)⟩

/-- [proved-derived; formal-checked] The right congruence a left-to-right reader keeps has three classes. -/
theorem card_right : Nat.card (Quotient rightSetoid) = 3 := by
  have hker : rightSetoid = Setoid.ker rcls := Setoid.ext fun x y => right_iff x y
  rw [hker, Nat.card_congr (Setoid.quotientKerEquivOfSurjective rcls rcls_surjective), Nat.card_eq_fintype_card]
  decide

end Language

/-! ## 4. Other algebras: the jet, the determinant and the sign -/

section Algebras

open TrivSqZeroExt

/-- [definition] The jet face `(f a, f′ a)`, read in the dual numbers. -/
noncomputable def jet (f : ℝ → ℝ) (a : ℝ) : DualNumber ℝ := inl (f a) + inr (deriv f a)

/-- [proved-standard; formal-checked] The jet is conserved by products: the jet of `f g` is the dual-number product
of the jets (Leibniz). -/
theorem jet_mul {f g : ℝ → ℝ} {a : ℝ} (hf : DifferentiableAt ℝ f a) (hg : DifferentiableAt ℝ g a) :
    jet (fun x => f x * g x) a = jet f a * jet g a := by
  ext
  · simp [jet]
  · simp only [jet, snd_add, snd_inl, snd_inr, zero_add, snd_mul, fst_add, fst_inl, fst_inr,
      add_zero, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    rw [deriv_fun_mul hf hg]
    ring

/-- [proved-standard; formal-checked] The derivative alone is not conserved by products: `x` and `x + 1` both have
derivative one at `0`, and `x · x`, `(x + 1) · x` have derivatives `0` and `1` there. -/
theorem deriv_not_conserved : ¬ ∃ D : ℝ → ℝ → ℝ, ∀ f g : ℝ → ℝ, DifferentiableAt ℝ f 0 →
    DifferentiableAt ℝ g 0 → deriv (fun x => f x * g x) 0 = D (deriv f 0) (deriv g 0) := by
  rintro ⟨D, hD⟩
  have hid : DifferentiableAt ℝ (fun x : ℝ => x) 0 := differentiableAt_id
  have hsh : DifferentiableAt ℝ (fun x : ℝ => x + 1) 0 := differentiableAt_id.add_const 1
  have h1 := hD (fun x => x) (fun x => x) hid hid
  have h2 := hD (fun x => x + 1) (fun x => x) hsh hid
  rw [deriv_fun_mul hid hid] at h1
  rw [deriv_fun_mul hsh hid] at h2
  simp only [deriv_id'', deriv_add_const] at h1 h2
  norm_num at h1 h2
  rw [← h2] at h1
  norm_num at h1

/-- [proved-standard; formal-checked] `det` is conserved by the matrix product. -/
theorem det_conserved (n : ℕ) : Conserved (Matrix.det : Matrix (Fin n) (Fin n) ℤ → ℤ) (· * ·) := by
  intro x x' y y' hx hy
  simp only [Matrix.det_mul, hx, hy]

/-- [proved-standard; formal-checked] The trace is not: `diag(1, −1)` and `0` both have trace `0`, and their
products with `diag(1, −1)` have traces `2` and `0`. -/
theorem trace_not_conserved :
    ¬ Conserved (Matrix.trace : Matrix (Fin 2) (Fin 2) ℤ → ℤ) (· * ·) := by
  intro hc
  have := hc !![1, 0; 0, -1] 0 !![1, 0; 0, -1] !![1, 0; 0, -1]
    (by simp [Matrix.trace_fin_two]) rfl
  simp [Matrix.trace_fin_two] at this

/-- [proved-standard; formal-checked] Nor is the trace beside `det`: `diag(1, −1)` and `[[0, 1], [1, 0]]` share
trace `0` and `det −1`, and their products with `diag(1, −1)` have traces `2` and `0`. -/
theorem trace_det_not_conserved :
    ¬ Conserved (fun A : Matrix (Fin 2) (Fin 2) ℤ => (A.trace, A.det)) (· * ·) := by
  intro hc
  have := hc !![1, 0; 0, -1] !![0, 1; 1, 0] !![1, 0; 0, -1] !![1, 0; 0, -1]
    (by simp [Matrix.trace_fin_two, Matrix.det_fin_two]) rfl
  simp [Matrix.trace_fin_two] at this

/-- [proved-standard; formal-checked] The trace of a product is the pairing of the whole operands,
`tr(AB) = ⟨A, Bᵀ⟩ = Σᵢⱼ Aᵢⱼ Bⱼᵢ`: a pair contact, not a function of the two traces. -/
theorem trace_mul_eq_pairing {n R : Type*} [Fintype n] [CommSemiring R] (A B : Matrix n n R) :
    (A * B).trace = ∑ i, ∑ j, A i j * B.transpose i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]

/-- [proved-standard; formal-checked] The sign is conserved by composition. -/
theorem sign_conserved {α : Type*} [DecidableEq α] [Fintype α] :
    Conserved (Equiv.Perm.sign : Equiv.Perm α → ℤˣ) (· * ·) := by
  intro x x' y y' hx hy
  simp only [Equiv.Perm.sign_mul, hx, hy]

/-- [proved-standard; formal-checked] The cycle type is not: `(0 1)` and `(0 2)` are both transpositions, while
`(0 1)(0 1) = 1` and `(0 1)(0 2)` is a three-cycle. -/
theorem cycleType_not_conserved :
    ¬ Conserved (Equiv.Perm.cycleType : Equiv.Perm (Fin 4) → Multiset ℕ) (· * ·) := by
  intro hc
  have h01 : (Equiv.swap (0 : Fin 4) 1).cycleType = {2} :=
    Equiv.Perm.isSwap_iff_cycleType.mp ⟨0, 1, by decide, rfl⟩
  have h02 : (Equiv.swap (0 : Fin 4) 2).cycleType = {2} :=
    Equiv.Perm.isSwap_iff_cycleType.mp ⟨0, 2, by decide, rfl⟩
  have := hc (Equiv.swap 0 1) (Equiv.swap 0 1) (Equiv.swap 0 1) (Equiv.swap 0 2) rfl (h01.trans h02.symm)
  beta_reduce at this
  rw [Equiv.swap_mul_self, Equiv.Perm.cycleType_one,
    (Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType] at this
  simp at this

end Algebras

end Holonics.Compression.OneFaceLaw
