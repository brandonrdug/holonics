import Holonics.Foundation.ReceiverHistoryCompression
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# The source passage enters as phase-carried moments

[definition] A fixed machine reads an ordered source `u₀ … u_(n−1)` through a linear advance
`U : S → S` (the declared per-step phase transport of its generators), an injection `I : X → S`
and an encoder `E : Letter → X`. The **moment** is defined by its one-step law

```text
moment []          = 0
moment (l ++ [u])  = U (moment l) + I (E u)
```

which is the per-step form `q_k⁺ = U_step(q_k) + I E(u_k)` of
`m_g(n) = Σ_(k<n) Ĝ_g(τ_g(k))⁻¹ E_g(u_k)` (retention audit of 2026-09-22; native owner
`holonics-hna/.../incident/machine_source.rs::MachineSourceMaps`). The theorems below are the
content of that definition, not a restatement of it:

1. `moment_closed_form` — the moment is the phase-weighted sum `Σ_k U^(n−1−k) I E(u_k)`.
2. `accumulate_perturb`, `position_adjoint_is_tape_free` — the exact response of any linear
   functional `g` to a change of the encoded value at position `k` is `g ∘ U^(n−1−k) ∘ I`; two
   sources of the same length have identical per-position adjoints. The adjoint needs no
   intermediate state, hence no tape.
3. `moment_pair_eq_iff`, `identity_advance_merges_permutations`, `rotation_separates_pair` —
   order enters only through the advance: `[a,b]` and `[b,a]` have equal moments exactly when
   `(U − 1) I (E a − E b) = 0`; the identity advance merges every permutation (a plural
   preimage fibre); a nonidentity rotation separates the two-letter case.
4. `offset_moment_separates_pair`, `offset_moment_separates_under_identity_advance` — with
   `U = 1` the oriented δ=1 moment `Σ_k v(k) ⊗ v(k+1)` separates what the moment merges.
5. `momentDescent`, `streamDescent` — the moment, and the constant-size stream state
   `(moment, last encoded value, offset moment)`, are instances of the existing
   `ReceiverHistoryCompression` owner for the append action, with induced quotient generator
   `U_u(x) = U x + I E u`. No list, fold state chain or update archive is the retained object:
   the retained object is an element of `S` (resp. `S × Option X × (X ⊗ X)`), whose size is
   independent of source length.

Epistemic grade: [proved-derived; formal-checked] for every theorem; the identification of `U`
with the machine's declared generator phase transport is the [definition] above.
-/

namespace Holonics.Transport.SourceMoment

open Holonics
open Holonics.Millennium.Chronology
open Holonics.Millennium.LineageCompression
open scoped TensorProduct

variable {R : Type*} [CommRing R]
variable {X S Letter : Type*} [AddCommGroup X] [Module R X] [AddCommGroup S] [Module R S]

/-- A fixed source-reading machine: linear advance, injection and encoder. -/
structure MomentMachine (R X S Letter : Type*) [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup S] [Module R S] where
  /-- The declared linear phase advance `U`. -/
  advance : S →ₗ[R] S
  /-- The injection `I` of an encoded increment into the state. -/
  inject : X →ₗ[R] S
  /-- The encoder `E`. -/
  encode : Letter → X

/-- The source transport: append one letter. -/
def appendLetter {Letter : Type*} (u : Letter) (l : List Letter) : List Letter := l ++ [u]

namespace MomentMachine

variable (M : MomentMachine R X S Letter)

/-- The accumulation of already encoded values, by the one-step law. -/
def accumulate (xs : List X) : S :=
  xs.foldl (fun s x => M.advance s + M.inject x) 0

/-- The moment of a source passage. -/
def moment (l : List Letter) : S := M.accumulate (l.map M.encode)

@[simp] theorem accumulate_nil : M.accumulate [] = 0 := rfl

/-- The defining one-step law of the accumulation. -/
theorem accumulate_append_one (xs : List X) (x : X) :
    M.accumulate (xs ++ [x]) = M.advance (M.accumulate xs) + M.inject x := by
  simp [accumulate, List.foldl_append]

@[simp] theorem moment_nil : M.moment [] = 0 := rfl

/-- [definition] The defining one-step law `moment (l ++ [u]) = U (moment l) + I (E u)`. -/
theorem moment_append_one (l : List Letter) (u : Letter) :
    M.moment (l ++ [u]) = M.advance (M.moment l) + M.inject (M.encode u) := by
  simp [moment, List.map_append, accumulate_append_one]

/-! ## 1. Closed form -/

/-- The phase-weighted sum over an encoded list, indexed by position. -/
def weightedSum (xs : List X) : S :=
  ∑ k ∈ Finset.range xs.length, (M.advance ^ (xs.length - 1 - k)) (M.inject (xs.getD k 0))

/-- [proved-derived; formal-checked] **Closed form of the accumulation.** -/
theorem accumulate_closed_form (xs : List X) : M.accumulate xs = M.weightedSum xs := by
  induction xs using List.reverseRecOn with
  | nil => simp [weightedSum]
  | append_singleton xs x ih =>
      rw [accumulate_append_one, ih]
      unfold weightedSum
      rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
      congr 1
      · rw [map_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k < xs.length := Finset.mem_range.mp hk
        have hget : (xs ++ [x]).getD k 0 = xs.getD k 0 := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk']
        have hpow : xs.length + 1 - 1 - k = (xs.length - 1 - k) + 1 := by omega
        rw [hget, hpow, pow_succ', Module.End.mul_apply]
      · have hget : (xs ++ [x]).getD xs.length 0 = x := by
          simp [List.getD_eq_getElem?_getD]
        have hpow : xs.length + 1 - 1 - xs.length = 0 := by omega
        rw [hget, hpow, pow_zero, Module.End.one_apply]

/-- [proved-derived; formal-checked] **Closed form of the moment**:
`moment l = Σ_k U^(n−1−k) I E(u_k)`. -/
theorem moment_closed_form (l : List Letter) :
    M.moment l = ∑ k ∈ Finset.range l.length,
      (M.advance ^ (l.length - 1 - k)) (M.inject ((l.map M.encode).getD k 0)) := by
  rw [moment, accumulate_closed_form, weightedSum, List.length_map]

/-! ## 2. The position adjoint needs no tape -/

/-- The per-position adjoint map `U^(n−1−k) ∘ I`. It is a function of `n` and `k` only. -/
def positionMap (n k : ℕ) : X →ₗ[R] S := (M.advance ^ (n - 1 - k)) ∘ₗ M.inject

/-- [proved-derived; formal-checked] **Exact position response.** Changing the encoded value at
position `k` by `δ` changes the accumulation by `U^(n−1−k) I δ`, exactly (the accumulation is
linear in the encoded values, so this difference is its derivative). -/
theorem accumulate_perturb (xs : List X) {k : ℕ} (hk : k < xs.length) (δ : X) :
    M.accumulate (xs.set k (xs.getD k 0 + δ)) =
      M.accumulate xs + M.positionMap xs.length k δ := by
  rw [accumulate_closed_form, accumulate_closed_form, weightedSum, weightedSum,
    List.length_set]
  have hterm : ∀ i ∈ Finset.range xs.length,
      (M.advance ^ (xs.length - 1 - i)) (M.inject ((xs.set k (xs.getD k 0 + δ)).getD i 0)) =
        (M.advance ^ (xs.length - 1 - i)) (M.inject (xs.getD i 0)) +
          (if i = k then M.positionMap xs.length k δ else 0) := by
    intro i _
    by_cases hik : i = k
    · subst hik
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hk, positionMap, map_add]
    · simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hik), hik]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp [Finset.mem_range.mpr hk]

/-- [proved-derived; formal-checked] **The adjoint is tape-free.** For every linear functional
`g` on the state, the exact response of `g ∘ accumulate` at position `k` is
`g ∘ U^(n−1−k) ∘ I`, and two encoded sources of the same length have the same per-position
response map, whatever their values and whatever intermediate states they pass through. -/
theorem position_adjoint_is_tape_free (g : S →ₗ[R] R) (xs ys : List X)
    (hlen : xs.length = ys.length) {k : ℕ} (hk : k < xs.length) (δ : X) :
    g (M.accumulate (xs.set k (xs.getD k 0 + δ))) - g (M.accumulate xs) =
        (g ∘ₗ M.positionMap xs.length k) δ ∧
      g (M.accumulate (xs.set k (xs.getD k 0 + δ))) - g (M.accumulate xs) =
        g (M.accumulate (ys.set k (ys.getD k 0 + δ))) - g (M.accumulate ys) := by
  have hx := M.accumulate_perturb xs hk δ
  have hy := M.accumulate_perturb ys (hlen ▸ hk) δ
  refine ⟨?_, ?_⟩
  · rw [hx, map_add]; simp
  · rw [hx, hy, map_add, map_add, hlen]; simp

/-! ## 3. Order separation -/

/-- The two-letter moments. -/
theorem moment_pair (a b : Letter) :
    M.moment [a, b] = M.advance (M.inject (M.encode a)) + M.inject (M.encode b) := by
  have h := M.moment_append_one [a] b
  have ha := M.moment_append_one [] a
  simp only [List.nil_append] at ha
  simp only [List.singleton_append] at h
  rw [h, ha, moment_nil, map_zero, zero_add]

/-- [proved-derived; formal-checked] **Order enters only through the advance.**
`moment [a,b] = moment [b,a] ↔ (U − 1) I (E a − E b) = 0`. -/
theorem moment_pair_eq_iff (a b : Letter) :
    M.moment [a, b] = M.moment [b, a] ↔
      (M.advance - 1) (M.inject (M.encode a - M.encode b)) = 0 := by
  have key : ∀ A B x y : S, A - B - (x - y) = (A + y) - (B + x) := by intros; abel
  rw [moment_pair, moment_pair, LinearMap.sub_apply, Module.End.one_apply, map_sub, map_sub,
    key, sub_eq_zero]

/-- With the identity advance the accumulation is the plain sum of injected values. -/
theorem accumulate_of_advance_eq_one (h : M.advance = 1) (xs : List X) :
    M.accumulate xs = (xs.map M.inject).sum := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
      rw [accumulate_append_one, ih, h, Module.End.one_apply]
      simp

/-- [proved-derived; formal-checked] **Identity advance merges every permutation.** With
`U = 1` the moment of a source equals the moment of every permutation of it: the order of the
source lies in a plural preimage fibre of the moment. -/
theorem identity_advance_merges_permutations (h : M.advance = 1) {l l' : List Letter}
    (hp : l.Perm l') : M.moment l = M.moment l' := by
  rw [moment, moment, accumulate_of_advance_eq_one M h, accumulate_of_advance_eq_one M h]
  exact ((hp.map M.encode).map M.inject).sum_eq

/-- [proved-derived; formal-checked] **A nonidentity advance separates the pair** whenever
`I (E a − E b)` is not fixed by `U`. -/
theorem advance_separates_pair (a b : Letter)
    (hmoved : M.advance (M.inject (M.encode a - M.encode b)) ≠
      M.inject (M.encode a - M.encode b)) :
    M.moment [a, b] ≠ M.moment [b, a] := by
  intro h
  apply hmoved
  have := (M.moment_pair_eq_iff a b).mp h
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
  exact this

/-! ### A concrete rotation witness over `ℚ²` -/

/-- The quarter-turn `(x, y) ↦ (−y, x)` on `ℚ × ℚ`. -/
def quarterTurn : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ) where
  toFun p := (-p.2, p.1)
  map_add' p q := by ext <;> simp; ring
  map_smul' c p := by ext <;> simp

/-- A two-letter machine read through the quarter-turn. -/
def rotor : MomentMachine ℚ (ℚ × ℚ) (ℚ × ℚ) Bool where
  advance := quarterTurn
  inject := LinearMap.id
  encode b := if b then (1, 0) else (0, 0)

/-- [proved-derived; formal-checked] The quarter-turn separates `[true,false]` from
`[false,true]`; the identity advance on the same letters (previous theorem) cannot. -/
theorem rotation_separates_pair : rotor.moment [true, false] ≠ rotor.moment [false, true] := by
  apply rotor.advance_separates_pair
  simp [rotor, quarterTurn]

/-! ## 4. The oriented offset moment separates what the moment merges -/

/-- The oriented δ=1 moment `Σ_k v(k) ⊗ v(k+1)` of the encoded values, at identity advance
(`v(k) = E(u_k)`). -/
def offsetMoment (l : List Letter) : X ⊗[R] X :=
  (List.zipWith (fun x y => x ⊗ₜ[R] y) (l.map M.encode) (l.map M.encode).tail).sum

theorem offsetMoment_pair (a b : Letter) :
    M.offsetMoment [a, b] = M.encode a ⊗ₜ[R] M.encode b := by
  simp [offsetMoment]

/-- [proved-derived; formal-checked] **The offset moment separates the pair** whenever
`E a ⊗ E b ≠ E b ⊗ E a`. -/
theorem offset_moment_separates_pair (a b : Letter)
    (horiented : M.encode a ⊗ₜ[R] M.encode b ≠ M.encode b ⊗ₜ[R] M.encode a) :
    M.offsetMoment [a, b] ≠ M.offsetMoment [b, a] := by
  rw [offsetMoment_pair, offsetMoment_pair]
  exact horiented

/-- [proved-derived; formal-checked] Under the identity advance the moment merges `[a,b]` and
`[b,a]`, while the oriented offset moment separates them under the same hypothesis. -/
theorem offset_moment_separates_under_identity_advance (h : M.advance = 1) (a b : Letter)
    (horiented : M.encode a ⊗ₜ[R] M.encode b ≠ M.encode b ⊗ₜ[R] M.encode a) :
    M.moment [a, b] = M.moment [b, a] ∧ M.offsetMoment [a, b] ≠ M.offsetMoment [b, a] :=
  ⟨M.identity_advance_merges_permutations h (List.Perm.swap b a []),
    M.offset_moment_separates_pair a b horiented⟩

/-! ## 5. Descent: the moment is a receiver-history compression for the append action -/

/-- The induced quotient generator `U_u(x) = U x + I E u`. -/
def momentStep (u : Letter) (s : S) : S := M.advance s + M.inject (M.encode u)

/-- [proved-derived; formal-checked] **Descent square.** Every receiver that reads the moment
(`read r ∘ moment`) factors through the moment, and the moment commutes with appending a
letter via `U_u`. By the existing owner this is exact for every ordered successor word. -/
def momentDescent {Receiver Face : Type*} (read : Receiver → S → Face) :
    ReceiverHistoryCompression Letter Receiver (List Letter) S Face where
  present :=
    { quotient := M.moment
      receiver := fun r l => read r (M.moment l)
      factor := read
      exact := fun _ _ => rfl }
  sourceTransport := appendLetter
  quotientTransport := M.momentStep
  generatorExact u l := M.moment_append_one l u

/-- [proved-derived; formal-checked] The plural fibre is real: with `U = 1`, `[a,b]` and
`[b,a]` give the same face for every moment receiver after every successor word. -/
theorem identity_advance_fibre_survives_every_successor (h : M.advance = 1)
    {Receiver Face : Type*} (read : Receiver → S → Face) (a b : Letter)
    (r : Receiver) (word : List Letter) :
    read r (M.moment (transportWord appendLetter word [a, b])) =
      read r (M.moment (transportWord appendLetter word [b, a])) :=
  (M.momentDescent read).quotientEqForcesEverySuccessorFace
    (M.identity_advance_merges_permutations h (List.Perm.swap b a [])) r word

/-! ### The constant-size stream state carrying the oriented offset moment -/

/-- The stream state `(moment, last encoded value, offset moment)`. -/
abbrev StreamState (R X S : Type*) [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup S] [Module R S] :=
  S × Option X × (X ⊗[R] X)

/-- The encoded last letter. -/
def lastEncoded (l : List Letter) : Option X := (l.map M.encode).getLast?

/-- The stream quotient of a source. -/
def stream (l : List Letter) : StreamState R X S :=
  (M.moment l, M.lastEncoded l, M.offsetMoment l)

/-- The induced stream generator. -/
def streamStep (u : Letter) : StreamState R X S → StreamState R X S
  | (s, prev, c) =>
      (M.advance s + M.inject (M.encode u), some (M.encode u),
        c + (match prev with
          | none => 0
          | some p => p ⊗ₜ[R] M.encode u))

theorem zipWith_tail_append_one (xs : List X) (x : X) :
    (List.zipWith (fun a b => a ⊗ₜ[R] b) (xs ++ [x]) (xs ++ [x]).tail).sum =
      (List.zipWith (fun a b => a ⊗ₜ[R] b) xs xs.tail).sum +
        (match xs.getLast? with
          | none => 0
          | some p => p ⊗ₜ[R] x) := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
      cases ys with
      | nil => simp
      | cons z zs =>
          have ih' := ih
          simp only [List.cons_append, List.tail_cons, List.zipWith_cons_cons,
            List.sum_cons] at ih' ⊢
          rw [ih']
          simp [List.getLast?_cons_cons, add_assoc]

/-- [proved-derived; formal-checked] The stream state commutes with appending one letter. -/
theorem stream_append_one (l : List Letter) (u : Letter) :
    M.stream (l ++ [u]) = M.streamStep u (M.stream l) := by
  simp only [stream, streamStep, moment_append_one, lastEncoded, offsetMoment,
    List.map_append, List.map_singleton, List.getLast?_append, List.getLast?_singleton,
    Option.some_or]
  rw [zipWith_tail_append_one]

/-- [proved-derived; formal-checked] **Constant-size descent carrying the separator.** The
stream state is a receiver-history compression for the append action; its receivers include
the oriented offset moment. -/
def streamDescent {Receiver Face : Type*} (read : Receiver → StreamState R X S → Face) :
    ReceiverHistoryCompression Letter Receiver (List Letter) (StreamState R X S) Face where
  present :=
    { quotient := M.stream
      receiver := fun r l => read r (M.stream l)
      factor := read
      exact := fun _ _ => rfl }
  sourceTransport := appendLetter
  quotientTransport := M.streamStep
  generatorExact u l := M.stream_append_one l u

/-- [proved-derived; formal-checked] Under the identity advance the stream quotient separates
`[a,b]` from `[b,a]` when `E a ⊗ E b ≠ E b ⊗ E a`, although their moments are equal. -/
theorem stream_separates_what_the_moment_merges (h : M.advance = 1) (a b : Letter)
    (horiented : M.encode a ⊗ₜ[R] M.encode b ≠ M.encode b ⊗ₜ[R] M.encode a) :
    M.moment [a, b] = M.moment [b, a] ∧ M.stream [a, b] ≠ M.stream [b, a] := by
  refine ⟨(M.offset_moment_separates_under_identity_advance h a b horiented).1, ?_⟩
  intro hs
  exact M.offset_moment_separates_pair a b horiented (congrArg (fun t => t.2.2) hs)

end MomentMachine

end Holonics.Transport.SourceMoment
