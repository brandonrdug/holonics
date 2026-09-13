import Mathlib.Data.List.Perm.Basic
import Lean.Elab.Tactic.Omega

/-!
# Ordered transport words and endpoint order blindness

This file owns the generic list action used by the holonic framework.  A transport word retains the
ordered sequence of generator entries, and equivariance extends to that exact sequence.
An entry need not itself encode a complete occurrence identity; addressed passage owners retain
that additional lineage.  The
`OrderBlind` predicate is only an endpoint-action property: when it holds, permuting a word does not
change its endpoint result.  It does not identify distinct words or separately retained occurrence lineage.
-/

namespace Soma.Holonics.Millennium.Chronology

universe u v

variable {ι : Type u} {X : Type v}

/-! ## Ordered transport words -/

/-- The transport a word of moves performs, read right to left: the rightmost letter acts first.
List positions retain generator order even when the endpoint action is order-blind. -/
def transportWord (T : ι → X → X) : List ι → X → X
  | [], x => x
  | i :: w, x => T i (transportWord T w x)

@[simp] theorem transportWord_nil (T : ι → X → X) (x : X) : transportWord T [] x = x := rfl

@[simp] theorem transportWord_cons (T : ι → X → X) (i : ι) (w : List ι) (x : X) :
    transportWord T (i :: w) x = T i (transportWord T w x) := rfl

/-- Equivariance on the generators extends to every ordered transport word.

This is the exact local-to-composite bridge used by a geometric action: if `f` intertwines each
declared generator `T i` with `S i`, it intertwines the chronology they generate, with its order
retained. The theorem does not claim that the actions or the intertwiner were recovered from
material; those are exterior hypotheses. -/
theorem generatorEquivarianceExtendsToEveryTransportWord
    {Y : Type*} (T : ι → X → X) (S : ι → Y → Y) (f : X → Y)
    (h : ∀ i x, f (T i x) = S i (f x)) (w : List ι) (x : X) :
    f (transportWord T w x) = transportWord S w (f x) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      rw [transportWord_cons, h, ih, transportWord_cons]

/-! ## A local distance certificate compiles an optimal navigation word

A nonnegative integer potential is checked against every admitted unit-cost move. If a policy
decreases it by exactly one until a zero/goal face, its returned word attains the lower bound.
The theorem is an optimality certificate, not an assumption that computing the potential is cheap.
Move order is the existing right-to-left transport convention.
-/

theorem transportWord_append (T : ι → X → X) (left right : List ι) (x : X) :
    transportWord T (left ++ right) x = transportWord T left (transportWord T right x) := by
  induction left with
  | nil => rfl
  | cons i left ih => simp [ih]

theorem word_length_lower_bound (T : ι → X → X) (potential : X → ℕ)
    (edgeBound : ∀ i x, potential x ≤ 1 + potential (T i x))
    (word : List ι) (x : X) :
    potential x ≤ word.length + potential (transportWord T word x) := by
  induction word with
  | nil => simp
  | cons i word ih =>
      have h := edgeBound i (transportWord T word x)
      simp only [List.length_cons, transportWord_cons]
      omega

def descendingWord (T : ι → X → X) (choose : X → ι) : ℕ → X → List ι
  | 0, _ => []
  | n + 1, x => descendingWord T choose n (T (choose x) x) ++ [choose x]

theorem descendingWord_length (T : ι → X → X) (choose : X → ι) (n : ℕ) (x : X) :
    (descendingWord T choose n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [descendingWord, ih]

theorem descendingWord_zero_face (T : ι → X → X) (choose : X → ι) (potential : X → ℕ)
    (descends : ∀ x, 0 < potential x → potential (T (choose x) x) + 1 = potential x)
    (n : ℕ) (x : X) (atDepth : potential x = n) :
    potential (transportWord T (descendingWord T choose n x) x) = 0 := by
  induction n generalizing x with
  | zero => simpa [descendingWord] using atDepth
  | succ n ih =>
      have hp : 0 < potential x := by omega
      have hn : potential (T (choose x) x) = n := by
        have h := descends x hp
        omega
      simpa [descendingWord, transportWord_append] using ih (T (choose x) x) hn

/-- The policy reaches an actual declared goal and is no longer than any competing goal word.
The zero-face implication concerns the full state, so an abstract goal with an unresolved fibre
cannot silently be substituted here. -/
theorem descendingWord_is_optimal (T : ι → X → X) (choose : X → ι)
    (potential : X → ℕ) (goal : X → Prop)
    (goalZero : ∀ x, goal x ↔ potential x = 0)
    (edgeBound : ∀ i x, potential x ≤ 1 + potential (T i x))
    (descends : ∀ x, 0 < potential x → potential (T (choose x) x) + 1 = potential x)
    (x : X) :
    goal (transportWord T (descendingWord T choose (potential x) x) x) ∧
      ∀ word, goal (transportWord T word x) →
        (descendingWord T choose (potential x) x).length ≤ word.length := by
  constructor
  · apply (goalZero _).2
    exact descendingWord_zero_face T choose potential descends (potential x) x rfl
  · intro word reaches
    have bound := word_length_lower_bound T potential edgeBound word x
    have zero := (goalZero _).1 reaches
    rw [descendingWord_length]
    omega

/-! ## Endpoint order blindness -/

/-- A family of transports is endpoint-order-blind when permuting a word leaves its endpoint action
unchanged. The word and separately retained occurrence population are not identified by this predicate. -/
def OrderBlind (T : ι → X → X) : Prop :=
  ∀ w v : List ι, w.Perm v → ∀ x : X, transportWord T w x = transportWord T v x

/-- Endpoint order blindness is exactly pairwise commutation of the endpoint actions. -/
theorem orderBlind_iff_commute {T : ι → X → X} :
    OrderBlind T ↔ ∀ i j : ι, ∀ x : X, T i (T j x) = T j (T i x) := by
  constructor
  · intro h i j x
    have hp : ([j, i] : List ι).Perm [i, j] := List.Perm.swap i j []
    simpa using (h [j, i] [i, j] hp x).symm
  · intro hc w v hperm
    induction hperm with
    | nil => intro x; rfl
    | cons a _ ih => intro x; simp [ih x]
    | swap a b l => intro x; simpa using hc b a (transportWord T l x)
    | trans _ _ ih₁ ih₂ => intro x; rw [ih₁ x, ih₂ x]

section Audit

#print axioms generatorEquivarianceExtendsToEveryTransportWord
#print axioms orderBlind_iff_commute

end Audit

end Soma.Holonics.Millennium.Chronology
