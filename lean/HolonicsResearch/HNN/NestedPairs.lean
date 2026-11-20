import HolonicsResearch.HNN.CarryGroupTracking
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# A bank that is not coupled reads crossed pairs as nested ones, and a relative phase is held by a pair alone

Three finite statements beside the reading of November 20 that sets the Hodge conjecture next to
the machine (the record of that day; atlas `parametron.crossed-pair-is-a-commutator`,
`code.nested-share-of-balanced` and `receiver.pair-reads-relative-phase`).

1. A carry reads a word of openers and closers as a product in a group, an opener as an element
   and its closer as the inverse. Two pairs nested, `a b b⁻¹ a⁻¹`, return the carry in every
   group. Two pairs crossed, `a b a⁻¹ b⁻¹`, return it if and only if the two elements commute:
   the crossed word is the commutator. So a bank of circles that are not coupled to each other
   (`CarryGroupTracking.AffineTracks`) reads a crossed word as it reads the nested one, whatever
   its width, and two swaps of three things are a carry that tells them apart.
2. The words of length `2n` with as many openers as closers are the choices of the openers'
   places, `C(2n, n)` of them. The nested ones are Mathlib's Dyck words, `catalan n` of them. One
   word with equal counts in `n + 1` is nested.
3. Over a whole cycle of a turn (the powers of a primitive root of unity) every reading that is
   real-linear in two strands has mean zero, whatever phase stands between the strands, while
   the product of one strand with the mirror of the other has that phase as its mean. The
   product of a turn and a mirror turn carries no turn of its own: it is the type the classical
   subject writes `(1,1)`.

Sources, `from training`: the commutator as the crossing of two pairs is the word problem of the
free group against its abelianization; the count is the ballot theorem (Bertrand 1887, André
1887) in Mathlib's form; the third statement is the orthogonality of characters of a cyclic
group. The readings on the machine are `agent-inferred` and stand in the record.

[proved-standard; formal-checked] What is proved: `nested_eq_one`, `crossed_eq_one_iff`,
`crossed_eq_one_of_comm`, `crossed_swaps_ne_one`, `affineTracks_crossed`, `card_balanced`,
`card_nested`, `nested_share`, `counts_at_three`, `mean_turn`, `linear_reading_mean`,
`turn_mul_mirror`, `no_linear_reading`, `pair_reads_relative_phase`.

Not proved here: that the invariants of `SU(2)` in an even tensor power of its plane are spanned
by the pairings that do not cross and number `catalan n` (Rumer, Teller and Weyl 1932); the
record cites it and the atlas row carries it in its scope.
-/

namespace Holonics.HNN.NestedPairs

open Complex ComplexConjugate Finset
open Holonics.HNN.CarryGroupTracking (AffineTracks affineTracks_comm)

variable {Γ ι : Type*}

/-! ## 1. Crossed and nested pairs under a carry -/

/-- [definition] Two pairs nested: `a` opens, `b` opens, `b` closes, `a` closes. -/
def nested [Group Γ] (a b : Γ) : Γ := a * b * b⁻¹ * a⁻¹

/-- [definition] Two pairs crossed: `a` opens, `b` opens, `a` closes, `b` closes. -/
def crossed [Group Γ] (a b : Γ) : Γ := a * b * a⁻¹ * b⁻¹

/-- [proved-standard; formal-checked] Nested pairs return the carry in every group. -/
theorem nested_eq_one [Group Γ] (a b : Γ) : nested a b = 1 := by
  unfold nested
  group

/-- [proved-standard; formal-checked] **Crossed pairs return the carry exactly where the two
elements commute.** -/
theorem crossed_eq_one_iff [Group Γ] (a b : Γ) : crossed a b = 1 ↔ a * b = b * a := by
  unfold crossed
  constructor
  · intro h
    have h2 : a * b * a⁻¹ * b⁻¹ * (b * a) = b * a := by rw [h, one_mul]
    have h3 : a * b * a⁻¹ * b⁻¹ * (b * a) = a * b := by group
    rw [← h3, h2]
  · intro h
    rw [h]
    group

/-- [proved-standard; formal-checked] A commuting carry reads crossed pairs as closed. -/
theorem crossed_eq_one_of_comm {Γ : Type*} [CommGroup Γ] (a b : Γ) : crossed a b = 1 :=
  (crossed_eq_one_iff a b).2 (mul_comm a b)

/-- [proved-standard; formal-checked] Two swaps of three things tell crossed pairs from nested
ones: their crossed word is not the identity. -/
theorem crossed_swaps_ne_one :
    crossed (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) (Equiv.swap 0 2 : Equiv.Perm (Fin 3)) ≠ 1 := by
  unfold crossed
  decide

/-- [proved-derived; formal-checked] **A bank of circles that are not coupled reads a crossed
word as it reads the nested one,** at every state and whatever its width: on a torsion group
whose every right multiplication is one affine step on every circle. -/
theorem affineTracks_crossed [Group Γ] (htor : ∀ g : Γ, IsOfFinOrder g) {f : Γ → ι → ℂ}
    (hf : AffineTracks f) (γ a b : Γ) : f (γ * crossed a b) = f (γ * nested a b) := by
  have h := affineTracks_comm htor hf (γ * a * b) a⁻¹ b⁻¹
  have e1 : γ * crossed a b = γ * a * b * a⁻¹ * b⁻¹ := by
    unfold crossed
    group
  have e2 : γ * nested a b = γ * a * b * b⁻¹ * a⁻¹ := by
    unfold nested
    group
  rw [e1, e2, h]

/-! ## 2. One word with equal counts in `n + 1` is nested -/

/-- [proved-standard; formal-checked] The words of length `2n` with as many openers as closers,
counted as the choices of the openers' `n` places among `2n`. -/
theorem card_balanced (n : ℕ) :
    (powersetCard n (univ : Finset (Fin (2 * n)))).card = n.centralBinom := by
  rw [card_powersetCard, card_univ, Fintype.card_fin, Nat.centralBinom_eq_two_mul_choose]

/-- [proved-standard; formal-checked] The nested words of length `2n` (Mathlib's Dyck words). -/
theorem card_nested (n : ℕ) :
    Fintype.card { p : DyckWord // p.semilength = n } = catalan n :=
  DyckWord.card_dyckWord_semilength_eq_catalan n

/-- [proved-standard; formal-checked] **One word with equal counts in `n + 1` is nested.** -/
theorem nested_share (n : ℕ) :
    (n + 1) * Fintype.card { p : DyckWord // p.semilength = n }
      = (powersetCard n (univ : Finset (Fin (2 * n)))).card := by
  rw [card_nested, card_balanced, succ_mul_catalan_eq_centralBinom]

/-- [proved-standard; formal-checked] At three pairs: twenty words with equal counts, five of
them nested. -/
theorem counts_at_three : Nat.centralBinom 3 = 20 ∧ catalan 3 = 5 :=
  ⟨by decide, catalan_three⟩

/-! ## 3. A relative phase is held by a pair, and by no linear reading -/

variable {n : ℕ} {ζ : ℂ}

/-- [proved-standard; formal-checked] A turn through a whole cycle has no mean. -/
theorem mean_turn (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n) : ∑ k ∈ range n, ζ ^ k = 0 :=
  hζ.geom_sum_eq_zero hn

/-- [proved-standard; formal-checked] Every reading of a strand that is real-linear in it,
`c·z + d·z̄`, has mean zero over the cycle. -/
theorem linear_reading_mean (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n) (c d : ℂ) :
    ∑ k ∈ range n, (c * ζ ^ k + d * conj (ζ ^ k)) = 0 := by
  have hc : ∑ k ∈ range n, conj (ζ ^ k) = conj (∑ k ∈ range n, ζ ^ k) :=
    (map_sum (starRingEnd ℂ) _ _).symm
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, hc, mean_turn hζ hn, map_zero, mul_zero, mul_zero,
    add_zero]

/-- [proved-standard; formal-checked] A turn times its mirror is one: the product carries no
turn. -/
theorem turn_mul_mirror (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n) (k : ℕ) :
    ζ ^ k * conj (ζ ^ k) = 1 := by
  have h1 : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one (by omega)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, h1]
  simp

/-- [proved-derived; formal-checked] **No reading that is real-linear in two strands holds the
phase between them:** with the second strand the first turned by `u`, every such reading has mean
zero over the cycle, for every `u`. -/
theorem no_linear_reading (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n) (u c d c' d' : ℂ) :
    ∑ k ∈ range n,
      (c * ζ ^ k + d * conj (ζ ^ k) + (c' * (u * ζ ^ k) + d' * conj (u * ζ ^ k))) = 0 := by
  have h2 : ∀ k ∈ range n, c' * (u * ζ ^ k) + d' * conj (u * ζ ^ k)
      = c' * u * ζ ^ k + d' * conj u * conj (ζ ^ k) := by
    intro k _
    rw [map_mul]
    ring
  rw [sum_add_distrib, linear_reading_mean hζ hn c d, sum_congr rfl h2,
    linear_reading_mean hζ hn (c' * u) (d' * conj u), add_zero]

/-- [proved-derived; formal-checked] **A pair reads the phase between two strands:** each strand
alone has mean zero, and the second strand times the mirror of the first has mean `u`. -/
theorem pair_reads_relative_phase (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n) (u : ℂ) :
    (∑ k ∈ range n, ζ ^ k = 0) ∧ (∑ k ∈ range n, u * ζ ^ k = 0) ∧
      ∑ k ∈ range n, u * ζ ^ k * conj (ζ ^ k) = n * u := by
  refine ⟨mean_turn hζ hn, ?_, ?_⟩
  · rw [← mul_sum, mean_turn hζ hn, mul_zero]
  · have h : ∀ k ∈ range n, u * ζ ^ k * conj (ζ ^ k) = u := by
      intro k _
      rw [mul_assoc, turn_mul_mirror hζ hn k, mul_one]
    rw [sum_congr rfl h, sum_const, card_range, nsmul_eq_mul]

end Holonics.HNN.NestedPairs
