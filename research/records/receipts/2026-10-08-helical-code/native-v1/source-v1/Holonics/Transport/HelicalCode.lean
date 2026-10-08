import Holonics.Transport.HelicalPairInteraction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Group.Semiconj.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# The helical code: a word on a helix read through an involutive pairing, residue frames and a quotient

[definition] The helical code is the composition of the elementary objects through which a Holon's
encoding is read (`docs/ELEMENTARY_OBJECTS.md`, "The helical code: how Holons encode"): a strand,
a word on a navigator's helix; its pairing by a fixed-point-free involution `σ` through helical pair
contacts, read backward; receivers' residue frames (a receiver reads each position as a residue, the
phase modulo its period; a residue class recurs across the epochs between its section arrivals, and
a position is read as residue, whole winding and epoch); a decoder, the quotient by the receiver's
kernel, which the admitted future fixes (what is designed is the placement: a coordinated
substitution is absorbed exactly when its reached difference `P(T u) − P(u)` lies in that kernel);
and the linking number of closed strands. This module states laws of that composition. It is a
statement of an object, not a decoder for any task: the alphabet is arbitrary and nothing here
reads, parses or classifies a particular language.

[definition] Owners it builds on and does not restate: `Transport/HelicalPairInteraction`
(`phaseTransport` `S⁻ᵈPSᵈ`, `reflectedReturn` with its involution and fixed-point laws,
`boundary_involution_reciprocal`, `menu_loop_closure`, `lock_iff_zero_power`);
`Geometry/PairResonance.diagonal_step_generates_the_coprime_torus` and
`HNN/Prediction.joint_residue_determines_position` own the meet of two frames of coprime periods
reading the same lifted clock (exactly one position per pair of residues below the product of the
periods; the residues fix the position only modulo that product, and the whole winding supplies the
rest), and are cited, not re-proved; `Transport/SourceMoment` owns the streaming form of the
phase-carried moment; `Foundation/TopologicalReceiver` owns the geometric crossing sign and linking
number, which this module reads only through ℤ-valued signs.

[proved-derived; formal-checked] Part one states, for an arbitrary alphabet `α` and `σ : α → α`:
- §1 `complementReverse σ w = σ(w)ᴿ` is an anti-automorphism of words
  (`complementReverse_append`), an involution when `σ` is (`complementReverse_involutive`), and
  length-preserving;
- §2 when `σ` fixes no letter, a word equal to its own pairing has even length
  (`even_length_of_fixed`); for an involution the fixed words of length `2m` correspond to the
  words of length `m`, each fixed word being its first half followed by that half's pairing
  (`firstHalfEquiv`, `card_fixedWords`);
- §3 the pairing read through any frame `A` (a phase `d` of the helix, `A = Sᵈ`, or a rotor's
  stepping), `A⁻¹σA = phaseTransport S σ d`, is again a fixed-point-free involution, and it is
  reciprocal (`phaseTransport_pairing`, `phaseTransport_reciprocal`); the self-paired words at every
  phase have even length and the same count (`card_fixedWords_at_phase`);
- §4 one crossing change at a family of ℤ-valued crossing signs moves their sum by exactly twice
  the reversed sign (`sum_crossingChange_sub`); the linking number, half the signed sum over the
  crossings between two components, therefore moves by exactly the reversed sign, `±1`
  (`half_sum_crossingChange`).

[proved-derived; formal-checked] Part two states the perfected laws of the guide, each with its
hypotheses named:
- §5 resonance on a strand. For a fixed advance (the uniform tick `τ(k) = k` of one navigator, the
  tick operator `x = Ĝ⁻¹` acting on a carrier), a word repeating with period `p` has
  `m_(Np) = Σ_(j<N) (x^p)ʲ m_p` and `(1 − x^p) m_(Np) = (1 − (x^p)ᴺ) m_p`, in any monoid acting
  distributively on an additive group (`geom_smul_sum_sub`, `strandFace_repeatWord`,
  `strandFace_repeatWord_sub`, `strandFace_repeatWord_one_sub`); when the period is whole turns on
  the face, `x^p m_p = m_p`, then `m_(Np) = N·m_p` (`strandFace_repeatWord_of_fixed`);
- §6 the partner's face, [conditional; formal-checked] on a declared equivariant embedding: an
  additive carrier map `J` with `J E = E σ` and `J Ĝ = Ĝ⁻¹ J`. For constant openings `α, β` of the
  strand and its partner, `f_β(σ̄ u) = J Ĝ^(n−1+α+β) f_α(u)` (`face_complementReverse`); `α = β = 0`
  is the declared case. When `J` is an involution, `v ↦ J (Ĝᶻ v)` is one (`partner_map_involutive`).
  *The uniform tick is the named hypothesis*: located advances and letter-selected screws need
  their own relation, `J S_a J = S_(σ a)⁻¹`, and are out of scope;
- §7 the dihedral pairing. On the index line the half-turn `k ↦ c − k` inverts the shift
  (`halfTurn_inverts_shift`). In any group with `U² = 1` and `U S U = S⁻¹`: `(SʲU)² = 1` and
  `S⁻ᵏ U Sᵏ = S⁻²ᵏ U` (`dihedral_reflection_sq`, `dihedral_conj`). On the `2p` frames
  `ZMod p × Bool`, with `t` the unit shift and `u_c (r, b) = (c − r, ¬b)`: `u_c t u_c = t⁻¹`
  pointwise, `t^j` is the shift by `j`, and the `2p` maps `t^j`, `t^j ∘ u_c` send a base frame to
  every frame exactly once (`frameFlip_frameShift_frameFlip`, `frameShift_iterate`,
  `dihedralFrame_bijective`);
- §8 four letters. The fixed-point-free involutions of `Fin 4` are exactly the three nonidentity
  translations of the Klein group `V`, which is closed, abelian and regular, and the pairing
  commutes with it, `σ (v·a) = v·σ a` (`free_involution_iff`, `card_free_involutions_fin4`,
  `kleinAct_assoc`, `kleinAct_comm`, `kleinAct_regular`, `free_involution_commutes`);
- §9 the inner code. With the partner intact, the contacts that slip are exactly the substituted
  positions, and at each the two repairs differ (`slipped_contacts_eq`, `slipped_repairs_distinct`);
- §10 a duplex passage on a ribbon, with signs `s, e·s, e·s, s`: the inter-strand sum moves by
  `−4es` and the linking number by `−2es` (`duplex_passage_sum`, `duplex_passage_linking`).

[open] Owed (#62): `Lk = Tw + Wr` (Călugăreanu–White–Fuller), first for polygonal ribbons, with the
ribbon writhe as the core's Gauss sum, and with it the sign pattern of a duplex passage, which §10
takes as declared; the projection invariance of `Lk` and `HalvesAgree`
(`Foundation/TopologicalReceiver`), without which "only a crossing moves `Lk`" is a statement about
the signed sum of a fixed diagram, not a theorem about motions of curves; the decoder's absorption
law (a coordinated substitution is absorbed exactly when its reached difference lies in the
receiver's kernel); the partner's face for letter-selected screws and located clocks; and the
declared embedding of letters into contact velocities that reads complementarity as zero slip
through `lock_iff_zero_power`.

Written without a compiler: the `formal-checked` tag on each statement stands once the validation
queue's kernel receipt exists.

[established-bounded; formal-checked] Scope: finite lists, finite groups of permutations, finite
sums of integers and the finite tables of `Fin 4` and `ZMod p × Bool`. No `axiom`, no `sorry`, no
`native_decide`.
-/

namespace Holonics.Transport.HelicalCode

open Holonics.Transport.HelicalPairInteraction

/-! ## 1. The pairing of words is an involutive anti-automorphism -/

section Words

variable {α : Type*}

/-- [definition] The complement-reverse `σ̄(w) = σ(w)ᴿ`: each letter paired by `σ`, read backward.
Position `k` of the second strand locks against position `n−1−k` of the first. -/
def complementReverse (σ : α → α) (w : List α) : List α := (w.map σ).reverse

@[simp] theorem complementReverse_nil (σ : α → α) : complementReverse σ ([] : List α) = [] := by
  simp [complementReverse]

theorem complementReverse_cons (σ : α → α) (a : α) (w : List α) :
    complementReverse σ (a :: w) = complementReverse σ w ++ [σ a] := by
  simp only [complementReverse, List.map_cons, List.reverse_cons]

/-- [proved-derived; formal-checked] **An anti-automorphism of words**: the second strand of a join
is the join of the second strands in the opposite order, `σ̄(vw) = σ̄(w)σ̄(v)`. -/
theorem complementReverse_append (σ : α → α) (u v : List α) :
    complementReverse σ (u ++ v) = complementReverse σ v ++ complementReverse σ u := by
  simp only [complementReverse, List.map_append, List.reverse_append]

theorem length_complementReverse (σ : α → α) (w : List α) :
    (complementReverse σ w).length = w.length := by
  simp only [complementReverse, List.length_reverse, List.length_map]

/-- [proved-derived; formal-checked] **An involution**: when `σ` is, so is the pairing of words. -/
theorem complementReverse_involutive {σ : α → α} (hσ : Function.Involutive σ) :
    Function.Involutive (complementReverse σ) := by
  intro w
  first
    | (simp only [complementReverse, List.map_reverse, List.reverse_reverse, List.map_map,
        hσ.comp_self, List.map_id]; done)
    | simp [complementReverse, hσ.comp_self]

/-! ## 2. Self-paired words have even length and are determined by their first half -/

/-- [proved-derived; formal-checked] The middle letter would be paired with itself: if `σ` fixes no
letter, a word `u ++ c :: t` with `|t| = |u|` is not its own complement-reverse. -/
theorem complementReverse_ne_of_middle {σ : α → α} (hfree : ∀ a, σ a ≠ a) (u t : List α) (c : α)
    (hlen : t.length = u.length) :
    complementReverse σ (u ++ c :: t) ≠ u ++ c :: t := by
  intro h
  rw [complementReverse_append, complementReverse_cons, List.append_assoc,
    List.singleton_append] at h
  have h2 := List.append_inj h ((length_complementReverse σ t).trans hlen)
  exact hfree c (List.cons.inj h2.2).1

/-- [proved-derived; formal-checked] **A self-paired word has even length** when no letter is paired
with itself: the fixed words of a fixed-point-free pairing are the even palindromes. Involutivity
of `σ` is not used. -/
theorem even_length_of_fixed {σ : α → α} (hfree : ∀ a, σ a ≠ a) {w : List α}
    (hw : complementReverse σ w = w) : Even w.length := by
  obtain ⟨k, hk | hk⟩ : ∃ k, w.length = 2 * k ∨ w.length = 2 * k + 1 :=
    ⟨w.length / 2, by omega⟩
  · exact Nat.even_iff.mpr (by omega)
  · exfalso
    have hsplit : w.take k ++ w.drop k = w := List.take_append_drop k w
    have hu : (w.take k).length = k := List.length_take_of_le (by omega)
    have hr : (w.drop k).length = k + 1 := by rw [List.length_drop]; omega
    obtain ⟨c, t, ht⟩ := List.exists_cons_of_length_eq_add_one hr
    have htl : t.length = k := by
      have h2 := hr
      rw [ht, List.length_cons] at h2
      omega
    have hfix : complementReverse σ (w.take k ++ c :: t) = w.take k ++ c :: t := by
      rw [← ht, hsplit]
      exact hw
    exact complementReverse_ne_of_middle hfree (w.take k) t c (htl.trans hu.symm) hfix

/-- [proved-derived; formal-checked] The second half of a self-paired word is the pairing of its
first half. -/
theorem eq_complementReverse_of_fixed {σ : α → α} {u r : List α} (hlen : u.length = r.length)
    (hw : complementReverse σ (u ++ r) = u ++ r) : r = complementReverse σ u := by
  rw [complementReverse_append] at hw
  have h2 := List.append_inj hw ((length_complementReverse σ r).trans hlen.symm)
  exact h2.2.symm

/-- [proved-derived; formal-checked] **The first half determines a self-paired word**: a word of
length `2m` equal to its own pairing is its first half followed by that half's pairing. -/
theorem fixed_eq_take_append {σ : α → α} {m : ℕ} {w : List α} (hlen : w.length = 2 * m)
    (hw : complementReverse σ w = w) : w = w.take m ++ complementReverse σ (w.take m) := by
  have hsplit : w.take m ++ w.drop m = w := List.take_append_drop m w
  have hu : (w.take m).length = m := List.length_take_of_le (by omega)
  have hr : (w.drop m).length = m := by rw [List.length_drop]; omega
  have hfix : complementReverse σ (w.take m ++ w.drop m) = w.take m ++ w.drop m := by
    rw [hsplit]
    exact hw
  have h2 := eq_complementReverse_of_fixed (hu.trans hr.symm) hfix
  calc w = w.take m ++ w.drop m := hsplit.symm
    _ = w.take m ++ complementReverse σ (w.take m) := by rw [h2]

/-- [proved-derived; formal-checked] Every word followed by its pairing is self-paired. -/
theorem complementReverse_append_self {σ : α → α} (hσ : Function.Involutive σ) (u : List α) :
    complementReverse σ (u ++ complementReverse σ u) = u ++ complementReverse σ u := by
  rw [complementReverse_append, complementReverse_involutive hσ u]

theorem length_append_complementReverse (σ : α → α) (u : List α) :
    (u ++ complementReverse σ u).length = 2 * u.length := by
  rw [List.length_append, length_complementReverse]
  omega

/-- [proved-derived; formal-checked] **Fixed words of length `2m` correspond to words of length
`m`**: `u ↦ u ++ σ̄(u)` and the first half are inverse. -/
def firstHalfEquiv {σ : α → α} (hσ : Function.Involutive σ) (m : ℕ) :
    {w : List α // w.length = 2 * m ∧ complementReverse σ w = w} ≃ {u : List α // u.length = m} where
  toFun w := ⟨w.1.take m, List.length_take_of_le (by have := w.2.1; omega)⟩
  invFun u := ⟨u.1 ++ complementReverse σ u.1,
    by rw [length_append_complementReverse, u.2], complementReverse_append_self hσ u.1⟩
  left_inv w := by
    apply Subtype.ext
    show w.1.take m ++ complementReverse σ (w.1.take m) = w.1
    exact (fixed_eq_take_append w.2.1 w.2.2).symm
  right_inv u := by
    apply Subtype.ext
    show (u.1 ++ complementReverse σ u.1).take m = u.1
    exact List.take_left' u.2

/-- [proved-derived; formal-checked] **The count of self-paired words**: a pairing by an involution
has `|A|^m` self-paired words of length `2m`, whether or not `σ` has fixed letters. -/
theorem card_fixedWords [Fintype α] {σ : α → α} (hσ : Function.Involutive σ) (m : ℕ) :
    Nat.card {w : List α // w.length = 2 * m ∧ complementReverse σ w = w}
      = Fintype.card α ^ m := by
  rw [Nat.card_congr (firstHalfEquiv hσ m)]
  have e : {u : List α // u.length = m} ≃ List.Vector α m := by
    first
      | exact Equiv.refl _
      | exact ⟨fun u => ⟨u.1, u.2⟩, fun v => ⟨v.1, v.2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, card_vector]

/-! ## 3. The pairing read through every frame -/

/-- [proved-derived; formal-checked] The phase transport is the reflected return of the carried
shift: the pairing read at phase `d` is `σ` read through the frame `Sᵈ`. -/
theorem phaseTransport_eq_reflectedReturn {G : Type*} [Group G] (S P : G) (d : ℤ) :
    phaseTransport S P d = reflectedReturn (S ^ d) P := by
  simp only [phaseTransport, reflectedReturn, _root_.zpow_neg]

/-- [proved-derived; formal-checked] An involutive reflection is involutive at every phase. -/
theorem phaseTransport_mul_self {G : Type*} [Group G] (S F : G) (hF : F * F = 1) (d : ℤ) :
    phaseTransport S F d * phaseTransport S F d = 1 := by
  rw [phaseTransport_eq_reflectedReturn]
  exact reflectedReturn_involutive (S ^ d) F hF

/-- [proved-derived; formal-checked] A fixed-point-free reflection is fixed-point-free at every
phase: no letter pairs with itself at any frame. -/
theorem phaseTransport_ne_self (S F : Equiv.Perm α) (hF : ∀ x, F x ≠ x) (d : ℤ) (x : α) :
    phaseTransport S F d x ≠ x := by
  rw [phaseTransport_eq_reflectedReturn]
  exact reflectedReturn_no_fixed_point (S ^ d) F hF x

/-- [proved-derived; formal-checked] A permutation squaring to the identity is an involution of the
points it moves. -/
theorem involutive_of_mul_self {p : Equiv.Perm α} (h : p * p = 1) : Function.Involutive p := by
  intro x
  have := congrArg (fun q : Equiv.Perm α => q x) h
  simpa [Equiv.Perm.mul_apply] using this

/-- [proved-derived; formal-checked] **The pairing read at any phase is a fixed-point-free
involution.** `S⁻ᵈσSᵈ` is again an involution, and no letter pairs with itself. -/
theorem phaseTransport_pairing (S σ : Equiv.Perm α) (hσ : σ * σ = 1) (hfree : ∀ x, σ x ≠ x)
    (d : ℤ) :
    Function.Involutive (phaseTransport S σ d) ∧ ∀ x, phaseTransport S σ d x ≠ x :=
  ⟨involutive_of_mul_self (phaseTransport_mul_self S σ hσ d), phaseTransport_ne_self S σ hfree d⟩

/-- [proved-derived; formal-checked] **The pairing is reciprocal at every phase**: each strand is
the other's key. -/
theorem phaseTransport_reciprocal (S σ : Equiv.Perm α) (hσ : σ * σ = 1) (d : ℤ) (a b : α) :
    phaseTransport S σ d a = b ↔ phaseTransport S σ d b = a :=
  boundary_involution_reciprocal (phaseTransport S σ d) (phaseTransport_mul_self S σ hσ d) a b

/-- [proved-derived; formal-checked] The pairing of words read at any phase is an involution. -/
theorem complementReverse_involutive_at_phase (S σ : Equiv.Perm α) (hσ : σ * σ = 1) (d : ℤ) :
    Function.Involutive (complementReverse ⇑(phaseTransport S σ d)) :=
  complementReverse_involutive (involutive_of_mul_self (phaseTransport_mul_self S σ hσ d))

/-- [proved-derived; formal-checked] At every phase the self-paired words of a fixed-point-free
pairing have even length. -/
theorem even_length_of_fixed_at_phase (S σ : Equiv.Perm α) (hfree : ∀ x, σ x ≠ x) (d : ℤ)
    {w : List α} (hw : complementReverse ⇑(phaseTransport S σ d) w = w) : Even w.length :=
  even_length_of_fixed (phaseTransport_ne_self S σ hfree d) hw

/-- [proved-derived; formal-checked] **The capacity of the code does not depend on the phase**: at
every frame the self-paired words of length `2m` are counted by their first halves, `|A|^m`. -/
theorem card_fixedWords_at_phase [Fintype α] (S σ : Equiv.Perm α) (hσ : σ * σ = 1) (d : ℤ)
    (m : ℕ) :
    Nat.card {w : List α // w.length = 2 * m ∧ complementReverse ⇑(phaseTransport S σ d) w = w}
      = Fintype.card α ^ m :=
  card_fixedWords (involutive_of_mul_self (phaseTransport_mul_self S σ hσ d)) m

end Words

/-! ## 4. Only a crossing changes the signed crossing sum -/

section Crossings

variable {ι : Type*} [DecidableEq ι]

/-- [definition] A crossing change at crossing `i` of a family of crossing signs: over and under
exchange there, so its sign reverses and every other crossing is untouched. The linking number of
two closed curves is half the sum of the signs of the crossings between them
(`Foundation/TopologicalReceiver.linkingNumber`: `signs k = (cross k).sign w`). -/
def crossingChange (signs : ι → ℤ) (i : ι) : ι → ℤ := Function.update signs i (-signs i)

theorem crossingChange_self (signs : ι → ℤ) (i : ι) : crossingChange signs i i = -signs i := by
  first
    | exact Function.update_self i (-signs i) signs
    | simp [crossingChange]

theorem crossingChange_of_ne (signs : ι → ℤ) {i k : ι} (hk : k ≠ i) :
    crossingChange signs i k = signs k := by
  first
    | exact Function.update_of_ne hk (-signs i) signs
    | simp [crossingChange, hk]

/-- [proved-derived; formal-checked] **One crossing change moves the signed sum by exactly twice the
sign it reverses**: `Σ' − Σ = −2·sᵢ`. -/
theorem sum_crossingChange_sub [Fintype ι] (signs : ι → ℤ) (i : ι) :
    ∑ k, crossingChange signs i k - ∑ k, signs k = -2 * signs i := by
  rw [← Finset.add_sum_erase Finset.univ (crossingChange signs i) (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ signs (Finset.mem_univ i), crossingChange_self signs i]
  have h : ∑ k ∈ Finset.univ.erase i, crossingChange signs i k
      = ∑ k ∈ Finset.univ.erase i, signs k :=
    Finset.sum_congr rfl fun k hk => crossingChange_of_ne signs (Finset.ne_of_mem_erase hk)
  rw [h]
  ring

/-- [proved-derived; formal-checked] For signs `±1`, one crossing change moves the signed sum by
`∓2`. -/
theorem sum_crossingChange_eq_pm_two [Fintype ι] (signs : ι → ℤ) (i : ι)
    (hi : signs i = 1 ∨ signs i = -1) :
    ∑ k, crossingChange signs i k - ∑ k, signs k = -2 ∨
      ∑ k, crossingChange signs i k - ∑ k, signs k = 2 := by
  have h := sum_crossingChange_sub signs i
  rcases hi with hi | hi
  · left
    omega
  · right
    omega

/-- [proved-derived; formal-checked] **The linking number, half the signed sum, moves by exactly the
reversed sign**: `±1` per crossing change. -/
theorem half_sum_crossingChange [Fintype ι] (signs : ι → ℤ) (i : ι) :
    ((∑ k, crossingChange signs i k : ℤ) : ℚ) / 2 - ((∑ k, signs k : ℤ) : ℚ) / 2
      = -(signs i : ℚ) := by
  have h := sum_crossingChange_sub signs i
  have h' : ((∑ k, crossingChange signs i k : ℤ) : ℚ) - ((∑ k, signs k : ℤ) : ℚ)
      = -2 * (signs i : ℚ) := by
    exact_mod_cast h
  linarith

end Crossings

/-! ## 5. Resonance: a word repeating in whole turns -/

section Resonance

variable {A M G : Type*} [Monoid G] [AddCommGroup M] [DistribMulAction G M]

/-- [proved-derived; formal-checked] The geometric sum of an action satisfies its one-step law:
`Σ_(j<N+1) yʲ • m = m + y • Σ_(j<N) yʲ • m`. -/
theorem geom_smul_sum_succ' (y : G) (m : M) (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), y ^ j • m = m + y • ∑ j ∈ Finset.range N, y ^ j • m := by
  have hs : ∑ j ∈ Finset.range N, y ^ (j + 1) • m = ∑ j ∈ Finset.range N, y • y ^ j • m :=
    Finset.sum_congr rfl fun j _ => by rw [smul_smul, pow_succ']
  rw [Finset.sum_range_succ', Finset.smul_sum, hs, pow_zero, one_smul, add_comm]

/-- [proved-derived; formal-checked] **The geometric identity for an action**, in any monoid acting
distributively on an additive group: `(1 − y) Σ_(j<N) yʲ = 1 − yᴺ`, read on a vector `m`. For a ring
acting on itself this is Mathlib's `mul_neg_geom_sum`. -/
theorem geom_smul_sum_sub (y : G) (m : M) (N : ℕ) :
    (∑ j ∈ Finset.range N, y ^ j • m) - y • ∑ j ∈ Finset.range N, y ^ j • m
      = m - y ^ N • m := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h1 : y • (y ^ N • m) = y ^ (N + 1) • m := by rw [smul_smul, pow_succ']
    rw [Finset.sum_range_succ, smul_add, h1]
    have key : ((∑ j ∈ Finset.range N, y ^ j • m) + y ^ N • m)
        - (y • ∑ j ∈ Finset.range N, y ^ j • m + y ^ (N + 1) • m)
        = ((∑ j ∈ Finset.range N, y ^ j • m) - y • ∑ j ∈ Finset.range N, y ^ j • m)
          + (y ^ N • m - y ^ (N + 1) • m) := by abel
    rw [key, ih]
    abel

/-- [proved-derived; formal-checked] The geometric identity for a ring `R` acting on a module:
`(1 − x) • Σ_(j<N) xʲ • v = (1 − xᴺ) • v`. -/
theorem one_sub_smul_geom_sum {R : Type*} [Ring R] [Module R M] (x : R) (v : M) (N : ℕ) :
    (1 - x) • (∑ j ∈ Finset.range N, x ^ j • v) = (1 - x ^ N) • v := by
  rw [sub_smul, one_smul, sub_smul, one_smul]
  exact geom_smul_sum_sub x v N

/-- [definition] The face of a word under the one-tick operator `x` (the inverse `Ĝ⁻¹` of the
navigator's tick): the phase-carried moment `m = Σ_k xᵏ • E(u_k)` of the strand, read from the
first letter, in the Horner form `m(a :: w) = E a + x • m(w)`. It is the strand face
`Σ_k Ĝ(τ(k))⁻¹ E(u_k)` for a **fixed advance**: the uniform tick `τ(k) = k` of one navigator.
Letter-selected screws and located clocks are not this face; for them the repeated word's own
monodromy over one period replaces `x^p`, and the occurrence count never stands in for the clock.
The streaming form of `Transport/SourceMoment` weights letter `k` by `U^(n−1−k)`: it reads the
newest letter first, the same sum from the other end. `E` is the encoder of letters into the
carrier `M`. -/
def strandFace (x : G) (E : A → M) : List A → M
  | [] => 0
  | a :: w => E a + x • strandFace x E w

theorem strandFace_singleton (x : G) (E : A → M) (a : A) : strandFace x E [a] = E a := by
  simp [strandFace]

/-- [proved-derived; formal-checked] **The face of a join**: the second word enters through the
phase it is placed at, `m(uv) = m(u) + x^|u| • m(v)`. -/
theorem strandFace_append (x : G) (E : A → M) (u v : List A) :
    strandFace x E (u ++ v) = strandFace x E u + x ^ u.length • strandFace x E v := by
  induction u with
  | nil => simp [strandFace]
  | cons a u ih =>
    first
      | (simp only [List.cons_append, strandFace, ih, smul_add, smul_smul, List.length_cons,
          pow_succ', add_assoc]; done)
      | simp [strandFace, ih, smul_add, smul_smul, pow_succ', add_assoc]

/-- [definition] The `N`-fold repeat of a word: a word repeating with period `|u|`. -/
def repeatWord (u : List A) : ℕ → List A
  | 0 => []
  | N + 1 => u ++ repeatWord u N

/-- [proved-derived; formal-checked] **A repeating word's face is a geometric sum of the period's
face**: `m_(Np) = Σ_(j<N) (x^p)ʲ • m_p`, with `p = |u|`. -/
theorem strandFace_repeatWord (x : G) (E : A → M) (u : List A) (N : ℕ) :
    strandFace x E (repeatWord u N)
      = ∑ j ∈ Finset.range N, (x ^ u.length) ^ j • strandFace x E u := by
  induction N with
  | zero => simp [repeatWord, strandFace]
  | succ N ih => rw [repeatWord, strandFace_append, ih, geom_smul_sum_succ']

/-- [proved-derived; formal-checked] **Resonance on a strand**: with `x = Ĝ⁻¹` and period `p`,
`m_(Np) − x^p • m_(Np) = m_p − x^(pN) • m_p`, that is `(1 − Ĝ⁻ᵖ) m_(Np) = (1 − Ĝ⁻ᴺᵖ) m_p`, for a
fixed advance. -/
theorem strandFace_repeatWord_sub (x : G) (E : A → M) (u : List A) (N : ℕ) :
    strandFace x E (repeatWord u N) - x ^ u.length • strandFace x E (repeatWord u N)
      = strandFace x E u - (x ^ u.length) ^ N • strandFace x E u := by
  rw [strandFace_repeatWord]
  exact geom_smul_sum_sub (x ^ u.length) (strandFace x E u) N

/-- [proved-derived; formal-checked] The same law for a ring acting on a module:
`(1 − x^p) • m_(Np) = (1 − (x^p)ᴺ) • m_p`. -/
theorem strandFace_repeatWord_one_sub {R : Type*} [Ring R] [Module R M] (x : R) (E : A → M)
    (u : List A) (N : ℕ) :
    (1 - x ^ u.length) • strandFace x E (repeatWord u N)
      = (1 - (x ^ u.length) ^ N) • strandFace x E u := by
  rw [strandFace_repeatWord]
  exact one_sub_smul_geom_sum (x ^ u.length) (strandFace x E u) N

/-- [proved-derived; formal-checked] **In resonance the face grows with every repeat**: if the
period is whole turns on the face (`x^p • m_p = m_p`; `x^p = 1` is the case of the identity), then
`m_(Np) = N • m_p`. -/
theorem strandFace_repeatWord_of_fixed (x : G) (E : A → M) (u : List A)
    (hres : x ^ u.length • strandFace x E u = strandFace x E u) (N : ℕ) :
    strandFace x E (repeatWord u N) = N • strandFace x E u := by
  have hpow : ∀ j : ℕ, (x ^ u.length) ^ j • strandFace x E u = strandFace x E u := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', mul_smul, ih, hres]
  have hsum : ∑ j ∈ Finset.range N, (x ^ u.length) ^ j • strandFace x E u
      = ∑ j ∈ Finset.range N, strandFace x E u := Finset.sum_congr rfl fun j _ => hpow j
  rw [strandFace_repeatWord, hsum, Finset.sum_const, Finset.card_range]

/-- [proved-derived; formal-checked] The face of a word given as a function on `Fin n` is the stated
sum `Σ_k xᵏ • E(u_k)`. -/
theorem strandFace_ofFn (x : G) (E : A → M) (n : ℕ) :
    ∀ u : Fin n → A, strandFace x E (List.ofFn u) = ∑ k : Fin n, x ^ (k : ℕ) • E (u k) := by
  induction n with
  | zero => intro u; simp [strandFace]
  | succ n ih =>
    intro u
    first
      | (rw [List.ofFn_succ, strandFace, ih (fun i => u i.succ), Fin.sum_univ_succ,
          Finset.smul_sum]; simp [pow_succ', smul_smul]; done)
      | simp [List.ofFn_succ, strandFace, ih, Fin.sum_univ_succ, Finset.smul_sum, pow_succ',
          smul_smul]

end Resonance

/-! ## 6. The partner's face -/

section Partner

variable {A M G : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- [definition] The face of a strand opening at tick `α : ℤ`, for the navigator `g`:
`f_α(u) = Σ_k g^(−(k+α)) • E(u_k)`. The tick of letter `k` is `k + α`: a declared uniform advance
by the one navigator, with a constant opening. -/
def face (g : G) (E : A → M) (α : ℤ) (w : List A) : M := g ^ (-α) • strandFace g⁻¹ E w

/-- [proved-derived; formal-checked] The face of an opening at `α` is the stated sum over the
letters of `u : Fin n → A`. -/
theorem face_ofFn (g : G) (E : A → M) (α : ℤ) {n : ℕ} (u : Fin n → A) :
    face g E α (List.ofFn u) = ∑ k : Fin n, g ^ (-(((k : ℕ) : ℤ) + α)) • E (u k) := by
  unfold face
  rw [strandFace_ofFn, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (g⁻¹) ^ (k : ℕ) = g ^ (-((k : ℕ) : ℤ)) := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  have hexp : -α + -((k : ℕ) : ℤ) = -(((k : ℕ) : ℤ) + α) := by ring
  rw [smul_smul, hk, ← zpow_add, hexp]

/-- [proved-derived; formal-checked] **A carrier map that inverts the navigator inverts every
integer power of it**: from the single relation `J Ĝ = Ĝ⁻¹ J` (that is `J Ĝ J = Ĝ⁻¹` on an
involution) follows `J Ĝᶻ = Ĝ⁻ᶻ J` for all `z : ℤ`. -/
theorem J_zpow (g : G) (J : M →+ M) (hJg : ∀ v, J (g • v) = g⁻¹ • J v) (z : ℤ) :
    ∀ v : M, J (g ^ z • v) = g ^ (-z) • J v := by
  have hinv : ∀ v, J (g⁻¹ • v) = g • J v := by
    intro v
    calc J (g⁻¹ • v) = g • g⁻¹ • J (g⁻¹ • v) := (smul_inv_smul g _).symm
      _ = g • J v := by rw [← hJg (g⁻¹ • v), smul_inv_smul]
  refine Int.induction_on z ?_ ?_ ?_
  · intro v
    simp
  · intro i ih v
    have e1 : g ^ ((i : ℤ) + 1) = g ^ (i : ℤ) * g := zpow_add_one g i
    have hexp : -((i : ℤ) + 1) = -(i : ℤ) - 1 := by ring
    have e2 : g ^ (-((i : ℤ) + 1)) = g ^ (-(i : ℤ)) * g⁻¹ := by
      rw [hexp, zpow_sub_one]
    rw [e1, e2, mul_smul, mul_smul, ih, hJg]
  · intro i ih v
    have e1 : g ^ (-(i : ℤ) - 1) = g ^ (-(i : ℤ)) * g⁻¹ := zpow_sub_one g _
    have hexp : -(-(i : ℤ) - 1) = -(-(i : ℤ)) + 1 := by ring
    have e2 : g ^ (-(-(i : ℤ) - 1)) = g ^ (-(-(i : ℤ))) * g := by
      rw [hexp, zpow_add_one]
    rw [e1, e2, mul_smul, mul_smul, ih, hinv]

/-- [proved-derived; formal-checked] The natural-power form: `J Ĝᵐ = Ĝ⁻ᵐ J`. -/
theorem J_pow (g : G) (J : M →+ M) (hJg : ∀ v, J (g • v) = g⁻¹ • J v) (m : ℕ) (v : M) :
    J (g ^ m • v) = (g⁻¹) ^ m • J v := by
  rw [inv_pow]
  have h := J_zpow g J hJg (m : ℤ) v
  rwa [zpow_natCast, zpow_neg, zpow_natCast] at h

/-- [conditional; formal-checked] **The partner's face, one-tick form.** Let `J` be an additive
map of the carrier that is the dyad half-turn of the encoder, `J (E a) = E (σ a)`, and inverts the
navigator, `J (g • v) = g⁻¹ • J v`. Then the face of the partner strand `σ̄(w)` satisfies
`g⁻¹ • m(σ̄ w) = J (g^n • m(w))`, `n = |w|`, for every word, the empty one included. Involutivity of
`J` is not used here. -/
theorem strandFace_complementReverse_nat (g : G) (E : A → M) (σ : A → A) (J : M →+ M)
    (hJE : ∀ a, J (E a) = E (σ a)) (hJg : ∀ v, J (g • v) = g⁻¹ • J v) (w : List A) :
    g⁻¹ • strandFace g⁻¹ E (complementReverse σ w)
      = J (g ^ w.length • strandFace g⁻¹ E w) := by
  induction w with
  | nil => simp [strandFace]
  | cons a w ih =>
    have hlen : (complementReverse σ w).length = w.length := length_complementReverse σ w
    have hsingle : strandFace g⁻¹ E [σ a] = E (σ a) := strandFace_singleton g⁻¹ E (σ a)
    have hpow1 : g ^ (w.length + 1) * g⁻¹ = g ^ w.length := by
      rw [pow_succ, mul_assoc, mul_inv_cancel, mul_one]
    have hJa : J (g ^ (w.length + 1) • E a) = (g⁻¹) ^ (w.length + 1) • E (σ a) := by
      rw [J_pow g J hJg, hJE]
    try rw [List.length_cons]
    calc g⁻¹ • strandFace g⁻¹ E (complementReverse σ (a :: w))
        = g⁻¹ • (strandFace g⁻¹ E (complementReverse σ w) + (g⁻¹) ^ w.length • E (σ a)) := by
          rw [complementReverse_cons, strandFace_append, hlen, hsingle]
      _ = g⁻¹ • strandFace g⁻¹ E (complementReverse σ w) + (g⁻¹) ^ (w.length + 1) • E (σ a) := by
          rw [smul_add, smul_smul, pow_succ']
      _ = J (g ^ w.length • strandFace g⁻¹ E w) + (g⁻¹) ^ (w.length + 1) • E (σ a) := by
          rw [ih]
      _ = J (g ^ (w.length + 1) • E a) + J (g ^ (w.length + 1) • g⁻¹ • strandFace g⁻¹ E w) := by
          rw [hJa, smul_smul, hpow1]
          exact add_comm _ _
      _ = J (g ^ (w.length + 1) • strandFace g⁻¹ E (a :: w)) := by
          rw [strandFace, smul_add, map_add]

/-- [conditional; formal-checked] **The partner's face with constant openings.** Under the
hypotheses of the one-tick form, for integer openings `α` of the strand and `β` of the partner,
`f_β(σ̄ u) = J (g^(n−1+α+β) • f_α(u))`, `n = |u|`; `α = β = 0` is the declared case,
`m(σ̄ u) = J Ĝⁿ⁻¹ m(u)`.

*Hypothesis named:* the uniform tick. Every letter advances the same navigator `g` by one step, so
the tick of letter `k` is `k + α`, and `J` inverts that one navigator. Located advances (ticks
`τ(k)` that are not affine) and letter-selected screws (each letter `a` choosing its step's screw
`S_a`) do not inherit this: they need their own relation, `J S_a J = S_(σ a)⁻¹`, and are out of
scope here. -/
theorem face_complementReverse (g : G) (E : A → M) (σ : A → A) (J : M →+ M)
    (hJE : ∀ a, J (E a) = E (σ a)) (hJg : ∀ v, J (g • v) = g⁻¹ • J v)
    (α β : ℤ) (w : List A) :
    face g E β (complementReverse σ w)
      = J (g ^ ((w.length : ℤ) - 1 + α + β) • face g E α w) := by
  have hz : ∀ (m : ℤ) (v : M), g ^ m • J v = J (g ^ (-m) • v) := by
    intro m v
    rw [J_zpow g J hJg (-m) v, neg_neg]
  have hP0 := strandFace_complementReverse_nat g E σ J hJE hJg w
  have hF' : strandFace g⁻¹ E (complementReverse σ w)
      = g • J (g ^ w.length • strandFace g⁻¹ E w) := by
    rw [← hP0, smul_inv_smul]
  have hexp' : -(-β + 1) + (w.length : ℤ) = β - 1 + (w.length : ℤ) := by ring
  have hexp : (w.length : ℤ) - 1 + α + β + -α = β - 1 + (w.length : ℤ) := by ring
  have hL : face g E β (complementReverse σ w)
      = J (g ^ (β - 1 + (w.length : ℤ)) • strandFace g⁻¹ E w) := by
    calc face g E β (complementReverse σ w)
        = g ^ (-β) • (g • J (g ^ w.length • strandFace g⁻¹ E w)) := by
          unfold face
          rw [hF']
      _ = (g ^ (-β) * g) • J (g ^ w.length • strandFace g⁻¹ E w) := by rw [smul_smul]
      _ = g ^ (-β + 1) • J (g ^ w.length • strandFace g⁻¹ E w) := by rw [zpow_add_one]
      _ = J (g ^ (-(-β + 1)) • (g ^ w.length • strandFace g⁻¹ E w)) := hz _ _
      _ = J ((g ^ (-(-β + 1)) * g ^ w.length) • strandFace g⁻¹ E w) := by rw [smul_smul]
      _ = J (g ^ (-(-β + 1) + (w.length : ℤ)) • strandFace g⁻¹ E w) := by
          rw [zpow_add, zpow_natCast]
      _ = J (g ^ (β - 1 + (w.length : ℤ)) • strandFace g⁻¹ E w) := by rw [hexp']
  have hR : g ^ ((w.length : ℤ) - 1 + α + β) • face g E α w
      = g ^ (β - 1 + (w.length : ℤ)) • strandFace g⁻¹ E w := by
    unfold face
    rw [smul_smul, ← zpow_add, hexp]
  rw [hL, hR]

/-- [proved-derived; formal-checked] **The partner map is an involution.** If `J` is an involution
inverting the navigator, then `v ↦ J (g^z • v)` is an involution for every `z : ℤ`; with `z = n−1`
it is the map from a strand's face to its partner's, `(J Ĝⁿ⁻¹)² = 1`. -/
theorem partner_map_involutive (g : G) (J : M →+ M) (hJJ : ∀ v, J (J v) = v)
    (hJg : ∀ v, J (g • v) = g⁻¹ • J v) (z : ℤ) :
    Function.Involutive (fun v : M => J (g ^ z • v)) := by
  intro v
  show J (g ^ z • J (g ^ z • v)) = v
  rw [J_zpow g J hJg z, hJJ, smul_smul, ← zpow_add]
  simp

end Partner

/-! ## 7. The dihedral pairing: the group law and the frames -/

section Dihedral

/-- [proved-derived; formal-checked] **A reflection inverts every power of the screw.** In any group
with a half-turn `U` (`U² = 1`) inverting `S` (`U S U = S⁻¹`): `U Sʲ = S⁻ʲ U` for every `j : ℤ`. -/
theorem dihedral_swap {G : Type*} [Group G] {S U : G} (hU : U * U = 1) (hUSU : U * S * U = S⁻¹)
    (j : ℤ) : U * S ^ j = S ^ (-j) * U := by
  have h1 : U * S = S⁻¹ * U := by
    calc U * S = U * S * (U * U) := by rw [hU, mul_one]
      _ = U * S * U * U := (mul_assoc (U * S) U U).symm
      _ = S⁻¹ * U := by rw [hUSU]
  have h2 : SemiconjBy U S S⁻¹ := h1
  have h3 := h2.zpow_right j
  rw [inv_zpow'] at h3
  exact h3

/-- [proved-derived; formal-checked] **Every `Sʲ U` is a half-turn**: `(Sʲ U)² = 1` for all
`j : ℤ`, the reflections of the dihedral group `⟨S, U | U² = 1, USU = S⁻¹⟩`. -/
theorem dihedral_reflection_sq {G : Type*} [Group G] {S U : G} (hU : U * U = 1)
    (hUSU : U * S * U = S⁻¹) (j : ℤ) : (S ^ j * U) ^ 2 = 1 := by
  have h := dihedral_swap hU hUSU j
  calc (S ^ j * U) ^ 2 = (S ^ j * U) * (S ^ j * U) := pow_two _
    _ = S ^ j * ((U * S ^ j) * U) := by simp only [mul_assoc]
    _ = S ^ j * ((S ^ (-j) * U) * U) := by rw [h]
    _ = S ^ j * (S ^ (-j) * (U * U)) := by simp only [mul_assoc]
    _ = 1 := by rw [hU, mul_one, zpow_neg, mul_inv_cancel]

/-- [proved-derived; formal-checked] **Conjugating by a power of the screw doubles the offset of a
reflection**: `S⁻ᵏ U Sᵏ = S⁻²ᵏ U`. -/
theorem dihedral_conj {G : Type*} [Group G] {S U : G} (hU : U * U = 1) (hUSU : U * S * U = S⁻¹)
    (k : ℤ) : S ^ (-k) * U * S ^ k = S ^ (-2 * k) * U := by
  have h := dihedral_swap hU hUSU k
  have e : -k + -k = -2 * k := by ring
  calc S ^ (-k) * U * S ^ k = S ^ (-k) * (U * S ^ k) := mul_assoc _ _ _
    _ = S ^ (-k) * (S ^ (-k) * U) := by rw [h]
    _ = S ^ (-k) * S ^ (-k) * U := (mul_assoc _ _ _).symm
    _ = S ^ (-2 * k) * U := by rw [← zpow_add, e]

/-- [proved-derived; formal-checked] **On the index line the half-turn inverts the shift**: the
reflection `k ↦ c − k` conjugates the shift `k ↦ k + j` to the shift `k ↦ k − j`. -/
theorem halfTurn_inverts_shift {R : Type*} [AddCommGroup R] (c j k : R) :
    c - ((c - k) + j) = k - j := by
  abel

/-- [definition] The frames of period `p` on a duplex: a phase in `ZMod p` on each of two strands,
`ZMod p × Bool`. The shift `t^j` advances every phase by `j`. -/
def frameShift (p : ℕ) (j : ZMod p) (x : ZMod p × Bool) : ZMod p × Bool := (x.1 + j, x.2)

/-- [definition] The half-turn `u_c` about the dyad at `c`: it exchanges the strands with the phase
reversed, `(r, b) ↦ (c − r, ¬b)`. -/
def frameFlip (p : ℕ) (c : ZMod p) (x : ZMod p × Bool) : ZMod p × Bool := (c - x.1, !x.2)

/-- [proved-derived; formal-checked] The half-turn is an involution. -/
theorem frameFlip_frameFlip (p : ℕ) (c : ZMod p) (x : ZMod p × Bool) :
    frameFlip p c (frameFlip p c x) = x := by
  refine Prod.ext ?_ ?_
  · show c - (c - x.1) = x.1
    ring
  · show (!(!x.2)) = x.2
    exact Bool.not_not x.2

/-- [proved-derived; formal-checked] **The half-turn inverts the shift, pointwise**:
`u_c ∘ t^j ∘ u_c = t^(−j)`. -/
theorem frameFlip_frameShift_frameFlip (p : ℕ) (c j : ZMod p) (x : ZMod p × Bool) :
    frameFlip p c (frameShift p j (frameFlip p c x)) = frameShift p (-j) x := by
  refine Prod.ext ?_ ?_
  · show c - (c - x.1 + j) = x.1 + -j
    ring
  · show (!(!x.2)) = x.2
    exact Bool.not_not x.2

/-- [proved-derived; formal-checked] `t^(−j)` is the inverse of `t^j`. -/
theorem frameShift_neg_frameShift (p : ℕ) (j : ZMod p) (x : ZMod p × Bool) :
    frameShift p (-j) (frameShift p j x) = x ∧ frameShift p j (frameShift p (-j) x) = x := by
  constructor
  · refine Prod.ext ?_ rfl
    show x.1 + j + -j = x.1
    ring
  · refine Prod.ext ?_ rfl
    show x.1 + -j + j = x.1
    ring

/-- [proved-derived; formal-checked] The `j`-th power of the unit shift `t = t¹` is the shift by `j`. -/
theorem frameShift_iterate (p j : ℕ) (x : ZMod p × Bool) :
    (frameShift p 1)^[j] x = frameShift p (j : ZMod p) x := by
  induction j generalizing x with
  | zero =>
    refine Prod.ext ?_ rfl
    show x.1 = x.1 + ((0 : ℕ) : ZMod p)
    simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih]
    refine Prod.ext ?_ rfl
    show x.1 + 1 + (j : ZMod p) = x.1 + ((j + 1 : ℕ) : ZMod p)
    push_cast
    ring

/-- [definition] The `2p` maps `t^j` and `t^j ∘ u_c` applied to a base frame `x₀`, indexed by
`(j, ε) ∈ ZMod p × Bool`. -/
def dihedralFrame (p : ℕ) (c : ZMod p) (x₀ : ZMod p × Bool) :
    ZMod p × Bool → ZMod p × Bool
  | (j, false) => frameShift p j x₀
  | (j, true) => frameShift p j (frameFlip p c x₀)

/-- [proved-derived; formal-checked] **The dihedral group acts simply transitively on the `2p`
frames**: the maps `t^j` and `t^j ∘ u_c` send a base frame to every frame exactly once. -/
theorem dihedralFrame_bijective (p : ℕ) (c : ZMod p) (x₀ : ZMod p × Bool) :
    Function.Bijective (dihedralFrame p c x₀) := by
  obtain ⟨r₀, b₀⟩ := x₀
  constructor
  · rintro ⟨j, ε⟩ ⟨j', ε'⟩ h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    cases b₀ <;> cases ε <;> cases ε' <;>
      first
        | simp_all [dihedralFrame, frameShift, frameFlip]
        | aesop
  · rintro ⟨r, b⟩
    cases b₀ <;> cases b
    · refine ⟨(r - r₀, false), Prod.ext ?_ rfl⟩
      show r₀ + (r - r₀) = r
      ring
    · refine ⟨(r - (c - r₀), true), Prod.ext ?_ rfl⟩
      show c - r₀ + (r - (c - r₀)) = r
      ring
    · refine ⟨(r - (c - r₀), true), Prod.ext ?_ rfl⟩
      show c - r₀ + (r - (c - r₀)) = r
      ring
    · refine ⟨(r - r₀, false), Prod.ext ?_ rfl⟩
      show r₀ + (r - r₀) = r
      ring

end Dihedral

/-! ## 8. Four letters: the Klein group -/

section FourLetters

set_option maxRecDepth 8192

/-- [definition] The Klein group `V = (ℤ/2)²` acting on four letters by its regular representation:
`kleinAct v a` is the translation of `a` by `v`, the table of `V`. -/
def kleinAct : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]]

/-- [proved-derived; formal-checked] The table: translating `0` by `v` gives `v`. -/
theorem kleinAct_zero_right : ∀ v : Fin 4, kleinAct v 0 = v := by decide

/-- [proved-derived; formal-checked] Every element is its own inverse: `v · v = 0`. -/
theorem kleinAct_self : ∀ v : Fin 4, kleinAct v v = 0 := by decide

/-- [proved-derived; formal-checked] **`V` is closed under multiplication and acts as a group**:
translating by `w` and then by `v` is translating by the product `kleinAct v w`. -/
theorem kleinAct_assoc :
    ∀ v w a : Fin 4, kleinAct v (kleinAct w a) = kleinAct (kleinAct v w) a := by decide

/-- [proved-derived; formal-checked] **`V` is abelian.** -/
theorem kleinAct_comm :
    ∀ v w a : Fin 4, kleinAct v (kleinAct w a) = kleinAct w (kleinAct v a) := by decide

/-- [proved-derived; formal-checked] **`V` acts regularly (simply transitively)**: for every `a`,
`b` exactly one element `v` of the four sends `a` to `b`. -/
theorem kleinAct_regular : ∀ a b : Fin 4,
    ∃ v : Fin 4, kleinAct v a = b ∧ ∀ w : Fin 4, kleinAct w a = b → w = v := by decide

/-- [proved-derived; formal-checked] The three nonidentity elements of `V` are fixed-point-free
involutions. -/
theorem kleinAct_free_involution : ∀ v : Fin 4, v ≠ 0 →
    (∀ a, kleinAct v (kleinAct v a) = a) ∧ ∀ a, kleinAct v a ≠ a := by decide

/-- [proved-derived; formal-checked] Distinct elements of `V` act differently. -/
theorem kleinAct_injective : ∀ v w : Fin 4, (∀ a, kleinAct v a = kleinAct w a) → v = w := by
  decide

/-- [proved-derived; formal-checked] Outside `{0, v}` the fourth letter is the translate: the
combinatorial core of the classification. -/
theorem kleinAct_fourth : ∀ v x y : Fin 4, v ≠ 0 → x ≠ 0 → x ≠ v → y ≠ 0 → y ≠ v → y ≠ x →
    y = kleinAct v x := by decide

/-- [proved-derived; formal-checked] A fixed-point-free involution of four letters is the
translation by its image of `0`. -/
theorem free_involution_eq_kleinAct (σ : Fin 4 → Fin 4) (hinv : ∀ a, σ (σ a) = a)
    (hfree : ∀ a, σ a ≠ a) : ∀ x, σ x = kleinAct (σ 0) x := by
  intro x
  have h0 : σ 0 ≠ 0 := hfree 0
  by_cases hx0 : x = 0
  · subst hx0
    exact (kleinAct_zero_right (σ 0)).symm
  · by_cases hxv : x = σ 0
    · subst hxv
      rw [hinv 0, kleinAct_self]
    · have hne0 : σ x ≠ 0 := by
        intro h
        apply hxv
        have h' := hinv x
        rw [h] at h'
        exact h'.symm
      have hnev : σ x ≠ σ 0 := by
        intro h
        apply hx0
        have h' := hinv x
        rw [h, hinv 0] at h'
        exact h'.symm
      exact kleinAct_fourth (σ 0) x (σ x) h0 hx0 hxv hne0 hnev (hfree x)

/-- [proved-derived; formal-checked] **On four letters the fixed-point-free involutions are exactly
the three nonidentity translations of `V`.** -/
theorem free_involution_iff (σ : Fin 4 → Fin 4) :
    ((∀ a, σ (σ a) = a) ∧ ∀ a, σ a ≠ a) ↔ ∃ v : Fin 4, v ≠ 0 ∧ ∀ a, σ a = kleinAct v a := by
  constructor
  · rintro ⟨hinv, hfree⟩
    exact ⟨σ 0, hfree 0, free_involution_eq_kleinAct σ hinv hfree⟩
  · rintro ⟨v, hv, hσ⟩
    obtain ⟨h1, h2⟩ := kleinAct_free_involution v hv
    constructor
    · intro a
      rw [hσ a, hσ (kleinAct v a)]
      exact h1 a
    · intro a
      rw [hσ a]
      exact h2 a

/-- [proved-derived; formal-checked] **There are exactly three.** -/
theorem card_free_involutions_fin4 :
    Nat.card {σ : Fin 4 → Fin 4 // (∀ a, σ (σ a) = a) ∧ ∀ a, σ a ≠ a} = 3 := by
  have hbij : Function.Bijective (fun v : {v : Fin 4 // v ≠ 0} =>
      (⟨kleinAct v.1, kleinAct_free_involution v.1 v.2⟩ :
        {σ : Fin 4 → Fin 4 // (∀ a, σ (σ a) = a) ∧ ∀ a, σ a ≠ a})) := by
    constructor
    · rintro ⟨v, hv⟩ ⟨w, hw⟩ h
      have h' : ∀ a, kleinAct v a = kleinAct w a := fun a => congrFun (congrArg Subtype.val h) a
      exact Subtype.ext (kleinAct_injective v w h')
    · rintro ⟨σ, hσ⟩
      obtain ⟨v, hv, hσv⟩ := (free_involution_iff σ).mp hσ
      exact ⟨⟨v, hv⟩, Subtype.ext (funext fun a => (hσv a).symm)⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card]
  first
    | decide
    | rfl
    | simp

/-- [proved-derived; formal-checked] **The pairing preserves the type of a substitution**: a
fixed-point-free involution of four letters commutes with every element of `V`,
`σ (v · a) = v · σ a`; a slipped contact is repaired by the same type on either strand. -/
theorem free_involution_commutes (σ : Fin 4 → Fin 4) (hinv : ∀ a, σ (σ a) = a)
    (hfree : ∀ a, σ a ≠ a) (v a : Fin 4) : σ (kleinAct v a) = kleinAct v (σ a) := by
  have h := free_involution_eq_kleinAct σ hinv hfree
  rw [h (kleinAct v a), h a]
  exact kleinAct_comm _ _ _

end FourLetters

/-! ## 9. The inner code: a substitution makes exactly its contact slip -/

section InnerCode

variable {α : Type*}

/-- [proved-derived; formal-checked] **Position `n−1−k` of the partner is `σ` of position `k`**:
the contact of the pairing, in the list reading. -/
theorem getElem?_complementReverse_rev (σ : α → α) (x : List α) {k : ℕ} (hk : k < x.length) :
    (complementReverse σ x)[x.length - 1 - k]? = (x[k]?).map σ := by
  have h1 : x.length - 1 - k < (x.map σ).length := by
    rw [List.length_map]
    omega
  have h2 : (x.map σ).length - 1 - (x.length - 1 - k) = k := by
    rw [List.length_map]
    omega
  show ((x.map σ).reverse)[x.length - 1 - k]? = (x[k]?).map σ
  rw [List.getElem?_reverse h1, h2, List.getElem?_map]

/-- [proved-derived; formal-checked] **A contact slips exactly where the strand was substituted.**
With the partner `y = σ̄(x)` intact and a damaged strand `x'`, the contact of position `k` of `x'`
with position `n−1−k` of `y` fails to lock exactly when `x'` differs from `x` at `k`. Only
injectivity of `σ` is used. -/
theorem slipped_contact_iff {σ : α → α} (hσ : Function.Injective σ) (x x' : List α) {k : ℕ}
    (hk : k < x.length) :
    (complementReverse σ x)[x.length - 1 - k]? ≠ (x'[k]?).map σ ↔ x'[k]? ≠ x[k]? := by
  rw [getElem?_complementReverse_rev σ x hk]
  constructor
  · intro h h'
    exact h (by rw [h'])
  · intro h h'
    exact h (Option.map_injective hσ h').symm

/-- [proved-derived; formal-checked] **The slipped contacts are exactly the substituted
positions.** -/
theorem slipped_contacts_eq {σ : α → α} (hσ : Function.Injective σ) (x x' : List α) :
    {k : ℕ | k < x.length ∧ (complementReverse σ x)[x.length - 1 - k]? ≠ (x'[k]?).map σ}
      = {k : ℕ | k < x.length ∧ x'[k]? ≠ x[k]?} := by
  ext k
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hk, h⟩
    exact ⟨hk, (slipped_contact_iff hσ x x' hk).mp h⟩
  · rintro ⟨hk, h⟩
    exact ⟨hk, (slipped_contact_iff hσ x x' hk).mpr h⟩

/-- [proved-derived; formal-checked] **At a slipped contact the two repairs differ**: either strand
may be the damaged one, and the candidates `x k` (restore the strand) and `x' k` (keep it and
repair the partner) are distinct. -/
theorem slipped_repairs_distinct {σ : α → α} (hσ : Function.Injective σ) (x x' : List α) {k : ℕ}
    (hk : k < x.length)
    (hslip : (complementReverse σ x)[x.length - 1 - k]? ≠ (x'[k]?).map σ) :
    x[k]? ≠ x'[k]? :=
  fun h => (slipped_contact_iff hσ x x' hk).mp hslip h.symm

end InnerCode

/-! ## 10. A duplex passage -/

section Duplex

/-- [definition] The four strand crossings of a duplex passage on a ribbon: signs `s, e·s, e·s, s`,
the middle two between different strands (`e = ±1` records whether the strands run parallel or
antiparallel to the core). -/
def duplexSigns (e s : ℤ) : Fin 4 → ℤ := ![s, e * s, e * s, s]

/-- [proved-derived; formal-checked] **A duplex passage moves the inter-strand sum by `−4es`.** A
crossing change negates all four crossings; the two between different strands carry the same sign,
so their sum moves by `−4·e·s`. The geometry (the sign pattern of a ribbon, owed with `Lk = Tw + Wr`)
is the declared input `duplexSigns`; this is the arithmetic of it. -/
theorem duplex_passage_sum (e s : ℤ) :
    (∑ k ∈ ({1, 2} : Finset (Fin 4)), -(duplexSigns e s k))
      - ∑ k ∈ ({1, 2} : Finset (Fin 4)), duplexSigns e s k = -4 * (e * s) := by
  have h1 : duplexSigns e s 1 = e * s := rfl
  have h2 : duplexSigns e s 2 = e * s := rfl
  have hne : (1 : Fin 4) ≠ 2 := by decide
  rw [Finset.sum_pair hne, Finset.sum_pair hne]
  first
    | (rw [h1, h2]; ring)
    | (simp only [h1, h2]; ring)

/-- [proved-derived; formal-checked] **The linking number, half the inter-strand sum, moves by
`−2es`**: `∓2` for a passage of a doubled strand, against `∓1` for one crossing change. -/
theorem duplex_passage_linking (e s : ℤ) :
    ((∑ k ∈ ({1, 2} : Finset (Fin 4)), -(duplexSigns e s k) : ℤ) : ℚ) / 2
      - ((∑ k ∈ ({1, 2} : Finset (Fin 4)), duplexSigns e s k : ℤ) : ℚ) / 2
      = -2 * ((e : ℚ) * s) := by
  have h := duplex_passage_sum e s
  have h' : ((∑ k ∈ ({1, 2} : Finset (Fin 4)), -(duplexSigns e s k) : ℤ) : ℚ)
      - ((∑ k ∈ ({1, 2} : Finset (Fin 4)), duplexSigns e s k : ℤ) : ℚ)
      = -4 * ((e : ℚ) * s) := by
    exact_mod_cast h
  linarith

/-- [proved-derived; formal-checked] For `e, s = ±1` the inter-strand sum moves by `±4`, so the
linking number, half of it, moves by `±2`. -/
theorem duplex_passage_pm_four (e s : ℤ) (he : e = 1 ∨ e = -1) (hs : s = 1 ∨ s = -1) :
    -4 * (e * s) = 4 ∨ -4 * (e * s) = -4 := by
  rcases he with rfl | rfl <;> rcases hs with rfl | rfl <;> norm_num

end Duplex

end Holonics.Transport.HelicalCode

#print axioms Holonics.Transport.HelicalCode.complementReverse
#print axioms Holonics.Transport.HelicalCode.complementReverse_nil
#print axioms Holonics.Transport.HelicalCode.complementReverse_cons
#print axioms Holonics.Transport.HelicalCode.complementReverse_append
#print axioms Holonics.Transport.HelicalCode.length_complementReverse
#print axioms Holonics.Transport.HelicalCode.complementReverse_involutive
#print axioms Holonics.Transport.HelicalCode.complementReverse_ne_of_middle
#print axioms Holonics.Transport.HelicalCode.even_length_of_fixed
#print axioms Holonics.Transport.HelicalCode.eq_complementReverse_of_fixed
#print axioms Holonics.Transport.HelicalCode.fixed_eq_take_append
#print axioms Holonics.Transport.HelicalCode.complementReverse_append_self
#print axioms Holonics.Transport.HelicalCode.length_append_complementReverse
#print axioms Holonics.Transport.HelicalCode.firstHalfEquiv
#print axioms Holonics.Transport.HelicalCode.card_fixedWords
#print axioms Holonics.Transport.HelicalCode.phaseTransport_eq_reflectedReturn
#print axioms Holonics.Transport.HelicalCode.phaseTransport_mul_self
#print axioms Holonics.Transport.HelicalCode.phaseTransport_ne_self
#print axioms Holonics.Transport.HelicalCode.involutive_of_mul_self
#print axioms Holonics.Transport.HelicalCode.phaseTransport_pairing
#print axioms Holonics.Transport.HelicalCode.phaseTransport_reciprocal
#print axioms Holonics.Transport.HelicalCode.complementReverse_involutive_at_phase
#print axioms Holonics.Transport.HelicalCode.even_length_of_fixed_at_phase
#print axioms Holonics.Transport.HelicalCode.card_fixedWords_at_phase
#print axioms Holonics.Transport.HelicalCode.crossingChange
#print axioms Holonics.Transport.HelicalCode.crossingChange_self
#print axioms Holonics.Transport.HelicalCode.crossingChange_of_ne
#print axioms Holonics.Transport.HelicalCode.sum_crossingChange_sub
#print axioms Holonics.Transport.HelicalCode.sum_crossingChange_eq_pm_two
#print axioms Holonics.Transport.HelicalCode.half_sum_crossingChange
#print axioms Holonics.Transport.HelicalCode.geom_smul_sum_succ'
#print axioms Holonics.Transport.HelicalCode.geom_smul_sum_sub
#print axioms Holonics.Transport.HelicalCode.one_sub_smul_geom_sum
#print axioms Holonics.Transport.HelicalCode.strandFace
#print axioms Holonics.Transport.HelicalCode.strandFace_singleton
#print axioms Holonics.Transport.HelicalCode.strandFace_append
#print axioms Holonics.Transport.HelicalCode.repeatWord
#print axioms Holonics.Transport.HelicalCode.strandFace_repeatWord
#print axioms Holonics.Transport.HelicalCode.strandFace_repeatWord_sub
#print axioms Holonics.Transport.HelicalCode.strandFace_repeatWord_one_sub
#print axioms Holonics.Transport.HelicalCode.strandFace_repeatWord_of_fixed
#print axioms Holonics.Transport.HelicalCode.strandFace_ofFn
#print axioms Holonics.Transport.HelicalCode.face
#print axioms Holonics.Transport.HelicalCode.face_ofFn
#print axioms Holonics.Transport.HelicalCode.J_zpow
#print axioms Holonics.Transport.HelicalCode.J_pow
#print axioms Holonics.Transport.HelicalCode.strandFace_complementReverse_nat
#print axioms Holonics.Transport.HelicalCode.face_complementReverse
#print axioms Holonics.Transport.HelicalCode.partner_map_involutive
#print axioms Holonics.Transport.HelicalCode.dihedral_swap
#print axioms Holonics.Transport.HelicalCode.dihedral_reflection_sq
#print axioms Holonics.Transport.HelicalCode.dihedral_conj
#print axioms Holonics.Transport.HelicalCode.halfTurn_inverts_shift
#print axioms Holonics.Transport.HelicalCode.frameShift
#print axioms Holonics.Transport.HelicalCode.frameFlip
#print axioms Holonics.Transport.HelicalCode.frameFlip_frameFlip
#print axioms Holonics.Transport.HelicalCode.frameFlip_frameShift_frameFlip
#print axioms Holonics.Transport.HelicalCode.frameShift_neg_frameShift
#print axioms Holonics.Transport.HelicalCode.frameShift_iterate
#print axioms Holonics.Transport.HelicalCode.dihedralFrame
#print axioms Holonics.Transport.HelicalCode.dihedralFrame_bijective
#print axioms Holonics.Transport.HelicalCode.kleinAct
#print axioms Holonics.Transport.HelicalCode.kleinAct_zero_right
#print axioms Holonics.Transport.HelicalCode.kleinAct_self
#print axioms Holonics.Transport.HelicalCode.kleinAct_assoc
#print axioms Holonics.Transport.HelicalCode.kleinAct_comm
#print axioms Holonics.Transport.HelicalCode.kleinAct_regular
#print axioms Holonics.Transport.HelicalCode.kleinAct_free_involution
#print axioms Holonics.Transport.HelicalCode.kleinAct_injective
#print axioms Holonics.Transport.HelicalCode.kleinAct_fourth
#print axioms Holonics.Transport.HelicalCode.free_involution_eq_kleinAct
#print axioms Holonics.Transport.HelicalCode.free_involution_iff
#print axioms Holonics.Transport.HelicalCode.card_free_involutions_fin4
#print axioms Holonics.Transport.HelicalCode.free_involution_commutes
#print axioms Holonics.Transport.HelicalCode.getElem?_complementReverse_rev
#print axioms Holonics.Transport.HelicalCode.slipped_contact_iff
#print axioms Holonics.Transport.HelicalCode.slipped_contacts_eq
#print axioms Holonics.Transport.HelicalCode.slipped_repairs_distinct
#print axioms Holonics.Transport.HelicalCode.duplexSigns
#print axioms Holonics.Transport.HelicalCode.duplex_passage_sum
#print axioms Holonics.Transport.HelicalCode.duplex_passage_linking
#print axioms Holonics.Transport.HelicalCode.duplex_passage_pm_four
