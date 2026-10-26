import HolonicsResearch.Geometry.ScrewTorsion
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# Commuting selected moves see only symbol counts

The record `research/records/2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ.md`
(§2) reads what a field of moves selected by the symbol can see through the image of the words
under its linear part: one linear part sees lag-residue counts (`laggedRun_eq_of_counts`),
reflections in one plane see parity and a signed phase sum (`plane_turns_commute`), and commuting
linear parts see the symbol counts. #410 owes the commuting row; this file proves it for the
selected stream `selectedRun` of `Geometry/ScrewTorsion` with moves that do not change over the
passage.

[proved-standard; formal-checked] What is proved.

1. **Each entry is transported by what followed it** (`selectedRun_eq_transport`): in any ring,
   `z_t = Σ_(k<t) λ(u_(t−1)) ⋯ λ(u_(k+1)) β(u_k)`, the entry at cell `k` carried by the linear parts
   of the symbols read after it (`after`, latest first).
2. **Commuting transports see only counts** (`transport_eq_of_counts`): when the linear parts
   commute pairwise, two passages whose symbols after their entries have the same counts transport
   their entries alike, whatever their order (`List.Perm.prod_eq'`).
3. **The transport is a product of powers** (`transport_eq_prod_counts`, `selectedRun_commuting`):
   in a commutative ring, `z_t = Σ_(k<t) (∏_a λ_a^(n_a)) β(u_k)`, with `n_a` the count of `a` after
   `k`, the fibre count of `Finset.prod_comp`.

So a field whose linear parts commute is a function of the entries and of the symbol counts that
followed each, never of their order; order needs linear parts that do not commute, the minimal
realization `E T_a = U_a E` of the record's table.

The computational object is the helical pair interaction: each move is a turn of a ring selected by
the symbol at its pair contact, and the state is the strand those turns carry. Of the winding
guide's six general objects this touches the helix (the carried state) and the tower thread (the
word acting on it); the pair, faces and placement, the cell holonomy and the tube stay attached.

Consumers: the atlas row `motion.commuting-symbol-counts` and the record's §2 table.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Geometry.CommutingCounts

open Finset
open Holonics.Geometry.Motion (selectedRun)

variable {S α : Type*}

/-- [definition] The symbols read after cell `k` and before cell `t`, latest first. -/
def after (u : ℕ → α) (k : ℕ) : ℕ → List α
  | 0 => []
  | t + 1 => if k < t then u t :: after u k t else []

/-- [definition] The transport of the entry at cell `k` to cell `t`:
`λ(u_(t−1)) ⋯ λ(u_(k+1))`. -/
def transport [Monoid S] (lam : α → S) (u : ℕ → α) (k t : ℕ) : S :=
  ((after u k t).map lam).prod

section Ring

variable [Ring S]

/-- [proved-standard; formal-checked] **Each entry is transported by what followed it:**
`z_t = Σ_(k<t) λ(u_(t−1)) ⋯ λ(u_(k+1)) β(u_k)`. -/
theorem selectedRun_eq_transport (lam beta : α → S) (u : ℕ → α) (t : ℕ) :
    selectedRun (fun _ => lam) (fun _ => beta) u t =
      ∑ k ∈ range t, transport lam u k t * beta (u k) := by
  induction t with
  | zero => simp [selectedRun]
  | succ t ih =>
    have h1 : ∀ k ∈ range t, transport lam u k (t + 1) * beta (u k) =
        lam (u t) * (transport lam u k t * beta (u k)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      simp [transport, after, hk, mul_assoc]
    have h2 : transport lam u t (t + 1) = 1 := by simp [transport, after]
    rw [Finset.sum_range_succ, Finset.sum_congr rfl h1, ← Finset.mul_sum, ← ih, h2, one_mul]
    simp only [selectedRun]

/-- [proved-standard; formal-checked] Pairwise commuting linear parts commute pairwise along any
word. -/
theorem pairwise_commute_map (lam : α → S) (hc : ∀ a b, Commute (lam a) (lam b)) :
    ∀ l : List α, (l.map lam).Pairwise Commute
  | [] => List.Pairwise.nil
  | a :: l => by
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨fun x hx => ?_, pairwise_commute_map lam hc l⟩
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
    exact hc a b

/-- [proved-standard; formal-checked] **Commuting transports see only counts:** when the linear
parts commute pairwise, two passages whose symbols after their entries have the same counts
transport their entries alike. -/
theorem transport_eq_of_counts [DecidableEq α] (lam : α → S)
    (hc : ∀ a b, Commute (lam a) (lam b)) (u u' : ℕ → α) (k t k' t' : ℕ)
    (h : ∀ a, (after u k t).count a = (after u' k' t').count a) :
    transport lam u k t = transport lam u' k' t' := by
  unfold transport
  exact ((List.perm_iff_count.mpr h).map lam).prod_eq' (pairwise_commute_map lam hc _)

end Ring

section CommRing

variable [CommRing S] [Fintype α] [DecidableEq α]

/-- [proved-standard; formal-checked] **The transport is a product of powers:**
`λ(u_(t−1)) ⋯ λ(u_(k+1)) = ∏_a λ_a^(n_a)`, with `n_a` the count of `a` after `k`. -/
theorem transport_eq_prod_counts (lam : α → S) (u : ℕ → α) (k t : ℕ) :
    transport lam u k t = ∏ a, lam a ^ (after u k t).count a := by
  unfold transport
  rw [Finset.prod_list_map_count]
  refine Finset.prod_subset (Finset.subset_univ _) fun a _ ha => ?_
  rw [List.count_eq_zero.mpr (by simpa using ha), pow_zero]

/-- [proved-standard; formal-checked] **Commuting selected moves see only symbol counts:**
`z_t = Σ_(k<t) (∏_a λ_a^(n_a)) β(u_k)`. -/
theorem selectedRun_commuting (lam beta : α → S) (u : ℕ → α) (t : ℕ) :
    selectedRun (fun _ => lam) (fun _ => beta) u t =
      ∑ k ∈ range t, (∏ a, lam a ^ (after u k t).count a) * beta (u k) := by
  rw [selectedRun_eq_transport]
  exact Finset.sum_congr rfl fun k _ => by rw [transport_eq_prod_counts]

end CommRing

end Holonics.Geometry.CommutingCounts
