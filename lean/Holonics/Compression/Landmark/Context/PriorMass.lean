import Holonics.Compression.Landmark.Context.Tree
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Choose.Central

/-!
# Compression.Landmark.Context.PriorMass: the node's prior mass and its code length

[definition; agent-inferred] The receiving tree's prior mass (the contact-loop record of October 2,
§25; rebuild step 4, #73). Every node of the landmark tree codes a digit of the cell's odometer word
with a binary face read from its counts. KT starts each digit value at weight `1/2`; the prior mass
starts it at `2^(−j)`, so a context seen a few times, always followed by the same cell, is trusted
sooner. The computational object is the helical pair interaction; this owner is the receiving
parametron's landmark register, whose face it reads. Of the winding guide's six general objects it
touches **faces and placement** (the node's face is a normalized receiving face on each dyadic
digit, and its code length is what the receiver pays at that face); the helix, the pair, the cell
holonomy, the tube and the tower thread stay attached, unchanged.

```text
face       k_s(b) = (2^j n_s(b) + 1)/(2^j n_s + 2) = (n_s(b) + α)/(n_s + 2α),  α = 2^(−j);  KT at j = 1
node law   U_α(k, m) = (α)_k (α)_m/(2α)_(k+m)   k, m the arrivals of the two digit values
vs KT      2α · KT(k, m) ≤ U_α(k, m)                 at most j − 1 bits over KT, every count
regret     (k/n)^k (m/n)^m ≤ 2^j √n · U_α(k, m)      at most ½ log₂ n + j bits; KT: ½ log₂ n + 1
one-sided  KT(n, 0) ≤ U_α(n, 0),  U_α(n + 1, 0) ≥ 1/(2(1 + αn))   at most 2 bits while n ≤ 2^j
choice     j ∈ {1, …, 8} charged log₂ 8 = 3 bits: Σ_w 2^(−(3 + code_ĵ(w))) ≤ 1 for any choice ĵ
tree       −log₂ ∏_t q_0(x_t) ≤ −log₂ prior_w(S) + Σ_(leaves s) [−log₂ (k_s/n_s)^(k_s) (m_s/n_s)^(m_s) + ½ log₂ n_s + j]
           every pruned tree S, any stop weights in [0, 1); one binary tree's ĵ charged 3 bits
depth      D → k + D: the bound against S of depth ≤ D gains deepLeaves(S) · (−log₂ w_D), nothing else;
           on the ladder −log₂(1 − 2^(−j_D)) = j_D − log₂(2^(j_D) − 1) ≤ 1 bit a deep leaf
```

[proved-derived; formal-checked] What is proved.

1. **The face** (`priorMass_face`): the face the host and the card read, halves starting at one and
   each arrival adding `2^j`, is the Dirichlet predictive (Pólya urn) at weight `2^(−j)`
   (`Tree.dirichletPredictive`), whose sequential likelihood on a binary word is `U_α(k, m)`
   (`urnSeq_eq_urnBool`, through `Tree.urnSeq_bool`). It is a node law (`massLaw`,
   `massLaw_read`), so every theorem of the tree weighting stated for a `Tree.NodeLaw` holds for it,
   and its likelihoods over the `2^n` binary words of length `n` sum to one (`urnSeq_sum`).
2. **At most `j − 1` bits over KT** (`priorMass_ge_kt`, `priorMass_code_le_kt`): for `0 < α ≤ 1/2`
   and every pair of counts, `2α · KT(k, m) ≤ U_α(k, m)`. When the arriving value is the majority one
   the weight-`α` face is at least KT's (`kt_face_le`), so off the diagonal the ratio `U_α/KT` only
   rises (`kt_right`); along the diagonal it falls, but stays above `2α(2s+2)/(2s+1+2α)`
   (`kt_diag`).
3. **The regret against the best fixed digit probability** (`kt_regret`, `priorMass_regret`,
   `priorMass_regret_bits`, `priorMass_regret_fixed`): for `n = k + m ≥ 1` the best fixed
   probability's likelihood `(k/n)^k (m/n)^m` (`bestFixed`, the maximum of `θ^k (1−θ)^m` over
   `θ ∈ [0, 1]`, `fixed_le_bestFixed`) is at most `2√n · KT(k, m)`, so KT's regret is at most
   `½ log₂ n + 1` bits; at rung `j` it is at most `½ log₂ n + j`. KT's bound closes the
   redundancy `Tree`'s header left owed in #62. It reads `KT(k, m) = (1/2)_k (1/2)_m/n!` with
   `(1/2)_k = k! C(2k, k)/4^k` (`ascPochhammer_eval_half`), the central binomial bound
   `16^k ≤ 4k C(2k, k)²` (`sixteen_pow_le_centralBinom_sq`), Mathlib's Stirling lower bound for
   `k!` and `m!`, the first term of the decreasing Stirling sequence for `n!`
   (`factorial_le_stirling_upper`), and `e ≤ π`.
4. **The one-sided context gains** (`priorMass_one_sided_ge_kt`, `priorMass_one_sided`,
   `priorMass_one_sided_two_bits`): a node that has seen only one digit value is never coded worse
   than by KT, and at rung `j` its first `2^j + 1` arrivals cost at most 2 bits together, where KT's
   cost grows as `½ log₂ n`. This is where the prior mass gains: the recurring contexts §24 located.
5. **The floor** (`priorMass_face_ge`, `priorMass_digit_face_ge`): a node with at most `n*` arrivals
   reads each digit value at least at `1/(2^j n* + 2)`, and so does the opened path's face at every
   depth under any stop weights in `[0, 1]`: the floor the lattice width `M_p` reads, KT's
   `Tree.digit_face_ge` at `j = 1`.
6. **The choice is a two-part code** (`two_part_kraft`, `priorMass_two_part`): charging `log₂ B` bits
   for a choice among `B` sub-probability laws satisfies Kraft for **any** choice, made on the
   development cells or even on the coded word itself; at the ladder `j = 1..8`, `3 + code_ĵ` is a
   valid code length.
7. **The tree's full redundancy** (`emitted_eq_weight`, `own_dominance₀`,
   `priorMass_tree_redundancy`, `priorMass_tree_redundancy_source`, `emitted_sum`, `tree_two_part`,
   `priorMass_tree_two_part`): over any observation list whose addresses reach depth `D`, the code
   the tree emits (its root faces multiplied over the passage) is its root weight over the urn own
   weights. For **every** pruned tree `S` with positive prior under **any** stop weights in `[0, 1)`
   (the declared stop prior, forced depths at `0`), it is at most `S`'s prior code plus, at each
   leaf, the best fixed digit probability's code of what reached the leaf and `½ log₂ n_s + j`
   (nothing at a leaf no arrival reached); so it is within those charges of every binary tree
   source `(S, θ)`. Under a causal context the emitted code sums to one over the words of each
   length, so choosing the rung, or the rung and the stop prior together, on the coded word itself
   costs `log₂` of the family: 3 bits at `j = 1..8`, `3 + log₂ F` with a stop prior among `F`.
8. **Raising the maximum depth** (`PrunedTree.lift`, `PrunedTree.prior_lift`, `ownLik_lift`,
   `leafSum_lift`, `priorMass_depth_lift`, `ladder_stop_bits`, `priorMass_depth_lift_ladder`): a
   pruned tree of depth at most `D` is one of depth at most `k + D` whose leaves at depth `D` are
   stops. Its prior gains exactly the stop weight `w_D` per such leaf, its leaves' own weights and
   routed counts are unchanged, so against every such `S` item 7's bound at `k + D` is the bound at
   `D` plus `deepLeaves(S) · (−log₂ w_D)` and nothing else; the deeper tree is compared with the
   deeper pruned trees as well. On the declared ladder `w_D = 1 − 2^(−j_D)` the stop costs
   `j_D − log₂(2^(j_D) − 1)` bits, at most one (`log₂(8/7)` at `j_D = 3`).

[agent-inferred] **The trade.** Items 2 and 3 are worst-case bounds and the worst case is the
balanced count: there the prior mass pays up to `j − 1` bits a node over KT (`2` at campaign 1's
`j = 3`). Item 4 is the gain on skewed counts. Which wins on a passage is a measurement, not a
theorem: §25's ladder and exposure read it on campaign 1.

[proved-standard] The KT redundancy `½ log₂ n + 1` is Krichevsky and Trofimov (1981); the bound
against the best fixed probability is standard. The proofs here are this owner's.

[conditional] **What item 7 covers in the Rust.** It bounds one digit tree's exact code, the
ideal tree's (`IdealLandmarks`): each digit tree's arrivals are an observation list whose
addresses reach `D` (padded with the boundary letter), and a cell's code is the sum of its digits'
codes, so the bound holds per digit tree and adds. It needs, and the HNN declares, the unbounded
register (`Capacity::Unbounded`, `hnn::receiving::landmark_declaration_with`) and `j ≥ 1` (the
declaration refuses `j = 0`): a register's ceiling is another node law, not the urn. Not stated
here: the executed lattice code adds the lattice's per-cell drift (#62, "the landmark lattice's
drift"; checked by the Rust tests through `Landmarks::face_rule`); the enlarged tree's join of the
cell and bundle branches adds at most one bit a dyadic cell against either branch (the join is
per digit tree, at `½`; `Tree.sequential_mixture_bounds`), uncomposed; and the concave form
`|S| γ(N/|S|)` of the leaves' charges. A rung declared on the development cells before the coded cells needs no charge on them;
the 3 bits cover a choice made on the coded word itself. `emitted_sum`, `tree_two_part` and
`priorMass_tree_two_part` are stated for one binary tree whose context is read from its own past
digits; over a larger alphabet a digit tree's context is the cell history, and the cell code's
completeness over its digit trees (each cell's digit faces summing to one,
`Tree.digit_emission_normalized`) is not composed with them here.

[agent-inferred] **The depth is a storage limit.** By item 8 a larger maximum depth never weakens
the guarantee against a tree source of the old depth by more than one stop code a leaf at the old
maximum depth, and it extends the guarantee to the deeper sources: depth bounds what the standing
can hold, it does not trade one statistical risk for another. Item 8 compares bounds against a fixed
`S`; it does not say the code at `k + D` is below the code at `D`, which is a measurement (the
contact-loop record's §28). The Rust's depth is `LandmarkDeclaration::depth` in bundles: the cell
branch's letter depth is that depth, the bundle branch's `(1 + r)` times it, so one more bundle is
`k = 1` in the cell branch and `k = 1 + r` in the bundle branch; the stop weight read at `D` is
`StopPrior::weight(D)`, the last rung past the list, and the HNN declares no forced depths.

| Claim | Lean | Rust |
|---|---|---|
| the face at prior mass `2^(−j)` | `priorMass_face`, `massLaw`, `massLaw_read`, `urnSeq_eq_urnBool` | host `compression::landmark::context::LandmarkDeclaration::mass`, its deposit (`Law`'s unit `2^j`, `Arena::count`); card `holonics_cuda::hnn::tree::CardTree` (`TreeLaw.unit`, kernel `hnn_tree_deposit`) |
| at most `j − 1` bits over KT | `priorMass_ge_kt`, `priorMass_code_le_kt` | (the bound; measured in §25's ladder) |
| regret `½ log₂ n + j`; KT's `½ log₂ n + 1` | `kt_regret`, `priorMass_regret`, `priorMass_regret_bits` | — |
| the one-sided gain | `priorMass_one_sided_ge_kt`, `priorMass_one_sided_two_bits` | — |
| the ladder charged 3 bits is a valid code | `two_part_kraft`, `priorMass_two_part` | `hnn::field::ReceiverDeclaration::mass` (campaign 1 declares `j = 3`, coded in `Field::describe`) |
| the tree's full redundancy, any stop weights; one binary tree's rung charged 3 bits | `emitted_eq_weight`, `own_dominance₀`, `priorMass_tree_redundancy`, `priorMass_tree_redundancy_source`, `emitted_sum`, `tree_two_part`, `priorMass_tree_two_part` | `compression::landmark::context::IdealLandmarks` (one digit tree's exact code), `StopPrior`, `hnn::field::ReceiverDeclaration::mass` |
| raising the maximum depth costs one stop code a leaf at the old maximum depth | `PrunedTree.prior_lift`, `ownLik_lift`, `leafSum_lift`, `priorMass_depth_lift`, `ladder_stop_bits`, `priorMass_depth_lift_ladder` | `compression::landmark::context::LandmarkDeclaration::depth`, `StopPrior::weight`, `hnn::field::ReceiverDeclaration` (`depth`) |
| the floor `1/(2^j n* + 2)` | `priorMass_face_ge` (the node), `priorMass_digit_face_ge` (the opened path, any stop weights) | `compression::landmark::context::face_bits` |
-/

namespace Holonics.Compression.Landmark.Context.PriorMass

open Holonics.Compression.Landmark.Context.Tree
open Polynomial Finset

/-! ### The face and the two-class urn -/

/-- [definition] **The prior mass `2^-j`** of the receiving tree's node at ladder rung `j`: the
weight with which each digit value starts, against one per arrival. -/
def massWeight (j : ℕ) : ℚ := 1 / 2 ^ j

theorem massWeight_pos (j : ℕ) : 0 < massWeight j := by
  unfold massWeight; positivity

theorem massWeight_le_half {j : ℕ} (hj : 1 ≤ j) : massWeight j ≤ 1 / 2 := by
  unfold massWeight
  have : (2 : ℚ) ≤ 2 ^ j := by
    calc (2 : ℚ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  exact one_div_le_one_div_of_le (by norm_num) this

/-- [proved-derived; formal-checked] **`priorMass_face`: the node's face is the Dirichlet
predictive at weight `2^-j`.** With `n_b` arrivals of digit `b` among `n`, the face the host and
card trees read, halves starting at one and each arrival adding `2^j`, is
`(2^j n_b + 1)/(2^j n + 2)`, which is the Pólya urn's prediction at initial weight `2^-j` per
digit value. At `j = 1` it is KT's `(n_b + 1/2)/(n + 1)`. -/
theorem priorMass_face (j : ℕ) (n : Bool → ℕ) (b : Bool) :
    dirichletPredictive (massWeight j) n b =
      (2 ^ j * (n b : ℚ) + 1) / (2 ^ j * ((n true : ℚ) + n false) + 2) := by
  have h2 : (0 : ℚ) < 2 ^ j := by positivity
  simp only [dirichletPredictive, massWeight, Fintype.sum_bool, Fintype.card_bool]
  push_cast
  field_simp

/-- [definition] **The two-class urn's likelihood** of a digit word with `k` arrivals of one value
and `m` of the other: `(α)_k (α)_m/(2α)_(k+m)`. -/
noncomputable def urnBool (α : ℚ) (k m : ℕ) : ℚ :=
  (ascPochhammer ℚ k).eval α * (ascPochhammer ℚ m).eval α / (ascPochhammer ℚ (k + m)).eval (α + α)

/-- The urn's sequential likelihood of a binary word depends only on its two counts. -/
theorem urnSeq_eq_urnBool {α : ℚ} (hα : 0 < α) (w : List Bool) :
    urnSeq α w = urnBool α (w.count true) (w.count false) := by
  rw [urnSeq_bool hα, urnBool, count_true_add_count_false]

theorem urnBool_zero (α : ℚ) : urnBool α 0 0 = 1 := by
  simp [urnBool]

theorem urnBool_comm (α : ℚ) (k m : ℕ) : urnBool α k m = urnBool α m k := by
  rw [urnBool, urnBool, Nat.add_comm, mul_comm ((ascPochhammer ℚ k).eval α)]

theorem urnBool_pos {α : ℚ} (hα : 0 < α) (k m : ℕ) : 0 < urnBool α k m := by
  unfold urnBool
  have := ascPochhammer_pos k α hα
  have := ascPochhammer_pos m α hα
  have := ascPochhammer_pos (k + m) (α + α) (by linarith)
  positivity

/-- One more arrival of the first value multiplies the likelihood by the face `(α+k)/(2α+k+m)`. -/
theorem urnBool_succ_left {α : ℚ} (hα : 0 < α) (k m : ℕ) :
    urnBool α (k + 1) m = urnBool α k m * ((α + k) / (α + α + ((k + m : ℕ) : ℚ))) := by
  have hc := ascPochhammer_pos (k + m) (α + α) (by linarith)
  have hd : 0 < α + α + ((k + m : ℕ) : ℚ) := by positivity
  rw [urnBool, urnBool, show k + 1 + m = (k + m) + 1 by omega, ascPochhammer_succ_eval,
    ascPochhammer_succ_eval]
  field_simp

theorem urnBool_succ_right {α : ℚ} (hα : 0 < α) (k m : ℕ) :
    urnBool α k (m + 1) = urnBool α k m * ((α + m) / (α + α + ((k + m : ℕ) : ℚ))) := by
  rw [urnBool_comm, urnBool_succ_left hα, urnBool_comm, Nat.add_comm m k]

/-! ### The prior mass against KT: at most `j − 1` bits per node -/

/-- [proved-derived; formal-checked] **The comparison of faces.** When the arriving value is the
majority one (`m ≤ k`), the weight-`α` face is at least KT's for every `0 < α ≤ 1/2`:
`(1/2+k)/(1+k+m) ≤ (α+k)/(2α+k+m)`, the difference being `(1−2α)(k−m)/2` over the product of
the denominators. -/
theorem kt_face_le {α : ℚ} (hα : 0 < α) (hα2 : α ≤ 1 / 2) {k m : ℕ} (hkm : m ≤ k) :
    (1 / 2 + k) / (1 / 2 + 1 / 2 + ((k + m : ℕ) : ℚ)) ≤ (α + k) / (α + α + ((k + m : ℕ) : ℚ)) := by
  have hkm' : (m : ℚ) ≤ k := by exact_mod_cast hkm
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hα2) (sub_nonneg.2 hkm')]

/-- Two steps along the diagonal: the first face is exactly one half. -/
theorem urnBool_diag_succ {α : ℚ} (hα : 0 < α) (s : ℕ) :
    urnBool α (s + 2) (s + 2) =
      urnBool α (s + 1) (s + 1) * ((α + ((s : ℚ) + 1)) / (2 * (α + α + (2 * (s : ℚ) + 3)))) := by
  rw [show s + 2 = (s + 1) + 1 by omega, urnBool_succ_right hα, urnBool_succ_left hα]
  have hd : 0 < α + α + (2 * (s : ℚ) + 3) := by positivity
  have hd' : 0 < α + α + (2 * (s : ℚ) + 2) := by positivity
  push_cast
  field_simp; ring

/-- The diagonal invariant: `2α(2s+2) U_½(s+1,s+1) ≤ (2s+1+2α) U_α(s+1,s+1)`. -/
theorem kt_diag {α : ℚ} (hα : 0 < α) (hα2 : α ≤ 1 / 2) (s : ℕ) :
    2 * α * (2 * s + 2) * urnBool (1 / 2) (s + 1) (s + 1) ≤
      (2 * s + 1 + 2 * α) * urnBool α (s + 1) (s + 1) := by
  have hh : (0 : ℚ) < 1 / 2 := by norm_num
  induction s with
  | zero =>
    rw [urnBool_succ_right hα, urnBool_succ_left hα, urnBool_zero,
      urnBool_succ_right hh, urnBool_succ_left hh, urnBool_zero]
    push_cast
    rw [le_iff_eq_or_lt]; left
    field_simp; ring
  | succ s ih =>
    have ha := urnBool_pos hh (s + 1) (s + 1)
    have hb := urnBool_pos hα (s + 1) (s + 1)
    rw [urnBool_diag_succ hα, urnBool_diag_succ hh]
    set a := urnBool (1 / 2) (s + 1) (s + 1)
    set b := urnBool α (s + 1) (s + 1)
    have hs : (0 : ℚ) ≤ s := by positivity
    have key : α * a * (2 * s + 3) ≤ b * (α + s + 1) := by
      have h1 := mul_le_mul_of_nonneg_left ih (by positivity : (0 : ℚ) ≤ 2 * s + 3)
      have h2 : 0 ≤ b * (1 - 2 * α) := mul_nonneg hb.le (by linarith)
      have h3 : (0 : ℚ) < 2 * s + 2 := by positivity
      nlinarith
    have hd : 0 < α + α + (2 * (s : ℚ) + 3) := by positivity
    push_cast
    calc _ = α * a * (2 * s + 3) / 2 := by field_simp; ring
      _ ≤ b * (α + s + 1) / 2 := by linarith
      _ = _ := by field_simp; ring

theorem kt_diag_all {α : ℚ} (hα : 0 < α) (hα2 : α ≤ 1 / 2) (s : ℕ) :
    2 * α * urnBool (1 / 2) s s ≤ urnBool α s s := by
  cases s with
  | zero => rw [urnBool_zero, urnBool_zero]; linarith
  | succ s =>
    have h := kt_diag hα hα2 s
    have hb := urnBool_pos hα (s + 1) (s + 1)
    have hs : (0 : ℚ) ≤ s := by positivity
    have h2 : (2 * s + 1 + 2 * α) * urnBool α (s + 1) (s + 1) ≤
        (2 * s + 2) * urnBool α (s + 1) (s + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) hb.le
    have h3 : (0 : ℚ) < 2 * s + 2 := by positivity
    nlinarith

/-- Off the diagonal, each arrival of the majority value only raises the ratio `U_α/U_½`. -/
theorem kt_right {α : ℚ} (hα : 0 < α) (hα2 : α ≤ 1 / 2) (s d : ℕ) :
    2 * α * urnBool (1 / 2) (s + d) s ≤ urnBool α (s + d) s := by
  have hh : (0 : ℚ) < 1 / 2 := by norm_num
  induction d with
  | zero => exact kt_diag_all hα hα2 s
  | succ d ih =>
    rw [show s + (d + 1) = (s + d) + 1 by omega, urnBool_succ_left hα, urnBool_succ_left hh]
    have hf := kt_face_le hα hα2 (show s ≤ s + d by omega)
    have hf0 : 0 ≤ (1 / 2 + ((s + d : ℕ) : ℚ)) / (1 / 2 + 1 / 2 + ((s + d + s : ℕ) : ℚ)) := by
      positivity
    calc 2 * α * (urnBool (1 / 2) (s + d) s *
          ((1 / 2 + ((s + d : ℕ) : ℚ)) / (1 / 2 + 1 / 2 + ((s + d + s : ℕ) : ℚ))))
        = (2 * α * urnBool (1 / 2) (s + d) s) *
          ((1 / 2 + ((s + d : ℕ) : ℚ)) / (1 / 2 + 1 / 2 + ((s + d + s : ℕ) : ℚ))) := by ring
      _ ≤ urnBool α (s + d) s *
          ((1 / 2 + ((s + d : ℕ) : ℚ)) / (1 / 2 + 1 / 2 + ((s + d + s : ℕ) : ℚ))) :=
        mul_le_mul_of_nonneg_right ih hf0
      _ ≤ _ := mul_le_mul_of_nonneg_left hf (urnBool_pos hα _ _).le

/-- [proved-derived; formal-checked] **`priorMass_ge_kt`: the prior mass costs at most `j − 1` bits
against KT at every count.** For `0 < α ≤ 1/2` and every pair of counts,
`2α · KT(k, m) ≤ U_α(k, m)`. Along the diagonal the ratio `U_α/U_½` falls but stays above
`2α(2s+2)/(2s+1+2α)` (`kt_diag`); off it, every arrival of the majority value raises the ratio
(`kt_face_le`). At `α = 2^-j` the factor is `2^(1−j)`: `j − 1` bits (`priorMass_code_le_kt`). -/
theorem priorMass_ge_kt {α : ℚ} (hα : 0 < α) (hα2 : α ≤ 1 / 2) (k m : ℕ) :
    2 * α * urnBool (1 / 2) k m ≤ urnBool α k m := by
  rcases le_total m k with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact kt_right hα hα2 m d
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [urnBool_comm, urnBool_comm α]
    exact kt_right hα hα2 k d

/-- [proved-derived; formal-checked] **The one-sided context gains.** A node that has seen only one
digit value is never coded worse than by KT: `U_½(k, 0) ≤ U_α(k, 0)` for `0 < α ≤ 1/2`. -/
theorem priorMass_one_sided_ge_kt {α : ℚ} (hα : 0 < α) (hα2 : α ≤ 1 / 2) (k : ℕ) :
    urnBool (1 / 2) k 0 ≤ urnBool α k 0 := by
  have hh : (0 : ℚ) < 1 / 2 := by norm_num
  induction k with
  | zero => rw [urnBool_zero, urnBool_zero]
  | succ k ih =>
    rw [urnBool_succ_left hα, urnBool_succ_left hh]
    have hf := kt_face_le hα hα2 (Nat.zero_le k)
    exact mul_le_mul ih hf (by positivity) (urnBool_pos hα _ _).le

/-- [proved-derived; formal-checked] **The one-sided code length.** At weight `α ≤ 1/2`, after
`n + 1` arrivals of one value, `U_α(n+1, 0) ≥ 1/(2(1 + αn))`. -/
theorem priorMass_one_sided {α : ℚ} (hα : 0 < α) (hα2 : α ≤ 1 / 2) (n : ℕ) :
    1 / (2 * (1 + α * n)) ≤ urnBool α (n + 1) 0 := by
  induction n with
  | zero =>
    rw [urnBool_succ_left hα, urnBool_zero]
    push_cast
    field_simp
    nlinarith
  | succ n ih =>
    rw [urnBool_succ_left hα]
    have hn : (0 : ℚ) ≤ n := by positivity
    have hd : 0 < 1 + α * n := by positivity
    have hf : 0 ≤ (α + ((n + 1 : ℕ) : ℚ)) / (α + α + ((n + 1 + 0 : ℕ) : ℚ)) := by positivity
    calc 1 / (2 * (1 + α * ((n + 1 : ℕ) : ℚ)))
        ≤ 1 / (2 * (1 + α * n)) * ((α + ((n + 1 : ℕ) : ℚ)) / (α + α + ((n + 1 + 0 : ℕ) : ℚ))) := by
          push_cast
          rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_nonneg (mul_nonneg hα.le hn) (by linarith : (0 : ℚ) ≤ 1 - α),
            sq_nonneg α]
      _ ≤ _ := mul_le_mul_of_nonneg_right ih hf

/-- [proved-derived; formal-checked] **Two bits while `n ≤ 2^j`.** At rung `j ≥ 1`, a node whose
first `n + 1 ≤ 2^j + 1` arrivals all carry one value has likelihood at least `1/4`: its whole run
costs at most 2 bits, where KT's cost grows as `½ log₂ n`. -/
theorem priorMass_one_sided_two_bits {j : ℕ} (hj : 1 ≤ j) {n : ℕ} (hn : (n : ℚ) ≤ 2 ^ j) :
    1 / 4 ≤ urnBool (massWeight j) (n + 1) 0 := by
  refine le_trans ?_ (priorMass_one_sided (massWeight_pos j) (massWeight_le_half hj) n)
  have h2 : (0 : ℚ) < 2 ^ j := by positivity
  have : massWeight j * n ≤ 1 := by
    rw [massWeight, one_div_mul_eq_div, div_le_one h2]; exact hn
  have h0 : 0 ≤ massWeight j * n := mul_nonneg (massWeight_pos j).le (by positivity)
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  linarith

/-! ### The regret against the best fixed digit probability -/

open Real

/-- The central binomial bound `16^k ≤ 4k · C(2k, k)²`. -/
theorem sixteen_pow_le_centralBinom_sq {k : ℕ} (hk : 1 ≤ k) :
    16 ^ k ≤ 4 * k * Nat.centralBinom k ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have h := Nat.succ_mul_centralBinom_succ k
    have key : 4 * (k + 1) * Nat.centralBinom (k + 1) ^ 2 * (k + 1) =
        16 * (2 * k + 1) ^ 2 * Nat.centralBinom k ^ 2 := by
      calc 4 * (k + 1) * Nat.centralBinom (k + 1) ^ 2 * (k + 1)
          = 4 * ((k + 1) * Nat.centralBinom (k + 1)) ^ 2 := by ring
        _ = 4 * (2 * (2 * k + 1) * Nat.centralBinom k) ^ 2 := by rw [h]
        _ = _ := by ring
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos k)
    calc 16 ^ (k + 1) * (k + 1) = 16 * 16 ^ k * (k + 1) := by ring
      _ ≤ 16 * (4 * k * Nat.centralBinom k ^ 2) * (k + 1) := by gcongr
      _ = 16 * (4 * k * (k + 1)) * Nat.centralBinom k ^ 2 := by ring
      _ ≤ 16 * (2 * k + 1) ^ 2 * Nat.centralBinom k ^ 2 := by gcongr; nlinarith
      _ = _ := key.symm

theorem four_pow_le_centralBinom {k : ℕ} (hk : 1 ≤ k) :
    (4 : ℝ) ^ k ≤ 2 * √(k : ℝ) * Nat.centralBinom k := by
  have h : ((16 ^ k : ℕ) : ℝ) ≤ ((4 * k * Nat.centralBinom k ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast sixteen_pow_le_centralBinom_sq hk
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm k 2, pow_mul]
  push_cast at h
  norm_num
  linarith

/-- KT's rising factorial at one half: `(1/2)_k = k! · C(2k, k)/4^k`. -/
theorem ascPochhammer_eval_half (k : ℕ) :
    (ascPochhammer ℚ k).eval (1 / 2 : ℚ) = (k.factorial : ℚ) * Nat.centralBinom k / 4 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ih]
    have h' : ((k : ℚ) + 1) * Nat.centralBinom (k + 1) = 2 * (2 * k + 1) * Nat.centralBinom k := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    calc (k.factorial : ℚ) * Nat.centralBinom k / 4 ^ k * (1 / 2 + k)
        = (k.factorial : ℚ) * (2 * (2 * k + 1) * Nat.centralBinom k) / (4 ^ k * 4) := by
          field_simp; ring
      _ = (k.factorial : ℚ) * (((k : ℚ) + 1) * Nat.centralBinom (k + 1)) / (4 ^ k * 4) := by
          rw [h']
      _ = _ := by push_cast [Nat.factorial_succ]; ring

/-- [definition] **KT's half face** `k! · C(2k, k)/4^k = (1/2)_k`, in the reals. -/
noncomputable def halfFace (k : ℕ) : ℝ := (k.factorial : ℝ) * Nat.centralBinom k / 4 ^ k

theorem halfFace_pos (k : ℕ) : 0 < halfFace k := by
  unfold halfFace
  have := Nat.centralBinom_pos k
  have := k.factorial_pos
  positivity

/-- KT's two-class likelihood through the half faces: `KT(k, m) = (1/2)_k (1/2)_m/(k+m)!`. -/
theorem urnBool_half_real (k m : ℕ) :
    (urnBool (1 / 2) k m : ℝ) = halfFace k * halfFace m / (k + m).factorial := by
  rw [urnBool, ascPochhammer_eval_half, ascPochhammer_eval_half,
    show (1 / 2 : ℚ) + 1 / 2 = 1 by norm_num, ascPochhammer_eval_one, halfFace, halfFace]
  push_cast
  ring

/-- Stirling's lower bound read on the half face: `√(π/2) (k/e)^k ≤ (1/2)_k`. -/
theorem halfFace_lower {k : ℕ} (hk : 1 ≤ k) :
    √(π / 2) * ((k : ℝ) / exp 1) ^ k ≤ halfFace k := by
  have hc := four_pow_le_centralBinom hk
  have hs := Stirling.le_factorial_stirling k
  have hsq : √(2 * π * k) = 2 * √(k : ℝ) * √(π / 2) := by
    rw [show (2 : ℝ) * π * k = (2 ^ 2 * k) * (π / 2) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  unfold halfFace
  rw [le_div_iff₀ (by positivity)]
  have h0 : 0 ≤ √(π / 2) * ((k : ℝ) / exp 1) ^ k := by positivity
  calc √(π / 2) * ((k : ℝ) / exp 1) ^ k * 4 ^ k
      ≤ √(π / 2) * ((k : ℝ) / exp 1) ^ k * (2 * √(k : ℝ) * Nat.centralBinom k) :=
        mul_le_mul_of_nonneg_left hc h0
    _ = √(2 * π * k) * ((k : ℝ) / exp 1) ^ k * Nat.centralBinom k := by rw [hsq]; ring
    _ ≤ (k.factorial : ℝ) * Nat.centralBinom k :=
        mul_le_mul_of_nonneg_right hs (by positivity)

/-- Stirling's upper bound from the first term of the decreasing sequence: `n! ≤ e √n (n/e)^n`. -/
theorem factorial_le_stirling_upper {n : ℕ} (hn : n ≠ 0) :
    (n.factorial : ℝ) ≤ exp 1 * √(n : ℝ) * ((n : ℝ) / exp 1) ^ n := by
  have h : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
    have := Stirling.stirlingSeq'_antitone (Nat.zero_le (n - 1))
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn)] using this
  have hpos : 0 < √(2 * (n : ℝ)) * ((n : ℝ) / exp 1) ^ n := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have := Real.sqrt_pos.2 (show (0 : ℝ) < 2 * n by linarith)
    positivity
  rw [Stirling.stirlingSeq_one, Stirling.stirlingSeq, div_le_iff₀ hpos] at h
  calc (n.factorial : ℝ) ≤ exp 1 / √2 * (√(2 * n) * ((n : ℝ) / exp 1) ^ n) := h
    _ = exp 1 * √(n : ℝ) * ((n : ℝ) / exp 1) ^ n := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have : (0 : ℝ) < √2 := by positivity
      field_simp

/-- [definition] **The best fixed digit probability's likelihood** of `k` arrivals of one value and
`m` of the other: `(k/n)^k (m/n)^m`, `n = k + m`, the maximum over `θ` of `θ^k (1−θ)^m`
(`fixed_le_bestFixed`). -/
noncomputable def bestFixed (k m : ℕ) : ℝ := ((k : ℝ) / (k + m)) ^ k * ((m : ℝ) / (k + m)) ^ m

theorem bestFixed_comm (k m : ℕ) : bestFixed k m = bestFixed m k := by
  unfold bestFixed; rw [add_comm (k : ℝ)]; ring

theorem bestFixed_pos (k m : ℕ) : 0 < bestFixed k m := by
  unfold bestFixed
  apply mul_pos
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have : (0 : ℝ) < k := by exact_mod_cast hk
      positivity
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have : (0 : ℝ) < m := by exact_mod_cast hm
      positivity

/-- [proved-derived; formal-checked] **No fixed digit probability does better than `bestFixed`.**
For every `θ ∈ [0, 1]`, `θ^k (1−θ)^m ≤ (k/n)^k (m/n)^m` (Gibbs: `log x ≤ x − 1`). -/
theorem fixed_le_bestFixed {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (k m : ℕ) :
    θ ^ k * (1 - θ) ^ m ≤ bestFixed k m := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [bestFixed]
    · have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      simp only [bestFixed, pow_zero, one_mul, Nat.cast_zero, zero_add, div_self this, one_pow]
      exact pow_le_one₀ (by linarith) (by linarith)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    simp only [bestFixed, pow_zero, mul_one, Nat.cast_zero, add_zero, div_self this, one_pow]
    exact pow_le_one₀ h0 h1
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hb := bestFixed_pos k m
  rcases eq_or_lt_of_le h0 with rfl | hθ0
  · rw [zero_pow hk.ne']; simpa using hb.le
  rcases eq_or_lt_of_le h1 with rfl | hθ1
  · rw [sub_self, zero_pow hm.ne']; simpa using hb.le
  have hθ1' : 0 < 1 - θ := by linarith
  unfold bestFixed
  set p := (k : ℝ) / (k + m)
  set q := (m : ℝ) / (k + m)
  have hp : 0 < p := by positivity
  have hq : 0 < q := by positivity
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_pow]
  have e1 : Real.log θ - Real.log p ≤ θ / p - 1 := by
    rw [← Real.log_div hθ0.ne' hp.ne']; exact Real.log_le_sub_one_of_pos (by positivity)
  have e2 : Real.log (1 - θ) - Real.log q ≤ (1 - θ) / q - 1 := by
    rw [← Real.log_div hθ1'.ne' hq.ne']; exact Real.log_le_sub_one_of_pos (by positivity)
  have s1 : (k : ℝ) * (θ / p - 1) + m * ((1 - θ) / q - 1) = 0 := by
    simp only [p, q]; field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left e1 hk'.le, mul_le_mul_of_nonneg_left e2 hm'.le]

/-- [proved-derived; formal-checked] **`kt_regret`: KT's regret is at most `½ log₂ n + 1` bits.**
Against the best fixed digit probability, `(k/n)^k (m/n)^m ≤ 2√n · KT(k, m)` for every `n ≥ 1`.
Through `KT(k, m) = (1/2)_k (1/2)_m/n!`, Stirling's lower bound on `k!` and `m!` (Mathlib's
`le_factorial_stirling`), the first term of the decreasing Stirling sequence for `n!`, and the
central binomial bound `16^k ≤ 4k C(2k,k)²`, the constant is `π/(2e) ≥ 1/2`. This closes the KT
redundancy that `Tree`'s header left owed in #62. -/
theorem kt_regret {k m : ℕ} (h : 1 ≤ k + m) :
    bestFixed k m ≤ 2 * √((k : ℝ) + m) * (urnBool (1 / 2) k m : ℝ) := by
  -- the one-sided case, then symmetry
  have one_sided : ∀ n : ℕ, 1 ≤ n → bestFixed n 0 ≤ 2 * √((n : ℝ) + 0) * (urnBool (1 / 2) n 0 : ℝ) := by
    intro n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    rw [urnBool_half_real, add_zero, halfFace, halfFace]
    simp only [bestFixed, Nat.cast_zero, add_zero, div_self hn', one_pow, pow_zero, mul_one,
      Nat.factorial_zero, Nat.cast_one, Nat.centralBinom_zero, div_one]
    have hc := four_pow_le_centralBinom hn
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    rw [show (n.factorial : ℝ) * Nat.centralBinom n / 4 ^ n / n.factorial =
      Nat.centralBinom n / 4 ^ n by field_simp]
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    linarith
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using one_sided k (by simpa using h)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [bestFixed_comm, urnBool_comm, add_comm (( 0 : ℕ) : ℝ)]
    simpa using one_sided m hm
  -- both counts positive
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn : (0 : ℝ) < k + m := by positivity
  have gk := halfFace_lower hk
  have gm := halfFace_lower hm
  have hF := factorial_le_stirling_upper (n := k + m) (by omega)
  have hF0 : (0 : ℝ) < (k + m).factorial := by exact_mod_cast (k + m).factorial_pos
  have hpi : exp 1 ≤ π := by
    have := Real.exp_one_lt_d9; have := Real.pi_gt_three; linarith
  have hπ2 : √(π / 2) * √(π / 2) = π / 2 := Real.mul_self_sqrt (by positivity)
  have hsplit : ((k : ℝ) / exp 1) ^ k * ((m : ℝ) / exp 1) ^ m =
      bestFixed k m * (((k : ℝ) + m) / exp 1) ^ (k + m) := by
    unfold bestFixed
    rw [pow_add, show ((k : ℝ) / exp 1) = (k : ℝ) / (k + m) * ((k + m) / exp 1) by
        field_simp,
      show ((m : ℝ) / exp 1) = (m : ℝ) / (k + m) * ((k + m) / exp 1) by field_simp,
      mul_pow, mul_pow]
    ring
  have hb := bestFixed_pos k m
  have hgk := halfFace_pos k
  have hgm := halfFace_pos m
  have hE : (0 : ℝ) < (((k : ℝ) + m) / exp 1) ^ (k + m) := by positivity
  push_cast at hF
  rw [urnBool_half_real, mul_div_assoc', le_div_iff₀ hF0]
  calc bestFixed k m * ((k + m).factorial : ℝ)
      ≤ bestFixed k m * (exp 1 * √((k : ℝ) + m) * (((k : ℝ) + m) / exp 1) ^ (k + m)) :=
        mul_le_mul_of_nonneg_left hF hb.le
    _ ≤ bestFixed k m * (π * √((k : ℝ) + m) * (((k : ℝ) + m) / exp 1) ^ (k + m)) := by
        gcongr
    _ = 2 * √((k : ℝ) + m) * ((√(π / 2) * √(π / 2)) *
          (((k : ℝ) / exp 1) ^ k * ((m : ℝ) / exp 1) ^ m)) := by
        rw [hπ2, hsplit]; ring
    _ = 2 * √((k : ℝ) + m) * ((√(π / 2) * ((k : ℝ) / exp 1) ^ k) *
          (√(π / 2) * ((m : ℝ) / exp 1) ^ m)) := by ring
    _ ≤ 2 * √((k : ℝ) + m) * (halfFace k * halfFace m) := by
        gcongr

/-- [proved-derived; formal-checked] **`priorMass_regret`: the regret at rung `j` is at most
`½ log₂ n + j` bits.** For `j ≥ 1` and `n = k + m ≥ 1`, the best fixed digit probability's
likelihood is at most `2^j √n` times the node's: KT's `2√n` (`kt_regret`) times the
`2^(j−1)` of `priorMass_ge_kt`. -/
theorem priorMass_regret {j : ℕ} (hj : 1 ≤ j) {k m : ℕ} (h : 1 ≤ k + m) :
    bestFixed k m ≤ 2 ^ j * √((k : ℝ) + m) * (urnBool (massWeight j) k m : ℝ) := by
  have hkt := kt_regret h
  have hge : ((2 * massWeight j * urnBool (1 / 2) k m : ℚ) : ℝ) ≤ (urnBool (massWeight j) k m : ℝ) :=
    by exact_mod_cast priorMass_ge_kt (massWeight_pos j) (massWeight_le_half hj) k m
  have h2 : (2 : ℝ) ^ j * (2 * (massWeight j : ℝ)) = 2 := by
    rw [massWeight]; push_cast; field_simp
  push_cast at hge
  calc bestFixed k m ≤ 2 * √((k : ℝ) + m) * (urnBool (1 / 2) k m : ℝ) := hkt
    _ = 2 ^ j * √((k : ℝ) + m) * (2 * (massWeight j : ℝ) * (urnBool (1 / 2) k m : ℝ)) := by
        rw [show (2 : ℝ) ^ j * √((k : ℝ) + m) * (2 * (massWeight j : ℝ) * (urnBool (1 / 2) k m : ℝ))
          = (2 ^ j * (2 * (massWeight j : ℝ))) * √((k : ℝ) + m) * (urnBool (1 / 2) k m : ℝ) by ring,
          h2]
    _ ≤ 2 ^ j * √((k : ℝ) + m) * (urnBool (massWeight j) k m : ℝ) := by
        gcongr

/-- [definition] **Code length in bits** of a likelihood: `−log₂ P`. -/
noncomputable def codeBits (P : ℝ) : ℝ := -Real.logb 2 P

/-- [proved-derived; formal-checked] **`priorMass_code_le_kt`: `j − 1` bits over KT.** At rung
`j ≥ 1`, every node's code length is at most KT's plus `j − 1` bits, at every count. -/
theorem priorMass_code_le_kt {j : ℕ} (hj : 1 ≤ j) (k m : ℕ) :
    codeBits (urnBool (massWeight j) k m) ≤ codeBits (urnBool (1 / 2) k m) + (j - 1) := by
  have hge : ((2 * massWeight j * urnBool (1 / 2) k m : ℚ) : ℝ) ≤ (urnBool (massWeight j) k m : ℝ) :=
    by exact_mod_cast priorMass_ge_kt (massWeight_pos j) (massWeight_le_half hj) k m
  have hpos : (0 : ℝ) < (urnBool (1 / 2) k m : ℝ) := by exact_mod_cast urnBool_pos (by norm_num) k m
  have hw : (0 : ℝ) < 2 * (massWeight j : ℝ) := by
    have := massWeight_pos j; have : (0 : ℝ) < (massWeight j : ℝ) := by exact_mod_cast this
    positivity
  push_cast at hge
  have hl := Real.logb_le_logb_of_le (b := 2) (by norm_num) (mul_pos hw hpos) hge
  rw [Real.logb_mul hw.ne' hpos.ne'] at hl
  have hlw : Real.logb 2 (2 * (massWeight j : ℝ)) = 1 - j := by
    rw [massWeight]; push_cast
    rw [show (2 : ℝ) * (1 / 2 ^ j) = 2 ^ (1 - (j : ℝ)) by
      rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast]; ring]
    rw [Real.logb_rpow (by norm_num) (by norm_num)]
  unfold codeBits
  linarith

/-- [proved-derived; formal-checked] **The regret in bits.** At rung `j ≥ 1`, with `n = k + m ≥ 1`,
the node's code length exceeds the best fixed digit probability's by at most `½ log₂ n + j`
bits; at `j = 1` (KT) by at most `½ log₂ n + 1`. -/
theorem priorMass_regret_bits {j : ℕ} (hj : 1 ≤ j) {k m : ℕ} (h : 1 ≤ k + m) :
    codeBits (urnBool (massWeight j) k m) ≤
      codeBits (bestFixed k m) + Real.logb 2 ((k : ℝ) + m) / 2 + j := by
  have hr := priorMass_regret hj h
  have hb := bestFixed_pos k m
  have hn : (0 : ℝ) < (k : ℝ) + m := by exact_mod_cast h
  have hU : (0 : ℝ) < (urnBool (massWeight j) k m : ℝ) := by
    exact_mod_cast urnBool_pos (massWeight_pos j) k m
  have hl := Real.logb_le_logb_of_le (b := 2) (by norm_num) hb hr
  rw [Real.logb_mul (by positivity) hU.ne', Real.logb_mul (by positivity) (by positivity),
    Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hl
  have hs : Real.logb 2 √((k : ℝ) + m) = Real.logb 2 ((k : ℝ) + m) / 2 := by
    unfold Real.logb; rw [Real.log_sqrt hn.le]; ring
  rw [hs] at hl
  unfold codeBits
  linarith

/-- [proved-derived; formal-checked] **Against every fixed digit probability.** For every
`θ ∈ [0, 1]`, `θ^k (1−θ)^m ≤ 2^j √n · U_(2^-j)(k, m)`. -/
theorem priorMass_regret_fixed {j : ℕ} (hj : 1 ≤ j) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    {k m : ℕ} (h : 1 ≤ k + m) :
    θ ^ k * (1 - θ) ^ m ≤ 2 ^ j * √((k : ℝ) + m) * (urnBool (massWeight j) k m : ℝ) :=
  (fixed_le_bestFixed h0 h1 k m).trans (priorMass_regret hj h)

/-! ### The choice of rung is a two-part code -/

/-- [proved-derived; formal-checked] **`two_part_kraft`: charging `log₂ B` bits for the choice
keeps the code valid.** For `B` laws `P_b`, each a sub-probability on a finite set, and **any**
choice `ĵ : X → Fin B` (made on training cells, or even on the coded data itself), the two-part
lengths `log₂ B + code_(ĵ x)(x)` satisfy Kraft: `Σ_x P_(ĵ x)(x)/B ≤ 1`. -/
theorem two_part_kraft {X : Type*} [Fintype X] {B : ℕ} (P : Fin B → X → ℝ)
    (h0 : ∀ b x, 0 ≤ P b x) (h1 : ∀ b, ∑ x, P b x ≤ 1) (choice : X → Fin B) :
    ∑ x, P (choice x) x / B ≤ 1 := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · have : IsEmpty X := ⟨fun x => (choice x).elim0⟩
    simp
  · rw [← Finset.sum_div, div_le_one (by exact_mod_cast hB)]
    calc ∑ x, P (choice x) x ≤ ∑ x, ∑ b, P b x :=
          Finset.sum_le_sum fun x _ =>
            Finset.single_le_sum (f := fun b => P b x) (fun b _ => h0 b x) (Finset.mem_univ _)
      _ = ∑ b, ∑ x, P b x := Finset.sum_comm
      _ ≤ ∑ _b : Fin B, (1 : ℝ) := Finset.sum_le_sum fun b _ => h1 b
      _ = B := by simp

/-- The Dirichlet predictive is a probability over the two digit values. -/
theorem dirichletPredictive_sum_bool {α : ℚ} (hα : 0 < α) (n : Bool → ℕ) :
    ∑ b, dirichletPredictive α n b = 1 := by
  have : (0 : ℚ) < (n true : ℚ) + n false + 2 * α := by positivity
  simp only [dirichletPredictive, Fintype.sum_bool, Fintype.card_bool]
  push_cast
  field_simp
  ring

theorem ofFn_snoc_bool {n : ℕ} (f : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc (α := fun _ => Bool) f b) = List.ofFn f ++ [b] := by
  rw [List.ofFn_succ']
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- [proved-derived; formal-checked] **The node's urn is a probability law on digit words.** For
every weight `α > 0` and length `n`, the urn likelihoods of the `2^n` binary words sum to one. -/
theorem urnSeq_sum {α : ℚ} (hα : 0 < α) (n : ℕ) :
    ∑ f : Fin n → Bool, urnSeq α (List.ofFn f) = 1 := by
  induction n with
  | zero => simp [urnSeq, urnRev]
  | succ n ih =>
    rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, ofFn_snoc_bool, urnSeq_snoc, ← Finset.mul_sum,
      dirichletPredictive_sum_bool hα, mul_one, ih]

/-- [proved-derived; formal-checked] **`priorMass_two_part`: the ladder `j = 1..8` charged 3 bits
is a valid code.** For every node with `n` digits and every choice of rung `ĵ ∈ {1, …, 8}`, the
lengths `3 + code_ĵ` satisfy Kraft: `Σ_w 2^-(3 + code_(ĵ w)(w)) ≤ 1`. -/
theorem priorMass_two_part (n : ℕ) (choice : (Fin n → Bool) → Fin 8) :
    ∑ f : Fin n → Bool,
      (2 : ℝ) ^ (-(3 + codeBits (urnSeq (massWeight ((choice f : ℕ) + 1)) (List.ofFn f)))) ≤ 1 := by
  have hP : ∀ (b : Fin 8) (f : Fin n → Bool), (0 : ℝ) < (urnSeq (massWeight ((b : ℕ) + 1)) (List.ofFn f) : ℝ) := by
    intro b f
    rw [urnSeq_eq_urnBool (massWeight_pos _)]
    exact_mod_cast urnBool_pos (massWeight_pos _) _ _
  have hk := two_part_kraft (B := 8)
    (fun b (f : Fin n → Bool) => (urnSeq (massWeight ((b : ℕ) + 1)) (List.ofFn f) : ℝ))
    (fun b f => (hP b f).le)
    (fun b => by
      have := urnSeq_sum (massWeight_pos ((b : ℕ) + 1)) n
      exact le_of_eq (by exact_mod_cast this))
    choice
  refine le_of_eq_of_le (Finset.sum_congr rfl fun f _ => ?_) hk
  rw [codeBits, neg_add, neg_neg, Real.rpow_add (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) (hP (choice f) f), Real.rpow_neg (by norm_num)]
  norm_num
  ring

/-! ### The node law and its floor -/

/-- [definition] **The prior-mass node law**: the register is the digit counts, stepped by
`Tree.bump`, read at the Dirichlet predictive at weight `2^-j`. Every theorem of the tree weighting
stated for a `Tree.NodeLaw` (its Kraft form and dominance, its step, its compaction) holds for it. -/
def massLaw (j : ℕ) : NodeLaw Bool where
  State := Bool → ℕ
  init := fun _ => 0
  step := bump
  face := dirichletPredictive (massWeight j)
  face_pos := fun n c => by
    have := massWeight_pos j
    unfold dirichletPredictive
    positivity
  face_sum := fun n => dirichletPredictive_sum_bool (massWeight_pos j) n

/-- [proved-derived; formal-checked] **`massLaw_read`: the node keeps the counts and weighs the
urn.** Its register after a word is the word's counts, and its own weight is the urn likelihood
`urnSeq 2^-j`, which is `U_(2^-j)(k, m)` (`urnSeq_eq_urnBool`). -/
theorem massLaw_read (j : ℕ) (w : List Bool) :
    (massLaw j).run w = counts w ∧ (massLaw j).mass w = urnSeq (massWeight j) w := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨counts_nil.symm, by rw [NodeLaw.mass_nil]; rfl⟩
  | append_singleton w c ih =>
    refine ⟨?_, ?_⟩
    · rw [NodeLaw.run_snoc, ih.1, counts_snoc]
      rfl
    · rw [NodeLaw.mass_snoc, ih.1, ih.2, urnSeq_snoc]
      rfl

/-- [proved-derived; formal-checked] **The node's floor** `1/(2^j n* + 2)`: a node that has seen
at most `n*` arrivals reads each digit value at least at `1/(2^j n* + 2)`; at `j = 1` KT's
`1/(2n* + 2)` (`Tree.kt_binary_ge`). -/
theorem priorMass_face_ge (j : ℕ) (n : Bool → ℕ) {N : ℕ} (hN : n true + n false ≤ N) (b : Bool) :
    1 / (2 ^ j * (N : ℚ) + 2) ≤ dirichletPredictive (massWeight j) n b := by
  rw [priorMass_face]
  have hN' : ((n true : ℚ) + n false) ≤ N := by exact_mod_cast hN
  have h2 : (0 : ℚ) < 2 ^ j := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hN' h2.le,
    mul_nonneg (mul_nonneg h2.le (Nat.cast_nonneg (n b) : (0 : ℚ) ≤ n b))
      (by positivity : (0 : ℚ) ≤ 2 ^ j * N + 2)]

/-- [proved-derived; formal-checked] **`priorMass_digit_face_ge`: the path's floor at prior mass
`2^-j`.** On a binary landmark tree whose nodes read the prior-mass face, if every node of the
opened path holds at most `n` arrivals, the path face at every depth is at least `1/(2^j n + 2)`,
under **any** stop weights `λ_d ∈ [0, 1]` (the exact posterior weights and the executed chart's
alike), through `Tree.path_face_ge_min` and the node floor `priorMass_face_ge`. At `j = 1` it is
`Tree.digit_face_ge`'s `1/(2n + 2)`. This is the floor the lattice width `M_p` reads
(Rust `face_bits`). -/
theorem priorMass_digit_face_ge {Ltr : Type*} (j : ℕ) (N : TreeStanding Ltr Bool)
    (lam : ℕ → ℚ) (D : ℕ) (hl : ∀ d < D, 0 ≤ lam d ∧ lam d ≤ 1) (a : List Ltr) (n : ℕ)
    (hn : ∀ d ≤ D, ∑ b, N (a.take d) b ≤ n) (b : Bool) :
    ∀ d ≤ D, 1 / (2 ^ j * (n : ℚ) + 2) ≤
      pathFace (fun d => dirichletPredictive (massWeight j) (N (a.take d))) lam D d b := by
  intro d hd
  refine (path_face_ge_min _ lam D b hl).1 _ d hd fun d' _ h2 => ?_
  have h := hn d' h2
  rw [Fintype.sum_bool] at h
  exact priorMass_face_ge j (N (a.take d')) h b

/-! ### The tree's redundancy at prior mass `2^-j` -/

section Redundancy

variable {Ltr : Type*} [Fintype Ltr] [DecidableEq Ltr] {A : Type*} [Fintype A]

/-- [definition] **The law standing of an observation list** (oldest first): each observation
`(a, c)` arrives at its address `a` (`Tree.lawArrive`), from the standing where no node is reached.
Under a causal context it is `Tree.lawStandingOf` (`observations`); here the addresses are any. -/
def obsStanding (L : NodeLaw A) (obs : List (List Ltr × A)) : LawStanding L Ltr :=
  obs.foldl (fun N o => lawArrive L N o.1 o.2) fun _ => none

omit [Fintype Ltr] in
theorem obsStanding_snoc (L : NodeLaw A) (obs : List (List Ltr × A)) (a : List Ltr) (c : A) :
    obsStanding L (obs ++ [(a, c)]) = lawArrive L (obsStanding L obs) a c := by
  rw [obsStanding, List.foldl_append]
  rfl

omit [Fintype Ltr] in
/-- Each node of the standing holds the node law's register and own weight of its routed
subsequence (`Tree.law_state_own_routed` for any observation list). -/
theorem obs_state_own_routed (L : NodeLaw A) (obs : List (List Ltr × A)) (s : List Ltr) :
    lawState L (obsStanding L obs) s = L.run (routed obs s) ∧
      lawOwn L (obsStanding L obs) s = L.mass (routed obs s) := by
  induction obs using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton obs o ih =>
    obtain ⟨a, c⟩ := o
    rw [obsStanding_snoc, routed_snoc]
    by_cases hs : a.take s.length = s
    · rw [if_pos hs, NodeLaw.run_snoc, NodeLaw.mass_snoc, ← ih.1, ← ih.2]
      simp [lawState, lawOwn, lawArrive, hs]
    · rw [if_neg hs, List.append_nil]
      simpa [lawState, lawOwn, lawArrive, hs] using ih

omit [Fintype Ltr] in
theorem lawOwn_obs_pos (L : NodeLaw A) (obs : List (List Ltr × A)) (s : List Ltr) :
    0 < lawOwn L (obsStanding L obs) s := by
  rw [(obs_state_own_routed L obs s).2]
  exact L.mass_pos _

/-- [definition] **The code the tree emits** over an observation list: the product of the tree's
faces at the root, each arrival read at the face of the standing before it (newest first in
`emittedRev`). Its `−log₂` is the passage's code length. -/
def emittedRev (L : NodeLaw A) (w : ℕ → ℚ) (D : ℕ) : List (List Ltr × A) → ℚ
  | [] => 1
  | o :: obs => emittedRev L w D obs * lawFace L w (obsStanding L obs.reverse) D o.1 0 o.2

/-- [definition] The emitted mass of an observation list, oldest first. -/
def emitted (L : NodeLaw A) (w : ℕ → ℚ) (D : ℕ) (obs : List (List Ltr × A)) : ℚ :=
  emittedRev L w D obs.reverse

theorem emitted_nil (L : NodeLaw A) (w : ℕ → ℚ) (D : ℕ) :
    emitted L w D ([] : List (List Ltr × A)) = 1 := rfl

theorem emitted_snoc (L : NodeLaw A) (w : ℕ → ℚ) (D : ℕ) (obs : List (List Ltr × A))
    (o : List Ltr × A) :
    emitted L w D (obs ++ [o]) = emitted L w D obs * lawFace L w (obsStanding L obs) D o.1 0 o.2 := by
  simp [emitted, emittedRev]

theorem emitted_pos (L : NodeLaw A) {w : ℕ → ℚ} (hw : StopLaw₀ w) (D : ℕ)
    (obs : List (List Ltr × A)) : 0 < emitted L w D obs := by
  induction obs using List.reverseRecOn with
  | nil => exact one_pos
  | append_singleton obs o ih =>
    rw [emitted_snoc]
    exact mul_pos ih ((law_face_normalized L hw _ (lawOwn_obs_pos L obs) D o.1 0
      (Nat.zero_le _)).1 o.2)

/-- [proved-derived; formal-checked] **`emitted_eq_weight`: the emitted code is the root's weight.**
When every address reaches depth `D`, the product of the tree's faces over the passage is the
tree's weight at the root over the node law's own weights, `∏_t q_0(x_t) = W_root`
(`Tree.law_weight_step₀` at depth `0`, from `Tree.ownWeight_one`). -/
theorem emitted_eq_weight (L : NodeLaw A) {w : ℕ → ℚ} (hw : StopLaw₀ w) (D : ℕ)
    (obs : List (List Ltr × A)) (hD : ∀ o ∈ obs, D ≤ o.1.length) :
    emitted L w D obs = ownWeight w (lawOwn L (obsStanding L obs)) D [] := by
  induction obs using List.reverseRecOn with
  | nil =>
    have e : lawOwn L (obsStanding L ([] : List (List Ltr × A))) = fun _ => 1 := rfl
    rw [e, ownWeight_one]
    rfl
  | append_singleton obs o ih =>
    have hD' : D ≤ o.1.length := hD o (by simp)
    rw [emitted_snoc, ih fun o' h => hD o' (by simp [h])]
    obtain ⟨a, c⟩ := o
    have h := law_weight_step₀ L hw (obsStanding L obs) (lawOwn_obs_pos L obs) hD' c 0
      (Nat.zero_le _)
    simp only [Nat.sub_zero, List.take_zero] at h
    rw [obsStanding_snoc]
    exact h.symm

/-- [proved-derived; formal-checked] **The sequential code is complete.** Under a causal context
whose addresses reach depth `D`, the emitted masses of the `|A|^n` words of length `n` sum to one,
for any node law and any stop weights in `[0, 1)`. -/
theorem emitted_sum (L : NodeLaw A) {w : ℕ → ℚ} (hw : StopLaw₀ w) (ctx : List A → List Ltr)
    (D : ℕ) (n : ℕ) :
    ∑ v : Fin n → A, emitted L w D (observations ctx (List.ofFn v)) = 1 := by
  have hn : wordSum n (fun h => emitted L w D (observations ctx h)) = 1 := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [wordSum]
      have e : (fun h => ∑ c, emitted L w D (observations ctx (c :: h))) =
          fun h => emitted L w D (observations ctx h) := by
        funext h
        simp only [observations, emitted_snoc, ← Finset.mul_sum]
        rw [(law_face_normalized L hw _ (lawOwn_obs_pos L _) D (ctx h) 0 (Nat.zero_le _)).2,
          mul_one]
      rw [e, ih]
  rwa [wordSum_eq_sum] at hn

omit [DecidableEq Ltr] in
theorem prior_nonneg₀ {w : ℕ → ℚ} (hw : StopLaw₀ w) :
    ∀ m d (S : PrunedTree Ltr m), 0 ≤ PrunedTree.prior w m d S
  | 0, _, _ => by simp [PrunedTree.prior]
  | m + 1, d, S => by
    cases hS : (S : Option (Ltr → PrunedTree Ltr m)) with
    | none => simp only [PrunedTree.prior, Option.elim]; exact (hw d).1
    | some f =>
      simp only [PrunedTree.prior, Option.elim]
      exact mul_nonneg (sub_nonneg.mpr (hw d).2.le)
        (Finset.prod_nonneg fun b _ => prior_nonneg₀ hw m (d + 1) (f b))

/-- **Dominance with forced depths**: under stop weights in `[0, 1)` and positive own weights,
`prior_w(S) ∏_(leaves) E ≤ W` for every pruned tree (`Tree.own_kraft_and_dominance`'s, which
needs `w_d > 0`; a tree stopping at a forced depth has prior `0`). -/
theorem own_dominance₀ {w : ℕ → ℚ} (hw : StopLaw₀ w) {E : List Ltr → ℚ} (hE : ∀ s, 0 < E s)
    (m : ℕ) (s : List Ltr) (S : PrunedTree Ltr m) :
    PrunedTree.prior w m s.length S * ownLik E m s S ≤ ownWeight w E m s := by
  rw [own_mixture_over_trees w E m s]
  exact Finset.single_le_sum (f := fun S => PrunedTree.prior w m s.length S * ownLik E m s S)
    (fun S _ => mul_nonneg (prior_nonneg₀ hw m _ S) (ownLik_pos hE m s S).le) (Finset.mem_univ S)

/-- [definition] **A sum over the leaves** of a pruned tree: `f` at each leaf, the leaf addressed
by its path from `s`. -/
def leafSum (f : List Ltr → ℝ) : (m : ℕ) → List Ltr → PrunedTree Ltr m → ℝ
  | 0, s, _ => f s
  | m + 1, s, S => Option.elim (S : Option (Ltr → PrunedTree Ltr m)) (f s)
      fun g => ∑ b, leafSum f m (s ++ [b]) (g b)

omit [DecidableEq Ltr] in
theorem leafSum_mono {f g : List Ltr → ℝ} (h : ∀ s, f s ≤ g s) :
    ∀ m s (S : PrunedTree Ltr m), leafSum f m s S ≤ leafSum g m s S
  | 0, s, _ => h s
  | m + 1, s, S => by
    cases hS : (S : Option (Ltr → PrunedTree Ltr m)) with
    | none => simp only [leafSum, Option.elim]; exact h s
    | some G =>
      simp only [leafSum, Option.elim]
      exact Finset.sum_le_sum fun b _ => leafSum_mono h m _ _

omit [DecidableEq Ltr] in
theorem leafSum_neg (f : List Ltr → ℝ) :
    ∀ m s (S : PrunedTree Ltr m), leafSum (fun s => -f s) m s S = -leafSum f m s S
  | 0, s, _ => rfl
  | m + 1, s, S => by
    cases hS : (S : Option (Ltr → PrunedTree Ltr m)) with
    | none => simp only [leafSum, Option.elim]
    | some G =>
      simp only [leafSum, Option.elim, leafSum_neg f m, Finset.sum_neg_distrib]

omit [DecidableEq Ltr] in
/-- The code length of a pruned tree's leaves is the sum of its leaves' code lengths. -/
theorem logb_ownLik {E : List Ltr → ℚ} (hE : ∀ s, 0 < E s) :
    ∀ m s (S : PrunedTree Ltr m),
      Real.logb 2 (ownLik E m s S : ℝ) = leafSum (fun s => Real.logb 2 (E s : ℝ)) m s S
  | 0, s, _ => rfl
  | m + 1, s, S => by
    cases hS : (S : Option (Ltr → PrunedTree Ltr m)) with
    | none => simp only [ownLik, leafSum, Option.elim]
    | some G =>
      simp only [ownLik, leafSum, Option.elim]
      push_cast
      rw [Real.logb_prod _ _ fun b _ => by exact_mod_cast (ownLik_pos hE m _ (G b)).ne']
      exact Finset.sum_congr rfl fun b _ => logb_ownLik hE m _ _

/-- [definition] **A leaf's parameter charge** at rung `j`: `½ log₂ n + j` bits for a leaf that
`n ≥ 1` arrivals reached, none for a leaf no arrival reached. -/
noncomputable def leafCharge (j k m : ℕ) : ℝ :=
  if k + m = 0 then 0 else Real.logb 2 ((k : ℝ) + m) / 2 + j

/-- The node's code is within its charge of the best fixed digit probability at every count,
the empty node included (`priorMass_regret_bits`). -/
theorem node_code_le {j : ℕ} (hj : 1 ≤ j) (k m : ℕ) :
    codeBits (urnBool (massWeight j) k m) ≤ codeBits (bestFixed k m) + leafCharge j k m := by
  unfold leafCharge
  split_ifs with h
  · have hk : k = 0 := by omega
    have hm : m = 0 := by omega
    subst hk hm
    simp [urnBool_zero, bestFixed, codeBits]
  · rw [← add_assoc]
    exact priorMass_regret_bits (k := k) (m := m) hj (by omega)

/-- [definition] The arrivals of digit value `b` routed to node `s`. -/
def routedCount (obs : List (List Ltr × Bool)) (s : List Ltr) (b : Bool) : ℕ :=
  (routed obs s).count b

/-- [proved-derived; formal-checked] **`priorMass_tree_redundancy`: the tree's full redundancy at
prior mass `2^-j`.** For a binary landmark tree at rung `j ≥ 1` under **any** stop weights in
`[0, 1)` (the declared stop prior `w_d = 1 − 2^(−j_d)`, and forced depths at `0`), whose addresses
reach depth `D`, and **every** pruned tree `S` of depth at most `D` with positive prior: the code
the tree emits over the passage is at most `S`'s prior code plus, at each leaf `s`, the best fixed
digit probability's code of what reached `s` plus `½ log₂ n_s + j` (nothing at a leaf no arrival
reached):
`−log₂ ∏_t q_0(x_t) ≤ −log₂ prior_w(S) + Σ_(leaves s) [−log₂ (k_s/n_s)^(k_s) (m_s/n_s)^(m_s) + ½ log₂ n_s + j]`.
It composes `emitted_eq_weight` (the emitted code is the root weight), `own_dominance₀` (the root
weight dominates every pruned tree; `Tree.own_kraft_and_dominance` with forced depths), the
routed own weights (`obs_state_own_routed`, `massLaw_read`, `urnSeq_eq_urnBool`) and each leaf's
regret (`priorMass_regret_bits`). At `w = ½` the prior code is `Γ(S)`
(`PrunedTree.prior_half_bits`), and at `j = 1` it is CTW's bound with KT's `½ log₂ n + 1`. -/
theorem priorMass_tree_redundancy {j : ℕ} (hj : 1 ≤ j) {w : ℕ → ℚ} (hw : StopLaw₀ w) (D : ℕ)
    (obs : List (List Ltr × Bool)) (hD : ∀ o ∈ obs, D ≤ o.1.length) (S : PrunedTree Ltr D)
    (hS : 0 < PrunedTree.prior w D 0 S) :
    codeBits (emitted (massLaw j) w D obs) ≤
      codeBits (PrunedTree.prior w D 0 S) +
        leafSum (fun s => codeBits (bestFixed (routedCount obs s true) (routedCount obs s false)) +
          leafCharge j (routedCount obs s true) (routedCount obs s false)) D [] S := by
  set E := lawOwn (massLaw j) (obsStanding (massLaw j) obs) with hEdef
  have hE : ∀ s, 0 < E s := lawOwn_obs_pos _ obs
  have hEs : ∀ s, E s = urnBool (massWeight j) (routedCount obs s true)
      (routedCount obs s false) := fun s => by
    rw [hEdef, (obs_state_own_routed _ obs s).2, (massLaw_read j _).2,
      urnSeq_eq_urnBool (massWeight_pos j)]
    rfl
  rw [emitted_eq_weight _ hw D obs hD]
  have hdom := own_dominance₀ hw hE D [] S
  simp only [List.length_nil] at hdom
  have hpR : (0 : ℝ) < (PrunedTree.prior w D 0 S : ℝ) := by exact_mod_cast hS
  have hLR : (0 : ℝ) < (ownLik E D [] S : ℝ) := by exact_mod_cast ownLik_pos hE D [] S
  have hdR : ((PrunedTree.prior w D 0 S : ℚ) : ℝ) * (ownLik E D [] S : ℝ) ≤
      (ownWeight w E D [] : ℝ) := by exact_mod_cast hdom
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (mul_pos hpR hLR) hdR
  rw [Real.logb_mul hpR.ne' hLR.ne', logb_ownLik hE] at hlog
  have hleaf := leafSum_mono (f := fun s => -Real.logb 2 (E s : ℝ))
    (g := fun s => codeBits (bestFixed (routedCount obs s true) (routedCount obs s false)) +
      leafCharge j (routedCount obs s true) (routedCount obs s false))
    (fun s => by
      have := node_code_le hj (routedCount obs s true) (routedCount obs s false)
      rw [hEs s]
      exact this) D [] S
  rw [leafSum_neg] at hleaf
  unfold codeBits at hleaf ⊢
  linarith

/-- [proved-derived; formal-checked] **Against every binary tree source.** For every pruned tree
`S` with positive prior and every leaf parameter `θ_s ∈ (0, 1)`, the emitted code is at most the
tree source's code `−log₂ prior_w(S) − Σ_(leaves) log₂ θ_s^(k_s) (1 − θ_s)^(m_s)` plus the leaves'
charges `Σ_(leaves, n_s ≥ 1) (½ log₂ n_s + j)` (`fixed_le_bestFixed`). -/
theorem priorMass_tree_redundancy_source {j : ℕ} (hj : 1 ≤ j) {w : ℕ → ℚ} (hw : StopLaw₀ w)
    (D : ℕ) (obs : List (List Ltr × Bool)) (hD : ∀ o ∈ obs, D ≤ o.1.length)
    (S : PrunedTree Ltr D) (hS : 0 < PrunedTree.prior w D 0 S) (θ : List Ltr → ℝ)
    (hθ : ∀ s, 0 < θ s ∧ θ s < 1) :
    codeBits (emitted (massLaw j) w D obs) ≤
      codeBits (PrunedTree.prior w D 0 S) +
        leafSum (fun s => codeBits (θ s ^ routedCount obs s true *
            (1 - θ s) ^ routedCount obs s false) +
          leafCharge j (routedCount obs s true) (routedCount obs s false)) D [] S := by
  refine (priorMass_tree_redundancy hj hw D obs hD S hS).trans (add_le_add le_rfl ?_)
  refine leafSum_mono (fun s => ?_) D [] S
  obtain ⟨h0, h1⟩ := hθ s
  have hpos : 0 < θ s ^ routedCount obs s true * (1 - θ s) ^ routedCount obs s false := by
    have : 0 < 1 - θ s := by linarith
    positivity
  have hle := fixed_le_bestFixed h0.le h1.le (routedCount obs s true) (routedCount obs s false)
  have hl := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hle
  unfold codeBits
  linarith

/-- [proved-derived; formal-checked] **`tree_two_part`: choosing the tree's declaration is a
two-part code.** For `B` declarations `(j_i, w_i)` (a rung and stop weights in `[0, 1)`), a causal
context whose addresses reach depth `D`, and **any** choice `ĵ` of declaration, made on the
development cells or on the coded word itself, the lengths `log₂ B + code_ĵ` satisfy Kraft over the
words of every length: `Σ_v 2^(−(log₂ B + code_(ĵ v)(v))) ≤ 1` (`emitted_sum`, `two_part_kraft`).
The ladder `j = 1..8` at one stop law is `priorMass_tree_two_part`; the rung chosen jointly with a
stop prior from a family of `F` is `B = 8F`. -/
theorem tree_two_part {B : ℕ} (par : Fin B → ℕ × (ℕ → ℚ)) (hw : ∀ i, StopLaw₀ (par i).2)
    (ctx : List Bool → List Ltr) (D n : ℕ) (choice : (Fin n → Bool) → Fin B) :
    ∑ v : Fin n → Bool,
      (emitted (massLaw (par (choice v)).1) (par (choice v)).2 D
        (observations ctx (List.ofFn v)) : ℝ) / B ≤ 1 :=
  two_part_kraft (fun i (v : Fin n → Bool) =>
      (emitted (massLaw (par i).1) (par i).2 D (observations ctx (List.ofFn v)) : ℝ))
    (fun i v => by exact_mod_cast (emitted_pos _ (hw i) D _).le)
    (fun i => le_of_eq (by exact_mod_cast emitted_sum _ (hw i) ctx D n)) choice

/-- [proved-derived; formal-checked] **`priorMass_tree_two_part`: the tree's rung charged 3 bits.**
At one stop law and the ladder `j = 1..8`, the lengths `3 + code_ĵ` of one binary tree's emitted code
satisfy Kraft for any choice of rung: `Σ_v 2^(−(3 + code_(ĵ v)(v))) ≤ 1`. With
`priorMass_tree_redundancy`, the two-part code is at most
`3 + min_j [−log₂ prior_w(S) + Σ_(leaves) (−log₂ (k_s/n_s)^(k_s) (m_s/n_s)^(m_s) + ½ log₂ n_s + j)]`
when the rung is chosen to minimize it. -/
theorem priorMass_tree_two_part {w : ℕ → ℚ} (hw : StopLaw₀ w) (ctx : List Bool → List Ltr)
    (D n : ℕ) (choice : (Fin n → Bool) → Fin 8) :
    ∑ v : Fin n → Bool, (2 : ℝ) ^ (-(3 + codeBits
      (emitted (massLaw ((choice v : ℕ) + 1)) w D (observations ctx (List.ofFn v))))) ≤ 1 := by
  have hk := tree_two_part (B := 8) (fun i => ((i : ℕ) + 1, w)) (fun _ => hw) ctx D n choice
  refine le_of_eq_of_le (Finset.sum_congr rfl fun v _ => ?_) hk
  have hP : (0 : ℝ) < (emitted (massLaw ((choice v : ℕ) + 1)) w D
      (observations ctx (List.ofFn v)) : ℝ) := by exact_mod_cast emitted_pos _ hw D _
  rw [codeBits, neg_add, neg_neg, Real.rpow_add (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) hP, Real.rpow_neg (by norm_num)]
  norm_num
  ring

end Redundancy

/-! ### Raising the maximum depth -/

section Depth

variable {Ltr : Type*} [Fintype Ltr] [DecidableEq Ltr]

/-- [definition] **The stop at depth `k` below**: a leaf at a node with `k` levels below it (a stop
when `k ≥ 1`, the maximum depth when `k = 0`). -/
def PrunedTree.stopLeaf : (k : ℕ) → PrunedTree Ltr k
  | 0 => PUnit.unit
  | k + 1 => (none : Option (Ltr → PrunedTree Ltr k))

/-- [definition] **The lift of a pruned tree by `k` levels**: the same splits, each leaf at the old
maximum depth becoming a stop with `k` levels below it, so a pruned tree of depth at most `m` is one
of depth at most `k + m`. -/
def PrunedTree.lift (k : ℕ) : (m : ℕ) → PrunedTree Ltr m → PrunedTree Ltr (k + m)
  | 0, _ => PrunedTree.stopLeaf k
  | m + 1, S => Option.map (fun f b => PrunedTree.lift k m (f b))
      (S : Option (Ltr → PrunedTree Ltr m))

/-- [definition] **The leaves at the maximum depth** of a pruned tree: the leaves whose depth has no
stop/split decision coded. -/
def PrunedTree.deepLeaves : (m : ℕ) → PrunedTree Ltr m → ℕ
  | 0, _ => 1
  | m + 1, S => Option.elim (S : Option (Ltr → PrunedTree Ltr m)) 0
      fun f => ∑ b, PrunedTree.deepLeaves m (f b)

omit [DecidableEq Ltr] in
theorem PrunedTree.prior_stopLeaf (w : ℕ → ℚ) (d : ℕ) :
    ∀ k, PrunedTree.prior w k d (PrunedTree.stopLeaf k : PrunedTree Ltr k) = if k = 0 then 1 else w d
  | 0 => rfl
  | _ + 1 => rfl

omit [DecidableEq Ltr] in
/-- [proved-derived; formal-checked] **The lifted prior**: lifting a pruned tree by `k ≥ 1` levels
multiplies its prior by the stop weight at the old maximum depth once for each leaf there,
`prior_w(lift_k S) = prior_w(S) · w_(d+m)^(deepLeaves S)`; the splits and the stops above keep
their weights. -/
theorem PrunedTree.prior_lift (w : ℕ → ℚ) {k : ℕ} (hk : 1 ≤ k) :
    ∀ m d (S : PrunedTree Ltr m),
      PrunedTree.prior w (k + m) d (PrunedTree.lift k m S) =
        PrunedTree.prior w m d S * w (d + m) ^ PrunedTree.deepLeaves m S
  | 0, d, S => by
    show PrunedTree.prior w k d (PrunedTree.stopLeaf k) =
      PrunedTree.prior w 0 d S * w (d + 0) ^ PrunedTree.deepLeaves 0 S
    rw [PrunedTree.prior_stopLeaf, if_neg (by omega)]
    simp [PrunedTree.prior, PrunedTree.deepLeaves]
  | m + 1, d, S => by
    cases hS : (S : Option (Ltr → PrunedTree Ltr m)) with
    | none =>
      show w d = w d * w (d + (m + 1)) ^ 0
      ring
    | some f =>
      show (1 - w d) * ∏ b, PrunedTree.prior w (k + m) (d + 1) (PrunedTree.lift k m (f b)) =
        ((1 - w d) * ∏ b, PrunedTree.prior w m (d + 1) (f b)) *
          w (d + (m + 1)) ^ (∑ b, PrunedTree.deepLeaves m (f b))
      simp only [PrunedTree.prior_lift w hk m (d + 1), Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, show d + 1 + m = d + (m + 1) by omega]
      ring

omit [DecidableEq Ltr] in
theorem ownLik_stopLeaf (E : List Ltr → ℚ) (s : List Ltr) :
    ∀ k, ownLik E k s (PrunedTree.stopLeaf k : PrunedTree Ltr k) = E s
  | 0 => rfl
  | _ + 1 => rfl

omit [DecidableEq Ltr] in
/-- The lift keeps the leaves' own weights: each old maximum-depth leaf becomes a stop at the same
node. -/
theorem ownLik_lift (E : List Ltr → ℚ) (k : ℕ) :
    ∀ m s (S : PrunedTree Ltr m), ownLik E (k + m) s (PrunedTree.lift k m S) = ownLik E m s S
  | 0, s, _ => ownLik_stopLeaf E s k
  | m + 1, s, S => by
    cases hS : (S : Option (Ltr → PrunedTree Ltr m)) with
    | none => rfl
    | some f =>
      show ∏ b, ownLik E (k + m) (s ++ [b]) (PrunedTree.lift k m (f b)) =
        ∏ b, ownLik E m (s ++ [b]) (f b)
      simp only [ownLik_lift E k m]

omit [DecidableEq Ltr] in
theorem leafSum_stopLeaf (f : List Ltr → ℝ) (s : List Ltr) :
    ∀ k, leafSum f k s (PrunedTree.stopLeaf k : PrunedTree Ltr k) = f s
  | 0 => rfl
  | _ + 1 => rfl

omit [DecidableEq Ltr] in
/-- The lift keeps every sum over the leaves. -/
theorem leafSum_lift (f : List Ltr → ℝ) (k : ℕ) :
    ∀ m s (S : PrunedTree Ltr m), leafSum f (k + m) s (PrunedTree.lift k m S) = leafSum f m s S
  | 0, s, _ => leafSum_stopLeaf f s k
  | m + 1, s, S => by
    cases hS : (S : Option (Ltr → PrunedTree Ltr m)) with
    | none => rfl
    | some g =>
      show ∑ b, leafSum f (k + m) (s ++ [b]) (PrunedTree.lift k m (g b)) =
        ∑ b, leafSum f m (s ++ [b]) (g b)
      simp only [leafSum_lift f k m]

/-- [proved-derived; formal-checked] **`priorMass_depth_lift`: raising the maximum depth costs one
stop code a deep leaf.** Raise the tree's maximum depth from `D` to `D' = k + D` (`k ≥ 1`, the
addresses reaching `D'`). Against every pruned tree `S` of depth at most `D` with positive prior,
the bound of `priorMass_tree_redundancy` at `D'` is the bound at `D` plus `−log₂ w_D` for each leaf
of `S` at the old maximum depth `D`, and nothing else: the prior code of `S`'s splits and stops
above `D`, the leaves' best fixed codes and their charges `½ log₂ n_s + j` are unchanged (each
leaf's routed counts depend only on its own address prefix). The deeper tree is also compared
with every pruned tree of depth up to `D'`. -/
theorem priorMass_depth_lift {j : ℕ} (hj : 1 ≤ j) {w : ℕ → ℚ} (hw : StopLaw₀ w) (hwD : ∀ D, 0 < w D)
    {k : ℕ} (hk : 1 ≤ k) (D : ℕ) (obs : List (List Ltr × Bool))
    (hD : ∀ o ∈ obs, k + D ≤ o.1.length) (S : PrunedTree Ltr D)
    (hS : 0 < PrunedTree.prior w D 0 S) :
    codeBits (emitted (massLaw j) w (k + D) obs) ≤
      codeBits (PrunedTree.prior w D 0 S) + PrunedTree.deepLeaves D S * codeBits (w D) +
        leafSum (fun s => codeBits (bestFixed (routedCount obs s true) (routedCount obs s false)) +
          leafCharge j (routedCount obs s true) (routedCount obs s false)) D [] S := by
  have hP := PrunedTree.prior_lift w hk D 0 S
  rw [zero_add] at hP
  have hwD' := hwD D
  have hS' : 0 < PrunedTree.prior w (k + D) 0 (PrunedTree.lift k D S) := by
    rw [hP]; positivity
  have h := priorMass_tree_redundancy hj hw (k + D) obs hD _ hS'
  rw [leafSum_lift, hP] at h
  refine h.trans (le_of_eq ?_)
  have hpR : (0 : ℝ) < (PrunedTree.prior w D 0 S : ℝ) := by exact_mod_cast hS
  have hwR : (0 : ℝ) < (w D : ℝ) := by exact_mod_cast hwD'
  unfold codeBits
  push_cast
  rw [Real.logb_mul hpR.ne' (by positivity), Real.logb_pow]
  ring

/-- [proved-derived; formal-checked] **The stop code on the dyadic ladder**: at rung `j ≥ 1` the
stop weight `w = 1 − 2^(−j)` codes in `−log₂ w = j − log₂(2^j − 1)` bits, at most one bit (exactly
one at `j = 1`, `log₂(8/7)` at `j = 3`). -/
theorem ladder_stop_bits {j : ℕ} (hj : 1 ≤ j) :
    codeBits (ladder j) = j - Real.logb 2 (2 ^ j - 1) ∧ codeBits (ladder j) ≤ 1 := by
  have h2 : (2 : ℝ) ≤ 2 ^ j := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have hl : ((ladder j : ℚ) : ℝ) = (2 ^ j - 1) / 2 ^ j := by
    unfold ladder; push_cast
    rw [one_div_pow]
    field_simp
  have hpos : (0 : ℝ) < 2 ^ j - 1 := by linarith
  have e : codeBits (ladder j) = j - Real.logb 2 (2 ^ j - 1) := by
    rw [codeBits, hl, Real.logb_div hpos.ne' (by positivity), Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    ring
  refine ⟨e, ?_⟩
  rw [e]
  have : Real.logb 2 (2 ^ (j - 1 : ℕ)) ≤ Real.logb 2 (2 ^ j - 1) := by
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    have : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]
    have : (1 : ℝ) ≤ 2 ^ (j - 1) := one_le_pow₀ (by norm_num)
    linarith
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), Nat.cast_sub hj] at this
  push_cast at this
  linarith

/-- [proved-derived; formal-checked] **The depth's cost on the Rust's stop prior.** With the declared
stop prior on the dyadic ladder, `w_d = 1 − 2^(−j_d)` (Rust `StopPrior::weight`, rungs `j_d ≥ 1`
read at each depth, the last rung past the list), raising the declared depth from `D` to `D' = k + D`
costs, against every pruned tree `S` of depth at most `D`, `deepLeaves(S) · (j_D − log₂(2^(j_D) − 1))`
bits, at most one bit per leaf of `S` at depth `D` (`log₂(8/7)` each at `j_D = 3`). -/
theorem priorMass_depth_lift_ladder {j : ℕ} (hj : 1 ≤ j) (rung : ℕ → ℕ) (hr : ∀ d, 1 ≤ rung d)
    {k : ℕ} (hk : 1 ≤ k) (D : ℕ) (obs : List (List Ltr × Bool))
    (hD : ∀ o ∈ obs, k + D ≤ o.1.length) (S : PrunedTree Ltr D) :
    codeBits (emitted (massLaw j) (fun d => ladder (rung d)) (k + D) obs) ≤
      codeBits (PrunedTree.prior (fun d => ladder (rung d)) D 0 S) +
        PrunedTree.deepLeaves D S * (rung D - Real.logb 2 (2 ^ rung D - 1)) +
        leafSum (fun s => codeBits (bestFixed (routedCount obs s true) (routedCount obs s false)) +
          leafCharge j (routedCount obs s true) (routedCount obs s false)) D [] S := by
  have hwD : ∀ d, 0 < ladder (rung d) := fun d => (ladder_founding (hr d)).1
  have hw : StopLaw (fun d => ladder (rung d)) := fun d =>
    ⟨(ladder_founding (hr d)).1, (ladder_founding (hr d)).2.1⟩
  have h := priorMass_depth_lift hj hw.toStopLaw₀ hwD hk D obs hD S
    (PrunedTree.prior_pos hw D 0 S)
  rwa [(ladder_stop_bits (hr D)).1] at h

end Depth

/-! ### Audit -/

section Audit

#print axioms priorMass_face
#print axioms urnSeq_eq_urnBool
#print axioms massLaw_read
#print axioms urnSeq_sum
#print axioms kt_face_le
#print axioms kt_diag
#print axioms priorMass_ge_kt
#print axioms priorMass_code_le_kt
#print axioms priorMass_one_sided_ge_kt
#print axioms priorMass_one_sided
#print axioms priorMass_one_sided_two_bits
#print axioms sixteen_pow_le_centralBinom_sq
#print axioms ascPochhammer_eval_half
#print axioms fixed_le_bestFixed
#print axioms kt_regret
#print axioms priorMass_regret
#print axioms priorMass_regret_bits
#print axioms priorMass_regret_fixed
#print axioms two_part_kraft
#print axioms priorMass_two_part
#print axioms priorMass_face_ge
#print axioms priorMass_digit_face_ge
#print axioms emitted_eq_weight
#print axioms emitted_sum
#print axioms own_dominance₀
#print axioms priorMass_tree_redundancy
#print axioms priorMass_tree_redundancy_source
#print axioms tree_two_part
#print axioms priorMass_tree_two_part
#print axioms PrunedTree.prior_lift
#print axioms priorMass_depth_lift
#print axioms ladder_stop_bits
#print axioms priorMass_depth_lift_ladder

end Audit

end Holonics.Compression.Landmark.Context.PriorMass
