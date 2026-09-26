import Holonics.HNN.RegionCounts
import Holonics.Aeon.Production.FirstLaw
import Holonics.Foundation.FractalPacking
import Holonics.Compression.Core.Cost
import Holonics.Foundation.Standing

/-!
# HNN.LandmarkTree: the receiving parametron's storage as a tree of landmarks

[definition; agent-inferred] Decision 28 of the step 4 design (`docs/plans/THE_REBUILD.md`), from
Brandon's direction and Sol's derivation (`research/records/2026-09-25_THE_COMPRESSION_IS_OF_
LANDMARKS_A_TREE_COCYCLE_AND_MERGES_PRICED_BY_THEIR_CODE_LENGTH_PAIR.md`). The computational object
is the helical pair interaction; this owner is the receiving parametron's storage read as a tree of
landmarks. Its nodes are typed address words (the preceding cells, newest first; later, declared
phase classes and key-located configurations), each holding Krichevsky–Trofimov masses (α = 1/2,
one per two) and founded at first arrival. The face is the context-tree weighting
(Willems–Shtarkov–Tjalkens) along the one path the current address opens. Of the winding guide's
six general objects it touches three: faces and placement (the receiving face), the tower thread
(the suffix restriction is a transverse scale restriction, and a cell's odometer digits descend its
dyadic cell, `Foundation/FractalPacking.descend`), and the pair (each edge compares a node's face
with its child's as a ratio). A tree has no two-cells: its path cochain is exact, and no cell
holonomy is claimed.

```text
address    a = [x_(j−1), …, x_(j−D)] newest first ;  node at depth d: a.take d ;  restriction: take
KT         E_s = ∏_c ∏_(j<n_c) (j + 1/2) / ∏_(j<n) (j + |A|/2) ;   k_s(c) = (n_c + 1/2)/(n + |A|/2)
mixture    W_s = E_s at depth D ;   W_s = (E_s + P_s)/2 ,  P_s = ∏_b W_(s b)
path face  q_D = k_D ;   q_d = λ_d k_d + (1 − λ_d) q_(d+1) ,   λ_d = E_d/(E_d + P_d) = β_d/(1 + β_d)
step       W'_d = W_d q_d(c) ,  E'_d = E_d k_d(c) ,  P'_d = P_d q_(d+1)(c) ,
           β'_d = β_d k_d(c)/q_(d+1)(c)
trees      W_s = Σ_S 2^(−Γ(S)) ∏_(leaves ℓ of S) E_(s ℓ) ,   Σ_S 2^(−Γ(S)) = 1
cochain    q_0 = q_D ∏_(d<D) q_d/q_(d+1) ;
           −log₂ q_0 = −log₂ q_D + Σ_(d<D) log₂ R_d ,  R_d = q_(d+1)/q_d
digits     q(c) = ∏_(i<w) q(prefix_i c, bit_i c) ;   q̂(0) = clamp_[1, 2^M − 1](round(2^M q(0)))/2^M
lattice    q̂_D = ⟦k_D⟧ ;  q̂_d = ⟦λ̂_d k_d + (1 − λ̂_d) q̂_(d+1)⟧ ;  β'_d = β_d k_d(c)/q̂_(d+1)(c) (1 − r)
```

The standing is the count table at every node (`TreeStanding`): no occurrence list is retained.
The routed subsequences appear only in the proof that each node's KT mass is the sequential KT
likelihood of what reached it (`standing_is_routed_counts`).

[proved-derived; formal-checked] What is proved.

1. **Address and scale square** (`address_scale_square`, `digit_context_square`,
   `digit_emission_descends`): restriction is `take`, composing by `min`; the opened path has
   `D + 1` nodes, each child its parent plus one older letter. At the emission of a digit, the
   digit-prefix restriction (fine, within the emitted cell) and the context restriction (coarse,
   across cells) commute as restrictions of the joint address; the digit prefix's dyadic cell
   (`FractalPacking.descend` of its hand word) contains the finer prefix's; the odometer digits
   `toBits w c` of a cell `c < 2^w` return `c` (`ofBits`), and each digit descends one level.
2. **Krichevsky–Trofimov** (`kt_likelihood_laws`, `ktMass_bump`): the sequential KT likelihood is
   positive, consistent (`Σ_c KT(w ++ [c]) = KT(w)`), its conditional is the likelihood ratio
   `RegionCounts.ktProb` (Decision 27's region face), it is exchangeable (the counts are the whole
   standing), and it is the unique law with that sequential step.
3. **The opened-path face** (`path_face_normalized`, `path_face_ge_min`, `pathFace_const`): for
   positive normalized node faces and **any** `λ_d ∈ [0,1]` (the exact weights or a lattice
   chart's), the path face is positive and normalized, and at least the minimum of the path's faces.
4. **The mixture and its step** (`weight_step`, `landmark_step`, `lamAt_eq_beta`,
   `treeWeight_arrive_off`): an arrival multiplies each opened node's weight by the path face there,
   `W'_d = W_d q_d(c)` (the conditional prediction is the successive likelihood ratio), moves
   `E' = E k`, `P' = P q_(d+1)` and `β' = β k/q_(d+1)`, and changes nothing off the path. **Over a
   stream with a causal context** (`mixture_is_probability`, `standing_is_routed_counts`), the root
   weight is a probability law on the words of every length, and each node's mass is the KT
   likelihood of its routed subsequence. **The Kraft form** (`mixture_over_trees`,
   `kraft_and_dominance`): the weight is the mixture over pruned trees with weights `2^(−Γ(S))`,
   these weights sum to one, and `−log₂ W ≤ Γ(S) − log₂ ∏ E` for every pruned tree.
5. **Depth one is Decision 27** (`depth_one_is_decision_27`): at depth one with the forced split
   `λ_0 = 0`, the face is `RegionCounts.countFace` of the KT masses the region word deposits at the
   preceding cell (`regionRun_local`, `count_face_eq_kt`); ordinary CTW at depth one mixes in the
   root face with `0 < λ_0 < 1`. This is the whole-cell emission (`|A|`-ary masses at a node),
   whose law lives here only; the digit emission's depth-one forced case (section 6) is a product
   over the cell's opened digits of binary KT faces at the preceding cell, not this `|A|`-ary face.
6. **The digit emission** (`digit_emission_normalized`, `forced_digits_normalized`,
   `face_cell_width`, `cell_faces_partition`): the product of binary faces normalized at every digit
   prefix sums to one over the cells `c < 2^w`, and over `K < 2^w` classes when the digits whose
   upper half holds no class are forced; the cell's face is the width of its descended interval
   (`splitChild`, abutting children; `FractalPacking.descend`'s children are fixed thirds with a gap
   and do not admit unequal splits). **The executed split** (`executed_split_laws`): the rounded,
   clamped `q̂(0)` on the lattice `2^(−M)ℤ` and `q̂(1) = 1 − q̂(0)` are positive and normalized at
   `M ≥ 1`, within `2^(−M−1)` of the exact faces when `q(0) ∈ [2^(−M), 1 − 2^(−M)]`. **The floor
   and the residual** (`kt_binary_ge`, `digit_face_ge`, `digit_log_residual`,
   `digit_log_residual_kt`): a binary KT face after `n` observations is at least `1/(2n + 2)`, so is
   the digit face whose path nodes hold at most `n`; for `q ≥ μ` and `|q̂ − q| ≤ ε < μ`,
   `|ln q̂ − ln q| ≤ ε/(μ − ε)`, upward at most `ε/μ`; at `μ = 1/(2n + 2)`, `ε = 2^(−M−1)` and
   `2n + 2 ≤ 2^M`, the residual is at most `(2n + 2)/2^M` per digit in `ln` (divide by `ln 2` for
   `log₂`), upward at most `(2n + 2)/2^(M+1)`.
7. **The cochain and the local autogradient** (`path_cochain`, `path_telescope_exact`,
   `tree_telescope`, `edge_log_derivative`): the edge log ratios are an additive exact cochain
   (segments sum to endpoint differences and concatenate by addition); the root face is the deepest
   node's KT face times the path's ratios, exactly in `ℚ`; `d log R = R⁻¹ dR` on each edge, and the
   path's log-derivatives telescope.
8. **The deposition join** (`deposition_is_log_ratio`, `concentrated_deposition`,
   `tree_deposit_is_deposition`): when a deposit moves the tree's root face `q → q'` at a fixed
   arrived source `p'`, the change of the scored code length is the first law's **deposition** term
   `−Σ p' log(q'/q) = C(p', q') − C(p', q)` (`Aeon/Production/FirstLaw`); for a concentrated arrival
   it is `−log(q'(t)/q(t))`, proved directly. The cochain supplies the deposition term, not the
   exchange term.
9. **Founding and release** (`unfounded_reads_prior`, `founding_step`, `founded_tree_same_law`,
   `release_rule`): an unfounded node reads as the prior (`E = P = W = β = 1`, the uniform face),
   and a node founded by an arrival keeps `β = 1`, so the tree founded at first arrival is the same
   law as the materialized tree. Replacing a tree standing preserves every admitted future face
   exactly when the causal signatures agree (`Foundation/Standing`), a retention is lawful exactly
   when it refines the signature, and nodes deeper than the admitted depth are releasable.
10. **The lattice chart** (`lattice_path_laws`, `lattice_path_floor`, `lattice_path_deviation`,
    `mix_ratio_bound`, `weight_log_lipschitz`, `lattice_step_telescope`, `lattice_node_telescope`,
    `rebase_log_residual`; section 6′): the executed path rounds every level to `2^(−M)ℤ`
    (`latticeFrom`); for any stop weights its faces are lattice points in `[2^(−M), 1 − 2^(−M)]`, the
    digit's split is positive and normalized and the cells' executed faces partition the unit cell;
    the faces never fall below the lattice floor of the KT floor; the absolute deviation from the
    exact path adds down the path, `(m + 1) 2^(−M−1) + Σ|λ̂ − λ|`; in logarithms the mixture moves by
    at most the drift of `β` plus the child's, and the node weight by at most its split mass's; one
    executed step is the weight's ratio times a rebase factor `γ ∈ [1 − r, 1]` with
    `β' = β k/q̂' · (1 − r)`, and a node's passage telescopes to the weight's ratio times those
    factors; a rebase's residual is `ln(x/⌊x⌋) < 1/⌊x⌋`, and `|log₂(1 − r)| < 2^(3−W)` for
    `r < 2^(1−W)`.

11. **The receiver's mixture of two faces** (`sequential_mixture`, `sequential_mixture_bounds`,
    `sequential_mixture_executed`; section 10): for positive faces `a_t`, `b_t` of the targets with
    `A_t = ∏_(s<t) a_s`, `B_t = ∏_(s<t) b_s`, the mixture `q_t = λ_t a_t + (1 − λ_t) b_t` with
    `λ_t = A_t/(A_t + B_t) = β_t/(1 + β_t)` (`β_0 = 1`, `β_(t+1) = β_t a_t/b_t`, stepped after every
    cell) telescopes, `∏_(t<n) q_t = ½ A_n + ½ B_n`, so
    `min(−log₂ A, −log₂ B) ≤ −log₂ ∏ q ≤ min(−log₂ A, −log₂ B) + 1`. With the ratio carried by a
    chart whose step at cell `t` carries a factor `ρ_t > 0`, `A_n ≤ 2 ∏ max(1, ρ_t) ∏ q̂_t` and
    `B_n ≤ 2 ∏ max(1, 1/ρ_t) ∏ q̂_t`, so the executed code length is within
    `min + 1 + Σ_t |log₂ ρ_t|`: the chart's drift adds once over the passage.

[counterexample; formal-checked]
* `budget_eviction_changes_face`: evicting an occupied child by budget alone changes a later face
  (`3/4` against `7/12`), so no lawful retention identifies the two standings: a storage budget
  alone gives no exact eviction rule.
* `host_digit_bound_fails_downward`: the per-digit bound `2^(−M−1)(2n + 2)` (in `ln`; times `log₂ e`
  in `log₂`) is not a bound when rounding moves the face down: at `M = 7`, `n = 42`, `q = 1/86`,
  `q̂ = 1/128`, `ln q − ln q̂ = ln(64/43) > 43/128`. It holds upward; the downward bound needs
  `ε/(μ − ε)`, at most twice it when `2n + 2 ≤ 2^M`.

[proved-standard] The recursive mixture and its model mixture are Willems, Shtarkov and Tjalkens
(1995); the α = 1/2 estimator is Krichevsky and Trofimov (1981). The proofs here are this owner's.

[conditional] CTW's redundancy bound against the best binary tree source adds to `Γ(S)` each
leaf's KT parameter cost, `|S| γ(N/|S|)` with `γ(z) = ½ log₂ z + 1`; it holds for binary tree
sources and does not transfer unchanged to whole-cell alphabets or phase-conditioned addresses.
Calling a node a landmark in the elementary objects' sense also needs its receiver face to certify
that navigator paths converge there; a shared spelling alone does not. `d log R` is a natural
gradient only once a metric is supplied.

[open] Owed in #62 ("Step 4 (#73) owed"): the KT parameter redundancy
`−log₂ KT(x) ≤ −log₂ P_θ(x) + ½ log₂ n + 1` (binary), which with `kraft_and_dominance` gives CTW's
full bound. **The lattice chart's passage-level drift** (#62, "the landmark lattice's drift"): the
composition over the tree and the passage of `lattice_node_telescope`, `weight_log_lipschitz` and
`mix_ratio_bound` into `|ln β̂_s − ln β_s| ≤ Σ_(subtree)(θ + 2|ln(1 − r)|) + Σ_s |ln(1 − r)|` and the
per-cell rule `(3/2) B [(n* D² + 2D + 1) 2^(−M−1)/μ̂ + n* D² 2^(1−W)]` (Rust `landmark::face_bits`,
`carrier_width`, `Landmarks::face_rule`), and **the certified binary logarithm's squaring
invariant** (Rust `landmark::binary_log`); both are checked by the Rust tests. The finite-cut orderings (the count-only tree below online order-0, order-1 and PPM-2
on the standing real cut) are measurement receipts, not theorems. The campaign 5 merge laws are not
stated here: they have no consumer yet.

The Rust consumer is `crates/holonics/src/hnn/landmark.rs` (`hnn::landmark`, written beside this
owner): `Landmarks` (the tree executed on the lattice: its all-class face `Landmarks::face`, a
window's faces in cell order `Landmarks::window_faces`, `probability`, `score`, its deposit
`Landmarks::deposit` and `receive`, the certificates),
`IdealLandmarks` (the ideal tree weighting in ℚ, the reference oracle), `Beta` (the carried β chart),
`OpenedPath::edge_ratios` (the cochain) and `face_bits`, `carrier_width` (the derived widths). Section 10's
consumer is `hnn::receiving::Mixture` (the receiver's scored face, its ratio stepped phase by phase
across a window).

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.LandmarkTree

open Holonics.HNN.RegionCounts (ktProb ktPrior countFace countRun targetWord regionRun)
open Holonics.Foundation.FractalPacking (Hand Cell descend root child)
open Holonics.Compression.Core.Cost (toBits ofBits toBits_length ofBits_toBits)

/-! ## 1. Addresses: restriction, the opened path and the scale square -/

section Address

variable {Ltr : Type*}

/-- [definition] **The restriction of an address word to depth `d`.** Address words are newest
letter first; the node at depth `d` keeps the `d` newest letters, and its parent drops the oldest
of them. -/
def restrict (d : ℕ) (a : List Ltr) : List Ltr := a.take d

/-- [definition] **The opened path** of an address: its nodes at depths `0, 1, …, D`, from the root
to the deepest node the address reaches. -/
def openedPath (D : ℕ) (a : List Ltr) : List (List Ltr) :=
  (List.range (D + 1)).map fun d => restrict d a

theorem restrict_restrict (d e : ℕ) (a : List Ltr) :
    restrict d (restrict e a) = restrict (min d e) a := List.take_take

theorem restrict_length {d : ℕ} {a : List Ltr} (h : d ≤ a.length) : (restrict d a).length = d := by
  simp [restrict, h]

theorem restrict_succ {d : ℕ} {a : List Ltr} (h : d < a.length) :
    restrict (d + 1) a = restrict d a ++ [a[d]] := by
  unfold restrict
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  rfl

/-- [proved-derived; formal-checked] **The scale square of the address.** Restriction composes:
restricting to depth `e` and then to `d` is restricting to `min d e`; so a coarser restriction of a
finer node is the coarser node, and the opened path has `D + 1` nodes, the node at depth `d + 1`
restricting to the node at depth `d` by dropping one letter. -/
theorem address_scale_square (a : List Ltr) (D : ℕ) :
    (∀ d e, restrict d (restrict e a) = restrict (min d e) a) ∧
      (∀ d e, d ≤ e → restrict d (restrict e a) = restrict d a) ∧
      (openedPath D a).length = D + 1 ∧
      (∀ s, s ∈ openedPath D a ↔ ∃ d ≤ D, restrict d a = s) ∧
      ∀ d (h : d < a.length), restrict (d + 1) a = restrict d a ++ [a[d]] := by
  refine ⟨fun d e => restrict_restrict d e a,
    fun d e h => by rw [restrict_restrict, min_eq_left h],
    by simp [openedPath], fun s => ?_, fun d h => restrict_succ h⟩
  · simp only [openedPath, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨d, hd, rfl⟩; exact ⟨d, by omega, rfl⟩
    · rintro ⟨d, hd, rfl⟩; exact ⟨d, by omega, rfl⟩

/-- [definition] The hand of one binary odometer digit: `0` restricts to the left child, `1` to the
right (`Foundation/FractalPacking.Hand`). -/
def handOf (b : Bool) : Hand := if b then Hand.right else Hand.left

/-- [definition] **The restriction word of a digit prefix**, newest digit first: FractalPacking's
address convention (the head is the newest restriction). -/
def digitWord (π : List Bool) : List Hand := (π.map handOf).reverse

/-- [definition] **The dyadic cell of a digit prefix**: the unit cell descended along the prefix's
restriction word (`FractalPacking.descend`). -/
def digitCell (π : List Bool) : Cell := descend (digitWord π) root

theorem descend_append (u v : List Hand) (cell : Cell) :
    descend (u ++ v) cell = descend u (descend v cell) := by
  induction u with
  | nil => rfl
  | cons h u ih => simp [descend, ih]

theorem digitCell_snoc (π : List Bool) (b : Bool) :
    digitCell (π ++ [b]) = child (handOf b) (digitCell π) := by
  simp [digitCell, digitWord, descend]

theorem digitWord_append (π ρ : List Bool) : digitWord (π ++ ρ) = digitWord ρ ++ digitWord π := by
  simp [digitWord]

/-- [definition] **The joint address** at the emission of one digit: the digit prefix already
emitted within the current cell (the fine restriction, inside the emitted cell) and the context
word of preceding cells, newest first (the coarse restriction, across cells). -/
structure JointAddress (Ltr : Type*) where
  /-- The emitted digit prefix of the current cell, most significant digit first. -/
  digits : List Bool
  /-- The preceding cells, newest first. -/
  context : List Ltr

/-- [definition] The fine restriction: keep the first `i` digits of the emitted prefix. -/
def JointAddress.fine (i : ℕ) (x : JointAddress Ltr) : JointAddress Ltr :=
  ⟨x.digits.take i, x.context⟩

/-- [definition] The coarse restriction: keep the `d` newest preceding cells. -/
def JointAddress.coarse (d : ℕ) (x : JointAddress Ltr) : JointAddress Ltr :=
  ⟨x.digits, restrict d x.context⟩

/-- [proved-derived; formal-checked] **The digit and context restrictions form a scale square.**
For the joint address of an emitted digit:
* the fine (digit-prefix) and coarse (context) restrictions commute;
* each composes with itself by `min`, so any two orders of restriction meet at one joint address;
* the digit prefix's dyadic cell contains the finer prefix's cell: the fine restriction is a
  containment of `FractalPacking` cells, and each emitted digit descends one level,
  `cell(π ++ [b]) = child(hand b, cell π)`.

The digit of a cell `c < 2^w` is its odometer digit `toBits w c` (`Compression/Core/Cost`), which
`ofBits` inverts. -/
theorem digit_context_square (x : JointAddress Ltr) (i d : ℕ) :
    (x.coarse d).fine i = (x.fine i).coarse d ∧
      (∀ i' d', ((((x.fine i).coarse d).fine i').coarse d') =
        (x.fine (min i' i)).coarse (min d' d)) ∧
      (digitCell (x.fine i).digits).Contains (digitCell x.digits) ∧
      (∀ b, digitCell (x.digits ++ [b]) = child (handOf b) (digitCell x.digits)) := by
  refine ⟨rfl, fun i' d' => ?_, ?_, digitCell_snoc x.digits⟩
  · simp only [JointAddress.fine, JointAddress.coarse, List.take_take, restrict_restrict]
  · have hsplit : x.digits = x.digits.take i ++ x.digits.drop i := (List.take_append_drop i _).symm
    have hcell : digitCell x.digits =
        descend (digitWord (x.digits.drop i)) (digitCell (x.digits.take i)) := by
      conv_lhs => rw [hsplit]
      rw [digitCell, digitWord_append, descend_append]
      rfl
    rw [hcell]
    exact Holonics.Foundation.FractalPacking.contains_descend _
      (Holonics.Foundation.FractalPacking.descend_positive _
        Holonics.Foundation.FractalPacking.root_positive)

/-- [proved-derived; formal-checked] **The odometer digits of a cell descend its dyadic cell.** For
a cell `c < 2^w`, its `w` digits `toBits w c` return `c` (`ofBits`), the cell of the full digit
word has width `3^(−w)` (FractalPacking's scale), and the prefix of length `i + 1` descends the
prefix of length `i` by the hand of digit `i`. -/
theorem digit_emission_descends {w c : ℕ} (hc : c < 2 ^ w) :
    ofBits (toBits w c) = c ∧ (digitCell (toBits w c)).width = (1 / 3 : ℚ) ^ w ∧
      ∀ i (hi : i < w), digitCell ((toBits w c).take (i + 1)) =
        child (handOf ((toBits w c)[i]'(by rw [toBits_length]; exact hi)))
          (digitCell ((toBits w c).take i)) := by
  refine ⟨by rw [ofBits_toBits, Nat.mod_eq_of_lt hc], ?_, fun i hi => ?_⟩
  · rw [digitCell, Holonics.Foundation.FractalPacking.root_descend_width]
    simp [digitWord, toBits_length]
  · rw [List.take_add_one, List.getElem?_eq_getElem (by rw [toBits_length]; exact hi)]
    exact digitCell_snoc _ _

end Address

/-! ## 2. Krichevsky–Trofimov masses and the sequential likelihood -/

section KT

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- [definition] **The Krichevsky–Trofimov mass of a count table** `n`:
`∏_c ∏_(j<n_c) (j + 1/2) / ∏_(j<Σn) (j + |A|/2)`, the α = 1/2 (one per two) Dirichlet mixture
likelihood of any word with those counts. -/
def ktMass (n : A → ℕ) : ℚ :=
  (∏ c, ∏ j ∈ Finset.range (n c), ((j : ℚ) + 1 / 2)) /
    ∏ j ∈ Finset.range (∑ c, n c), ((j : ℚ) + Fintype.card A / 2)

/-- [definition] **The KT face of a count table**: `k(c) = (n_c + 1/2)/(Σn + |A|/2)`
(`RegionCounts.ktProb`). -/
def ktFace (n : A → ℕ) (c : A) : ℚ := ktProb (n c) (∑ c, n c) (Fintype.card A)

/-- [definition] One arrival of class `c` added to a count table. -/
def bump (n : A → ℕ) (c : A) : A → ℕ := fun c' => n c' + if c' = c then 1 else 0

/-- [definition] The count table of a word. -/
def counts (w : List A) : A → ℕ := fun c => w.count c

/-- [definition] **The sequential KT likelihood** of a word: the KT mass of its counts. -/
def ktSeq (w : List A) : ℚ := ktMass (counts w)

theorem sum_bump (n : A → ℕ) (c : A) : ∑ c', bump n c c' = ∑ c', n c' + 1 := by
  simp [bump, Finset.sum_add_distrib]

theorem sum_counts (w : List A) : ∑ c, counts w c = w.length := by
  induction w with
  | nil => simp [counts]
  | cons x w ih =>
    simp only [counts, List.count_cons, Finset.sum_add_distrib, List.length_cons] at ih ⊢
    rw [ih]
    simp [beq_iff_eq]

omit [Fintype A] in
theorem counts_snoc (w : List A) (c : A) : counts (w ++ [c]) = bump (counts w) c := by
  funext c'
  simp only [counts, bump, List.count_append, List.count_singleton, beq_iff_eq]
  by_cases h : c' = c
  · subst h; simp
  · simp [h, Ne.symm h]

omit [DecidableEq A] in
theorem ktMass_zero : ktMass (fun _ : A => 0) = 1 := by
  simp [ktMass]

omit [DecidableEq A] in
theorem ktMass_pos [Nonempty A] (n : A → ℕ) : 0 < ktMass n := by
  have hk : (0 : ℚ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  apply div_pos
  · exact Finset.prod_pos fun c _ => Finset.prod_pos fun j _ => by positivity
  · exact Finset.prod_pos fun j _ => by positivity

omit [DecidableEq A] in
theorem ktFace_pos [Nonempty A] (n : A → ℕ) (c : A) : 0 < ktFace n c := by
  have hk : (0 : ℚ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  unfold ktFace ktProb
  positivity

omit [DecidableEq A] in
theorem ktFace_sum [Nonempty A] (n : A → ℕ) : ∑ c, ktFace n c = 1 := by
  have hk : (0 : ℚ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  unfold ktFace ktProb
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  rw [div_eq_one_iff_eq (by positivity)]
  ring

omit [DecidableEq A] in
/-- The KT face of the empty count table is uniform, `1/|A|`. -/
theorem ktFace_zero [Nonempty A] (c : A) : ktFace (fun _ : A => 0) c = 1 / Fintype.card A := by
  have hk : (0 : ℚ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  simp only [ktFace, ktProb, Finset.sum_const_zero, CharP.cast_eq_zero, zero_add]
  field_simp

/-- [proved-derived; formal-checked] **One arrival multiplies the KT mass by the KT face**:
`KT(n + e_c) = KT(n)·(n_c + 1/2)/(Σn + |A|/2)`. -/
theorem ktMass_bump [Nonempty A] (n : A → ℕ) (c : A) :
    ktMass (bump n c) = ktMass n * ktFace n c := by
  have hk : (0 : ℚ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hnum : ∏ c', ∏ j ∈ Finset.range (bump n c c'), ((j : ℚ) + 1 / 2) =
      (∏ c', ∏ j ∈ Finset.range (n c'), ((j : ℚ) + 1 / 2)) * ((n c : ℚ) + 1 / 2) := by
    have : ∀ c', ∏ j ∈ Finset.range (bump n c c'), ((j : ℚ) + 1 / 2) =
        (∏ j ∈ Finset.range (n c'), ((j : ℚ) + 1 / 2)) *
          (if c' = c then ((n c' : ℚ) + 1 / 2) else 1) := by
      intro c'
      by_cases h : c' = c
      · simp [bump, h, Finset.prod_range_succ]
      · simp [bump, h]
    rw [Finset.prod_congr rfl fun c' _ => this c', Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  have hden : ∏ j ∈ Finset.range (∑ c', bump n c c'), ((j : ℚ) + Fintype.card A / 2) =
      (∏ j ∈ Finset.range (∑ c', n c'), ((j : ℚ) + Fintype.card A / 2)) *
        (((∑ c', n c' : ℕ) : ℚ) + Fintype.card A / 2) := by
    rw [sum_bump, Finset.prod_range_succ]
  have hD : 0 < ∏ j ∈ Finset.range (∑ c', n c'), ((j : ℚ) + Fintype.card A / 2) :=
    Finset.prod_pos fun j _ => by positivity
  have hD' : (0 : ℚ) < ((∑ c', n c' : ℕ) : ℚ) + Fintype.card A / 2 := by positivity
  rw [ktMass, hnum, hden, ktMass, ktFace, ktProb, mul_div_mul_comm]

omit [Fintype A] in
theorem counts_nil : counts ([] : List A) = fun _ => 0 := by
  funext c; simp [counts]

theorem ktSeq_nil : ktSeq ([] : List A) = 1 := by
  rw [ktSeq, counts_nil, ktMass_zero]

/-- [proved-derived; formal-checked] **The sequential step**: appending the class `c` to a word
multiplies its KT likelihood by KT's conditional probability of `c` after that word. -/
theorem ktSeq_snoc [Nonempty A] (w : List A) (c : A) :
    ktSeq (w ++ [c]) = ktSeq w * ktProb (w.count c) w.length (Fintype.card A) := by
  rw [ktSeq, counts_snoc, ktMass_bump, ktFace, sum_counts]
  rfl

/-- [proved-derived; formal-checked] **`kt_likelihood_laws`: the sequential KT likelihood.**
Over a finite alphabet at α = 1/2:
* it is positive, and the empty word has likelihood one;
* **consistency**: `Σ_c KT(w ++ [c]) = KT(w)`, so KT is a probability law on words of each length;
* **the conditional is the likelihood ratio**: `KT(w ++ [c])/KT(w) = (n_c + 1/2)/(n + |A|/2)`,
  `RegionCounts.ktProb`, the region face of Decision 27 (`count_face_eq_kt`);
* **exchangeability**: permuted words have equal likelihood; the counts are the whole standing;
* **uniqueness**: any law with the empty word at one and that sequential step is `ktSeq`, so the
  count form is the sequential product of successive predictions. -/
theorem kt_likelihood_laws [Nonempty A] :
    (∀ w : List A, 0 < ktSeq w) ∧ ktSeq ([] : List A) = 1 ∧
      (∀ w : List A, ∑ c, ktSeq (w ++ [c]) = ktSeq w) ∧
      (∀ (w : List A) c, ktSeq (w ++ [c]) / ktSeq w =
        ktProb (w.count c) w.length (Fintype.card A)) ∧
      (∀ w₁ w₂ : List A, w₁.Perm w₂ → ktSeq w₁ = ktSeq w₂) ∧
      ∀ f : List A → ℚ, f [] = 1 →
        (∀ w c, f (w ++ [c]) = f w * ktProb (w.count c) w.length (Fintype.card A)) →
          ∀ w, f w = ktSeq w := by
  refine ⟨fun w => ktMass_pos _, ktSeq_nil, fun w => ?_, fun w c => ?_, fun w₁ w₂ h => ?_,
    fun f h0 hs w => ?_⟩
  · have := ktFace_sum (counts w)
    simp only [ktSeq, counts_snoc, ktMass_bump, ← Finset.mul_sum, this, mul_one]
  · have hw : ktSeq w ≠ 0 := (ktMass_pos _).ne'
    rw [ktSeq_snoc, mul_div_cancel_left₀ _ hw]
  · unfold ktSeq counts
    congr 1
    funext c
    exact h.count_eq c
  · induction w using List.reverseRecOn with
    | nil => rw [h0, ktSeq_nil]
    | append_singleton w c ih => rw [hs, ih, ktSeq_snoc]

end KT

/-! ## 3. The opened-path face -/

section PathFace

variable {A : Type*} [Fintype A]

/-- [definition] **The mixture along the opened path**, from depth `d` with `m` levels below:
`q_d = k_d` at the deepest node, and `q_d = λ_d k_d + (1 − λ_d) q_(d+1)` above it. -/
def mixFrom (k : ℕ → A → ℚ) (lam : ℕ → ℚ) : ℕ → ℕ → A → ℚ
  | 0, d => k d
  | m + 1, d => fun c => lam d * k d c + (1 - lam d) * mixFrom k lam m (d + 1) c

/-- [definition] **The opened-path face at depth `d`** of a path of maximum depth `D`. -/
def pathFace (k : ℕ → A → ℚ) (lam : ℕ → ℚ) (D d : ℕ) : A → ℚ := mixFrom k lam (D - d) d

omit [Fintype A] in
theorem pathFace_deepest (k : ℕ → A → ℚ) (lam : ℕ → ℚ) (D : ℕ) : pathFace k lam D D = k D := by
  simp [pathFace, mixFrom]

omit [Fintype A] in
theorem pathFace_step (k : ℕ → A → ℚ) (lam : ℕ → ℚ) {D d : ℕ} (h : d < D) (c : A) :
    pathFace k lam D d c = lam d * k d c + (1 - lam d) * pathFace k lam D (d + 1) c := by
  unfold pathFace
  obtain ⟨m, hm⟩ : ∃ m, D - d = m + 1 := ⟨D - d - 1, by omega⟩
  rw [hm, mixFrom, show D - (d + 1) = m by omega]

theorem mix_pos {l x y : ℚ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hx : 0 < x) (hy : 0 < y) :
    0 < l * x + (1 - l) * y := by
  rcases hl0.lt_or_eq with h | h
  · have := mul_pos h hx
    have := mul_nonneg (sub_nonneg.mpr hl1) hy.le
    linarith
  · subst h; simpa using hy

/-- [proved-derived; formal-checked] **`path_face_normalized`.** For positive, normalized faces
`k_d` at the path's depths `d ≤ D` and **any** weights `λ_d ∈ [0,1]` at the depths `d < D`, the
opened-path face `q_d` at every depth `d ≤ D` is positive and sums to one. This covers the exact
CTW weights and the executed chart, where `λ` is carried on a lattice. -/
theorem path_face_normalized (k : ℕ → A → ℚ) (lam : ℕ → ℚ) (D : ℕ)
    (hk : ∀ d ≤ D, ∀ c, 0 < k d c) (hks : ∀ d ≤ D, ∑ c, k d c = 1)
    (hl : ∀ d < D, 0 ≤ lam d ∧ lam d ≤ 1) :
    ∀ d ≤ D, (∀ c, 0 < pathFace k lam D d c) ∧ ∑ c, pathFace k lam D d c = 1 := by
  suffices h : ∀ m d, d + m = D → (∀ c, 0 < mixFrom k lam m d c) ∧ ∑ c, mixFrom k lam m d c = 1 by
    intro d hd
    exact h (D - d) d (by omega)
  intro m
  induction m with
  | zero =>
    intro d hd
    exact ⟨hk d (by omega), hks d (by omega)⟩
  | succ m ih =>
    intro d hd
    obtain ⟨hpos, hsum⟩ := ih (d + 1) (by omega)
    obtain ⟨hl0, hl1⟩ := hl d (by omega)
    refine ⟨fun c => mix_pos hl0 hl1 (hk d (by omega) c) (hpos c), ?_⟩
    simp only [mixFrom, Finset.sum_add_distrib, ← Finset.mul_sum, hks d (by omega), hsum]
    ring

omit [Fintype A] in
/-- [proved-derived; formal-checked] **`path_face_ge_min`.** Under any weights `λ_d ∈ [0,1]`, the
opened-path face at depth `d` is at least every common lower bound of the path's faces `k_d'`,
`d ≤ d' ≤ D`; in particular it is at least their minimum. -/
theorem path_face_ge_min (k : ℕ → A → ℚ) (lam : ℕ → ℚ) (D : ℕ) (c : A)
    (hl : ∀ d < D, 0 ≤ lam d ∧ lam d ≤ 1) :
    (∀ lo : ℚ, ∀ d ≤ D, (∀ d', d ≤ d' → d' ≤ D → lo ≤ k d' c) → lo ≤ pathFace k lam D d c) ∧
      ∀ d (hd : d ≤ D), (Finset.Icc d D).inf' ⟨d, Finset.mem_Icc.mpr ⟨le_rfl, hd⟩⟩
        (fun d' => k d' c) ≤ pathFace k lam D d c := by
  have hbound : ∀ lo : ℚ, ∀ d ≤ D, (∀ d', d ≤ d' → d' ≤ D → lo ≤ k d' c) →
      lo ≤ pathFace k lam D d c := by
    intro lo
    suffices h : ∀ m d, d + m = D → (∀ d', d ≤ d' → d' ≤ D → lo ≤ k d' c) →
        lo ≤ mixFrom k lam m d c by
      intro d hd hlo
      exact h (D - d) d (by omega) hlo
    intro m
    induction m with
    | zero => intro d hd hlo; exact hlo d le_rfl (by omega)
    | succ m ih =>
      intro d hd hlo
      have hq := ih (d + 1) (by omega) fun d' h1 h2 => hlo d' (by omega) h2
      have hkd := hlo d le_rfl (by omega)
      obtain ⟨hl0, hl1⟩ := hl d (by omega)
      simp only [mixFrom]
      have e1 := mul_le_mul_of_nonneg_left hkd hl0
      have e2 := mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hl1)
      nlinarith
  refine ⟨hbound, fun d hd => hbound _ d hd fun d' h1 h2 => ?_⟩
  exact Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨h1, h2⟩)

omit [Fintype A] in
/-- A path whose faces agree at a class reads that value at every depth, whatever the weights. -/
theorem pathFace_const (k : ℕ → A → ℚ) (lam : ℕ → ℚ) (D : ℕ) (c : A) (v : ℚ) :
    ∀ d ≤ D, (∀ d', d ≤ d' → d' ≤ D → k d' c = v) → pathFace k lam D d c = v := by
  suffices h : ∀ m d, d + m = D → (∀ d', d ≤ d' → d' ≤ D → k d' c = v) →
      mixFrom k lam m d c = v by
    intro d hd hv
    exact h (D - d) d (by omega) hv
  intro m
  induction m with
  | zero => intro d hd hv; exact hv d le_rfl (by omega)
  | succ m ih =>
    intro d hd hv
    simp only [mixFrom, hv d le_rfl (by omega),
      ih (d + 1) (by omega) fun d' h1 h2 => hv d' (by omega) h2]
    ring

end PathFace

/-! ## 4. The landmark tree: the recursive mixture and its step -/

section Tree

variable {Ltr : Type*} [Fintype Ltr] [DecidableEq Ltr] {A : Type*} [Fintype A] [DecidableEq A]

/-- [definition] **The tree standing**: the KT count table at every node (address word) of the
landmark tree. It is the whole retention of the tree receiver: no occurrence list is kept. -/
abbrev TreeStanding (Ltr A : Type*) := List Ltr → A → ℕ

/-- [definition] **The empty standing**: no landmark is founded. -/
def emptyStanding : TreeStanding Ltr A := fun _ _ => 0

/-- [definition] **An arrival** of class `c` at address `a`: every node on the path the address
opens (every node `s` to which `a` restricts, `a.take |s| = s`) deposits one count of `c`; every
node off the path is unchanged. -/
def arrive (N : TreeStanding Ltr A) (a : List Ltr) (c : A) : TreeStanding Ltr A :=
  fun s => if a.take s.length = s then bump (N s) c else N s

/-- [definition] **The recursive mixture** (Willems–Shtarkov–Tjalkens) at node `s` with `m`
levels below it: `W_s = E_s` at the maximum depth and `W_s = (E_s + ∏_b W_(s b))/2` above it, with
`E_s` the node's KT mass. -/
def treeWeight (N : TreeStanding Ltr A) : ℕ → List Ltr → ℚ
  | 0, s => ktMass (N s)
  | m + 1, s => (ktMass (N s) + ∏ b, treeWeight N m (s ++ [b])) / 2

/-- [definition] **The split mass** `P_s = ∏_b W_(s b)`: the children's weights multiplied. -/
def splitMass (N : TreeStanding Ltr A) (m : ℕ) (s : List Ltr) : ℚ :=
  ∏ b, treeWeight N m (s ++ [b])

omit [DecidableEq A] [DecidableEq Ltr] in
theorem treeWeight_succ (N : TreeStanding Ltr A) (m : ℕ) (s : List Ltr) :
    treeWeight N (m + 1) s = (ktMass (N s) + splitMass N m s) / 2 := rfl

omit [DecidableEq A] [DecidableEq Ltr] in
theorem treeWeight_pos [Nonempty A] (N : TreeStanding Ltr A) : ∀ m s, 0 < treeWeight N m s
  | 0, s => ktMass_pos _
  | m + 1, s => by
    have hE := ktMass_pos (N s)
    have hP : 0 < ∏ b, treeWeight N m (s ++ [b]) :=
      Finset.prod_pos fun _ _ => treeWeight_pos N m _
    simp only [treeWeight]
    linarith

omit [DecidableEq A] [DecidableEq Ltr] in
theorem splitMass_pos [Nonempty A] (N : TreeStanding Ltr A) (m : ℕ) (s : List Ltr) :
    0 < splitMass N m s :=
  Finset.prod_pos fun _ _ => treeWeight_pos N m _

/-- [definition] **The KT face of the node at depth `d`** of the path opened by `a`. -/
def kAt (N : TreeStanding Ltr A) (a : List Ltr) (d : ℕ) : A → ℚ := ktFace (N (a.take d))

/-- [definition] **The stop weight** at depth `d`: `λ_d = E_d/(E_d + P_d)`, the posterior weight of
stopping at the node against splitting below it. -/
def lamAt (N : TreeStanding Ltr A) (D : ℕ) (a : List Ltr) (d : ℕ) : ℚ :=
  ktMass (N (a.take d)) / (ktMass (N (a.take d)) + splitMass N (D - d - 1) (a.take d))

/-- [definition] **The tree's face along the opened path** at depth `d`: the path face of the
nodes' KT faces under the stop weights. -/
def face (N : TreeStanding Ltr A) (D : ℕ) (a : List Ltr) (d : ℕ) : A → ℚ :=
  pathFace (kAt N a) (lamAt N D a) D d

omit [DecidableEq A] [DecidableEq Ltr] in
theorem lamAt_mem [Nonempty A] (N : TreeStanding Ltr A) (D : ℕ) (a : List Ltr) (d : ℕ) :
    0 < lamAt N D a d ∧ lamAt N D a d < 1 := by
  have hE := ktMass_pos (N (a.take d))
  have hP := splitMass_pos N (D - d - 1) (a.take d)
  unfold lamAt
  exact ⟨div_pos hE (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩

omit [DecidableEq A] [DecidableEq Ltr] in
/-- The stop weight is `λ = β/(1 + β)` with the stop-to-split ratio `β = E/P`. -/
theorem lamAt_eq_beta [Nonempty A] (N : TreeStanding Ltr A) (D : ℕ) (a : List Ltr) (d : ℕ) :
    lamAt N D a d =
      (ktMass (N (a.take d)) / splitMass N (D - d - 1) (a.take d)) /
        (1 + ktMass (N (a.take d)) / splitMass N (D - d - 1) (a.take d)) := by
  have hE := ktMass_pos (N (a.take d))
  have hP := splitMass_pos N (D - d - 1) (a.take d)
  unfold lamAt
  field_simp
  ring

omit [DecidableEq A] [DecidableEq Ltr] in
/-- [proved-derived; formal-checked] The tree's face along any opened path is positive and
normalized at every depth `d ≤ D` (`path_face_normalized`: KT faces are positive sections and the
stop weights lie in `(0, 1)`). -/
theorem face_normalized [Nonempty A] (N : TreeStanding Ltr A) (D : ℕ) (a : List Ltr) :
    ∀ d ≤ D, (∀ c, 0 < face N D a d c) ∧ ∑ c, face N D a d c = 1 :=
  path_face_normalized _ _ D (fun _ _ c => ktFace_pos _ c) (fun _ _ => ktFace_sum _)
    fun d _ => ⟨(lamAt_mem N D a d).1.le, (lamAt_mem N D a d).2.le⟩

omit [DecidableEq A] [DecidableEq Ltr] in
/-- The tree's path face is positive at every depth (below `D` it is the node's KT face). -/
theorem face_pos_all [Nonempty A] (N : TreeStanding Ltr A) (D : ℕ) (a : List Ltr) (c : A) (d : ℕ) :
    0 < face N D a d c := by
  by_cases hd : d ≤ D
  · exact (face_normalized N D a d hd).1 c
  · have : D - d = 0 := by omega
    simp only [face, pathFace, this, mixFrom, kAt]
    exact ktFace_pos _ c

omit [Fintype Ltr] [DecidableEq Ltr] in
/-- A node restricted from an address opens on it. -/
theorem opens_take (a : List Ltr) (d : ℕ) : a.take (a.take d).length = a.take d :=
  (List.prefix_iff_eq_take.mp (List.take_prefix d a)).symm

omit [Fintype Ltr] [DecidableEq Ltr] in
/-- A node off the opened path has every descendant off the path. -/
theorem off_path_descendant {a s : List Ltr} (h : ¬ a.take s.length = s) (t : List Ltr) :
    ¬ a.take (s ++ t).length = s ++ t := by
  intro ht
  have hp : s ++ t <+: a := List.prefix_iff_eq_take.mpr ht.symm
  exact h (List.prefix_iff_eq_take.mp ((List.prefix_append s t).trans hp)).symm

omit [Fintype Ltr] [DecidableEq Ltr] in
/-- Of the children of an opened node, only the one along the address is opened. -/
theorem off_path_child {a : List Ltr} {d : ℕ} (hd : d < a.length) {b : Ltr} (hb : b ≠ a[d]) :
    ¬ a.take (a.take d ++ [b]).length = a.take d ++ [b] := by
  intro h
  have hlen : (a.take d ++ [b]).length = d + 1 := by simp; omega
  rw [hlen, ← restrict, restrict_succ hd, restrict] at h
  exact hb (List.singleton_inj.mp (List.append_cancel_left h)).symm

/-- [proved-derived; formal-checked] **A deposit is local to the opened path**: at a node off the
path the arrival changes no weight at any depth below it. -/
theorem treeWeight_arrive_off (N : TreeStanding Ltr A) {a s : List Ltr}
    (h : ¬ a.take s.length = s) (c : A) (m : ℕ) :
    treeWeight (arrive N a c) m s = treeWeight N m s := by
  induction m generalizing s with
  | zero => simp [treeWeight, arrive, h]
  | succ m ih =>
    simp only [treeWeight, arrive, if_neg h]
    congr 2
    exact Finset.prod_congr rfl fun b _ => ih (off_path_descendant h [b])

theorem prod_update_one {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : ι → ℚ) (i0 : ι) (r : ℚ)
    (h0 : g i0 = f i0 * r) (h : ∀ i, i ≠ i0 → g i = f i) : ∏ i, g i = (∏ i, f i) * r := by
  have e : ∀ i, g i = f i * (if i = i0 then r else 1) := fun i => by
    by_cases hi : i = i0
    · subst hi; simp [h0]
    · simp [hi, h i hi]
  rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

/-- The split mass of an opened node moves by its opened child's factor. -/
theorem splitMass_arrive (N : TreeStanding Ltr A) {a : List Ltr} {d : ℕ} (hd : d < a.length)
    (c : A) (m : ℕ) (r : ℚ)
    (hchild : treeWeight (arrive N a c) m (a.take (d + 1)) = treeWeight N m (a.take (d + 1)) * r) :
    splitMass (arrive N a c) m (a.take d) = splitMass N m (a.take d) * r := by
  unfold splitMass
  refine prod_update_one _ _ a[d] r ?_ fun b hb =>
    treeWeight_arrive_off N (off_path_child hd hb) c m
  have e : a.take d ++ [a[d]] = a.take (d + 1) := (restrict_succ hd).symm
  rw [e]
  exact hchild

/-- [proved-derived; formal-checked] **`weight_step`: the conditional prediction is the successive
likelihood ratio.** For an address `a` of length at least `D` and a class `c`, at every depth
`d ≤ D` of the opened path, `W'_d = W_d · q_d(c)`: the arrival multiplies the node's weight by the
tree's face there, `q_D = k_D` and `q_d = λ_d k_d + (1 − λ_d) q_(d+1)` with
`λ_d = E_d/(E_d + P_d)`. -/
theorem weight_step [Nonempty A] (N : TreeStanding Ltr A) {D : ℕ} {a : List Ltr}
    (hD : D ≤ a.length) (c : A) :
    ∀ d ≤ D, treeWeight (arrive N a c) (D - d) (a.take d) =
      treeWeight N (D - d) (a.take d) * face N D a d c := by
  suffices h : ∀ m d, d + m = D → treeWeight (arrive N a c) m (a.take d) =
      treeWeight N m (a.take d) * face N D a d c by
    intro d hd
    exact h (D - d) d (by omega)
  intro m
  induction m with
  | zero =>
    intro d hd
    have hdD : d = D := by omega
    subst hdD
    simp only [treeWeight, arrive, if_pos (opens_take a d), ktMass_bump]
    rw [face, pathFace_deepest]
    rfl
  | succ m ih =>
    intro d hd
    have hda : d < a.length := by omega
    have hsplit := splitMass_arrive N hda c m (face N D a (d + 1) c) (ih (d + 1) (by omega))
    rw [treeWeight_succ, treeWeight_succ, hsplit]
    simp only [arrive, if_pos (opens_take a d), ktMass_bump]
    simp only [face]
    rw [pathFace_step _ _ (show d < D by omega)]
    have hlam : lamAt N D a d =
        ktMass (N (a.take d)) / (ktMass (N (a.take d)) + splitMass N m (a.take d)) := by
      unfold lamAt
      rw [show D - d - 1 = m by omega]
    rw [hlam]
    have hE := ktMass_pos (N (a.take d))
    have hP := splitMass_pos N m (a.take d)
    unfold kAt
    field_simp
    ring

/-- [proved-derived; formal-checked] **`landmark_step`: the mixture and its step.** For an address
`a` of length at least `D` and a class `c`:
* at the root, `W' = W · q_0(c)`, and `q_0(c) = W'/W` is the successive likelihood ratio;
* **consistency**: `Σ_c W'(c) = W`, the root weight is a probability law's step;
* at each opened node above the maximum depth, `E' = E·k_d(c)` and `P' = P·q_(d+1)(c)`, so the
  stop-to-split ratio `β = E/P` moves by `β' = β·k_d(c)/q_(d+1)(c)`;
* at every depth, `q_d(c) = W'_d/W_d`. -/
theorem landmark_step [Nonempty A] (N : TreeStanding Ltr A) {D : ℕ} {a : List Ltr}
    (hD : D ≤ a.length) (c : A) :
    treeWeight (arrive N a c) D [] = treeWeight N D [] * face N D a 0 c ∧
      face N D a 0 c = treeWeight (arrive N a c) D [] / treeWeight N D [] ∧
      ∑ c', treeWeight (arrive N a c') D [] = treeWeight N D [] ∧
      (∀ d < D, ktMass (arrive N a c (a.take d)) = ktMass (N (a.take d)) * kAt N a d c ∧
        splitMass (arrive N a c) (D - d - 1) (a.take d) =
          splitMass N (D - d - 1) (a.take d) * face N D a (d + 1) c ∧
        ktMass (arrive N a c (a.take d)) / splitMass (arrive N a c) (D - d - 1) (a.take d) =
          ktMass (N (a.take d)) / splitMass N (D - d - 1) (a.take d) * kAt N a d c /
            face N D a (d + 1) c) ∧
      ∀ d ≤ D, face N D a d c =
        treeWeight (arrive N a c) (D - d) (a.take d) / treeWeight N (D - d) (a.take d) := by
  have hroot : ∀ c, treeWeight (arrive N a c) D [] = treeWeight N D [] * face N D a 0 c := by
    intro c
    simpa using weight_step N hD c 0 (Nat.zero_le _)
  have hW := treeWeight_pos N D []
  have hratio : ∀ d ≤ D, face N D a d c =
      treeWeight (arrive N a c) (D - d) (a.take d) / treeWeight N (D - d) (a.take d) := by
    intro d hd
    rw [weight_step N hD c d hd, mul_div_cancel_left₀ _ (treeWeight_pos N _ _).ne']
  refine ⟨hroot c, by simpa using hratio 0 (Nat.zero_le _), ?_, fun d hd => ?_, hratio⟩
  · rw [Finset.sum_congr rfl fun c' _ => hroot c', ← Finset.mul_sum,
      (face_normalized N D a 0 (Nat.zero_le _)).2, mul_one]
  · have hda : d < a.length := by omega
    have hE : ktMass (arrive N a c (a.take d)) = ktMass (N (a.take d)) * kAt N a d c := by
      simp only [arrive, if_pos (opens_take a d), ktMass_bump, kAt]
    have hchild := weight_step N hD c (d + 1) (by omega)
    rw [show D - (d + 1) = D - d - 1 by omega] at hchild
    have hP := splitMass_arrive N hda c (D - d - 1) (face N D a (d + 1) c) hchild
    refine ⟨hE, hP, ?_⟩
    rw [hE, hP]
    have hq := (face_normalized N D a (d + 1) (by omega)).1 c
    have hPp := splitMass_pos N (D - d - 1) (a.take d)
    field_simp

/-! ### The product law over words, with a causal context -/

/-- [definition] **The standing after a past**, for a causal context `ctx` (the address of the next
arrival is a function of the past, newest first): the empty standing, and each class `c` arriving
at the address its past opens. -/
def standingOf (ctx : List A → List Ltr) : List A → TreeStanding Ltr A
  | [] => emptyStanding
  | c :: h => arrive (standingOf ctx h) (ctx h) c

/-- [definition] **The sum over all words of length `n`**, newest letter first: the past `h` of
length `n` and then every next class `c`. -/
def wordSum : ℕ → (List A → ℚ) → ℚ
  | 0, f => f []
  | n + 1, f => wordSum n fun h => ∑ c, f (c :: h)

omit [DecidableEq A] in
/-- `wordSum n f` is the sum of `f` over every word of length `n` (`List.ofFn` of a tuple). -/
theorem wordSum_eq_sum (n : ℕ) (f : List A → ℚ) :
    wordSum n f = ∑ v : Fin n → A, f (List.ofFn v) := by
  induction n generalizing f with
  | zero => simp [wordSum]
  | succ n ih =>
    rw [wordSum, ih, ← (Fin.consEquiv fun _ : Fin (n + 1) => A).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun c _ => ?_
    simp [Fin.consEquiv, List.ofFn_succ]

omit [DecidableEq A] [DecidableEq Ltr] in
theorem treeWeight_empty [Nonempty A] :
    ∀ m s, treeWeight (emptyStanding : TreeStanding Ltr A) m s = 1
  | 0, _ => ktMass_zero
  | m + 1, s => by
    show (ktMass (fun _ : A => 0) + ∏ b, treeWeight emptyStanding m (s ++ [b])) / 2 = 1
    simp only [ktMass_zero, treeWeight_empty m, Finset.prod_const_one]
    norm_num

/-- [proved-derived; formal-checked] **`mixture_is_probability`: the recursive mixture is a
probability law on words of each length.** For a causal context `ctx` whose addresses reach depth
`D`, the root weight after a past is positive, each next class multiplies it by the tree's face at
the address that past opens, and the root weights over all words of length `n` sum to one. -/
theorem mixture_is_probability [Nonempty A] (ctx : List A → List Ltr) (D : ℕ)
    (hctx : ∀ h, D ≤ (ctx h).length) :
    (∀ h, 0 < treeWeight (standingOf ctx h) D []) ∧
      (∀ h c, treeWeight (standingOf ctx (c :: h)) D [] =
        treeWeight (standingOf ctx h) D [] * face (standingOf ctx h) D (ctx h) 0 c) ∧
      ∀ n, wordSum n (fun h => treeWeight (standingOf ctx h) D []) = 1 ∧
        ∑ v : Fin n → A, treeWeight (standingOf ctx (List.ofFn v)) D [] = 1 := by
  refine ⟨fun h => treeWeight_pos _ _ _, fun h c => (landmark_step _ (hctx h) c).1, fun n => ?_⟩
  have hn : wordSum n (fun h => treeWeight (standingOf ctx h) D []) = 1 := by
    induction n with
    | zero => simp [wordSum, standingOf, treeWeight_empty]
    | succ n ih =>
      rw [wordSum]
      have e : (fun h => ∑ c, treeWeight (standingOf ctx (c :: h)) D []) =
          fun h => treeWeight (standingOf ctx h) D [] := by
        funext h
        exact (landmark_step _ (hctx h) (Classical.arbitrary A)).2.2.1
      rw [e, ih]
  exact ⟨hn, by rw [wordSum_eq_sum] at hn; exact hn⟩

/-! ### The routed subsequences: the counts are the KT masses of what reached each node -/

/-- [definition] **The routed subsequence** of node `s`: the classes of the observations whose
address opens `s`, in arrival order. It is a reference for the proof only; the standing retains
its counts. -/
def routed (obs : List (List Ltr × A)) (s : List Ltr) : List A :=
  (obs.filter fun o => o.1.take s.length = s).map Prod.snd

/-- [definition] **The count standing of an observation list**: at each node, the counts of its
routed subsequence. -/
def nodeCounts (obs : List (List Ltr × A)) : TreeStanding Ltr A := fun s => counts (routed obs s)

/-- [definition] The observations of a past under a causal context, oldest first. -/
def observations (ctx : List A → List Ltr) : List A → List (List Ltr × A)
  | [] => []
  | c :: h => observations ctx h ++ [(ctx h, c)]

omit [Fintype A] [Fintype Ltr] [DecidableEq A] in
theorem routed_snoc (obs : List (List Ltr × A)) (a : List Ltr) (c : A) (s : List Ltr) :
    routed (obs ++ [(a, c)]) s = routed obs s ++ if a.take s.length = s then [c] else [] := by
  by_cases h : a.take s.length = s <;> simp [routed, List.filter_append, h]

omit [Fintype Ltr] [Fintype A] in
theorem nodeCounts_snoc (obs : List (List Ltr × A)) (a : List Ltr) (c : A) :
    nodeCounts (obs ++ [(a, c)]) = arrive (nodeCounts obs) a c := by
  funext s
  simp only [nodeCounts, arrive, routed_snoc]
  by_cases h : a.take s.length = s
  · simp [h, counts_snoc]
  · simp [h]

omit [Fintype Ltr] in
/-- [proved-derived; formal-checked] **The standing is the routed counts.** Under a causal
context, the standing after a past is the count table of the observations routed to each node, so
each node's KT mass is the sequential KT likelihood of its routed subsequence
(`E_s = KT(x_s)`, the CTW node likelihood). -/
theorem standing_is_routed_counts (ctx : List A → List Ltr) (h : List A) (s : List Ltr) :
    standingOf ctx h = nodeCounts (observations ctx h) ∧
      ktMass (standingOf ctx h s) = ktSeq (routed (observations ctx h) s) := by
  have e : standingOf ctx h = nodeCounts (observations ctx h) := by
    induction h with
    | nil =>
      funext s c
      simp [standingOf, emptyStanding, nodeCounts, observations, routed, counts]
    | cons c h ih => rw [standingOf, observations, nodeCounts_snoc, ih]
  exact ⟨e, by rw [e]; rfl⟩

/-! ### Depth one is Decision 27 -/

/-- [definition] **The region word** of Decision 27: each observation reaches the region of its
depth-one restriction (the preceding cell) with unit weight. -/
def regionWord (obs : List (List Ltr × A)) : List (List Ltr × ℚ × A) :=
  obs.map fun o => (o.1.take 1, 1, o.2)

open Holonics.HNN.RegionCounts (target regionRun_local count_face_eq_kt) in
omit [Fintype Ltr] in
/-- [proved-derived; formal-checked] **`depth_one_is_decision_27`.** At depth one with the forced
split `λ_0 = 0`, the tree's face at an address `a` is the face of the depth-one node, and it equals
Decision 27's region face: `RegionCounts.countFace` of the KT masses the region word deposited at
the region `a.take 1` (`regionRun_local`, `count_face_eq_kt`), which is KT's
`(n_c + 1/2)/(n + |A|/2)` over that region's routed classes. Ordinary CTW at depth one instead
weighs in the root's context-free face with `0 < λ_0 < 1` (`lamAt_mem`). The node faces here are
the whole-cell emission's `|A|`-ary KT faces; the digit emission's depth-one forced case multiplies
binary KT faces over the cell's opened digits and is not this face. -/
theorem depth_one_is_decision_27 [Nonempty A] (obs : List (List Ltr × A)) {a : List Ltr}
    (ha : 1 ≤ a.length) (lam : ℕ → ℚ) (h0 : lam 0 = 0) (c : A) :
    pathFace (kAt (nodeCounts obs) a) lam 1 0 c =
        countFace (regionRun (fun _ => ktPrior) (regionWord obs) (a.take 1)) c ∧
      pathFace (kAt (nodeCounts obs) a) lam 1 0 c =
        ktProb ((routed obs (a.take 1)).count c) (routed obs (a.take 1)).length
          (Fintype.card A) := by
  have hr : (a.take 1).length = 1 := by simp; omega
  have hface : pathFace (kAt (nodeCounts obs) a) lam 1 0 c =
      ktProb ((routed obs (a.take 1)).count c) (routed obs (a.take 1)).length
        (Fintype.card A) := by
    rw [pathFace_step _ _ (Nat.zero_lt_one), h0, pathFace_deepest]
    simp only [zero_mul, sub_zero, one_mul, zero_add, kAt, ktFace, nodeCounts, sum_counts]
    rfl
  refine ⟨?_, hface⟩
  have hfilter : ((regionWord obs).filter fun d => d.1 = a.take 1).map
      (fun d => (d.2.1, target d.2.2)) = targetWord (routed obs (a.take 1)) := by
    simp only [regionWord, routed, targetWord, List.filter_map, List.map_map, hr]
    rfl
  rw [regionRun_local, hfilter, (count_face_eq_kt _ c).2.2, hface]

end Tree

/-! ## 5. The mixture over pruned trees (the Kraft form) -/

section Kraft

universe u

/-- [definition] **Pruned trees of depth at most `m`** over the address letters: at a node with
depth remaining, a leaf (`none`, stop) or a split into one subtree per letter (`some`). -/
def PrunedTree (Ltr : Type u) : ℕ → Type u
  | 0 => PUnit
  | m + 1 => Option (Ltr → PrunedTree Ltr m)

/-- The pruned trees of each depth form a finite type. -/
@[reducible] def PrunedTree.fintype (Ltr : Type u) [Fintype Ltr] [DecidableEq Ltr] :
    (m : ℕ) → Fintype (PrunedTree Ltr m)
  | 0 => inferInstanceAs (Fintype PUnit)
  | m + 1 =>
    letI := PrunedTree.fintype Ltr m
    inferInstanceAs (Fintype (Option (Ltr → PrunedTree Ltr m)))

instance (Ltr : Type u) [Fintype Ltr] [DecidableEq Ltr] (m : ℕ) : Fintype (PrunedTree Ltr m) :=
  PrunedTree.fintype Ltr m

variable {Ltr : Type u} [Fintype Ltr] [DecidableEq Ltr] {A : Type*} [Fintype A] [DecidableEq A]

/-- [definition] **The model cost** `Γ(S)`: one bit (stop or split) at every node of `S` above the
maximum depth. For binary letters it is `2|S| − 1 − |S_D|`, `|S|` the leaves and `S_D` the leaves
at the maximum depth. -/
def PrunedTree.cost : (m : ℕ) → PrunedTree Ltr m → ℕ
  | 0, _ => 0
  | m + 1, S => Option.elim (S : Option (Ltr → PrunedTree Ltr m)) 1
      fun f => 1 + ∑ b, PrunedTree.cost m (f b)

/-- [definition] **The likelihood of a pruned tree**: the product of its leaves' KT masses. -/
def treeLik (N : TreeStanding Ltr A) : (m : ℕ) → List Ltr → PrunedTree Ltr m → ℚ
  | 0, s, _ => ktMass (N s)
  | m + 1, s, S => Option.elim (S : Option (Ltr → PrunedTree Ltr m)) (ktMass (N s))
      fun f => ∏ b, treeLik N m (s ++ [b]) (f b)

omit [DecidableEq A] [DecidableEq Ltr] in
theorem treeLik_pos [Nonempty A] (N : TreeStanding Ltr A) :
    ∀ m s (S : PrunedTree Ltr m), 0 < treeLik N m s S
  | 0, s, _ => ktMass_pos _
  | m + 1, s, S => by
    cases hS : (S : Option (Ltr → PrunedTree Ltr m)) with
    | none => simp only [treeLik, Option.elim]; exact ktMass_pos _
    | some f =>
      simp only [treeLik, Option.elim]
      exact Finset.prod_pos fun b _ => treeLik_pos N m _ _

omit [DecidableEq A] in
/-- [proved-derived; formal-checked] **`mixture_over_trees`: the recursive mixture is the mixture
over pruned trees with the Kraft weights `2^(−Γ(S))`** (Willems–Shtarkov–Tjalkens, the model
mixture): `W_s = Σ_S 2^(−Γ(S)) ∏_(leaves ℓ of S) E_(s ℓ)`. -/
theorem mixture_over_trees (N : TreeStanding Ltr A) :
    ∀ m s, treeWeight N m s =
      ∑ S : PrunedTree Ltr m, (1 / 2 : ℚ) ^ PrunedTree.cost m S * treeLik N m s S
  | 0, s => by
    have hc : Fintype.card (PrunedTree Ltr 0) = 1 := rfl
    simp [treeWeight, treeLik, PrunedTree.cost, hc]
  | m + 1, s => by
    rw [treeWeight_succ, splitMass]
    simp only [mixture_over_trees N m]
    rw [Fintype.prod_sum]
    have e : ∑ S : PrunedTree Ltr (m + 1),
        (1 / 2 : ℚ) ^ PrunedTree.cost (m + 1) S * treeLik N (m + 1) s S =
        (1 / 2 : ℚ) ^ 1 * ktMass (N s) + ∑ f : Ltr → PrunedTree Ltr m,
          (1 / 2 : ℚ) ^ (1 + ∑ b, PrunedTree.cost m (f b)) *
            ∏ b, treeLik N m (s ++ [b]) (f b) :=
      Fintype.sum_option (fun S : Option (Ltr → PrunedTree Ltr m) =>
        (1 / 2 : ℚ) ^ PrunedTree.cost (m + 1) S * treeLik N (m + 1) s S)
    rw [e, add_div, pow_one]
    congr 1
    · ring
    · rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [pow_add, ← Finset.prod_pow_eq_pow_sum, Finset.prod_mul_distrib]
      ring

omit [DecidableEq A] [DecidableEq Ltr] in
theorem treeLik_empty [Nonempty A] :
    ∀ m s (S : PrunedTree Ltr m), treeLik (emptyStanding : TreeStanding Ltr A) m s S = 1
  | 0, _, _ => ktMass_zero
  | m + 1, s, S => by
    cases hS : (S : Option (Ltr → PrunedTree Ltr m)) with
    | none => simp only [treeLik, Option.elim]; exact ktMass_zero
    | some f =>
      simp only [treeLik, Option.elim]
      exact Finset.prod_eq_one fun b _ => treeLik_empty m _ _

omit [DecidableEq A] in
/-- [proved-derived; formal-checked] **`kraft_and_dominance`.**
* **Kraft**: `Σ_S 2^(−Γ(S)) = 1` over the pruned trees of each depth (the stop/split code is
  complete);
* **dominance**: for every pruned tree `S`, `W_s ≥ 2^(−Γ(S)) ∏_(leaves) E`, so the mixture's code
  length is at most the tree's model cost plus its leaves' KT code length,
  `−log₂ W ≤ Γ(S) − log₂ ∏ E`.

This is the model-cost part of CTW's redundancy bound, exact. The parameter part (each leaf's KT
excess over a fixed binary parameter, `½ log₂ n + 1`) stays conditional (module docstring). -/
theorem kraft_and_dominance [Nonempty A] (N : TreeStanding Ltr A) (m : ℕ) (s : List Ltr) :
    ∑ S : PrunedTree Ltr m, (1 / 2 : ℚ) ^ PrunedTree.cost m S = 1 ∧
      ∀ S : PrunedTree Ltr m,
        (1 / 2 : ℚ) ^ PrunedTree.cost m S * treeLik N m s S ≤ treeWeight N m s ∧
        -Real.logb 2 (treeWeight N m s : ℝ) ≤
          (PrunedTree.cost m S : ℝ) - Real.logb 2 (treeLik N m s S : ℝ) := by
  have hdom : ∀ S : PrunedTree Ltr m,
      (1 / 2 : ℚ) ^ PrunedTree.cost m S * treeLik N m s S ≤ treeWeight N m s := by
    intro S
    rw [mixture_over_trees N m s]
    exact Finset.single_le_sum (f := fun S => (1 / 2 : ℚ) ^ PrunedTree.cost m S * treeLik N m s S)
      (fun S _ => by have := treeLik_pos N m s S; positivity) (Finset.mem_univ S)
  refine ⟨?_, fun S => ⟨hdom S, ?_⟩⟩
  · have := mixture_over_trees (emptyStanding : TreeStanding Ltr A) m s
    simpa [treeWeight_empty, treeLik_empty] using this.symm
  · have hL := treeLik_pos N m s S
    have hW := treeWeight_pos N m s
    have hd : ((1 / 2 : ℚ) ^ PrunedTree.cost m S * treeLik N m s S : ℚ) ≤ treeWeight N m s :=
      hdom S
    have hdR : (2 : ℝ) ^ (-(PrunedTree.cost m S : ℝ)) * (treeLik N m s S : ℝ) ≤
        (treeWeight N m s : ℝ) := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← one_div, ← one_div_pow]
      have := (Rat.cast_le (K := ℝ)).mpr hd
      push_cast at this
      exact this
    have hLR : (0 : ℝ) < treeLik N m s S := by exact_mod_cast hL
    have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hdR
    rw [Real.logb_mul (by positivity) hLR.ne', Real.logb_rpow (by norm_num) (by norm_num)] at hlog
    linarith

end Kraft

/-! ## 6. The digit emission of a cell -/

section Digits

/-- [definition] **The emission mass of a digit word** `l` after the prefix `pre`: the product of
the binary faces `q(π, b)` at each successive digit prefix `π`. -/
def emit (q : List Bool → Bool → ℚ) : List Bool → List Bool → ℚ
  | _, [] => 1
  | pre, b :: rest => q pre b * emit q (pre ++ [b]) rest

theorem emit_pos {q : List Bool → Bool → ℚ} (hq : ∀ π b, 0 < q π b) :
    ∀ pre l, 0 < emit q pre l
  | _, [] => one_pos
  | pre, b :: rest => mul_pos (hq pre b) (emit_pos hq (pre ++ [b]) rest)

/-- The low `w` digits do not see a multiple of `2^w`. -/
theorem toBits_add_pow (w n k : ℕ) : toBits w (n + 2 ^ w * k) = toBits w n := by
  induction w generalizing k with
  | zero => rfl
  | succ w ih =>
    have e : n + 2 ^ (w + 1) * k = n + 2 ^ w * (2 * k) := by ring
    have hdiv : (n + 2 ^ w * (2 * k)) / 2 ^ w = n / 2 ^ w + 2 * k :=
      Nat.add_mul_div_left n (2 * k) (by positivity)
    have hmod : (n / 2 ^ w + 2 * k) % 2 = n / 2 ^ w % 2 := Nat.add_mul_mod_self_left _ 2 k
    simp only [toBits, e, hdiv, hmod, ih]

theorem toBits_succ_low {w c : ℕ} (hc : c < 2 ^ w) : toBits (w + 1) c = false :: toBits w c := by
  simp [toBits, Nat.div_eq_of_lt hc]

theorem toBits_succ_high {w c : ℕ} (hc : c < 2 ^ w) :
    toBits (w + 1) (2 ^ w + c) = true :: toBits w c := by
  have h1 : (2 ^ w + c) / 2 ^ w = 1 := by
    rw [Nat.add_div_of_dvd_right (dvd_refl _), Nat.div_self (by positivity), Nat.div_eq_of_lt hc]
  have h2 : toBits w (2 ^ w + c) = toBits w c := by
    rw [add_comm, show c + 2 ^ w = c + 2 ^ w * 1 by ring, toBits_add_pow]
  simp [toBits, h1, h2]

/-- [proved-derived; formal-checked] **`digit_emission_normalized`.** For binary faces normalized at
every digit prefix (`q(π, 0) + q(π, 1) = 1`), the cell face `c ↦ ∏_(i<w) q(prefix_i c, bit_i c)`,
the emission mass of the odometer digits `toBits w c`, sums to one over the cells `c < 2^w`, after
any prefix; when the faces are positive, so is every cell face. -/
theorem digit_emission_normalized (q : List Bool → Bool → ℚ)
    (hs : ∀ π, q π false + q π true = 1) (w : ℕ) :
    ((∀ π b, 0 < q π b) → ∀ pre c, 0 < emit q pre (toBits w c)) ∧
      ∀ pre, ∑ c ∈ Finset.range (2 ^ w), emit q pre (toBits w c) = 1 := by
  refine ⟨fun hq pre c => emit_pos hq pre _, ?_⟩
  induction w with
  | zero => intro pre; simp [toBits, emit]
  | succ w ih =>
    intro pre
    rw [show 2 ^ (w + 1) = 2 ^ w + 2 ^ w by ring, Finset.sum_range_add]
    have hlo : ∑ c ∈ Finset.range (2 ^ w), emit q pre (toBits (w + 1) c) =
        q pre false * ∑ c ∈ Finset.range (2 ^ w), emit q (pre ++ [false]) (toBits w c) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [toBits_succ_low (Finset.mem_range.mp hc), emit]
    have hhi : ∑ c ∈ Finset.range (2 ^ w), emit q pre (toBits (w + 1) (2 ^ w + c)) =
        q pre true * ∑ c ∈ Finset.range (2 ^ w), emit q (pre ++ [true]) (toBits w c) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [toBits_succ_high (Finset.mem_range.mp hc), emit]
    rw [hlo, hhi, ih, ih, mul_one, mul_one, hs]

theorem ofBits_snoc (l : List Bool) (b : Bool) : ofBits (l ++ [b]) = 2 * ofBits l + b.toNat := by
  induction l with
  | nil => simp [ofBits]
  | cons x l ih =>
    simp only [List.cons_append, ofBits, ih, List.length_append, List.length_singleton, pow_succ]
    ring

theorem emit_eq_zero_of_factor {q : List Bool → Bool → ℚ} :
    ∀ (pre l : List Bool) (i : ℕ) (hi : i < l.length),
      q (pre ++ l.take i) (l[i]'hi) = 0 → emit q pre l = 0
  | _, [], _, hi, _ => absurd hi (by simp)
  | pre, b :: rest, 0, _, h => by simp only [emit]; simp at h; rw [h, zero_mul]
  | pre, b :: rest, i + 1, hi, h => by
    simp only [emit]
    rw [emit_eq_zero_of_factor (pre ++ [b]) rest i (by simpa using hi) (by simpa using h),
      mul_zero]

/-- [proved-derived; formal-checked] **`forced_digits_normalized`: an alphabet that is not a power
of two.** For `K` classes, `0 < K ≤ 2^w`, coded by their `w` odometer digits, let the digit faces be
normalized at every prefix and **forced** where the upper half holds no class: at a prefix `π` whose
upper child's lowest code `ofBits(π ++ [1])·2^(w−|π|−1)` is at least `K`, `q(π, 1) = 0`. Then every
code `c ≥ K` has emission zero, and the cell faces of the `K` classes sum to one. -/
theorem forced_digits_normalized (q : List Bool → Bool → ℚ)
    (hs : ∀ π, q π false + q π true = 1) {K w : ℕ} (hK : 0 < K) (hKw : K ≤ 2 ^ w)
    (hforce : ∀ π : List Bool, π.length < w →
      K ≤ ofBits (π ++ [true]) * 2 ^ (w - π.length - 1) → q π true = 0) :
    (∀ c, K ≤ c → c < 2 ^ w → emit q [] (toBits w c) = 0) ∧
      ∑ c ∈ Finset.range K, emit q [] (toBits w c) = 1 := by
  -- the invariant: the current dyadic cell's lowest code is a class, the full code is not
  have key : ∀ (rest pre : List Bool), pre.length + rest.length = w →
      ofBits pre * 2 ^ (w - pre.length) < K → K ≤ ofBits (pre ++ rest) →
      emit q pre rest = 0 := by
    intro rest
    induction rest with
    | nil =>
      intro pre hlen hlo hhi
      simp only [List.length_nil, add_zero] at hlen
      subst hlen
      simp only [Nat.sub_self, pow_zero, mul_one, List.append_nil] at hlo hhi
      omega
    | cons b rest ih =>
      intro pre hlen hlo hhi
      simp only [List.length_cons] at hlen
      have hlt : pre.length < w := by omega
      simp only [emit]
      by_cases hchild : ofBits (pre ++ [b]) * 2 ^ (w - (pre ++ [b]).length) < K
      · rw [ih (pre ++ [b]) (by simp; omega) hchild (by simpa using hhi), mul_zero]
      · cases b with
        | false =>
          exfalso
          apply hchild
          rw [ofBits_snoc, List.length_append, List.length_singleton]
          have e : w - pre.length = (w - (pre.length + 1)) + 1 := by omega
          rw [e, pow_succ] at hlo
          simp only [Bool.toNat_false, add_zero]
          calc 2 * ofBits pre * 2 ^ (w - (pre.length + 1))
              = ofBits pre * (2 ^ (w - (pre.length + 1)) * 2) := by ring
            _ < K := hlo
        | true =>
          have hz : q pre true = 0 := hforce pre hlt (by
            simp only [List.length_append, List.length_singleton] at hchild
            rw [show w - pre.length - 1 = w - (pre.length + 1) by omega]
            omega)
          rw [hz, zero_mul]
  have hzero : ∀ c, K ≤ c → c < 2 ^ w → emit q [] (toBits w c) = 0 := by
    intro c hc hcw
    refine key _ [] (by simp [toBits_length]) (by simp [ofBits]; exact hK) ?_
    rw [List.nil_append, ofBits_toBits, Nat.mod_eq_of_lt hcw]
    exact hc
  refine ⟨hzero, ?_⟩
  have htot := (digit_emission_normalized q hs w).2 []
  rw [← Finset.sum_range_add_sum_Ico _ hKw] at htot
  have hIco : ∑ c ∈ Finset.Ico K (2 ^ w), emit q [] (toBits w c) = 0 :=
    Finset.sum_eq_zero fun c hc => by
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hc
      exact hzero c h1 h2
  rw [hIco, add_zero] at htot
  exact htot

/-- [proved-derived; formal-checked] **A binary KT face is at least `1/(2n + 2)`**: after `n`
observations, `(n_b + 1/2)/(n + 1) ≥ (1/2)/(n + 1)`. -/
theorem kt_binary_ge (nb n : ℕ) : 1 / (2 * (n : ℚ) + 2) ≤ ktProb nb n 2 := by
  unfold ktProb
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  nlinarith [(Nat.cast_nonneg nb : (0 : ℚ) ≤ nb), (Nat.cast_nonneg n : (0 : ℚ) ≤ n)]

/-- [proved-derived; formal-checked] **`digit_face_ge`.** On a binary landmark tree (the digit's
tree at one digit prefix), if every node of the opened path holds at most `n` observations, the
tree's digit face is at least `1/(2n + 2)` at every depth (`path_face_ge_min`, `kt_binary_ge`). -/
theorem digit_face_ge {Ltr : Type*} [Fintype Ltr] [DecidableEq Ltr]
    (N : TreeStanding Ltr Bool) (D : ℕ) (a : List Ltr) (n : ℕ)
    (hn : ∀ d ≤ D, ∑ b, N (a.take d) b ≤ n) (b : Bool) :
    ∀ d ≤ D, 1 / (2 * (n : ℚ) + 2) ≤ face N D a d b := by
  intro d hd
  refine (path_face_ge_min (kAt N a) (lamAt N D a) D b
    fun d' _ => ⟨(lamAt_mem N D a d').1.le, (lamAt_mem N D a d').2.le⟩).1 _ d hd
    fun d' _ h2 => ?_
  have hk := kt_binary_ge (N (a.take d') b) (∑ b', N (a.take d') b')
  have hm : (∑ b', N (a.take d') b' : ℚ) ≤ n := by exact_mod_cast hn d' h2
  calc 1 / (2 * (n : ℚ) + 2) ≤ 1 / (2 * ((∑ b', N (a.take d') b' : ℕ) : ℚ) + 2) := by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        linarith
    _ ≤ kAt N a d' b := by
        simpa [kAt, ktFace] using hk

/-- [definition] **The executed digit split's numerator**: `2^M q(0)` rounded to the nearest
integer (`round`, ties upward), clamped into `[1, 2^M − 1]`. -/
def splitNumerator (M : ℕ) (q0 : ℚ) : ℤ := max 1 (min (2 ^ M - 1) (round (q0 * 2 ^ M)))

/-- [definition] **The executed digit split** on the lattice `2^(−M)ℤ`: `q̂(0)` is the numerator
over `2^M`, and `q̂(1) = 1 − q̂(0)`. -/
def executedSplit (M : ℕ) (q0 : ℚ) (b : Bool) : ℚ :=
  if b then 1 - (splitNumerator M q0 : ℚ) / 2 ^ M else (splitNumerator M q0 : ℚ) / 2 ^ M

/-- [proved-derived; formal-checked] **`executed_split_laws`.** At `M ≥ 1`:
* the numerator lies in `[1, 2^M − 1]`, so both executed digit faces are positive and they sum to
  one;
* when the exact `q(0)` lies in `[2^(−M), 1 − 2^(−M)]`, the clamp is inactive and each executed
  face is within `2^(−M−1)` of the exact one, `|q̂(b) − q(b)| ≤ 2^(−M−1)`.

So the executed cell face (the emission of `q̂` along the odometer digits) is positive and
normalized over the cells (`digit_emission_normalized`). -/
theorem executed_split_laws {M : ℕ} (hM : 1 ≤ M) (q0 : ℚ) :
    (1 ≤ splitNumerator M q0 ∧ splitNumerator M q0 ≤ 2 ^ M - 1) ∧
      (∀ b, 0 < executedSplit M q0 b) ∧
      executedSplit M q0 false + executedSplit M q0 true = 1 ∧
      (1 / 2 ^ M ≤ q0 → q0 ≤ 1 - 1 / 2 ^ M →
        |executedSplit M q0 false - q0| ≤ 1 / 2 ^ (M + 1) ∧
          |executedSplit M q0 true - (1 - q0)| ≤ 1 / 2 ^ (M + 1)) := by
  have h2M : (2 : ℤ) ≤ 2 ^ M := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hM
  have hbounds : 1 ≤ splitNumerator M q0 ∧ splitNumerator M q0 ≤ 2 ^ M - 1 := by
    unfold splitNumerator
    exact ⟨le_max_left _ _, max_le (by omega) (min_le_left _ _)⟩
  have hP : (0 : ℚ) < 2 ^ M := by positivity
  have hlo : (1 : ℚ) ≤ splitNumerator M q0 := by exact_mod_cast hbounds.1
  have hhi : (splitNumerator M q0 : ℚ) ≤ 2 ^ M - 1 := by exact_mod_cast hbounds.2
  refine ⟨hbounds, fun b => ?_, by simp [executedSplit], fun hq1 hq2 => ?_⟩
  · cases b
    · simp only [executedSplit, Bool.false_eq_true, if_false]
      exact div_pos (by linarith) hP
    · simp only [executedSplit, if_true, sub_pos]
      rw [div_lt_one hP]
      linarith
  · set x := q0 * 2 ^ M with hx
    have hx1 : 1 ≤ x := by
      rw [hx]; rw [div_le_iff₀ hP] at hq1; linarith
    have hx2 : x ≤ 2 ^ M - 1 := by
      have : q0 * 2 ^ M ≤ (1 - 1 / 2 ^ M) * 2 ^ M := mul_le_mul_of_nonneg_right hq2 hP.le
      rw [hx]; rw [sub_mul, one_div, inv_mul_cancel₀ hP.ne', one_mul] at this; linarith
    have hr := abs_sub_round x
    rw [abs_le] at hr
    have hr1 : (1 : ℤ) ≤ round x := by
      have : (0 : ℚ) < round x := by linarith [hr.2]
      have : (0 : ℤ) < round x := by exact_mod_cast this
      omega
    have hr2 : round x ≤ (2 : ℤ) ^ M - 1 := by
      have : ((round x : ℤ) : ℚ) < 2 ^ M := by linarith [hr.1]
      have : round x < (2 : ℤ) ^ M := by exact_mod_cast this
      omega
    have hnum : splitNumerator M q0 = round x := by
      unfold splitNumerator
      rw [← hx, min_eq_right hr2, max_eq_right hr1]
    have hres : |executedSplit M q0 false - q0| ≤ 1 / 2 ^ (M + 1) := by
      simp only [executedSplit, Bool.false_eq_true, if_false, hnum]
      have e : (round x : ℚ) / 2 ^ M - q0 = -(x - round x) / 2 ^ M := by
        rw [hx]; field_simp; ring
      rw [e, abs_div, abs_neg, abs_of_pos hP, div_le_iff₀ hP, pow_succ]
      have : (1 : ℚ) / (2 ^ M * 2) * 2 ^ M = 1 / 2 := by field_simp
      rw [this]
      exact abs_le.mpr hr
    refine ⟨hres, ?_⟩
    have e : executedSplit M q0 true - (1 - q0) = -(executedSplit M q0 false - q0) := by
      simp only [executedSplit, Bool.false_eq_true, if_false, if_true]; ring
    rw [e, abs_neg]
    exact hres

/-- [definition] **One split of a cell at the digit face `s`**: the left child keeps the lower
`s`-share of the width and the right child the rest, with no gap. -/
def splitChild (s : ℚ) : Hand → Cell → Cell
  | .left, cell => ⟨cell.lower, cell.lower + s * cell.width⟩
  | .right, cell => ⟨cell.lower + s * cell.width, cell.upper⟩

/-- [definition] **The face cell of a digit word**: the cell descended along the digits, each digit
splitting at the digit face of its prefix (the arithmetic-coding interval of the emission). -/
def faceCell (q : List Bool → Bool → ℚ) : List Bool → List Bool → Cell → Cell
  | _, [], cell => cell
  | pre, b :: rest, cell => faceCell q (pre ++ [b]) rest (splitChild (q pre false) (handOf b) cell)

/-- [proved-derived; formal-checked] **`face_cell_width`: the cell's face is the width of its
descended interval.** For binary faces normalized at every prefix, the left and right children
abut (no gap) with widths `q(π, 0)·w` and `q(π, 1)·w`, and the cell descended along a digit word
has width `emit q pre l · w`; over the odometer digits of the cells `c < 2^w` from the unit cell,
those widths are the cell faces and sum to one.

`FractalPacking`'s `descend` keeps the same address word (`Hand`, newest restriction first) but its
children are fixed thirds separated by a gap of one third (`child_width`, `sibling_gap`): its form
does not admit unequal splits, so the face cells are this owner's `splitChild`, not `descend`. -/
theorem face_cell_width (q : List Bool → Bool → ℚ) (hs : ∀ π, q π false + q π true = 1) :
    (∀ (π : List Bool) (cell : Cell),
        (splitChild (q π false) Hand.left cell).upper =
          (splitChild (q π false) Hand.right cell).lower ∧
        (splitChild (q π false) Hand.left cell).width = q π false * cell.width ∧
        (splitChild (q π false) Hand.right cell).width = q π true * cell.width) ∧
      ∀ pre l cell, (faceCell q pre l cell).width = emit q pre l * cell.width := by
  have hsplit : ∀ (π : List Bool) (b : Bool) (cell : Cell),
      (splitChild (q π false) (handOf b) cell).width = q π b * cell.width := by
    intro π b cell
    have ht : q π true = 1 - q π false := by linarith [hs π]
    cases b
    · simp only [splitChild, handOf, Bool.false_eq_true, if_false, Cell.width]; ring
    · simp only [splitChild, handOf, if_true, Cell.width, ht]; ring
  refine ⟨fun π cell => ⟨rfl, hsplit π false cell, hsplit π true cell⟩, ?_⟩
  intro pre l
  induction l generalizing pre with
  | nil => intro cell; simp [faceCell, emit]
  | cons b rest ih =>
    intro cell
    rw [faceCell, ih, emit, hsplit]
    ring

/-- [proved-derived; formal-checked] **`cell_faces_partition`.** From the unit cell, the face cell
of each cell's odometer digits has width equal to the cell's face, and over the cells `c < 2^w`
those widths sum to one (`face_cell_width`, `digit_emission_normalized`). With the executed digit
split at `M ≥ 1` (`executed_split_laws`) every cell face is positive: the executed face is a
dyadic partition of the unit cell, exactly normalized. -/
theorem cell_faces_partition (q : List Bool → Bool → ℚ) (hs : ∀ π, q π false + q π true = 1)
    (w : ℕ) :
    (∀ c, (faceCell q [] (toBits w c) root).width = emit q [] (toBits w c)) ∧
      ∑ c ∈ Finset.range (2 ^ w), (faceCell q [] (toBits w c) root).width = 1 ∧
      ∀ {M : ℕ}, 1 ≤ M → ∀ q0 : List Bool → ℚ,
        (∀ c, 0 < emit (fun π b => executedSplit M (q0 π) b) [] (toBits w c)) ∧
          ∑ c ∈ Finset.range (2 ^ w),
            emit (fun π b => executedSplit M (q0 π) b) [] (toBits w c) = 1 := by
  have hw : ∀ c, (faceCell q [] (toBits w c) root).width = emit q [] (toBits w c) := fun c => by
    rw [(face_cell_width q hs).2]
    simp [root, Cell.width]
  refine ⟨hw, ?_, ?_⟩
  · rw [Finset.sum_congr rfl fun c _ => hw c]
    exact (digit_emission_normalized q hs w).2 []
  · intro M hM q0
    have hs' : ∀ π, executedSplit M (q0 π) false + executedSplit M (q0 π) true = 1 :=
      fun π => (executed_split_laws hM (q0 π)).2.2.1
    exact ⟨(digit_emission_normalized _ hs' w).1
        (fun π b => (executed_split_laws hM (q0 π)).2.1 b) [],
      (digit_emission_normalized _ hs' w).2 []⟩

/-- [proved-derived; formal-checked] **`digit_log_residual`.** For a face `q ≥ μ > 0` and an
executed face `q̂` with `|q̂ − q| ≤ ε < μ`:
* `q̂ > 0` and `|ln q̂ − ln q| ≤ ε/(μ − ε)`;
* upward (`q ≤ q̂`) the residual is at most `ε/μ`.
The downward direction needs `μ − ε`: `ln(q/q̂) ≤ (q − q̂)/q̂`, and `q̂` may lie below `μ`. -/
theorem digit_log_residual {q qh μ ε : ℝ} (hμ : 0 < μ) (hq : μ ≤ q) (hεμ : ε < μ)
    (he : |qh - q| ≤ ε) :
    0 < qh ∧ |Real.log qh - Real.log q| ≤ ε / (μ - ε) ∧
      (q ≤ qh → Real.log qh - Real.log q ≤ ε / μ) := by
  obtain ⟨he1, he2⟩ := abs_le.mp he
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) he
  have hq0 : 0 < q := by linarith
  have hqh : μ - ε ≤ qh := by linarith
  have hqh0 : 0 < qh := by linarith
  have hme : 0 < μ - ε := by linarith
  have hup : Real.log qh - Real.log q ≤ ε / μ := by
    rw [← Real.log_div hqh0.ne' hq0.ne']
    calc Real.log (qh / q) ≤ qh / q - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = (qh - q) / q := by field_simp
      _ ≤ ε / q := div_le_div_of_nonneg_right (by linarith) hq0.le
      _ ≤ ε / μ := div_le_div_of_nonneg_left hε0 hμ hq
  have hdown : Real.log q - Real.log qh ≤ ε / (μ - ε) := by
    rw [← Real.log_div hq0.ne' hqh0.ne']
    calc Real.log (q / qh) ≤ q / qh - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = (q - qh) / qh := by field_simp
      _ ≤ ε / qh := div_le_div_of_nonneg_right (by linarith) hqh0.le
      _ ≤ ε / (μ - ε) := div_le_div_of_nonneg_left hε0 hme hqh
  have hmono : ε / μ ≤ ε / (μ - ε) := div_le_div_of_nonneg_left hε0 hme (by linarith)
  refine ⟨hqh0, abs_le.mpr ⟨by linarith, by linarith⟩, fun _ => hup⟩

/-- [proved-derived; formal-checked] **`digit_log_residual_kt`: the per-digit residual at the
executed grain.** For a digit face `q ≥ 1/(2n + 2)` (`digit_face_ge`), an executed face with
`|q̂ − q| ≤ 2^(−M−1)` (`executed_split_laws`), and `2n + 2 ≤ 2^M`:
* `|ln q̂ − ln q| ≤ (2n + 2)/2^M`, twice `2^(−M−1)(2n + 2)`; in `log₂`, divide by `ln 2`;
* upward (`q ≤ q̂`), `ln q̂ − ln q ≤ (2n + 2)/2^(M+1)`.
The downward direction does not satisfy `2^(−M−1)(2n + 2)` (`host_digit_bound_fails_downward`). -/
theorem digit_log_residual_kt {q qh : ℝ} {n M : ℕ} (hq : 1 / (2 * (n : ℝ) + 2) ≤ q)
    (he : |qh - q| ≤ 1 / 2 ^ (M + 1)) (hM : 2 * n + 2 ≤ 2 ^ M) :
    |Real.log qh - Real.log q| ≤ (2 * n + 2) / 2 ^ M ∧
      (q ≤ qh → Real.log qh - Real.log q ≤ (2 * n + 2) / 2 ^ (M + 1)) := by
  set K : ℝ := 2 * n + 2 with hK
  have hK0 : 0 < K := by positivity
  have hP0 : (0 : ℝ) < 2 ^ M := by positivity
  have hKP : K ≤ 2 ^ M := by rw [hK]; exact_mod_cast hM
  have hεμ : (1 : ℝ) / 2 ^ (M + 1) < 1 / K := by
    rw [div_lt_div_iff₀ (by positivity) hK0, pow_succ]; linarith
  obtain ⟨_, habs, hup⟩ := digit_log_residual (by positivity) hq hεμ he
  refine ⟨habs.trans ?_, fun h => (hup h).trans (le_of_eq ?_)⟩
  · have hb : 0 < 1 / K - 1 / 2 ^ (M + 1) := by linarith [hεμ]
    rw [div_le_div_iff₀ hb hP0]
    have e1 : 1 / (2 : ℝ) ^ (M + 1) * 2 ^ M = 1 / 2 := by rw [pow_succ]; field_simp
    have e2 : K * (1 / K - 1 / 2 ^ (M + 1)) = 1 - K / 2 ^ (M + 1) := by
      rw [mul_sub, mul_one_div_cancel hK0.ne', mul_one_div]
    rw [e1, e2]
    have : K / 2 ^ (M + 1) ≤ 1 / 2 := by
      rw [pow_succ, div_le_iff₀ (by positivity)]; linarith
    linarith
  · field_simp

/-- [proved-derived; formal-checked] **`host_digit_bound_fails_downward`.** The per-digit bound
`2^(−M−1)(2n + 2)` (in `ln`; times `log₂ e` in `log₂`) fails when rounding moves the face down:
at `M = 7` and `n = 42` (`2n + 2 = 86 ≤ 128`), the exact face `q = 1/86` lies in
`[2^(−7), 1 − 2^(−7)]` and at the KT floor `1/(2n + 2)`, its executed split is `q̂ = 1/128`,
`|q̂ − q| = 21/5504 ≤ 2^(−8)`, and yet `ln q − ln q̂ = ln(64/43) > 43/128 = 2^(−8)·86`, decided by
`exp(43/128) ≤ 1 + 43/128 + (43/128)² = 23737/16384 < 64/43`. -/
theorem host_digit_bound_fails_downward :
    executedSplit 7 (1 / 86) false = 1 / 128 ∧
      ((1 : ℚ) / 2 ^ 7 ≤ 1 / 86 ∧ (1 / 86 : ℚ) ≤ 1 - 1 / 2 ^ 7) ∧
      (1 : ℚ) / (2 * 42 + 2) ≤ 1 / 86 ∧ 2 * 42 + 2 ≤ 2 ^ 7 ∧
      |(1 / 128 : ℚ) - 1 / 86| ≤ 1 / 2 ^ (7 + 1) ∧
      (2 * 42 + 2 : ℝ) / 2 ^ (7 + 1) < Real.log (1 / 86) - Real.log (1 / 128) ∧
      (2 * 42 + 2 : ℝ) / 2 ^ (7 + 1) / Real.log 2 <
        Real.logb 2 (1 / 86) - Real.logb 2 (1 / 128) := by
  have hr : round ((1 / 86 : ℚ) * 2 ^ 7) = 1 := by
    rw [round_eq, Int.floor_eq_iff]
    norm_num
  have hsplit : executedSplit 7 (1 / 86) false = 1 / 128 := by
    simp only [executedSplit, splitNumerator, hr, Bool.false_eq_true, if_false]
    norm_num
  have hlog : (2 * 42 + 2 : ℝ) / 2 ^ (7 + 1) < Real.log (1 / 86) - Real.log (1 / 128) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    rw [show (1 / 86 : ℝ) / (1 / 128) = 64 / 43 by norm_num,
      show (2 * 42 + 2 : ℝ) / 2 ^ (7 + 1) = 43 / 128 by norm_num]
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have hb := Real.abs_exp_sub_one_sub_id_le (x := 43 / 128) (by
      rw [abs_of_pos (by norm_num)]; norm_num)
    have := (abs_le.mp hb).2
    have : Real.exp (43 / 128) ≤ 1 + 43 / 128 + (43 / 128) ^ 2 := by linarith
    calc Real.exp (43 / 128) ≤ 1 + 43 / 128 + (43 / 128) ^ 2 := this
      _ < 64 / 43 := by norm_num
  refine ⟨hsplit, ⟨by norm_num, by norm_num⟩, by norm_num, by norm_num, ?_, hlog, ?_⟩
  · rw [abs_le]; constructor <;> norm_num
  · rw [Real.logb, Real.logb, ← sub_div]
    exact div_lt_div_of_pos_right hlog (Real.log_pos (by norm_num))

end Digits

/-! ## 6′. The lattice chart: the executed path on `2^(−M)ℤ` -/

section Lattice

/-- [definition] **The lattice path from depth `d` with `m` levels below** (the digit `0`, Rust
`hnn::landmark::Landmarks`): the leaf reads its KT face rounded to the lattice `2^(−M)ℤ`,
`⟦k_d⟧`, and a node its rounded mixture `⟦λ̂_d k_d + (1 − λ̂_d) q̂_(d+1)⟧`, each by `executedSplit`
(nearest, ties up, clamped into `[2^(−M), 1 − 2^(−M)]`). The first unfounded depth reads the prior
(`k = 1/2`, which rounds to itself), a forced depth has `λ̂ = 0`. -/
def latticeFrom (M : ℕ) (k lam : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, d => executedSplit M (k d) false
  | m + 1, d => executedSplit M (lam d * k d + (1 - lam d) * latticeFrom M k lam m (d + 1)) false

/-- [definition] **The exact path of one digit**: the path face `mixFrom` at one class
(`exactFrom_eq_mixFrom`). -/
def exactFrom (k lam : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, d => k d
  | m + 1, d => lam d * k d + (1 - lam d) * exactFrom k lam m (d + 1)

theorem exactFrom_eq_mixFrom {A : Type*} (k : ℕ → A → ℚ) (lam : ℕ → ℚ) (c : A) :
    ∀ m d, exactFrom (fun d => k d c) lam m d = mixFrom k lam m d c
  | 0, _ => rfl
  | m + 1, d => by simp only [exactFrom, mixFrom, exactFrom_eq_mixFrom k lam c m (d + 1)]

/-- [definition] **The value the lattice path's top rounds**: the digit's executed split is
`executedSplit M (latticeTop …)` (`latticeFrom_top`). -/
def latticeTop (M : ℕ) (k lam : ℕ → ℚ) : ℕ → ℚ
  | 0 => k 0
  | m + 1 => lam 0 * k 0 + (1 - lam 0) * latticeFrom M k lam m 1

theorem latticeFrom_top (M : ℕ) (k lam : ℕ → ℚ) (m : ℕ) :
    latticeFrom M k lam m 0 = executedSplit M (latticeTop M k lam m) false := by
  cases m <;> rfl

theorem latticeFrom_split (M : ℕ) (k lam : ℕ → ℚ) :
    ∀ m d, ∃ x, latticeFrom M k lam m d = executedSplit M x false
  | 0, d => ⟨k d, rfl⟩
  | _ + 1, _ => ⟨_, rfl⟩

theorem executedSplit_false (M : ℕ) (x : ℚ) :
    executedSplit M x false = (splitNumerator M x : ℚ) / 2 ^ M := by
  simp [executedSplit]

/-- [proved-derived; formal-checked] **`lattice_path_laws`.** At `M ≥ 1`, for any KT faces and
**any** stop weights (the lattice chart's `λ̂`, or anything else):
* every face of the lattice path is a lattice point `n/2^M` with `1 ≤ n ≤ 2^M − 1`;
* the digit's executed split `(q̂_0, 1 − q̂_0)` is positive and sums to one;
* over the odometer digits of the cells `c < 2^w`, each digit prefix `π` with its own path, the
  cells' executed faces are positive and sum to one (`cell_faces_partition`). -/
theorem lattice_path_laws {M : ℕ} (hM : 1 ≤ M) (k lam : ℕ → ℚ) (D : ℕ) :
    (∀ m d, ∃ n : ℤ, 1 ≤ n ∧ n ≤ 2 ^ M - 1 ∧ latticeFrom M k lam m d = n / 2 ^ M) ∧
      (∀ b, 0 < executedSplit M (latticeTop M k lam D) b) ∧
      executedSplit M (latticeTop M k lam D) false +
          executedSplit M (latticeTop M k lam D) true = 1 ∧
      ∀ (w : ℕ) (kπ lamπ : List Bool → ℕ → ℚ),
        (∀ c, 0 < emit (fun π b => executedSplit M (latticeTop M (kπ π) (lamπ π) D) b) []
          (toBits w c)) ∧
          ∑ c ∈ Finset.range (2 ^ w),
            emit (fun π b => executedSplit M (latticeTop M (kπ π) (lamπ π) D) b) []
              (toBits w c) = 1 := by
  refine ⟨fun m d => ?_, (executed_split_laws hM _).2.1, (executed_split_laws hM _).2.2.1,
    fun w kπ lamπ => ((cell_faces_partition (fun _ _ => (1 / 2 : ℚ)) (fun _ => by norm_num)
      w).2.2 hM fun π => latticeTop M (kπ π) (lamπ π) D)⟩
  obtain ⟨x, hx⟩ := latticeFrom_split M k lam m d
  obtain ⟨⟨h1, h2⟩, -⟩ := executed_split_laws hM x
  exact ⟨splitNumerator M x, h1, h2, by rw [hx, executedSplit_false]⟩

/-- Every lattice face lies in `[2^(−M), 1 − 2^(−M)]`. -/
theorem lattice_mem {M : ℕ} (hM : 1 ≤ M) (k lam : ℕ → ℚ) (m d : ℕ) :
    1 / 2 ^ M ≤ latticeFrom M k lam m d ∧ latticeFrom M k lam m d ≤ 1 - 1 / 2 ^ M := by
  obtain ⟨n, h1, h2, hq⟩ := (lattice_path_laws hM k lam 0).1 m d
  have hP : (0 : ℚ) < 2 ^ M := by positivity
  have h1' : (1 : ℚ) ≤ n := by exact_mod_cast h1
  have h2' : (n : ℚ) ≤ 2 ^ M - 1 := by exact_mod_cast h2
  rw [hq]
  constructor
  · exact div_le_div_of_nonneg_right h1' hP.le
  · rw [div_le_iff₀ hP, sub_mul, one_div_mul_cancel hP.ne']
    linarith

/-- Rounding to nearest never crosses a lattice point `N/2^M ≤ x` below it. -/
theorem executedSplit_ge {M : ℕ} {N : ℤ} {x : ℚ} (hN : N ≤ 2 ^ M - 1) (hx : (N : ℚ) / 2 ^ M ≤ x) :
    (N : ℚ) / 2 ^ M ≤ executedSplit M x false := by
  have hP : (0 : ℚ) < 2 ^ M := by positivity
  rw [executedSplit_false]
  apply div_le_div_of_nonneg_right _ hP.le
  have hfl : N ≤ ⌊x * 2 ^ M⌋ := by
    rw [Int.le_floor]
    rwa [div_le_iff₀ hP] at hx
  have hround : ⌊x * 2 ^ M⌋ ≤ round (x * 2 ^ M) := by
    rw [round_eq]
    exact Int.floor_mono (by linarith)
  have : N ≤ splitNumerator M x := by
    unfold splitNumerator
    exact le_max_of_le_right (le_min hN (hfl.trans hround))
  exact_mod_cast this

/-- [proved-derived; formal-checked] **`lattice_path_floor`.** When every KT face on the path is
at least `μ` (`digit_face_ge`: `μ = 1/(2n + 2)`) and every stop weight lies in `[0, 1]`, every
lattice face is at least `⌊2^M μ⌋/2^M` (when that numerator is at most `2^M − 1`): a convex
combination of values at least a lattice point rounds to at least it. The floor `μ̂` of the widths'
rule (Rust `landmark::face_bits`) does not decay down the path. -/
theorem lattice_path_floor {M : ℕ} (k lam : ℕ → ℚ) {μ : ℚ}
    (hk : ∀ d, μ ≤ k d) (hl : ∀ d, 0 ≤ lam d ∧ lam d ≤ 1)
    (hμ : ⌊μ * 2 ^ M⌋ ≤ 2 ^ M - 1) :
    ∀ m d, (⌊μ * 2 ^ M⌋ : ℚ) / 2 ^ M ≤ latticeFrom M k lam m d := by
  have hP : (0 : ℚ) < 2 ^ M := by positivity
  have hfloor : (⌊μ * 2 ^ M⌋ : ℚ) / 2 ^ M ≤ μ := by
    rw [div_le_iff₀ hP]
    exact Int.floor_le _
  intro m
  induction m with
  | zero => intro d; exact executedSplit_ge hμ (hfloor.trans (hk d))
  | succ m ih =>
    intro d
    refine executedSplit_ge hμ ?_
    have h1 := hfloor.trans (hk d)
    have h2 := ih (d + 1)
    obtain ⟨hl0, hl1⟩ := hl d
    nlinarith

/-- [proved-derived; formal-checked] **`lattice_path_deviation`: the absolute deviation adds down
the path.** For KT faces in `[2^(−M), 1 − 2^(−M)]` and stop weights `λ, λ̂ ∈ [0, 1]`, the lattice
path under `λ̂` stays within `(m + 1) 2^(−M−1) + Σ_(i<m) |λ̂_(d+i) − λ_(d+i)|` of the exact path under
`λ`: convex combinations do not amplify a deviation, and each level adds its rounding. With the
stop weights rounded on the lattice too, `|q̂_0 − q_0| ≤ (2D + 1) 2^(−M−1)`. -/
theorem lattice_path_deviation {M : ℕ} (hM : 1 ≤ M) (k lam lamh : ℕ → ℚ)
    (hk : ∀ d, 1 / 2 ^ M ≤ k d ∧ k d ≤ 1 - 1 / 2 ^ M)
    (hl : ∀ d, 0 ≤ lam d ∧ lam d ≤ 1) (hlh : ∀ d, 0 ≤ lamh d ∧ lamh d ≤ 1) :
    ∀ m d, |latticeFrom M k lamh m d - exactFrom k lam m d| ≤
      ((m : ℚ) + 1) / 2 ^ (M + 1) + ∑ i ∈ Finset.range m, |lamh (d + i) - lam (d + i)| := by
  intro m
  induction m with
  | zero =>
    intro d
    obtain ⟨h1, h2⟩ := hk d
    have := ((executed_split_laws hM (k d)).2.2.2 h1 h2).1
    simpa [latticeFrom, exactFrom] using this
  | succ m ih =>
    intro d
    set qh := latticeFrom M k lamh m (d + 1) with hqh
    set q := exactFrom k lam m (d + 1) with hq
    obtain ⟨hq1, hq2⟩ := lattice_mem hM k lamh m (d + 1)
    obtain ⟨hk1, hk2⟩ := hk d
    obtain ⟨hl0, hl1⟩ := hl d
    obtain ⟨hh0, hh1⟩ := hlh d
    set v := lamh d * k d + (1 - lamh d) * qh with hv
    have hv1 : 1 / 2 ^ M ≤ v := by rw [hv]; nlinarith
    have hv2 : v ≤ 1 - 1 / 2 ^ M := by rw [hv]; nlinarith
    have hround := ((executed_split_laws hM v).2.2.2 hv1 hv2).1
    have hih := ih (d + 1)
    have hkq : |k d - qh| ≤ 1 := by
      rw [abs_le]
      have : (0 : ℚ) < 1 / 2 ^ M := by positivity
      constructor <;> linarith
    have hmix : |v - (lam d * k d + (1 - lam d) * q)| ≤ |lamh d - lam d| + |qh - q| := by
      have e : v - (lam d * k d + (1 - lam d) * q) =
          (lamh d - lam d) * (k d - qh) + (1 - lam d) * (qh - q) := by rw [hv]; ring
      rw [e]
      calc |(lamh d - lam d) * (k d - qh) + (1 - lam d) * (qh - q)|
          ≤ |(lamh d - lam d) * (k d - qh)| + |(1 - lam d) * (qh - q)| := abs_add_le _ _
        _ = |lamh d - lam d| * |k d - qh| + (1 - lam d) * |qh - q| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hl1)]
        _ ≤ |lamh d - lam d| * 1 + 1 * |qh - q| := by
          have ha := abs_nonneg (lamh d - lam d)
          have hb := abs_nonneg (qh - q)
          nlinarith [mul_le_mul_of_nonneg_left hkq ha, mul_nonneg hl0 hb]
        _ = |lamh d - lam d| + |qh - q| := by ring
    have hsum : ∑ i ∈ Finset.range (m + 1), |lamh (d + i) - lam (d + i)| =
        ∑ i ∈ Finset.range m, |lamh (d + 1 + i) - lam (d + 1 + i)| + |lamh d - lam d| := by
      rw [Finset.sum_range_succ']
      simp only [add_zero]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show d + (i + 1) = d + 1 + i by omega]
    have e : latticeFrom M k lamh (m + 1) d - exactFrom k lam (m + 1) d =
        (executedSplit M v false - v) + (v - (lam d * k d + (1 - lam d) * q)) := by
      simp only [latticeFrom, exactFrom, hv, hqh, hq]
      ring
    rw [e, hsum]
    push_cast
    calc |(executedSplit M v false - v) + (v - (lam d * k d + (1 - lam d) * q))|
        ≤ |executedSplit M v false - v| + |v - (lam d * k d + (1 - lam d) * q)| := abs_add_le _ _
      _ ≤ 1 / 2 ^ (M + 1) + (|lamh d - lam d| + |qh - q|) := add_le_add hround hmix
      _ ≤ 1 / 2 ^ (M + 1) + (|lamh d - lam d| + (((m : ℚ) + 1) / 2 ^ (M + 1) +
            ∑ i ∈ Finset.range m, |lamh (d + 1 + i) - lam (d + 1 + i)|)) := by linarith
      _ = ((m : ℚ) + 1 + 1) / 2 ^ (M + 1) + (∑ i ∈ Finset.range m,
            |lamh (d + 1 + i) - lam (d + 1 + i)| + |lamh d - lam d|) := by ring

/-- [proved-derived; formal-checked] **`mix_ratio_bound`: the mixture moves by at most the
factors of its two inputs.** For the path mixture `(β k + q)/(1 + β) = λ k + (1 − λ) q`
(`λ = β/(1 + β)`, `lamAt_eq_beta`), if `β̂` lies within the factor `ρ_β ≥ 1` of `β` and `q̂` within
`ρ_q ≥ 1` of `q`, the mixture of `(β̂, q̂)` lies within `ρ_β ρ_q` of that of `(β, q)`. In logarithms,
`|ln q̂_d − ln q_d| ≤ |ln β̂_d − ln β_d| + |ln q̂_(d+1) − ln q_(d+1)|`: down the path the chart's drift
adds, never compounds. -/
theorem mix_ratio_bound {k β βh q qh ρβ ρq : ℚ} (hk : 0 ≤ k) (hβ : 0 < β) (hβh : 0 < βh)
    (hq : 0 < q) (hqh : 0 < qh) (hρβ : 1 ≤ ρβ) (hρq : 1 ≤ ρq)
    (h1 : βh ≤ ρβ * β) (h2 : β ≤ ρβ * βh) (h3 : qh ≤ ρq * q) (h4 : q ≤ ρq * qh) :
    (βh * k + qh) / (1 + βh) ≤ ρβ * ρq * ((β * k + q) / (1 + β)) ∧
      (β * k + q) / (1 + β) ≤ ρβ * ρq * ((βh * k + qh) / (1 + βh)) := by
  have key : ∀ {b bh p ph : ℚ}, 0 < b → 0 < bh → 0 < p → 0 < ph → bh ≤ ρβ * b → b ≤ ρβ * bh →
      ph ≤ ρq * p → (bh * k + ph) / (1 + bh) ≤ ρβ * ρq * ((b * k + p) / (1 + b)) := by
    intro b bh p ph hb hbh hp hph e1 e2 e3
    rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by linarith)]
    have s1 : bh * k + ph ≤ ρq * (bh * k + p) := by
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hρq) hbh.le) hk]
    have s2 : (bh * k + p) * (1 + b) ≤ ρβ * ((b * k + p) * (1 + bh)) := by
      nlinarith [mul_le_mul_of_nonneg_right e1 hk, mul_le_mul_of_nonneg_right e2 hp.le,
        mul_nonneg (sub_nonneg.2 hρβ) (mul_nonneg (mul_nonneg hb.le hbh.le) hk),
        mul_nonneg (sub_nonneg.2 hρβ) hp.le]
    calc (bh * k + ph) * (1 + b) ≤ ρq * (bh * k + p) * (1 + b) :=
          mul_le_mul_of_nonneg_right s1 (by linarith)
      _ = ρq * ((bh * k + p) * (1 + b)) := by ring
      _ ≤ ρq * (ρβ * ((b * k + p) * (1 + bh))) :=
          mul_le_mul_of_nonneg_left s2 (by linarith)
      _ = ρβ * ρq * (b * k + p) * (1 + bh) := by ring
  exact ⟨key hβ hβh hq hqh h1 h2 h3, key hβh hβ hqh hq h2 h1 h4⟩

/-- [proved-derived; formal-checked] **`weight_log_lipschitz`.** The node weight `(E + P)/2` moves
by at most the factor by which the split mass `P` moves: `ln(E + e^y)` is 1-Lipschitz in `y`. So
a node's code length drifts from the ideal by at most its children's drift and its own rounding
(`lattice_node_telescope`). -/
theorem weight_log_lipschitz {E P Ph ρ : ℚ} (hE : 0 < E) (hρ : 1 ≤ ρ) (h1 : Ph ≤ ρ * P)
    (h2 : P ≤ ρ * Ph) :
    E + Ph ≤ ρ * (E + P) ∧ E + P ≤ ρ * (E + Ph) := by
  constructor <;> nlinarith

/-- [proved-derived; formal-checked] **`lattice_step_telescope`: one executed step at a node.**
With the carried `β = E/P` (`P` the executed split mass, the child's executed faces multiplied), a
KT face `k` and the child's executed face `x`, the step `E' = E k`, `P' = P x/(1 − r)` with a
rebase's relative residual `r ∈ [0, 1)`:
* the mixture `(β k + x)/(1 + β)` is `(E' + (1 − r) P')/(E + P)`, the weight's ratio times a factor
  `γ ∈ [1 − r, 1]`;
* the carried ratio is `β' = β k/x · (1 − r)` (the deposit's step on the lattice face). -/
theorem lattice_step_telescope {E P k x r : ℚ} (hE : 0 < E) (hP : 0 < P) (hk : 0 < k)
    (hx : 0 < x) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (E / P * k + x) / (1 + E / P) = (E * k + (1 - r) * (P * x / (1 - r))) / (E + P) ∧
      E * k / (P * x / (1 - r)) = E / P * k / x * (1 - r) ∧
      1 - r ≤ (E * k + (1 - r) * (P * x / (1 - r))) / (E * k + P * x / (1 - r)) ∧
      (E * k + (1 - r) * (P * x / (1 - r))) / (E * k + P * x / (1 - r)) ≤ 1 := by
  have hr : (0 : ℚ) < 1 - r := by linarith
  have hb : 0 < P * x / (1 - r) := by positivity
  have ha : 0 < E * k := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
  · rw [le_div_iff₀ (by linarith)]
    nlinarith
  · rw [div_le_one (by linarith)]
    nlinarith

/-- [proved-derived; formal-checked] **`lattice_node_telescope`: a node over its passage.** Over
`n` steps the product of the node's mixtures (its executed faces before their own rounding) is the
weight's ratio `(E_n + P_n)/(E_0 + P_0)` times the rebases' factors `γ_t ∈ [1 − r_t, 1]`: the
executed tree is the ideal tree's recursion on the executed quantities, so its drift is the
rounding and rebases summed over the subtree, never compounded. -/
theorem lattice_node_telescope (E P k x r : ℕ → ℚ) (hE : ∀ t, 0 < E t) (hP : ∀ t, 0 < P t)
    (hr : ∀ t, r t < 1) (hEs : ∀ t, E (t + 1) = E t * k t)
    (hPs : ∀ t, P (t + 1) = P t * x t / (1 - r t)) (n : ℕ) :
    ∏ t ∈ Finset.range n, (E t / P t * k t + x t) / (1 + E t / P t) =
      (E n + P n) / (E 0 + P 0) *
        ∏ t ∈ Finset.range n, (E (t + 1) + (1 - r t) * P (t + 1)) / (E (t + 1) + P (t + 1)) := by
  induction n with
  | zero =>
    have := (add_pos (hE 0) (hP 0)).ne'
    simp [this]
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
    have h0 := (add_pos (hE 0) (hP 0)).ne'
    have hn := (add_pos (hE n) (hP n)).ne'
    have hn1 := (add_pos (hE (n + 1)) (hP (n + 1))).ne'
    have hPn := (hP n).ne'
    have hrn : (1 : ℚ) - r n ≠ 0 := by have := hr n; linarith
    have hn' : P n + E n ≠ 0 := by rw [add_comm]; exact hn
    have step : (E n / P n * k n + x n) / (1 + E n / P n) =
        (E (n + 1) + (1 - r n) * P (n + 1)) / (E n + P n) := by
      rw [hEs, hPs, mul_div_cancel₀ _ hrn]
      have h1 : 1 + E n / P n ≠ 0 := by have := hE n; have := hP n; positivity
      rw [div_eq_div_iff h1 hn]
      field_simp
      ring
    rw [step]
    field_simp

/-- [proved-derived; formal-checked] **`rebase_log_residual`.** A rebase keeps the mantissa
`m = ⌊x⌋ ≥ 1` of the scaled ratio `x`: its relative residual in `ln` is `ln(x/m) ∈ [0, 1/m)`, below
`2^(1−W)` for a `W`-bit mantissa (Rust `landmark::Beta::carry`). For a relative residual
`r ∈ [0, 2^(1−W))` at `W ≥ 2`, `|log₂(1 − r)| < 2^(3−W)`. -/
theorem rebase_log_residual :
    (∀ {x m : ℝ}, 1 ≤ m → m ≤ x → x < m + 1 →
      0 ≤ Real.log (x / m) ∧ Real.log (x / m) < 1 / m) ∧
    ∀ {r : ℝ} {W : ℕ}, 2 ≤ W → 0 ≤ r → r < 2 ^ (1 - (W : ℤ)) →
      |Real.logb 2 (1 - r)| < 2 ^ (3 - (W : ℤ)) := by
  refine ⟨fun {x m} hm hx hx1 => ?_, fun {r W} hW hr0 hr => ?_⟩
  · have hm0 : 0 < m := by linarith
    have hxm : 1 ≤ x / m := by rw [le_div_iff₀ hm0]; linarith
    refine ⟨Real.log_nonneg hxm, ?_⟩
    calc Real.log (x / m) ≤ x / m - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = (x - m) / m := by field_simp
      _ < 1 / m := div_lt_div_of_pos_right (by linarith) hm0
  · have hW' : (2 : ℝ) ^ (1 - (W : ℤ)) ≤ 1 / 2 := by
      have : (1 - (W : ℤ)) ≤ -1 := by omega
      calc (2 : ℝ) ^ (1 - (W : ℤ)) ≤ 2 ^ (-1 : ℤ) := zpow_le_zpow_right₀ (by norm_num) this
        _ = 1 / 2 := by norm_num
    have hr1 : r < 1 / 2 := lt_of_lt_of_le hr hW'
    have hpos : 0 < 1 - r := by linarith
    have hlog_le : Real.log (1 - r) ≤ 0 := Real.log_nonpos hpos.le (by linarith)
    have hlog_ge : -(r / (1 - r)) ≤ Real.log (1 - r) := by
      have := Real.one_sub_inv_le_log_of_pos hpos
      have e : 1 - (1 - r)⁻¹ = -(r / (1 - r)) := by field_simp; ring
      linarith
    have hfrac : r / (1 - r) ≤ 2 * r := by
      rw [div_le_iff₀ hpos]; nlinarith
    have hl2 : (1 : ℝ) / 2 < Real.log 2 := by
      have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
    have hlog2 : 0 < Real.log 2 := by linarith
    rw [Real.logb, abs_div, abs_of_pos hlog2, abs_of_nonpos hlog_le, div_lt_iff₀ hlog2]
    have e3 : (2 : ℝ) ^ (3 - (W : ℤ)) = 4 * 2 ^ (1 - (W : ℤ)) := by
      rw [show (3 - (W : ℤ)) = 2 + (1 - (W : ℤ)) by ring, zpow_add₀ (by norm_num)]
      norm_num
    rw [e3]
    have hr2 : 0 ≤ (2 : ℝ) ^ (1 - (W : ℤ)) := by positivity
    nlinarith

end Lattice

/-! ## 7. The path cochain and the local autogradient -/

section Cochain

/-- [definition] **The edge ratio** of the opened path, `R_d = q_(d+1)/q_d`: the child's face over
the node's, a ratio of two faces of one class. -/
def edgeRatio (q : ℕ → ℝ) (d : ℕ) : ℝ := q (d + 1) / q d

/-- [proved-derived; formal-checked] **`path_cochain`: the edge log ratios are an additive exact
cochain on the path.** For positive faces `q_d`:
* a segment's edge logs sum to the difference of its endpoints,
  `Σ_(i≤d<j) log R_d = log q_j − log q_i`
  (exact: the coboundary of the node function `log q`);
* concatenating segments adds;
* `log q_0 = log q_D + Σ_(d<D) log(q_d/q_(d+1))`, and in code lengths
  `−log₂ q_0 = −log₂ q_D + Σ_(d<D) log₂ R_d`.
A tree has no two-cells, so no holonomy is claimed: the cochain is exact on every path. -/
theorem path_cochain (q : ℕ → ℝ) (hq : ∀ d, 0 < q d) :
    (∀ i j, i ≤ j → ∑ d ∈ Finset.Ico i j, Real.log (edgeRatio q d) =
      Real.log (q j) - Real.log (q i)) ∧
      (∀ i j k, i ≤ j → j ≤ k →
        ∑ d ∈ Finset.Ico i j, Real.log (edgeRatio q d) +
            ∑ d ∈ Finset.Ico j k, Real.log (edgeRatio q d) =
          ∑ d ∈ Finset.Ico i k, Real.log (edgeRatio q d)) ∧
      (∀ D, Real.log (q 0) = Real.log (q D) + ∑ d ∈ Finset.range D, Real.log (q d / q (d + 1))) ∧
      ∀ D, -Real.logb 2 (q 0) =
        -Real.logb 2 (q D) + ∑ d ∈ Finset.range D, Real.logb 2 (edgeRatio q d) := by
  have hseg : ∀ i j, i ≤ j → ∑ d ∈ Finset.Ico i j, Real.log (edgeRatio q d) =
      Real.log (q j) - Real.log (q i) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => simp
    | succ j hij ih =>
      rw [Finset.sum_Ico_succ_top hij, ih, edgeRatio, Real.log_div (hq _).ne' (hq _).ne']
      ring
  refine ⟨hseg, fun i j k h1 h2 => Finset.sum_Ico_consecutive _ h1 h2, fun D => ?_, fun D => ?_⟩
  · have h := hseg 0 D (Nat.zero_le D)
    rw [Finset.range_eq_Ico]
    have e : ∀ d ∈ Finset.Ico 0 D, Real.log (q d / q (d + 1)) = -Real.log (edgeRatio q d) :=
      fun d _ => by
        rw [edgeRatio, Real.log_div (hq _).ne' (hq _).ne', Real.log_div (hq _).ne' (hq _).ne']
        ring
    rw [Finset.sum_congr rfl e, Finset.sum_neg_distrib, h]
    ring
  · have h := hseg 0 D (Nat.zero_le D)
    rw [Finset.range_eq_Ico]
    simp only [Real.logb, ← Finset.sum_div, h]
    ring

/-- [proved-derived; formal-checked] **`edge_log_derivative`: `d log R = R⁻¹ dR` on each edge.**
Along the line `q + x δ` of the path's faces (positive at `x = 0`), the edge log ratio
`log((q_(d+1) + x δ_(d+1))/(q_d + x δ_d))` has derivative `R_d⁻¹ dR_d` at `x = 0`, with
`dR_d = (δ_(d+1) q_d − q_(d+1) δ_d)/q_d²`; it equals `δ_(d+1)/q_(d+1) − δ_d/q_d`, and along the path
these telescope to `δ_D/q_D − δ_0/q_0`. The covector is local to the path's counts and weights: no
derivative passes through a network. It is a natural gradient only once a metric is supplied. -/
theorem edge_log_derivative (q δ : ℕ → ℝ) (hq : ∀ d, 0 < q d) (d : ℕ) :
    HasDerivAt (fun x : ℝ => Real.log ((q (d + 1) + x * δ (d + 1)) / (q d + x * δ d)))
      ((edgeRatio q d)⁻¹ * ((δ (d + 1) * q d - q (d + 1) * δ d) / q d ^ 2)) 0 ∧
      (edgeRatio q d)⁻¹ * ((δ (d + 1) * q d - q (d + 1) * δ d) / q d ^ 2) =
        δ (d + 1) / q (d + 1) - δ d / q d ∧
      ∀ D, ∑ d ∈ Finset.range D, (δ (d + 1) / q (d + 1) - δ d / q d) = δ D / q D - δ 0 / q 0 := by
  have h1 : HasDerivAt (fun x : ℝ => q (d + 1) + x * δ (d + 1)) (δ (d + 1)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (δ (d + 1))).const_add (q (d + 1))
  have h0 : HasDerivAt (fun x : ℝ => q d + x * δ d) (δ d) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (δ d)).const_add (q d)
  have hR := h1.div h0 (by simpa using (hq d).ne')
  have hRne : (q (d + 1) + 0 * δ (d + 1)) / (q d + 0 * δ d) ≠ 0 := by
    simp only [zero_mul, add_zero]; exact div_ne_zero (hq _).ne' (hq _).ne'
  have hL := hR.log hRne
  refine ⟨hL.congr_deriv ?_, ?_, fun D => Finset.sum_range_sub (fun d => δ d / q d) D⟩
  · simp only [Pi.div_apply, zero_mul, add_zero, edgeRatio]
    rw [div_eq_inv_mul]
  · have := (hq d).ne'; have := (hq (d + 1)).ne'
    simp only [edgeRatio]
    field_simp

/-- [proved-derived; formal-checked] **The exact telescope** in `ℚ`: for faces nonzero along the
path, `q_0 = q_D · ∏_(d<D) q_d/q_(d+1)`, with no logarithm taken. -/
theorem path_telescope_exact (q : ℕ → ℚ) (D : ℕ) (hq : ∀ d ≤ D, q d ≠ 0) :
    q 0 = q D * ∏ d ∈ Finset.range D, (q d / q (d + 1)) := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, mul_comm (q (D + 1)), mul_assoc,
      mul_div_cancel₀ _ (hq (D + 1) le_rfl), mul_comm, ← ih fun d hd => hq d (by omega)]

/-- [proved-derived; formal-checked] **`tree_telescope`.** Along the path an address opens, the
tree's root face of a class is the deepest node's KT face times the path's node-to-child ratios,
exactly in `ℚ`, and in code lengths the root's is the deepest node's plus the edges' `log₂ R_d`
(`path_cochain`). -/
theorem tree_telescope {Ltr : Type*} [Fintype Ltr] [DecidableEq Ltr] {A : Type*} [Fintype A]
    [Nonempty A] (N : TreeStanding Ltr A) (D : ℕ) (a : List Ltr) (c : A) :
    face N D a 0 c = kAt N a D c * ∏ d ∈ Finset.range D, (face N D a d c / face N D a (d + 1) c) ∧
      -Real.logb 2 (face N D a 0 c : ℝ) = -Real.logb 2 (kAt N a D c : ℝ) +
        ∑ d ∈ Finset.range D, Real.logb 2 (edgeRatio (fun d => (face N D a d c : ℝ)) d) := by
  have hD : face N D a D c = kAt N a D c := by simp [face, pathFace_deepest]
  have hpos := face_pos_all N D a c
  refine ⟨?_, ?_⟩
  · rw [← hD]
    exact path_telescope_exact _ D fun d _ => (hpos d).ne'
  · have := (path_cochain (fun d => (face N D a d c : ℝ)) fun d => by exact_mod_cast hpos d).2.2.2 D
    simp only [hD] at this
    exact this

end Cochain

/-! ## 8. The deposition join -/

section Deposition

open Holonics.Computation.HolonicInformationTheory (PositiveProbabilitySection)

variable {A : Type*} [Fintype A]

/-- [proved-derived; formal-checked] **`deposition_is_log_ratio`.** The first law's deposition term
(`Aeon/Production/FirstLaw`) between two positive receiver sections `q → q'` at a fixed arrived
source `p'` is `−Σ_c p'(c) log(q'(c)/q(c))`, the arrived source's average of the faces' log
ratios, and the change of cross-entropy at that source (`deposition_eq_crossEntropy_change`). -/
theorem deposition_is_log_ratio (p' q q' : PositiveProbabilitySection A) :
    Holonics.Aeon.Production.FirstLaw.deposition p' q q' =
        -∑ c, p'.mass c * Real.log (q'.mass c / q.mass c) ∧
      Holonics.Aeon.Production.FirstLaw.deposition p' q q' =
        p'.crossEntropy q' - p'.crossEntropy q := by
  refine ⟨?_, Holonics.Aeon.Production.FirstLaw.deposition_eq_crossEntropy_change p' q q'⟩
  unfold Holonics.Aeon.Production.FirstLaw.deposition
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Real.log_div (q'.positive c).ne' (q.positive c).ne']

/-- [proved-derived; formal-checked] **`concentrated_deposition`.** For a concentrated (one-hot)
arrival `e_t` and positive faces `q, q'`, the deposition reading is the target's log ratio,
`−Σ_c e_t(c) log(q'(c)/q(c)) = −log(q'(t)/q(t))`, the change of the target's code length
`(−log q'(t)) − (−log q(t))`. The first law's positive-section theorem does not cover `e_t`; this
is the direct identity. -/
theorem concentrated_deposition [DecidableEq A] (q q' : A → ℝ) (hq : ∀ c, 0 < q c)
    (hq' : ∀ c, 0 < q' c) (t : A) :
    -∑ c, (Pi.single t 1 : A → ℝ) c * Real.log (q' c / q c) = -Real.log (q' t / q t) ∧
      -Real.log (q' t / q t) = -Real.log (q' t) - -Real.log (q t) := by
  refine ⟨?_, by rw [Real.log_div (hq' t).ne' (hq t).ne']; ring⟩
  simp [Pi.single_apply]

variable {Ltr : Type*} [Fintype Ltr] [DecidableEq Ltr] [DecidableEq A] [Nonempty A]

/-- [definition] **The tree's root face at an address, as a positive section** in the real chart. -/
def faceSection (N : TreeStanding Ltr A) (D : ℕ) (a : List Ltr) : PositiveProbabilitySection A where
  mass c := (face N D a 0 c : ℝ)
  positive c := by exact_mod_cast (face_normalized N D a 0 (Nat.zero_le _)).1 c
  normalized := by
    have := (face_normalized N D a 0 (Nat.zero_le _)).2
    exact_mod_cast this

/-- [proved-derived; formal-checked] **`tree_deposit_is_deposition`: the deposition join.** When an
arrival `(a₀, c₀)` deposits into the tree, the root face at the next address `a` moves from `q` to
`q'`; at a fixed arrived source `p'`, the change of the scored code length is the first law's
deposition term, `−Σ p' log(q'/q) = C(p', q') − C(p', q)`; for a concentrated arrival at `t` it is
`−log(q'(t)/q(t))`. The tree supplies the deposition term, not the exchange term: the exchange
moves the source through an unchanged receiver, and a tree has no two-cell on which a coboundary
could be the exchange. -/
theorem tree_deposit_is_deposition (N : TreeStanding Ltr A) (D : ℕ) (a₀ : List Ltr) (c₀ : A)
    (a : List Ltr) (p' : PositiveProbabilitySection A) (t : A) :
    Holonics.Aeon.Production.FirstLaw.deposition p' (faceSection N D a)
        (faceSection (arrive N a₀ c₀) D a) =
        p'.crossEntropy (faceSection (arrive N a₀ c₀) D a) - p'.crossEntropy (faceSection N D a) ∧
      Holonics.Aeon.Production.FirstLaw.deposition p' (faceSection N D a)
          (faceSection (arrive N a₀ c₀) D a) =
        -∑ c, p'.mass c * Real.log ((face (arrive N a₀ c₀) D a 0 c : ℝ) / (face N D a 0 c : ℝ)) ∧
      -∑ c, (Pi.single t 1 : A → ℝ) c *
          Real.log ((face (arrive N a₀ c₀) D a 0 c : ℝ) / (face N D a 0 c : ℝ)) =
        -Real.log ((face (arrive N a₀ c₀) D a 0 t : ℝ) / (face N D a 0 t : ℝ)) := by
  obtain ⟨h1, h2⟩ :=
    deposition_is_log_ratio p' (faceSection N D a) (faceSection (arrive N a₀ c₀) D a)
  exact ⟨h2, h1, (concentrated_deposition _ _ (faceSection N D a).positive
    (faceSection (arrive N a₀ c₀) D a).positive t).1⟩

end Deposition

/-! ## 9. Founding at first arrival, and release -/

section Release

variable {Ltr : Type*} [Fintype Ltr] [DecidableEq Ltr] {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq Ltr] [DecidableEq A] in
/-- [proved-derived; formal-checked] **`unfounded_reads_prior`.** A node none of whose descendants
has received an arrival reads as the prior: `E = 1`, `P = 1`, `W = 1` at every depth, the stop to
split ratio `β = E/P = 1`, and its KT face is the uniform `1/|A|`. -/
theorem unfounded_reads_prior [Nonempty A] (N : TreeStanding Ltr A) (s : List Ltr)
    (h : ∀ t, N (s ++ t) = fun _ => 0) (c : A) :
    ktMass (N s) = 1 ∧ (∀ m, treeWeight N m s = 1) ∧ (∀ m, splitMass N m s = 1) ∧
      (∀ m, ktMass (N s) / splitMass N m s = 1) ∧ ktFace (N s) c = 1 / Fintype.card A := by
  have hs : N s = fun _ => 0 := by simpa using h []
  have hE : ktMass (N s) = 1 := by rw [hs, ktMass_zero]
  have hW : ∀ m s', (∀ t, N (s' ++ t) = fun _ => 0) → treeWeight N m s' = 1 := by
    intro m
    induction m with
    | zero => intro s' h'; simpa [treeWeight, ktMass_zero] using congrArg ktMass (h' [])
    | succ m ih =>
      intro s' h'
      have hE' : ktMass (N s') = 1 := by simpa [ktMass_zero] using congrArg ktMass (h' [])
      rw [treeWeight_succ, hE', splitMass,
        Finset.prod_eq_one fun b _ => ih _ fun t => by simpa using h' (b :: t)]
      norm_num
  have hP : ∀ m, splitMass N m s = 1 := fun m =>
    Finset.prod_eq_one fun b _ => hW m _ fun t => by simpa using h (b :: t)
  refine ⟨hE, fun m => hW m s h, hP, fun m => by rw [hE, hP, div_one], ?_⟩
  rw [hs, ktFace_zero]

/-- [proved-derived; formal-checked] **`founding_step`: a node founded by an arrival starts at
`β = 1`.** At an opened node above the maximum depth whose subtree has received nothing, `β = 1`
before the arrival and still `β' = β·k_d(c)/q_(d+1)(c) = 1` after it: the node's KT face and the
face below it are both the uniform prior `1/|A|` (`pathFace_const`). So founding at first arrival
with `β = 1` is the tree's own step. -/
theorem founding_step [Nonempty A] (N : TreeStanding Ltr A) {D : ℕ} {a : List Ltr}
    (hD : D ≤ a.length) (c : A) {d : ℕ} (hd : d < D)
    (h : ∀ t, N (a.take d ++ t) = fun _ => 0) :
    ktMass (N (a.take d)) / splitMass N (D - d - 1) (a.take d) = 1 ∧
      ktMass (arrive N a c (a.take d)) / splitMass (arrive N a c) (D - d - 1) (a.take d) = 1 := by
  obtain ⟨_, _, _, hβ, hk⟩ := unfounded_reads_prior N (a.take d) h c
  have hK : (0 : ℚ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hbelow : face N D a (d + 1) c = 1 / Fintype.card A := by
    refine pathFace_const _ _ D c _ (d + 1) (by omega) fun d' h1 h2 => ?_
    have e : a.take d' = a.take d ++ (a.drop d).take (d' - d) := by
      rw [← List.take_add, show d + (d' - d) = d' by omega]
    simp only [kAt, e, h, ktFace_zero]
  refine ⟨hβ (D - d - 1), ?_⟩
  rw [((landmark_step N hD c).2.2.2.1 d hd).2.2, hβ, kAt, hk, hbelow]
  field_simp

/-- [definition] **A nested standing**: every node holds at most its parent's counts (what reaches
a node reaches its every restriction). -/
def Nested (N : TreeStanding Ltr A) : Prop := ∀ s t c, N (s ++ t) c ≤ N s c

omit [Fintype Ltr] [Fintype A] in
theorem arrive_nested {N : TreeStanding Ltr A} (hN : Nested N) (a : List Ltr) (c : A) :
    Nested (arrive N a c) := by
  intro s t c'
  simp only [arrive]
  by_cases hst : a.take (s ++ t).length = s ++ t
  · have hs : a.take s.length = s := by
      by_contra hs; exact off_path_descendant hs t hst
    simp only [if_pos hst, if_pos hs, bump]
    have := hN s t c'
    omega
  · simp only [if_neg hst]
    by_cases hs : a.take s.length = s
    · simp only [if_pos hs, bump]; have := hN s t c'; omega
    · simp only [if_neg hs]; exact hN s t c'

omit [Fintype Ltr] [DecidableEq Ltr] [Fintype A] in
theorem counts_eq_zero_iff (w : List A) : counts w = (fun _ => 0) ↔ w = [] := by
  constructor
  · intro h
    cases w with
    | nil => rfl
    | cons x w =>
      have := congrFun h x
      simp [counts] at this
  · rintro rfl; exact counts_nil

/-- [definition] **The tree founded at first arrival**: a node reads as the prior until something
reaches it; only founded nodes (nonzero counts) are materialized. -/
def sparseWeight (N : TreeStanding Ltr A) : ℕ → List Ltr → ℚ
  | 0, s => if N s = (fun _ => 0) then 1 else ktMass (N s)
  | m + 1, s => if N s = (fun _ => 0) then 1 else
      (ktMass (N s) + ∏ b, sparseWeight N m (s ++ [b])) / 2

/-- [proved-derived; formal-checked] **`founded_tree_same_law`.** For a nested standing (every
standing built by arrivals, and the routed counts of every observation list), the tree founded at
first arrival (unfounded nodes read as the prior) is the same law as the materialized tree at every
node and depth; for routed counts a node is founded exactly when something has reached it. -/
theorem founded_tree_same_law [Nonempty A] :
    (∀ (N : TreeStanding Ltr A), Nested N → ∀ m s, sparseWeight N m s = treeWeight N m s) ∧
      (∀ ctx : List A → List Ltr, ∀ h, Nested (standingOf ctx h)) ∧
      ∀ (obs : List (List Ltr × A)) s,
        nodeCounts obs s = (fun _ => 0) ↔ routed obs s = [] := by
  refine ⟨fun N hN => ?_, fun ctx h => ?_, fun obs s => counts_eq_zero_iff _⟩
  · intro m
    induction m with
    | zero =>
      intro s
      by_cases h0 : N s = fun _ => 0
      · simp [sparseWeight, treeWeight, h0, ktMass_zero]
      · simp [sparseWeight, treeWeight, h0]
    | succ m ih =>
      intro s
      by_cases h0 : N s = fun _ => 0
      · have hall : ∀ t, N (s ++ t) = fun _ => 0 := fun t => by
          funext c; have := hN s t c; rw [h0] at this; simpa using this
        simp only [sparseWeight, if_pos h0]
        exact ((unfounded_reads_prior N s hall (Classical.arbitrary A)).2.1 (m + 1)).symm
      · simp only [sparseWeight, if_neg h0, treeWeight, ih]
  · induction h with
    | nil => intro s t c; simp [standingOf, emptyStanding]
    | cons c h ih => exact arrive_nested ih _ _

open Holonics.Foundation.Standing (StandingLaw causalSignature
  causalSignature_eq_iff_futureAgreement standingLaw_exists_iff_future_factors)
open Holonics.Foundation.CausalRelevance.NonLinear (futureAgreement)
open Holonics.Foundation.Chronology (transportWord)

/-- [definition] **The tree's root read**: the receiver `(a, c)` reads the tree's root face of the
class `c` at the address `a`. -/
def rootRead (D : ℕ) (r : List Ltr × A) (N : TreeStanding Ltr A) : ℚ := face N D r.1 0 r.2

/-- [definition] **The arrival transport**: an arrival `(a, c)` deposits along the path `a`
opens. -/
def arrival (g : List Ltr × A) (N : TreeStanding Ltr A) : TreeStanding Ltr A := arrive N g.1 g.2

omit [Fintype Ltr] [Fintype A] [DecidableEq A] in
theorem pathFace_congr {k k' : ℕ → A → ℚ} {lam lam' : ℕ → ℚ} {D : ℕ}
    (hk : ∀ d ≤ D, k d = k' d) (hl : ∀ d < D, lam d = lam' d) :
    ∀ d ≤ D, pathFace k lam D d = pathFace k' lam' D d := by
  suffices h : ∀ m d, d + m = D → mixFrom k lam m d = mixFrom k' lam' m d by
    intro d hd; exact h (D - d) d (by omega)
  intro m
  induction m with
  | zero => intro d hd; exact hk d (by omega)
  | succ m ih =>
    intro d hd
    funext c
    simp only [mixFrom, ih (d + 1) (by omega), hk d (by omega), hl d (by omega)]

omit [DecidableEq Ltr] [DecidableEq A] in
theorem treeWeight_congr {N N' : TreeStanding Ltr A} :
    ∀ m s, (∀ t : List Ltr, t.length ≤ m → N (s ++ t) = N' (s ++ t)) →
      treeWeight N m s = treeWeight N' m s
  | 0, s, h => by simpa [treeWeight] using congrArg ktMass (h [] (le_refl _))
  | m + 1, s, h => by
    have hs : N s = N' s := by simpa using h [] (Nat.zero_le _)
    simp only [treeWeight, hs]
    congr 2
    refine Finset.prod_congr rfl fun b _ => treeWeight_congr m _ fun t ht => ?_
    simpa using h (b :: t) (by simp; omega)

/-- [proved-derived; formal-checked] **`release_rule`: release is the retention law's future
quotient.**
* Replacing a tree standing `N` by `N'` preserves every admitted future face (every word of
  arrivals, read at every address and class) exactly when their causal signatures agree
  (`Foundation/Standing.causalSignature_eq_iff_futureAgreement`).
* A retention map carries a lawful `StandingLaw` of the tree exactly when equal retention forces
  equal causal signature (`standingLaw_exists_iff_future_factors`).
* **Nodes below the admitted depth are releasable**: two standings that agree at every node of
  depth at most `D` agree on every future face of the depth-`D` read. -/
theorem release_rule (D : ℕ) :
    (∀ N N' : TreeStanding Ltr A,
      futureAgreement (rootRead D) arrival N N' ↔
        causalSignature (rootRead D) arrival N = causalSignature (rootRead D) arrival N') ∧
      (∀ {R : Type*} (retain : TreeStanding Ltr A → R),
        (∃ L : StandingLaw (List Ltr × A) (List Ltr × A) (TreeStanding Ltr A) R ℚ,
            L.transport = arrival ∧ L.observe = rootRead D ∧ L.retain = retain) ↔
          ∀ N N', retain N = retain N' →
            causalSignature (rootRead D) arrival N = causalSignature (rootRead D) arrival N') ∧
      ∀ N N' : TreeStanding Ltr A, (∀ s : List Ltr, s.length ≤ D → N s = N' s) →
        futureAgreement (rootRead D) arrival N N' := by
  refine ⟨fun N N' => (causalSignature_eq_iff_futureAgreement _ _ _ _).symm,
    fun retain => standingLaw_exists_iff_future_factors _ _ retain, fun N N' h => ?_⟩
  intro r word
  have hword : ∀ s : List Ltr, s.length ≤ D →
      transportWord arrival word N s = transportWord arrival word N' s := by
    induction word with
    | nil => exact h
    | cons g word ih =>
      intro s hs
      simp only [transportWord, arrival, arrive, ih s hs]
  set M := transportWord arrival word N
  set M' := transportWord arrival word N'
  have hk : ∀ d ≤ D, kAt M r.1 d = kAt M' r.1 d := fun d hd => by
    unfold kAt
    rw [hword _ (by simp; omega)]
  have hl : ∀ d < D, lamAt M D r.1 d = lamAt M' D r.1 d := fun d hd => by
    have hs : (r.1.take d).length ≤ d := by simp
    have hE : M (r.1.take d) = M' (r.1.take d) := hword _ (by omega)
    have hP : splitMass M (D - d - 1) (r.1.take d) = splitMass M' (D - d - 1) (r.1.take d) := by
      unfold splitMass
      refine Finset.prod_congr rfl fun b _ => treeWeight_congr _ _ fun t ht => hword _ ?_
      simp only [List.length_append, List.length_singleton]
      omega
    simp only [lamAt, hE, hP]
  simp only [rootRead, face]
  rw [pathFace_congr hk hl 0 (Nat.zero_le _)]

/-- [definition] The fixture standing: one arrival of class `0` at the address `[0]`, letters and
classes in `Fin 2`. It founds the root and the child `[0]`. -/
def oneArrival : TreeStanding (Fin 2) (Fin 2) := arrive emptyStanding [0] 0

/-- [definition] The fixture standing with the occupied child `[0]` evicted (its counts reset to
the prior), as a budget alone would. -/
def evicted : TreeStanding (Fin 2) (Fin 2) := Function.update oneArrival [0] (fun _ => 0)

/-- [proved-derived; formal-checked] **`budget_eviction_changes_face`.** Evicting an occupied child
by budget alone changes a later face: at depth one, after one arrival of class `0` at `[0]`, the
root face of class `0` at the address `[0]` is `3/4`; with the child `[0]` evicted it is `7/12`.
So no lawful retention identifies the two standings
(`Foundation/Standing.separating_future_refutes_the_standing`): a storage budget alone gives no
exact eviction rule. -/
theorem budget_eviction_changes_face :
    rootRead 1 ([0], 0) oneArrival = 3 / 4 ∧ rootRead 1 ([0], 0) evicted = 7 / 12 ∧
      ∀ {R : Type} (L : StandingLaw (List (Fin 2) × Fin 2) (List (Fin 2) × Fin 2)
          (TreeStanding (Fin 2) (Fin 2)) R ℚ),
        L.transport = arrival → L.observe = rootRead 1 →
          L.retain oneArrival ≠ L.retain evicted := by
  have e0 : oneArrival [] = bump (fun _ => 0) 0 := by
    unfold oneArrival arrive; rw [if_pos (by decide)]; rfl
  have e1 : oneArrival [0] = bump (fun _ => 0) 0 := by
    unfold oneArrival arrive; rw [if_pos (by decide)]; rfl
  have e2 : oneArrival [1] = fun _ => 0 := by
    unfold oneArrival arrive; rw [if_neg (by decide)]; rfl
  have v0 : evicted [] = bump (fun _ => 0) 0 := by
    simp [evicted, Function.update_of_ne, e0]
  have v1 : evicted [0] = fun _ => 0 := by simp [evicted]
  have v2 : evicted [1] = fun _ => 0 := by
    simp [evicted, Function.update_of_ne, e2]
  have mb : ktMass (bump (fun _ : Fin 2 => 0) 0) = 1 / 2 := by
    rw [ktMass_bump, ktMass_zero]
    simp [ktFace, ktProb]
  have fb : ktFace (bump (fun _ : Fin 2 => 0) 0) 0 = 3 / 4 := by
    simp [ktFace, ktProb, bump]
    norm_num
  have f0 : ktFace (fun _ : Fin 2 => 0) 0 = 1 / 2 := by
    simp [ktFace, ktProb]
  have hread : ∀ N : TreeStanding (Fin 2) (Fin 2), rootRead 1 ([0], 0) N =
      lamAt N 1 [0] 0 * ktFace (N []) 0 + (1 - lamAt N 1 [0] 0) * ktFace (N [0]) 0 := by
    intro N
    simp only [rootRead, face]
    rw [pathFace_step _ _ Nat.zero_lt_one, pathFace_deepest]
    simp [kAt]
  have h1 : rootRead 1 ([0], 0) oneArrival = 3 / 4 := by
    rw [hread, e0, e1, fb]; ring
  have h2 : rootRead 1 ([0], 0) evicted = 7 / 12 := by
    have hlam : lamAt evicted 1 [0] 0 = 1 / 3 := by
      simp only [lamAt, splitMass, Fin.prod_univ_two]
      simp only [List.take_zero, List.nil_append, Nat.sub_self, Fin.isValue]
      rw [v0, mb]
      simp only [treeWeight, v1, v2, ktMass_zero]
      norm_num
    rw [hread, v0, v1, fb, f0, hlam]
    norm_num
  refine ⟨h1, h2, fun L ht ho => ?_⟩
  apply Holonics.Foundation.Standing.StandingLaw.separating_future_refutes_the_standing L
    ([0], 0) []
  simp only [transportWord, ho, h1, h2]
  norm_num

end Release

/-! ## 10. The receiver's mixture of two faces over a passage -/

section SequentialMixture

open Finset

/-- [definition] **A face's prequential likelihood** over the first `n` cells, `A_n = ∏_(t<n) a_t`
(`A_0 = 1`). -/
def seqLik (a : ℕ → ℚ) (n : ℕ) : ℚ := ∏ t ∈ range n, a t

/-- [definition] **The mixture's likelihood ratio** `β_t = A_t/B_t` of two faces. -/
def seqRatio (a b : ℕ → ℚ) (t : ℕ) : ℚ := seqLik a t / seqLik b t

/-- [definition] **The sequential two-face mixture** at cell `t`: `q_t = λ_t a_t + (1 − λ_t) b_t`
with `λ_t = A_t/(A_t + B_t)`, the posterior weight of the first face under the prior ½/½. -/
def seqMix (a b : ℕ → ℚ) (t : ℕ) : ℚ :=
  seqLik a t / (seqLik a t + seqLik b t) * a t +
    (1 - seqLik a t / (seqLik a t + seqLik b t)) * b t

theorem seqLik_zero (a : ℕ → ℚ) : seqLik a 0 = 1 := prod_range_zero _

theorem seqLik_succ (a : ℕ → ℚ) (n : ℕ) : seqLik a (n + 1) = seqLik a n * a n :=
  prod_range_succ _ _

theorem seqLik_pos {a : ℕ → ℚ} (ha : ∀ t, 0 < a t) (n : ℕ) : 0 < seqLik a n :=
  prod_pos fun t _ => ha t

/-- [proved-derived; formal-checked] **`sequential_mixture`: the receiver's mixture of two faces,
stepped cell by cell.** For positive faces `a_t`, `b_t` of the cells' targets with prequential
likelihoods `A_t = ∏_(s<t) a_s`, `B_t = ∏_(s<t) b_s`:
* the ratio opens at `β_0 = 1` (the prior ½/½) and steps by `β_(t+1) = β_t a_t/b_t` after each
  cell, in cell order;
* the weight is `λ_t = A_t/(A_t + B_t) = β_t/(1 + β_t)`;
* the mixture's product telescopes: `∏_(t<n) q_t = ½ A_n + ½ B_n`.

The weight at cell `t` must be the ratio after every earlier cell: a weight read before an earlier
cell's step breaks the telescope. -/
theorem sequential_mixture {a b : ℕ → ℚ} (ha : ∀ t, 0 < a t) (hb : ∀ t, 0 < b t) :
    seqRatio a b 0 = 1 ∧
      (∀ t, seqRatio a b (t + 1) = seqRatio a b t * a t / b t) ∧
      (∀ t, seqLik a t / (seqLik a t + seqLik b t) = seqRatio a b t / (1 + seqRatio a b t)) ∧
      ∀ n, ∏ t ∈ range n, seqMix a b t = seqLik a n / 2 + seqLik b n / 2 := by
  refine ⟨by simp [seqRatio, seqLik_zero], fun t => ?_, fun t => ?_, fun n => ?_⟩
  · have hA := seqLik_pos ha t
    have hB := seqLik_pos hb t
    have := hb t
    simp only [seqRatio, seqLik_succ]
    field_simp
  · have hA := seqLik_pos ha t
    have hB := seqLik_pos hb t
    simp only [seqRatio]
    field_simp
    ring
  · induction n with
    | zero => simp [seqLik_zero]; norm_num
    | succ n ih =>
      rw [prod_range_succ, ih, seqLik_succ, seqLik_succ]
      have hA := seqLik_pos ha n
      have hB := seqLik_pos hb n
      have hAB : seqLik a n + seqLik b n ≠ 0 := by positivity
      simp only [seqMix]
      field_simp
      ring

/-- [proved-derived; formal-checked] **`sequential_mixture_bounds`: within one bit of the better
face.** `½ max(A_n, B_n) ≤ ∏_(t<n) q_t ≤ max(A_n, B_n)`, so the mixture's code length lies
between the better face's and one bit above it:
`min(−log₂ A_n, −log₂ B_n) ≤ −log₂ ∏ q ≤ min(−log₂ A_n, −log₂ B_n) + 1`. -/
theorem sequential_mixture_bounds {a b : ℕ → ℚ} (ha : ∀ t, 0 < a t) (hb : ∀ t, 0 < b t)
    (n : ℕ) :
    max (seqLik a n) (seqLik b n) / 2 ≤ ∏ t ∈ range n, seqMix a b t ∧
      ∏ t ∈ range n, seqMix a b t ≤ max (seqLik a n) (seqLik b n) ∧
      min (-Real.logb 2 (seqLik a n : ℝ)) (-Real.logb 2 (seqLik b n : ℝ)) ≤
        -Real.logb 2 ((∏ t ∈ range n, seqMix a b t : ℚ) : ℝ) ∧
      -Real.logb 2 ((∏ t ∈ range n, seqMix a b t : ℚ) : ℝ) ≤
        min (-Real.logb 2 (seqLik a n : ℝ)) (-Real.logb 2 (seqLik b n : ℝ)) + 1 := by
  have hP := (sequential_mixture ha hb).2.2.2 n
  have hA := seqLik_pos ha n
  have hB := seqLik_pos hb n
  set P := ∏ t ∈ range n, seqMix a b t with hPdef
  set A := seqLik a n
  set B := seqLik b n
  have lo : max A B / 2 ≤ P := by
    rw [hP]; rcases le_total A B with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hi : P ≤ max A B := by
    rw [hP]; rcases le_total A B with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hPR : (0 : ℝ) < P := by
    have : (0 : ℚ) < P := lt_of_lt_of_le (by positivity) lo
    exact_mod_cast this
  have loA : (A : ℝ) / 2 ≤ P := by
    have : A / 2 ≤ P := le_trans (by have := le_max_left A B; linarith) lo
    exact_mod_cast this
  have loB : (B : ℝ) / 2 ≤ P := by
    have : B / 2 ≤ P := le_trans (by have := le_max_right A B; linarith) lo
    exact_mod_cast this
  have half : ∀ {x : ℝ}, 0 < x → Real.logb 2 (x / 2) = Real.logb 2 x - 1 := by
    intro x hx
    rw [Real.logb_div hx.ne' (by norm_num), Real.logb_self_eq_one (by norm_num)]
  have gA := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) loA
  have gB := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) loB
  rw [half hAR] at gA
  rw [half hBR] at gB
  refine ⟨lo, hi, ?_, ?_⟩
  · rcases le_total A B with h | h
    · have : P ≤ B := by rw [max_eq_right h] at hi; exact hi
      have hR : (P : ℝ) ≤ B := by exact_mod_cast this
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hPR hR
      exact le_trans (min_le_right _ _) (by linarith)
    · have : P ≤ A := by rw [max_eq_left h] at hi; exact hi
      have hR : (P : ℝ) ≤ A := by exact_mod_cast this
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hPR hR
      exact le_trans (min_le_left _ _) (by linarith)
  · have : -Real.logb 2 (P : ℝ) - 1 ≤ min (-Real.logb 2 (A : ℝ)) (-Real.logb 2 (B : ℝ)) :=
      le_min (by linarith) (by linarith)
    linarith

/-- [definition] **The executed ratio**: `β̂_0 = 1` and `β̂_(t+1) = β̂_t a_t/(b_t ρ_t)`, the carried
ratio stepped with the chart's factor `ρ_t > 0` at each cell (the rational chart of `b_t` and a
rebase). -/
def execRatio (a b ρ : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | t + 1 => execRatio a b ρ t * a t / (b t * ρ t)

/-- [definition] **The executed mixture** at cell `t`: `q̂_t = (β̂_t a_t + b_t)/(1 + β̂_t)`, the
weight `λ̂_t = β̂_t/(1 + β̂_t)` read from the carried ratio. -/
def execMix (a b ρ : ℕ → ℚ) (t : ℕ) : ℚ :=
  (execRatio a b ρ t * a t + b t) / (1 + execRatio a b ρ t)

/-- [proved-derived; formal-checked] **`sequential_mixture_executed`: the carried ratio's drift
adds once over the passage.** With the ratio stepped by the chart's factors `ρ_t > 0`, the executed
mixture's product dominates each face's likelihood up to the factors on its own side:
`A_n ≤ 2 ∏ max(1, ρ_t) · ∏ q̂_t` and `B_n ≤ 2 ∏ max(1, 1/ρ_t) · ∏ q̂_t`; in bits,
`−log₂ ∏_(t<n) q̂_t ≤ min(−log₂ A_n, −log₂ B_n) + 1 + Σ_(t<n) |log₂ ρ_t|`. At `ρ ≡ 1` it is
`sequential_mixture_bounds`' upper half. -/
theorem sequential_mixture_executed {a b ρ : ℕ → ℚ} (ha : ∀ t, 0 < a t) (hb : ∀ t, 0 < b t)
    (hρ : ∀ t, 0 < ρ t) (n : ℕ) :
    seqLik a n ≤ 2 * (∏ t ∈ range n, max 1 (ρ t)) * ∏ t ∈ range n, execMix a b ρ t ∧
      seqLik b n ≤ 2 * (∏ t ∈ range n, max 1 (ρ t)⁻¹) * ∏ t ∈ range n, execMix a b ρ t ∧
      -Real.logb 2 ((∏ t ∈ range n, execMix a b ρ t : ℚ) : ℝ) ≤
        min (-Real.logb 2 (seqLik a n : ℝ)) (-Real.logb 2 (seqLik b n : ℝ)) + 1 +
          ∑ t ∈ range n, |Real.logb 2 (ρ t : ℝ)| := by
  -- The carried ratio is `A_t/B̂_t` with `B̂_t = ∏_(s<t) b_s ρ_s`.
  set Bh : ℕ → ℚ := seqLik (fun t => b t * ρ t) with hBh
  have hbρ : ∀ t, 0 < b t * ρ t := fun t => mul_pos (hb t) (hρ t)
  have hratio : ∀ t, execRatio a b ρ t = seqLik a t / Bh t := by
    intro t
    induction t with
    | zero => simp [execRatio, hBh, seqLik_zero]
    | succ t ih =>
      have hA := seqLik_pos ha t
      have hB := seqLik_pos hbρ t
      have := hb t
      have := hρ t
      rw [execRatio, ih, hBh, seqLik_succ, seqLik_succ]
      field_simp
  have hmix : ∀ t, execMix a b ρ t =
      (seqLik a t * a t + Bh t * b t) / (seqLik a t + Bh t) := by
    intro t
    have hA := seqLik_pos ha t
    have hB : 0 < Bh t := seqLik_pos hbρ t
    rw [execMix, hratio]
    field_simp
    ring
  -- The invariant `A_n + B̂_n ≤ 2 ∏ max(1, ρ_t) · ∏ q̂_t`.
  have hinv : ∀ n, seqLik a n + Bh n ≤
      2 * (∏ t ∈ range n, max 1 (ρ t)) * ∏ t ∈ range n, execMix a b ρ t := by
    intro n
    induction n with
    | zero => simp [hBh, seqLik_zero]; norm_num
    | succ n ih =>
      have hA := seqLik_pos ha n
      have hB := seqLik_pos hbρ n
      have hAB : 0 < seqLik a n + Bh n := by positivity
      have hm : 0 ≤ max 1 (ρ n) := le_trans zero_le_one (le_max_left _ _)
      have hq : 0 < execMix a b ρ n := by
        rw [hmix]; have := ha n; have := hb n; positivity
      rw [prod_range_succ, prod_range_succ, seqLik_succ, hBh, seqLik_succ, ← hBh]
      have step : seqLik a n * a n + Bh n * (b n * ρ n) ≤
          max 1 (ρ n) * ((seqLik a n + Bh n) * execMix a b ρ n) := by
        rw [hmix, mul_div_cancel₀ _ hAB.ne']
        have h1 : seqLik a n * a n ≤ max 1 (ρ n) * (seqLik a n * a n) := by
          have := ha n
          nlinarith [le_max_left 1 (ρ n), mul_pos hA (ha n)]
        have h2 : Bh n * (b n * ρ n) ≤ max 1 (ρ n) * (Bh n * b n) := by
          have := hb n
          have e : Bh n * (b n * ρ n) = ρ n * (Bh n * b n) := by ring
          rw [e]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        nlinarith
      calc seqLik a n * a n + Bh n * (b n * ρ n)
          ≤ max 1 (ρ n) * ((seqLik a n + Bh n) * execMix a b ρ n) := step
        _ ≤ max 1 (ρ n) * ((2 * (∏ t ∈ range n, max 1 (ρ t)) *
              ∏ t ∈ range n, execMix a b ρ t) * execMix a b ρ n) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ih hq.le) hm
        _ = 2 * ((∏ t ∈ range n, max 1 (ρ t)) * max 1 (ρ n)) *
              ((∏ t ∈ range n, execMix a b ρ t) * execMix a b ρ n) := by ring
  have hA := seqLik_pos ha n
  have hBhn := seqLik_pos hbρ n
  have hP : 0 < ∏ t ∈ range n, execMix a b ρ t := prod_pos fun t _ => by
    rw [hmix]
    have := seqLik_pos ha t; have := seqLik_pos hbρ t; have := ha t; have := hb t
    positivity
  set P := ∏ t ∈ range n, execMix a b ρ t with hPdef
  set U := ∏ t ∈ range n, max 1 (ρ t) with hU
  set V := ∏ t ∈ range n, max 1 (ρ t)⁻¹ with hV
  have hUpos : 0 < U := prod_pos fun t _ => lt_of_lt_of_le one_pos (le_max_left _ _)
  have hVpos : 0 < V := prod_pos fun t _ => lt_of_lt_of_le one_pos (le_max_left _ _)
  have hApart : seqLik a n ≤ 2 * U * P := by
    have := hinv n; linarith
  -- `B_n = B̂_n ∏ ρ_t⁻¹` and `max(1, ρ) ρ⁻¹ = max(1, ρ⁻¹)`.
  have hBsplit : seqLik b n * ∏ t ∈ range n, ρ t = Bh n := by
    simp only [hBh, seqLik, prod_mul_distrib]
  have hUV : U * (∏ t ∈ range n, ρ t)⁻¹ = V := by
    rw [hU, hV, ← prod_inv_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun t _ => ?_
    have := hρ t
    rcases le_total 1 (ρ t) with h | h
    · rw [max_eq_right h, max_eq_left (inv_le_one_of_one_le₀ h), mul_inv_cancel₀ this.ne']
    · rw [max_eq_left h, max_eq_right (one_le_inv₀ this |>.mpr h), one_mul]
  have hρprod : 0 < ∏ t ∈ range n, ρ t := prod_pos fun t _ => hρ t
  have hBpart : seqLik b n ≤ 2 * V * P := by
    have hb' : Bh n ≤ 2 * U * P := by have := hinv n; linarith
    have e : seqLik b n = Bh n * (∏ t ∈ range n, ρ t)⁻¹ := by
      rw [← hBsplit, mul_inv_cancel_right₀ hρprod.ne']
    rw [e, ← hUV]
    have hi : 0 < (∏ t ∈ range n, ρ t)⁻¹ := inv_pos.mpr hρprod
    calc Bh n * (∏ t ∈ range n, ρ t)⁻¹ ≤ 2 * U * P * (∏ t ∈ range n, ρ t)⁻¹ :=
          mul_le_mul_of_nonneg_right hb' hi.le
      _ = 2 * (U * (∏ t ∈ range n, ρ t)⁻¹) * P := by ring
  refine ⟨hApart, hBpart, ?_⟩
  -- In bits: `log₂ max(1, ρ) ≤ |log₂ ρ|` and `log₂ max(1, ρ⁻¹) ≤ |log₂ ρ|`, summed.
  have hlogU : Real.logb 2 (U : ℝ) ≤ ∑ t ∈ range n, |Real.logb 2 (ρ t : ℝ)| := by
    rw [hU]; push_cast
    rw [Real.logb_prod]
    · refine sum_le_sum fun t _ => ?_
      have hr : (0 : ℝ) < ρ t := by exact_mod_cast hρ t
      rcases le_total 1 (ρ t : ℝ) with h | h
      · rw [max_eq_right h]; exact le_abs_self _
      · rw [max_eq_left h, Real.logb_one]; exact abs_nonneg _
    · intro t _; exact (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
  have hlogV : Real.logb 2 (V : ℝ) ≤ ∑ t ∈ range n, |Real.logb 2 (ρ t : ℝ)| := by
    rw [hV]; push_cast
    rw [Real.logb_prod]
    · refine sum_le_sum fun t _ => ?_
      have hr : (0 : ℝ) < ρ t := by exact_mod_cast hρ t
      rcases le_total 1 (ρ t : ℝ)⁻¹ with h | h
      · rw [max_eq_right h, Real.logb_inv]; exact neg_le_abs _
      · rw [max_eq_left h, Real.logb_one]; exact abs_nonneg _
    · intro t _; exact (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hUR : (0 : ℝ) < U := by exact_mod_cast hUpos
  have hVR : (0 : ℝ) < V := by exact_mod_cast hVpos
  have hAR : (0 : ℝ) < seqLik a n := by exact_mod_cast hA
  have hBR : (0 : ℝ) < seqLik b n := by exact_mod_cast seqLik_pos hb n
  have bound : ∀ {X W : ℝ}, 0 < X → 0 < W → X ≤ 2 * W * P →
      -Real.logb 2 (P : ℝ) ≤ -Real.logb 2 X + 1 + Real.logb 2 W := by
    intro X W hX hW h
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hX h
    rw [Real.logb_mul (by positivity) hPR.ne', Real.logb_mul (by norm_num) hW.ne',
      Real.logb_self_eq_one (by norm_num)] at this
    linarith
  have bA := bound hAR hUR (by exact_mod_cast hApart)
  have bB := bound hBR hVR (by exact_mod_cast hBpart)
  have : -Real.logb 2 (P : ℝ) - 1 - ∑ t ∈ range n, |Real.logb 2 (ρ t : ℝ)| ≤
      min (-Real.logb 2 (seqLik a n : ℝ)) (-Real.logb 2 (seqLik b n : ℝ)) :=
    le_min (by linarith) (by linarith)
  linarith

end SequentialMixture

section Audit

#print axioms address_scale_square
#print axioms digit_context_square
#print axioms digit_emission_descends
#print axioms ktMass_bump
#print axioms kt_likelihood_laws
#print axioms path_face_normalized
#print axioms path_face_ge_min
#print axioms pathFace_const
#print axioms lamAt_eq_beta
#print axioms face_normalized
#print axioms treeWeight_arrive_off
#print axioms weight_step
#print axioms landmark_step
#print axioms wordSum_eq_sum
#print axioms mixture_is_probability
#print axioms standing_is_routed_counts
#print axioms depth_one_is_decision_27
#print axioms mixture_over_trees
#print axioms kraft_and_dominance
#print axioms digit_emission_normalized
#print axioms forced_digits_normalized
#print axioms kt_binary_ge
#print axioms digit_face_ge
#print axioms executed_split_laws
#print axioms face_cell_width
#print axioms cell_faces_partition
#print axioms digit_log_residual
#print axioms digit_log_residual_kt
#print axioms host_digit_bound_fails_downward
#print axioms lattice_path_laws
#print axioms lattice_path_floor
#print axioms lattice_path_deviation
#print axioms mix_ratio_bound
#print axioms weight_log_lipschitz
#print axioms lattice_step_telescope
#print axioms lattice_node_telescope
#print axioms rebase_log_residual
#print axioms path_cochain
#print axioms edge_log_derivative
#print axioms path_telescope_exact
#print axioms tree_telescope
#print axioms deposition_is_log_ratio
#print axioms concentrated_deposition
#print axioms tree_deposit_is_deposition
#print axioms unfounded_reads_prior
#print axioms founding_step
#print axioms founded_tree_same_law
#print axioms release_rule
#print axioms budget_eviction_changes_face
#print axioms sequential_mixture
#print axioms sequential_mixture_bounds
#print axioms sequential_mixture_executed

end Audit

end Holonics.HNN.LandmarkTree
