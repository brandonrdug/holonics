import Holonics.Compression.Landmark.Context.PriorMass
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Compression.Landmark.Context.BaseMeasure: the root's base measure, its code, floor and cost

[definition; agent-inferred] The receiving tree's root base (the contact-loop record of October 2,
§30–31; rebuild step 4, #73; Rust `compression::landmark::context::{BaseMeasure, base_sixteenths,
Topology::kt_based, based_floor, face_bits_at, mass_operand}`, the card's `tree_kt`). Each node of a
digit tree splits its two prior masses `2^(−j)` by one base `π` that every node of the digit tree
shares. `π` is read from the digit tree's root, before the cell's deposit: the root's face at the
even base, mixed with the even split at `½`, rounded to the receiver's grain `1/16` (ties up). The
computational object is the helical pair interaction; this owner is the receiving parametron's
landmark register, whose face it reads. Of the winding guide's six general objects it touches
**faces and placement** (each node's face is a normalized receiving face on a dyadic digit, and the
base is a placement shared down the tree) and the **tower thread** (the base is read at the root of
the restriction chain and carried to every node below it); the helix, the pair, the cell holonomy
and the tube stay attached, unchanged.

The Rust's digit `0` is Lean's `false`; `m_b = 2^j n_b + 1` are a node's masses at the even base
(the Rust's `halves`), `M = m_0 + m_1 = 2^j n + 2`.

```text
base       r = ⌊(2(8 m_0 + 4M) + M)/(2M)⌋ = ⌊16(½ k_0 + ¼) + ½⌋ ,  k_0 = m_0/M at the root ,
           π_0 = r/16 ,  π_1 = (16 − r)/16 ,  4 ≤ r ≤ 12 : every base mass in [¼, ¾]
empty      a root with no arrival: r = 8, π = ½  (the Rust's "no root yet" reads the same)
face       q_s(b) = (2^j n_b + 2π_b)/(2^j n + 2) = (16 m_b − 16 + 2·16π_b)/(16M)   (kt_based)
prior      a level with no arrival reads q(b) = π_b, whatever the stop weights   (Stop::Prior)
code       ∏_t q_root(x_t) = W_root over the based own weights ;  each face normalized ;
           the code sums to one over the words of each length under a causal context
floor      q_s(b) ≥ 1/(2(2^j n* + 2)) at every node and on the opened path, any stop weights
           (based_floor = 2(2^j n* + 2);  one bit below the even base's)
widths     n* = 6148, B = 8, L_R = 16, j = 3, P = 63:  M_p = 50, W = 37, κ = 20 (mass_operand = 16(2^j n* + 2)),
           R = 89; the largest operand 127 bits ≤ 128
cost       E^π_s ≥ E^½_s · g(k_s) g(m_s) ,  g(K) = ∏_(r<K) (2^j r + ½)/(2^j r + 1)   (π ≥ ¼)
           −log₂ g(K + 1) ≤ 1 + 3/2^(j+2) · (1 + ln K) ;  at j = 3, K ≤ 6148: < 2 bits a value, < 4 a leaf
tree       −log₂ ∏_t q_0(x_t) ≤ −log₂ prior_w(S)
             + Σ_(leaves s) [−log₂ (k_s/n_s)^(k_s) (m_s/n_s)^(m_s) + ½ log₂ n_s + j + c(k_s) + c(m_s)]
```

[proved-derived; formal-checked] What is proved.

1. **The base** (`rootSixteenths`, `rootSixteenths_round`, `rootSixteenths_mem`,
   `rootSixteenths_empty`, `rootBase`, `rootBase_quarter`, `rootBase_sum`, `rootBase_empty`): the
   Rust's integer division `⌊(2(8 m_0 + 4M) + M)/(2M)⌋` is `⌊16(½ k_0 + ¼) + ½⌋`, the mix rounded to
   the nearest sixteenth with ties up (the Rust's difference (a) from the notebook's
   `shared-g4`). Since `1 ≤ m_0 < M`, the mix lies in `(¼, ¾)` and its rounding in `[4, 12]`
   sixteenths, so each base mass is at least `¼`. A digit tree with no arrival has `m_0 = 1`,
   `M = 2`, and the formula gives `r = 8`: the Rust's `½` for a tree with no root yet (difference
   (c)) is the formula's own value there, so it needs no separate case.
2. **The face** (`basedFace`, `basedFace_pos`, `basedFace_sum`, `basedFace_half`,
   `rootBase_face_sixteenths`, `basedFace_zero`, `prior_read`): the face
   `(2^j n_b + 2π_b)/(2^j n + 2)` is positive and normalized for every positive normalized base; at
   `π = ½` it is the even base's urn face (`PriorMass.priorMass_face`); at the root's base it is the
   Rust's `(16 m_b − 16 + 2·16π_b, 16M)`. A node with no arrival reads `π_b`, so a read past the
   last stored level reads `π_b` at every level below it whatever the stop weights: the Rust's
   `Stop::Prior` read of `π_0` (difference (b)) is the full tree's own read there, where the
   notebook's `½` was not. It keeps every base mass at least `¼` by item 1.
3. **The code** (`basedOwn`, `basedOwn_snoc`, `baseEmitted`, `baseEmitted_face_normalized`,
   `baseEmitted_eq_weight`, `baseEmitted_sum`, `rootBaseOf`): for **any** base read from the
   passage before each arrival (positive and normalized), the emitted code is the product of
   positive normalized path faces, it is the root's weight over the based own weights
   (`Tree.own_weight_step₀` at depth `0`), and under a causal context it sums to one over the words
   of each length. The root's base (`rootBaseOf`) reads only the counts the root holds before the
   arrival, every arrival being routed through the root, the root itself included: the code stays a
   normalized sequential code using only past data.
4. **The floor** (`basedFace_ge`, `rootBase_face_ge`, `rootBase_path_face_ge`): with each base
   mass at least `¼`, a node with at most `n*` arrivals reads each digit value at least at
   `1/(2(2^j n* + 2))`, and so does the opened path's face at every depth under any stop weights in
   `[0, 1]`. This is the doubled floor the Rust's `based_floor` gives `face_bits_at`. It does not
   depend on the depth.
5. **The widths at depth 63** (`campaign_face_bits`, `campaign_carrier_bits`,
   `campaign_mass_operand`, `campaign_operands`, `campaign_rule_floor`): campaign 1's `M_p = 50` (one more than the even
   base's 49), `W = 37`, `κ = 20` bits of `16(2^3·6148 + 2)`, so the β step's mantissa division
   `2W + κ + M + 1 = 145` passes `u128` and the carrier rebases at `R = 89 ≥ W`; every operand the
   Rust (`Widths::operand_bits`, `admitted`) and the card (`single_division_admitted`) ask for is at
   most 127 bits. The rule (`Landmarks::face_rule`) reads `⌊2^(M_p)/based_floor⌋`; doubling the
   floor's reciprocal raises `M_p` by exactly one bit (`⌈log₂ 2x⌉ = ⌈log₂ x⌉ + 1`), so
   `⌊2^(M_p + 1)/(2K)⌋ = ⌊2^(M_p)/K⌋` and the rule at depth 63 is the even base's.
6. **The cost over the even base** (`baseGain`, `basedOwn_half`, `basedOwn_ge`, `baseCost`,
   `baseCost_succ_le`, `baseCost_campaign`, `leaf_cost_campaign`, `base_tree_redundancy`,
   `rootBase_tree_redundancy`): at each node the based own weight is at least the even base's urn
   weight times `g(k)·g(m)`, `g(K) = ∏_(r<K) (2^j r + ½)/(2^j r + 1)`, because every base mass is at
   least `¼`. So the tree's redundancy against **every** pruned tree `S` with positive prior under
   any stop weights in `[0, 1)` is `PriorMass.priorMass_tree_redundancy`'s, plus at most
   `c(k_s) + c(m_s)` bits a leaf, `c = −log₂ g`. `c(K + 1) ≤ 1 + 3/2^(j+2)(1 + ln K)` (the first
   arrival of a value costs at most one bit, each later one `log₂ e · ½/(2^j r + ½)`); at campaign
   1's `j = 3` and `n* = 6148`, `c < 2` bits a value and `c(k) + c(m) < 4` bits a leaf.

[agent-inferred] **The worst case is a one-sided leaf against the root.** The bound of item 6 is
attained in the limit by a leaf that sees only one value while the root's base sits at `¼` for that
value: then `E^π/E^½ = g(k)` exactly. A leaf whose values agree with the root's base gains instead;
which wins on a passage is the measurement of the contact-loop record's §31 (held out, model −
PPM-2 from −462 2/16 to −560 15/16 bits), not a theorem.

[conditional] **What items 3 and 6 cover in the Rust.** They bound one digit tree's exact code,
the ideal tree's, as `PriorMass` item 7 does, with the same conditions (the unbounded register,
`j ≥ 1`, addresses padded to `D`). The executed lattice code adds the lattice's drift
(`Context/Drift`, `Context/StoredDrift`, `Context/JoinDrift`), whose floor is item 4's: the base is
an exact sixteenth, so it adds no drift of its own. The enlarged tree's join and the concave form of
the leaves' charges are not composed here, as in `PriorMass`.
-/

namespace Holonics.Compression.Landmark.Context.BaseMeasure

open Holonics.Compression.Landmark.Context.Tree
open Holonics.Compression.Landmark.Context.PriorMass
open Finset

/-! ### 1. The root's base in sixteenths -/

/-- [definition] **The root's base in sixteenths** (Rust `base_sixteenths`, the card's `tree_kt`):
`r = ⌊(2(8 m_0 + 4M) + M)/(2M)⌋` with the root's masses `m_0 = 2^j n_0 + 1` (digit `0`, Lean
`false`) and `M = 2^j n + 2` at the even base. -/
def rootSixteenths (j : ℕ) (n : Bool → ℕ) : ℕ :=
  (2 * (8 * (2 ^ j * n false + 1) + 4 * (2 ^ j * (n true + n false) + 2)) +
      (2 ^ j * (n true + n false) + 2)) / (2 * (2 ^ j * (n true + n false) + 2))

/-- [proved-derived; formal-checked] **`rootSixteenths_round`: the base is the mix rounded to a
sixteenth, ties up.** With the root's even-base face `k_0 = m_0/M`,
`r ≤ 16(½ k_0 + ¼) + ½ < r + 1`, so `r = ⌊16(½ k_0 + ¼) + ½⌋`. -/
theorem rootSixteenths_round (j : ℕ) (n : Bool → ℕ) :
    (rootSixteenths j n : ℚ) ≤
        16 * ((2 ^ j * (n false : ℚ) + 1) / (2 ^ j * ((n true : ℚ) + n false) + 2) / 2 + 1 / 4) +
          1 / 2 ∧
      16 * ((2 ^ j * (n false : ℚ) + 1) / (2 ^ j * ((n true : ℚ) + n false) + 2) / 2 + 1 / 4) +
          1 / 2 < rootSixteenths j n + 1 := by
  set A := 2 * (8 * (2 ^ j * n false + 1) + 4 * (2 ^ j * (n true + n false) + 2)) +
      (2 ^ j * (n true + n false) + 2) with hA
  set B := 2 * (2 ^ j * (n true + n false) + 2) with hB
  have hBpos : 0 < B := by omega
  have hval : 16 * ((2 ^ j * (n false : ℚ) + 1) / (2 ^ j * ((n true : ℚ) + n false) + 2) / 2 +
      1 / 4) + 1 / 2 = (A : ℚ) / B := by
    have hM : (0 : ℚ) < 2 ^ j * ((n true : ℚ) + n false) + 2 := by positivity
    rw [hA, hB]
    push_cast
    field_simp
    ring
  have hr : rootSixteenths j n = A / B := rfl
  rw [hval, hr]
  have h1 : A / B * B ≤ A := Nat.div_mul_le_self A B
  have h2 : A < (A / B + 1) * B := by
    have := Nat.div_add_mod A B
    have := Nat.mod_lt A hBpos
    nlinarith
  have hBq : (0 : ℚ) < B := by exact_mod_cast hBpos
  constructor
  · rw [le_div_iff₀ hBq]
    exact_mod_cast h1
  · rw [div_lt_iff₀ hBq]
    exact_mod_cast h2

/-- [proved-derived; formal-checked] **`rootSixteenths_mem`: the base lies in `[4, 12]`
sixteenths.** Since `1 ≤ m_0 < M`, the mix lies in `(¼, ¾)` and its rounding in `[4, 12]`. -/
theorem rootSixteenths_mem (j : ℕ) (n : Bool → ℕ) :
    4 ≤ rootSixteenths j n ∧ rootSixteenths j n ≤ 12 := by
  have hM : 2 ^ j * n false + 1 < 2 ^ j * (n true + n false) + 2 := by rw [mul_add]; omega
  unfold rootSixteenths
  constructor
  · rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  · have : (2 * (8 * (2 ^ j * n false + 1) + 4 * (2 ^ j * (n true + n false) + 2)) +
        (2 ^ j * (n true + n false) + 2)) / (2 * (2 ^ j * (n true + n false) + 2)) < 13 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    omega

/-- [proved-derived; formal-checked] **`rootSixteenths_empty`: a root with no arrival reads `8`**,
the even split `½`: the Rust's `[8, 8]` for a digit tree with no root yet is the formula's value. -/
theorem rootSixteenths_empty (j : ℕ) : rootSixteenths j (fun _ => 0) = 8 := by
  simp [rootSixteenths]

/-- [definition] **The root's base** `π_0 = r/16`, `π_1 = (16 − r)/16`. -/
def rootBase (j : ℕ) (n : Bool → ℕ) : Bool → ℚ := fun b =>
  if b then (16 - (rootSixteenths j n : ℚ)) / 16 else (rootSixteenths j n : ℚ) / 16

/-- [proved-derived; formal-checked] **Every base mass lies in `[¼, ¾]`.** -/
theorem rootBase_quarter (j : ℕ) (n : Bool → ℕ) (b : Bool) :
    1 / 4 ≤ rootBase j n b ∧ rootBase j n b ≤ 3 / 4 := by
  obtain ⟨h4, h12⟩ := rootSixteenths_mem j n
  have h4' : (4 : ℚ) ≤ rootSixteenths j n := by exact_mod_cast h4
  have h12' : (rootSixteenths j n : ℚ) ≤ 12 := by exact_mod_cast h12
  cases b <;> simp only [rootBase, Bool.false_eq_true, if_false, if_true] <;>
    constructor <;> linarith

theorem rootBase_pos (j : ℕ) (n : Bool → ℕ) (b : Bool) : 0 < rootBase j n b := by
  linarith [(rootBase_quarter j n b).1]

theorem rootBase_sum (j : ℕ) (n : Bool → ℕ) : rootBase j n true + rootBase j n false = 1 := by
  simp only [rootBase, if_true, Bool.false_eq_true, if_false]
  ring

theorem rootBase_empty (j : ℕ) (b : Bool) : rootBase j (fun _ => 0) b = 1 / 2 := by
  cases b <;> simp [rootBase, rootSixteenths_empty] <;> norm_num

/-! ### 2. The face at a base -/

/-- [definition] **A node's face at a base `π`**: `(2^j n_b + 2π_b)/(2^j n + 2)`, the node's two
prior masses `2^(−j)` split by `π` (`2^(1−j) π_b` each). -/
def basedFace (j : ℕ) (π : Bool → ℚ) (n : Bool → ℕ) (b : Bool) : ℚ :=
  (2 ^ j * (n b : ℚ) + 2 * π b) / (2 ^ j * ((n true : ℚ) + n false) + 2)

theorem basedFace_pos (j : ℕ) {π : Bool → ℚ} (hπ : ∀ b, 0 < π b) (n : Bool → ℕ) (b : Bool) :
    0 < basedFace j π n b := by
  unfold basedFace
  have := hπ b
  positivity

theorem basedFace_sum (j : ℕ) {π : Bool → ℚ} (hs : π true + π false = 1) (n : Bool → ℕ) :
    ∑ b, basedFace j π n b = 1 := by
  have hM : (0 : ℚ) < 2 ^ j * ((n true : ℚ) + n false) + 2 := by positivity
  rw [Fintype.sum_bool]
  unfold basedFace
  rw [← add_div, div_eq_one_iff_eq hM.ne']
  linear_combination 2 * hs

/-- At the even base the face is the even base's urn face (`PriorMass.priorMass_face`). -/
theorem basedFace_half (j : ℕ) (n : Bool → ℕ) (b : Bool) :
    basedFace j (fun _ => 1 / 2) n b = dirichletPredictive (massWeight j) n b := by
  rw [priorMass_face]
  unfold basedFace
  norm_num

/-- The even base's face in the urn's form `(α + n_b)/(2α + n)`, `α = 2^(−j)`. -/
theorem basedFace_half_urn (j : ℕ) (n : Bool → ℕ) (b : Bool) :
    basedFace j (fun _ => 1 / 2) n b =
      (massWeight j + n b) / (massWeight j + massWeight j + ((n true + n false : ℕ) : ℚ)) := by
  have h2 : (0 : ℚ) < 2 ^ j := by positivity
  unfold basedFace massWeight
  push_cast
  field_simp
  ring

/-- [proved-derived; formal-checked] **`rootBase_face_sixteenths`: the face the Rust reads.** At
the root's base the face is `(16 m_b − 16 + 2·16π_b)/(16M)` with `m_b = 2^j n_b + 1`,
`M = 2^j n + 2` (`Topology::kt_based`, the card's `tree_kt`). -/
theorem rootBase_face_sixteenths (j : ℕ) (n0 n : Bool → ℕ) (b : Bool) :
    basedFace j (rootBase j n0) n b =
      ((16 * (2 ^ j * n b + 1) - 16 +
          2 * (if b then 16 - rootSixteenths j n0 else rootSixteenths j n0) : ℕ) : ℚ) /
        ((16 * (2 ^ j * (n true + n false) + 2) : ℕ) : ℚ) := by
  have h12 := (rootSixteenths_mem j n0).2
  have hM : (0 : ℚ) < 2 ^ j * ((n true : ℚ) + n false) + 2 := by positivity
  cases b
  · have e : 16 * (2 ^ j * n false + 1) - 16 + 2 * (if false = true then 16 - rootSixteenths j n0
        else rootSixteenths j n0) = 16 * (2 ^ j * n false) + 2 * rootSixteenths j n0 := by
      simp only [Bool.false_eq_true, if_false]
      omega
    rw [e]
    unfold basedFace rootBase
    simp only [Bool.false_eq_true, if_false]
    push_cast
    field_simp
  · have hr : rootSixteenths j n0 ≤ 16 := by omega
    have e : 16 * (2 ^ j * n true + 1) - 16 + 2 * (if true = true then 16 - rootSixteenths j n0
        else rootSixteenths j n0) = 16 * (2 ^ j * n true) + 2 * (16 - rootSixteenths j n0) := by
      simp only [if_true]
      omega
    rw [e]
    unfold basedFace rootBase
    simp only [if_true]
    push_cast [Nat.cast_sub hr]
    field_simp

/-- A node with no arrival reads the base. -/
theorem basedFace_zero (j : ℕ) (π : Bool → ℚ) (b : Bool) :
    basedFace j π (fun _ => 0) b = π b := by
  simp [basedFace]

/-- [proved-derived; formal-checked] **`prior_read`: past the last stored level the path reads the
base.** If no arrival reached the opened path's nodes at depths `d..D`, its face at depth `d` is
`π_b` under **any** stop weights: the Rust's `Stop::Prior` read of `π_0` (`½` at the even base). -/
theorem prior_read (j : ℕ) (π : Bool → ℚ) (N : ℕ → Bool → ℕ) (lam : ℕ → ℚ) {D d : ℕ}
    (hd : d ≤ D) (hz : ∀ d', d ≤ d' → d' ≤ D → N d' = fun _ => 0) (b : Bool) :
    pathFace (fun d => basedFace j π (N d)) lam D d b = π b :=
  pathFace_const _ lam D b (π b) d hd fun d' h1 h2 => by
    rw [hz d' h1 h2, basedFace_zero]

/-! ### 3. The floor -/

/-- [proved-derived; formal-checked] **`basedFace_ge`: the node's floor at a base.** With base mass
`π_b ≥ μ ≥ 0` and at most `N` arrivals, the face of `b` is at least `2μ/(2^j N + 2)`. -/
theorem basedFace_ge (j : ℕ) {π : Bool → ℚ} {μ : ℚ} (hμ0 : 0 ≤ μ) (n : Bool → ℕ) {N : ℕ}
    (hN : n true + n false ≤ N) (b : Bool) (hμ : μ ≤ π b) :
    2 * μ / (2 ^ j * (N : ℚ) + 2) ≤ basedFace j π n b := by
  have hN' : ((n true : ℚ) + n false) ≤ N := by exact_mod_cast hN
  have h2 : (0 : ℚ) < 2 ^ j := by positivity
  have hd : (0 : ℚ) < 2 ^ j * ((n true : ℚ) + n false) + 2 := by positivity
  have hb0 : (0 : ℚ) ≤ 2 ^ j * (n b : ℚ) := by positivity
  have hnum : 2 * μ ≤ 2 ^ j * (n b : ℚ) + 2 * π b := by linarith
  unfold basedFace
  calc 2 * μ / (2 ^ j * (N : ℚ) + 2)
      ≤ 2 * μ / (2 ^ j * ((n true : ℚ) + n false) + 2) :=
        div_le_div_of_nonneg_left (by linarith) hd (by nlinarith)
    _ ≤ (2 ^ j * (n b : ℚ) + 2 * π b) / (2 ^ j * ((n true : ℚ) + n false) + 2) :=
        div_le_div_of_nonneg_right hnum hd.le

/-- [proved-derived; formal-checked] **`rootBase_face_ge`: the root base's floor is
`1/(2(2^j n* + 2))`**, one bit below the even base's `1/(2^j n* + 2)` (Rust `based_floor`). -/
theorem rootBase_face_ge (j : ℕ) (n0 n : Bool → ℕ) {N : ℕ} (hN : n true + n false ≤ N)
    (b : Bool) : 1 / (2 * (2 ^ j * (N : ℚ) + 2)) ≤ basedFace j (rootBase j n0) n b := by
  have h := basedFace_ge j (μ := 1 / 4) (by norm_num) n hN b (rootBase_quarter j n0 b).1
  have hd : (0 : ℚ) < 2 ^ j * (N : ℚ) + 2 := by positivity
  calc 1 / (2 * (2 ^ j * (N : ℚ) + 2)) = 2 * (1 / 4) / (2 ^ j * (N : ℚ) + 2) := by
        field_simp
        ring
    _ ≤ _ := h

/-- [proved-derived; formal-checked] **`rootBase_path_face_ge`: the path's floor at the root's
base.** If every node of the opened path holds at most `n` arrivals, the path face at every depth is
at least `1/(2(2^j n + 2))` under **any** stop weights `λ_d ∈ [0, 1]`, through
`Tree.path_face_ge_min`: the floor the lattice width `M_p` reads (Rust `face_bits_at`). -/
theorem rootBase_path_face_ge {Ltr : Type*} (j : ℕ) (n0 : Bool → ℕ) (N : TreeStanding Ltr Bool)
    (lam : ℕ → ℚ) (D : ℕ) (hl : ∀ d < D, 0 ≤ lam d ∧ lam d ≤ 1) (a : List Ltr) (n : ℕ)
    (hn : ∀ d ≤ D, N (a.take d) true + N (a.take d) false ≤ n) (b : Bool) :
    ∀ d ≤ D, 1 / (2 * (2 ^ j * (n : ℚ) + 2)) ≤
      pathFace (fun d => basedFace j (rootBase j n0) (N (a.take d))) lam D d b := by
  intro d hd
  exact (path_face_ge_min _ lam D b hl).1 _ d hd fun d' _ h2 =>
    rootBase_face_ge j n0 (N (a.take d')) (hn d' h2) b

/-! ### 4. The widths at campaign 1's depth 63 -/

/-- [proved-derived; formal-checked] **`campaign_face_bits`: `M_p = 50`.** At `n* = 6148`,
`B = 8`, `L_R = 16`, `j = 3`, `P = 63`, the least `M` with
`2^M ≥ 3 B L_R · 2(2^j n* + 2) · (n* P² + 2P + 1)` is `50` (Rust `face_bits_at` at the root's
base; `49` at the even base). -/
theorem campaign_face_bits :
    2 ^ 49 < 3 * 8 * 16 * (2 * (2 ^ 3 * 6148 + 2)) * (6148 * 63 ^ 2 + 2 * 63 + 1) ∧
      3 * 8 * 16 * (2 * (2 ^ 3 * 6148 + 2)) * (6148 * 63 ^ 2 + 2 * 63 + 1) ≤ 2 ^ 50 := by
  norm_num

/-- `W = 37`: the least `W` with `2^W ≥ 12 B L_R (2n* + 1) P²` (Rust `carrier_width`). -/
theorem campaign_carrier_bits :
    2 ^ 36 < 12 * 8 * 16 * (2 * 6148 + 1) * 63 ^ 2 ∧ 12 * 8 * 16 * (2 * 6148 + 1) * 63 ^ 2 ≤ 2 ^ 37 := by
  norm_num

/-- `κ = 20`: the bits of `16(2^j n* + 2)` (Rust `mass_operand` at the root's base), so every face
denominator `16M` is below `2^κ`. -/
theorem campaign_mass_operand :
    2 ^ 19 ≤ 16 * (2 ^ 3 * 6148 + 2) ∧ 16 * (2 ^ 3 * 6148 + 2) < 2 ^ 20 := by
  norm_num

/-- [proved-derived; formal-checked] **`campaign_operands`: every operand fits `u128`.** At
`M = 50`, `W = 37`, `κ = 20`: the β step's mantissa division `2W + κ + M + 1 = 145` passes 128, so
the carrier rebases at `R = 126 − W = 89 ≥ W`; the lattice operands
`max(2M + 2, M + κ + 3, M + W + 3, W + κ + M) = 107`, the rebased division `R + W + 1 = 127`, and
the card's single divisions `max(2M + κ + 3, 2W + M + 3) = 127` are all at most 128 bits
(Rust `Widths::operand_bits`, `admitted`, `single_division_admitted`). -/
theorem campaign_operands :
    128 < 2 * 37 + 20 + 50 + 1 ∧ 37 ≤ 126 - 37 ∧
      max (max (max (2 * 50 + 2) (50 + 20 + 3)) (50 + 37 + 3)) (37 + 20 + 50) = 107 ∧
      (126 - 37) + 37 + 1 = 127 ∧ max (2 * 50 + 20 + 3) (2 * 37 + 50 + 3) = 127 := by
  decide

/-- [proved-derived; formal-checked] **`campaign_rule_floor`: the rule's floor is the even base's.**
At the even base `M_p = 49` (the least `M` with `2^M ≥ 3 B L_R (2^j n* + 2)(n* P² + 2P + 1)`), and
the rule's floor `⌊2^(M_p)/based_floor⌋` (`Landmarks::face_rule`) is `11445329024` at both bases:
`⌊2^50/(2(2^3·6148 + 2))⌋ = ⌊2^49/(2^3·6148 + 2)⌋`. The rule's other terms read `W`, `R` and `B`,
which the base does not change (`W` reads no floor, `R = 126 − W`), so campaign 1's rule at depth 63
is the even base's. -/
theorem campaign_rule_floor :
    (2 ^ 48 < 3 * 8 * 16 * (2 ^ 3 * 6148 + 2) * (6148 * 63 ^ 2 + 2 * 63 + 1) ∧
      3 * 8 * 16 * (2 ^ 3 * 6148 + 2) * (6148 * 63 ^ 2 + 2 * 63 + 1) ≤ 2 ^ 49) ∧
      2 ^ 50 / (2 * (2 ^ 3 * 6148 + 2)) = 11445329024 ∧
      2 ^ 49 / (2 ^ 3 * 6148 + 2) = 11445329024 := by
  norm_num

/-! ### 5. The code at a base read from the passage -/

section Code

variable {Ltr : Type*} [Fintype Ltr] [DecidableEq Ltr]

/-- [definition] **A base read from the passage**: the base an arrival meets is a function of the
observations before it (oldest first). -/
abbrev Base (Ltr : Type*) := List (List Ltr × Bool) → Bool → ℚ

/-- [definition] The counts routed to node `s`. -/
def countsAt (obs : List (List Ltr × Bool)) (s : List Ltr) : Bool → ℕ := fun b => routedCount obs s b

/-- [definition] **The face node `s` reads** after the observations `obs`, at the base they give. -/
def faceAt (j : ℕ) (base : Base Ltr) (obs : List (List Ltr × Bool)) (s : List Ltr) : Bool → ℚ :=
  basedFace j (base obs) (countsAt obs s)

/-- [definition] The based own weights, newest observation first. -/
def ownRev (j : ℕ) (base : Base Ltr) : List (List Ltr × Bool) → List Ltr → ℚ
  | [], _ => 1
  | o :: obs, s => if o.1.take s.length = s then
      ownRev j base obs s * faceAt j base obs.reverse s o.2 else ownRev j base obs s

/-- [definition] **The based own weight** `E_s`: the product of the faces node `s` read at each
arrival routed to it, each at the base and counts before that arrival. -/
def basedOwn (j : ℕ) (base : Base Ltr) (obs : List (List Ltr × Bool)) : List Ltr → ℚ :=
  ownRev j base obs.reverse

omit [Fintype Ltr] in
theorem basedOwn_snoc (j : ℕ) (base : Base Ltr) (obs : List (List Ltr × Bool)) (a : List Ltr)
    (c : Bool) (s : List Ltr) :
    basedOwn j base (obs ++ [(a, c)]) s = if a.take s.length = s then
      basedOwn j base obs s * faceAt j base obs s c else basedOwn j base obs s := by
  simp [basedOwn, ownRev]

omit [Fintype Ltr] in
theorem countsAt_snoc (obs : List (List Ltr × Bool)) (a : List Ltr) (c : Bool) (s : List Ltr)
    (b : Bool) : countsAt (obs ++ [(a, c)]) s b =
      countsAt obs s b + if a.take s.length = s ∧ c = b then 1 else 0 := by
  by_cases h : a.take s.length = s <;> by_cases hc : c = b <;>
    simp [countsAt, routedCount, routed_snoc, h, hc]

omit [Fintype Ltr] in
theorem countsAt_nil (s : List Ltr) (b : Bool) : countsAt ([] : List (List Ltr × Bool)) s b = 0 := by
  simp [countsAt, routedCount, routed]

omit [Fintype Ltr] in
/-- Every arrival is routed through the root: the root's counts are the passage's. -/
theorem routed_root (obs : List (List Ltr × Bool)) : routed obs [] = obs.map Prod.snd := by
  simp [routed]

omit [Fintype Ltr] in
theorem basedOwn_pos (j : ℕ) {base : Base Ltr} (hb : ∀ obs b, 0 < base obs b) :
    ∀ obs s, 0 < basedOwn j base obs s := by
  intro obs s
  induction obs using List.reverseRecOn with
  | nil => simp [basedOwn, ownRev]
  | append_singleton obs o ih =>
    obtain ⟨a, c⟩ := o
    rw [basedOwn_snoc]
    split_ifs
    · exact mul_pos ih (basedFace_pos j (hb obs) _ c)
    · exact ih

/-- [definition] The emitted code, newest observation first. -/
def baseEmittedRev (j : ℕ) (base : Base Ltr) (w : ℕ → ℚ) (D : ℕ) :
    List (List Ltr × Bool) → ℚ
  | [] => 1
  | o :: obs => baseEmittedRev j base w D obs *
      pathFace (fun d => faceAt j base obs.reverse (o.1.take d))
        (ownLam w (basedOwn j base obs.reverse) D o.1) D 0 o.2

/-- [definition] **The code the based tree emits**: each arrival read at the root of its opened
path, every node's face at the base and counts before the arrival, and the stop weights over the
based own weights. -/
def baseEmitted (j : ℕ) (base : Base Ltr) (w : ℕ → ℚ) (D : ℕ) (obs : List (List Ltr × Bool)) : ℚ :=
  baseEmittedRev j base w D obs.reverse

theorem baseEmitted_snoc (j : ℕ) (base : Base Ltr) (w : ℕ → ℚ) (D : ℕ)
    (obs : List (List Ltr × Bool)) (a : List Ltr) (c : Bool) :
    baseEmitted j base w D (obs ++ [(a, c)]) = baseEmitted j base w D obs *
      pathFace (fun d => faceAt j base obs (a.take d)) (ownLam w (basedOwn j base obs) D a) D 0 c := by
  simp [baseEmitted, baseEmittedRev]

/-- [proved-derived; formal-checked] **`baseEmitted_face_normalized`: every path face is positive
and normalized**, at every depth, under any stop weights in `[0, 1)`, for any positive normalized
base. -/
theorem baseEmitted_face_normalized (j : ℕ) {base : Base Ltr} (hb : ∀ obs b, 0 < base obs b)
    (hs : ∀ obs, base obs true + base obs false = 1) {w : ℕ → ℚ} (hw : StopLaw₀ w) (D : ℕ)
    (obs : List (List Ltr × Bool)) (a : List Ltr) :
    ∀ d ≤ D, (∀ c, 0 < pathFace (fun d => faceAt j base obs (a.take d))
        (ownLam w (basedOwn j base obs) D a) D d c) ∧
      ∑ c, pathFace (fun d => faceAt j base obs (a.take d))
        (ownLam w (basedOwn j base obs) D a) D d c = 1 :=
  own_face_positive_normalized hw (basedOwn_pos j hb obs) _ D a
    (fun _ _ c => basedFace_pos j (hb obs) _ c) fun _ _ => basedFace_sum j (hs obs) _

/-- [proved-derived; formal-checked] **`baseEmitted_eq_weight`: the emitted code is the root's
weight.** When every address reaches depth `D`, the product of the path faces over the passage is
the tree's weight at the root over the based own weights, for **any** positive base read from the
passage before each arrival (`Tree.own_weight_step₀` at depth `0`, from `Tree.ownWeight_one`). -/
theorem baseEmitted_eq_weight (j : ℕ) {base : Base Ltr} (hb : ∀ obs b, 0 < base obs b)
    {w : ℕ → ℚ} (hw : StopLaw₀ w) (D : ℕ) (obs : List (List Ltr × Bool))
    (hD : ∀ o ∈ obs, D ≤ o.1.length) :
    baseEmitted j base w D obs = ownWeight w (basedOwn j base obs) D [] := by
  induction obs using List.reverseRecOn with
  | nil =>
    have e : basedOwn j base ([] : List (List Ltr × Bool)) = fun _ => 1 := by
      funext s
      simp [basedOwn, ownRev]
    rw [e, ownWeight_one]
    rfl
  | append_singleton obs o ih =>
    have hD' : D ≤ o.1.length := hD o (by simp)
    have ih' := ih fun o' h => hD o' (by simp [h])
    obtain ⟨a, c⟩ := o
    rw [baseEmitted_snoc, ih']
    have h := own_weight_step₀ hw (basedOwn_pos j hb obs) (E' := basedOwn j base (obs ++ [(a, c)]))
      hD' (fun d => faceAt j base obs (a.take d)) c
      (fun s hs => by rw [basedOwn_snoc, if_neg hs])
      (fun d _ => by rw [basedOwn_snoc, if_pos (opens_take a d)]) 0 (Nat.zero_le _)
    simp only [Nat.sub_zero, List.take_zero] at h
    exact h.symm

/-- [proved-derived; formal-checked] **`baseEmitted_sum`: the based code is complete.** Under a
causal context, the emitted masses of the `2^n` binary words of length `n` sum to one, for any
positive normalized base read from the passage and any stop weights in `[0, 1)`. -/
theorem baseEmitted_sum (j : ℕ) {base : Base Ltr} (hb : ∀ obs b, 0 < base obs b)
    (hs : ∀ obs, base obs true + base obs false = 1) {w : ℕ → ℚ} (hw : StopLaw₀ w)
    (ctx : List Bool → List Ltr) (D n : ℕ) :
    ∑ v : Fin n → Bool, baseEmitted j base w D (observations ctx (List.ofFn v)) = 1 := by
  have hn : wordSum n (fun h => baseEmitted j base w D (observations ctx h)) = 1 := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [wordSum]
      have e : (fun h => ∑ c, baseEmitted j base w D (observations ctx (c :: h))) =
          fun h => baseEmitted j base w D (observations ctx h) := by
        funext h
        simp only [observations, baseEmitted_snoc, ← Finset.mul_sum]
        rw [(baseEmitted_face_normalized j hb hs hw D _ (ctx h) 0 (Nat.zero_le _)).2, mul_one]
      rw [e, ih]
  rwa [wordSum_eq_sum] at hn

/-- [definition] **The root's base read from the passage** (Rust `BaseMeasure::Root`): the root's
counts before the arrival, every arrival routed through the root (`routed_root`). -/
def rootBaseOf (j : ℕ) : Base Ltr := fun obs => rootBase j (countsAt obs [])

omit [Fintype Ltr] in
theorem rootBaseOf_pos (j : ℕ) : ∀ obs b, 0 < rootBaseOf (Ltr := Ltr) j obs b :=
  fun _ _ => rootBase_pos j _ _

omit [Fintype Ltr] in
theorem rootBaseOf_sum (j : ℕ) : ∀ obs, rootBaseOf (Ltr := Ltr) j obs true +
    rootBaseOf j obs false = 1 :=
  fun _ => rootBase_sum j _

omit [Fintype Ltr] in
theorem rootBaseOf_quarter (j : ℕ) : ∀ obs b, 1 / 4 ≤ rootBaseOf (Ltr := Ltr) j obs b :=
  fun _ _ => (rootBase_quarter j _ _).1

end Code

/-! ### 6. The cost over the even base and the tree's redundancy -/

/-- [definition] **The gain factor** `g(K) = ∏_(r<K) (2^j r + 2μ)/(2^j r + 1)`: what `K` arrivals of
one value at base mass at least `μ` keep of the even base's weight. -/
def baseGain (j : ℕ) (μ : ℚ) (K : ℕ) : ℚ :=
  ∏ r ∈ range K, ((2 ^ j * (r : ℚ) + 2 * μ) / (2 ^ j * (r : ℚ) + 1))

theorem baseGain_pos (j : ℕ) {μ : ℚ} (hμ : 0 < μ) (K : ℕ) : 0 < baseGain j μ K :=
  Finset.prod_pos fun r _ => by positivity

theorem baseGain_succ (j : ℕ) (μ : ℚ) (K : ℕ) :
    baseGain j μ (K + 1) = baseGain j μ K * ((2 ^ j * (K : ℚ) + 2 * μ) / (2 ^ j * (K : ℚ) + 1)) := by
  rw [baseGain, prod_range_succ, ← baseGain]

/-- The one-arrival step behind `basedOwn_ge`. -/
theorem gain_step {E G1 G2 Eπ x N f μ π : ℚ} (hE : 0 ≤ E * G1 * G2) (hih : E * G1 * G2 ≤ Eπ)
    (hx : 0 ≤ x) (hN : 0 < N) (hμ : 0 < μ) (hπ : μ ≤ π) (hf : f = x + 1) :
    E * (f / N) * (G1 * ((x + 2 * μ) / (x + 1))) * G2 ≤ Eπ * ((x + 2 * π) / N) := by
  subst hf
  have hx1 : 0 < x + 1 := by linarith
  have e : E * ((x + 1) / N) * (G1 * ((x + 2 * μ) / (x + 1))) * G2 =
      (E * G1 * G2) * ((x + 2 * μ) / N) := by
    field_simp
  rw [e]
  have hEπ : 0 ≤ Eπ := hE.trans hih
  calc (E * G1 * G2) * ((x + 2 * μ) / N) ≤ Eπ * ((x + 2 * μ) / N) :=
        mul_le_mul_of_nonneg_right hih (by positivity)
    _ ≤ Eπ * ((x + 2 * π) / N) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hN.le) hEπ

section Redundancy

variable {Ltr : Type*} [Fintype Ltr] [DecidableEq Ltr]

/-- [definition] The even base `½` as a base read from the passage. -/
def halfBase : Base Ltr := fun _ _ => 1 / 2

omit [Fintype Ltr] in
/-- [proved-derived; formal-checked] **At the even base the based own weight is the urn's
likelihood** `U_α(k, m)`, `α = 2^(−j)` (`PriorMass.urnBool`), of what reached the node. -/
theorem basedOwn_half (j : ℕ) : ∀ (obs : List (List Ltr × Bool)) s,
    basedOwn j halfBase obs s =
      urnBool (massWeight j) (countsAt obs s true) (countsAt obs s false) := by
  intro obs s
  induction obs using List.reverseRecOn with
  | nil => simp [basedOwn, ownRev, countsAt_nil, urnBool_zero]
  | append_singleton obs o ih =>
    obtain ⟨a, c⟩ := o
    rw [basedOwn_snoc, countsAt_snoc, countsAt_snoc]
    by_cases h : a.take s.length = s
    · rw [if_pos h, ih, faceAt, show (halfBase obs : Bool → ℚ) = fun _ => 1 / 2 from rfl,
        basedFace_half_urn]
      cases c
      · simp only [h, true_and, Bool.false_eq_true, if_true, if_false, add_zero]
        rw [urnBool_succ_right (massWeight_pos j)]
      · simp only [h, true_and, Bool.true_eq_false, if_true, if_false, add_zero]
        rw [urnBool_succ_left (massWeight_pos j)]
    · simp [h, ih]

omit [Fintype Ltr] in
/-- [proved-derived; formal-checked] **`basedOwn_ge`: a base with every mass at least `μ` keeps
`g(k) g(m)` of the even base's weight** at every node: `E^π_s ≥ E^½_s · g(k_s) · g(m_s)`. -/
theorem basedOwn_ge (j : ℕ) {base : Base Ltr} {μ : ℚ} (hμ : 0 < μ) (hb : ∀ obs b, μ ≤ base obs b) :
    ∀ (obs : List (List Ltr × Bool)) s,
      basedOwn j halfBase obs s * baseGain j μ (countsAt obs s true) *
        baseGain j μ (countsAt obs s false) ≤ basedOwn j base obs s := by
  intro obs s
  induction obs using List.reverseRecOn with
  | nil => simp [basedOwn, ownRev, countsAt_nil, baseGain]
  | append_singleton obs o ih =>
    obtain ⟨a, c⟩ := o
    have hpos : 0 ≤ basedOwn j halfBase obs s * baseGain j μ (countsAt obs s true) *
        baseGain j μ (countsAt obs s false) :=
      (mul_pos (mul_pos (basedOwn_pos j (fun _ _ => by norm_num [halfBase]) obs s)
        (baseGain_pos j hμ _)) (baseGain_pos j hμ _)).le
    rw [basedOwn_snoc, basedOwn_snoc, countsAt_snoc, countsAt_snoc]
    by_cases h : a.take s.length = s
    · rw [if_pos h, if_pos h]
      have hN : (0 : ℚ) < 2 ^ j * ((countsAt obs s true : ℚ) + countsAt obs s false) + 2 := by
        positivity
      cases c
      · simp only [h, true_and, Bool.false_eq_true, if_true, if_false, add_zero]
        rw [baseGain_succ]
        have := gain_step (E := basedOwn j halfBase obs s) (G1 := baseGain j μ (countsAt obs s false))
          (G2 := baseGain j μ (countsAt obs s true)) (Eπ := basedOwn j base obs s)
          (x := 2 ^ j * (countsAt obs s false : ℚ)) (π := base obs false) (μ := μ)
          (N := 2 ^ j * ((countsAt obs s true : ℚ) + countsAt obs s false) + 2)
          (f := 2 ^ j * (countsAt obs s false : ℚ) + 2 * (1 / 2))
          (by linarith [hpos]) (by linarith [ih]) (by positivity) hN hμ (hb obs false) (by ring)
        unfold faceAt basedFace
        simp only [halfBase]
        linarith [this]
      · simp only [h, true_and, Bool.true_eq_false, if_true, if_false, add_zero]
        rw [baseGain_succ]
        have := gain_step (E := basedOwn j halfBase obs s) (G1 := baseGain j μ (countsAt obs s true))
          (G2 := baseGain j μ (countsAt obs s false)) (Eπ := basedOwn j base obs s)
          (x := 2 ^ j * (countsAt obs s true : ℚ)) (π := base obs true) (μ := μ)
          (N := 2 ^ j * ((countsAt obs s true : ℚ) + countsAt obs s false) + 2)
          (f := 2 ^ j * (countsAt obs s true : ℚ) + 2 * (1 / 2))
          hpos ih (by positivity) hN hμ (hb obs true) (by ring)
        unfold faceAt basedFace
        simp only [halfBase]
        linarith [this]
    · simp only [h, false_and, if_false, Nat.add_zero]
      exact ih

/-- [definition] **The cost of a value's `K` arrivals** at base mass at least `¼`, over the even
base: `c(K) = −log₂ g(K)`. -/
noncomputable def baseCost (j K : ℕ) : ℝ := codeBits (baseGain j (1 / 4) K)

theorem baseCost_zero (j : ℕ) : baseCost j 0 = 0 := by
  simp [baseCost, baseGain, codeBits]

/-- `−log₂ q ≤ 3/2 (1/q − 1)` for `0 < q ≤ 1` (`ln 2 > 2/3`). -/
theorem neg_logb_le {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) : -Real.logb 2 q ≤ 3 / 2 * (1 / q - 1) := by
  have hl2 : 2 / 3 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hlog : Real.log (1 / q) ≤ 1 / q - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [one_div, Real.log_inv] at hlog
  have hge : 0 ≤ 1 / q - 1 := by rw [sub_nonneg, le_div_iff₀ hq]; linarith
  have hlogq : -Real.log q ≤ 1 / q - 1 := by rw [one_div]; linarith
  rw [Real.logb, ← neg_div, div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg hge (by linarith : (0 : ℝ) ≤ 3 / 2 * Real.log 2 - 1)]

/-- `Σ_(i<K) 1/(i+1) ≤ 1 + ln K` (`1/(i+1) ≤ ln((i+1)/i)` for `i ≥ 1`). -/
theorem sum_inv_succ_le (K : ℕ) : ∑ i ∈ range K, (1 : ℝ) / (i + 1) ≤ 1 + Real.log K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ]
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK
      simp
    · have hKr : (0 : ℝ) < K := by exact_mod_cast hK
      have hstep : (1 : ℝ) / (K + 1) ≤ Real.log (K + 1) - Real.log K := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < K / (K + 1) by positivity)
        rw [Real.log_div hKr.ne' (by positivity)] at h
        have e : (K : ℝ) / (K + 1) - 1 = -(1 / (K + 1)) := by field_simp; ring
        linarith
      push_cast
      linarith

/-- [proved-derived; formal-checked] **`baseCost_succ_le`: the cost of `K + 1` arrivals of one
value is at most `1 + 3/2^(j+2) (1 + ln K)` bits.** The first arrival, at the base's floor `¼`
against the even base's `½`, costs one bit; the `(r+1)`-th costs at most
`log₂ e · ½/(2^j r + ½) ≤ 3/(2^(j+2) r)`. -/
theorem baseCost_succ_le (j K : ℕ) :
    baseCost j (K + 1) ≤ 1 + 3 / 2 ^ (j + 2) * (1 + Real.log K) := by
  set f : ℕ → ℚ := fun i =>
    (2 ^ j * ((i + 1 : ℕ) : ℚ) + 2 * (1 / 4)) / (2 ^ j * ((i + 1 : ℕ) : ℚ) + 1) with hf
  have hg : baseGain j (1 / 4) (K + 1) = (∏ i ∈ range K, f i) * (1 / 2) := by
    rw [baseGain, prod_range_succ']
    norm_num [hf]
  have hfpos : ∀ i, 0 < f i := fun i => by simp only [hf]; positivity
  have hterm : ∀ i : ℕ, -Real.logb 2 (f i : ℝ) ≤ 3 / 2 ^ (j + 2) * (1 / ((i : ℝ) + 1)) := by
    intro i
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hpj : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hx : (1 : ℝ) ≤ 2 ^ j * ((i : ℝ) + 1) := by nlinarith
    have hfi : (f i : ℝ) = (2 ^ j * ((i : ℝ) + 1) + 1 / 2) / (2 ^ j * ((i : ℝ) + 1) + 1) := by
      simp only [hf]
      push_cast
      ring
    have h1 := neg_logb_le (q := (f i : ℝ)) (by rw [hfi]; positivity)
      (by rw [hfi, div_le_one (by positivity)]; linarith)
    refine h1.trans ?_
    rw [hfi]
    have e1 : 3 / 2 * (1 / ((2 ^ j * ((i : ℝ) + 1) + 1 / 2) / (2 ^ j * ((i : ℝ) + 1) + 1)) - 1) =
        3 / (4 * (2 ^ j * ((i : ℝ) + 1) + 1 / 2)) := by
      field_simp
      ring
    have e2 : 3 / 2 ^ (j + 2) * (1 / ((i : ℝ) + 1)) = 3 / (4 * (2 ^ j * ((i : ℝ) + 1))) := by
      rw [pow_add]
      field_simp
      ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  unfold baseCost codeBits
  rw [hg]
  push_cast
  rw [Real.logb_mul (Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (hfpos i).ne')
      (by norm_num), Real.logb_prod _ _ fun i _ => by exact_mod_cast (hfpos i).ne']
  have h0 : Real.logb 2 (1 / 2 : ℝ) = -1 := by
    rw [one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
  rw [h0]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ range K) => hterm i
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at hsum
  have hH := mul_le_mul_of_nonneg_left (sum_inv_succ_le K)
    (by positivity : (0 : ℝ) ≤ 3 / 2 ^ (j + 2))
  linarith

/-- [proved-derived; formal-checked] **`baseCost_campaign`: under 2 bits a value at campaign 1.**
At `j = 3` and at most `n* = 6148` arrivals, `c(K) ≤ 1 + 3/32 (1 + ln 6147) < 2` (`6147 < e^9`). -/
theorem baseCost_campaign {K : ℕ} (hK : K ≤ 6148) : baseCost 3 K < 2 := by
  rcases K with _ | K
  · rw [baseCost_zero]
    norm_num
  · have h := baseCost_succ_le 3 K
    have hlog : Real.log K < 9 := by
      rcases Nat.eq_zero_or_pos K with h0 | h0
      · subst h0
        simp
      · rw [Real.log_lt_iff_lt_exp (by exact_mod_cast h0)]
        have h9 : (2.7182818283 : ℝ) ^ 9 < Real.exp 1 ^ 9 :=
          pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
        rw [Real.exp_one_pow] at h9
        have hK' : (K : ℝ) ≤ 6147 := by exact_mod_cast (by omega : K ≤ 6147)
        norm_num at h9 ⊢
        linarith
    norm_num at h
    linarith

/-- At campaign 1 the root's base costs under 4 bits a leaf over the even base. -/
theorem leaf_cost_campaign {k m : ℕ} (h : k + m ≤ 6148) : baseCost 3 k + baseCost 3 m < 4 := by
  linarith [baseCost_campaign (by omega : k ≤ 6148), baseCost_campaign (by omega : m ≤ 6148)]

/-- [proved-derived; formal-checked] **`base_tree_redundancy`: the tree's redundancy at a base with
every mass at least `¼`.** For a binary landmark tree at rung `j ≥ 1` under **any** stop weights in
`[0, 1)`, whose addresses reach depth `D`, and **every** pruned tree `S` of depth at most `D` with
positive prior: the code the tree emits is at most `S`'s prior code plus, at each leaf, the best
fixed digit probability's code, `½ log₂ n_s + j`, and the base's cost `c(k_s) + c(m_s)` over the
even base. It is `PriorMass.priorMass_tree_redundancy`'s composition (`baseEmitted_eq_weight`,
`PriorMass.own_dominance₀`, `PriorMass.node_code_le`) with `basedOwn_ge` at `μ = ¼`. -/
theorem base_tree_redundancy {j : ℕ} (hj : 1 ≤ j) {base : Base Ltr}
    (hb : ∀ obs b, 1 / 4 ≤ base obs b) {w : ℕ → ℚ} (hw : StopLaw₀ w) (D : ℕ)
    (obs : List (List Ltr × Bool)) (hD : ∀ o ∈ obs, D ≤ o.1.length) (S : PrunedTree Ltr D)
    (hS : 0 < PrunedTree.prior w D 0 S) :
    codeBits (baseEmitted j base w D obs) ≤
      codeBits (PrunedTree.prior w D 0 S) +
        leafSum (fun s => codeBits (bestFixed (routedCount obs s true) (routedCount obs s false)) +
          leafCharge j (routedCount obs s true) (routedCount obs s false) +
          baseCost j (routedCount obs s true) + baseCost j (routedCount obs s false)) D [] S := by
  have hbpos : ∀ obs b, 0 < base obs b := fun obs b => lt_of_lt_of_le (by norm_num) (hb obs b)
  set E := basedOwn j base obs with hEdef
  have hE : ∀ s, 0 < E s := basedOwn_pos j hbpos obs
  rw [baseEmitted_eq_weight j hbpos hw D obs hD]
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
      leafCharge j (routedCount obs s true) (routedCount obs s false) +
      baseCost j (routedCount obs s true) + baseCost j (routedCount obs s false))
    (fun s => by
      have hU := urnBool_pos (massWeight_pos j) (routedCount obs s true) (routedCount obs s false)
      have hgk := baseGain_pos j (μ := 1 / 4) (by norm_num) (routedCount obs s true)
      have hgm := baseGain_pos j (μ := 1 / 4) (by norm_num) (routedCount obs s false)
      have hge := basedOwn_ge j (μ := 1 / 4) (by norm_num) hb obs s
      rw [basedOwn_half] at hge
      simp only [countsAt] at hge
      have hgeR : ((urnBool (massWeight j) (routedCount obs s true) (routedCount obs s false) : ℚ) :
          ℝ) * (baseGain j (1 / 4) (routedCount obs s true) : ℝ) *
          (baseGain j (1 / 4) (routedCount obs s false) : ℝ) ≤ (E s : ℝ) := by
        exact_mod_cast hge
      have hUR : (0 : ℝ) < (urnBool (massWeight j) (routedCount obs s true)
        (routedCount obs s false) : ℝ) := by exact_mod_cast hU
      have hgkR : (0 : ℝ) < (baseGain j (1 / 4) (routedCount obs s true) : ℝ) := by
        exact_mod_cast hgk
      have hgmR : (0 : ℝ) < (baseGain j (1 / 4) (routedCount obs s false) : ℝ) := by
        exact_mod_cast hgm
      have hl := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hgeR
      rw [Real.logb_mul (by positivity) hgmR.ne', Real.logb_mul hUR.ne' hgkR.ne'] at hl
      have hn := node_code_le hj (routedCount obs s true) (routedCount obs s false)
      unfold baseCost codeBits at *
      linarith) D [] S
  rw [leafSum_neg] at hleaf
  unfold codeBits at hleaf ⊢
  linarith

/-- [proved-derived; formal-checked] **`rootBase_tree_redundancy`: the root's base, as the Rust
reads it.** `base_tree_redundancy` at `rootBaseOf`, every base mass at least `¼` by
`rootBase_quarter`. -/
theorem rootBase_tree_redundancy {j : ℕ} (hj : 1 ≤ j) {w : ℕ → ℚ} (hw : StopLaw₀ w) (D : ℕ)
    (obs : List (List Ltr × Bool)) (hD : ∀ o ∈ obs, D ≤ o.1.length) (S : PrunedTree Ltr D)
    (hS : 0 < PrunedTree.prior w D 0 S) :
    codeBits (baseEmitted j (rootBaseOf j) w D obs) ≤
      codeBits (PrunedTree.prior w D 0 S) +
        leafSum (fun s => codeBits (bestFixed (routedCount obs s true) (routedCount obs s false)) +
          leafCharge j (routedCount obs s true) (routedCount obs s false) +
          baseCost j (routedCount obs s true) + baseCost j (routedCount obs s false)) D [] S :=
  base_tree_redundancy hj (rootBaseOf_quarter j) hw D obs hD S hS

end Redundancy

/-! ### Audit -/

section Audit

#print axioms rootSixteenths_round
#print axioms rootSixteenths_mem
#print axioms rootSixteenths_empty
#print axioms rootBase_quarter
#print axioms rootBase_sum
#print axioms rootBase_empty
#print axioms basedFace_sum
#print axioms basedFace_half
#print axioms rootBase_face_sixteenths
#print axioms prior_read
#print axioms basedFace_ge
#print axioms rootBase_face_ge
#print axioms rootBase_path_face_ge
#print axioms campaign_face_bits
#print axioms campaign_carrier_bits
#print axioms campaign_mass_operand
#print axioms campaign_operands
#print axioms campaign_rule_floor
#print axioms baseEmitted_face_normalized
#print axioms baseEmitted_eq_weight
#print axioms baseEmitted_sum
#print axioms rootBaseOf_quarter
#print axioms basedOwn_half
#print axioms basedOwn_ge
#print axioms baseCost_succ_le
#print axioms baseCost_campaign
#print axioms leaf_cost_campaign
#print axioms base_tree_redundancy
#print axioms rootBase_tree_redundancy

end Audit

end Holonics.Compression.Landmark.Context.BaseMeasure
