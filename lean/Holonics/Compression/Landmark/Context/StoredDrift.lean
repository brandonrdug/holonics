import Holonics.Compression.Landmark.Context.Drift

/-!
# Compression.Landmark.Context.StoredDrift: the compacted executed tree as an instance of the full tree

[definition; agent-inferred] The compacted storage's drift (#62, "the compacted storage as an
instance of the full tree"; rebuild step 4, #73). The executed receiving tree is stored where paths
part (`Context/Compaction`, Decision 37): a unary chain is one stored node at its summed rung, read
once at its top, and a chain parts into an upper and a lower part when an arrival leaves it, each
part's ratio formed exactly and carried at `W` bits. At the declared depth `D = 63` of campaign 1
the Rust can run only this compacted tree, so every bound of `Context/Drift` (proved for the full
executed tree, a carried ratio at every node) reaches the executed code only through this owner.
The computational object is the helical pair interaction; this owner is the receiving parametron's
landmark tree, executed and stored where it is plural. Of the winding guide's six general objects it
touches the **tower thread** (context depth as restriction: a stored chain's implicit nodes are a
unique gluing that reads exactly, the discrepancy adds down the restriction chain) and **faces and
placement** (the executed face against the ideal face at each stored level); the helix, the pair,
the cell holonomy and the tube stay attached, unchanged.

The object is the full tree carrying, at every node `s`, the ideal weight `W_s` and the executed
weight `Ŵ_s` that the stored state determines, with one stored discrepancy `K_s`:

```text
ideal      W_s = E_s + κ_s ∏_b W_(s b)                (|s| < D),    W_s the leaf's KT mass at D
executed   Ŵ_s = E_s + e^(K_s) κ_s ∏_b Ŵ_(s b)       (|s| < D),    Ŵ_s = W_s at D
instance   K_s = 0 at every implicit node: a stored chain's discrepancy sits at its bottom node
           (the node whose children are stored), every leaf chain reads exactly
total      tot(0, s) = 0 ,  tot(n + 1, s) = |K_s| + Σ_b tot(n, s b)          (the subtree's |K|)
weight     |ln Ŵ_s − ln W_s| ≤ tot(D − |s|, s) ,  |ln Q̂_s − ln P_s| ≤ tot(D − |s|, s)   (Q̂, P the split masses)
passage    |Σ_(t<N) (ln q̂_t − ln q_t)| ≤ Σ_(t<N) tot(ΔK_t)(D, root) + Σ_(t<N) |J_t| ,
           J_t = ln Ŵ_root(t + 1) − ln Ŵ_root(t) − ln q̂_t ,  K(0) = 0
step       a stored bottom's carried split mass steps Q̂′ = Q̂ x̂ c:  ΔK = ln c − J_child
read       |J| ≤ θ + |ln c|  (c every factor of the read's step, a split's upper rounding r_u among them)
split      ΔK_(s_j) = ln r_u − J_off (the upper part's bottom),  ΔK_ℓ = ln ρ_ℓ (the lower part's bottom),
           |J_off| ≤ |ln ρ_ℓ| ,  the split moves every weight above s_j by at most |ln r_u|
cell       |ln q̂_0 − ln q_0| ≤ Σ_(levels ≤ L) θ_i + Σ_(levels < L) |ln Q̂_i − ln P_i|      (stored levels)
```

[proved-derived; formal-checked] What is proved.

1. **The subtree's discrepancy** (`tot`, `tot_nonneg`, `tot_of_zero`, `tot_add_le`, `tot_le_history`,
   `tot_path_le`): `tot(n, s)` sums `|K|` over the `n` levels from `s`; from `K(0) = 0` the
   discrepancy at time `N` is within the changes summed over the passage; a change supported on one
   address's prefixes totals its path sum.
2. **The weight and the split mass** (`ConsistentTree`, `ConsistentTree.split_log`,
   `ConsistentTree.drift_le_tot`, `ConsistentTree.split_mass_drift`): the executed weight and split
   mass are within the subtree's discrepancy of the ideal, because a weight is 1-Lipschitz in the
   log of its split mass (`Drift.log_add_le`). The stored discrepancies need not be small one by one;
   only their sum over a subtree enters.
3. **The passage** (`stored_passage`): both codes telescope to the root weights, so the executed
   code is within the discrepancies' changes and the root's read jumps, each summed once over the
   passage.
4. **The events** (`carried_step`, `read_jump`, `off_jump`, `up_path`, `split_effect`,
   `split_charge`): a stored bottom's step changes its discrepancy by its factors less its child's
   read jump; a read jumps by its rounding and its factors; a part's rounding moves its weight by at
   most the rounding; a change below a node moves the weights above it, along the path, by at most
   its own move; a split's upper part, formed exactly against the lower part's weight before that
   part's rounding, moves every weight above it by its own rounding `r_u` alone (the lower
   rounding's move `J_off` cancels at the parting node), so a split charges
   `|ln r_u| + 2|ln ρ_ℓ|` to the discrepancies below and above it and `2(|ln r_u| + |ln ρ_ℓ|)` to
   the passage.
5. **One cell** (`level_read_drift`): over the stored levels of a read, the face departs by the
   levels' roundings and their split masses' drifts (`Drift.node_face_drift` down the levels), each
   at most its bottom's `tot` (item 2).
6. **The per-cell count of mantissa units** (`arrivalUnits`, `rebases_below`, `arrival_units_le`,
   `levels_units`, `cell_units`, `rule_units`): one arrival charges a stored level with bottom
   `b < D` at most `2(D − b) − 1 + 4` units (its own rebase, twice each rebase below, which have
   distinct bottoms in `(b, D)`, and at most `4` from its one split); a read's levels have
   distinct bottoms below `D`, so with at most `n*` arrivals a level a cell carries at most
   `n* D² + 4n* D` units a digit, within the rule's `n* P² + max((n* + 1) P², 4n* P)` for `D ≤ P`,
   which is `(2n* + 1) P²` for `P ≥ 4`; at `P = 1` the count `(n* + 1) P²` alone is short
   (`rule_units_shallow`).

[agent-inferred] **The instance** (Rust `compression::landmark::context`, the host `Arena` and its
`Law`; the card's `holonics_cuda::hnn::tree::CardTree`, `hnn_tree_deposit`, which mirrors the host
split and carries no certificates). The placement of `K`, the read of the arena as a
`ConsistentTree`, exact leaf chains and the split's closed forms are proved in
`Context/StoredInstance` (`instTree`, `instance_read`, `instK_implicit`, `split_closed_form`); the
Rust's read of its arena as `execFrom` stays agent-inferred there.
- **A stored chain** `s_0 … s_(k−1)` over a stored bottom `s_k` is one node at its summed rung
  `S = Σ j_i` (`κ_i = 1 − w_i = 2^(−j_i)`), weight `ladder S · E + 2^(−S) X̂` with `X̂ = (2^S − 1) E/β̂`
  (`Compaction.chain_ratio`, an identity in the bottom split mass). Placing the chain's discrepancy
  `K = ln X̂ − ln ∏_b Ŵ_(s_k b)` at `s_(k−1)` and `K = 0` at `s_0 … s_(k−2)` makes every implicit
  node's executed weight the exact composition, so the chain's read at `s_0` is one level: its
  `θ` the one rounding at its top, its split-mass drift `|ln X̂ − ln X| ≤ tot(s_(k−1))`. A leaf
  chain reads its KT face `⟦k⟧` (`Law::leaf`) and has `K = 0` throughout.
- **A step** (`Law::apply_branch`) moves `β̂` by the KT face, the child's lattice face and a
  mantissa or carrier rebase `c` (`Tree.rebase_log_residual`, `Carrier`): `carried_step`.
- **A split** (`Law::part`, `Beta::split`, `Compaction.chain_split`) at the parting node `s_j`:
  the lower part keeps `X̂` exactly (`β_ℓ = β (2^(S_low) − 1)/(2^S − 1)`) and rounds it once at `W`
  bits (`ρ_ℓ`); the upper part is the exact closed form of the lower part's weight before that
  rounding, rounded once (`r_u`). So `ΔK_(s_j) = ln r_u − J_off`, `ΔK_ℓ = ln ρ_ℓ` at the lower
  part's bottom, off the arrival's path. Above a leaf the upper part is founded at `2^(S_up) − 1`
  (`Law::chain`), the leaf keeps its exact face: `ΔK_(s_j) = ln r_u`, no lower term. An upper part
  with no rung passes its face through (`Compaction.chain_split_pass`): no discrepancy.
- **The carried certificates.** A stored level's `drift` must dominate `tot` at its bottom over the
  history (item 1), and the root's `excess` the passage (item 3). With `u`, `ℓ` the upper and lower
  roundings' units: a step adds `rebase` and the child's increment to the drift and `θ + 2 rebase`
  plus the child's increment to the increment, as `Law::apply_branch` does; a split adds `ℓ` to
  the lower part's drift, `u + 2ℓ` to the upper part's drift (its own `ΔK` and the lower part's),
  and `2(u + ℓ)` to the increment it carries up (`split_charge`). Before this owner the Rust added
  `u` to the upper part's drift and `u + ℓ` to the increment; it now adds the proved charges, which
  only enlarge the certificates and change no face.
- **The per-cell rule** (`Landmarks::face_rule`), counted by item 6. The instance of
  `arrivalUnits`: `r_m` is `Law::apply_branch`'s mantissa rebase at level `m` (`⌈2^C/m'⌉` with
  `m' ≥ 2^(W−1)`, one unit of `2^(1−W)`, taken only at `level < top`, so never at a leaf's bottom
  `D`); `s_p = u + ℓ` is `Parting::units` at the parting level `p`, carried up twice in the
  increment; `o_p = u + 2ℓ` is `Law::part`'s addition to the upper part's drift (one unit each,
  `u = ℓ = 0` where a part keeps its chart, `s_p = o_p ≤ 1` at a leaf's founding). The lower part,
  off the arrival's path, takes `ℓ ≤ 1` (`Law::part`'s `lower_units`): that unit is the splitting
  arrival's, which never passes through the lower part, so a level's drift holds the units of its
  own arrivals and one unit for each arrival that split its chain above it, distinct arrivals of
  the passage (`cell_units`, with a charge of `1 ≤ 2(D − b) − 1 + 4` for the latter). Each part
  inherits the chain's drift: the lower part keeps the chain's bottom, and the upper part's earlier
  charges were bounded at the chain's deeper bottom by a smaller value. An arrival charges a level
  once, so `n*` bounds the arrivals a level counts. Per cell at most `n* D² + 4 n* D` units against
  the rule's `n* P² + max((n* + 1) P², 4 n* P)` (`mantissa_units`, `P ≥ D` the path depth), which
  is `(2n* + 1) P²` for `P ≥ 4` (the count `(n* + 1) P²` alone is short of `4 n* P` at `P ≤ 3`,
  where the maximum can widen `W`: at `n* = 6,148`, `D = 1`, `W = 26` against `25`). A carrier
  release (`ρ_c`) is taken at the same steps as a mantissa rebase, with no split, so its count is
  item 6's without the `4`: the rule's `n* P²`. At campaign 1's `D = 63`
  (`P = 63`, `n* = 6,148 = 2²·29·53`) the widths stay the rule's, `M_p = 49` at the even base
  (`50` at the root's, `BaseMeasure.campaign_face_bits`), `W = 37`, and the
  per-cell read stays within a quarter grain per source; the per-cell `D²` term gives a usable
  resolution there.

[proved-standard] The weight telescoping is Willems, Shtarkov and Tjalkens (1995); the compacted
tree is Willems's unbounded-depth storage (1998). The proofs here are this owner's.

| Claim | Lean | Rust |
|---|---|---|
| the subtree's discrepancy, its history and its path sum | `tot`, `tot_le_history`, `tot_path_le` | `Chart::drift` (each stored level's) |
| the weight and the split mass within the subtree's discrepancy | `ConsistentTree.drift_le_tot`, `ConsistentTree.split_mass_drift` | `Landmarks` (its arena), `Law::reading` |
| the passage | `stored_passage` | `Chart::excess` (the root's), `Landmarks::deposit` |
| a step, a read, a split | `carried_step`, `read_jump`, `off_jump`, `up_path`, `split_effect`, `split_charge` | `Law::apply_branch`, `Law::part`, `Beta::split`, `hnn_tree_deposit` |
| one cell over the stored levels | `level_read_drift` | `CellReading::residual`, `Landmarks::face_rule` |
| the per-cell count of mantissa units | `arrivalUnits`, `rebases_below`, `arrival_units_le`, `levels_units`, `cell_units`, `rule_units` | `Law::apply_branch`, `Law::part`, `mantissa_units`, `Landmarks::face_rule` |

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.Landmark.Context.StoredDrift

open Finset Holonics.Compression.Landmark.Context.Drift

/-! ### The subtree's discrepancy -/

section Total

variable {Ltr : Type*} [Fintype Ltr]

/-- [definition] **`tot f n s`: the discrepancy summed over a subtree.** `|f|` summed over the
nodes `s ++ v` with `|v| < n`: `tot f 0 s = 0`, `tot f (n + 1) s = |f s| + Σ_b tot f n (s ++ [b])`. -/
noncomputable def tot (f : List Ltr → ℝ) : ℕ → List Ltr → ℝ
  | 0, _ => 0
  | n + 1, s => |f s| + ∑ b, tot f n (s ++ [b])

theorem tot_zero (f : List Ltr → ℝ) (s : List Ltr) : tot f 0 s = 0 := rfl

theorem tot_succ (f : List Ltr → ℝ) (n : ℕ) (s : List Ltr) :
    tot f (n + 1) s = |f s| + ∑ b, tot f n (s ++ [b]) := rfl

/-- [proved-derived] `tot` is nonnegative. -/
theorem tot_nonneg (f : List Ltr → ℝ) : ∀ n s, 0 ≤ tot f n s
  | 0, _ => le_rfl
  | n + 1, _ => add_nonneg (abs_nonneg _) (sum_nonneg fun _ _ => tot_nonneg f n _)

/-- [proved-derived] A discrepancy that vanishes everywhere totals zero. -/
theorem tot_of_zero (f : List Ltr → ℝ) (hf : ∀ s, f s = 0) : ∀ n s, tot f n s = 0
  | 0, _ => rfl
  | n + 1, s => by
    rw [tot_succ, hf s, abs_zero, zero_add]
    exact sum_eq_zero fun b _ => tot_of_zero f hf n _

/-- [proved-derived] **`tot_add_le`.** `tot` is subadditive: a change on a path and a change off
it total at most their totals. -/
theorem tot_add_le (f g : List Ltr → ℝ) :
    ∀ n s, tot (fun s => f s + g s) n s ≤ tot f n s + tot g n s
  | 0, _ => by simp [tot_zero]
  | n + 1, s => by
    rw [tot_succ, tot_succ, tot_succ]
    have h1 := abs_add_le (f s) (g s)
    have h2 : ∑ b, tot (fun s => f s + g s) n (s ++ [b]) ≤
        ∑ b, (tot f n (s ++ [b]) + tot g n (s ++ [b])) :=
      sum_le_sum fun b _ => tot_add_le f g n _
    rw [sum_add_distrib] at h2
    linarith

/-- [proved-derived] **`tot_le_history`: the discrepancy is within its changes summed over the
passage.** From `K 0 = 0`, `tot (K N) n s ≤ Σ_(t<N) tot (K (t + 1) − K t) n s`: each node's
discrepancy telescopes, and the subtree's sum commutes with the passage's. -/
theorem tot_le_history (K : ℕ → List Ltr → ℝ) (h0 : ∀ s, K 0 s = 0) (N : ℕ) :
    ∀ n s, tot (K N) n s ≤ ∑ t ∈ range N, tot (fun s => K (t + 1) s - K t s) n s
  | 0, s => by simp [tot_zero]
  | n + 1, s => by
    simp only [tot_succ]
    rw [sum_add_distrib]
    have hK : K N s = ∑ t ∈ range N, (K (t + 1) s - K t s) := by
      rw [sum_range_sub (fun t => K t s), h0, sub_zero]
    have h1 : |K N s| ≤ ∑ t ∈ range N, |K (t + 1) s - K t s| := by
      rw [hK]; exact abs_sum_le_sum_abs _ _
    have h2 : ∑ b, tot (K N) n (s ++ [b]) ≤
        ∑ b, ∑ t ∈ range N, tot (fun s => K (t + 1) s - K t s) n (s ++ [b]) :=
      sum_le_sum fun b _ => tot_le_history K h0 N n _
    rw [Finset.sum_comm] at h2
    linarith

variable [DecidableEq Ltr]

/-- [proved-derived] **`tot_path_le`: a change on one address's prefixes totals its path sum.**
If `f` vanishes off the prefixes of `a`, then at a prefix `s` of `a`,
`tot f n s ≤ Σ_(|s| ≤ d < |s| + n) |f (a.take d)|`, and off them `tot f n s ≤ 0`. -/
theorem tot_path_le (f : List Ltr → ℝ) (a : List Ltr) (hf : ∀ s, ¬ s <+: a → f s = 0) :
    ∀ n s, tot f n s ≤
      if s <+: a then ∑ d ∈ Ico s.length (s.length + n), |f (a.take d)| else 0
  | 0, s => by split_ifs <;> simp [tot_zero]
  | n + 1, s => by
    by_cases hs : s <+: a
    · rw [if_pos hs, tot_succ]
      set V := ∑ d ∈ Ico (s.length + 1) (s.length + (n + 1)), |f (a.take d)| with hV
      have hV0 : 0 ≤ V := sum_nonneg fun _ _ => abs_nonneg _
      have hkid : ∀ b, tot f n (s ++ [b]) ≤ if s ++ [b] <+: a then V else 0 := by
        intro b
        have := tot_path_le f a hf n (s ++ [b])
        simp only [List.length_append, List.length_singleton] at this
        have e : s.length + 1 + n = s.length + (n + 1) := by omega
        rw [e] at this
        exact this
      have hcard : ((univ : Finset Ltr).filter fun b => s ++ [b] <+: a).card ≤ 1 := by
        refine card_le_one.2 fun b hb b' hb' => ?_
        have hb := (mem_filter.1 hb).2
        have hb' := (mem_filter.1 hb').2
        have : s ++ [b] = s ++ [b'] :=
          (List.prefix_of_prefix_length_le hb hb' (by simp)).eq_of_length (by simp)
        simpa using this
      have hsum : ∑ b, tot f n (s ++ [b]) ≤ V := by
        calc ∑ b, tot f n (s ++ [b]) ≤ ∑ b, (if s ++ [b] <+: a then V else 0) :=
              sum_le_sum fun b _ => hkid b
          _ = ((univ : Finset Ltr).filter fun b => s ++ [b] <+: a).card * V := by
              rw [← sum_filter, sum_const, nsmul_eq_mul]
          _ ≤ 1 * V := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hV0
          _ = V := one_mul V
      have hs' : a.take s.length = s := (List.prefix_iff_eq_take.1 hs).symm
      rw [sum_eq_sum_Ico_succ_bot (by omega : s.length < s.length + (n + 1)), hs']
      linarith
    · rw [if_neg hs, tot_succ, hf s hs, abs_zero, zero_add]
      refine sum_nonpos fun b _ => ?_
      have := tot_path_le f a hf n (s ++ [b])
      rwa [if_neg fun h => hs ((List.prefix_append s [b]).trans h)] at this

end Total

/-! ### The weight and the split mass -/

/-- [definition] **The full tree with its executed weights.** At each node `s`:
* `E ≥ 0` the own weight (the stop weight times the KT mass), `κ > 0` the split share (`1 − w`);
* `W` the ideal weight, `E + κ ∏_b W(s b)` above the depth `D`;
* `Ŵ` the executed weight the stored state determines, `E + e^K κ ∏_b Ŵ(s b)` above `D`, with `K`
  the stored discrepancy (`0` at every implicit node of a stored chain), and the leaf's own mass at
  `D` (a leaf reads its counts exactly). -/
structure ConsistentTree (Ltr : Type*) [Fintype Ltr] (D : ℕ) where
  E : List Ltr → ℝ
  κ : List Ltr → ℝ
  K : List Ltr → ℝ
  W : List Ltr → ℝ
  Wh : List Ltr → ℝ
  E_nonneg : ∀ s, 0 ≤ E s
  κ_pos : ∀ s, 0 < κ s
  W_pos : ∀ s, 0 < W s
  Wh_pos : ∀ s, 0 < Wh s
  W_node : ∀ s : List Ltr, s.length < D → W s = E s + κ s * ∏ b, W (s ++ [b])
  Wh_node : ∀ s : List Ltr, s.length < D →
    Wh s = E s + Real.exp (K s) * (κ s * ∏ b, Wh (s ++ [b]))
  leaf : ∀ s : List Ltr, s.length = D → Wh s = W s

namespace ConsistentTree

variable {Ltr : Type*} [Fintype Ltr] {D : ℕ} (T : ConsistentTree Ltr D)

/-- [definition] The ideal split mass `P_s = κ ∏_b W(s b)`. -/
noncomputable def P (s : List Ltr) : ℝ := T.κ s * ∏ b, T.W (s ++ [b])

/-- [definition] The executed split mass `Q̂_s = e^K κ ∏_b Ŵ(s b)`: the stored chart's `β̂ = E/Q̂`. -/
noncomputable def Qh (s : List Ltr) : ℝ := Real.exp (T.K s) * (T.κ s * ∏ b, T.Wh (s ++ [b]))

theorem P_pos (s : List Ltr) : 0 < T.P s :=
  mul_pos (T.κ_pos s) (prod_pos fun _ _ => T.W_pos _)

theorem Qh_pos (s : List Ltr) : 0 < T.Qh s :=
  mul_pos (Real.exp_pos _) (mul_pos (T.κ_pos s) (prod_pos fun _ _ => T.Wh_pos _))

/-- [proved-derived] **`split_log`.** `ln Q̂_s − ln P_s = K_s + Σ_b (ln Ŵ(s b) − ln W(s b))`: the
split mass's drift is the node's discrepancy and its children's. -/
theorem split_log (s : List Ltr) :
    Real.log (T.Qh s) - Real.log (T.P s) =
      T.K s + ∑ b, (Real.log (T.Wh (s ++ [b])) - Real.log (T.W (s ++ [b]))) := by
  have hWh : ∀ b ∈ (univ : Finset Ltr), T.Wh (s ++ [b]) ≠ 0 := fun b _ => (T.Wh_pos _).ne'
  have hW : ∀ b ∈ (univ : Finset Ltr), T.W (s ++ [b]) ≠ 0 := fun b _ => (T.W_pos _).ne'
  rw [Qh, P, Real.log_mul (Real.exp_pos _).ne' (mul_pos (T.κ_pos s)
      (prod_pos fun _ _ => T.Wh_pos _)).ne', Real.log_exp,
    Real.log_mul (T.κ_pos s).ne' (prod_pos fun _ _ => T.Wh_pos _).ne',
    Real.log_mul (T.κ_pos s).ne' (prod_pos fun _ _ => T.W_pos _).ne',
    Real.log_prod hWh, Real.log_prod hW, sum_sub_distrib]
  ring

/-- [proved-derived] **`drift_le_tot`: the executed weight is within the subtree's discrepancy.**
`|ln Ŵ_s − ln W_s| ≤ tot K (D − |s|) s`: a weight is 1-Lipschitz in the log of its split mass
(`Drift.log_add_le`), and the split mass's drift is the node's discrepancy and its children's
(`split_log`). -/
theorem drift_le_tot : ∀ k (s : List Ltr), s.length + k = D →
    |Real.log (T.Wh s) - Real.log (T.W s)| ≤ tot T.K k s
  | 0, s, hs => by
    rw [T.leaf s (by omega), sub_self, abs_zero, tot_zero]
  | k + 1, s, hs => by
    have hsD : s.length < D := by omega
    have hw : T.Wh s = T.E s + T.Qh s := T.Wh_node s hsD
    have hW : T.W s = T.E s + T.P s := T.W_node s hsD
    rw [hw, hW, tot_succ]
    refine (log_add_le (T.E_nonneg s) (T.Qh_pos s) (T.P_pos s)).trans ?_
    rw [T.split_log s]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b _ => ?_)
    exact drift_le_tot k (s ++ [b]) (by simp; omega)

/-- [proved-derived] **`split_mass_drift`: the stored chart's drift is within its subtree's
discrepancy.** Above `D`, `|ln Q̂_s − ln P_s| ≤ tot K (D − |s|) s`: the chart's `Δ = |ln β̂ − ln β|`
at the bottom of a stored chain is at most the discrepancies below it, its own included. -/
theorem split_mass_drift (s : List Ltr) (hs : s.length < D) :
    |Real.log (T.Qh s) - Real.log (T.P s)| ≤ tot T.K (D - s.length) s := by
  obtain ⟨k, hk⟩ : ∃ k, D - s.length = k + 1 := ⟨D - s.length - 1, by omega⟩
  rw [hk, tot_succ, T.split_log s]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b _ => ?_)
  exact T.drift_le_tot k (s ++ [b]) (by simp; omega)

end ConsistentTree

/-! ### The passage -/

section Passage

variable {Ltr : Type*} [Fintype Ltr] {D : ℕ}

/-- [proved-derived] **`stored_passage`: the executed code against the ideal code over the passage.**
Let `T t` be the tree before observation `t` (the stored state, its discrepancies from `0` at the
founding), `q_t = W_root(t + 1)/W_root(t)` the ideal face (`Tree.lattice_node_telescope`), `q̂_t` the
executed read, and `J_t = ln Ŵ_root(t + 1) − ln Ŵ_root(t) − ln q̂_t` the read's jump (its rounding,
its factors, a split's move). Then
`|Σ_(t<N) (ln q̂_t − ln q_t)| ≤ Σ_(t<N) tot(K(t + 1) − K t)(D, root) + Σ_(t<N) |J_t|`:
both codes telescope to the root weights, whose logs differ by at most the root's `tot`
(`ConsistentTree.drift_le_tot`), which is within its changes (`tot_le_history`). -/
theorem stored_passage (T : ℕ → ConsistentTree Ltr D) (q qh : ℕ → ℝ)
    (hq : ∀ t, q t = (T (t + 1)).W [] / (T t).W []) (h0 : ∀ s, (T 0).K s = 0) (N : ℕ) :
    |∑ t ∈ range N, (Real.log (qh t) - Real.log (q t))| ≤
      ∑ t ∈ range N, tot (fun s => (T (t + 1)).K s - (T t).K s) D [] +
        ∑ t ∈ range N,
          |Real.log ((T (t + 1)).Wh []) - Real.log ((T t).Wh []) - Real.log (qh t)| := by
  set δ : ℕ → ℝ := fun t => Real.log ((T t).Wh []) - Real.log ((T t).W []) with hδ
  set J : ℕ → ℝ := fun t =>
    Real.log ((T (t + 1)).Wh []) - Real.log ((T t).Wh []) - Real.log (qh t) with hJ
  have hterm : ∀ t, Real.log (qh t) - Real.log (q t) = (δ (t + 1) - δ t) - J t := by
    intro t
    rw [hq t, Real.log_div ((T (t + 1)).W_pos []).ne' ((T t).W_pos []).ne']
    simp only [hδ, hJ]
    ring
  have hsum : ∑ t ∈ range N, (Real.log (qh t) - Real.log (q t)) =
      (δ N - δ 0) - ∑ t ∈ range N, J t := by
    rw [sum_congr rfl fun t _ => hterm t, sum_sub_distrib, sum_range_sub δ N]
  have hN : |δ N| ≤ ∑ t ∈ range N, tot (fun s => (T (t + 1)).K s - (T t).K s) D [] :=
    ((T N).drift_le_tot D [] (by simp)).trans
      (tot_le_history (fun t => (T t).K) h0 N D [])
  have hz : |δ 0| ≤ 0 := by
    have := (T 0).drift_le_tot D [] (by simp)
    rwa [tot_of_zero _ h0] at this
  rw [hsum]
  have hJs := abs_sum_le_sum_abs J (range N)
  have htri : |(δ N - δ 0) - ∑ t ∈ range N, J t| ≤ |δ N| + |δ 0| + |∑ t ∈ range N, J t| := by
    refine (abs_sub _ _).trans ?_
    linarith [abs_sub (δ N) (δ 0)]
  linarith

end Passage

/-! ### The events -/

/-- [proved-derived] **`carried_step`: a stored bottom's step moves its discrepancy by its factors
less its child's read jump.** With the consistent split mass `M = κ ∏ Ŵ` and the executed one
`Q̂ = e^K M`, a step carries `Q̂′ = Q̂ x̂ c` (`x̂` the child's read, `c > 0` its rebase or the
carrier's release) while the consistent mass moves by the child's weight, `M′ = M w′/w`. Then
`K′ = K + ln c − J` with the child's read jump `J = ln w′ − ln w − ln x̂`. -/
theorem carried_step {Q Q' M M' K K' xh c w w' : ℝ} (hM : 0 < M) (hw : 0 < w) (hw' : 0 < w')
    (hxh : 0 < xh) (hc : 0 < c) (hQ : Q = Real.exp K * M) (hQ' : Q' = Real.exp K' * M')
    (hstep : Q' = Q * xh * c) (hM' : M' = M * (w' / w)) :
    K' = K + Real.log c - (Real.log w' - Real.log w - Real.log xh) := by
  have hM'pos : 0 < M' := hM' ▸ mul_pos hM (div_pos hw' hw)
  have hl : Real.log Q' = K' + Real.log M' := by
    rw [hQ', Real.log_mul (Real.exp_pos _).ne' hM'pos.ne', Real.log_exp]
  have hr : Real.log Q' = K + Real.log M + Real.log xh + Real.log c := by
    rw [hstep, hQ, Real.log_mul (mul_pos (mul_pos (Real.exp_pos _) hM) hxh).ne' hc.ne',
      Real.log_mul (mul_pos (Real.exp_pos _) hM).ne' hxh.ne',
      Real.log_mul (Real.exp_pos _).ne' hM.ne', Real.log_exp]
  have hm : Real.log M' = Real.log M + Real.log w' - Real.log w := by
    rw [hM', Real.log_mul hM.ne' (div_pos hw' hw).ne', Real.log_div hw'.ne' hw.ne']
    ring
  linarith

/-- [proved-derived] **`read_jump`: a read jumps by its rounding and its factors.** The executed
read `q̂` is within `θ` in `ln` of `(E′ + Q̂ x̂)/(E + Q̂)`, while the stored state carries `Q̂ x̂ c`, so
the executed weight moves `Ŵ′/Ŵ = (E′ + Q̂ x̂ c)/(E + Q̂)` and
`|ln Ŵ′ − ln Ŵ − ln q̂| ≤ θ + |ln c|` (`c` the product of the step's factors: its rebase, the
carrier's release, a split's upper rounding). A stored chain is one level: `E` and `Q̂` its
`ladder S · E` and `2^(−S) X̂` (`Compaction.chain_ratio`). -/
theorem read_jump {E E' Q xh c θ qh : ℝ} (hE : 0 ≤ E) (hE' : 0 ≤ E') (hQ : 0 < Q) (hxh : 0 < xh)
    (hc : 0 < c)
    (hθ : |Real.log qh - Real.log ((E' + Q * xh) / (E + Q))| ≤ θ) :
    |Real.log (E' + Q * xh * c) - Real.log (E + Q) - Real.log qh| ≤ θ + |Real.log c| := by
  have hQx := mul_pos hQ hxh
  have h1 : |Real.log (E' + Q * xh * c) - Real.log (E' + Q * xh)| ≤ |Real.log c| := by
    have := log_add_le hE' (mul_pos hQx hc) hQx
    rwa [Real.log_mul hQx.ne' hc.ne', add_sub_cancel_left] at this
  have e : Real.log (E' + Q * xh * c) - Real.log (E + Q) - Real.log qh =
      (Real.log (E' + Q * xh * c) - Real.log (E' + Q * xh)) -
        (Real.log qh - Real.log ((E' + Q * xh) / (E + Q))) := by
    rw [Real.log_div (by positivity) (by positivity)]
    ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  linarith

/-- [proved-derived] **`off_jump`: a part's rounding moves its weight by at most the rounding.**
`|ln(E + X ρ) − ln(E + X)| ≤ |ln ρ|` (the lower part's `J_off` at a split, its `X̂` rounded by `ρ_ℓ`
at `W` bits; `Drift.log_add_le`). -/
theorem off_jump {E X ρ : ℝ} (hE : 0 ≤ E) (hX : 0 < X) (hρ : 0 < ρ) :
    |Real.log (E + X * ρ) - Real.log (E + X)| ≤ |Real.log ρ| := by
  have := log_add_le hE (mul_pos hX hρ) hX
  rwa [Real.log_mul hX.ne' hρ.ne', add_sub_cancel_left] at this

/-- [proved-derived] **`split_effect`: the split moves the parting node's weight by its upper
rounding alone.** At the parting node `s_j` (implicit before the split, `K = 0`), the upper part is
the exact closed form of the lower part's weight `w` before its rounding, rounded by `r`
(`Compaction.chain_split`), so `K′ = K + ln r − (ln w′ − ln w)` with `w′` the lower part's weight
after its rounding. Then `|ln Ŵ′ − ln Ŵ| ≤ |ln r|` at `s_j`: the lower rounding's move cancels. -/
theorem split_effect {E M K K' w w' r : ℝ} (hE : 0 ≤ E) (hM : 0 < M) (hw : 0 < w) (hw' : 0 < w')
    (hr : 0 < r) (hK : K' = K + Real.log r - (Real.log w' - Real.log w)) :
    |Real.log (E + Real.exp K' * (M * w')) - Real.log (E + Real.exp K * (M * w))| ≤
      |Real.log r| := by
  have e : Real.exp K' * (M * w') = Real.exp K * (M * w) * r := by
    rw [hK, Real.exp_sub, Real.exp_add, Real.exp_sub, Real.exp_log hr, Real.exp_log hw',
      Real.exp_log hw]
    field_simp
  have hK0 := mul_pos (Real.exp_pos K) (mul_pos hM hw)
  have := log_add_le hE (mul_pos hK0 hr) hK0
  rwa [Real.log_mul hK0.ne' hr.ne', add_sub_cancel_left, ← e] at this

section Path

variable {Ltr : Type*} [Fintype Ltr] {D : ℕ}

/-- [proved-derived] **`up_path`: a change below a node moves the weights above it by at most its
own move.** Two executed trees with the same own weights, shares and discrepancies at the strict
ancestors of `s`, and the same weights at every child of a strict ancestor off the path to `s`:
at every ancestor `s′` of `s`, `|ln Ŵ′_(s′) − ln Ŵ_(s′)| ≤ |ln Ŵ′_s − ln Ŵ_s|` (each weight is
1-Lipschitz in the one child weight that moves). With `split_effect` at `s = s_j`, a split moves
the root's executed weight by at most `|ln r_u|`. -/
theorem up_path (T T' : ConsistentTree Ltr D) (s : List Ltr) (hsD : s.length ≤ D)
    (hE : ∀ s', s' <+: s → s'.length < s.length → T'.E s' = T.E s')
    (hκ : ∀ s', s' <+: s → s'.length < s.length → T'.κ s' = T.κ s')
    (hK : ∀ s', s' <+: s → s'.length < s.length → T'.K s' = T.K s')
    (hsib : ∀ s' (b : Ltr), s' <+: s → s'.length < s.length → ¬ s' ++ [b] <+: s →
      T'.Wh (s' ++ [b]) = T.Wh (s' ++ [b])) :
    ∀ k s', s' <+: s → s'.length + k = s.length →
      |Real.log (T'.Wh s') - Real.log (T.Wh s')| ≤ |Real.log (T'.Wh s) - Real.log (T.Wh s)| := by
  intro k
  induction k with
  | zero =>
    intro s' hs' hl
    rw [hs'.eq_of_length (by omega)]
  | succ k ih =>
    intro s' hs' hl
    have hlt : s'.length < s.length := by omega
    have hD : s'.length < D := by omega
    set b0 : Ltr := s[s'.length] with hb0
    have hc : s' ++ [b0] <+: s := (prefix_concat_iff hs' hlt).2 rfl
    rw [T'.Wh_node s' hD, T.Wh_node s' hD, hE s' hs' hlt, hκ s' hs' hlt, hK s' hs' hlt]
    have hpos' : 0 < Real.exp (T.K s') * (T.κ s' * ∏ b, T'.Wh (s' ++ [b])) :=
      mul_pos (Real.exp_pos _) (mul_pos (T.κ_pos s') (prod_pos fun _ _ => T'.Wh_pos _))
    have hpos : 0 < Real.exp (T.K s') * (T.κ s' * ∏ b, T.Wh (s' ++ [b])) :=
      mul_pos (Real.exp_pos _) (mul_pos (T.κ_pos s') (prod_pos fun _ _ => T.Wh_pos _))
    refine (log_add_le (T.E_nonneg s') hpos' hpos).trans ?_
    have hprod : Real.log (Real.exp (T.K s') * (T.κ s' * ∏ b, T'.Wh (s' ++ [b]))) -
        Real.log (Real.exp (T.K s') * (T.κ s' * ∏ b, T.Wh (s' ++ [b]))) =
        Real.log (T'.Wh (s' ++ [b0])) - Real.log (T.Wh (s' ++ [b0])) := by
      have hWh' : ∀ b ∈ (univ : Finset Ltr), T'.Wh (s' ++ [b]) ≠ 0 := fun b _ => (T'.Wh_pos _).ne'
      have hWh : ∀ b ∈ (univ : Finset Ltr), T.Wh (s' ++ [b]) ≠ 0 := fun b _ => (T.Wh_pos _).ne'
      rw [Real.log_mul (Real.exp_pos _).ne' (mul_pos (T.κ_pos s')
          (prod_pos fun _ _ => T'.Wh_pos _)).ne',
        Real.log_mul (Real.exp_pos _).ne' (mul_pos (T.κ_pos s')
          (prod_pos fun _ _ => T.Wh_pos _)).ne',
        Real.log_mul (T.κ_pos s').ne' (prod_pos fun _ _ => T'.Wh_pos _).ne',
        Real.log_mul (T.κ_pos s').ne' (prod_pos fun _ _ => T.Wh_pos _).ne',
        Real.log_prod hWh', Real.log_prod hWh]
      have hsum : ∑ b, Real.log (T'.Wh (s' ++ [b])) - ∑ b, Real.log (T.Wh (s' ++ [b])) =
          Real.log (T'.Wh (s' ++ [b0])) - Real.log (T.Wh (s' ++ [b0])) := by
        rw [← sum_sub_distrib]
        refine sum_eq_single b0 (fun b _ hb => ?_) (fun h => absurd (mem_univ b0) h)
        have hoff : ¬ s' ++ [b] <+: s := fun h =>
          hb ((prefix_concat_iff hs' hlt).1 h).symm
        rw [hsib s' b hs' hlt hoff, sub_self]
      linarith
    rw [hprod]
    exact ih (s' ++ [b0]) hc (by simp; omega)

end Path

/-- [proved-derived] **`split_charge`: a split's charges.** At a split, the parting node's
discrepancy moves by `ln r_u − J_off`, the lower part's bottom's by `ln ρ_ℓ`, with
`|J_off| ≤ |ln ρ_ℓ|` (`off_jump`), and the weights above the parting node by at most `|ln r_u|`
(`split_effect`, `up_path`). So the discrepancies below and above a stored level take at most
`|ln r_u| + 2|ln ρ_ℓ|` (the upper part's drift), and the passage, which also reads the move above,
at most `2(|ln r_u| + |ln ρ_ℓ|)` (the increment a split carries up). -/
theorem split_charge {ru ρ Joff e : ℝ} (hoff : |Joff| ≤ |Real.log ρ|) (he : |e| ≤ |Real.log ru|) :
    |Real.log ru - Joff| + |Real.log ρ| ≤ |Real.log ru| + 2 * |Real.log ρ| ∧
      |Real.log ru - Joff| + |Real.log ρ| + |e| ≤ 2 * (|Real.log ru| + |Real.log ρ|) := by
  have h := abs_sub (Real.log ru) Joff
  constructor <;> linarith

/-! ### One cell over the stored levels -/

/-- [proved-derived] **`level_read_drift`: one cell's read over its stored levels.** At the levels
`i = 0, …, L` of a read (each a stored chain read once at its top), let level `i < L` read
`q̂_i` within `θ_i` of `(E′_i + Q̂_i q̂_(i+1))/(E_i + Q̂_i)` (its carried `β̂ = E/Q̂`, `Q̂` the bottom
split mass times `2^(−S)`), the ideal face `q_i = (E′_i + P_i q_(i+1))/(E_i + P_i)`, and the bottom
level read within `θ_L` of its face. Then
`|ln q̂_0 − ln q_0| ≤ Σ_(i ≤ L) θ_i + Σ_(i < L) |ln Q̂_i − ln P_i|`, each split-mass drift at most its
bottom's `tot` (`ConsistentTree.split_mass_drift`): the read's certificate `Σ θ + Σ drift`
(Rust `CellReading::residual`). -/
theorem level_read_drift (L : ℕ) (E E' P Q q qh θ : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i)
    (hE' : ∀ i, 0 ≤ E' i) (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i) (hq : ∀ i, 0 < q i)
    (hqh : ∀ i, 0 < qh i)
    (hideal : ∀ i < L, q i = (E' i + P i * q (i + 1)) / (E i + P i))
    (hround : ∀ i < L,
      |Real.log (qh i) - Real.log ((E' i + Q i * qh (i + 1)) / (E i + Q i))| ≤ θ i)
    (hbottom : |Real.log (qh L) - Real.log (q L)| ≤ θ L) :
    |Real.log (qh 0) - Real.log (q 0)| ≤
      ∑ i ∈ range (L + 1), θ i + ∑ i ∈ range L, |Real.log (Q i) - Real.log (P i)| := by
  have key : ∀ k i, i + k = L → |Real.log (qh i) - Real.log (q i)| ≤
      ∑ j ∈ Ico i (L + 1), θ j + ∑ j ∈ Ico i L, |Real.log (Q j) - Real.log (P j)| := by
    intro k
    induction k with
    | zero =>
      intro i hi
      simp only [add_zero] at hi
      subst hi
      simpa [Nat.Ico_succ_singleton] using hbottom
    | succ k ih =>
      intro i hi
      have hiL : i < L := by omega
      have hface := node_face_drift (hE i) (hE' i) (hP i) (hQ i) (hq (i + 1)) (hqh (i + 1))
        (hround i hiL)
      rw [← hideal i hiL] at hface
      have hrest := ih (i + 1) (by omega)
      rw [sum_eq_sum_Ico_succ_bot (by omega : i < L + 1), sum_eq_sum_Ico_succ_bot hiL]
      linarith
  have h := key L 0 (by omega)
  simpa [← range_eq_Ico] using h

/-! ### The per-cell count of mantissa units

The rule's `U = n* P² + max((n* + 1) P², 4n* P)` (Rust `mantissa_units`) counts, per digit, the
units of `2^(1−W)` a cell's read can carry in its stored levels' drifts: one per mantissa rebase,
one per rounding of a split part. One arrival's deposit (`Law::apply_branch`) walks its path's
stored levels `m = 0, …, L − 1` bottom-up: level `m` adds the carried increment from below and its
own rebase `r_m` to its drift, and carries up `θ_m + 2r_m + 2s_m` plus the carried increment, with
`s_m = u + ℓ` the split's two roundings at the parting level (`split_charge`); the parting level's
upper part also takes `o = u + 2ℓ` into its drift (`Law::part`). The `θ` are the face roundings,
counted apart (the rule's `ε/μ̂` term), so in units the arrival charges level `ℓ`

```text
arrivalUnits ℓ = r_ℓ + o_ℓ + Σ_(ℓ < m < L) 2 (r_m + s_m) .
```

A rebase is taken only at a level read below its stored bottom (`level < top`), so a level whose
bottom is the declared depth `D` (a leaf) takes none; the bottoms rise strictly down a path. -/

/-- [definition] **One arrival's units at level `ℓ`** of its path of `L` stored levels: its own
rebase `r ℓ`, the parting upper part's `o ℓ`, and twice every rebase and split below it. -/
def arrivalUnits (L : ℕ) (r s o : ℕ → ℕ) (ℓ : ℕ) : ℕ :=
  r ℓ + o ℓ + ∑ m ∈ Ioo ℓ L, 2 * (r m + s m)

/-- [proved-derived] **`rebases_below`: the rebases below a level number at most `D − 1 − b`.**
With the bottoms strictly rising down the path, at most `D`, and a rebase only below `D`, the
levels below one with bottom `b` that rebase have distinct bottoms in `(b, D)`. -/
theorem rebases_below {L D ℓ : ℕ} {bot r : ℕ → ℕ} (hmono : ∀ i j, i < j → j < L → bot i < bot j)
    (hD : ∀ m < L, bot m ≤ D) (hr : ∀ m, r m ≤ 1) (hrD : ∀ m < L, bot m = D → r m = 0) :
    ∑ m ∈ Ioo ℓ L, r m ≤ D - 1 - bot ℓ := by
  classical
  have h1 : ∑ m ∈ Ioo ℓ L, r m ≤ ((Ioo ℓ L).filter fun m => bot m < D).card := by
    rw [card_eq_sum_ones, sum_filter]
    refine sum_le_sum fun m hm => ?_
    have hmL : m < L := (mem_Ioo.1 hm).2
    split_ifs with h
    · exact hr m
    · have : bot m = D := le_antisymm (hD m hmL) (not_lt.1 h)
      rw [hrD m hmL this]
  have h2 : ((Ioo ℓ L).filter fun m => bot m < D).card ≤ (Ioo (bot ℓ) D).card := by
    refine card_le_card_of_injOn bot (fun m hm => ?_) (fun i hi j hj hij => ?_)
    · rw [coe_filter, Set.mem_ofPred_eq, mem_Ioo] at hm
      exact mem_Ioo.2 ⟨hmono ℓ m hm.1.1 hm.1.2, hm.2⟩
    · rw [coe_filter, Set.mem_ofPred_eq, mem_Ioo] at hi hj
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact absurd hij (hmono i j h hj.1.2).ne
      · exact absurd hij (hmono j i h hi.1.2).ne'
  rw [Nat.card_Ioo] at h2
  omega

/-- [proved-derived] **`arrival_units_le`: one arrival charges a level at most `2(D − b) − 1 + 4`
units.** At a level with bottom `b < D`: its own rebase and twice each rebase below,
`1 + 2(D − 1 − b) = 2(D − b) − 1` (`rebases_below`), and the split's at most `4`: twice its two
roundings to the levels above the parting level, `u + 2ℓ ≤ 3` to the parting level's upper part
(`split_charge`), nothing below it. There is at most one parting level `p` a path. -/
theorem arrival_units_le {L D ℓ p : ℕ} {bot r s o : ℕ → ℕ}
    (hmono : ∀ i j, i < j → j < L → bot i < bot j) (hD : ∀ m < L, bot m ≤ D)
    (hr : ∀ m, r m ≤ 1) (hrD : ∀ m < L, bot m = D → r m = 0)
    (hs : ∀ m, m ≠ p → s m = 0) (ho : ∀ m, m ≠ p → o m = 0) (hsp : s p ≤ 2) (hop : o p ≤ 3)
    (hb : bot ℓ < D) :
    arrivalUnits L r s o ℓ ≤ 2 * (D - bot ℓ) - 1 + 4 := by
  classical
  have hreb := rebases_below (ℓ := ℓ) hmono hD hr hrD
  have hsplit : o ℓ + ∑ m ∈ Ioo ℓ L, 2 * s m ≤ 4 := by
    by_cases hp : p ∈ Ioo ℓ L
    · rw [← mul_sum, sum_eq_single_of_mem p hp (fun m _ hm => hs m hm),
        ho ℓ (mem_Ioo.1 hp).1.ne]
      omega
    · rw [sum_eq_zero fun m hm => by rw [hs m (fun h => hp (h ▸ hm)), mul_zero]]
      by_cases hlp : ℓ = p
      · subst hlp; omega
      · rw [ho ℓ hlp]; omega
  have hsum : ∑ m ∈ Ioo ℓ L, 2 * (r m + s m) =
      2 * ∑ m ∈ Ioo ℓ L, r m + ∑ m ∈ Ioo ℓ L, 2 * s m := by
    rw [mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun m _ => by ring
  unfold arrivalUnits
  rw [hsum]
  have := hr ℓ
  omega

/-- [proved-derived] **`levels_units`: `Σ (2(D − b) − 1) ≤ D²` over a read's levels.** The levels
of a read that carry a drift have distinct bottoms below `D`, so the sum is at most the full
tree's `Σ_(d<D) (2(D − d) − 1) = D²` (`Drift.sum_levels_below`, here in `ℕ`), and there are at
most `D` of them. -/
theorem levels_units {L D : ℕ} {c : ℕ → ℕ} (hmono : ∀ i j, i < j → j < L → c i < c j)
    (hD : ∀ ℓ < L, c ℓ < D) :
    ∑ ℓ ∈ range L, (2 * (D - c ℓ) - 1 + 4) ≤ D ^ 2 + 4 * D := by
  classical
  have hrise : ∀ ℓ < L, ℓ ≤ c ℓ := by
    intro ℓ
    induction ℓ with
    | zero => intro _; omega
    | succ k ih => intro hk; have := hmono k (k + 1) (by omega) hk; have := ih (by omega); omega
  have hLD : L ≤ D := by
    rcases Nat.eq_zero_or_pos L with h | h
    · omega
    · have := hrise (L - 1) (by omega); have := hD (L - 1) (by omega); omega
  have hfull : ∀ D : ℕ, ∑ d ∈ range D, (2 * (D - d) - 1) = D ^ 2 := by
    intro D
    induction D with
    | zero => simp
    | succ D ih =>
      rw [sum_range_succ]
      have e : ∑ d ∈ range D, (2 * (D + 1 - d) - 1) = ∑ d ∈ range D, (2 * (D - d) - 1 + 2) :=
        sum_congr rfl fun d hd => by have := mem_range.1 hd; omega
      rw [e, sum_add_distrib, ih, sum_const, card_range, smul_eq_mul]
      have : 2 * (D + 1 - D) - 1 = 1 := by omega
      rw [this]; ring
  calc ∑ ℓ ∈ range L, (2 * (D - c ℓ) - 1 + 4)
      ≤ ∑ ℓ ∈ range L, (2 * (D - ℓ) - 1 + 4) :=
        sum_le_sum fun ℓ hℓ => by have := hrise ℓ (mem_range.1 hℓ); omega
    _ = ∑ ℓ ∈ range L, (2 * (D - ℓ) - 1) + 4 * L := by
        rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_comm]
    _ ≤ ∑ ℓ ∈ range D, (2 * (D - ℓ) - 1) + 4 * D :=
        add_le_add (sum_le_sum_of_subset (range_subset_range.2 hLD)) (by omega)
    _ = D ^ 2 + 4 * D := by rw [hfull]

/-- [proved-derived] **`cell_units`: a cell's read carries at most `n* D² + 4n* D` units a
digit.** Each level `ℓ` of the read (bottom `c ℓ < D`, rising) holds the units of the arrivals
through it, each at most `2(D − c ℓ) − 1 + 4` (`arrival_units_le`; a split part inherits its
chain's drift, and the bound only grows as the bottom rises toward the root), and one unit for each
arrival that split its chain above it; `arrivals ℓ` counts both, distinct, at most `n*`. -/
theorem cell_units {α : Type*} {L D n : ℕ} {c : ℕ → ℕ} (arrivals : ℕ → Finset α)
    (charge : ℕ → α → ℕ) (hmono : ∀ i j, i < j → j < L → c i < c j) (hD : ∀ ℓ < L, c ℓ < D)
    (hcard : ∀ ℓ < L, (arrivals ℓ).card ≤ n)
    (hcharge : ∀ ℓ < L, ∀ a ∈ arrivals ℓ, charge ℓ a ≤ 2 * (D - c ℓ) - 1 + 4) :
    ∑ ℓ ∈ range L, ∑ a ∈ arrivals ℓ, charge ℓ a ≤ n * D ^ 2 + 4 * n * D := by
  calc ∑ ℓ ∈ range L, ∑ a ∈ arrivals ℓ, charge ℓ a
      ≤ ∑ ℓ ∈ range L, n * (2 * (D - c ℓ) - 1 + 4) := by
        refine sum_le_sum fun ℓ hℓ => ?_
        have hℓ := mem_range.1 hℓ
        calc ∑ a ∈ arrivals ℓ, charge ℓ a ≤ (arrivals ℓ).card • (2 * (D - c ℓ) - 1 + 4) :=
              sum_le_card_nsmul _ _ _ (hcharge ℓ hℓ)
          _ ≤ n * (2 * (D - c ℓ) - 1 + 4) := by
              rw [smul_eq_mul]; exact Nat.mul_le_mul_right _ (hcard ℓ hℓ)
    _ = n * ∑ ℓ ∈ range L, (2 * (D - c ℓ) - 1 + 4) := by rw [mul_sum]
    _ ≤ n * (D ^ 2 + 4 * D) := Nat.mul_le_mul_left _ (levels_units hmono hD)
    _ = n * D ^ 2 + 4 * n * D := by ring

/-- [proved-derived] **`rule_units`: the rule's `U` covers the count.** For `D ≤ P`,
`n D² + 4n D ≤ n P² + max((n + 1) P², 4n P)` (`mantissa_units`), and for `P ≥ 4` the rule is
`(2n + 1) P²`. -/
theorem rule_units {n D P : ℕ} (hDP : D ≤ P) :
    n * D ^ 2 + 4 * n * D ≤ n * P ^ 2 + max ((n + 1) * P ^ 2) (4 * n * P) ∧
      (4 ≤ P → n * P ^ 2 + max ((n + 1) * P ^ 2) (4 * n * P) = (2 * n + 1) * P ^ 2) := by
  refine ⟨?_, fun hP => ?_⟩
  · have h1 : n * D ^ 2 ≤ n * P ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hDP 2)
    have h2 : 4 * n * D ≤ 4 * n * P := Nat.mul_le_mul_left _ hDP
    have := le_max_right ((n + 1) * P ^ 2) (4 * n * P)
    omega
  · have : 4 * n * P ≤ (n + 1) * P ^ 2 := by
      calc 4 * n * P ≤ P * n * P := by
            rw [show 4 * n * P = 4 * (n * P) by ring, show P * n * P = P * (n * P) by ring]
            exact Nat.mul_le_mul_right _ hP
        _ ≤ (n + 1) * P ^ 2 := by nlinarith
    rw [max_eq_left this]; ring

/-- [proved-derived] **`rule_units_shallow`: the count `(n + 1) P²` alone is short at `P = 1`.**
At campaign 1's `n* = 6,148` and `P = 1`, `(n* + 1) P² = 6,149 < 24,592 = 4n* P`, so the maximum
in `U` is needed there. -/
theorem rule_units_shallow : (6148 + 1) * 1 ^ 2 < 4 * 6148 * 1 := by norm_num

/-! ### Audit -/

section Audit

#print axioms tot_nonneg
#print axioms tot_of_zero
#print axioms tot_add_le
#print axioms tot_le_history
#print axioms tot_path_le
#print axioms ConsistentTree.split_log
#print axioms ConsistentTree.drift_le_tot
#print axioms ConsistentTree.split_mass_drift
#print axioms stored_passage
#print axioms carried_step
#print axioms read_jump
#print axioms off_jump
#print axioms split_effect
#print axioms up_path
#print axioms split_charge
#print axioms level_read_drift
#print axioms rebases_below
#print axioms arrival_units_le
#print axioms levels_units
#print axioms cell_units
#print axioms rule_units
#print axioms rule_units_shallow

end Audit

end Holonics.Compression.Landmark.Context.StoredDrift
