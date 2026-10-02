import Holonics.Compression.Landmark.Context.Tree

/-!
# Compression.Landmark.Context.Drift: the lattice's drift over the tree and the passage

[definition; agent-inferred] The landmark lattice's passage-level drift (#62, "the landmark
lattice's drift"; rebuild step 4, #73). The executed receiving tree reads each node's face on the
lattice `2^(−M_p)` from a carried ratio `β̂` (Tree §6′); the ideal tree reads the same faces exactly.
This owner composes `Tree`'s one-step lattice laws (`lattice_step_telescope`,
`lattice_node_telescope`, `weight_log_lipschitz`, `mix_ratio_bound`) over the tree and the passage
into the executed code's departure from the ideal code, over the whole passage and at one cell. The
computational object is the helical pair interaction; this owner is the receiving parametron's
landmark tree, executed. Of the winding guide's six general objects it touches the **tower thread**
(the drift adds down the restriction chain of context depths, a node's arrivals partitioned among
its children) and **faces and placement** (the executed face against the ideal face at each
receiving face); the helix, the pair, the cell holonomy and the tube stay attached, unchanged.

```text
node       q_t = (E_(t+1) + P_t x_t)/(E_t + P_t),  q̂_t ≈ (E_(t+1) + Q_t x̂_t)/(E_t + Q_t) within θ_t in ln
           P' = P x,  Q' = Q x̂ c  at an arrival (c > 0: a rebase, a carrier release, a split);  β = E/P, β̂ = E/Q
drift      ln Q_N − ln P_N = ln Q_0 − ln P_0 + Σ (ln x̂ − ln x + ln c)
passage    |Σ (ln q̂ − ln q)| ≤ |Σ (ln x̂ − ln x)| + Σ (θ + |ln c|) + 2|ln Q_0 − ln P_0|        one node
tree       |Σ_(t<N) (ln q̂_root − ln q_root)| ≤ Σ_(t<N) Σ_(d ≤ D) (θ_d + |ln c_d|)               (no c at D)
cell       |ln q̂_root,t₀ − ln q_root,t₀| ≤ Σ_(d ≤ D) θ_d + Σ_(d < D) Σ_(t < t₀ at s_d) (|ln c_(s_d)| + Σ_(d < d' ≤ D) (θ_d' + |ln c_d'|))
uniform    θ ≤ 2u above D, θ ≤ u at D, |ln c| ≤ ρ:
           passage ≤ N ((2D + 1) u + D ρ);   cell ≤ t₀ D² (u + ρ) + (2D + 1) u
```

[proved-derived; formal-checked] What is proved.

1. **The weight's logarithm** (`log_add_mono`, `log_add_le`, `log_add_between`, `face_log_le`,
   `face_weight_form`): adding a nonnegative own weight moves `ln` of a split mass by a value of
   the same sign and at most its size, so the node weight is 1-Lipschitz in the log of its split
   mass (`Tree.weight_log_lipschitz`'s real-log face), and the face `(E' + Q x̂)/(E + Q)` moves from
   `(E' + P x)/(E + P)` by at most `|ln Q − ln P| + |ln x̂ − ln x|` (`Tree.mix_ratio_bound`'s); it is
   the lattice chart's mixture `(β k + x)/(1 + β)` at `β = E/Q`, `k = E'/E`.
2. **One node over its passage** (`filter_telescope`, `split_drift`, `node_passage_drift`): the
   chart's drift `ln Q − ln P` is the founding's, the children's summed departures and the factors'
   logs. Both codes telescope to their weights, so the node's summed departure is at most its
   children's summed departure (not their departures summed in absolute value), its roundings, its
   factors once each, and twice the founding's drift. A factor raised and a factor lowered offset:
   the final weights differ by a value between `0` and the chart's drift, and each factor's step
   departs from the telescope by a value of the opposite sign (`log_add_between`).
3. **One node at one arrival** (`node_face_drift`): the face departs by its rounding, the chart's
   drift at the node, and its child's departure.
4. **Over the tree** (`tree_drift`, `tree_drift_below`, `arrivals`, `arrivals_partition`): every
   observation's address reaches the maximum depth, so a node's arrivals partition among its
   children, and the summed departure at a node is at most its arrivals' costs summed over the
   depths from it to `D`.
5. **The executed tree** (`ExecutedTree`, `ExecutedTree.passage_drift`, `ExecutedTree.cell_drift`):
   - over the passage, the executed code is within each observation's costs summed down its path
     of the ideal code: the drift is summed once over the passage, never compounded;
   - at one cell, the read departs by the path's roundings plus, at each node, the costs of its
     earlier arrivals below it: the per-cell rule's composition.
6. **In the Rust's units** (`ExecutedTree.passage_drift_uniform`, `ExecutedTree.cell_drift_uniform`,
   `sum_levels_below`): with each internal rounding at most `2u`, each leaf rounding at most `u`
   and each factor within `ρ` in `ln`, the passage's code is within `N((2D + 1)u + Dρ)` of the
   ideal, and one cell within `t₀ D² (u + ρ) + (2D + 1)u`. At `u = ε/μ̂ = 2^(−M_p−1)/μ̂`,
   `ρ = 2^(1−W) + ρ_c`, `t₀ ≤ n*` and `P = D`, the cell bound is the Rust rule's
   `(n* P² + 2P + 1) ε/μ̂ + n* P² (2^(1−W) + ρ_c)` before the digits `B` and `log₂ e < 3/2`
   (`Landmarks::face_rule`). The rule's `P` is `LandmarkDeclaration::path_depth`: `D` on the
   cell branch alone, and with the bundle branch both branches' depths plus `2`, at least each
   branch's depth (the bound grows with `D`; the join's own drift is not stated here).

[agent-inferred] **The passage is sharper than the cell.** A cell's read carries its nodes' drift,
which grows with their arrivals (the `t₀` above); the passage's code does not, because each node's
code telescopes to its weight and its weight is 1-Lipschitz in its split mass. Per reading the
passage pays `(2D + 1)u + Dρ`, about `n* D/2` times less than the per-cell rule's `n* D² (u + ρ)`
summed over the cells. So the widths `M_p` and `W`, derived to hold the per-cell read within a
quarter grain, hold the passage's code far tighter; a width derived for the average code alone
would need about `log₂(n* D/2)` bits fewer. The widths stay the rule's: the read's per-cell certificate is the
receiver's resolution.

[conditional] **What the theorems cover in the Rust.**
- **The carried certificates.** The deposit carries each node's `excess` (its routed
  subsequence's executed code against the ideal) and `drift` (`Δ ≥ |ln β̂ − ln β|`): it adds the
  read's `θ`, twice the rebases' units, the child's increment and a split's units to the excess,
  and the child's increment and the rebases' units to the drift (`Law::apply_branch`). Item 2
  states the excess's law with each factor counted once, so the doubled rebase units are
  conservative; item 5's `cell_drift` is the read's `ρ ≤ Σ drift + Σ θ`.
- **The factors.** A mantissa rebase is `c = x/m'` with `|ln c| < 2^(1−W)`
  (`Tree.rebase_log_residual`); a carrier release lies in `[1, 1 + 1/D̂)` (`Carrier`), of the
  opposite sign, which item 2 allows.
- **Stored where paths part** (agent-inferred, not formalized). `ExecutedTree` is the full tree.
  The compacted executed tree (`Compaction`, Decision 37) is read as an instance: a stored chain's
  implicit nodes read their faces exactly (`θ = 0`, `c = 1`, by `Compaction.chain_ratio`, an
  identity in the chain's bottom split mass), its rebases are factors at its bottom, its rounding
  at its top, and a split's two `W`-bit carries are factors at the two parts' bottoms on the
  arrival before the split. That instance, and the count of splits behind the rule's
  `(2n* + 1) P² 2^(1−W)`, stay owed in #62.
- **Not stated here**: the enlarged tree's join (`Context/LocalWeighing`'s executed join tree,
  whose two sides are both executed, adds its own drift; each dyadic cell's join costs at most one
  bit against either branch), and the certified binary logarithm's squaring invariant
  (`landmark::binary_log`); both stay owed in #62.

[proved-standard] The telescoping of a context-tree weighting code to its root weight is Willems,
Shtarkov and Tjalkens (1995); the proofs here are this owner's.

| Claim | Lean | Rust |
|---|---|---|
| the weight is 1-Lipschitz in its split mass; the face's drift | `log_add_le`, `log_add_between`, `face_log_le`, `face_weight_form` | `compression::landmark::context::Beta` (the carried `β̂`) |
| a node's code over its passage; the chart's drift | `split_drift`, `node_passage_drift`, `node_face_drift` | `Law::apply_branch` (`excess`, `drift`) |
| the drift summed over the tree and the passage | `tree_drift`, `tree_drift_below`, `arrivals_partition`, `ExecutedTree.passage_drift` | `Landmarks::deposit` |
| one cell's read; the per-cell rule | `ExecutedTree.cell_drift`, `ExecutedTree.cell_drift_uniform`, `ExecutedTree.passage_drift_uniform` | `Landmarks::face_rule`, `face_bits`, `carrier_width`, `CellReading::residual` |
-/

namespace Holonics.Compression.Landmark.Context.Drift

open Finset

/-! ### The logarithm of a weight -/

/-- [proved-standard] **`log_add_mono`.** Adding a nonnegative own weight shrinks a log ratio:
for `0 < a ≤ b` and `E ≥ 0`, `0 ≤ ln(E + b) − ln(E + a) ≤ ln b − ln a`. -/
theorem log_add_mono {E a b : ℝ} (hE : 0 ≤ E) (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ Real.log (E + b) - Real.log (E + a) ∧
      Real.log (E + b) - Real.log (E + a) ≤ Real.log b - Real.log a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  refine ⟨sub_nonneg.2 (Real.log_le_log (by linarith) (by linarith)), ?_⟩
  have hq : (E + b) / (E + a) ≤ b / a := by
    rw [div_le_div_iff₀ (by linarith) ha]
    nlinarith [mul_le_mul_of_nonneg_left hab hE]
  have h := Real.log_le_log (by positivity) hq
  rw [Real.log_div (by linarith) (by linarith), Real.log_div hb.ne' ha.ne'] at h
  exact h

/-- [proved-standard] **`log_add_le`: the weight is 1-Lipschitz in the log of its split mass.**
`|ln(E + a) − ln(E + b)| ≤ |ln a − ln b|` for `E ≥ 0`, `a, b > 0` (the real-log face of
`Tree.weight_log_lipschitz`). -/
theorem log_add_le {E a b : ℝ} (hE : 0 ≤ E) (ha : 0 < a) (hb : 0 < b) :
    |Real.log (E + a) - Real.log (E + b)| ≤ |Real.log a - Real.log b| := by
  rcases le_total a b with hab | hab
  · obtain ⟨h0, h1⟩ := log_add_mono hE ha hab
    rw [abs_sub_comm, abs_of_nonneg h0, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact h1
  · obtain ⟨h0, h1⟩ := log_add_mono hE hb hab
    rw [abs_of_nonneg h0, abs_of_nonneg (by linarith)]
    exact h1

/-- [proved-derived] **`face_log_le`: the path mixture moves by at most its two inputs' drifts.**
The node's face read through its weights, `(E' + Q x)/(E + Q)` (`face_weight_form`: the path
mixture `(β k + x)/(1 + β)` at `β = E/Q`, `k = E'/E`), moves from `(E' + P x)/(E + P)` by at most
`|ln Q − ln P| + |ln x̂ − ln x|` in `ln`: the real-log face of `Tree.mix_ratio_bound`, with the
chart's drift `Δ = |ln β̂ − ln β| = |ln Q − ln P|`. -/
theorem face_log_le {E E' P Q x xh : ℝ} (hE : 0 ≤ E) (hE' : 0 ≤ E') (hP : 0 < P) (hQ : 0 < Q)
    (hx : 0 < x) (hxh : 0 < xh) :
    |Real.log ((E' + Q * xh) / (E + Q)) - Real.log ((E' + P * x) / (E + P))| ≤
      |Real.log Q - Real.log P| + |Real.log xh - Real.log x| := by
  rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity)]
  have h1 : |Real.log (E' + Q * xh) - Real.log (E' + Q * x)| ≤ |Real.log xh - Real.log x| := by
    have := log_add_le hE' (mul_pos hQ hxh) (mul_pos hQ hx)
    rwa [Real.log_mul hQ.ne' hxh.ne', Real.log_mul hQ.ne' hx.ne', add_sub_add_left_eq_sub] at this
  have h2 : |(Real.log (E' + Q * x) - Real.log (E' + P * x)) -
      (Real.log (E + Q) - Real.log (E + P))| ≤ |Real.log Q - Real.log P| := by
    rcases le_total P Q with hPQ | hPQ
    · obtain ⟨a0, a1⟩ := log_add_mono hE' (mul_pos hP hx)
        (mul_le_mul_of_nonneg_right hPQ hx.le)
      obtain ⟨b0, b1⟩ := log_add_mono hE hP hPQ
      rw [Real.log_mul hQ.ne' hx.ne', Real.log_mul hP.ne' hx.ne'] at a1
      rw [abs_of_nonneg (sub_nonneg.2 (Real.log_le_log hP hPQ)), abs_le]
      constructor <;> linarith
    · obtain ⟨a0, a1⟩ := log_add_mono hE' (mul_pos hQ hx)
        (mul_le_mul_of_nonneg_right hPQ hx.le)
      obtain ⟨b0, b1⟩ := log_add_mono hE hQ hPQ
      rw [Real.log_mul hQ.ne' hx.ne', Real.log_mul hP.ne' hx.ne'] at a1
      rw [abs_of_nonpos (sub_nonpos.2 (Real.log_le_log hQ hPQ)), abs_le]
      constructor <;> linarith
  calc |Real.log (E' + Q * xh) - Real.log (E + Q) - (Real.log (E' + P * x) - Real.log (E + P))|
      = |(Real.log (E' + Q * xh) - Real.log (E' + Q * x)) +
          ((Real.log (E' + Q * x) - Real.log (E' + P * x)) -
            (Real.log (E + Q) - Real.log (E + P)))| := by ring_nf
    _ ≤ |Real.log (E' + Q * xh) - Real.log (E' + Q * x)| +
          |(Real.log (E' + Q * x) - Real.log (E' + P * x)) -
            (Real.log (E + Q) - Real.log (E + P))| := abs_add_le _ _
    _ ≤ |Real.log xh - Real.log x| + |Real.log Q - Real.log P| := add_le_add h1 h2
    _ = _ := add_comm _ _

/-- [proved-derived] **`face_weight_form`.** The lattice chart's path mixture at the carried ratio
`β = E/Q` and the KT face `k = E'/E` is the weight ratio `(E' + Q x)/(E + Q)`
(`Tree.lattice_step_telescope`'s first face). -/
theorem face_weight_form {E E' Q x : ℝ} (hE : 0 < E) (hQ : 0 < Q) :
    (E / Q * (E' / E) + x) / (1 + E / Q) = (E' + Q * x) / (E + Q) := by
  field_simp
  ring

/-! ### One node over its passage -/

/-- [proved-derived] **`filter_telescope`.** A quantity that moves only at the arrivals `p`
telescopes over them: `Σ_(t < N, p t) (g(t + 1) − g t) = g N − g 0`. -/
theorem filter_telescope (g : ℕ → ℝ) (p : ℕ → Prop) [DecidablePred p]
    (hg : ∀ t, ¬ p t → g (t + 1) = g t) (N : ℕ) :
    ∑ t ∈ (range N).filter p, (g (t + 1) - g t) = g N - g 0 := by
  rw [sum_filter, ← sum_range_sub g N]
  refine sum_congr rfl fun t _ => ?_
  split_ifs with h
  · rfl
  · rw [hg t h, sub_self]

/-- [proved-derived] **`split_drift`: the executed split mass against the ideal one.** At a node
whose ideal split mass steps `P' = P x` and executed split mass `Q' = Q x̂ c` at each arrival (`x`,
`x̂` the child's ideal and executed faces, `c` any positive factor: a mantissa or carrier rebase,
`1/(1 − r)`, or a stored chain's split, `Tree.lattice_step_telescope`) and stays between arrivals,
`ln Q_N − ln P_N = ln Q_0 − ln P_0 + Σ_(t < N, p t) (ln x̂_t − ln x_t + ln c_t)`: the chart's drift
`Δ = |ln β̂ − ln β|` (`β = E/P`, `β̂ = E/Q`) is the child's summed drift plus the factors. -/
theorem split_drift (P Q x xh c : ℕ → ℝ) (p : ℕ → Prop) [DecidablePred p]
    (hP : ∀ t, 0 < P t) (hQ : ∀ t, 0 < Q t) (hx : ∀ t, p t → 0 < x t)
    (hxh : ∀ t, p t → 0 < xh t) (hc : ∀ t, p t → 0 < c t)
    (hPs : ∀ t, P (t + 1) = if p t then P t * x t else P t)
    (hQs : ∀ t, Q (t + 1) = if p t then Q t * xh t * c t else Q t) (N : ℕ) :
    Real.log (Q N) - Real.log (P N) = Real.log (Q 0) - Real.log (P 0) +
      ∑ t ∈ (range N).filter p, (Real.log (xh t) - Real.log (x t) + Real.log (c t)) := by
  have key := filter_telescope (fun t => Real.log (Q t) - Real.log (P t)) p
    (fun t h => by simp only [hPs t, hQs t, if_neg h]) N
  rw [← sub_eq_iff_eq_add', ← key]
  refine sum_congr rfl fun t ht => ?_
  have h := (mem_filter.1 ht).2
  rw [hPs t, hQs t, if_pos h, if_pos h, Real.log_mul (mul_pos (hQ t) (hxh t h)).ne' (hc t h).ne',
    Real.log_mul (hQ t).ne' (hxh t h).ne', Real.log_mul (hP t).ne' (hx t h).ne']
  ring

/-- [proved-derived] **`log_add_between`: the weight's log ratio lies between `0` and the split
masses' log ratio.** `ln(E + Q) − ln(E + P)` has the sign of `ln Q − ln P` and at most its size. -/
theorem log_add_between {E P Q : ℝ} (hE : 0 ≤ E) (hP : 0 < P) (hQ : 0 < Q) :
    min 0 (Real.log Q - Real.log P) ≤ Real.log (E + Q) - Real.log (E + P) ∧
      Real.log (E + Q) - Real.log (E + P) ≤ max 0 (Real.log Q - Real.log P) := by
  rcases le_total P Q with h | h
  · obtain ⟨h0, h1⟩ := log_add_mono hE hP h
    exact ⟨(min_le_left _ _).trans h0, h1.trans (le_max_right _ _)⟩
  · obtain ⟨h0, h1⟩ := log_add_mono hE hQ h
    exact ⟨(min_le_right _ _).trans (by linarith), (by linarith : _ ≤ (0 : ℝ)).trans
      (le_max_left _ _)⟩

/-- [proved-derived] **`node_passage_drift`: one node's executed code against its ideal code over
the passage.** At a node with own weight `E ≥ 0` (its stop weight times its own mass; it steps only
at the arrivals `p`), ideal split mass `P` and executed split mass `Q` stepping as in `split_drift`,
the ideal face at an arrival is the weight ratio `q_t = (E_(t+1) + P_t x_t)/(E_t + P_t)` and the
executed face `q̂_t` is the lattice's rounding of `(E_(t+1) + Q_t x̂_t)/(E_t + Q_t)`, within `θ_t` in
`ln`. Then over the passage
`|Σ (ln q̂_t − ln q_t)| ≤ |Σ (ln x̂_t − ln x_t)| + Σ (θ_t + |ln c_t|) + 2|ln Q_0 − ln P_0|`.
Both codes telescope to their weights (`Tree.lattice_node_telescope`); the final weights differ by
a value between `0` and the split masses' drift (`log_add_between`), and each factor's step
departs from the telescope by a value of the opposite sign and at most its size, so the factors
raised and the factors lowered offset, and each costs one `|ln c_t|`: the node adds its own
roundings and factors once to its children's summed drift, and nothing compounds. -/
theorem node_passage_drift (E P Q x xh c θ qh : ℕ → ℝ) (p : ℕ → Prop) [DecidablePred p]
    (hE : ∀ t, 0 ≤ E t) (hP : ∀ t, 0 < P t) (hQ : ∀ t, 0 < Q t) (hx : ∀ t, p t → 0 < x t)
    (hxh : ∀ t, p t → 0 < xh t) (hc : ∀ t, p t → 0 < c t)
    (hEs : ∀ t, ¬ p t → E (t + 1) = E t)
    (hPs : ∀ t, P (t + 1) = if p t then P t * x t else P t)
    (hQs : ∀ t, Q (t + 1) = if p t then Q t * xh t * c t else Q t)
    (hθ : ∀ t, p t →
      |Real.log (qh t) - Real.log ((E (t + 1) + Q t * xh t) / (E t + Q t))| ≤ θ t) (N : ℕ) :
    |∑ t ∈ (range N).filter p,
        (Real.log (qh t) - Real.log ((E (t + 1) + P t * x t) / (E t + P t)))| ≤
      |∑ t ∈ (range N).filter p, (Real.log (xh t) - Real.log (x t))| +
        ∑ t ∈ (range N).filter p, (θ t + |Real.log (c t)|) +
        2 * |Real.log (Q 0) - Real.log (P 0)| := by
  set A : ℕ → ℝ := fun t => Real.log (E t + Q t) with hA
  set B : ℕ → ℝ := fun t => Real.log (E t + P t) with hB
  set F := (range N).filter p with hF
  -- the executed face's departure from the executed weight's step
  set δ : ℕ → ℝ := fun t => Real.log ((E (t + 1) + Q t * xh t) / (E t + Q t)) - (A (t + 1) - A t)
    with hδ
  set up : ℕ → ℝ := fun t => max (Real.log (c t)) 0 with hup
  set dn : ℕ → ℝ := fun t => max (-Real.log (c t)) 0 with hdn
  have hδle : ∀ t ∈ F, -up t ≤ δ t ∧ δ t ≤ dn t := by
    intro t ht
    have h := (mem_filter.1 ht).2
    have hE1 := hE (t + 1)
    have hQx := mul_pos (hQ t) (hxh t h)
    have e : δ t = -(Real.log (E (t + 1) + Q t * xh t * c t) - Real.log (E (t + 1) + Q t * xh t)) := by
      simp only [hδ, hA, hQs t, if_pos h]
      rw [Real.log_div (by positivity) (by linarith [hE t, hQ t])]
      ring
    obtain ⟨b0, b1⟩ := log_add_between hE1 hQx (mul_pos hQx (hc t h))
    rw [Real.log_mul hQx.ne' (hc t h).ne', add_sub_cancel_left] at b0 b1
    rw [e]
    constructor
    · have : max 0 (Real.log (c t)) = up t := max_comm _ _
      linarith
    · have : -min 0 (Real.log (c t)) = dn t := by
        simp only [hdn]
        rcases le_total 0 (Real.log (c t)) with h' | h'
        · rw [min_eq_left h', max_eq_right (by linarith)]; ring
        · rw [min_eq_right h', max_eq_left (by linarith)]
      linarith
  have hideal : ∀ t ∈ F,
      Real.log ((E (t + 1) + P t * x t) / (E t + P t)) = B (t + 1) - B t := by
    intro t ht
    have h := (mem_filter.1 ht).2
    simp only [hB, hPs t, if_pos h]
    rw [Real.log_div (by linarith [hE (t + 1), mul_pos (hP t) (hx t h)])
      (by linarith [hE t, hP t])]
  have hAB : ∑ t ∈ F, ((A (t + 1) - A t) - (B (t + 1) - B t)) = (A N - B N) - (A 0 - B 0) := by
    have := filter_telescope (fun t => A t - B t) p (fun t h => by
      simp only [hA, hB, hEs t h, hPs t, hQs t, if_neg h]) N
    rw [← this]
    exact sum_congr rfl fun t _ => by ring
  have hsplit := split_drift P Q x xh c p hP hQ hx hxh hc hPs hQs N
  rw [← hF] at hsplit
  have hlogc : ∑ t ∈ F, Real.log (c t) = ∑ t ∈ F, up t - ∑ t ∈ F, dn t := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun t _ => ?_
    simp only [hup, hdn]
    rcases le_total 0 (Real.log (c t)) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have habsc : ∑ t ∈ F, |Real.log (c t)| = ∑ t ∈ F, up t + ∑ t ∈ F, dn t := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun t _ => ?_
    simp only [hup, hdn]
    rcases le_total 0 (Real.log (c t)) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring
    · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring
  have hup0 : 0 ≤ ∑ t ∈ F, up t := sum_nonneg fun t _ => le_max_right _ _
  have hdn0 : 0 ≤ ∑ t ∈ F, dn t := sum_nonneg fun t _ => le_max_right _ _
  obtain ⟨hN0, hN1⟩ := log_add_between (hE N) (hP N) (hQ N)
  have h0 : |A 0 - B 0| ≤ |Real.log (Q 0) - Real.log (P 0)| :=
    log_add_le (hE 0) (hQ 0) (hP 0)
  have hsum : ∑ t ∈ F, (Real.log (qh t) - Real.log ((E (t + 1) + P t * x t) / (E t + P t))) =
      ∑ t ∈ F, (Real.log (qh t) - Real.log ((E (t + 1) + Q t * xh t) / (E t + Q t))) +
        ∑ t ∈ F, δ t + ((A N - B N) - (A 0 - B 0)) := by
    rw [← hAB, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun t ht => ?_
    rw [hideal t ht, hδ]
    ring
  rw [hsum]
  have hθs : |∑ t ∈ F, (Real.log (qh t) - Real.log ((E (t + 1) + Q t * xh t) / (E t + Q t)))| ≤
      ∑ t ∈ F, θ t :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t ht => hθ t (mem_filter.1 ht).2)
  have hδlo : -∑ t ∈ F, up t ≤ ∑ t ∈ F, δ t := by
    rw [← sum_neg_distrib]; exact sum_le_sum fun t ht => (hδle t ht).1
  have hδhi : ∑ t ∈ F, δ t ≤ ∑ t ∈ F, dn t := sum_le_sum fun t ht => (hδle t ht).2
  -- the final weights and the factors' departures, together
  set ψ0 := Real.log (Q 0) - Real.log (P 0)
  set χ := ∑ t ∈ F, (Real.log (xh t) - Real.log (x t))
  have hψN : Real.log (Q N) - Real.log (P N) = ψ0 + χ + (∑ t ∈ F, up t - ∑ t ∈ F, dn t) := by
    rw [hsplit, sum_add_distrib, hlogc]; ring
  rw [hψN] at hN0 hN1
  have hmid : |(A N - B N) + ∑ t ∈ F, δ t| ≤ |ψ0| + |χ| + ∑ t ∈ F, |Real.log (c t)| := by
    rw [habsc, abs_le]
    have hψ := abs_nonneg ψ0
    have hχ := abs_nonneg χ
    have hψ1 := le_abs_self ψ0
    have hψ2 := neg_abs_le ψ0
    have hχ1 := le_abs_self χ
    have hχ2 := neg_abs_le χ
    constructor
    · rcases le_total 0 (ψ0 + χ + (∑ t ∈ F, up t - ∑ t ∈ F, dn t)) with h | h
      · rw [min_eq_left h] at hN0; linarith
      · rw [min_eq_right h] at hN0; linarith
    · rcases le_total 0 (ψ0 + χ + (∑ t ∈ F, up t - ∑ t ∈ F, dn t)) with h | h
      · rw [max_eq_right h] at hN1; linarith
      · rw [max_eq_left h] at hN1; linarith
  have htri := abs_add_le (∑ t ∈ F, (Real.log (qh t) -
    Real.log ((E (t + 1) + Q t * xh t) / (E t + Q t)))) ((A N - B N) + ∑ t ∈ F, δ t - (A 0 - B 0))
  have htri2 := abs_sub ((A N - B N) + ∑ t ∈ F, δ t) (A 0 - B 0)
  have e : ∑ t ∈ F, (Real.log (qh t) - Real.log ((E (t + 1) + Q t * xh t) / (E t + Q t))) +
      ∑ t ∈ F, δ t + ((A N - B N) - (A 0 - B 0)) =
      ∑ t ∈ F, (Real.log (qh t) - Real.log ((E (t + 1) + Q t * xh t) / (E t + Q t))) +
        ((A N - B N) + ∑ t ∈ F, δ t - (A 0 - B 0)) := by ring
  rw [e, sum_add_distrib]
  linarith

/-- [proved-derived] **`node_face_drift`: one node's face at one arrival.** With the same faces,
`|ln q̂_t − ln q_t| ≤ θ_t + |ln Q_t − ln P_t| + |ln x̂_t − ln x_t|`: the executed face departs from
the ideal by its rounding, the chart's drift at the node and the child's departure
(`Tree.mix_ratio_bound` down the path). -/
theorem node_face_drift {E E' P Q x xh qh θ : ℝ} (hE : 0 ≤ E) (hE' : 0 ≤ E') (hP : 0 < P)
    (hQ : 0 < Q) (hx : 0 < x) (hxh : 0 < xh)
    (hθ : |Real.log qh - Real.log ((E' + Q * xh) / (E + Q))| ≤ θ) :
    |Real.log qh - Real.log ((E' + P * x) / (E + P))| ≤
      θ + |Real.log Q - Real.log P| + |Real.log xh - Real.log x| := by
  have h := face_log_le hE hE' hP hQ hx hxh
  calc |Real.log qh - Real.log ((E' + P * x) / (E + P))|
      = |(Real.log qh - Real.log ((E' + Q * xh) / (E + Q))) +
          (Real.log ((E' + Q * xh) / (E + Q)) - Real.log ((E' + P * x) / (E + P)))| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := by linarith

/-! ### Over the tree -/

section Tree

variable {Ltr : Type*} [Fintype Ltr]

/-- [proved-derived] **`tree_drift`: the drift adds over the subtree.** Let each node `s` (an
address prefix, `|s| ≤ D`) have the arrivals `arr s`, partitioned among its children above the
maximum depth, and let `F d t` be the departure at depth `d` on arrival `t`'s path
(`ln q̂ − ln q`, the executed face against the ideal). When each node's summed departure is at most
its children's summed departure plus its own `cost` (`node_passage_drift`), and a leaf's at most its
own `cost`, then each node's summed departure is at most the costs summed over its arrivals and
the depths from it to `D`: `|Σ_(arr s) F_(|s|)| ≤ Σ_(arr s) Σ_(|s| ≤ d ≤ D) cost_d`. -/
theorem tree_drift (D : ℕ) (arr : List Ltr → Finset ℕ)
    (hpart : ∀ s : List Ltr, s.length < D → ∀ g : ℕ → ℝ,
      ∑ t ∈ arr s, g t = ∑ b, ∑ t ∈ arr (s ++ [b]), g t)
    (F cost : ℕ → ℕ → ℝ)
    (hnode : ∀ s : List Ltr, s.length < D →
      |∑ t ∈ arr s, F s.length t| ≤ |∑ t ∈ arr s, F (s.length + 1) t| +
        ∑ t ∈ arr s, cost s.length t)
    (hleaf : ∀ s : List Ltr, s.length = D → |∑ t ∈ arr s, F D t| ≤ ∑ t ∈ arr s, cost D t) :
    ∀ s : List Ltr, s.length ≤ D →
      |∑ t ∈ arr s, F s.length t| ≤ ∑ t ∈ arr s, ∑ d ∈ Ico s.length (D + 1), cost d t := by
  suffices h : ∀ k (s : List Ltr), s.length + k = D →
      |∑ t ∈ arr s, F s.length t| ≤ ∑ t ∈ arr s, ∑ d ∈ Ico s.length (D + 1), cost d t by
    intro s hs
    exact h (D - s.length) s (by omega)
  intro k
  induction k with
  | zero =>
    intro s hs
    simp only [add_zero] at hs
    subst hs
    simpa [Nat.Ico_succ_singleton] using hleaf s rfl
  | succ k ih =>
    intro s hs
    have hlt : s.length < D := by omega
    have hkids : |∑ t ∈ arr s, F (s.length + 1) t| ≤
        ∑ t ∈ arr s, ∑ d ∈ Ico (s.length + 1) (D + 1), cost d t := by
      rw [hpart s hlt, hpart s hlt]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b _ => ?_)
      have := ih (s ++ [b]) (by simp; omega)
      simpa using this
    have hsplit : ∀ t, ∑ d ∈ Ico s.length (D + 1), cost d t =
        cost s.length t + ∑ d ∈ Ico (s.length + 1) (D + 1), cost d t :=
      fun t => sum_eq_sum_Ico_succ_bot (by omega) _
    simp only [hsplit, sum_add_distrib]
    linarith [hnode s hlt]

/-- [proved-derived] **`tree_drift_below`.** Under the same hypotheses, a node's children's summed
departures over its arrivals are at most the costs summed over its arrivals and the depths below it:
`|Σ_(arr s) F_(|s|+1)| ≤ Σ_(arr s) Σ_(|s| < d ≤ D) cost_d` (`|s| < D`). It bounds the chart's drift
at the node (`split_drift`). -/
theorem tree_drift_below (D : ℕ) (arr : List Ltr → Finset ℕ)
    (hpart : ∀ s : List Ltr, s.length < D → ∀ g : ℕ → ℝ,
      ∑ t ∈ arr s, g t = ∑ b, ∑ t ∈ arr (s ++ [b]), g t)
    (F cost : ℕ → ℕ → ℝ)
    (hnode : ∀ s : List Ltr, s.length < D →
      |∑ t ∈ arr s, F s.length t| ≤ |∑ t ∈ arr s, F (s.length + 1) t| +
        ∑ t ∈ arr s, cost s.length t)
    (hleaf : ∀ s : List Ltr, s.length = D → |∑ t ∈ arr s, F D t| ≤ ∑ t ∈ arr s, cost D t)
    (s : List Ltr) (hs : s.length < D) :
    |∑ t ∈ arr s, F (s.length + 1) t| ≤
      ∑ t ∈ arr s, ∑ d ∈ Ico (s.length + 1) (D + 1), cost d t := by
  rw [hpart s hs, hpart s hs]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b _ => ?_)
  have := tree_drift D arr hpart F cost hnode hleaf (s ++ [b]) (by simp; omega)
  simpa using this

variable [DecidableEq Ltr]

/-- [definition] **The arrivals at a node** among the first `N`: the observations whose address
`a t` begins with the node's prefix `s`. -/
def arrivals (a : ℕ → List Ltr) (N : ℕ) (s : List Ltr) : Finset ℕ :=
  (range N).filter fun t => s <+: a t

omit [Fintype Ltr] [DecidableEq Ltr] in
theorem prefix_concat_iff {s l : List Ltr} {b : Ltr} (hs : s <+: l) (hl : s.length < l.length) :
    s ++ [b] <+: l ↔ l[s.length] = b := by
  rw [List.prefix_iff_eq_take] at hs ⊢
  have htake : l.take (s.length + 1) = l.take s.length ++ [l[s.length]] :=
    (List.take_concat_get' l s.length hl).symm
  simp only [List.length_append, List.length_singleton]
  rw [htake, ← hs]
  constructor
  · intro h
    have := List.append_cancel_left h
    simp only [List.cons.injEq, and_true] at this
    exact this.symm
  · intro h
    rw [h]

/-- [proved-derived] **`arrivals_partition`: every arrival above the maximum depth continues into
exactly one child** (the routing of `Compaction.routed_split`, here on the addresses): when every
address among the first `N` reaches depth `D`, a node above `D` sums over its arrivals as its
children do over theirs. -/
theorem arrivals_partition (a : ℕ → List Ltr) (N D : ℕ) (hD : ∀ t < N, D ≤ (a t).length)
    (s : List Ltr) (hs : s.length < D) (g : ℕ → ℝ) :
    ∑ t ∈ arrivals a N s, g t = ∑ b, ∑ t ∈ arrivals a N (s ++ [b]), g t := by
  simp only [arrivals, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun t ht => ?_
  have hl : s.length < (a t).length := lt_of_lt_of_le hs (hD t (mem_range.1 ht))
  by_cases h : s <+: a t
  · rw [if_pos h]
    simp_rw [prefix_concat_iff h hl]
    rw [sum_ite_eq]
    simp
  · rw [if_neg h]
    refine (sum_eq_zero fun (b : Ltr) _ => ?_).symm
    rw [if_neg]
    exact fun hb => h ((List.prefix_append s [b]).trans hb)

end Tree

/-! ### The executed tree over the passage -/

/-- [definition] **An executed digit tree beside its ideal tree.** The observations' addresses `a t`
reach the maximum depth `D` (padded with the boundary letter); the observation `t` arrives at the
node `s` when `s <+: a t`, and the node's child on its path is `(a t).take (|s| + 1)`. At each node:
* `E ≥ 0` its own weight (the stop weight times its own mass, `0` at a forced depth), stepping only
  at its arrivals;
* `P > 0` the ideal split mass, the product of its children's ideal faces over its arrivals, and
  `q` the ideal face, the weight ratio `(E' + P x)/(E + P)` above `D`
  (`Tree.lattice_node_telescope`; at `D` the leaf's own face);
* `Q > 0` the executed split mass, the chart's `β̂ = E/Q` (`face_weight_form`), stepping by the
  child's executed face and a positive factor `c` (a mantissa rebase `x/m`, `Tree.rebase_log_residual`;
  a carrier rebase; a stored chain's split), founded where the ideal is (`β₀ = 2^j − 1` exactly,
  `Tree.ladder_founding`);
* `q̂` the executed face, within `θ` in `ln` of the executed mixture `(E' + Q x̂)/(E + Q)` (the
  stop weight's and the face's rounding on the lattice), and at `D` within `θ` of the leaf's face. -/
structure ExecutedTree (Ltr : Type*) [DecidableEq Ltr] (D : ℕ) where
  a : ℕ → List Ltr
  E : List Ltr → ℕ → ℝ
  P : List Ltr → ℕ → ℝ
  Q : List Ltr → ℕ → ℝ
  c : List Ltr → ℕ → ℝ
  θ : List Ltr → ℕ → ℝ
  q : List Ltr → ℕ → ℝ
  qh : List Ltr → ℕ → ℝ
  reach : ∀ t, D ≤ (a t).length
  E_nonneg : ∀ s t, 0 ≤ E s t
  P_pos : ∀ s t, 0 < P s t
  Q_pos : ∀ s t, 0 < Q s t
  q_pos : ∀ s t, s <+: a t → 0 < q s t
  qh_pos : ∀ s t, s <+: a t → 0 < qh s t
  c_pos : ∀ s t, s <+: a t → 0 < c s t
  E_stay : ∀ s t, ¬ s <+: a t → E s (t + 1) = E s t
  P_step : ∀ s t, s.length < D →
    P s (t + 1) = if s <+: a t then P s t * q ((a t).take (s.length + 1)) t else P s t
  Q_step : ∀ s t, s.length < D →
    Q s (t + 1) = if s <+: a t then Q s t * qh ((a t).take (s.length + 1)) t * c s t else Q s t
  founding : ∀ s, Q s 0 = P s 0
  ideal : ∀ s t, s.length < D → s <+: a t →
    q s t = (E s (t + 1) + P s t * q ((a t).take (s.length + 1)) t) / (E s t + P s t)
  rounding : ∀ s t, s.length < D → s <+: a t →
    |Real.log (qh s t) - Real.log ((E s (t + 1) + Q s t * qh ((a t).take (s.length + 1)) t) /
      (E s t + Q s t))| ≤ θ s t
  leaf : ∀ s t, s.length = D → s <+: a t → |Real.log (qh s t) - Real.log (q s t)| ≤ θ s t

namespace ExecutedTree

variable {Ltr : Type*} [Fintype Ltr] [DecidableEq Ltr] {D : ℕ} (T : ExecutedTree Ltr D)

/-- [definition] The departure at depth `d` on arrival `t`'s path, `ln q̂ − ln q`. -/
noncomputable def F (d t : ℕ) : ℝ := Real.log (T.qh ((T.a t).take d) t) - Real.log (T.q ((T.a t).take d) t)

/-- [definition] **A level's cost on arrival `t`'s path**: its rounding, and above `D` its factor,
`θ_d + |ln c_d|`. -/
noncomputable def cost (d t : ℕ) : ℝ :=
  T.θ ((T.a t).take d) t + if d < D then |Real.log (T.c ((T.a t).take d) t)| else 0

omit [Fintype Ltr] in
theorem take_of_mem {N : ℕ} {s : List Ltr} {t : ℕ} (ht : t ∈ arrivals T.a N s) :
    (T.a t).take s.length = s :=
  (List.prefix_iff_eq_take.1 (mem_filter.1 ht).2).symm

omit [Fintype Ltr] in
theorem child_prefix (s : List Ltr) (t : ℕ) : (T.a t).take (s.length + 1) <+: T.a t :=
  List.take_prefix _ _

omit [Fintype Ltr] in
/-- [proved-derived] **Each node's summed departure** is at most its children's plus its own cost
(`node_passage_drift`, the founding exact). -/
theorem node_bound (N : ℕ) (s : List Ltr) (hs : s.length < D) :
    |∑ t ∈ arrivals T.a N s, T.F s.length t| ≤
      |∑ t ∈ arrivals T.a N s, T.F (s.length + 1) t| +
        ∑ t ∈ arrivals T.a N s, T.cost s.length t := by
  have h := node_passage_drift (T.E s) (T.P s) (T.Q s)
    (fun t => T.q ((T.a t).take (s.length + 1)) t) (fun t => T.qh ((T.a t).take (s.length + 1)) t)
    (T.c s) (T.θ s) (T.qh s) (fun t => s <+: T.a t) (T.E_nonneg s) (T.P_pos s) (T.Q_pos s)
    (fun t _ => T.q_pos _ t (T.child_prefix s t)) (fun t _ => T.qh_pos _ t (T.child_prefix s t))
    (fun t h => T.c_pos s t h) (fun t h => T.E_stay s t h) (fun t => T.P_step s t hs)
    (fun t => T.Q_step s t hs) (fun t h => T.rounding s t hs h) N
  rw [T.founding s, sub_self, abs_zero, mul_zero, add_zero] at h
  have e1 : ∑ t ∈ arrivals T.a N s, T.F s.length t =
      ∑ t ∈ (range N).filter (fun t => s <+: T.a t), (Real.log (T.qh s t) -
        Real.log ((T.E s (t + 1) + T.P s t * T.q ((T.a t).take (s.length + 1)) t) /
          (T.E s t + T.P s t))) := by
    refine sum_congr rfl fun t ht => ?_
    rw [F, T.take_of_mem ht, ← T.ideal s t hs (mem_filter.1 ht).2]
  have e2 : ∑ t ∈ arrivals T.a N s, T.cost s.length t =
      ∑ t ∈ (range N).filter (fun t => s <+: T.a t),
        (T.θ s t + |Real.log (T.c s t)|) := by
    refine sum_congr rfl fun t ht => ?_
    rw [cost, T.take_of_mem ht, if_pos hs]
  rw [e1, e2]
  exact h

omit [Fintype Ltr] in
/-- A leaf's summed departure is at most its roundings. -/
theorem leaf_bound (N : ℕ) (s : List Ltr) (hs : s.length = D) :
    |∑ t ∈ arrivals T.a N s, T.F D t| ≤ ∑ t ∈ arrivals T.a N s, T.cost D t := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t ht => ?_)
  have hk := T.take_of_mem ht
  rw [hs] at hk
  rw [F, cost, hk, if_neg (lt_irrefl D), add_zero]
  exact T.leaf s t hs (mem_filter.1 ht).2

/-- [proved-derived] **`passage_drift`: the executed code against the ideal code over the
passage.** Over the first `N` observations the executed tree's code differs from the ideal tree's
by at most each observation's costs summed down its path:
`|Σ_(t<N) (ln q̂_t − ln q_t)| ≤ Σ_(t<N) Σ_(d ≤ D) (θ_d + |ln c_d|)` (no `c` at `D`). The drift is the
rounding and the factors summed over the passage once, never compounded: each reading pays its
path's `D + 1` roundings and `D` factors, whatever the passage's length. -/
theorem passage_drift (N : ℕ) :
    |∑ t ∈ range N, (Real.log (T.qh [] t) - Real.log (T.q [] t))| ≤
      ∑ t ∈ range N, ∑ d ∈ range (D + 1), T.cost d t := by
  have h := tree_drift D (arrivals T.a N)
    (fun s hs g => arrivals_partition T.a N D (fun t _ => T.reach t) s hs g) T.F T.cost
    (T.node_bound N) (T.leaf_bound N) [] (Nat.zero_le _)
  have hr : arrivals T.a N [] = range N := filter_true_of_mem fun t _ => List.nil_prefix
  simp only [hr, List.length_nil, F, List.take_zero, ← range_eq_Ico] at h
  exact h

/-- [proved-derived] **`cell_drift`: one cell's executed face against its ideal face.** At the
observation `t₀`, with `s_d` its path's node at depth `d`,
`|ln q̂_t₀ − ln q_t₀| ≤ Σ_(d ≤ D) θ_(s_d) + Σ_(d < D) Σ_(t ∈ arr_(t₀)(s_d)) (|ln c_(s_d)| + Σ_(d < d' ≤ D) cost_(d'))`
over the earlier arrivals at each node: the chart's drift at `s_d` is its earlier arrivals' costs
below it (`split_drift`, `tree_drift_below`), added down the path with the roundings
(`node_face_drift`). This is the per-cell rule's composition (Rust `Landmarks::face_rule`). -/
theorem cell_drift (t₀ : ℕ) :
    |Real.log (T.qh [] t₀) - Real.log (T.q [] t₀)| ≤
      ∑ d ∈ range (D + 1), T.θ ((T.a t₀).take d) t₀ +
        ∑ d ∈ range D, ∑ t ∈ arrivals T.a t₀ ((T.a t₀).take d),
          (|Real.log (T.c ((T.a t₀).take d) t)| + ∑ d' ∈ Ico (d + 1) (D + 1), T.cost d' t) := by
  set Δ : ℕ → ℝ := fun d => ∑ t ∈ arrivals T.a t₀ ((T.a t₀).take d),
    (|Real.log (T.c ((T.a t₀).take d) t)| + ∑ d' ∈ Ico (d + 1) (D + 1), T.cost d' t) with hΔ
  have hlen : ∀ d, d ≤ D → ((T.a t₀).take d).length = d := fun d hd =>
    List.length_take_of_le (hd.trans (T.reach t₀))
  -- the chart's drift at the node on the path at depth d < D
  have hdrift : ∀ d, d < D → |Real.log (T.Q ((T.a t₀).take d) t₀) -
      Real.log (T.P ((T.a t₀).take d) t₀)| ≤ Δ d := by
    intro d hd
    set s := (T.a t₀).take d with hsdef
    have hs : s.length = d := hlen d hd.le
    have hsD : s.length < D := hs ▸ hd
    have hsplit := split_drift (T.P s) (T.Q s)
      (fun t => T.q ((T.a t).take (s.length + 1)) t) (fun t => T.qh ((T.a t).take (s.length + 1)) t)
      (T.c s) (fun t => s <+: T.a t) (T.P_pos s) (T.Q_pos s)
      (fun t _ => T.q_pos _ t (T.child_prefix s t)) (fun t _ => T.qh_pos _ t (T.child_prefix s t))
      (fun t h => T.c_pos s t h) (fun t => T.P_step s t hsD) (fun t => T.Q_step s t hsD) t₀
    rw [T.founding s, sub_self, zero_add, sum_add_distrib] at hsplit
    have hbelow := tree_drift_below D (arrivals T.a t₀)
      (fun s hs g => arrivals_partition T.a t₀ D (fun t _ => T.reach t) s hs g) T.F T.cost
      (T.node_bound t₀) (T.leaf_bound t₀) s hsD
    have eF : ∑ t ∈ arrivals T.a t₀ s, T.F (s.length + 1) t =
        ∑ t ∈ (range t₀).filter (fun t => s <+: T.a t),
          (Real.log (T.qh ((T.a t).take (s.length + 1)) t) -
            Real.log (T.q ((T.a t).take (s.length + 1)) t)) := rfl
    rw [hsplit, hΔ]
    simp only [hs] at hbelow eF
    rw [eF] at hbelow
    simp only [sum_add_distrib]
    refine (abs_add_le _ _).trans ?_
    have := abs_sum_le_sum_abs (fun t => Real.log (T.c s t)) ((range t₀).filter fun t => s <+: T.a t)
    unfold arrivals at hbelow ⊢
    simp only [hs] at *
    linarith
  -- down the path
  have hpath : ∀ k d, d + k = D →
      |Real.log (T.qh ((T.a t₀).take d) t₀) - Real.log (T.q ((T.a t₀).take d) t₀)| ≤
        ∑ d' ∈ Ico d (D + 1), T.θ ((T.a t₀).take d') t₀ + ∑ d' ∈ Ico d D, Δ d' := by
    intro k
    induction k with
    | zero =>
      intro d hd
      simp only [add_zero] at hd
      subst hd
      simp only [Nat.Ico_succ_singleton, sum_singleton, Ico_self, sum_empty, add_zero]
      exact T.leaf _ t₀ (hlen d le_rfl) (List.take_prefix _ _)
    | succ k ih =>
      intro d hd
      have hdD : d < D := by omega
      set s := (T.a t₀).take d with hsdef
      have hs : s.length = d := hlen d hdD.le
      have hsD : s.length < D := hs ▸ hdD
      have hpre : s <+: T.a t₀ := List.take_prefix _ _
      have hchild : (T.a t₀).take (s.length + 1) = (T.a t₀).take (d + 1) := by rw [hs]
      have hface := node_face_drift (T.E_nonneg s t₀) (T.E_nonneg s (t₀ + 1)) (T.P_pos s t₀)
        (T.Q_pos s t₀) (T.q_pos _ t₀ (T.child_prefix s t₀)) (T.qh_pos _ t₀ (T.child_prefix s t₀))
        (T.rounding s t₀ hsD hpre)
      rw [← T.ideal s t₀ hsD hpre, hchild] at hface
      have hrest := ih (d + 1) (by omega)
      rw [sum_eq_sum_Ico_succ_bot (by omega : d < D + 1), sum_eq_sum_Ico_succ_bot hdD]
      linarith [hdrift d hdD]
  have h := hpath D 0 (by omega)
  simp only [List.take_zero, ← range_eq_Ico] at h
  exact h

/-- `Σ_(d < D) (2(D − d) − 1) = D²`: the levels below each node of a path, summed. -/
theorem sum_levels_below (D : ℕ) : ∑ d ∈ range D, (2 * ((D : ℝ) - d) - 1) = (D : ℝ) ^ 2 := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [sum_range_succ]
    have e : ∑ d ∈ range D, (2 * (((D + 1 : ℕ) : ℝ) - d) - 1) =
        ∑ d ∈ range D, (2 * ((D : ℝ) - d) - 1) + ∑ _d ∈ range D, (2 : ℝ) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun d _ => ?_
      push_cast
      ring
    rw [e, ih, sum_const, card_range, nsmul_eq_mul]
    push_cast
    ring

/-- [proved-derived] **`passage_drift_uniform`.** With every internal rounding at most `2u`, every
leaf rounding at most `u` and every factor within `ρ` in `ln`, the executed code over `N`
observations is within `N((2D + 1)u + Dρ)` of the ideal code: per reading `(2D + 1)u + Dρ`,
independent of the passage's length. In the Rust's units `u = ε/μ̂ = 2^(−M_p−1)/μ̂` and
`ρ = 2^(1−W) + ρ_c` a factor's share. -/
theorem passage_drift_uniform {u ρ : ℝ}
    (hθ : ∀ s t, s.length < D → s <+: T.a t → T.θ s t ≤ 2 * u)
    (hθD : ∀ s t, s.length = D → s <+: T.a t → T.θ s t ≤ u)
    (hc : ∀ s t, s.length < D → s <+: T.a t → |Real.log (T.c s t)| ≤ ρ) (N : ℕ) :
    |∑ t ∈ range N, (Real.log (T.qh [] t) - Real.log (T.q [] t))| ≤
      N * ((2 * D + 1) * u + D * ρ) := by
  refine (T.passage_drift N).trans ?_
  have hlen : ∀ t d, d ≤ D → ((T.a t).take d).length = d := fun t d hd =>
    List.length_take_of_le (hd.trans (T.reach t))
  have hrow : ∀ t, ∑ d ∈ range (D + 1), T.cost d t ≤ (2 * D + 1) * u + D * ρ := by
    intro t
    rw [sum_range_succ]
    have hlast : T.cost D t ≤ u := by
      rw [cost, if_neg (lt_irrefl D), add_zero]
      exact hθD _ t (hlen t D le_rfl) (List.take_prefix _ _)
    have hbody : ∑ d ∈ range D, T.cost d t ≤ ∑ _d ∈ range D, (2 * u + ρ) := by
      refine sum_le_sum fun d hd => ?_
      have hdD := mem_range.1 hd
      rw [cost, if_pos hdD]
      have h1 := hθ _ t (by rw [hlen t d hdD.le]; exact hdD) (List.take_prefix _ _)
      have h2 := hc _ t (by rw [hlen t d hdD.le]; exact hdD) (List.take_prefix _ _)
      linarith
    rw [sum_const, card_range, nsmul_eq_mul] at hbody
    nlinarith
  calc ∑ t ∈ range N, ∑ d ∈ range (D + 1), T.cost d t
      ≤ ∑ _t ∈ range N, ((2 * D + 1) * u + D * ρ) := sum_le_sum fun t _ => hrow t
    _ = N * ((2 * D + 1) * u + D * ρ) := by rw [sum_const, card_range, nsmul_eq_mul]

/-- [proved-derived] **`cell_drift_uniform`: the per-cell rule.** Under the same bounds, with
`u, ρ ≥ 0`, the cell read at observation `t₀` is within `t₀ D² (u + ρ) + (2D + 1)u` of its ideal
face in `ln`: the node at depth `d` carries at most `t₀` earlier arrivals, each with
`2(D − d) − 1` units `u + ρ` below it, and `Σ_(d<D) (2(D − d) − 1) = D²`. At `t₀ ≤ n*` and the
path depth `P = D` (one branch; `P ≥ D` with the bundle branch) this is the Rust rule's `(n* P² + 2P + 1) ε/μ̂ + n* P² ρ` before the digits `B`
and `log₂ e < 3/2` (`Landmarks::face_rule`). -/
theorem cell_drift_uniform {u ρ : ℝ} (hu : 0 ≤ u) (hρ : 0 ≤ ρ)
    (hθ : ∀ s t, s.length < D → s <+: T.a t → T.θ s t ≤ 2 * u)
    (hθD : ∀ s t, s.length = D → s <+: T.a t → T.θ s t ≤ u)
    (hc : ∀ s t, s.length < D → s <+: T.a t → |Real.log (T.c s t)| ≤ ρ) (t₀ : ℕ) :
    |Real.log (T.qh [] t₀) - Real.log (T.q [] t₀)| ≤
      t₀ * (D : ℝ) ^ 2 * (u + ρ) + (2 * D + 1) * u := by
  refine (T.cell_drift t₀).trans ?_
  have hlen : ∀ t d, d ≤ D → ((T.a t).take d).length = d := fun t d hd =>
    List.length_take_of_le (hd.trans (T.reach t))
  have hcost : ∀ t d, d < D → T.cost d t ≤ 2 * u + ρ := by
    intro t d hdD
    rw [cost, if_pos hdD]
    have h1 := hθ _ t (by rw [hlen t d hdD.le]; exact hdD) (List.take_prefix _ _)
    have h2 := hc _ t (by rw [hlen t d hdD.le]; exact hdD) (List.take_prefix _ _)
    linarith
  have hcostD : ∀ t, T.cost D t ≤ u := by
    intro t
    rw [cost, if_neg (lt_irrefl D), add_zero]
    exact hθD _ t (hlen t D le_rfl) (List.take_prefix _ _)
  -- the roundings down the path
  have hθs : ∑ d ∈ range (D + 1), T.θ ((T.a t₀).take d) t₀ ≤ (2 * D + 1) * u := by
    rw [sum_range_succ]
    have hb : ∑ d ∈ range D, T.θ ((T.a t₀).take d) t₀ ≤ ∑ _d ∈ range D, 2 * u :=
      sum_le_sum fun d hd => hθ _ t₀ (by rw [hlen t₀ d (mem_range.1 hd).le]; exact mem_range.1 hd)
        (List.take_prefix _ _)
    rw [sum_const, card_range, nsmul_eq_mul] at hb
    have := hθD _ t₀ (hlen t₀ D le_rfl) (List.take_prefix _ _)
    nlinarith
  -- one arrival's charge at the node at depth d
  have harr : ∀ d, d < D → ∀ t ∈ arrivals T.a t₀ ((T.a t₀).take d),
      |Real.log (T.c ((T.a t₀).take d) t)| + ∑ d' ∈ Ico (d + 1) (D + 1), T.cost d' t ≤
        (2 * ((D : ℝ) - d) - 1) * (u + ρ) := by
    intro d hdD t ht
    have hpre : (T.a t₀).take d <+: T.a t := (mem_filter.1 ht).2
    have h1 := hc _ t (by rw [hlen t₀ d hdD.le]; exact hdD) hpre
    rw [sum_Ico_succ_top (by omega : d + 1 ≤ D)]
    have hb : ∑ d' ∈ Ico (d + 1) D, T.cost d' t ≤ ∑ _d' ∈ Ico (d + 1) D, (2 * u + ρ) :=
      sum_le_sum fun d' hd' => hcost t d' (mem_Ico.1 hd').2
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul] at hb
    have hcast : ((D - (d + 1) : ℕ) : ℝ) = (D : ℝ) - d - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast] at hb
    have := hcostD t
    nlinarith
  have hΔ : ∀ d ∈ range D, ∑ t ∈ arrivals T.a t₀ ((T.a t₀).take d),
      (|Real.log (T.c ((T.a t₀).take d) t)| + ∑ d' ∈ Ico (d + 1) (D + 1), T.cost d' t) ≤
        t₀ * ((2 * ((D : ℝ) - d) - 1) * (u + ρ)) := by
    intro d hd
    have hdD := mem_range.1 hd
    have hnn : 0 ≤ (2 * ((D : ℝ) - d) - 1) * (u + ρ) := by
      have : (d : ℝ) + 1 ≤ D := by exact_mod_cast hdD
      nlinarith
    calc _ ≤ ∑ _t ∈ arrivals T.a t₀ ((T.a t₀).take d), (2 * ((D : ℝ) - d) - 1) * (u + ρ) :=
          sum_le_sum (harr d hdD)
      _ = (arrivals T.a t₀ ((T.a t₀).take d)).card * ((2 * ((D : ℝ) - d) - 1) * (u + ρ)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ t₀ * ((2 * ((D : ℝ) - d) - 1) * (u + ρ)) := by
          refine mul_le_mul_of_nonneg_right ?_ hnn
          have : (arrivals T.a t₀ ((T.a t₀).take d)).card ≤ t₀ :=
            (card_filter_le _ _).trans (card_range t₀).le
          exact_mod_cast this
  have hsum := sum_le_sum hΔ
  rw [← mul_sum, ← sum_mul, sum_levels_below] at hsum
  nlinarith

end ExecutedTree

/-! ### Audit -/

section Audit

#print axioms log_add_mono
#print axioms log_add_le
#print axioms log_add_between
#print axioms face_log_le
#print axioms face_weight_form
#print axioms filter_telescope
#print axioms split_drift
#print axioms node_passage_drift
#print axioms node_face_drift
#print axioms tree_drift
#print axioms tree_drift_below
#print axioms prefix_concat_iff
#print axioms arrivals_partition
#print axioms ExecutedTree.node_bound
#print axioms ExecutedTree.leaf_bound
#print axioms ExecutedTree.passage_drift
#print axioms ExecutedTree.cell_drift
#print axioms ExecutedTree.sum_levels_below
#print axioms ExecutedTree.passage_drift_uniform
#print axioms ExecutedTree.cell_drift_uniform

end Audit

end Holonics.Compression.Landmark.Context.Drift
