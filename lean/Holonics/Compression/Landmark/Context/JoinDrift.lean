import Holonics.Compression.Landmark.Context.Drift

/-!
# Compression.Landmark.Context.JoinDrift: the executed join's drift

[definition; agent-inferred] The executed join's drift (#62, "the executed join's drift"; rebuild
step 4, #73). With the bundle branch declared, each dyadic cell's digit is read by two executed
trees, the cell branch's and the bundle branch's, and joined in an enlarged tree: one join per
dyadic cell (`Standing::join`, not the digit trees' `JoinTree`) carries the ratio `β̂` of the two
branches' executed weights and mixes their root faces (`Context/LocalWeighing`'s two-face mixture,
`forward_executed`'s executed chart). Unlike a tree
node, the join's two sides are both executed, so its drift moves with both branches' drifts. The
computational object is the helical pair interaction; this owner is the receiving parametron's
join of two landmark trees. Of the winding guide's six general objects it touches **faces and
placement** (the join's executed face against the ideal mixture) and the **pair** (`β̂`, the two
branches' weights compared as an undivided ratio and carried exactly); the helix, the cell
holonomy, the tube and the tower thread stay attached, unchanged.

The object, at the join's arrivals `t` (every digit at its dyadic cell), with `W_c`, `W_b` the two
branch roots' ideal weights (the prior folded into their founding), `x_c`, `x_b` their ideal faces
at the digit's symbol and `x̂_c`, `x̂_b` their executed faces:

```text
ideal      β_t = W_c(t)/W_b(t) ,  W_c(t + 1) = W_c(t) x_c(t) ,  W_b(t + 1) = W_b(t) x_b(t)
           q_t = (β_t x_c + x_b)/(1 + β_t) = (W_c(t + 1) + W_b(t + 1))/(W_c(t) + W_b(t))
executed   β̂_(t+1) = β̂_t (x̂_c/x̂_b) c_t ,  β̂_0 = β_0 ,  q̂_t within θ_t in ln of (β̂_t x̂_c + x̂_b)/(1 + β̂_t)
one face   |ln q̂ − ln q| ≤ θ + |ln β̂ − ln β| + |ln x̂_c − ln x_c| + |ln x̂_b − ln x_b|
ratio      ln β̂_N − ln β_N = Σ (ln x̂_c − ln x_c) − Σ (ln x̂_b − ln x_b) + Σ ln c
passage    |Σ_(t<N) (ln q̂_t − ln q_t)| ≤ |Σ (ln x̂_c − ln x_c)| + |Σ (ln x̂_b − ln x_b)| + Σ (θ + 2|ln c|)
```

[proved-derived; formal-checked] What is proved.
- `mix_log_le`: a sum's logarithm moves by at most its two terms' log moves.
- `join_face_drift`, `join_read_drift`: one digit's joined face departs from the ideal mixture by
  its rounding, the join's ratio drift and the two branches' face drifts.
- `log_step_sum`, `join_ratio`, `join_ratio_drift`: the carried ratio's drift is the cell branch's
  summed drift minus the bundle branch's plus the rebases, each counted once.
- `join_passage`: over the passage the join's executed code is within the two branches' passage
  drifts plus, at each arrival, its rounding and twice its rebase. The executed join reads the
  weight `Â = Ŵ_c (1 + 1/β̂)`: a rebase `c` makes the face depart from `Â`'s step by at most
  `|ln c|` (the weight's own read jump), and the final `Â` departs from the ideal `W_c + W_b` by
  the two branches' drifts and the summed `|ln c|` once more.

[conditional] **What the theorems cover in the Rust.** In an enlarged tree (`Law::joined`) the
deposit (`Law::apply`) steps each join by `carried_step(β̂, side_c, 1, side_b, 0)`: `β̂' = β̂
(x̂_c/x̂_b) c`, the sides being the two branch roots' executed faces at the digit's symbol on one
lattice, so `x̂_c/x̂_b` is their ratio exactly. It adds the branches' increments and the rebase
units to the join's `drift`, which is `join_ratio_drift` (each branch root's increments sum to at
least its passage drift, `Drift.ExecutedTree.passage_drift` and `StoredDrift.stored_passage`), and
`θ + 2·units +` the increments to the join's `excess`, which is `join_passage` term for term: the
doubled rebase units are what the proof charges, not a conservative margin. One digit's certificate
(`Law::digit_certificate`) is the two branches' certificates plus the join's `drift` and its
rounding (`Law::join_rounding`), which is `join_read_drift`. The rebase units bound `|ln c|` as at
a node (`Tree.rebase_log_residual`, `Carrier`). The ideal side is the oracle's: the two branches'
ideal root weights at prior one half each, so `β_0 = 1`, which every join of an enlarged tree is
founded at exactly (`Standing::join`). The join's rounding `θ_h = 2^(−M)/min(q̂_h, q̂_c, q̂_b)`
(`Law::join_rounding`) is the lattice blend's, as at a node. The digit trees' joins
(`FaceJoins::receive`) keep the same accounting at every join of a `JoinTree`, founded at its
`β₀`; a side that is itself a join reads its face and its excess increment in place of a branch
root's, so the theorems apply join by join up the tree.

[proved-standard] Mixing two sequential codes by their running weights is the two-expert Bayesian
mixture (`LocalWeighing.static_mixture`); the bounds here are this owner's.

| Claim | Lean | Rust |
|---|---|---|
| one digit's joined face | `mix_log_le`, `join_face_drift`, `join_read_drift` | `Law::join_face`, `Law::join_rounding`, `Law::digit_certificate` |
| the carried ratio's drift | `log_step_sum`, `join_ratio`, `join_ratio_drift` | `Law::apply` (the join's `drift`) |
| the join's code over its passage | `join_passage` | `Law::apply` (the join's `excess`), `FaceJoins::receive` |
-/

namespace Holonics.Compression.Landmark.Context.JoinDrift

open Finset Drift

/-! ### One digit -/

/-- [proved-derived] **`mix_log_le`: a sum's logarithm moves by at most its terms' moves.** For
positive `a, b, a', b'`, `|ln(a' + b') − ln(a + b)| ≤ |ln a' − ln a| + |ln b' − ln b|`. -/
theorem mix_log_le {a b a' b' : ℝ} (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b') :
    |Real.log (a' + b') - Real.log (a + b)| ≤
      |Real.log a' - Real.log a| + |Real.log b' - Real.log b| := by
  have h1 := log_add_le hb'.le ha' ha
  have h2 := log_add_le ha.le hb' hb
  rw [add_comm b' a', add_comm b' a] at h1
  calc |Real.log (a' + b') - Real.log (a + b)|
      = |(Real.log (a' + b') - Real.log (a + b')) + (Real.log (a + b') - Real.log (a + b))| := by
        ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

/-- [proved-derived] **`join_face_drift`: the joined face moves by at most its three inputs'
drifts.** The mixture `(β k + x)/(1 + β)` of the cell face `k` and the bundle face `x` at the ratio
`β` moves by at most `|ln β̂ − ln β| + |ln k̂ − ln k| + |ln x̂ − ln x|` in `ln`: `face_log_le` at the
own weight `1`, the split mass `1/β` and the face `x`, then `log_add_le` for `k`. -/
theorem join_face_drift {β βh k kh x xh : ℝ} (hβ : 0 < β) (hβh : 0 < βh) (hk : 0 < k)
    (hkh : 0 < kh) (hx : 0 < x) (hxh : 0 < xh) :
    |Real.log ((βh * kh + xh) / (1 + βh)) - Real.log ((β * k + x) / (1 + β))| ≤
      |Real.log βh - Real.log β| + |Real.log kh - Real.log k| + |Real.log xh - Real.log x| := by
  have form : ∀ {b y z : ℝ}, 0 < b → (b * y + z) / (1 + b) = (y + b⁻¹ * z) / (1 + b⁻¹) := by
    intro b y z hb
    field_simp
    ring
  have hβi : 0 < β⁻¹ := inv_pos.2 hβ
  have hβhi : 0 < βh⁻¹ := inv_pos.2 hβh
  have h1 := face_log_le zero_le_one hkh.le hβi hβhi hx hxh
  rw [← form hβh, ← form hβ, Real.log_inv, Real.log_inv, neg_sub_neg, abs_sub_comm (Real.log β)]
    at h1
  have h2 : |Real.log ((β * kh + x) / (1 + β)) - Real.log ((β * k + x) / (1 + β))| ≤
      |Real.log kh - Real.log k| := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      sub_sub_sub_cancel_right, add_comm (β * kh), add_comm (β * k)]
    have := log_add_le hx.le (mul_pos hβ hkh) (mul_pos hβ hk)
    rwa [Real.log_mul hβ.ne' hkh.ne', Real.log_mul hβ.ne' hk.ne', add_sub_add_left_eq_sub] at this
  calc |Real.log ((βh * kh + xh) / (1 + βh)) - Real.log ((β * k + x) / (1 + β))|
      = |(Real.log ((βh * kh + xh) / (1 + βh)) - Real.log ((β * kh + x) / (1 + β))) +
          (Real.log ((β * kh + x) / (1 + β)) - Real.log ((β * k + x) / (1 + β)))| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := by linarith

/-- [proved-derived] **`join_read_drift`: one digit's executed joined face.** A face `q̂` within
`θ` in `ln` of the executed mixture is within `θ + |ln β̂ − ln β| + |ln k̂ − ln k| + |ln x̂ − ln x|`
of the ideal mixture: the digit's certificate is the two branches' certificates, the join's drift
and its rounding (`Law::digit_certificate`). -/
theorem join_read_drift {β βh k kh x xh qh θ : ℝ} (hβ : 0 < β) (hβh : 0 < βh) (hk : 0 < k)
    (hkh : 0 < kh) (hx : 0 < x) (hxh : 0 < xh)
    (hθ : |Real.log qh - Real.log ((βh * kh + xh) / (1 + βh))| ≤ θ) :
    |Real.log qh - Real.log ((β * k + x) / (1 + β))| ≤
      θ + |Real.log βh - Real.log β| + |Real.log kh - Real.log k| +
        |Real.log xh - Real.log x| := by
  have h := join_face_drift hβ hβh hk hkh hx hxh
  calc |Real.log qh - Real.log ((β * k + x) / (1 + β))|
      = |(Real.log qh - Real.log ((βh * kh + xh) / (1 + βh))) +
          (Real.log ((βh * kh + xh) / (1 + βh)) - Real.log ((β * k + x) / (1 + β)))| := by
        ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := by linarith

/-! ### The carried ratio -/

/-- [proved-derived] **`log_step_sum`.** A positive quantity stepped by positive factors has the
logarithm of its founding plus the factors' logarithms: `ln f_N = ln f_0 + Σ_(t<N) ln r_t`. -/
theorem log_step_sum (f r : ℕ → ℝ) (hf : ∀ t, 0 < f t) (hr : ∀ t, 0 < r t)
    (hs : ∀ t, f (t + 1) = f t * r t) (N : ℕ) :
    Real.log (f N) = Real.log (f 0) + ∑ t ∈ range N, Real.log (r t) := by
  induction N with
  | zero => simp
  | succ n ih => rw [hs n, Real.log_mul (hf n).ne' (hr n).ne', ih, sum_range_succ]; ring

/-- [proved-derived] **`join_ratio`: the carried ratio against the ideal one.** With the ideal
ratio `β = W_c/W_b` of the two branches' weights stepping by their faces, and the carried `β̂`
stepping by the executed faces' ratio and a rebase `c` from `β̂_0 = β_0`,
`ln β̂_N − ln β_N = Σ (ln x̂_c − ln x_c) − Σ (ln x̂_b − ln x_b) + Σ ln c`. -/
theorem join_ratio (Wc Wb xc xb xch xbh βh c : ℕ → ℝ) (hWc : ∀ t, 0 < Wc t)
    (hWb : ∀ t, 0 < Wb t) (hxc : ∀ t, 0 < xc t) (hxb : ∀ t, 0 < xb t) (hxch : ∀ t, 0 < xch t)
    (hxbh : ∀ t, 0 < xbh t) (hβh : ∀ t, 0 < βh t) (hc : ∀ t, 0 < c t)
    (hWcs : ∀ t, Wc (t + 1) = Wc t * xc t) (hWbs : ∀ t, Wb (t + 1) = Wb t * xb t)
    (hβhs : ∀ t, βh (t + 1) = βh t * (xch t / xbh t * c t)) (h0 : βh 0 = Wc 0 / Wb 0) (N : ℕ) :
    Real.log (βh N) - Real.log (Wc N / Wb N) =
      ∑ t ∈ range N, (Real.log (xch t) - Real.log (xc t)) -
        ∑ t ∈ range N, (Real.log (xbh t) - Real.log (xb t)) + ∑ t ∈ range N, Real.log (c t) := by
  have hr : ∀ t, 0 < xch t / xbh t * c t := fun t => by
    have := hxch t; have := hxbh t; have := hc t; positivity
  rw [log_step_sum βh _ hβh hr hβhs, Real.log_div (hWc N).ne' (hWb N).ne',
    log_step_sum Wc xc hWc hxc hWcs, log_step_sum Wb xb hWb hxb hWbs, h0,
    Real.log_div (hWc 0).ne' (hWb 0).ne']
  have e : ∀ t ∈ range N, Real.log (xch t / xbh t * c t) =
      Real.log (xch t) - Real.log (xbh t) + Real.log (c t) := fun t _ => by
    rw [Real.log_mul (div_pos (hxch t) (hxbh t)).ne' (hc t).ne',
      Real.log_div (hxch t).ne' (hxbh t).ne']
  rw [sum_congr rfl e, sum_add_distrib, sum_sub_distrib, sum_sub_distrib, sum_sub_distrib]
  ring

/-- [proved-derived] **`join_ratio_drift`: the join chart's drift.**
`|ln β̂_N − ln β_N| ≤ |Σ (ln x̂_c − ln x_c)| + |Σ (ln x̂_b − ln x_b)| + Σ |ln c|`: the join's `drift`
adds both branches' increments and the rebase units (`Law::apply`). -/
theorem join_ratio_drift (Wc Wb xc xb xch xbh βh c : ℕ → ℝ) (hWc : ∀ t, 0 < Wc t)
    (hWb : ∀ t, 0 < Wb t) (hxc : ∀ t, 0 < xc t) (hxb : ∀ t, 0 < xb t) (hxch : ∀ t, 0 < xch t)
    (hxbh : ∀ t, 0 < xbh t) (hβh : ∀ t, 0 < βh t) (hc : ∀ t, 0 < c t)
    (hWcs : ∀ t, Wc (t + 1) = Wc t * xc t) (hWbs : ∀ t, Wb (t + 1) = Wb t * xb t)
    (hβhs : ∀ t, βh (t + 1) = βh t * (xch t / xbh t * c t)) (h0 : βh 0 = Wc 0 / Wb 0) (N : ℕ) :
    |Real.log (βh N) - Real.log (Wc N / Wb N)| ≤
      |∑ t ∈ range N, (Real.log (xch t) - Real.log (xc t))| +
        |∑ t ∈ range N, (Real.log (xbh t) - Real.log (xb t))| +
        ∑ t ∈ range N, |Real.log (c t)| := by
  rw [join_ratio Wc Wb xc xb xch xbh βh c hWc hWb hxc hxb hxch hxbh hβh hc hWcs hWbs hβhs h0 N]
  have h3 := abs_sum_le_sum_abs (fun t => Real.log (c t)) (range N)
  have h1 := abs_sub (∑ t ∈ range N, (Real.log (xch t) - Real.log (xc t)))
    (∑ t ∈ range N, (Real.log (xbh t) - Real.log (xb t)))
  exact (abs_add_le _ _).trans (by linarith)

/-! ### The join's code over its passage -/

/-- [proved-derived] **`join_passage`: the executed join's code against the ideal mixture's.**
With the cell branch's executed weight `Ŵ_c` stepping by its executed faces from `W_c(0)`, the
carried `β̂` as in `join_ratio`, and each executed joined face `q̂_t` within `θ_t` in `ln` of
`(β̂_t x̂_c + x̂_b)/(1 + β̂_t)`, over the passage
`|Σ (ln q̂_t − ln q_t)| ≤ |Σ (ln x̂_c − ln x_c)| + |Σ (ln x̂_b − ln x_b)| + Σ (θ_t + 2|ln c_t|)`
with `q_t = (β_t x_c + x_b)/(1 + β_t)`, `β = W_c/W_b`. The executed faces telescope to the weight
`Â = Ŵ_c + Ŵ_c/β̂` up to each rebase's read jump (at most `|ln c|`, `log_add_le`), the ideal faces
to `W_c + W_b`, and the two weights start equal and end within the two branches' drifts and the
rebases summed once (`mix_log_le`, `join_ratio`). -/
theorem join_passage (Wc Wb Wch xc xb xch xbh βh c θ qh : ℕ → ℝ) (hWc : ∀ t, 0 < Wc t)
    (hWb : ∀ t, 0 < Wb t) (hWch : ∀ t, 0 < Wch t) (hxc : ∀ t, 0 < xc t) (hxb : ∀ t, 0 < xb t)
    (hxch : ∀ t, 0 < xch t) (hxbh : ∀ t, 0 < xbh t) (hβh : ∀ t, 0 < βh t)
    (hc : ∀ t, 0 < c t) (hWcs : ∀ t, Wc (t + 1) = Wc t * xc t)
    (hWbs : ∀ t, Wb (t + 1) = Wb t * xb t) (hWchs : ∀ t, Wch (t + 1) = Wch t * xch t)
    (hβhs : ∀ t, βh (t + 1) = βh t * (xch t / xbh t * c t)) (h0 : βh 0 = Wc 0 / Wb 0)
    (hWch0 : Wch 0 = Wc 0)
    (hθ : ∀ t, |Real.log (qh t) - Real.log ((βh t * xch t + xbh t) / (1 + βh t))| ≤ θ t)
    (N : ℕ) :
    |∑ t ∈ range N,
        (Real.log (qh t) - Real.log ((Wc t / Wb t * xc t + xb t) / (1 + Wc t / Wb t)))| ≤
      |∑ t ∈ range N, (Real.log (xch t) - Real.log (xc t))| +
        |∑ t ∈ range N, (Real.log (xbh t) - Real.log (xb t))| +
        ∑ t ∈ range N, (θ t + 2 * |Real.log (c t)|) := by
  set A : ℕ → ℝ := fun t => Wch t + Wch t / βh t with hA
  set B : ℕ → ℝ := fun t => Wc t + Wb t with hB
  have hApos : ∀ t, 0 < A t := fun t => by
    have := hWch t; have := hβh t; simp only [hA]; positivity
  have hBpos : ∀ t, 0 < B t := fun t => by have := hWc t; have := hWb t; simp only [hB]; positivity
  -- the ideal faces telescope to `B`
  have hideal : ∀ t, Real.log ((Wc t / Wb t * xc t + xb t) / (1 + Wc t / Wb t)) =
      Real.log (B (t + 1)) - Real.log (B t) := fun t => by
    have e : (Wc t / Wb t * xc t + xb t) / (1 + Wc t / Wb t) = B (t + 1) / B t := by
      have := hWb t; have := hWc t
      simp only [hB, hWcs t, hWbs t]
      field_simp
      ring
    rw [e, Real.log_div (hBpos _).ne' (hBpos _).ne']
  -- the executed faces before rounding telescope to `A`, each up to its rebase's read jump
  have hjump : ∀ t, |Real.log ((βh t * xch t + xbh t) / (1 + βh t)) -
      (Real.log (A (t + 1)) - Real.log (A t))| ≤ |Real.log (c t)| := fun t => by
    have hb := hβh t; have hw := hWch t; have hx := hxch t; have hy := hxbh t; have hct := hc t
    have e1 : A (t + 1) = Wch t / βh t * (βh t * xch t + xbh t / c t) := by
      simp only [hA, hWchs t, hβhs t]
      field_simp
    have e0 : A t = Wch t / βh t * (1 + βh t) := by
      simp only [hA]
      field_simp
      ring
    have hm : 0 < Wch t / βh t := by positivity
    rw [e1, e0, Real.log_mul hm.ne' (by positivity), Real.log_mul hm.ne' (by positivity),
      Real.log_div (by positivity) (by positivity)]
    have h := log_add_le (mul_pos hb hx).le hy (div_pos hy hct)
    rw [Real.log_div hy.ne' hct.ne', sub_sub_cancel] at h
    calc |Real.log (βh t * xch t + xbh t) - Real.log (1 + βh t) -
          (Real.log (Wch t / βh t) + Real.log (βh t * xch t + xbh t / c t) -
            (Real.log (Wch t / βh t) + Real.log (1 + βh t)))|
        = |Real.log (βh t * xch t + xbh t) - Real.log (βh t * xch t + xbh t / c t)| := by ring_nf
      _ ≤ _ := h
  -- the two weights start equal
  have hAB0 : A 0 = B 0 := by
    have := hWb 0; have := hWc 0
    simp only [hA, hB, hWch0, h0]
    field_simp
  -- and end within the branches' drifts and the rebases
  have hlogWch := log_step_sum Wch xch hWch hxch hWchs N
  have hlogWc := log_step_sum Wc xc hWc hxc hWcs N
  have hratio := join_ratio Wc Wb xc xb xch xbh βh c hWc hWb hxc hxb hxch hxbh hβh hc hWcs hWbs
    hβhs h0 N
  rw [Real.log_div (hWc N).ne' (hWb N).ne'] at hratio
  have hc1 : Real.log (Wch N) - Real.log (Wc N) =
      ∑ t ∈ range N, (Real.log (xch t) - Real.log (xc t)) := by
    rw [hlogWch, hlogWc, hWch0, sum_sub_distrib]; ring
  have hc2 : Real.log (Wch N / βh N) - Real.log (Wb N) =
      ∑ t ∈ range N, (Real.log (xbh t) - Real.log (xb t)) - ∑ t ∈ range N, Real.log (c t) := by
    rw [Real.log_div (hWch N).ne' (hβh N).ne']; linarith
  have hend : |Real.log (A N) - Real.log (B N)| ≤
      |∑ t ∈ range N, (Real.log (xch t) - Real.log (xc t))| +
        |∑ t ∈ range N, (Real.log (xbh t) - Real.log (xb t))| +
        ∑ t ∈ range N, |Real.log (c t)| := by
    have h := mix_log_le (hWc N) (hWb N) (hWch N) (div_pos (hWch N) (hβh N))
    rw [hc1, hc2] at h
    have h' := abs_sub (∑ t ∈ range N, (Real.log (xbh t) - Real.log (xb t)))
      (∑ t ∈ range N, Real.log (c t))
    have h3 := abs_sum_le_sum_abs (fun t => Real.log (c t)) (range N)
    exact h.trans (by linarith)
  -- assemble
  have hsplit : ∑ t ∈ range N,
      (Real.log (qh t) - Real.log ((Wc t / Wb t * xc t + xb t) / (1 + Wc t / Wb t))) =
      ∑ t ∈ range N, (Real.log (qh t) - Real.log ((βh t * xch t + xbh t) / (1 + βh t))) +
        ∑ t ∈ range N, (Real.log ((βh t * xch t + xbh t) / (1 + βh t)) -
          (Real.log (A (t + 1)) - Real.log (A t))) +
        (Real.log (A N) - Real.log (B N)) := by
    have tA := sum_range_sub (fun t => Real.log (A t)) N
    have tB := sum_range_sub (fun t => Real.log (B t)) N
    rw [hAB0] at tA
    rw [sum_congr rfl fun t _ => by rw [hideal t]]
    have e : Real.log (A N) - Real.log (B N) =
        ∑ t ∈ range N, (Real.log (A (t + 1)) - Real.log (A t)) -
          ∑ t ∈ range N, (Real.log (B (t + 1)) - Real.log (B t)) := by rw [tA, tB]; ring
    rw [e, ← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun t _ => by ring
  rw [hsplit]
  have hθs := (abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun t (_ : t ∈ range N) => hθ t)
  have hjs := (abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun t (_ : t ∈ range N) => hjump t)
  have htot : ∑ t ∈ range N, (θ t + 2 * |Real.log (c t)|) =
      ∑ t ∈ range N, θ t + ∑ t ∈ range N, |Real.log (c t)| +
        ∑ t ∈ range N, |Real.log (c t)| := by
    rw [← sum_add_distrib, ← sum_add_distrib]; exact sum_congr rfl fun t _ => by ring
  rw [htot]
  have hx := abs_add_le (∑ t ∈ range N,
      (Real.log (qh t) - Real.log ((βh t * xch t + xbh t) / (1 + βh t))) +
    ∑ t ∈ range N, (Real.log ((βh t * xch t + xbh t) / (1 + βh t)) -
      (Real.log (A (t + 1)) - Real.log (A t)))) (Real.log (A N) - Real.log (B N))
  have hy := abs_add_le (∑ t ∈ range N,
      (Real.log (qh t) - Real.log ((βh t * xch t + xbh t) / (1 + βh t))))
    (∑ t ∈ range N, (Real.log ((βh t * xch t + xbh t) / (1 + βh t)) -
      (Real.log (A (t + 1)) - Real.log (A t))))
  linarith

/-! ### Audit -/

#print axioms mix_log_le
#print axioms join_face_drift
#print axioms join_read_drift
#print axioms log_step_sum
#print axioms join_ratio
#print axioms join_ratio_drift
#print axioms join_passage

end Holonics.Compression.Landmark.Context.JoinDrift
