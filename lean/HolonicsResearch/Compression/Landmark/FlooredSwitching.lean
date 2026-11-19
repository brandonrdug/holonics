import Holonics.Compression.Landmark.Context.Population
import Holonics.Compression.Landmark.Context.Dormancy

/-!
# The executed floor: a dormant member returns at `K + log₂ M` bits

[proved-derived; formal-checked] The source is #410's box "The executed floor's segment/switching
bound for the population's local mixture, `≤ −log₂ π_(f₀) + Σ_i code_(f_i) + k(K + log₂ M) + drift`
(`receiver::population::local`; no Lean statement)". The law is the retired Rust module's header,
"The executed chart" and "The floor is dormancy in time" (`crates/holonics/src/receiver/population/local.rs`
at `4fd4b973b^`; `4fd4b973b` retired `LocalMixture` on September 28, measured and not adopted). It is
kept in the record
`research/records/2026-09-28_A_NUMBER_IS_A_HELIX_ITS_BASE_IS_A_FACE_AND_A_FAMILY_WINS_WHERE_IT_IS_CLOSEST.md`
(§5 and its obligation "The executed floor's switching bound", owed to #62, now #410) and in the "not in
Lean" clauses of the atlas row `receiver.population-local-mixture`. The rows `receiver.population-dormancy`,
`receiver.population-switch-price` and `hnn.fixed-share` hold the declared switching law (the fixed share on
the hazard ladder) that the floor stands beside, and `hnn.landmark-released-ratio`
(`HNN/ReleasedTelescope`) the two-face clamp of a ratio into `[2^(−K), 2^K]`, whose turn between faces costs
`K + 1` bits: this owner's `K + log₂ M` at `M = 2`. The owner extended is
`Compression/Landmark/Context/Population` (`local_telescope`, `local_mixture_code`: the node-local law with
unrounded, unfloored weights); `LocalWeighing.{IsPrior, static_mixture, fwdMix, idKernel, halfPrior,
neg_logb_le_of_le}` and `Dormancy.stay_code_le` are reused.

The model. One context's ticks `t < n` on its own clock (§7 joins the contexts); `M = |ι|` members;
weights `w_t(f) ≥ 0`, the weights the face at tick `t` mixes, after the floor; faces `P_t(f) > 0`, member
`f`'s face of the received cell; the total `W_t = Σ_f w_t(f)` (`chartTotal`), the meeting
`V_t = Σ_f w_t(f) P_t(f)` (`chartMass`) and the executed face `q̂_t = V_t/W_t` (`chartFace`). The chart's
three laws, in the abstract:

```text
rounding  w_(t+1)(f) ≥ ρ_t w_t(f) P_t(f), ρ_t > 0     ρ_t ≥ 1 − 2^(−62) at a 64-bit mantissa; 1 where none rounds
raise     W_(t+1) ≤ (1 + ε_t) V_t, ε_t ≥ 0            ε_t = M 2^(−K) where a floor binds; 0 where none does
floor     2^(−K) w_s(g) ≤ w_s(f) for every g          at each switch time s, f the member taken up there
```

What is proved.

1. **The segment telescope** (`segment_telescope`, `segment_code`; through `share_step`, `floor_share`,
   `logb_floor_share` and the invariant `path_share`): for every path `σ` with `k = switchCount σ (n − 1)`
   switches before its last tick,
   `−log₂ ∏_(t<n) q̂_t ≤ −log₂(w_0(σ_0)/W_0) + Σ_(t<n) (−log₂ P_t(σ_t)) + k (K + log₂ M)
   + Σ_(t<n) (log₂(1 + ε_t) − log₂ ρ_t)`.
   On a segment held by `g` the faces multiply to at least the totals' ratio over `∏ (1 + ε_t)`, and the
   last total holds `g`'s weight, at least its first weight times `∏ ρ_t P_t(g)`; at a switch the member
   taken up holds at least `2^(−K)/M` of the total (`max_g w_s(g) ≥ W_s/M`): the switch's price is
   `K + log₂ M` bits.
2. **The drift** (`logb_one_add_le`, `neg_logb_one_sub_le`, `drift_le`): `log₂(1 + y) ≤ 2y` for `y ≥ 0`
   and `−log₂(1 − x) ≤ 3x` for `0 ≤ x ≤ ½`; with every factor `ρ_t` in `[1 − 2^(−R), 1]` (`R ≥ 1`) and
   every raise `ε_t` in `[0, M 2^(−K)]` the drift is at most `3 r 2^(−R) + M φ 2^(1−K)`, `r` the ticks with
   `ρ_t ≠ 1` and `φ` those with `ε_t ≠ 0`. At `R = 62` it is the Rust's `RungReceipt::drift`.
3. **The floor law** (`leader`, `floorStep`, `floorBinds`, `floorRaise`, `floorChart`). For
   `û(f) = max(u(f), 2^(−K) max_g u(g))` over nonnegative `u`: (a) the total rises by at most `M 2^(−K)` of
   `Σ_f u(f)`, and not at all where no floor binds (`floor_raise`, `floor_idle`, `floor_raise_le`), so the
   raise law holds with `ε = M 2^(−K)` where a floor binds and `ε = 0` elsewhere; (b) the leader is unchanged
   (`floor_leader`); (c) every member holds `2^(−K)` of every member after it, so the floor law holds at
   every tick (`floor_holds`); (d) while some member is positive no member is zeroed: dormant, not dead
   (`floor_keeps_dormant`). Together (`executed_laws`, `executed_face_pos`, `executed_floor_code`;
   `floorChart_code` with no rounding): a chart whose weights open at a prior `π`, are multiplied by their
   faces, rounded down by factors in `[1 − 2^(−R), 1]` and floored codes along every path within
   `−log₂ π(σ_0) + Σ_t (−log₂ P_t(σ_t)) + k (K + log₂ M) + 3 r 2^(−R) + M φ 2^(1−K)`: the box's bound with
   its drift certified.
4. **Static Bayes pays what it fell behind** (`static_bayes_pays_what_it_fell_behind`, over
   `swap_member_lik`, `swap_static`, `swap_code`, `swap_floored_code`): two members exchanged on `0^N 1^N`
   (`swapFace`: faces `7/8` and `1/8`, `δ = 1/8`). Each member and the static mixture at `½/½` code
   `2N log₂(8/7) + N log₂ 7` bits; the floored chart codes at most `2N log₂(8/7) + K + 2 + 8N 2^(−K)`. The
   static mixture's excess, at least `N log₂ 7 − (K + 2) − 8N 2^(−K)`, grows with the first segment's
   length: the second member falls `N log₂ 7` bits behind there and the static mixture pays it all back,
   where the floor charges `K + log₂ M` once.
5. **The floored mixture can code below its best single member** (`floored_below_best_member`,
   `floored_codes_below_every_member`), which no static mixture does (`Σ_f π_f L_f ≤ max_f L_f`): on the
   exchanged passage it does wherever `K + 2 + 8N 2^(−K) < N log₂ 7`; and at `N = 2`, `K = 2` the floored
   weights written out (`swap_weights_one`, `swap_weights_two`, `swap_weights_three`) give the faces
   `1/2, 29/40, 11/40, 53/88`, whose product `1537/25600` exceeds each member's and the static mixture's
   `49/4096`.
6. **The uniform prior and the contexts** (`uniform_opening_code`, `uniform_best_member_code`,
   `uniform_local_mixture_code`, `code_splits_by_context`): a uniform opening pays `log₂ M`; with item 1 at
   `k = 0` a context codes within its best member's code plus `log₂ M` plus the drift;
   `Population.local_mixture_code` at `π = 1/M` gives the local mixture's `Σ_(c met) (min_f code_f(c) +
   log₂ M)` (the atlas row's "not in Lean" clause); and a passage's code is the sum of its contexts' codes.
7. **The floored local mixture** (`ctxClock`, `ctxTicks`, `prod_fiber_clock`, `floored_local_code`): a
   context's ticks read on its own clock are that clock's first `n_c` ticks in order, so where each context
   runs the executed chart on its own clock the local mixture's executed code is at most the sum, over the
   contexts met, of item 3's bound on each: the box's per-context sum.

What is not claimed.

* The gating ladder's choice of rung, its charge `⌈log₂ |ladder|⌉` bits and its comparison rungs.
* The `PassageCode` enclosures through which the Rust read each code: this file works on rational faces
  and the real logarithms of their products.
* That the Rust's product of a 64-bit mantissa and a face (`times`, `kept`) lands in `[1 − 2^(−62), 1]`
  of the unrounded product, and that its counters `roundings` and `floors` count `r` and `φ`: the factors
  and the counts are hypotheses here.
* A member at zero likelihood (death): faces are positive, as in `Population.local_telescope`; a member's
  face, read from its whole past, enters only as the sequence `P_t(f)` on its context's clock.
* The floor's comparison with the declared fixed share on the hazard ladder (`Dormancy.share_path_code_le`:
  `k j + 3` bits over `n ≤ 2^j` cells, against the floor's `k (K + log₂ M) + M φ 2^(1−K)`), which the
  record names as owed, and any measured reading of either.
* Items 4 and 5 are read on one witness passage; no rate over a family of passages is stated.

The computational object is the helical pair interaction read as a receiver's population: at each context
the members (navigator families) meet the received cell through their faces, the context's posterior weighs
that meeting where it happens, and the floor holds a member that loses the meeting at a declared fraction of
the leader, so the pair stays coupled while one side is silent. Of the winding guide's six general objects
this touches **faces and placement** (each member's face and the executed face), the **tube** (each
context's chart moves only at its own ticks, `ctxClock`, and a dormant member keeps its floor while the
passage runs on) and the **tower thread** (the gating map's contexts restrict the passage, whose code is
their sum); the helix, the pair's slip and the cell holonomy stay attached through the members' own owners.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Compression.Landmark.FlooredSwitching

open Finset
open Holonics.Compression.Landmark.Context.Tree
open Holonics.Compression.Landmark.Context.LocalWeighing
open Holonics.Compression.Landmark.Context.Population
open Holonics.Compression.Landmark.Context.Dormancy

/-! ## 1. The executed chart and its segment telescope -/

section Switches

variable {ι : Type*} [DecidableEq ι]

/-- [definition] **A path's switches** over its first `n` ticks: `#{t < n : σ_t ≠ σ_(t+1)}`
(`LocalWeighing.switches` over any members). -/
def switchCount (σ : ℕ → ι) (n : ℕ) : ℕ :=
  ((range n).filter fun t => σ t ≠ σ (t + 1)).card

/-- [proved-derived; formal-checked] No tick, no switch. -/
theorem switchCount_zero (σ : ℕ → ι) : switchCount σ 0 = 0 := by
  simp [switchCount]

/-- [proved-derived; formal-checked] A tick adds a switch where, and only where, the path changes member. -/
theorem switchCount_succ (σ : ℕ → ι) (m : ℕ) :
    switchCount σ (m + 1) = switchCount σ m + if σ m ≠ σ (m + 1) then 1 else 0 := by
  unfold switchCount
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

end Switches

section Segment

variable {ι : Type*} [Fintype ι]

/-- [definition] **A context's total** at tick `t`: `W_t = Σ_f w_t(f)`. -/
def chartTotal (w : ℕ → ι → ℚ) (t : ℕ) : ℚ := ∑ f, w t f

/-- [definition] **The weights' meeting with the faces** at tick `t`: `V_t = Σ_f w_t(f) P_t(f)`. -/
def chartMass (w P : ℕ → ι → ℚ) (t : ℕ) : ℚ := ∑ f, w t f * P t f

/-- [definition] **The executed face** of the received cell at tick `t`: `q̂_t = V_t / W_t`. -/
def chartFace (w P : ℕ → ι → ℚ) (t : ℕ) : ℚ := chartMass w P t / chartTotal w t

/-- [proved-derived; formal-checked] A positive total meets positive faces in a positive mass. -/
theorem chartMass_pos {w P : ℕ → ι → ℚ} (hw : ∀ t f, 0 ≤ w t f) (hP : ∀ t f, 0 < P t f) {t : ℕ}
    (hW : 0 < chartTotal w t) : 0 < chartMass w P t := by
  obtain ⟨f, -, hf⟩ := exists_lt_of_sum_lt (s := univ) (f := fun _ => (0 : ℚ)) (g := w t)
    (by simpa [chartTotal] using hW)
  exact sum_pos' (fun g _ => mul_nonneg (hw t g) (hP t g).le) ⟨f, mem_univ _, mul_pos hf (hP t f)⟩

/-- [proved-derived; formal-checked] Under the rounding law a positive opening total stays
positive at every tick. -/
theorem chartTotal_pos {w P : ℕ → ι → ℚ} {ρ : ℕ → ℚ} (hw : ∀ t f, 0 ≤ w t f)
    (hP : ∀ t f, 0 < P t f) (hρ : ∀ t, 0 < ρ t)
    (hround : ∀ t f, ρ t * (w t f * P t f) ≤ w (t + 1) f) (h0 : 0 < chartTotal w 0) :
    ∀ t, 0 < chartTotal w t
  | 0 => h0
  | t + 1 => by
    have hV := chartMass_pos hw hP (chartTotal_pos hw hP hρ hround h0 t)
    calc 0 < ρ t * chartMass w P t := mul_pos (hρ t) hV
      _ = ∑ f, ρ t * (w t f * P t f) := by rw [chartMass, mul_sum]
      _ ≤ chartTotal w (t + 1) := sum_le_sum fun f _ => hround t f

/-- [proved-derived; formal-checked] **One tick.** A member's share times its rounded face is at
most the raised executed face times its share after the tick:
`(w_t(g)/W_t) ρ_t P_t(g) ≤ (1 + ε_t) q̂_t (w_(t+1)(g)/W_(t+1))`. -/
theorem share_step {w P : ℕ → ι → ℚ} {ρ ε : ℕ → ℚ} {t : ℕ} {g : ι}
    (hW : 0 < chartTotal w t) (hW' : 0 < chartTotal w (t + 1)) (hg : 0 ≤ w (t + 1) g)
    (hround : ρ t * (w t g * P t g) ≤ w (t + 1) g)
    (hraise : chartTotal w (t + 1) ≤ (1 + ε t) * chartMass w P t) :
    w t g / chartTotal w t * (ρ t * P t g) ≤
      (1 + ε t) * chartFace w P t * (w (t + 1) g / chartTotal w (t + 1)) := by
  have e1 : w t g / chartTotal w t * (ρ t * P t g) = ρ t * (w t g * P t g) / chartTotal w t := by
    ring
  have e2 : (1 + ε t) * chartFace w P t * (w (t + 1) g / chartTotal w (t + 1)) =
      (1 + ε t) * chartMass w P t / chartTotal w (t + 1) * w (t + 1) g / chartTotal w t := by
    rw [chartFace]; ring
  rw [e1, e2]
  refine div_le_div_of_nonneg_right ?_ hW.le
  calc ρ t * (w t g * P t g) ≤ w (t + 1) g := hround
    _ = chartTotal w (t + 1) / chartTotal w (t + 1) * w (t + 1) g := by
        rw [div_self hW'.ne', one_mul]
    _ ≤ (1 + ε t) * chartMass w P t / chartTotal w (t + 1) * w (t + 1) g :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hraise hW'.le) hg

/-- [proved-derived; formal-checked] **The floor's share.** A member holding `2^(−K)` of every
member holds at least `2^(−K)/M` of the total: `max_g w_s(g) ≥ W_s/M`. -/
theorem floor_share {w : ℕ → ι → ℚ} {K s : ℕ} {h : ι} (hW : 0 < chartTotal w s)
    (hfloor : ∀ g, (1 / 2 : ℚ) ^ K * w s g ≤ w s h) :
    (1 / 2 : ℚ) ^ K / Fintype.card ι ≤ w s h / chartTotal w s := by
  have hM : (0 : ℚ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨h⟩
  rw [div_le_div_iff₀ hM hW]
  calc (1 / 2 : ℚ) ^ K * chartTotal w s = ∑ g, (1 / 2 : ℚ) ^ K * w s g := by
        rw [chartTotal, mul_sum]
    _ ≤ ∑ _g : ι, w s h := sum_le_sum fun g _ => hfloor g
    _ = w s h * Fintype.card ι := by rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]

/-- [proved-standard; formal-checked] The stay step's algebra: an invariant carried through one tick
on the same member. -/
theorem stay_alg {A Q E s ρP q e s' : ℚ} (hJ : A ≤ Q * E * s) (hρP : 0 ≤ ρP) (hQE : 0 ≤ Q * E)
    (hstep : s * ρP ≤ e * q * s') : A * ρP ≤ Q * q * (E * e) * s' :=
  calc A * ρP ≤ Q * E * s * ρP := mul_le_mul_of_nonneg_right hJ hρP
    _ = Q * E * (s * ρP) := by ring
    _ ≤ Q * E * (e * q * s') := mul_le_mul_of_nonneg_left hstep hQE
    _ = Q * q * (E * e) * s' := by ring

/-- [proved-standard; formal-checked] The switch step's algebra: the old member's tick, then the new
member's floor share. -/
theorem switch_alg {A Q E s ρP q e s' c : ℚ} (hJ : A ≤ Q * E * s) (hρP : 0 ≤ ρP)
    (hQE : 0 ≤ Q * E) (hc : 0 ≤ c) (heq : 0 ≤ e * q) (hstep : s * ρP ≤ e * q) (hfl : c ≤ s') :
    A * ρP * c ≤ Q * q * (E * e) * s' :=
  calc A * ρP * c ≤ Q * E * s * ρP * c :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hJ hρP) hc
    _ = Q * E * (s * ρP) * c := by ring
    _ ≤ Q * E * (e * q) * c := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hQE) hc
    _ ≤ Q * E * (e * q) * s' := mul_le_mul_of_nonneg_left hfl (mul_nonneg hQE heq)
    _ = Q * q * (E * e) * s' := by ring

/-- [proved-standard; formal-checked] The last tick's algebra: the invariant read without a share
after it. -/
theorem last_alg {A Q E s ρP q e : ℚ} (hJ : A ≤ Q * E * s) (hρP : 0 ≤ ρP) (hQE : 0 ≤ Q * E)
    (hstep : s * ρP ≤ e * q) : A * ρP ≤ Q * q * (E * e) :=
  calc A * ρP ≤ Q * E * s * ρP := mul_le_mul_of_nonneg_right hJ hρP
    _ = Q * E * (s * ρP) := by ring
    _ ≤ Q * E * (e * q) := mul_le_mul_of_nonneg_left hstep hQE
    _ = Q * q * (E * e) := by ring

variable [DecidableEq ι]

/-- [proved-derived; formal-checked] **`path_share`: the segment invariant.** Along a path whose
taken-up members hold the floor at each switch before tick `m`,
`(w_0(σ_0)/W_0) ∏_(t<m) ρ_t P_t(σ_t) (2^(−K)/M)^(k_m) ≤ ∏_(t<m) q̂_t ∏_(t<m)(1 + ε_t) (w_m(σ_m)/W_m)`,
`k_m` the switches before `m`. -/
theorem path_share {K : ℕ} {w P : ℕ → ι → ℚ} {ρ ε : ℕ → ℚ}
    (hw : ∀ t f, 0 ≤ w t f) (hP : ∀ t f, 0 < P t f) (hρ : ∀ t, 0 < ρ t) (hε : ∀ t, 0 ≤ ε t)
    (hround : ∀ t f, ρ t * (w t f * P t f) ≤ w (t + 1) f)
    (hraise : ∀ t, chartTotal w (t + 1) ≤ (1 + ε t) * chartMass w P t)
    (hW0 : 0 < chartTotal w 0) (σ : ℕ → ι) :
    ∀ m, (∀ t < m, σ t ≠ σ (t + 1) →
        ∀ g, (1 / 2 : ℚ) ^ K * w (t + 1) g ≤ w (t + 1) (σ (t + 1))) →
      w 0 (σ 0) / chartTotal w 0 * (∏ t ∈ range m, (ρ t * P t (σ t))) *
          ((1 / 2 : ℚ) ^ K / Fintype.card ι) ^ switchCount σ m ≤
        (∏ t ∈ range m, chartFace w P t) * (∏ t ∈ range m, (1 + ε t)) *
          (w m (σ m) / chartTotal w m) := by
  have hW := chartTotal_pos hw hP hρ hround hW0
  have hq : ∀ t, 0 < chartFace w P t := fun t => div_pos (chartMass_pos hw hP (hW t)) (hW t)
  intro m
  induction m with
  | zero => intro _; simp [switchCount_zero]
  | succ m ih =>
    intro hfloor
    have hJ := ih fun t ht => hfloor t (Nat.lt_succ_of_lt ht)
    have hρP : 0 ≤ ρ m * P m (σ m) := (mul_pos (hρ m) (hP m _)).le
    have hQE : 0 ≤ (∏ t ∈ range m, chartFace w P t) * ∏ t ∈ range m, (1 + ε t) :=
      mul_nonneg (prod_nonneg fun t _ => (hq t).le) (prod_nonneg fun t _ => by linarith [hε t])
    have heq : 0 ≤ (1 + ε m) * chartFace w P m := mul_nonneg (by linarith [hε m]) (hq m).le
    have hstep := share_step (g := σ m) (hW m) (hW (m + 1)) (hw (m + 1) (σ m)) (hround m (σ m))
      (hraise m)
    rw [prod_range_succ, prod_range_succ, prod_range_succ, switchCount_succ]
    by_cases hs : σ m ≠ σ (m + 1)
    · rw [if_pos hs, pow_succ]
      have hfl := floor_share (hW (m + 1)) (hfloor m (Nat.lt_succ_self m) hs)
      have hle1 : w (m + 1) (σ m) / chartTotal w (m + 1) ≤ 1 :=
        div_le_one_of_le₀ (single_le_sum (fun f _ => hw (m + 1) f) (mem_univ _)) (hW _).le
      have hstep' : w m (σ m) / chartTotal w m * (ρ m * P m (σ m)) ≤
          (1 + ε m) * chartFace w P m :=
        hstep.trans (by simpa using mul_le_mul_of_nonneg_left hle1 heq)
      exact (le_of_eq (by ring)).trans
        (switch_alg hJ hρP hQE (by positivity) heq hstep' hfl)
    · rw [if_neg hs, add_zero]
      have hσ : σ (m + 1) = σ m := (not_not.mp hs).symm
      rw [hσ]
      exact (le_of_eq (by ring)).trans (stay_alg hJ hρP hQE hstep)

/-- [proved-derived; formal-checked] **`segment_telescope`: the segment/switching bound as a
product.** For every path `σ` whose taken-up members hold the floor at each switch before its last
tick, with `k = switchCount σ (n − 1)`:
`(w_0(σ_0)/W_0) ∏_(t<n) ρ_t P_t(σ_t) (2^(−K)/M)^k ≤ ∏_(t<n) q̂_t ∏_(t<n) (1 + ε_t)`. -/
theorem segment_telescope {K : ℕ} {w P : ℕ → ι → ℚ} {ρ ε : ℕ → ℚ}
    (hw : ∀ t f, 0 ≤ w t f) (hP : ∀ t f, 0 < P t f) (hρ : ∀ t, 0 < ρ t) (hε : ∀ t, 0 ≤ ε t)
    (hround : ∀ t f, ρ t * (w t f * P t f) ≤ w (t + 1) f)
    (hraise : ∀ t, chartTotal w (t + 1) ≤ (1 + ε t) * chartMass w P t)
    (σ : ℕ → ι) (n : ℕ) (h0 : 0 < w 0 (σ 0))
    (hfloor : ∀ t < n - 1, σ t ≠ σ (t + 1) →
      ∀ g, (1 / 2 : ℚ) ^ K * w (t + 1) g ≤ w (t + 1) (σ (t + 1))) :
    w 0 (σ 0) / chartTotal w 0 * (∏ t ∈ range n, (ρ t * P t (σ t))) *
        ((1 / 2 : ℚ) ^ K / Fintype.card ι) ^ switchCount σ (n - 1) ≤
      (∏ t ∈ range n, chartFace w P t) * ∏ t ∈ range n, (1 + ε t) := by
  have hW0 : 0 < chartTotal w 0 :=
    lt_of_lt_of_le h0 (single_le_sum (fun f _ => hw 0 f) (mem_univ (σ 0)))
  have hW := chartTotal_pos hw hP hρ hround hW0
  have hq : ∀ t, 0 < chartFace w P t := fun t => div_pos (chartMass_pos hw hP (hW t)) (hW t)
  cases n with
  | zero =>
    simp only [range_zero, prod_empty, mul_one, Nat.zero_sub, switchCount_zero, pow_zero]
    exact div_le_one_of_le₀ (single_le_sum (fun f _ => hw 0 f) (mem_univ _)) hW0.le
  | succ m =>
    rw [Nat.add_sub_cancel]
    have hJ := path_share hw hP hρ hε hround hraise hW0 σ m hfloor
    have hρP : 0 ≤ ρ m * P m (σ m) := (mul_pos (hρ m) (hP m _)).le
    have hQE : 0 ≤ (∏ t ∈ range m, chartFace w P t) * ∏ t ∈ range m, (1 + ε t) :=
      mul_nonneg (prod_nonneg fun t _ => (hq t).le) (prod_nonneg fun t _ => by linarith [hε t])
    have heq : 0 ≤ (1 + ε m) * chartFace w P m := mul_nonneg (by linarith [hε m]) (hq m).le
    have hstep := share_step (g := σ m) (hW m) (hW (m + 1)) (hw (m + 1) (σ m)) (hround m (σ m))
      (hraise m)
    have hle1 : w (m + 1) (σ m) / chartTotal w (m + 1) ≤ 1 :=
      div_le_one_of_le₀ (single_le_sum (fun f _ => hw (m + 1) f) (mem_univ _)) (hW _).le
    have hstep' : w m (σ m) / chartTotal w m * (ρ m * P m (σ m)) ≤
        (1 + ε m) * chartFace w P m :=
      hstep.trans (by simpa using mul_le_mul_of_nonneg_left hle1 heq)
    rw [prod_range_succ, prod_range_succ, prod_range_succ]
    exact (le_of_eq (by ring)).trans (last_alg hJ hρP hQE hstep')

omit [Fintype ι] [DecidableEq ι] in
/-- [proved-standard; formal-checked] A product of positive rationals reads its bits as a sum. -/
theorem logb_cast_prod {α : Type*} {s : Finset α} {a : α → ℚ} (ha : ∀ t ∈ s, 0 < a t) :
    Real.logb 2 ((∏ t ∈ s, a t : ℚ) : ℝ) = ∑ t ∈ s, Real.logb 2 (a t : ℝ) := by
  rw [Rat.cast_prod]
  exact Real.logb_prod _ _ fun t ht => by exact_mod_cast (ha t ht).ne'

omit [Fintype ι] [DecidableEq ι] in
/-- [proved-standard; formal-checked] Two positive rationals' product reads its bits as a sum. -/
theorem logb_cast_mul {a b : ℚ} (ha : 0 < a) (hb : 0 < b) :
    Real.logb 2 ((a * b : ℚ) : ℝ) = Real.logb 2 (a : ℝ) + Real.logb 2 (b : ℝ) := by
  rw [Rat.cast_mul]
  exact Real.logb_mul (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')

omit [Fintype ι] [DecidableEq ι] in
/-- [proved-standard; formal-checked] **The switch's price**: the floor share `2^(−K)/M` reads
`−(K + log₂ M)` bits. -/
theorem logb_floor_share (K : ℕ) {M : ℕ} (hM : 0 < M) :
    Real.logb 2 ((((1 / 2 : ℚ) ^ K / M : ℚ)) : ℝ) = -((K : ℝ) + Real.logb 2 (M : ℝ)) := by
  push_cast
  rw [Real.logb_div (by positivity) (by exact_mod_cast hM.ne'), Real.logb_pow, one_div,
    Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
  ring

/-- [proved-derived; formal-checked] **`segment_code`: the segment/switching bound in bits.** For
every path `σ` with `k = switchCount σ (n − 1)` switches before its last tick, whose taken-up members
hold the floor at each switch,
`−log₂ ∏_(t<n) q̂_t ≤ −log₂(w_0(σ_0)/W_0) + Σ_(t<n) (−log₂ P_t(σ_t)) + k (K + log₂ M)
+ Σ_(t<n) (log₂(1 + ε_t) − log₂ ρ_t)`. -/
theorem segment_code {K : ℕ} {w P : ℕ → ι → ℚ} {ρ ε : ℕ → ℚ}
    (hw : ∀ t f, 0 ≤ w t f) (hP : ∀ t f, 0 < P t f) (hρ : ∀ t, 0 < ρ t) (hε : ∀ t, 0 ≤ ε t)
    (hround : ∀ t f, ρ t * (w t f * P t f) ≤ w (t + 1) f)
    (hraise : ∀ t, chartTotal w (t + 1) ≤ (1 + ε t) * chartMass w P t)
    (σ : ℕ → ι) (n : ℕ) (h0 : 0 < w 0 (σ 0))
    (hfloor : ∀ t < n - 1, σ t ≠ σ (t + 1) →
      ∀ g, (1 / 2 : ℚ) ^ K * w (t + 1) g ≤ w (t + 1) (σ (t + 1))) :
    -Real.logb 2 ((∏ t ∈ range n, chartFace w P t : ℚ) : ℝ) ≤
      -Real.logb 2 ((w 0 (σ 0) / chartTotal w 0 : ℚ) : ℝ) +
        ∑ t ∈ range n, -Real.logb 2 (P t (σ t) : ℝ) +
        switchCount σ (n - 1) * ((K : ℝ) + Real.logb 2 (Fintype.card ι : ℝ)) +
        ∑ t ∈ range n, (Real.logb 2 ((1 + ε t : ℚ) : ℝ) - Real.logb 2 (ρ t : ℝ)) := by
  have hprod := segment_telescope hw hP hρ hε hround hraise σ n h0 hfloor
  have hW0 : 0 < chartTotal w 0 :=
    lt_of_lt_of_le h0 (single_le_sum (fun f _ => hw 0 f) (mem_univ (σ 0)))
  have hW := chartTotal_pos hw hP hρ hround hW0
  have hq : ∀ t, 0 < chartFace w P t := fun t => div_pos (chartMass_pos hw hP (hW t)) (hW t)
  have hM : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨σ 0⟩
  have hS0 : 0 < w 0 (σ 0) / chartTotal w 0 := div_pos h0 hW0
  have hPi : 0 < ∏ t ∈ range n, (ρ t * P t (σ t)) := prod_pos fun t _ => mul_pos (hρ t) (hP t _)
  have hc : 0 < (1 / 2 : ℚ) ^ K / Fintype.card ι := div_pos (by positivity) (by exact_mod_cast hM)
  have hck : 0 < ((1 / 2 : ℚ) ^ K / Fintype.card ι) ^ switchCount σ (n - 1) := pow_pos hc _
  have hQ : 0 < ∏ t ∈ range n, chartFace w P t := prod_pos fun t _ => hq t
  have hE : ∀ t ∈ range n, 0 < 1 + ε t := fun t _ => by linarith [hε t]
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num)
    (by exact_mod_cast mul_pos (mul_pos hS0 hPi) hck) (Rat.cast_le.mpr hprod)
  rw [logb_cast_mul (mul_pos hS0 hPi) hck, logb_cast_mul hS0 hPi, Rat.cast_pow, Real.logb_pow,
    logb_floor_share K hM, logb_cast_prod fun t _ => mul_pos (hρ t) (hP t _),
    logb_cast_mul hQ (prod_pos hE), logb_cast_prod hE] at hlog
  rw [sum_congr rfl fun t _ => logb_cast_mul (hρ t) (hP t (σ t)), sum_add_distrib] at hlog
  rw [sum_neg_distrib, sum_sub_distrib]
  linarith

end Segment

/-! ## 2. The drift -/

section Drift

/-- [proved-standard; formal-checked] `log₂(1 + y) ≤ 2y` for `y ≥ 0`: `ln(1 + y) ≤ y` and
`ln 2 > ½`. -/
theorem logb_one_add_le {y : ℝ} (hy : 0 ≤ y) : Real.logb 2 (1 + y) ≤ 2 * y := by
  have h1 : Real.log (1 + y) ≤ y := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + y)
    linarith
  have hl2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith

/-- [proved-standard; formal-checked] `−log₂(1 − x) ≤ 3x` for `0 ≤ x ≤ ½`: `−ln(1 − x) ≤ x/(1 − x) ≤ 2x`
and `ln 2 > ⅔` (`Dormancy.stay_code_le` is its case `x = 2^(−j)`). -/
theorem neg_logb_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -Real.logb 2 (1 - x) ≤ 3 * x := by
  have h1x : 0 < 1 - x := by linarith
  have hlog : -Real.log (1 - x) ≤ 2 * x := by
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr h1x)
    rw [Real.log_inv] at this
    have hinv : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp; ring
    rw [hinv] at this
    have : x / (1 - x) ≤ 2 * x := by
      rw [div_le_iff₀ h1x]; nlinarith
    linarith
  have hl2 : (2 : ℝ) / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  rw [Real.logb, show -(Real.log (1 - x) / Real.log 2) = -Real.log (1 - x) / Real.log 2 by ring,
    div_le_iff₀ (by linarith)]
  nlinarith

/-- [proved-derived; formal-checked] **`drift_le`: the certified drift.** With every rounding factor
in `[1 − 2^(−R), 1]` (`R ≥ 1`) and every floor's raise in `[0, M 2^(−K)]`, the drift over `n` ticks
is at most `3 r 2^(−R) + M φ 2^(1−K)`, `r` the ticks with `ρ_t ≠ 1` and `φ` those with `ε_t ≠ 0`
(`Dormancy.stay_code_le` prices a rounding). -/
theorem drift_le {R K M : ℕ} (hR : 1 ≤ R) {ρ ε : ℕ → ℚ} (n : ℕ)
    (hρ : ∀ t ∈ range n, 1 - (1 / 2 : ℚ) ^ R ≤ ρ t ∧ ρ t ≤ 1)
    (hε : ∀ t ∈ range n, 0 ≤ ε t ∧ ε t ≤ M * (1 / 2 : ℚ) ^ K) :
    ∑ t ∈ range n, (Real.logb 2 ((1 + ε t : ℚ) : ℝ) - Real.logb 2 (ρ t : ℝ)) ≤
      3 * ((range n).filter fun t => ρ t ≠ 1).card * (1 / 2 : ℝ) ^ R +
        M * ((range n).filter fun t => ε t ≠ 0).card * (2 * (1 / 2 : ℝ) ^ K) := by
  have hhalf : (1 / 2 : ℚ) ^ R ≤ 1 / 2 :=
    calc (1 / 2 : ℚ) ^ R ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hR
      _ = 1 / 2 := by norm_num
  have hterm : ∀ t ∈ range n, Real.logb 2 ((1 + ε t : ℚ) : ℝ) - Real.logb 2 (ρ t : ℝ) ≤
      (if ρ t ≠ 1 then 3 * (1 / 2 : ℝ) ^ R else 0) +
        (if ε t ≠ 0 then (M : ℝ) * (2 * (1 / 2 : ℝ) ^ K) else 0) := by
    intro t ht
    obtain ⟨hρl, -⟩ := hρ t ht
    obtain ⟨hε0, hεu⟩ := hε t ht
    have hA : -Real.logb 2 (ρ t : ℝ) ≤ if ρ t ≠ 1 then 3 * (1 / 2 : ℝ) ^ R else 0 := by
      split_ifs with h
      · have hpos : (0 : ℚ) < 1 - (1 / 2) ^ R := by linarith
        have hb := neg_logb_le_of_le (a := ((1 - (1 / 2 : ℚ) ^ R : ℚ) : ℝ)) (b := (ρ t : ℝ))
          (by exact_mod_cast hpos) (by exact_mod_cast hρl)
        exact hb.trans (stay_code_le hR)
      · rw [not_not.mp h]; simp
    have hB : Real.logb 2 ((1 + ε t : ℚ) : ℝ) ≤
        if ε t ≠ 0 then (M : ℝ) * (2 * (1 / 2 : ℝ) ^ K) else 0 := by
      split_ifs with h
      · have hεu' : (ε t : ℝ) ≤ M * (1 / 2 : ℝ) ^ K := by
          have := (Rat.cast_le (K := ℝ)).mpr hεu
          push_cast at this
          exact this
        push_cast
        calc Real.logb 2 (1 + (ε t : ℝ)) ≤ 2 * (ε t : ℝ) := logb_one_add_le (by exact_mod_cast hε0)
          _ ≤ (M : ℝ) * (2 * (1 / 2 : ℝ) ^ K) := by linarith
      · rw [not_not.mp h]; simp
    linarith
  calc ∑ t ∈ range n, (Real.logb 2 ((1 + ε t : ℚ) : ℝ) - Real.logb 2 (ρ t : ℝ))
      ≤ ∑ t ∈ range n, ((if ρ t ≠ 1 then 3 * (1 / 2 : ℝ) ^ R else 0) +
          (if ε t ≠ 0 then (M : ℝ) * (2 * (1 / 2 : ℝ) ^ K) else 0)) := sum_le_sum hterm
    _ = _ := by
      rw [sum_add_distrib, ← sum_filter, ← sum_filter, sum_const, sum_const, nsmul_eq_mul,
        nsmul_eq_mul]
      ring

end Drift

/-! ## 3. The floor law -/

section Floor

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- [definition] **A context's leader**: the greatest weight, `max_g u(g)`. -/
def leader (u : ι → ℚ) : ℚ := univ.sup' univ_nonempty u

/-- [definition] **The floor**: every member below `2^(−K)` of the leader is held there,
`û(f) = max(u(f), 2^(−K) max_g u(g))` (Rust `local::Rung::receive`, the leader's mantissa at its
exponent less `K`). -/
def floorStep (K : ℕ) (u : ι → ℚ) : ι → ℚ := fun f => max (u f) ((1 / 2 : ℚ) ^ K * leader u)

/-- [definition] **The floor binds** where some member lies below `2^(−K)` of the leader. -/
def floorBinds (K : ℕ) (u : ι → ℚ) : Prop := ∃ f, u f < (1 / 2 : ℚ) ^ K * leader u

/-- [definition] Whether the floor binds is decided member by member. -/
instance (K : ℕ) (u : ι → ℚ) : Decidable (floorBinds K u) := by
  unfold floorBinds; infer_instance

/-- [definition] **The floor's raise** at a tick: `M 2^(−K)` where the floor binds, `0` elsewhere. -/
def floorRaise (K : ℕ) (u : ι → ℚ) : ℚ :=
  if floorBinds K u then Fintype.card ι * (1 / 2 : ℚ) ^ K else 0

/-- [definition] **The floored chart with unrounded products**: the opening `w₀`, then at every tick
each weight times its face, floored. -/
def floorChart (K : ℕ) (w0 : ι → ℚ) (P : ℕ → ι → ℚ) : ℕ → ι → ℚ
  | 0 => w0
  | t + 1 => floorStep K fun f => floorChart K w0 P t f * P t f

/-- [proved-standard; formal-checked] Every weight is at most the leader. -/
theorem le_leader (u : ι → ℚ) (f : ι) : u f ≤ leader u := le_sup' u (mem_univ f)

/-- [proved-standard; formal-checked] Nonnegative weights have a nonnegative leader. -/
theorem leader_nonneg {u : ι → ℚ} (hu : ∀ f, 0 ≤ u f) : 0 ≤ leader u :=
  (hu (Classical.arbitrary ι)).trans (le_leader u _)

/-- [proved-standard; formal-checked] The leader of nonnegative weights is at most their total. -/
theorem leader_le_sum {u : ι → ℚ} (hu : ∀ f, 0 ≤ u f) : leader u ≤ ∑ f, u f :=
  sup'_le _ _ fun f _ => single_le_sum (fun g _ => hu g) (mem_univ f)

/-- [proved-derived; formal-checked] The floor only raises a weight. -/
theorem le_floorStep (K : ℕ) (u : ι → ℚ) (f : ι) : u f ≤ floorStep K u f := le_max_left _ _

/-- [proved-derived; formal-checked] After the floor every weight holds `2^(−K)` of the leader before it. -/
theorem floorStep_floor (K : ℕ) (u : ι → ℚ) (f : ι) :
    (1 / 2 : ℚ) ^ K * leader u ≤ floorStep K u f := le_max_right _ _

/-- [proved-derived; formal-checked] **(a) The floor raises the total by at most `M 2^(−K)` of it**:
`Σ_f û(f) ≤ (1 + M 2^(−K)) Σ_f u(f)`. -/
theorem floor_raise (K : ℕ) {u : ι → ℚ} (hu : ∀ f, 0 ≤ u f) :
    ∑ f, floorStep K u f ≤ (1 + Fintype.card ι * (1 / 2 : ℚ) ^ K) * ∑ f, u f := by
  have hL := leader_nonneg hu
  have hk : (0 : ℚ) ≤ (1 / 2) ^ K := by positivity
  have hterm : ∀ f, floorStep K u f ≤ u f + (1 / 2 : ℚ) ^ K * leader u := fun f =>
    max_le (le_add_of_nonneg_right (mul_nonneg hk hL)) (le_add_of_nonneg_left (hu f))
  calc ∑ f, floorStep K u f ≤ ∑ f, (u f + (1 / 2 : ℚ) ^ K * leader u) :=
        sum_le_sum fun f _ => hterm f
    _ = ∑ f, u f + Fintype.card ι * ((1 / 2 : ℚ) ^ K * leader u) := by
        rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
    _ ≤ ∑ f, u f + Fintype.card ι * ((1 / 2 : ℚ) ^ K * ∑ f, u f) := by
        gcongr
        exact leader_le_sum hu
    _ = (1 + Fintype.card ι * (1 / 2 : ℚ) ^ K) * ∑ f, u f := by ring

/-- [proved-derived; formal-checked] **(a) Where no floor binds, nothing moves**: `û = u`. -/
theorem floor_idle (K : ℕ) {u : ι → ℚ} (h : ¬ floorBinds K u) : floorStep K u = u := by
  funext f
  simp only [floorBinds, not_exists, not_lt] at h
  exact max_eq_left (h f)

/-- [proved-derived; formal-checked] **(a) The raise law at a tick**: `Σ_f û(f) ≤ (1 + ε) Σ_f u(f)`
with `ε` the floor's raise (`M 2^(−K)` where it binds, `0` elsewhere). -/
theorem floor_raise_le (K : ℕ) {u : ι → ℚ} (hu : ∀ f, 0 ≤ u f) :
    ∑ f, floorStep K u f ≤ (1 + floorRaise K u) * ∑ f, u f := by
  unfold floorRaise
  split_ifs with h
  · exact floor_raise K hu
  · rw [floor_idle K h, add_zero, one_mul]

/-- [proved-derived; formal-checked] The floor's raise is nonnegative. -/
theorem floorRaise_nonneg (K : ℕ) (u : ι → ℚ) : 0 ≤ floorRaise K u := by
  unfold floorRaise; split_ifs <;> positivity

/-- [proved-derived; formal-checked] **(b) The leader is unchanged by the floor.** -/
theorem floor_leader (K : ℕ) {u : ι → ℚ} (hu : ∀ f, 0 ≤ u f) :
    leader (floorStep K u) = leader u := by
  have hL := leader_nonneg hu
  have hk : (1 / 2 : ℚ) ^ K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  refine le_antisymm (sup'_le _ _ fun f _ => max_le (le_leader u f) ?_)
    (sup'_le _ _ fun f _ => (le_floorStep K u f).trans (le_leader _ f))
  calc (1 / 2 : ℚ) ^ K * leader u ≤ 1 * leader u := mul_le_mul_of_nonneg_right hk hL
    _ = leader u := one_mul _

/-- [proved-derived; formal-checked] **(c) After the floor every member holds `2^(−K)` of every
member**, so of the leader: the floor hypothesis of `segment_code` holds at every tick. -/
theorem floor_holds (K : ℕ) {u : ι → ℚ} (hu : ∀ f, 0 ≤ u f) (f g : ι) :
    (1 / 2 : ℚ) ^ K * floorStep K u g ≤ floorStep K u f :=
  calc (1 / 2 : ℚ) ^ K * floorStep K u g ≤ (1 / 2 : ℚ) ^ K * leader (floorStep K u) :=
        mul_le_mul_of_nonneg_left (le_leader _ g) (by positivity)
    _ = (1 / 2 : ℚ) ^ K * leader u := by rw [floor_leader K hu]
    _ ≤ floorStep K u f := floorStep_floor K u f

/-- [proved-derived; formal-checked] **(d) Dormant, not dead**: while some member holds a positive
weight, the floor leaves every member positive. -/
theorem floor_keeps_dormant (K : ℕ) {u : ι → ℚ} {g : ι} (hg : 0 < u g) (f : ι) :
    0 < floorStep K u f :=
  lt_of_lt_of_le (mul_pos (by positivity) (lt_of_lt_of_le hg (le_leader u g)))
    (floorStep_floor K u f)

/-- [proved-derived; formal-checked] The floored chart opens at its opening. -/
theorem floorChart_zero (K : ℕ) (w0 : ι → ℚ) (P : ℕ → ι → ℚ) : floorChart K w0 P 0 = w0 := rfl

/-- [proved-derived; formal-checked] The floored chart's step: each weight times its face, floored. -/
theorem floorChart_succ (K : ℕ) (w0 : ι → ℚ) (P : ℕ → ι → ℚ) (t : ℕ) :
    floorChart K w0 P (t + 1) = floorStep K fun f => floorChart K w0 P t f * P t f := rfl

/-- [proved-derived; formal-checked] **The executed chart's laws.** Weights opened at a prior,
multiplied by their faces and rounded down by factors in `[1 − 2^(−R), 1]` (`R ≥ 1`), then floored,
keep positive factors and nonnegative weights, and satisfy the rounding law and the raise law with
`ε_t` the floor's raise. -/
theorem executed_laws {K R : ℕ} (hR : 1 ≤ R) {w P u : ℕ → ι → ℚ} {ρ : ℕ → ℚ}
    (hπ : IsPrior (w 0)) (hP : ∀ t f, 0 < P t f)
    (hρ : ∀ t, 1 - (1 / 2 : ℚ) ^ R ≤ ρ t ∧ ρ t ≤ 1)
    (hu : ∀ t f, ρ t * (w t f * P t f) ≤ u t f ∧ u t f ≤ w t f * P t f)
    (hstep : ∀ t, w (t + 1) = floorStep K (u t)) :
    (∀ t, 0 < ρ t) ∧ (∀ t f, 0 ≤ w t f) ∧ (∀ t f, 0 ≤ u t f) ∧
      (∀ t f, ρ t * (w t f * P t f) ≤ w (t + 1) f) ∧
      ∀ t, chartTotal w (t + 1) ≤ (1 + floorRaise K (u t)) * chartMass w P t := by
  have hhalf : (1 / 2 : ℚ) ^ R ≤ 1 / 2 :=
    calc (1 / 2 : ℚ) ^ R ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hR
      _ = 1 / 2 := by norm_num
  have hρpos : ∀ t, 0 < ρ t := fun t => by linarith [(hρ t).1]
  have hw : ∀ t f, 0 ≤ w t f := by
    intro t
    induction t with
    | zero => exact hπ.1
    | succ t ih =>
      intro f
      rw [hstep]
      exact (mul_nonneg (hρpos t).le (mul_nonneg (ih f) (hP t f).le)).trans
        ((hu t f).1.trans (le_floorStep K _ f))
  have hu0 : ∀ t f, 0 ≤ u t f := fun t f =>
    (mul_nonneg (hρpos t).le (mul_nonneg (hw t f) (hP t f).le)).trans (hu t f).1
  refine ⟨hρpos, hw, hu0, fun t f => ?_, fun t => ?_⟩
  · rw [hstep]; exact (hu t f).1.trans (le_floorStep K _ f)
  · rw [chartTotal, hstep]
    refine (floor_raise_le K (hu0 t)).trans (mul_le_mul_of_nonneg_left ?_ ?_)
    · exact sum_le_sum fun f _ => (hu t f).2
    · linarith [floorRaise_nonneg K (u t)]

/-- [proved-derived; formal-checked] Every executed face is positive. -/
theorem executed_face_pos {K R : ℕ} (hR : 1 ≤ R) {w P u : ℕ → ι → ℚ} {ρ : ℕ → ℚ}
    (hπ : IsPrior (w 0)) (hP : ∀ t f, 0 < P t f)
    (hρ : ∀ t, 1 - (1 / 2 : ℚ) ^ R ≤ ρ t ∧ ρ t ≤ 1)
    (hu : ∀ t f, ρ t * (w t f * P t f) ≤ u t f ∧ u t f ≤ w t f * P t f)
    (hstep : ∀ t, w (t + 1) = floorStep K (u t)) (t : ℕ) : 0 < chartFace w P t := by
  obtain ⟨hρpos, hw, -, hround, -⟩ := executed_laws hR hπ hP hρ hu hstep
  have hW := chartTotal_pos hw hP hρpos hround (by rw [chartTotal, hπ.2]; exact one_pos) t
  exact div_pos (chartMass_pos hw hP hW) hW

variable [DecidableEq ι]

/-- [proved-derived; formal-checked] **`executed_floor_code`: the executed floor's
segment/switching bound** (#410's box). Weights opened at a prior, multiplied by their faces and
rounded down by factors in `[1 − 2^(−R), 1]`, then floored at `2^(−K)` of the leader, code along
every path `σ` with `k` switches before its last tick within
`−log₂ π(σ_0) + Σ_t (−log₂ P_t(σ_t)) + k (K + log₂ M) + 3 r 2^(−R) + M φ 2^(1−K)`, `r` the ticks
that rounded (`ρ_t ≠ 1`) and `φ` those at which a floor bound. -/
theorem executed_floor_code {K R : ℕ} (hR : 1 ≤ R) {w P u : ℕ → ι → ℚ} {ρ : ℕ → ℚ}
    (hπ : IsPrior (w 0)) (hP : ∀ t f, 0 < P t f)
    (hρ : ∀ t, 1 - (1 / 2 : ℚ) ^ R ≤ ρ t ∧ ρ t ≤ 1)
    (hu : ∀ t f, ρ t * (w t f * P t f) ≤ u t f ∧ u t f ≤ w t f * P t f)
    (hstep : ∀ t, w (t + 1) = floorStep K (u t)) (σ : ℕ → ι) (n : ℕ) (h0 : 0 < w 0 (σ 0)) :
    -Real.logb 2 ((∏ t ∈ range n, chartFace w P t : ℚ) : ℝ) ≤
      -Real.logb 2 (w 0 (σ 0) : ℝ) + ∑ t ∈ range n, -Real.logb 2 (P t (σ t) : ℝ) +
        switchCount σ (n - 1) * ((K : ℝ) + Real.logb 2 (Fintype.card ι : ℝ)) +
        (3 * ((range n).filter fun t => ρ t ≠ 1).card * (1 / 2 : ℝ) ^ R +
          Fintype.card ι * ((range n).filter fun t => floorBinds K (u t)).card *
            (2 * (1 / 2 : ℝ) ^ K)) := by
  obtain ⟨hρpos, hw, hu0, hround, hraise⟩ := executed_laws hR hπ hP hρ hu hstep
  have hfloor : ∀ t < n - 1, σ t ≠ σ (t + 1) →
      ∀ g, (1 / 2 : ℚ) ^ K * w (t + 1) g ≤ w (t + 1) (σ (t + 1)) := by
    intro t _ _ g
    rw [hstep]
    exact floor_holds K (hu0 t) _ g
  have hcode := segment_code hw hP hρpos (fun t => floorRaise_nonneg K (u t)) hround hraise σ n
    h0 hfloor
  have hW0 : chartTotal w 0 = 1 := hπ.2
  rw [hW0, div_one] at hcode
  have hdrift := drift_le (M := Fintype.card ι) (K := K) hR (ρ := ρ)
    (ε := fun t => floorRaise K (u t)) n (fun t _ => hρ t) (fun t _ => ⟨floorRaise_nonneg K _, by
      unfold floorRaise; split_ifs
      · exact le_rfl
      · positivity⟩)
  have hfilter : ((range n).filter fun t => floorRaise K (u t) ≠ 0) =
      (range n).filter fun t => floorBinds K (u t) := by
    refine filter_congr fun t _ => ?_
    unfold floorRaise
    split_ifs with h
    · simp only [ne_eq, h, iff_true]
      exact mul_ne_zero (by exact_mod_cast Fintype.card_ne_zero) (by positivity)
    · simp [h]
  rw [hfilter] at hdrift
  linarith

/-- [proved-derived; formal-checked] **The floored chart's code** (`executed_floor_code` with no
rounding, `ρ = 1`): along every path, `−log₂ π(σ_0) + Σ_t (−log₂ P_t(σ_t)) + k (K + log₂ M) +
M φ 2^(1−K)`, `φ` the ticks at which a floor bound. -/
theorem floorChart_code (K : ℕ) {π : ι → ℚ} (hπ : IsPrior π) {P : ℕ → ι → ℚ}
    (hP : ∀ t f, 0 < P t f) (σ : ℕ → ι) (n : ℕ) (h0 : 0 < π (σ 0)) :
    -Real.logb 2 ((∏ t ∈ range n, chartFace (floorChart K π P) P t : ℚ) : ℝ) ≤
      -Real.logb 2 (π (σ 0) : ℝ) + ∑ t ∈ range n, -Real.logb 2 (P t (σ t) : ℝ) +
        switchCount σ (n - 1) * ((K : ℝ) + Real.logb 2 (Fintype.card ι : ℝ)) +
        Fintype.card ι *
          ((range n).filter fun t => floorBinds K fun f => floorChart K π P t f * P t f).card *
            (2 * (1 / 2 : ℝ) ^ K) := by
  have h := executed_floor_code (K := K) (R := 1) le_rfl (w := floorChart K π P) (P := P)
    (u := fun t f => floorChart K π P t f * P t f) (ρ := fun _ => 1) hπ hP
    (fun _ => ⟨by norm_num, le_rfl⟩) (fun t f => ⟨by rw [one_mul], le_rfl⟩)
    (floorChart_succ K π P) σ n h0
  simp only [ne_eq, not_true_eq_false, filter_false, card_empty, Nat.cast_zero, mul_zero,
    zero_mul, zero_add, floorChart_zero] at h
  exact h

end Floor

/-! ## 4–5. Two members exchanged: static Bayes pays what it fell behind, and the floor follows -/

section Witness

/-- [definition] **Two members exchanged on the passage `0^N 1^N`** (`δ = 1/8`): at tick `t` a
member gives the received cell `7/8` where the cell is its own (`true` owns the first segment's
cell, `false` the second's) and `1/8` elsewhere. -/
def swapFace (N : ℕ) : ℕ → Bool → ℚ := fun t f => if f = decide (t < N) then 7 / 8 else 1 / 8

/-- [definition] **The switching path**: `true` on the first `N` ticks, `false` after. -/
def swapPath (N : ℕ) : ℕ → Bool := fun t => decide (t < N)

/-- [proved-derived; formal-checked] Every exchanged face is positive. -/
theorem swapFace_pos (N t : ℕ) (f : Bool) : 0 < swapFace N t f := by
  unfold swapFace; split_ifs <;> norm_num

/-- [proved-derived; formal-checked] The switching path reads `7/8` at every tick. -/
theorem swapFace_path (N t : ℕ) : swapFace N t (swapPath N t) = 7 / 8 := by
  simp [swapFace, swapPath]

/-- [proved-derived; formal-checked] The switching path switches once before its last tick. -/
theorem switchCount_swapPath {N : ℕ} (hN : 1 ≤ N) : switchCount (swapPath N) (2 * N - 1) = 1 := by
  have h : ((range (2 * N - 1)).filter fun t => swapPath N t ≠ swapPath N (t + 1)) = {N - 1} := by
    ext t
    simp only [mem_filter, mem_range, mem_singleton, swapPath, ne_eq, decide_eq_decide]
    omega
  rw [switchCount, h, card_singleton]

/-- [proved-derived; formal-checked] **Each member alone** codes the passage at
`(7/8)^N (1/8)^N = (7/64)^N`. -/
theorem swap_member_lik (N : ℕ) (f : Bool) :
    seqLik (fun t => swapFace N t f) (2 * N) = (7 / 64) ^ N := by
  unfold seqLik
  rw [two_mul, prod_range_add]
  have h1 : ∏ t ∈ range N, swapFace N t f = (if f = true then (7 / 8 : ℚ) else 1 / 8) ^ N := by
    rw [prod_congr rfl fun t ht => (show swapFace N t f = if f = true then 7 / 8 else 1 / 8 by
      simp [swapFace, mem_range.mp ht]), prod_const, card_range]
  have h2 : ∏ t ∈ range N, swapFace N (N + t) f =
      (if f = false then (7 / 8 : ℚ) else 1 / 8) ^ N := by
    rw [prod_congr rfl fun t _ => (show swapFace N (N + t) f = if f = false then 7 / 8 else 1 / 8 by
      simp [swapFace]), prod_const, card_range]
  rw [h1, h2]
  cases f <;> simp only [Bool.false_eq_true, if_false, if_true] <;> rw [← mul_pow] <;> norm_num

/-- [proved-derived; formal-checked] **The static mixture** at `½/½` (`LocalWeighing.static_mixture`)
codes the passage as each member does: its product is `(7/64)^N`. -/
theorem swap_static (N : ℕ) :
    ∏ t ∈ range (2 * N), fwdMix halfPrior (fun f t => swapFace N t f) idKernel t =
      (7 / 64) ^ N := by
  rw [(static_mixture halfPrior_isPrior (fun x t => swapFace_pos N t x) (2 * N)).2.1]
  simp only [Fintype.sum_bool, swap_member_lik, halfPrior]
  ring

/-- [proved-standard; formal-checked] `(7/64)^N` reads `2N log₂(8/7) + N log₂ 7` bits. -/
theorem swap_code (N : ℕ) :
    -Real.logb 2 ((((7 : ℚ) / 64) ^ N : ℚ) : ℝ) = 2 * N * Real.logb 2 (8 / 7) + N * Real.logb 2 7 := by
  have e : ((((7 : ℚ) / 64) ^ N : ℚ) : ℝ) = (((8 : ℝ) / 7) ^ 2 * 7)⁻¹ ^ N := by
    push_cast; norm_num
  rw [e, Real.logb_pow, Real.logb_inv, Real.logb_mul (by norm_num) (by norm_num), Real.logb_pow]
  push_cast
  ring

/-- [proved-derived; formal-checked] **The floored chart on the exchanged passage** codes within
`2N log₂(8/7) + K + 2 + 8N 2^(−K)`: one switch at `K + log₂ 2`, the opening's bit, and the floor's
raise at most `2·2N·2^(1−K)`. -/
theorem swap_floored_code (K : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    -Real.logb 2 ((∏ t ∈ range (2 * N),
        chartFace (floorChart K halfPrior (swapFace N)) (swapFace N) t : ℚ) : ℝ) ≤
      2 * N * Real.logb 2 (8 / 7) + (K + 2) + 8 * N * (1 / 2 : ℝ) ^ K := by
  have h := floorChart_code K halfPrior_isPrior (fun t f => swapFace_pos N t f) (swapPath N) (2 * N)
    (by norm_num [halfPrior])
  rw [switchCount_swapPath hN] at h
  simp only [swapFace_path, sum_const, card_range, nsmul_eq_mul, Fintype.card_bool] at h
  have hφ := (card_filter_le (range (2 * N))
    fun t => floorBinds K fun f => floorChart K halfPrior (swapFace N) t f * swapFace N t f).trans
      (card_range (2 * N)).le
  have hφ' : (((range (2 * N)).filter
      fun t => floorBinds K fun f => floorChart K halfPrior (swapFace N) t f * swapFace N t f).card
        : ℝ) ≤ 2 * N := by exact_mod_cast hφ
  have e1 : -Real.logb 2 (((7 / 8 : ℚ) : ℝ)) = Real.logb 2 (8 / 7) := by
    rw [show ((7 / 8 : ℚ) : ℝ) = ((8 : ℝ) / 7)⁻¹ by norm_num, Real.logb_inv, neg_neg]
  have e2 : -Real.logb 2 ((halfPrior (swapPath N 0) : ℚ) : ℝ) = 1 := by
    simp only [halfPrior]
    rw [show ((1 / 2 : ℚ) : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.logb_inv,
      Real.logb_self_eq_one (by norm_num), neg_neg]
  have e3 : Real.logb 2 ((2 : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_ofNat, Real.logb_self_eq_one (by norm_num)]
  rw [e1, e2, e3] at h
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h
  have hk : (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ K := by positivity
  have := mul_le_mul_of_nonneg_right hφ' hk
  linarith

/-- [proved-derived; formal-checked] **Static Bayes pays what it fell behind.** On `0^N 1^N` with
the two members exchanged, each member and the static mixture code `2N log₂(8/7) + N log₂ 7` bits,
and the floored chart codes at least `N log₂ 7 − (K + 2) − 8N 2^(−K)` bits fewer: without the floor
the second member, `N log₂ 7` bits behind after the first segment, pays all of it back. -/
theorem static_bayes_pays_what_it_fell_behind (K : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    (∀ f, seqLik (fun t => swapFace N t f) (2 * N) = (7 / 64) ^ N) ∧
      ∏ t ∈ range (2 * N), fwdMix halfPrior (fun f t => swapFace N t f) idKernel t =
        (7 / 64) ^ N ∧
      -Real.logb 2 ((∏ t ∈ range (2 * N),
          fwdMix halfPrior (fun f t => swapFace N t f) idKernel t : ℚ) : ℝ) =
        2 * N * Real.logb 2 (8 / 7) + N * Real.logb 2 7 ∧
      N * Real.logb 2 7 - (K + 2) - 8 * N * (1 / 2 : ℝ) ^ K ≤
        -Real.logb 2 ((∏ t ∈ range (2 * N),
            fwdMix halfPrior (fun f t => swapFace N t f) idKernel t : ℚ) : ℝ) -
          -Real.logb 2 ((∏ t ∈ range (2 * N),
            chartFace (floorChart K halfPrior (swapFace N)) (swapFace N) t : ℚ) : ℝ) := by
  have hcode : -Real.logb 2 ((∏ t ∈ range (2 * N),
      fwdMix halfPrior (fun f t => swapFace N t f) idKernel t : ℚ) : ℝ) =
        2 * N * Real.logb 2 (8 / 7) + N * Real.logb 2 7 := by
    rw [swap_static, swap_code]
  refine ⟨swap_member_lik N, swap_static N, hcode, ?_⟩
  have := swap_floored_code K hN
  rw [hcode]
  linarith

/-- [proved-derived; formal-checked] **The floored mixture can code below its best single member**,
which no static mixture does (`Σ_f π_f L_f ≤ max_f L_f`): on the exchanged passage, wherever
`K + 2 + 8N 2^(−K) < N log₂ 7`, the floored chart codes strictly below each member. -/
theorem floored_below_best_member (K : ℕ) {N : ℕ} (hN : 1 ≤ N)
    (hgap : (K + 2 : ℝ) + 8 * N * (1 / 2 : ℝ) ^ K < N * Real.logb 2 7) (f : Bool) :
    -Real.logb 2 ((∏ t ∈ range (2 * N),
        chartFace (floorChart K halfPrior (swapFace N)) (swapFace N) t : ℚ) : ℝ) <
      -Real.logb 2 ((seqLik (fun t => swapFace N t f) (2 * N) : ℚ) : ℝ) := by
  rw [swap_member_lik, swap_code]
  have := swap_floored_code K hN
  linarith

/-- [proved-standard; formal-checked] On two members the leader is the larger weight. -/
theorem leader_bool (u : Bool → ℚ) : leader u = max (u true) (u false) := by
  refine le_antisymm (sup'_le _ _ fun b _ => ?_) (max_le (le_leader u true) (le_leader u false))
  cases b
  · exact le_max_right _ _
  · exact le_max_left _ _

/-- [proved-derived; formal-checked] The floored weights at `N = 2`, `K = 2` after one tick:
`(7/16, 7/64)`, the second member raised to the floor. -/
theorem swap_weights_one :
    floorChart 2 halfPrior (swapFace 2) 1 = fun f => if f then 7 / 16 else 7 / 64 := by
  rw [floorChart_succ, floorChart_zero]
  funext f
  cases f <;> simp [floorStep, leader_bool, halfPrior, swapFace] <;> norm_num [max_def]

/-- [proved-derived; formal-checked] After two ticks: `(49/128, 49/512)`, held at the floor. -/
theorem swap_weights_two :
    floorChart 2 halfPrior (swapFace 2) 2 = fun f => if f then 49 / 128 else 49 / 512 := by
  rw [floorChart_succ, swap_weights_one]
  funext f
  cases f <;> simp [floorStep, leader_bool, swapFace] <;> norm_num [max_def]

/-- [proved-derived; formal-checked] After three ticks, on the second segment:
`(49/1024, 343/4096)`, the second member leading and no floor binding. -/
theorem swap_weights_three :
    floorChart 2 halfPrior (swapFace 2) 3 = fun f => if f then 49 / 1024 else 343 / 4096 := by
  rw [floorChart_succ, swap_weights_two]
  funext f
  cases f <;> simp [floorStep, leader_bool, swapFace] <;> norm_num [max_def]

/-- [proved-derived; formal-checked] **A computed witness** at `N = 2`, `K = 2`: the floored chart's
faces `1/2, 29/40, 11/40, 53/88` multiply to `1537/25600`, above each member's and the static
mixture's `49/4096`; in bits the floored chart codes below its best single member. -/
theorem floored_codes_below_every_member :
    ∏ t ∈ range 4, chartFace (floorChart 2 halfPrior (swapFace 2)) (swapFace 2) t =
        1537 / 25600 ∧
      (∀ f, seqLik (fun t => swapFace 2 t f) 4 = 49 / 4096) ∧
      ∏ t ∈ range 4, fwdMix halfPrior (fun f t => swapFace 2 t f) idKernel t = 49 / 4096 ∧
      ∀ f, -Real.logb 2 ((∏ t ∈ range 4,
          chartFace (floorChart 2 halfPrior (swapFace 2)) (swapFace 2) t : ℚ) : ℝ) <
        -Real.logb 2 ((seqLik (fun t => swapFace 2 t f) 4 : ℚ) : ℝ) := by
  have hprod : ∏ t ∈ range 4, chartFace (floorChart 2 halfPrior (swapFace 2)) (swapFace 2) t =
      1537 / 25600 := by
    simp only [prod_range_succ, range_zero, prod_empty, one_mul, chartFace, chartMass, chartTotal,
      Fintype.sum_bool]
    rw [floorChart_zero, swap_weights_one, swap_weights_two, swap_weights_three]
    norm_num [halfPrior, swapFace]
  have hlik : ∀ f, seqLik (fun t => swapFace 2 t f) 4 = 49 / 4096 := fun f => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, swap_member_lik]; norm_num
  refine ⟨hprod, hlik, by rw [show (4 : ℕ) = 2 * 2 from rfl, swap_static]; norm_num, fun f => ?_⟩
  rw [hprod, hlik]
  have := Real.logb_lt_logb (b := 2) (by norm_num) (by norm_num : (0 : ℝ) < ((49 / 4096 : ℚ) : ℝ))
    (by norm_num : ((49 / 4096 : ℚ) : ℝ) < ((1537 / 25600 : ℚ) : ℝ))
  linarith

end Witness

/-! ## 6. The uniform prior: each context pays its best member and `log₂ M` -/

section Uniform

variable {ι : Type*} [Fintype ι]

/-- [proved-derived; formal-checked] **A uniform opening pays `log₂ M`**: with every opening weight
`a > 0`, `−log₂(w_0(f)/W_0) = log₂ M`. -/
theorem uniform_opening_code {w : ℕ → ι → ℚ} {a : ℚ} (ha : 0 < a) (hw0 : ∀ f, w 0 f = a) (f : ι) :
    -Real.logb 2 ((w 0 f / chartTotal w 0 : ℚ) : ℝ) = Real.logb 2 (Fintype.card ι : ℝ) := by
  have hM : (Fintype.card ι : ℚ) ≠ 0 := by exact_mod_cast (Fintype.card_pos_iff.mpr ⟨f⟩).ne'
  have e : w 0 f / chartTotal w 0 = (Fintype.card ι : ℚ)⁻¹ := by
    simp only [chartTotal, hw0, sum_const, card_univ, nsmul_eq_mul]
    field_simp
  rw [e, Rat.cast_inv, Real.logb_inv, neg_neg, Rat.cast_natCast]

/-- [proved-derived; formal-checked] **Item 1 at `k = 0` under a uniform opening**: one context's
executed code is at most its best member's code plus `log₂ M` plus the drift,
`−log₂ ∏ q̂ ≤ min_f Σ_t (−log₂ P_t(f)) + log₂ M + Σ_t (log₂(1 + ε_t) − log₂ ρ_t)`. -/
theorem uniform_best_member_code [DecidableEq ι] [Nonempty ι] {w P : ℕ → ι → ℚ} {ρ ε : ℕ → ℚ}
    {a : ℚ} (hw : ∀ t f, 0 ≤ w t f) (hP : ∀ t f, 0 < P t f) (hρ : ∀ t, 0 < ρ t)
    (hε : ∀ t, 0 ≤ ε t) (hround : ∀ t f, ρ t * (w t f * P t f) ≤ w (t + 1) f)
    (hraise : ∀ t, chartTotal w (t + 1) ≤ (1 + ε t) * chartMass w P t)
    (ha : 0 < a) (hw0 : ∀ f, w 0 f = a) (n : ℕ) :
    -Real.logb 2 ((∏ t ∈ range n, chartFace w P t : ℚ) : ℝ) ≤
      univ.inf' univ_nonempty (fun f => ∑ t ∈ range n, -Real.logb 2 (P t f : ℝ)) +
        Real.logb 2 (Fintype.card ι : ℝ) +
        ∑ t ∈ range n, (Real.logb 2 ((1 + ε t : ℚ) : ℝ) - Real.logb 2 (ρ t : ℝ)) := by
  obtain ⟨f, -, hf⟩ := exists_mem_eq_inf' (univ_nonempty (α := ι))
    (fun f => ∑ t ∈ range n, -Real.logb 2 (P t f : ℝ))
  have h := segment_code (K := 0) hw hP hρ hε hround hraise (fun _ => f) n (by rw [hw0]; exact ha)
    (fun t _ hs => absurd rfl hs)
  have hk : switchCount (fun _ : ℕ => f) (n - 1) = 0 := by simp [switchCount]
  rw [hk, uniform_opening_code ha hw0 f] at h
  rw [hf]
  simp only [Nat.cast_zero, zero_mul, add_zero] at h
  linarith

/-- [proved-derived; formal-checked] **The local mixture under the uniform prior** (the atlas row's
"not in Lean" clause, from `Population.local_mixture_code`): each context met pays its best
member's code there and `log₂ M`,
`−log₂ ∏_(t<n) q_t ≤ Σ_(c met) (min_f code_f(c) + log₂ M)`, `code_f(c) = −log₂ L_f(c, n)`. -/
theorem uniform_local_mixture_code {C : Type*} [Fintype C] [DecidableEq C] [Nonempty ι]
    {f : ι → ℕ → ℚ} (hf : ∀ x t, 0 < f x t) (γ : ℕ → C) (n : ℕ) :
    -Real.logb 2 ((∏ t ∈ range n, localFace uniformPrior f γ t : ℚ) : ℝ) ≤
      ∑ c ∈ (range n).image γ,
        (univ.inf' univ_nonempty (fun x => -Real.logb 2 (ctxLik (f x) γ c n : ℝ)) +
          Real.logb 2 (Fintype.card ι : ℝ)) := by
  have hmin : ∀ c : C, ∃ x ∈ (univ : Finset ι),
      univ.inf' univ_nonempty (fun x => -Real.logb 2 (ctxLik (f x) γ c n : ℝ)) =
        -Real.logb 2 (ctxLik (f x) γ c n : ℝ) := fun c =>
    exists_mem_eq_inf' univ_nonempty _
  choose g _ hg using hmin
  have hM : (0 : ℚ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hπ : ∀ c, 0 < uniformPrior (κ := ι) (g c) := fun c => by
    unfold uniformPrior; positivity
  have hcode := local_mixture_code uniformPrior_isPrior hf γ n g hπ
  refine hcode.trans (le_of_eq (sum_congr rfl fun c _ => ?_))
  rw [hg c]
  have e : -Real.logb 2 ((uniformPrior (κ := ι) (g c) : ℚ) : ℝ) = Real.logb 2 (Fintype.card ι : ℝ) := by
    unfold uniformPrior
    rw [one_div, Rat.cast_inv, Real.logb_inv, neg_neg, Rat.cast_natCast]
  linarith

/-- [proved-standard; formal-checked] **The code splits by context**: the passage's code is the sum
over the contexts met of the code of each context's own faces. -/
theorem code_splits_by_context {C : Type*} [DecidableEq C] {q : ℕ → ℚ} (hq : ∀ t, 0 < q t)
    (γ : ℕ → C) (n : ℕ) :
    -Real.logb 2 ((∏ t ∈ range n, q t : ℚ) : ℝ) =
      ∑ c ∈ (range n).image γ,
        -Real.logb 2 ((∏ t ∈ (range n).filter (fun t => γ t = c), q t : ℚ) : ℝ) := by
  rw [← prod_fiberwise_of_maps_to (fun t ht => mem_image_of_mem γ ht) q,
    logb_cast_prod fun c _ => prod_pos fun t _ => hq t, sum_neg_distrib]

end Uniform

/-! ## 7. The floored local mixture: each context runs the floor on its own clock -/

section Local

variable {C : Type*} [DecidableEq C]

/-- [definition] **A context's own clock**: tick `t` is the `ctxClock γ t`-th tick of its context
`γ t`, the count of the earlier ticks the gating map places there. -/
def ctxClock (γ : ℕ → C) (t : ℕ) : ℕ := ((range t).filter fun s => γ s = γ t).card

/-- [definition] **A context's ticks** before `n`: `#{t < n : γ t = c}`. -/
def ctxTicks (γ : ℕ → C) (c : C) (n : ℕ) : ℕ := ((range n).filter fun t => γ t = c).card

/-- [proved-derived; formal-checked] **A context's ticks, read on its own clock**: the passage's
ticks in context `c` are its clock's first `ctxTicks γ c n` ticks, in order,
`∏_(t<n, γ t = c) g(ctxClock γ t) = ∏_(j < ctxTicks γ c n) g(j)`. -/
theorem prod_fiber_clock (γ : ℕ → C) (c : C) (g : ℕ → ℚ) (n : ℕ) :
    ∏ t ∈ (range n).filter (fun t => γ t = c), g (ctxClock γ t) =
      ∏ j ∈ range (ctxTicks γ c n), g j := by
  induction n with
  | zero => simp [ctxTicks]
  | succ n ih =>
    unfold ctxTicks at ih ⊢
    rw [range_add_one, filter_insert]
    split_ifs with h
    · rw [prod_insert (by simp), card_insert_of_notMem (by simp), prod_range_succ, ih, mul_comm]
      congr 2
      unfold ctxClock
      rw [h]
    · exact ih

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- [proved-derived; formal-checked] **`floored_local_code`: the local mixture's executed code is
the sum of its contexts' segment/switching bounds.** Each context `c` met runs the executed chart on
its own clock (its prior, its faces `P_c`, roundings `ρ_c` and floor) and the passage's face at tick
`t` is its context's executed face at its own tick; then for every choice of a path `σ_c` per
context, `−log₂ ∏_(t<n) q̂_t ≤ Σ_(c met) (−log₂ π_c(σ_c(0)) + Σ_(j<n_c) (−log₂ P_c(j, σ_c(j)))
+ k_c (K + log₂ M) + 3 r_c 2^(−R) + M φ_c 2^(1−K))`, `n_c` the context's ticks. -/
theorem floored_local_code {K R : ℕ} (hR : 1 ≤ R) (γ : ℕ → C) {w P u : C → ℕ → ι → ℚ}
    {ρ : C → ℕ → ℚ} (hπ : ∀ c, IsPrior (w c 0)) (hP : ∀ c t f, 0 < P c t f)
    (hρ : ∀ c t, 1 - (1 / 2 : ℚ) ^ R ≤ ρ c t ∧ ρ c t ≤ 1)
    (hu : ∀ c t f, ρ c t * (w c t f * P c t f) ≤ u c t f ∧ u c t f ≤ w c t f * P c t f)
    (hstep : ∀ c t, w c (t + 1) = floorStep K (u c t)) (σ : C → ℕ → ι)
    (h0 : ∀ c, 0 < w c 0 (σ c 0)) (n : ℕ) :
    -Real.logb 2 ((∏ t ∈ range n, chartFace (w (γ t)) (P (γ t)) (ctxClock γ t) : ℚ) : ℝ) ≤
      ∑ c ∈ (range n).image γ,
        (-Real.logb 2 (w c 0 (σ c 0) : ℝ) +
          ∑ j ∈ range (ctxTicks γ c n), -Real.logb 2 (P c j (σ c j) : ℝ) +
          switchCount (σ c) (ctxTicks γ c n - 1) * ((K : ℝ) + Real.logb 2 (Fintype.card ι : ℝ)) +
          (3 * ((range (ctxTicks γ c n)).filter fun j => ρ c j ≠ 1).card * (1 / 2 : ℝ) ^ R +
            Fintype.card ι * ((range (ctxTicks γ c n)).filter fun j => floorBinds K (u c j)).card *
              (2 * (1 / 2 : ℝ) ^ K))) := by
  have hq : ∀ t, 0 < chartFace (w (γ t)) (P (γ t)) (ctxClock γ t) := fun t =>
    executed_face_pos hR (hπ (γ t)) (hP (γ t)) (hρ (γ t)) (hu (γ t)) (hstep (γ t)) _
  rw [code_splits_by_context hq γ n]
  refine sum_le_sum fun c _ => ?_
  have hfib : ∏ t ∈ (range n).filter (fun t => γ t = c),
      chartFace (w (γ t)) (P (γ t)) (ctxClock γ t) =
        ∏ j ∈ range (ctxTicks γ c n), chartFace (w c) (P c) j := by
    rw [← prod_fiber_clock γ c (chartFace (w c) (P c)) n]
    exact prod_congr rfl fun t ht => by rw [(mem_filter.mp ht).2]
  rw [hfib]
  exact executed_floor_code hR (hπ c) (hP c) (hρ c) (hu c) (hstep c) (σ c) _ (h0 c)

end Local

end Holonics.Compression.Landmark.FlooredSwitching
