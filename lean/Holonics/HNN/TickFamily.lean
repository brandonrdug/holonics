import Holonics.HNN.CarriedStanding

/-!
# HNN.TickFamily: the word's laws for a block operator family indexed by the tick

[definition] #62 (5975321323, item 1; `HNN/CarriedStanding`, model limit 2). The laws of
`HNN/Propagation` and `HNN/Retention` take one block operator `T` for every tick of a word. The Rust
word is not time-invariant on a ring with a pumped resonator: the pump's phase is the tick since the
refinement opened, modulo the step's order (`hnn::ring::PumpDeclaration::phase_at`,
`hnn::word::Word::opened_at`), and it moves the element edge `g → g` of that ring each tick. Here
the word runs a family `T : ℕ → BlockOp`, `x_(k+1) = T_k x_k` (`trajectoryAt`), with no relation
assumed between ticks; the time-invariant word is the constant family (`trajectoryAt_const`).

[proved-derived; formal-checked] What is proved, for any family whose every tick is sparse on the
declared block graph.

1. **The causal cone** (`trajectoryAt_causal_cone`): a change on `S` lies, after `t` ticks, within
   `t` hops of `S`.
2. **The exact variation** (`word_variation_at`, Duhamel's formula): for two families on one open
   state, `⟨g, x′_t⟩ − ⟨g, x_t⟩ = Σ_(k<t) ⟨g, Φ′_(t←k+1) (T′_k − T_k) x_k⟩`, where `Φ′_(t←k+1)` is the
   primed word run from tick `k + 1` to `t` (`shiftOp`).
3. **Release past the space-time diamond** (`release_past_diamond_at`,
   `release_past_diamond_static`): two families that agree at tick `k` on every edge `z → y` with
   `r_z ≤ k` and `o_y ≤ e_last − 1 − k` (`InDiamondAt`) give every reading supported on the
   receivers at every epoch `t ≤ e_last` the same value, and the trajectory agrees at tick `k` on
   every block that observes a receiver within `e_last − k` hops
   (`trajectoryAt_agrees_where_observed`). The static diamond `r_z + 1 + o_y ≤ e_last` of
   `Propagation.release_past_diamond` contains every tick's space-time diamond.
4. **The walk laws** (`trajectoryAt_agrees_on_walk`, `readings_agree_on_walk`): families that agree
   at every tick on every edge a walk from `S` to `R` passes keep a change on the reached blocks
   that agrees on the observing ones, at every tick and every epoch, with no bound on the word's
   length.
5. **The return** (`sweepAt`, `sweepAt_pairing`, `sweepAt_agrees_on_walk`): the reading covector
   swept back through the duals of the ticks in reverse order pairs exactly with the trajectory,
   `⟨λ_n, x_(t−n)⟩ = ⟨g, x_t⟩`, and it agrees on the reached blocks under the walk agreement.
6. **The deposit's data** (`depositDataAt`, `depositDataAt_agree`, `depositDataAt_const`): on an edge
   the data are the features `x_k(z)` and the covectors swept back to tick `k + 1` in the edge's
   window; they agree on every walk edge under the walk agreement, and the constant family gives
   `Retention.depositData`.

Every law here holds for any tick dependence. The pumped ring's moves only its element edge, and
the edge is read by its ring's element (`LocusMap.Reads`), so its pump phase enters the laws only
through which tick the word is at.

The resident's standing law with a tick-indexed word and shared loci is `HNN/TickStanding`; the
resonator's operand on the loaded ring, its pump phase family and its release are `HNN/LoadedRing`.

`HNN/Propagation`, `HNN/Retention` and `HNN/CarriedStanding` are unchanged. No `sorry`, no `axiom`,
no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.TickFamily

open Holonics.HNN.Propagation Holonics.HNN.Retention Holonics.HNN.CarriedStanding
open scoped BigOperators

section Family

variable {B : Type*} [Fintype B] {adj : B → B → Prop}
variable {K : Type*} [Field K] {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]

/-- [definition] **The word's trajectory under a tick-indexed family**: `x_0 = x₀` and
`x_(k+1) = T_k x_k`. -/
def trajectoryAt (T : ℕ → BlockOp K M) (x₀ : (b : B) → M b) : ℕ → (b : B) → M b
  | 0 => x₀
  | k + 1 => tick (T k) (trajectoryAt T x₀ k)

/-- [definition] The family read from tick `s` on. -/
def shiftOp (T : ℕ → BlockOp K M) (s : ℕ) : ℕ → BlockOp K M := fun k => T (s + k)

omit [Fintype B] in
theorem shiftOp_zero (T : ℕ → BlockOp K M) : shiftOp T 0 = T := by
  funext k
  simp [shiftOp]

omit [Fintype B] in
theorem shiftOp_shiftOp (T : ℕ → BlockOp K M) (s s' : ℕ) :
    shiftOp (shiftOp T s) s' = shiftOp T (s + s') := by
  funext k
  simp [shiftOp, Nat.add_assoc]

/-- [proved-derived; formal-checked] The constant family is the time-invariant word. -/
theorem trajectoryAt_const (T : BlockOp K M) (x₀ : (b : B) → M b) (t : ℕ) :
    trajectoryAt (fun _ => T) x₀ t = trajectory T x₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change tick T (trajectoryAt (fun _ => T) x₀ t) = tick T (trajectory T x₀ t)
    rw [ih]

/-- [proved-derived; formal-checked] Running `s` ticks and then `n` more is running `s + n`. -/
theorem trajectoryAt_shift (T : ℕ → BlockOp K M) (x₀ : (b : B) → M b) (s n : ℕ) :
    trajectoryAt (shiftOp T s) (trajectoryAt T x₀ s) n = trajectoryAt T x₀ (s + n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change tick (T (s + n)) (trajectoryAt (shiftOp T s) (trajectoryAt T x₀ s) n) =
      tick (T (s + n)) (trajectoryAt T x₀ (s + n))
    rw [ih]

theorem trajectoryAt_sub (T : ℕ → BlockOp K M) (x x' : (b : B) → M b) (t : ℕ) :
    trajectoryAt T x t - trajectoryAt T x' t = trajectoryAt T (x - x') t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext y
    simp only [trajectoryAt, tick, Pi.sub_apply, ← ih, map_sub, Finset.sum_sub_distrib]

theorem pair_sub' (g : (b : B) → Module.Dual K (M b)) (x x' : (b : B) → M b) :
    pair g x - pair g x' = pair g (x - x') := by
  simp only [pair, Pi.sub_apply, map_sub, Finset.sum_sub_distrib]

/-- [proved-derived; formal-checked] **The causal cone** of a tick-indexed word. -/
theorem trajectoryAt_causal_cone {T : ℕ → BlockOp K M} (hT : ∀ k, Sparse adj (T k))
    {x₀ : (b : B) → M b} {S : Set B} (hx : SupportedIn x₀ S) (t : ℕ) :
    SupportedIn (trajectoryAt T x₀ t) (reachWithin adj S t) := by
  induction t with
  | zero =>
    intro b hb
    exact hx b fun hbS => hb ⟨b, hbS, 0, le_rfl, ReachIn.refl b⟩
  | succ t ih =>
    intro y hy
    change ∑ z, T t y z (trajectoryAt T x₀ t z) = 0
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hz : z ∈ reachWithin adj S t
    · have hnadj : ¬ adj z y := fun h => hy (reachWithin_step hz h)
      rw [hT t y z hnadj, LinearMap.zero_apply]
    · rw [ih z hz, map_zero]

/-- [proved-derived; formal-checked] **The exact variation of a tick-indexed word** (Duhamel's
formula). For two families on one open state, a reading changes by exactly
`⟨g, x′_t⟩ − ⟨g, x_t⟩ = Σ_(k<t) ⟨g, Φ′_(t←k+1) (T′_k − T_k) x_k⟩`: the difference of the two ticks
at `k`, applied to the unprimed word's own state at `k`, run on by the primed word to `t`. -/
theorem word_variation_at (T' T : ℕ → BlockOp K M) (x₀ : (b : B) → M b)
    (g : (b : B) → Module.Dual K (M b)) (t : ℕ) :
    pair g (trajectoryAt T' x₀ t) - pair g (trajectoryAt T x₀ t) =
      ∑ k ∈ Finset.range t, pair g (trajectoryAt (shiftOp T' (k + 1))
        (tick (opSub (T' k) (T k)) (trajectoryAt T x₀ k)) (t - 1 - k)) := by
  set D : ℕ → K := fun k =>
    pair g (trajectoryAt (shiftOp T' k) (trajectoryAt T x₀ k) (t - k)) with hDdef
  have hD : ∀ k < t, D k - D (k + 1) = pair g (trajectoryAt (shiftOp T' (k + 1))
      (tick (opSub (T' k) (T k)) (trajectoryAt T x₀ k)) (t - 1 - k)) := by
    intro k hkt
    have h1 : trajectoryAt (shiftOp T' k) (trajectoryAt T x₀ k) (t - k) =
        trajectoryAt (shiftOp T' (k + 1)) (tick (T' k) (trajectoryAt T x₀ k)) (t - 1 - k) := by
      rw [show t - k = 1 + (t - 1 - k) by omega,
        ← trajectoryAt_shift (shiftOp T' k) (trajectoryAt T x₀ k) 1 (t - 1 - k), shiftOp_shiftOp]
      rfl
    have h2 : trajectoryAt (shiftOp T' (k + 1)) (trajectoryAt T x₀ (k + 1)) (t - (k + 1)) =
        trajectoryAt (shiftOp T' (k + 1)) (tick (T k) (trajectoryAt T x₀ k)) (t - 1 - k) := by
      rw [show t - (k + 1) = t - 1 - k by omega]
      rfl
    simp only [hDdef]
    rw [h1, h2, pair_sub', trajectoryAt_sub, tick_opSub]
    rfl
  have h0 : D 0 = pair g (trajectoryAt T' x₀ t) := by
    simp only [hDdef, Nat.sub_zero, shiftOp_zero]
    rfl
  have ht : D t = pair g (trajectoryAt T x₀ t) := by
    simp only [hDdef, Nat.sub_self]
    rfl
  rw [← h0, ← ht, ← Finset.sum_range_sub']
  exact Finset.sum_congr rfl fun k hk => hD k (Finset.mem_range.mp hk)

variable (adj) in
/-- [definition] **The edge `z → y` at tick `k` lies in the space-time diamond** of the sources `S`,
the receivers `R` and the last epoch `e_last`: its input can be nonzero (`r_z ≤ k`) and its output
can still be read (`o_y ≤ e_last − 1 − k`). -/
def InDiamondAt (S R : Set B) (eLast k : ℕ) (z y : B) : Prop :=
  z ∈ reachWithin adj S k ∧ Observes adj R y (eLast - 1 - k)

omit [Fintype B] in
/-- [proved-derived; formal-checked] Every tick's space-time diamond lies in the static diamond. -/
theorem inDiamond_of_inDiamondAt {S R : Set B} {eLast k : ℕ} (hk : k < eLast) {z y : B}
    (h : InDiamondAt adj S R eLast k z y) : InDiamond adj S R eLast z y :=
  ⟨k, eLast - 1 - k, h.1, h.2, by omega⟩

/-- [proved-derived; formal-checked] **The trajectory agrees wherever it is still observed.** If two
tick-indexed families agree at each tick `k < e_last` on that tick's space-time diamond, the change
at block `z` and tick `k ≤ e_last` agrees whenever `z` observes a receiver within `e_last − k`
hops. -/
theorem trajectoryAt_agrees_where_observed {T T' : ℕ → BlockOp K M} (hT : ∀ k, Sparse adj (T k))
    (hT' : ∀ k, Sparse adj (T' k)) {x₀ : (b : B) → M b} {S R : Set B} (hx : SupportedIn x₀ S)
    {eLast : ℕ} (hagree : ∀ k < eLast, ∀ y z, InDiamondAt adj S R eLast k z y → T' k y z = T k y z)
    (k : ℕ) (hk : k ≤ eLast) (z : B) (hz : Observes adj R z (eLast - k)) :
    trajectoryAt T' x₀ k z = trajectoryAt T x₀ k z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    change ∑ w, T' k z w (trajectoryAt T' x₀ k w) = ∑ w, T k z w (trajectoryAt T x₀ k w)
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hadj : adj w z
    · have hw : Observes adj R w (eLast - k) := by
        have := observes_step hadj hz
        rwa [show eLast - (k + 1) + 1 = eLast - k by omega] at this
      rw [ih (by omega) w hw]
      by_cases hr : w ∈ reachWithin adj S k
      · rw [hagree k (by omega) z w ⟨hr, by rwa [show eLast - 1 - k = eLast - (k + 1) by omega]⟩]
      · rw [trajectoryAt_causal_cone hT hx k w hr, map_zero, map_zero]
    · rw [hT k z w hadj, hT' k z w hadj, LinearMap.zero_apply, LinearMap.zero_apply]

/-- [proved-derived; formal-checked] **An operator outside the space-time diamond changes no
admitted reading** (`Propagation.release_past_diamond` for a tick-indexed word). Two families that
agree at each tick `k < e_last` on every edge of that tick's space-time diamond give every reading
supported on the receivers the same value at every epoch `t ≤ e_last`, whatever they do elsewhere,
the pumped edges included. -/
theorem release_past_diamond_at {T T' : ℕ → BlockOp K M} (hT : ∀ k, Sparse adj (T k))
    (hT' : ∀ k, Sparse adj (T' k)) {x₀ : (b : B) → M b} {g : (b : B) → Module.Dual K (M b)}
    {S R : Set B} (hx : SupportedIn x₀ S) (hg : SupportedIn g R) {eLast t : ℕ} (ht : t ≤ eLast)
    (hagree : ∀ k < eLast, ∀ y z, InDiamondAt adj S R eLast k z y → T' k y z = T k y z) :
    pair g (trajectoryAt T' x₀ t) = pair g (trajectoryAt T x₀ t) := by
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : b ∈ R
  · rw [trajectoryAt_agrees_where_observed hT hT' hx hagree t ht b
      ⟨b, hb, 0, Nat.zero_le _, ReachIn.refl b⟩]
  · rw [hg b hb]
    simp

/-- [proved-derived; formal-checked] **The static diamond suffices**: two families that agree at
every tick on every edge `z → y` with `r_z + 1 + o_y ≤ e_last` give every admitted reading the same
value. -/
theorem release_past_diamond_static {T T' : ℕ → BlockOp K M} (hT : ∀ k, Sparse adj (T k))
    (hT' : ∀ k, Sparse adj (T' k)) {x₀ : (b : B) → M b} {g : (b : B) → Module.Dual K (M b)}
    {S R : Set B} (hx : SupportedIn x₀ S) (hg : SupportedIn g R) {eLast t : ℕ} (ht : t ≤ eLast)
    (hagree : ∀ k < eLast, ∀ y z, InDiamond adj S R eLast z y → T' k y z = T k y z) :
    pair g (trajectoryAt T' x₀ t) = pair g (trajectoryAt T x₀ t) :=
  release_past_diamond_at hT hT' hx hg ht fun k hk y z h =>
    hagree k hk y z (inDiamond_of_inDiamondAt hk h)

/-- [proved-derived; formal-checked] **The walk agreement at every tick.** If two tick-indexed
families agree at every tick on every edge a walk from `S` to `R` passes, two changes supported on
the reached blocks and agreeing on the observing ones stay so at every tick of the word. -/
theorem trajectoryAt_agrees_on_walk {T T' : ℕ → BlockOp K M} (hT : ∀ k, Sparse adj (T k))
    (hT' : ∀ k, Sparse adj (T' k)) {S R : Set B}
    (hagree : ∀ k y z, OnWalk adj S R z y → T k y z = T' k y z)
    {x x' : (b : B) → M b} (hx : SupportedIn x (reachAll adj S))
    (hx' : SupportedIn x' (reachAll adj S)) (hxx : ∀ b, ObservesAll adj R b → x b = x' b)
    (t : ℕ) :
    SupportedIn (trajectoryAt T x t) (reachAll adj S) ∧
      SupportedIn (trajectoryAt T' x' t) (reachAll adj S) ∧
      ∀ b, ObservesAll adj R b → trajectoryAt T x t b = trajectoryAt T' x' t b := by
  induction t with
  | zero => exact ⟨hx, hx', hxx⟩
  | succ t ih => exact tick_agrees_on_walk (hT t) (hT' t) (hagree t) ih.1 ih.2.1 ih.2.2

/-- [proved-derived; formal-checked] **Every admitted reading agrees** under the walk agreement, at
every epoch. -/
theorem readings_agree_on_walk {T T' : ℕ → BlockOp K M} (hT : ∀ k, Sparse adj (T k))
    (hT' : ∀ k, Sparse adj (T' k)) {S R : Set B}
    (hagree : ∀ k y z, OnWalk adj S R z y → T k y z = T' k y z)
    {x x' : (b : B) → M b} (hx : SupportedIn x (reachAll adj S))
    (hx' : SupportedIn x' (reachAll adj S)) (hxx : ∀ b, ObservesAll adj R b → x b = x' b)
    {g : (b : B) → Module.Dual K (M b)} (hg : SupportedIn g R) (t : ℕ) :
    pair g (trajectoryAt T x t) = pair g (trajectoryAt T' x' t) :=
  pair_agrees_on_observers hg (trajectoryAt_agrees_on_walk hT hT' hagree hx hx' hxx t).2.2

/-! ### The return through a tick-indexed word -/

/-- [definition] **The swept covector**: the reading covector `g` at epoch `t`, carried back `n`
ticks through the duals of `T_(t−1), …, T_(t−n)`. -/
def sweepAt (T : ℕ → BlockOp K M) (g : (b : B) → Module.Dual K (M b)) (t : ℕ) :
    ℕ → (b : B) → Module.Dual K (M b)
  | 0 => g
  | n + 1 => tick (dualOp (T (t - 1 - n))) (sweepAt T g t n)

theorem sweepAt_eq_trajectoryAt (T : ℕ → BlockOp K M) (g : (b : B) → Module.Dual K (M b))
    (t n : ℕ) : sweepAt T g t n = trajectoryAt (fun j => dualOp (T (t - 1 - j))) g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change tick (dualOp (T (t - 1 - n))) (sweepAt T g t n) =
      tick (dualOp (T (t - 1 - n))) (trajectoryAt (fun j => dualOp (T (t - 1 - j))) g n)
    rw [ih]

/-- [proved-derived; formal-checked] **The reading pairs exactly with the swept covector**:
`⟨λ_n, x_(t−n)⟩ = ⟨g, x_t⟩` for `n ≤ t`; the duals compose in reverse order and nothing is
inverted. -/
theorem sweepAt_pairing (T : ℕ → BlockOp K M) (x₀ : (b : B) → M b)
    (g : (b : B) → Module.Dual K (M b)) (t n : ℕ) (hn : n ≤ t) :
    pair (sweepAt T g t n) (trajectoryAt T x₀ (t - n)) = pair g (trajectoryAt T x₀ t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change pair (tick (dualOp (T (t - 1 - n))) (sweepAt T g t n)) (trajectoryAt T x₀ (t - (n + 1)))
      = _
    rw [← pair_tick, show t - 1 - n = t - (n + 1) by omega,
      show tick (T (t - (n + 1))) (trajectoryAt T x₀ (t - (n + 1))) =
        trajectoryAt T x₀ (t - (n + 1) + 1) from rfl,
      show t - (n + 1) + 1 = t - n by omega]
    exact ih (by omega)

theorem sweepAt_const (T : BlockOp K M) (g : (b : B) → Module.Dual K (M b)) (t n : ℕ) :
    sweepAt (fun _ => T) g t n = sweep T g n := by
  rw [sweepAt_eq_trajectoryAt, sweep, ← trajectoryAt_const]

/-- [proved-derived; formal-checked] **The swept covectors agree on the reached blocks** under the
walk agreement: the walk law on the reversed graph, from `R` to `S`. -/
theorem sweepAt_agrees_on_walk {T T' : ℕ → BlockOp K M} (hT : ∀ k, Sparse adj (T k))
    (hT' : ∀ k, Sparse adj (T' k)) {S R : Set B}
    (hagree : ∀ k y z, OnWalk adj S R z y → T k y z = T' k y z)
    {g : (b : B) → Module.Dual K (M b)} (hg : SupportedIn g R) (t n : ℕ) {y : B}
    (hy : y ∈ reachAll adj S) : sweepAt T g t n y = sweepAt T' g t n y := by
  have hg' : SupportedIn g (reachAll (flip adj) R) := fun b hb =>
    hg b fun hbR => hb (subset_reachAll (adj := flip adj) R hbR)
  have hagree' : ∀ j y z, OnWalk (flip adj) R S z y →
      dualOp (T (t - 1 - j)) y z = dualOp (T' (t - 1 - j)) y z := by
    rintro j y z ⟨hz, hy⟩
    simp only [dualOp]
    rw [hagree (t - 1 - j) z y ⟨observesAll_flip.mp hy, reachAll_flip.mp hz⟩]
  rw [sweepAt_eq_trajectoryAt, sweepAt_eq_trajectoryAt]
  exact (trajectoryAt_agrees_on_walk (adj := flip adj) (fun j => sparse_dualOp (hT (t - 1 - j)))
    (fun j => sparse_dualOp (hT' (t - 1 - j))) hagree' hg' hg' (fun _ _ => rfl) n).2.2 y
    (observesAll_flip.mpr hy)

/-! ### The deposit's data -/

variable (adj) in
/-- [definition] **The data a deposit reads on the edge `z → y`** of a tick-indexed word: for every
admitted reading and every tick `k` in the edge's window, the feature `x_k(z)` and the covector
`λ(y)` swept back to tick `k + 1` through the ticks the word ran. -/
def depositDataAt (T : ℕ → BlockOp K M) (x₀ : (b : B) → M b) (S R : Set B)
    (rd : List (ℕ × ((b : B) → Module.Dual K (M b)))) (z y : B) :
    List (M z × Module.Dual K (M y)) :=
  rd.flatMap fun r => (windowTicks adj S R r.1 z y).map fun k =>
    (trajectoryAt T x₀ k z, sweepAt T r.2 r.1 (r.1 - 1 - k) y)

/-- [proved-derived; formal-checked] The constant family's data are `Retention.depositData`. -/
theorem depositDataAt_const (T : BlockOp K M) (x₀ : (b : B) → M b) (S R : Set B)
    (rd : List (ℕ × ((b : B) → Module.Dual K (M b)))) (z y : B) :
    depositDataAt adj (fun _ => T) x₀ S R rd z y = depositData adj T x₀ S R rd z y := by
  simp only [depositDataAt, depositData, trajectoryAt_const, sweepAt_const]

/-- [proved-derived; formal-checked] **A deposit's data agree on every walk edge** for two
tick-indexed families that agree at every tick on every walk edge, open states on the reached blocks
agreeing on the observing ones, windows seeded at sets that agree on the observing blocks, and
readings supported on `R` (`CarriedStanding.depositData_agree` for a tick-indexed word). -/
theorem depositDataAt_agree {T T' : ℕ → BlockOp K M} (hT : ∀ k, Sparse adj (T k))
    (hT' : ∀ k, Sparse adj (T' k)) {S R sd sd' : Set B}
    (hagree : ∀ k y z, OnWalk adj S R z y → T k y z = T' k y z)
    (hsd : ∀ s, ObservesAll adj R s → (s ∈ sd ↔ s ∈ sd')) {x₀ x₀' : (b : B) → M b}
    (hx : SupportedIn x₀ (reachAll adj S)) (hx' : SupportedIn x₀' (reachAll adj S))
    (hxx : ∀ b, ObservesAll adj R b → x₀ b = x₀' b)
    {rd : List (ℕ × ((b : B) → Module.Dual K (M b)))} (hrd : ∀ r ∈ rd, SupportedIn r.2 R)
    {y z : B} (hw : OnWalk adj S R z y) (hadj : adj z y) :
    depositDataAt adj T x₀ sd R rd z y = depositDataAt adj T' x₀' sd' R rd z y := by
  have hz : ObservesAll adj R z := observesAll_step hadj hw.2
  have hy : y ∈ reachAll adj S := reachAll_step hw.1 hadj
  rw [depositDataAt, depositDataAt]
  refine List.flatMap_congr fun r hr => ?_
  rw [windowTicks_agree hsd hz]
  refine List.map_congr_left fun k _ => Prod.ext ?_ ?_
  · exact (trajectoryAt_agrees_on_walk hT hT' hagree hx hx' hxx k).2.2 z hz
  · exact sweepAt_agrees_on_walk hT hT' hagree (hrd r hr) _ _ hy

end Family

#print axioms trajectoryAt_const
#print axioms trajectoryAt_shift
#print axioms trajectoryAt_causal_cone
#print axioms word_variation_at
#print axioms trajectoryAt_agrees_where_observed
#print axioms release_past_diamond_at
#print axioms release_past_diamond_static
#print axioms trajectoryAt_agrees_on_walk
#print axioms readings_agree_on_walk
#print axioms sweepAt_pairing
#print axioms sweepAt_agrees_on_walk
#print axioms depositDataAt_const
#print axioms depositDataAt_agree

end Holonics.HNN.TickFamily
