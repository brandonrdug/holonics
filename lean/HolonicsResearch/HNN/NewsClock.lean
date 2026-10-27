import Holonics.Aeon.Clock.Epoch
import Mathlib.Tactic

/-!
# The news clock: a level's ticks carry the flux, and a span's move is the product of its sub-moves

The record `research/records/2026-10-27_THE_LEVELS_TICK_ON_THEIR_OWN_NEWS_SO_THE_TOWER_LEARNS_ITS_ENCODING_ON_ITS_OWN_AXIS.md`
(§2, §6.4) clocks each level of the tower by its own news. The tower's running code
`S_t = Σ_(k ≤ t) c_k` (each `c_k ≥ 0`) is a monotone flux; level `l ≥ 1` has section `σ_l` with
`σ_(l+1) = r σ_l`, ticks `Δτ_l(t) = ⌊S_t / σ_l⌋ − ⌊S_(t−1) / σ_l⌋` times at arrival `t`, and moves a
mode by `h_t = λ_t^(Δτ_l(t)) h_(t−1) + u_t`. This file proves the box that record leaves in #410:
the ticks form an epoch tower under a monotone flux, and the clocked move over a span is the
product of its sub-moves, with the scale square between two levels.

[proved-derived; formal-checked] What is proved.

1. **The coarse count is the carry of the fine count** (`count_carry`):
   `⌊S / (σ r)⌋ = winding r ⌊S / σ⌋`. This is `Epoch.odometer_tower` pulled back through the
   flux: `odometer_tower` carries the arrival index, which is level 0's clock; a news level carries
   its count of sections crossed. Level 0 to level 1 is not a carry of this kind.
2. **A coarser level never ticks more** (`ticks_carry_le`): for `a ≤ b`,
   `Δτ_(σ r) ≤ Δτ_σ` at every arrival, from `⌊(A + d) / r⌋ ≤ ⌊A / r⌋ + d` (`div_add_le`).
3. **From rest the ticks count the sections crossed** (`ticks_from_rest`):
   `Σ_(t < T) Δτ_σ(t) = ⌊S_T / σ⌋` for a monotone flux with `S_0 = 0`.
4. **The ticks form an epoch tower** (`tickSet_carry_subset`, `news_epoch_tower`): the arrivals
   where the coarse level ticks are among the fine level's, so each coarse epoch is the union of
   the fine epochs that coarsen to it (`Epoch.coarse_epoch_is_union_of_fine`). The epoch sets
   count an arrival once; the counts with multiplicity are items 2 and 3.
5. **The carried residue suffices** (`ticks_of_residue`, `ticks_of_carried`): the ticks of an
   arrival adding `c` to the flux depend only on the flux's residue modulo the section, and a
   residue modulo `σ'` carries every section `σ ∣ σ'`. So a stream that carries
   `S_T mod σ_(L−1)` carries every level's phase.
6. **The move over a span is the product of its sub-moves** (`state_of_moves`): with a mode `z_t`
   per arrival (gated or not),
   `h_T = (Π_(t<T) z_t^(Δτ(t))) h_0 + Σ_(t<T) (Π_(t<s<T) z_s^(Δτ(s))) u_t`, phase-carried moments
   with no tape. For one mode the span's product depends only on the counts
   at its ends (`span_move_const`): `Π_(t₀ ≤ t < t₁) z^(Δτ(t)) = z^(⌊S_(t₁)/σ⌋ − ⌊S_(t₀)/σ⌋)`, so
   `h_T = z^(⌊S_T/σ⌋ − ⌊S_0/σ⌋) h_0 + Σ_t z^(⌊S_T/σ⌋ − ⌊S_(t+1)/σ⌋) u_t` (`state_moments_const`).
7. **The scale square, up to the carried residue** (`exponent_carry`, `scale_square`,
   `scale_square_of_residue`): at each arrival, a mode on the fine clock moves by
   `z^(Δτ_σ) · z^(⌊a/σ⌋ mod r) = (z^r)^(Δτ_(σ r)) · z^(⌊b/σ⌋ mod r)`, so `r ∘ T_fine = T_coarse ∘ r`
   with `z ↦ z^r` holds exactly when the fine count's residue modulo `r` is the same at both ends,
   and otherwise up to that residue. The square relates one mode read on two clocks; the tower's
   levels carry their own learned modes.

The computational object is the helical pair interaction: each level's clock is a helix whose turn
is the section and whose carry is the tick, and the mode's move is the turn read at that clock. Of
the winding guide's six general objects this touches the helix (the count and its carry), the
tube (the clocked span and its moments) and the tower thread (the coarsening between levels); the
pair, faces and placement and the cell holonomy stay attached.

Consumers: the atlas row `hnn.tower-news-clock-carry` and the record's §6.4.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.NewsClock

open Finset

/-- [definition] The ticks of a level with section `σ` at an arrival that moves the flux from `a`
to `b`. -/
def ticks (σ a b : ℕ) : ℕ := b / σ - a / σ

/-- [definition] The arrivals among the first `T` at which a level with section `σ` ticks under the
flux `S`. -/
def tickSet (σ : ℕ) (S : ℕ → ℕ) (T : ℕ) : Finset ℕ :=
  (Ioc 0 T).filter (fun t => S (t - 1) / σ < S t / σ)

/-- [definition] The clocked move at arrival `t`: the arrival's mode taken once a tick. -/
def move {M : Type*} [Monoid M] (z : ℕ → M) (σ : ℕ) (S : ℕ → ℕ) (t : ℕ) : M :=
  z t ^ ticks σ (S t) (S (t + 1))

/-! ## 1. The count and its carry -/

/-- [proved-derived; formal-checked] **The coarse count is the carry of the fine count:**
`⌊S / (σ r)⌋ = winding r ⌊S / σ⌋`. -/
theorem count_carry (σ r S : ℕ) :
    S / (σ * r) = Holonics.Geometry.PhaseCarry.winding r (S / σ) := by
  rw [Holonics.Geometry.PhaseCarry.winding, Nat.div_div_eq_div_mul]

/-- [proved-standard; formal-checked] Division by `r` moves a count by at most what the count
moved: `⌊(A + d) / r⌋ ≤ ⌊A / r⌋ + d`. -/
theorem div_add_le (A d r : ℕ) : (A + d) / r ≤ A / r + d := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · have h1 := Nat.div_add_mod A r
    have h3 := Nat.mod_lt A hr
    have hd : d ≤ d * r := Nat.le_mul_of_pos_right d hr
    have hlt : (A + d) / r < A / r + d + 1 := by
      rw [Nat.div_lt_iff_lt_mul hr]
      have hexp : (A / r + d + 1) * r = r * (A / r) + d * r + r := by ring
      rw [hexp]
      generalize r * (A / r) = m at h1 ⊢
      generalize d * r = n at hd ⊢
      generalize A % r = x at h1 h3
      omega
    omega

/-- [proved-derived; formal-checked] **A coarser level never ticks more:** at an arrival moving
the flux from `a` to `b ≥ a`, the level with section `σ r` ticks at most as often as the level with
section `σ`. -/
theorem ticks_carry_le (σ r : ℕ) {a b : ℕ} (hab : a ≤ b) : ticks (σ * r) a b ≤ ticks σ a b := by
  have h : a / σ ≤ b / σ := Nat.div_le_div_right hab
  have hd := div_add_le (a / σ) (b / σ - a / σ) r
  rw [Nat.add_sub_of_le h] at hd
  unfold ticks
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  omega

/-- [proved-derived; formal-checked] **From rest the ticks count the sections crossed:** under a
monotone flux with `S 0 = 0`, the ticks over the first `T` arrivals sum to `⌊S_T / σ⌋`. -/
theorem ticks_from_rest (σ : ℕ) {S : ℕ → ℕ} (hS : Monotone S) (h0 : S 0 = 0) (T : ℕ) :
    ∑ t ∈ range T, ticks σ (S t) (S (t + 1)) = S T / σ := by
  induction T with
  | zero => simp [h0]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    have : S T / σ ≤ S (T + 1) / σ := Nat.div_le_div_right (hS (Nat.le_succ T))
    unfold ticks
    omega

/-! ## 2. The epoch tower -/

/-- [proved-derived; formal-checked] **The coarse level ticks only where the fine level ticks.** -/
theorem tickSet_carry_subset (σ r : ℕ) (S : ℕ → ℕ) (T : ℕ) :
    tickSet (σ * r) S T ⊆ tickSet σ S T := by
  intro t ht
  simp only [tickSet, Finset.mem_filter] at ht ⊢
  refine ⟨ht.1, ?_⟩
  have h := ht.2
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at h
  by_contra hcon
  exact absurd h (not_lt.mpr (Nat.div_le_div_right (not_lt.mp hcon)))

/-- [proved-derived; formal-checked] **The news clock's ticks form an epoch tower:** each coarse
epoch is the union of the fine epochs that coarsen to it. -/
theorem news_epoch_tower (σ r : ℕ) (S : ℕ → ℕ) (T N k' : ℕ) :
    Holonics.Aeon.Clock.Epoch.epoch (tickSet (σ * r) S T) N k' =
      ((range ((tickSet σ S T).card + 1)).filter
        (fun k => Holonics.Aeon.Clock.Epoch.coarsen (tickSet σ S T) (tickSet (σ * r) S T) k =
          k')).biUnion (Holonics.Aeon.Clock.Epoch.epoch (tickSet σ S T) N) :=
  Holonics.Aeon.Clock.Epoch.coarse_epoch_is_union_of_fine (tickSet_carry_subset σ r S T) N k'

/-! ## 3. The carried residue -/

/-- [proved-derived; formal-checked] **The ticks of an arrival depend only on the residue:** an
arrival adding `c` to the flux `a` ticks `⌊(a mod σ + c) / σ⌋` times. -/
theorem ticks_of_residue (σ a c : ℕ) : ticks σ a (a + c) = (a % σ + c) / σ := by
  unfold ticks
  rcases Nat.eq_zero_or_pos σ with rfl | hσ
  · simp
  · have h1 := Nat.div_add_mod a σ
    have h2 : a + c = (a % σ + c) + σ * (a / σ) := by omega
    rw [h2, Nat.add_mul_div_left _ _ hσ]
    exact Nat.add_sub_cancel _ _

/-- [proved-derived; formal-checked] **A residue modulo `σ'` carries every section `σ ∣ σ'`:** the
stream that carries the flux modulo the coarsest section carries every level's next ticks. -/
theorem ticks_of_carried {σ σ' : ℕ} (h : σ ∣ σ') (a c : ℕ) :
    ticks σ a (a + c) = (a % σ' % σ + c) / σ := by
  rw [Nat.mod_mod_of_dvd a h, ticks_of_residue]

/-! ## 4. The move over a span -/

/-- [proved-derived; formal-checked] **The move over a span is the product of its sub-moves:** for
`h_(t+1) = z_t^(Δτ(t)) h_t + u_t`, the state after `T` arrivals is the moved start plus each input
moved by the product of the later sub-moves. -/
theorem state_of_moves {R : Type*} [CommSemiring R] (z : ℕ → R) (σ : ℕ) (S : ℕ → ℕ)
    (h u : ℕ → R) (hstep : ∀ t, h (t + 1) = move z σ S t * h t + u t) (T : ℕ) :
    h T = (∏ t ∈ range T, move z σ S t) * h 0 +
      ∑ t ∈ range T, (∏ s ∈ Ico (t + 1) T, move z σ S s) * u t := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hIco : ∀ t ∈ range T,
        (∏ s ∈ Ico (t + 1) (T + 1), move z σ S s) * u t =
          move z σ S T * ((∏ s ∈ Ico (t + 1) T, move z σ S s) * u t) := by
      intro t ht
      have htT : t + 1 ≤ T := by have := Finset.mem_range.mp ht; omega
      rw [Finset.prod_Ico_succ_top htT]
      ring
    rw [hstep T, ih, Finset.prod_range_succ, Finset.sum_range_succ, Finset.sum_congr rfl hIco,
      Finset.Ico_self, Finset.prod_empty, one_mul, ← Finset.mul_sum]
    ring

/-- [proved-derived; formal-checked] **For one mode a span's move depends only on its end counts:**
`Π_(t₀ ≤ t < t₁) z^(Δτ(t)) = z^(⌊S_(t₁)/σ⌋ − ⌊S_(t₀)/σ⌋)` under a monotone flux. -/
theorem span_move_const {M : Type*} [CommMonoid M] (z : M) (σ : ℕ) {S : ℕ → ℕ} (hS : Monotone S)
    {t₀ t₁ : ℕ} (h : t₀ ≤ t₁) :
    ∏ t ∈ Ico t₀ t₁, move (fun _ => z) σ S t = z ^ (S t₁ / σ - S t₀ / σ) := by
  induction t₁, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.prod_Ico_succ_top hn, ih]
    simp only [move]
    rw [← pow_add]
    congr 1
    have h1 : S t₀ / σ ≤ S n / σ := Nat.div_le_div_right (hS hn)
    have h2 : S n / σ ≤ S (n + 1) / σ := Nat.div_le_div_right (hS (Nat.le_succ n))
    unfold ticks
    omega

/-- [proved-derived; formal-checked] **One mode's state is its phase-carried moments on its own
clock:** `h_T = z^(⌊S_T/σ⌋ − ⌊S_0/σ⌋) h_0 + Σ_(t<T) z^(⌊S_T/σ⌋ − ⌊S_(t+1)/σ⌋) u_t`. -/
theorem state_moments_const {R : Type*} [CommSemiring R] (z : R) (σ : ℕ) {S : ℕ → ℕ}
    (hS : Monotone S) (h u : ℕ → R)
    (hstep : ∀ t, h (t + 1) = move (fun _ => z) σ S t * h t + u t) (T : ℕ) :
    h T = z ^ (S T / σ - S 0 / σ) * h 0 +
      ∑ t ∈ range T, z ^ (S T / σ - S (t + 1) / σ) * u t := by
  rw [state_of_moves (fun _ => z) σ S h u hstep T, Finset.range_eq_Ico,
    span_move_const z σ hS (t₀ := 0) (t₁ := T) (Nat.zero_le T)]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  have htT : t + 1 ≤ T := by have := (Finset.mem_Ico.mp ht).2; omega
  rw [span_move_const z σ hS (t₀ := t + 1) (t₁ := T) htT]

/-! ## 5. The scale square -/

/-- [proved-standard; formal-checked] **The fine count is the carried coarse count plus its
residue:** for `X ≤ Y`, `(Y − X) + X mod r = r (⌊Y/r⌋ − ⌊X/r⌋) + Y mod r`. -/
theorem exponent_carry (r : ℕ) {X Y : ℕ} (hXY : X ≤ Y) :
    Y - X + X % r = r * (Y / r - X / r) + Y % r := by
  have hX := Nat.div_add_mod X r
  have hY := Nat.div_add_mod Y r
  obtain ⟨q, hq⟩ : ∃ q, Y / r = X / r + q :=
    ⟨Y / r - X / r, (Nat.add_sub_of_le (Nat.div_le_div_right hXY)).symm⟩
  rw [hq, mul_add] at hY
  rw [hq, Nat.add_sub_cancel_left]
  generalize r * (X / r) = m at hX hY
  generalize r * q = n at hY ⊢
  generalize X % r = x at hX ⊢
  generalize Y % r = y at hY ⊢
  omega

/-- [proved-derived; formal-checked] **The scale square, up to the carried residue:** at an
arrival moving the flux from `a` to `b ≥ a`, a mode `z` on the fine clock (section `σ`) and the
mode `z^r` on the coarse clock (section `σ r`) agree once each is completed by the fine count's
residue modulo `r` at its end. -/
theorem scale_square {M : Type*} [Monoid M] (z : M) (σ r a b : ℕ) (hab : a ≤ b) :
    z ^ ticks σ a b * z ^ (a / σ % r) = (z ^ r) ^ ticks (σ * r) a b * z ^ (b / σ % r) := by
  have h : a / σ ≤ b / σ := Nat.div_le_div_right hab
  unfold ticks
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← pow_mul, ← pow_add, ← pow_add,
    exponent_carry r h]

/-- [proved-derived; formal-checked] **The scale square is exact between equal residues:** when the
fine count has the same residue modulo `r` at both ends, `z^(Δτ_σ) = (z^r)^(Δτ_(σ r))`. -/
theorem scale_square_of_residue {M : Type*} [Monoid M] (z : M) (σ r a b : ℕ) (hab : a ≤ b)
    (hres : a / σ % r = b / σ % r) : z ^ ticks σ a b = (z ^ r) ^ ticks (σ * r) a b := by
  have h : a / σ ≤ b / σ := Nat.div_le_div_right hab
  have hc := exponent_carry r h
  rw [hres] at hc
  unfold ticks
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← pow_mul]
  congr 1
  exact Nat.add_right_cancel hc

end Holonics.HNN.NewsClock
