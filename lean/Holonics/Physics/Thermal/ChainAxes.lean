import Holonics.Aeon.Production.PathReversal
import Holonics.Aeon.Clock.Epoch
import Holonics.Physics.Thermal.Schnakenberg

/-!
# The time and entropy axes along an oriented chain (#5)

[definition] Rebuild step 6, K3 (#74), and issue #5: construct the entropy coordinate along an
oriented chain of cells from the per-junction irreversibility, relate it to the longitudinal
axis, and state what is monotone, what reverses with the orientation, and what a neck does. Two
objects are kept apart: the **neck** is the bottleneck, the junction of least forward flow
(`neckFlow`), and the **carry section** is the junction `N − 1 → 0` at which the helix of the
lift takes its carry (`sectionForm 0 N`). The
**longitudinal axis** is the aeon reading of a section: the signed epochs, forward minus backward
crossings (`Aeon/Clock/Epoch.signed_count_is_flux`). The **entropy axis** is the production: per
junction the irreversibility `a = log(J₊/J₋)` (or the medium's affinity `log(P₊/P₋)`), summed
along the chain into the **entropy coordinate** `s(r) = Σ_(i<r) a i` (`coordinate`), and read on
an aeon as the affinity clock of `Aeon/Production/PathReversal` (`pathLogRatio_split`).

[proved-derived; formal-checked] What is proved.

1. **In stationarity every cut is balanced** (`stationary_cut_balance`): the flow out of any set
   of cells equals the flow into it. On an **open chain** (a path, nearest-neighbour moves) each
   junction is a cut by itself, so the stationary law is in detailed balance
   (`path_detailedBalance`, Kolmogorov's criterion on a tree) and its production is zero
   (`path_no_arrow`). An open chain carries an entropy coordinate (its medium affinities) but no
   stationary arrow: **the entropy axis is not the longitudinal axis**.
2. **A ring carries one current.** On a nearest-neighbour ring of at least three cells, the
   stationary law's net current is the same at every junction (`ring_one_current`, from
   `stationary_cut_balance` on the singleton cuts, and `ring_nets_eq`), so its production is the
   current times the cycle affinity, `σ = J · A` with `A = Σ_i log(J₊ i/J₋ i)`
   (`stationary_ringProduction_eq`, composing `ringProduction_eq`). On positive rational flows the
   ring's production is Schnakenberg's `neckProduction` over all its junctions
   (`ringProduction_eq_neck`, `neckProduction_ring_eq`). The cycle affinity is the medium's alone:
   the law cancels around the ring (`cycleAffinity_law_free`). `J` and `A` have one sign
   (`current_affinity_sign`): the entropy axis increases in the direction of the steady current and
   is flat exactly without current.
3. **What the neck does, and where the carry sits.** Every junction bounds the current,
   `J < J₊ i` (`current_lt_forward`), hence the production, `σ ≤ J₊ i · A` for `A ≥ 0`
   (`production_le_junction`); the sharpest of these bounds is the neck's, the least forward flow,
   `σ ≤ (min_i J₊ i) · A` (`production_le_neck`): the neck is the bottleneck of both axes. On the
   lift of the ring the entropy clock is the exact clock of a **helix**,
   `Φ(z) = s(z mod N) + A ⌊z/N⌋` (`helix_step`, `entropyForm_eq_exact`): the carry section takes
   the carry. So along every aeon
   **entropy = (s(end) − s(start)) + A · (signed epochs at the carry section)**
   (`entropy_reading`); on an aeon that returns to its cell it is exactly `A` times the signed
   epochs (`cycle_reading`), the state term is bounded by `2 Σ |a|` (`state_term_bounded`), and
   without cycle affinity the entropy axis decouples from the winding
   (`balanced_ring_decouples`). The carry section is a choice of chart, any junction can carry it;
   it need not be the neck.
4. **What reverses.** Reversing the orientation of the ring negates the current and the cycle
   affinity and leaves the production unchanged (`ring_reversal`). Reversing an aeon negates both
   readings (`Aeon/Clock/Reading.reading_reverse`).

[counterexample; formal-checked] **The entropy reading of a single aeon is not monotone**: one
step against a junction of positive irreversibility reads `−a < 0`
(`backward_step_reads_negative`). What is monotone is the mean over the path law
(`PathReversal.production_nonneg_of_support`, `production_eq_mul`: `σₙ = nσ ≥ 0`) and, on the
lift, the helix along the orientation when every `a ≥ 0` (`helix_monotone`).

[open] Finite chains only. Owed (#62): the identification of the lift's `entropyForm` with the
path log-ratio, `wordReading (entropyForm a) (lift γ) = Σ_i affinity P (γ i) (γ (i+1))` for a
positive ring path `γ` lifted to `ℤ` with `a z = affinity P (z mod N) (z+1 mod N)`
(`Aeon/Production/PathReversal.pathLogRatio_split`); and the mean signed crossing of the carry
section under the stationary path law as the current,
`E_π[forward − backward crossings of the carry section over n steps] = n · J`. The Rust owner
`holonics::physics::thermal` checks both exactly. No `axiom`, no `sorry`.
-/

namespace Holonics.Physics.Thermal.ChainAxes

open Finset Holonics.Aeon.Production Holonics.Aeon.Production.PathReversal

/-! ## 1. In stationarity every cut is balanced -/

section Cut

variable {S : Type*} [Fintype S] [DecidableEq S] {π : S → ℝ} {P : S → S → ℝ}

/-- [proved-derived; formal-checked] **Stationary cut balance**: the flow out of any set of cells
equals the flow into it. -/
theorem stationary_cut_balance (hπ : Kac.Stationary P π) (hrow : ∀ x, ∑ y, P x y = 1)
    (A : Finset S) :
    ∑ x ∈ A, ∑ y ∈ Aᶜ, flow π P x y = ∑ x ∈ Aᶜ, ∑ y ∈ A, flow π P x y := by
  have hout : ∑ x ∈ A, ∑ y, flow π P x y = ∑ x ∈ A, π x :=
    sum_congr rfl fun x _ => by simp only [flow, ← mul_sum, hrow x, mul_one]
  have hin : ∑ x, ∑ y ∈ A, flow π P x y = ∑ y ∈ A, π y := by
    rw [sum_comm]; exact sum_congr rfl fun y _ => hπ y
  have h1 : ∑ x ∈ A, ∑ y, flow π P x y =
      ∑ x ∈ A, ∑ y ∈ A, flow π P x y + ∑ x ∈ A, ∑ y ∈ Aᶜ, flow π P x y := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun x _ => (sum_add_sum_compl A _).symm
  have h2 : ∑ x, ∑ y ∈ A, flow π P x y =
      ∑ x ∈ A, ∑ y ∈ A, flow π P x y + ∑ x ∈ Aᶜ, ∑ y ∈ A, flow π P x y :=
    (sum_add_sum_compl A _).symm
  linarith

end Cut

/-! ## 2. The open chain has no stationary arrow -/

section Path

variable {N : ℕ} {π : Fin (N + 1) → ℝ} {P : Fin (N + 1) → Fin (N + 1) → ℝ}

/-- [definition] **An open chain**: every transition moves at most one cell. -/
def NearestNeighbour (P : Fin (N + 1) → Fin (N + 1) → ℝ) : Prop :=
  ∀ x y, P x y ≠ 0 → (x : ℕ) ≤ y + 1 ∧ (y : ℕ) ≤ x + 1

theorem flow_eq_zero_of_far (hnn : NearestNeighbour P) {x y : Fin (N + 1)}
    (hfar : ¬ ((x : ℕ) ≤ y + 1 ∧ (y : ℕ) ≤ x + 1)) : flow π P x y = 0 := by
  unfold flow
  by_cases h : P x y = 0
  · rw [h, mul_zero]
  · exact absurd (hnn x y h) hfar

/-- The cut below cell `x`. -/
def below (x : Fin (N + 1)) : Finset (Fin (N + 1)) := univ.filter fun z => (z : ℕ) ≤ x

theorem mem_below {x z : Fin (N + 1)} : z ∈ below x ↔ (z : ℕ) ≤ x := by simp [below]

/-- The only junction crossing the cut below `x` is `x → x + 1`, forward and back. -/
theorem cut_below_forward (hnn : NearestNeighbour P) {x y : Fin (N + 1)}
    (hxy : (y : ℕ) = x + 1) :
    ∑ z ∈ below x, ∑ w ∈ (below x)ᶜ, flow π P z w = flow π P x y := by
  have hy : y ∈ (below x)ᶜ := by rw [mem_compl, mem_below]; omega
  rw [sum_eq_single_of_mem x (mem_below.mpr le_rfl)]
  · rw [sum_eq_single_of_mem y hy]
    intro w hw hne
    rw [mem_compl, mem_below] at hw
    apply flow_eq_zero_of_far hnn
    intro ⟨_, h2⟩
    exact hne (Fin.ext (by omega))
  · intro z hz hne
    rw [mem_below] at hz
    have hz' : (z : ℕ) < x := lt_of_le_of_ne hz (fun h => hne (Fin.ext h))
    refine sum_eq_zero fun w hw => ?_
    rw [mem_compl, mem_below] at hw
    exact flow_eq_zero_of_far hnn (by omega)

theorem cut_below_backward (hnn : NearestNeighbour P) {x y : Fin (N + 1)}
    (hxy : (y : ℕ) = x + 1) :
    ∑ z ∈ (below x)ᶜ, ∑ w ∈ below x, flow π P z w = flow π P y x := by
  have hy : y ∈ (below x)ᶜ := by rw [mem_compl, mem_below]; omega
  rw [sum_eq_single_of_mem y hy]
  · rw [sum_eq_single_of_mem x (mem_below.mpr le_rfl)]
    intro w hw hne
    rw [mem_below] at hw
    apply flow_eq_zero_of_far hnn
    intro ⟨h1, _⟩
    exact hne (Fin.ext (by omega))
  · intro z hz hne
    rw [mem_compl, mem_below] at hz
    refine sum_eq_zero fun w hw => ?_
    rw [mem_below] at hw
    apply flow_eq_zero_of_far hnn
    intro ⟨h1, _⟩
    exact hne (Fin.ext (by omega))

/-- [proved-derived; formal-checked] **Kolmogorov on a path: the stationary law of an open chain
is in detailed balance.** -/
theorem path_detailedBalance (hnn : NearestNeighbour P) (hπ : Kac.Stationary P π)
    (hrow : ∀ x, ∑ y, P x y = 1) : DetailedBalance π P := by
  have key : ∀ x y : Fin (N + 1), (y : ℕ) = x + 1 → flow π P x y = flow π P y x := by
    intro x y hxy
    have := stationary_cut_balance hπ hrow (below x)
    rwa [cut_below_forward hnn hxy, cut_below_backward hnn hxy] at this
  intro x y
  by_cases h1 : (y : ℕ) = x + 1
  · exact key x y h1
  · by_cases h2 : (x : ℕ) = y + 1
    · exact (key y x h2).symm
    · by_cases h3 : x = y
      · rw [h3]
      · have hx : (x : ℕ) ≠ y := fun h => h3 (Fin.ext h)
        rw [flow_eq_zero_of_far hnn (by omega), flow_eq_zero_of_far hnn (by omega)]

/-- [proved-derived; formal-checked] **An open chain has no stationary arrow**: its epoch
production, and the production of every aeon, is zero. -/
theorem path_no_arrow (hA : Admissible π P) (hnn : NearestNeighbour P) (hπ : Kac.Stationary P π)
    (hrow : ∀ x, ∑ y, P x y = 1) (n : ℕ) :
    RealChart.epochProduction π P = 0 ∧ RealChart.production π P n = 0 := by
  have hdb := path_detailedBalance hnn hπ hrow
  refine ⟨(RealChart.epochProduction_eq_zero_iff hA).mpr hdb, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact RealChart.production_zero
  · exact (RealChart.production_eq_zero_iff hA hπ hrow hn).mpr hdb

end Path

/-! ## 3. The ring: the current, the cycle affinity, and the neck -/

section Ring

variable {N : ℕ} [NeZero N]

/-- [definition] **The cycle affinity** read from the junction flows, `Σ_i log(J₊ i / J₋ i)`. -/
noncomputable def cycleAffinity (Jf Jb : Fin N → ℝ) : ℝ :=
  ∑ i, (Real.log (Jf i) - Real.log (Jb i))

/-- [definition] **Schnakenberg's production of the ring**. -/
noncomputable def ringProduction (Jf Jb : Fin N → ℝ) : ℝ :=
  ∑ i, (Jf i - Jb i) * (Real.log (Jf i) - Real.log (Jb i))

omit [NeZero N] in
/-- [proved-derived; formal-checked] **`σ = J · A`**: with one net current `J` through every
junction, the production is the current times the cycle affinity. That a stationary ring carries
one current is `ring_one_current`; the composition is `stationary_ringProduction_eq`. -/
theorem ringProduction_eq {Jf Jb : Fin N → ℝ} {J : ℝ} (hJ : ∀ i, Jf i - Jb i = J) :
    ringProduction Jf Jb = J * cycleAffinity Jf Jb := by
  unfold ringProduction cycleAffinity
  rw [mul_sum]
  exact sum_congr rfl fun i _ => by rw [hJ i]

omit [NeZero N] in
/-- [proved-derived; formal-checked] **The ring's production is Schnakenberg's neck production**
over all its junctions, on positive rational flows (`Schnakenberg.neckProduction`, the one owner
of the junction term). -/
theorem ringProduction_eq_neck {Jf Jb : Fin N → ℚ} (hf : ∀ i, 0 < Jf i) (hb : ∀ i, 0 < Jb i) :
    ringProduction (fun i => (Jf i : ℝ)) (fun i => (Jb i : ℝ)) =
      Schnakenberg.neckProduction univ Jf Jb := by
  unfold ringProduction Schnakenberg.neckProduction Schnakenberg.term
  refine sum_congr rfl fun i _ => ?_
  push_cast
  rw [Real.log_div (by exact_mod_cast (hf i).ne') (by exact_mod_cast (hb i).ne')]

omit [NeZero N] in
/-- [proved-derived; formal-checked] **`σ = J · A` for the neck production**: with one net
rational current `J` through every junction, Schnakenberg's production of the ring is the current
times the cycle affinity. -/
theorem neckProduction_ring_eq {Jf Jb : Fin N → ℚ} {J : ℚ} (hf : ∀ i, 0 < Jf i)
    (hb : ∀ i, 0 < Jb i) (hJ : ∀ i, Jf i - Jb i = J) :
    Schnakenberg.neckProduction univ Jf Jb =
      J * cycleAffinity (fun i => (Jf i : ℝ)) (fun i => (Jb i : ℝ)) := by
  rw [← ringProduction_eq_neck hf hb]
  exact ringProduction_eq fun i => by rw [← hJ i]; push_cast; ring

/-- [proved-derived; formal-checked] **The cycle affinity is the medium's**: for flows
`J₊ i = π i · p i`, `J₋ i = π (i+1) · q i`, the law cancels around the ring. -/
theorem cycleAffinity_law_free (π p q : Fin N → ℝ) (hπ : ∀ i, 0 < π i) (hp : ∀ i, 0 < p i)
    (hq : ∀ i, 0 < q i) :
    cycleAffinity (fun i => π i * p i) (fun i => π (i + 1) * q i) =
      ∑ i, (Real.log (p i) - Real.log (q i)) := by
  unfold cycleAffinity
  have hsplit : ∀ i, Real.log (π i * p i) - Real.log (π (i + 1) * q i) =
      (Real.log (π i) - Real.log (π (i + 1))) + (Real.log (p i) - Real.log (q i)) := by
    intro i
    rw [Real.log_mul (hπ i).ne' (hp i).ne', Real.log_mul (hπ (i + 1)).ne' (hq i).ne']
    ring
  simp only [hsplit, sum_add_distrib, sum_sub_distrib]
  have hrot : ∑ i : Fin N, Real.log (π (i + 1)) = ∑ i, Real.log (π i) :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ fun _ => rfl
  rw [hrot, sub_self, zero_add]

omit [NeZero N] in
theorem ringProduction_nonneg {Jf Jb : Fin N → ℝ} (hf : ∀ i, 0 < Jf i) (hb : ∀ i, 0 < Jb i) :
    0 ≤ ringProduction Jf Jb := by
  refine sum_nonneg fun i _ => ?_
  rcases le_total (Jb i) (Jf i) with h | h
  · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (Real.log_le_log (hb i) h))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
      (sub_nonpos.mpr (Real.log_le_log (hf i) h))

/-- [proved-derived; formal-checked] **The current and the cycle affinity have one sign.** -/
theorem current_affinity_sign {Jf Jb : Fin N → ℝ} {J : ℝ} (hf : ∀ i, 0 < Jf i)
    (hb : ∀ i, 0 < Jb i) (hJ : ∀ i, Jf i - Jb i = J) :
    (0 < J ↔ 0 < cycleAffinity Jf Jb) ∧ (J = 0 ↔ cycleAffinity Jf Jb = 0) ∧
      (J < 0 ↔ cycleAffinity Jf Jb < 0) := by
  have hne : (univ : Finset (Fin N)).Nonempty := univ_nonempty
  have pos : 0 < J → 0 < cycleAffinity Jf Jb := fun hJp =>
    sum_pos (fun i _ => sub_pos.mpr (Real.log_lt_log (hb i) (by linarith [hJ i]))) hne
  have neg : J < 0 → cycleAffinity Jf Jb < 0 := fun hJn =>
    sum_neg (fun i _ => sub_neg.mpr (Real.log_lt_log (hf i) (by linarith [hJ i]))) hne
  have zero : J = 0 → cycleAffinity Jf Jb = 0 := fun hJ0 =>
    sum_eq_zero fun i _ => by rw [show Jf i = Jb i by linarith [hJ i], sub_self]
  refine ⟨⟨pos, fun hA => ?_⟩, ⟨zero, fun hA => ?_⟩, ⟨neg, fun hA => ?_⟩⟩
  · rcases lt_trichotomy J 0 with h | h | h
    · linarith [neg h]
    · linarith [zero h]
    · exact h
  · rcases lt_trichotomy J 0 with h | h | h
    · linarith [neg h]
    · exact h
    · linarith [pos h]
  · rcases lt_trichotomy J 0 with h | h | h
    · exact h
    · linarith [zero h]
    · linarith [pos h]

omit [NeZero N] in
/-- [proved-derived; formal-checked] **Every junction bounds the current**: `J < J₊ i`. -/
theorem current_lt_forward {Jf Jb : Fin N → ℝ} {J : ℝ} (hb : ∀ i, 0 < Jb i)
    (hJ : ∀ i, Jf i - Jb i = J) (i : Fin N) : J < Jf i := by
  linarith [hJ i, hb i]

omit [NeZero N] in
/-- [proved-derived; formal-checked] **Every junction bounds the production**: `σ ≤ J₊ i · A` at
every junction. -/
theorem production_le_junction {Jf Jb : Fin N → ℝ} {J : ℝ} (hb : ∀ i, 0 < Jb i)
    (hJ : ∀ i, Jf i - Jb i = J) (hA : 0 ≤ cycleAffinity Jf Jb) (i : Fin N) :
    ringProduction Jf Jb ≤ Jf i * cycleAffinity Jf Jb := by
  rw [ringProduction_eq hJ]
  exact mul_le_mul_of_nonneg_right (current_lt_forward hb hJ i).le hA

/-- [definition] **The neck's forward flow**: the least forward flow of the ring, the bottleneck. -/
noncomputable def neckFlow (Jf : Fin N → ℝ) : ℝ := univ.inf' univ_nonempty Jf

theorem neckFlow_le (Jf : Fin N → ℝ) (i : Fin N) : neckFlow Jf ≤ Jf i :=
  inf'_le _ (mem_univ i)

/-- [proved-derived; formal-checked] **The neck bounds the production**: `σ ≤ (min_i J₊ i) · A`,
the sharpest of the junction bounds, attained at the junction of least forward flow. -/
theorem production_le_neck {Jf Jb : Fin N → ℝ} {J : ℝ} (hb : ∀ i, 0 < Jb i)
    (hJ : ∀ i, Jf i - Jb i = J) (hA : 0 ≤ cycleAffinity Jf Jb) :
    ringProduction Jf Jb ≤ neckFlow Jf * cycleAffinity Jf Jb := by
  obtain ⟨i, -, hi⟩ := exists_mem_eq_inf' (univ_nonempty (α := Fin N)) Jf
  rw [neckFlow, hi]
  exact production_le_junction hb hJ hA i

omit [NeZero N] in
/-- [proved-derived; formal-checked] **Reversing the orientation** exchanges forward and backward
flows along the reflected ring: the current and the cycle affinity change sign, the production
does not. -/
theorem ring_reversal {Jf Jb : Fin N → ℝ} {J : ℝ} (hJ : ∀ i, Jf i - Jb i = J) :
    (∀ i, Jb (Fin.rev i) - Jf (Fin.rev i) = -J) ∧
      cycleAffinity (fun i => Jb (Fin.rev i)) (fun i => Jf (Fin.rev i)) = -cycleAffinity Jf Jb ∧
      ringProduction (fun i => Jb (Fin.rev i)) (fun i => Jf (Fin.rev i)) =
        ringProduction Jf Jb := by
  refine ⟨fun i => by linarith [hJ (Fin.rev i)], ?_, ?_⟩
  · unfold cycleAffinity
    rw [← sum_neg_distrib]
    refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
    simp only [Fin.revPerm_apply]
    ring
  · unfold ringProduction
    refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
    simp only [Fin.revPerm_apply]
    ring

end Ring

/-! ### A stationary ring carries one current -/

section RingCurrent

variable {M : ℕ} {π : Fin (M + 3) → ℝ} {P : Fin (M + 3) → Fin (M + 3) → ℝ}

/-- [definition] **A nearest-neighbour ring**: every transition stays or moves one cell around the
circle. -/
def RingNeighbour (P : Fin (M + 3) → Fin (M + 3) → ℝ) : Prop :=
  ∀ x y, P x y ≠ 0 → y = x ∨ y = x + 1 ∨ x = y + 1

/-- [definition] The net current of junction `i → i + 1`. -/
noncomputable def ringNet (π : Fin (M + 3) → ℝ) (P : Fin (M + 3) → Fin (M + 3) → ℝ) (i : Fin (M + 3)) : ℝ :=
  flow π P i (i + 1) - flow π P (i + 1) i

theorem one_ne_zero_ring : (1 : Fin (M + 3)) ≠ 0 := by
  rw [Ne, Fin.ext_iff, Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega)]
  omega

theorem two_ne_zero_ring : (1 + 1 : Fin (M + 3)) ≠ 0 := by
  rw [Ne, Fin.ext_iff, Fin.val_add, Fin.val_one', Fin.val_zero,
    Nat.mod_eq_of_lt (show 1 < M + 3 by omega), Nat.mod_eq_of_lt (show 1 + 1 < M + 3 by omega)]
  omega

/-- [proved-derived; formal-checked] **A stationary ring carries one current**: on a
nearest-neighbour ring of at least three cells, the net current of junction `i + 1 → i + 2`
equals that of `i → i + 1` (`stationary_cut_balance` on the singleton cut `{i + 1}`). -/
theorem ring_one_current (hnn : RingNeighbour P) (hπ : Kac.Stationary P π)
    (hrow : ∀ x, ∑ y, P x y = 1) (i : Fin (M + 3)) : ringNet π P (i + 1) = ringNet π P i := by
  set c := i + 1 with hc
  have hcut := stationary_cut_balance hπ hrow {c}
  simp only [sum_singleton] at hcut
  have hne1 : c + 1 ≠ c := fun h => one_ne_zero_ring (M := M) (add_eq_left.mp h)
  have hne2 : i ≠ c := by
    intro h
    rw [hc] at h
    exact one_ne_zero_ring (M := M) (add_eq_left.mp h.symm)
  have hne3 : c + 1 ≠ i := by
    intro h
    rw [hc, add_assoc] at h
    exact two_ne_zero_ring (M := M) (add_eq_left.mp h)
  have hmem1 : c + 1 ∈ ({c}ᶜ : Finset (Fin (M + 3))) := by simp [hne1]
  have hmem2 : i ∈ ({c}ᶜ : Finset (Fin (M + 3))) := by simp [hne2]
  have hout : ∑ y ∈ ({c}ᶜ : Finset _), flow π P c y = flow π P c (c + 1) + flow π P c i := by
    refine sum_eq_add_of_mem (c + 1) i hmem1 hmem2 hne3 fun y hy hyne => ?_
    unfold flow
    by_contra h
    have hP := hnn c y (right_ne_zero_of_mul h)
    rw [mem_compl, mem_singleton] at hy
    rcases hP with h1 | h1 | h1
    · exact hy h1
    · exact hyne.1 h1
    · exact hyne.2 (add_right_cancel (h1.symm.trans hc))
  have hin : ∑ x ∈ ({c}ᶜ : Finset _), flow π P x c = flow π P (c + 1) c + flow π P i c := by
    refine sum_eq_add_of_mem (c + 1) i hmem1 hmem2 hne3 fun x hx hxne => ?_
    unfold flow
    by_contra h
    have hP := hnn x c (right_ne_zero_of_mul h)
    rw [mem_compl, mem_singleton] at hx
    rcases hP with h1 | h1 | h1
    · exact hx h1.symm
    · exact hxne.2 (add_right_cancel (h1.symm.trans hc))
    · exact hxne.1 h1
  rw [hout, hin] at hcut
  unfold ringNet
  linarith

/-- [proved-derived; formal-checked] **Every junction of a stationary ring carries the same net
current.** -/
theorem ring_nets_eq (hnn : RingNeighbour P) (hπ : Kac.Stationary P π)
    (hrow : ∀ x, ∑ y, P x y = 1) (i : Fin (M + 3)) : ringNet π P i = ringNet π P 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ k ih => rw [← Fin.coeSucc_eq_succ, ring_one_current hnn hπ hrow, ih]

/-- [proved-derived; formal-checked] **A stationary ring produces its current times its cycle
affinity**: `σ = J · A` with `J` the one net current (`ring_nets_eq`, `ringProduction_eq`). -/
theorem stationary_ringProduction_eq (hnn : RingNeighbour P) (hπ : Kac.Stationary P π)
    (hrow : ∀ x, ∑ y, P x y = 1) :
    ringProduction (fun i => flow π P i (i + 1)) (fun i => flow π P (i + 1) i) =
      ringNet π P 0 *
        cycleAffinity (fun i => flow π P i (i + 1)) (fun i => flow π P (i + 1) i) :=
  ringProduction_eq fun i => ring_nets_eq hnn hπ hrow i

end RingCurrent

/-! ## 4. The lift: the entropy clock is a helix, and its carry sits at the carry section -/

section Lift

open Holonics.Aeon.Clock.Groupoid Holonics.Aeon.Clock.Reading Holonics.Aeon.Clock.Winding
  Holonics.Aeon.Clock.Epoch

variable (N : ℕ) (a : ℤ → ℝ)

/-- [definition] **The entropy coordinate**: the irreversibility summed over the first `r`
junctions. -/
noncomputable def coordinate (r : ℕ) : ℝ := ∑ i ∈ range r, a i

/-- [definition] **The turn**: the cycle affinity, the coordinate after one full circuit. -/
noncomputable def turn : ℝ := coordinate a N

/-- [definition] **The helix**: circle plus carry, `Φ(z) = s(z mod N) + A ⌊z/N⌋`. -/
noncomputable def helix (z : ℤ) : ℝ := coordinate a (z % N).toNat + turn N a * ((z / N : ℤ) : ℝ)

/-- [definition] **The entropy clock** on the lift of the ring: the step `z → z + 1` reads the
irreversibility of junction `z`. -/
def entropyForm : (Fin 1 → ℤ) × Fin 1 → ℝ := fun e => a (e.1 0)

variable {N a}

/-- [proved-derived; formal-checked] **The helix advances by the junction's irreversibility**,
the carry `A` taken exactly at the carry section `N − 1 → 0`. -/
theorem helix_step (hN : 0 < N) (hper : Function.Periodic a N) (z : ℤ) :
    helix N a (z + 1) - helix N a z = a z := by
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  set r := z % N with hr
  set q := z / N with hq
  have hz : r + N * q = z := Int.emod_add_mul_ediv z N
  have hr0 : 0 ≤ r := Int.emod_nonneg z hN'
  have hrN : r < N := Int.emod_lt_of_pos z (by exact_mod_cast hN)
  have ha : a z = a r := by
    rw [← hz, show r + (N : ℤ) * q = r + (q : ℤ) * (N : ℤ) by ring]
    exact hper.int_mul q r
  have hz1 : z + 1 = (r + 1) + N * q := by omega
  rcases lt_or_eq_of_le (show r + 1 ≤ N by omega) with hlt | heq
  · have hmod : (z + 1) % N = r + 1 := by
      rw [hz1, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) hlt]
    have hdiv : (z + 1) / N = q := by
      rw [hz1, Int.add_mul_ediv_left _ _ hN', Int.ediv_eq_zero_of_lt (by omega) hlt, zero_add]
    unfold helix
    rw [hmod, hdiv, show (r + 1).toNat = r.toNat + 1 by omega, coordinate, sum_range_succ,
      ha, Int.toNat_of_nonneg hr0]
    unfold coordinate
    ring
  · have hmod : (z + 1) % N = 0 := by
      rw [hz1, heq, show (N : ℤ) + N * q = 0 + N * (q + 1) by ring, Int.add_mul_emod_self_left,
        Int.zero_emod]
    have hdiv : (z + 1) / N = q + 1 := by
      rw [hz1, heq, show (N : ℤ) + N * q = 0 + N * (q + 1) by ring, Int.add_mul_ediv_left _ _ hN',
        Int.zero_ediv, zero_add]
    have hN1 : N = r.toNat + 1 := by omega
    have hc : coordinate a N = coordinate a r.toNat + a r := by
      rw [hN1, coordinate, sum_range_succ, Int.toNat_of_nonneg hr0]
      rfl
    unfold helix turn
    rw [hmod, hdiv, ← hr, ← hq, ha, hc]
    simp only [coordinate, show (0 : ℤ).toNat = 0 from rfl, sum_range_zero]
    push_cast
    ring

/-- [proved-derived; formal-checked] **What is monotone along the lift**: when every junction is
irreversible forward (`a ≥ 0`), the helix never decreases along the orientation. -/
theorem helix_monotone (hN : 0 < N) (hper : Function.Periodic a N) (ha : ∀ z, 0 ≤ a z) :
    Monotone (helix N a) :=
  monotone_int_of_le_succ fun z => by linarith [helix_step hN hper z, ha z]

/-- [proved-derived; formal-checked] **The entropy clock is the exact clock of the helix.** -/
theorem entropyForm_eq_exact (hN : 0 < N) (hper : Function.Periodic a N) :
    entropyForm a = exactForm (clockLift (Fin 1)) (fun x => helix N a (x 0)) := by
  funext e
  rcases e with ⟨x, j⟩
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simp only [entropyForm, exactForm, clockLift, Pi.add_apply, Pi.single_eq_same]
  rw [helix_step hN hper]

/-- [proved-derived; formal-checked] **The two axes cross at the carry section.** Along every aeon
of the ring's lift, the entropy reading is the change of the entropy coordinate plus the turn times
the signed epochs at the carry section `sectionForm 0 N`. -/
theorem entropy_reading (hN : 0 < N) (hper : Function.Periodic a N) {x y : Fin 1 → ℤ}
    (γ : Aeon (clockLift (Fin 1)) x y) :
    wordReading (entropyForm a) γ.steps =
      (coordinate a (y 0 % N).toNat - coordinate a (x 0 % N).toNat) +
        turn N a * (((forwardCrossings (sectionForm (0 : Fin 1) N) γ.steps : ℤ) -
          backwardCrossings (sectionForm (0 : Fin 1) N) γ.steps : ℤ) : ℝ) := by
  rw [entropyForm_eq_exact hN hper, wordReading_exactForm _ γ.chained,
    signed_count_is_flux 0 hN γ]
  unfold helix
  push_cast
  ring

/-- [proved-derived; formal-checked] **On an aeon that returns to its cell, entropy is the turn
times the signed epochs at the carry section.** -/
theorem cycle_reading (hN : 0 < N) (hper : Function.Periodic a N) {x y : Fin 1 → ℤ}
    (γ : Aeon (clockLift (Fin 1)) x y) (hcell : y 0 % N = x 0 % N) :
    wordReading (entropyForm a) γ.steps =
      turn N a * (((forwardCrossings (sectionForm (0 : Fin 1) N) γ.steps : ℤ) -
        backwardCrossings (sectionForm (0 : Fin 1) N) γ.steps : ℤ) : ℝ) := by
  rw [entropy_reading hN hper γ, hcell, sub_self, zero_add]

/-- [proved-derived; formal-checked] **Without cycle affinity the axes decouple**: the entropy
reading is the change of the coordinate alone, whatever the winding. -/
theorem balanced_ring_decouples (hN : 0 < N) (hper : Function.Periodic a N)
    (hturn : turn N a = 0) {x y : Fin 1 → ℤ} (γ : Aeon (clockLift (Fin 1)) x y) :
    wordReading (entropyForm a) γ.steps =
      coordinate a (y 0 % N).toNat - coordinate a (x 0 % N).toNat := by
  rw [entropy_reading hN hper γ, hturn, zero_mul, add_zero]

/-- [proved-derived; formal-checked] **The state term is bounded**: every coordinate on the
circle is at most `Σ_(i<N) |a i|` in magnitude, so entropy tracks the turn times the signed epochs
within `2 Σ |a|`. -/
theorem state_term_bounded {r : ℕ} (hr : r ≤ N) : |coordinate a r| ≤ ∑ i ∈ range N, |a i| := by
  unfold coordinate
  exact (abs_sum_le_sum_abs _ _).trans
    (sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hr) fun _ _ _ => abs_nonneg _)

/-- [counterexample; formal-checked] **One aeon's entropy is not monotone**: a single step back
across junction `0` reads `−a 0`, negative when that junction is irreversible forward. -/
theorem backward_step_reads_negative (h0 : 0 < a 0) :
    ∃ γ : Aeon (clockLift (Fin 1)) (Pi.single 0 1) 0,
      wordReading (entropyForm a) γ.steps = -a 0 ∧ wordReading (entropyForm a) γ.steps < 0 := by
  refine ⟨⟨[((0, 0), false)], ?_⟩, ?_, ?_⟩
  · simp only [ParametricComplex.chained_cons, ParametricComplex.chained_nil, clockLift,
      ParametricComplex.start, ParametricComplex.finish, Bool.false_eq_true, if_false]
    exact ⟨by simp, by simp⟩
  · simp [wordReading, stepReading, entropyForm]
  · simp [wordReading, stepReading, entropyForm, h0]

end Lift

section Audit

#print axioms stationary_cut_balance
#print axioms path_detailedBalance
#print axioms path_no_arrow
#print axioms ringProduction_eq
#print axioms cycleAffinity_law_free
#print axioms current_affinity_sign
#print axioms ringProduction_eq_neck
#print axioms neckProduction_ring_eq
#print axioms production_le_junction
#print axioms production_le_neck
#print axioms ring_one_current
#print axioms stationary_ringProduction_eq
#print axioms ring_reversal
#print axioms helix_step
#print axioms helix_monotone
#print axioms entropy_reading
#print axioms backward_step_reads_negative

end Audit

end Holonics.Physics.Thermal.ChainAxes
