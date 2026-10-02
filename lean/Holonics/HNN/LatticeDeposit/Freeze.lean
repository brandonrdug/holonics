import Holonics.HNN.LatticeDeposit
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Field

/-!
# HNN.LatticeDeposit.Freeze: why a contact stops moving, and when its dropped moves matter

[definition] The contact-loop record (October 2, §14) measured that after the first aeon a
contact family's steps stop reaching its lattice: the share of certified families with no entry
moved rose from about half to 97 percent while the return reaching them grew by about `2^6`. This
module derives what the code's deposit law implies for that, in the lattice deposit's owner
(`HNN/LatticeDeposit`, realized by `hnn::constitution`'s `BudgetedCarry` and `Carry`).

**The step.** A factor family's unit step is `D = G_x / h′` with `h′ = h + e` its carried
statistic, `e` the feature energy the window adds (`hnn::constitution`, "The factor families'
certified step"). The applied step `η D` takes the largest dyadic `η` with `η C ≤ a` and
`η c ≤ 1`, `c = max_t |w g_t|_∞`. Along the ray the curvature cap `η ≤ a/C` grows with `h′`, so
past the first deposits the cap `η c ≤ 1` binds, and it divides the covector by its own scale:
the step's size no longer depends on how large the return is, only on the feature and on `h′`.
That is why a return grown `2^6` times still moves the contact no further. In the measurable form
used here, deposit `i` moves an entry by at most `κ` times the share of the statistic it adds,
`|δ_i| ≤ κ (h_(i+1) − h_i)/h_(i+1)`, with `κ` read per deposit as `|η D|_∞ · h′ / e`.

[proved-derived; formal-checked] What is proved.

1. **The logarithm law** (`sum_fraction_le_log`, `move_le_log`, `move_needs_growth`). Under that
   bound the exact sum of the entry's updates from deposit `m` to deposit `n` is at most
   `κ log(h_n/h_m)` in size, whatever the updates' signs, rounded or not. For the updates alone to
   sum to one lattice unit `u` after deposit `m`, the statistic must grow by the factor `e^(u/κ)`.
   That bounds the accumulated updates, not the first move: the carried remainder can sit just
   inside the cell's edge, so a small update can move the entry once. A sustained displacement is
   bounded, though: by the accounting (`run_accounting`, with both carried remainders at most
   `u/2` and the releases below `u/2`), moving `k` units needs `|Σ δ| > (k − 3/2) u`, so the
   statistic must grow by `e^((k − 3/2)u/κ)`. A statistic that grows linearly in the windows makes
   that exponentially many windows: the contact freezes because its step decays as `1/h`, not
   because rounding loses its moves.
2. **A coherent contact still moves, but only logarithmically** (`sum_log_ratio`,
   `coherent_move_ge`). If every update keeps one sign and at least `κ′` times the share, and no
   deposit grows the statistic by more than the factor `1 + ρ`, the sum is at least
   `κ′/(1 + ρ) · log(h_n/h_m)`.
3. **Rounding loses less than half a unit since the founding** (`frozen_accumulation_lt_unit`,
   `moved_of_accumulation`). The deposit already carries the remainder below the coarse lattice
   into the next deposit and releases only what lies below the fine lattice, whose total since the
   locus's founding is below `u/2` (`within_one_unit_since_founding`). So an entry that has not
   moved has an exact accumulation within one unit of zero, and an accumulation of one unit moves
   it. Carrying the remainder is therefore already the code's law; what can be lost is bounded,
   coherent or not.
4. **Coherence, measured per entry** (`sign_mgf_le`, `sign_tail`, `sign_tail_abs`,
   `coherence_ratio_le`, `coherence_ratio_one_sign`). Let `S = Σ δ_i` and `Q = Σ δ_i²` over an
   entry's updates, and `Z = S/√Q`. Always `Z² ≤ n` (Cauchy–Schwarz), and an entry whose updates
   keep one sign has `Z² ≥ 1`, with `Z² = n` when they are equal. If the signs carry no information
   (the magnitudes fixed, the signs equally likely either way, independently), at most
   `2 · 2^n e^(−t²/2)` of the `2^n` sign patterns reach `|Z| ≥ t`. So `|Z| ≥ √(2 ln(2/α))` rejects
   incoherent signs at level `α`. The same statistic applies to the released residuals.
5. **The Kraft bound on the code's schedule is tight** (`fine_neg_half_cell`, `rem_neg_half_cell`,
   `carry_drainStep`, `drain_run`, `release_bound_tight`). The bound itself is the owner's
   `release_bounded_since_founding`: under the code's precision `k_m = 2⌊log₂ m⌋ + 1` (Lean
   `gammaLength` at the clock the deposit advances to, Rust `BudgetedCarry::precision`), an entry's
   releases since its founding total less than `u/2`, whatever their signs, because
   `Σ_m 2^(−k_m) < 1`. It is reached: an update at the lower edge of the fine cell rounds to zero
   and is released whole, so from a founding carrier `2^J − 1` such deposits leave the entry where
   it was and drop exactly `(u/2)(1 − 2^(−J))`. Half a unit is the supremum, so the main line's
   coherent residuals (record §15) can approach it but not pass it.
6. **The step against the fine cell** (`gammaWeight_bounds`, `step_exceeds_fine_cell`). The fine
   cell at clock `m` is between `u/(2m²)` and `2u/m²`. A step decaying as `κ′/m` exceeds the half
   cell once `κ′ m > u`, so it is carried, not released. The contacts are held by the coarse unit
   `u`: past the first move the carried remainder can supply, the logarithm law (item 1) says each
   further unit needs the statistic to grow by about `e^(u/κ)`; the release is not what freezes
   them.
7. **The bound under a refining schedule** (`schedule_release_le`, `schedule_release_attained`,
   `refining_schedule_kraft_ge`, `refining_schedule_kraft_ge_one`). For any precision schedule the
   releases at an entry total at most `(u/2) Σ_j 2^(−k_j)`, and that total is reached. If the fine
   cell at deposit `m` were the dyadic refinement of `1/L(m)` of a unit, with `L` the confirmable
   grain `L(N) = ⌈√(N ln 2/2)⌉` (`HNN/Ratio/Resolution`, PR #151), the weights of the first `N`
   deposits sum to at least `√N/4`: one from `N = 16`, and without bound. The drop could then
   reach `(u/2)·√N/4`, a whole unit from `N = 64`. The half-unit conclusion holds because the
   code's cell refines as `1/m²`, which is summable; a cell refining as `1/√m` is not.
   Here the coarse unit `u` is held fixed, as the carrier fixes `L`. If the coarse unit itself
   refined with the grain, the half-unit bound would shrink with it, and each drop would have to be
   read against the unit current at its deposit; re-basing a carrier's lattice is not modelled here
   and stays owed in #62.

[definition] **The condition, in what the main line measures.** The carried remainder's own sign is
not the statistic: it lies in `[−u/2, u/2)` and changes sign every time the entry moves. The
statistic is the entry's cumulative update `S` against its noise `√Q`.
* **Coherent** (`|Z|` grows like `√n`, above `√(2 ln(2/α))`): the updates add, the carried
  remainder holds them, and the entry moves once `|S|` passes half a unit. The rate is the
  logarithm law, so the contact moves `κ log(h_n/h_m)` at most.
* **Incoherent** (`|Z|` of order one): the sum stays within `t√Q` with the stated odds, and with the
  step decaying as `1/h` the remaining `Q` after deposit `m` is of order `1/m`. Its effect on the
  receiver's exponents is the gain times that, and when it is below the resolution
  `√(2/(N ln 2))` of `HNN/Ratio/Resolution` the one-bit criterion says rounding it away loses
  nothing the receiver could confirm.
* **The released residuals**, coherent or not, total less than half a unit per entry under the
  code's schedule (item 5). Their coherence decides how close to that bound they come, and it
  would decide the drift only under a schedule whose weights are not summable (item 7).

No `axiom`, no `sorry`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.LatticeDeposit.Freeze

open Holonics.HNN.LatticeDeposit
open Finset

/-! ## 1. The statistic's growth bounds the sum of a decaying step -/

section Statistic

/-- [proved-standard; formal-checked] **The share a deposit adds is at most the log growth.**
For `0 < a ≤ b`, `(b − a)/b ≤ log(b/a)`. -/
theorem fraction_le_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / b ≤ Real.log (b / a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  have hinv : Real.log (a / b) = -Real.log (b / a) := by
    rw [← Real.log_inv, inv_div]
  rw [hinv] at h
  have e : (b - a) / b = 1 - a / b := by field_simp
  rw [e]; linarith

/-- [proved-standard; formal-checked] **The log growth is at most the share over the old
statistic.** For `0 < a ≤ b`, `log(b/a) ≤ (b − a)/a`. -/
theorem log_le_fraction {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log (b / a) ≤ (b - a) / a := by
  have h := Real.log_le_sub_one_of_pos (div_pos (lt_of_lt_of_le ha hab) ha)
  have e : (b - a) / a = b / a - 1 := by field_simp
  rw [e]; exact h

/-- [proved-standard; formal-checked] **The log ratios telescope.** -/
theorem sum_log_ratio (h : ℕ → ℝ) (hpos : ∀ i, 0 < h i) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Ico m n, Real.log (h (i + 1) / h i) = Real.log (h n / h m) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [sum_Ico_succ_top hmn, ih]
    have e : h (n + 1) / h m = h n / h m * (h (n + 1) / h n) := by
      have := (hpos n).ne'; have := (hpos m).ne'; field_simp
    rw [e, Real.log_mul (div_pos (hpos n) (hpos m)).ne' (div_pos (hpos (n + 1)) (hpos n)).ne']

/-- [proved-derived; formal-checked] **The shares a run of deposits adds are at most the log
growth of the statistic over the run.** For a positive nondecreasing statistic `h`,
`Σ_(m ≤ i < n) (h_(i+1) − h_i)/h_(i+1) ≤ log(h_n/h_m)`. -/
theorem sum_fraction_le_log (h : ℕ → ℝ) (hpos : ∀ i, 0 < h i) (hmono : ∀ i, h i ≤ h (i + 1))
    {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Ico m n, (h (i + 1) - h i) / h (i + 1) ≤ Real.log (h n / h m) := by
  rw [← sum_log_ratio h hpos hmn]
  exact sum_le_sum fun i _ => fraction_le_log (hpos i) (hmono i)

/-- [proved-derived; formal-checked] **The logarithm law.** If each deposit moves an entry by at
most `κ` times the share of the statistic it adds, the entry's exact accumulated update over the
run is at most `κ log(h_n/h_m)` in size, whatever the signs. -/
theorem move_le_log (h : ℕ → ℝ) (hpos : ∀ i, 0 < h i) (hmono : ∀ i, h i ≤ h (i + 1))
    (δ : ℕ → ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hδ : ∀ i, |δ i| ≤ κ * ((h (i + 1) - h i) / h (i + 1))) {m n : ℕ} (hmn : m ≤ n) :
    |∑ i ∈ Ico m n, δ i| ≤ κ * Real.log (h n / h m) := by
  calc |∑ i ∈ Ico m n, δ i| ≤ ∑ i ∈ Ico m n, |δ i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Ico m n, κ * ((h (i + 1) - h i) / h (i + 1)) := sum_le_sum fun i _ => hδ i
    _ = κ * ∑ i ∈ Ico m n, (h (i + 1) - h i) / h (i + 1) := (mul_sum _ _ _).symm
    _ ≤ κ * Real.log (h n / h m) :=
        mul_le_mul_of_nonneg_left (sum_fraction_le_log h hpos hmono hmn) hκ

/-- [proved-derived; formal-checked] **Accumulating one unit needs exponential growth.** Under the
logarithm law, updates that sum to at least `u` over the run need `h_n ≥ h_m e^(u/κ)`. This bounds
the accumulated updates; the carried remainder can bring the entry's first move sooner. -/
theorem move_needs_growth (h : ℕ → ℝ) (hpos : ∀ i, 0 < h i) (hmono : ∀ i, h i ≤ h (i + 1))
    (δ : ℕ → ℝ) {κ u : ℝ} (hκ : 0 < κ)
    (hδ : ∀ i, |δ i| ≤ κ * ((h (i + 1) - h i) / h (i + 1))) {m n : ℕ} (hmn : m ≤ n)
    (hu : u ≤ |∑ i ∈ Ico m n, δ i|) :
    h m * Real.exp (u / κ) ≤ h n := by
  have hlaw := move_le_log h hpos hmono δ hκ.le hδ hmn
  have hle : u / κ ≤ Real.log (h n / h m) := by
    rw [div_le_iff₀ hκ]; linarith
  have := Real.exp_le_exp.mpr hle
  rw [Real.exp_log (div_pos (hpos n) (hpos m)), le_div_iff₀ (hpos m)] at this
  linarith

/-- [proved-derived; formal-checked] **A coherent entry still moves logarithmically.** If every
update in the run is at least `κ′ ≥ 0` times the share the deposit adds, and no deposit grows the
statistic by more than the factor `1 + ρ`, the accumulated update is at least
`κ′/(1 + ρ) · log(h_n/h_m)`. -/
theorem coherent_move_ge (h : ℕ → ℝ) (hpos : ∀ i, 0 < h i) (hmono : ∀ i, h i ≤ h (i + 1))
    (δ : ℕ → ℝ) {κ' ρ : ℝ} (hκ' : 0 ≤ κ') (hρ : 0 ≤ ρ)
    (hgrow : ∀ i, h (i + 1) ≤ (1 + ρ) * h i)
    {m n : ℕ} (hmn : m ≤ n) (hδ : ∀ i ∈ Ico m n, κ' * ((h (i + 1) - h i) / h (i + 1)) ≤ δ i) :
    κ' / (1 + ρ) * Real.log (h n / h m) ≤ ∑ i ∈ Ico m n, δ i := by
  have h1ρ : 0 < 1 + ρ := by linarith
  have hshare : ∀ i, Real.log (h (i + 1) / h i) / (1 + ρ) ≤ (h (i + 1) - h i) / h (i + 1) := by
    intro i
    have hi := hpos i
    have hi1 := hpos (i + 1)
    have hl := log_le_fraction hi (hmono i)
    rw [div_le_iff₀ h1ρ]
    calc Real.log (h (i + 1) / h i) ≤ (h (i + 1) - h i) / h i := hl
      _ ≤ (h (i + 1) - h i) / h (i + 1) * (1 + ρ) := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hi hi1]
        have hd : 0 ≤ h (i + 1) - h i := by linarith [hmono i]
        nlinarith [hgrow i, mul_le_mul_of_nonneg_left (hgrow i) hd]
  rw [← sum_log_ratio h hpos hmn, div_mul_eq_mul_div, mul_sum, sum_div]
  refine sum_le_sum fun i hi => ?_
  calc κ' * Real.log (h (i + 1) / h i) / (1 + ρ) =
        κ' * (Real.log (h (i + 1) / h i) / (1 + ρ)) := by ring
    _ ≤ κ' * ((h (i + 1) - h i) / h (i + 1)) := mul_le_mul_of_nonneg_left (hshare i) hκ'
    _ ≤ δ i := hδ i hi

end Statistic

/-! ## 2. What rounding can lose -/

section Frozen

variable {L : ℕ} {E : Type*}

/-- [proved-derived; formal-checked] **A frozen entry's accumulation is within one unit.** If a
run from the locus's founding leaves an entry's value unchanged, its starting remainder plus the
exact updates that reached it is less than one lattice unit (`within_one_unit_since_founding`):
the carried remainder holds less than half a unit and the releases since the founding less than
half. -/
theorem frozen_accumulation_lt_unit (s : Carried L E) (Δs : List (E → ℚ)) (i : E)
    (hfrozen : (run s Δs).value i = s.value i) :
    |s.rem i + (Δs.map (· i)).sum| < unit L := by
  have h := within_one_unit_since_founding s Δs i
  rw [hfrozen] at h
  have e : s.value i - (s.value i + s.rem i + (Δs.map (· i)).sum) =
      -(s.rem i + (Δs.map (· i)).sum) := by ring
  rwa [e, abs_neg] at h

/-- [proved-derived; formal-checked] **One unit of accumulation moves the entry.** -/
theorem moved_of_accumulation (s : Carried L E) (Δs : List (E → ℚ)) (i : E)
    (h : unit L ≤ |s.rem i + (Δs.map (· i)).sum|) :
    (run s Δs).value i ≠ s.value i := fun hfrozen =>
  absurd (frozen_accumulation_lt_unit s Δs i hfrozen) (not_lt.mpr h)

end Frozen

/-! ## 3. Coherence of an entry's updates -/

section Signs

variable {n : ℕ}

/-- [definition] A sign `±1` read from a bit. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- [definition] **The signed sum** of fixed magnitudes `δ` under the sign pattern `ε`. -/
def signedSum (δ : Fin n → ℝ) (ε : Fin n → Bool) : ℝ := ∑ i, sgn (ε i) * δ i

/-- [proved-derived; formal-checked] **The moment generating sum over sign patterns.**
`Σ_ε e^(λ S_ε) = Π_i 2 cosh(λ δ_i) ≤ 2^n e^(λ² Q/2)`, `Q = Σ δ_i²`. -/
theorem sign_mgf_le (δ : Fin n → ℝ) (lam : ℝ) :
    ∑ ε : Fin n → Bool, Real.exp (lam * signedSum δ ε) ≤
      2 ^ n * Real.exp (lam ^ 2 * (∑ i, δ i ^ 2) / 2) := by
  have hprod : ∑ ε : Fin n → Bool, Real.exp (lam * signedSum δ ε) =
      ∏ i, ∑ b : Bool, Real.exp (lam * (sgn b * δ i)) := by
    rw [Fintype.prod_sum]
    refine Fintype.sum_congr _ _ fun ε => ?_
    rw [signedSum, mul_sum, Real.exp_sum]
  rw [hprod]
  have hterm : ∀ i, ∑ b : Bool, Real.exp (lam * (sgn b * δ i)) ≤
      2 * Real.exp ((lam * δ i) ^ 2 / 2) := by
    intro i
    have hc := Real.cosh_le_exp_half_sq (lam * δ i)
    rw [Real.cosh_eq] at hc
    simp only [Fintype.sum_bool, sgn, if_true, Bool.false_eq_true, if_false]
    have e1 : lam * (1 * δ i) = lam * δ i := by ring
    have e2 : lam * (-1 * δ i) = -(lam * δ i) := by ring
    rw [e1, e2]
    linarith
  calc ∏ i, ∑ b : Bool, Real.exp (lam * (sgn b * δ i))
      ≤ ∏ i : Fin n, 2 * Real.exp ((lam * δ i) ^ 2 / 2) :=
        prod_le_prod (fun i _ => sum_nonneg fun b _ => (Real.exp_pos _).le) fun i _ => hterm i
    _ = 2 ^ n * Real.exp (lam ^ 2 * (∑ i, δ i ^ 2) / 2) := by
        rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ← Real.exp_sum]
        congr 2
        rw [mul_sum, sum_div]
        exact sum_congr rfl fun i _ => by ring

/-- [proved-derived; formal-checked] **The tail of incoherent signs.** With the magnitudes fixed
and `Q > 0`, at most `2^n e^(−t²/2)` of the `2^n` sign patterns have `S ≥ t √Q`. -/
theorem sign_tail (δ : Fin n → ℝ) (hQ : 0 < ∑ i, δ i ^ 2) {t : ℝ} (ht : 0 ≤ t) :
    ((univ.filter fun ε : Fin n → Bool =>
        t * Real.sqrt (∑ i, δ i ^ 2) ≤ signedSum δ ε).card : ℝ) ≤
      2 ^ n * Real.exp (-(t ^ 2 / 2)) := by
  set Q := ∑ i, δ i ^ 2
  set A := univ.filter fun ε : Fin n → Bool => t * Real.sqrt Q ≤ signedSum δ ε
  have hsq : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  set lam := t / Real.sqrt Q
  have hlam : 0 ≤ lam := div_nonneg ht hsq.le
  have hlamQ : lam ^ 2 * Q = t ^ 2 := by
    rw [div_pow, Real.sq_sqrt hQ.le]; field_simp
  have hlow : ∀ ε ∈ A, Real.exp (t ^ 2) ≤ Real.exp (lam * signedSum δ ε) := by
    intro ε hε
    have hε' := (mem_filter.mp hε).2
    apply Real.exp_le_exp.mpr
    have : lam * (t * Real.sqrt Q) = t ^ 2 := by
      simp only [lam]; field_simp
    rw [← this]
    exact mul_le_mul_of_nonneg_left hε' hlam
  have hA : (A.card : ℝ) * Real.exp (t ^ 2) ≤ 2 ^ n * Real.exp (t ^ 2 / 2) := by
    calc (A.card : ℝ) * Real.exp (t ^ 2) = ∑ ε ∈ A, Real.exp (t ^ 2) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ ε ∈ A, Real.exp (lam * signedSum δ ε) := sum_le_sum hlow
      _ ≤ ∑ ε : Fin n → Bool, Real.exp (lam * signedSum δ ε) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => (Real.exp_pos _).le
      _ ≤ 2 ^ n * Real.exp (lam ^ 2 * Q / 2) := sign_mgf_le δ lam
      _ = 2 ^ n * Real.exp (t ^ 2 / 2) := by rw [hlamQ]
  have he : Real.exp (t ^ 2) = Real.exp (t ^ 2 / 2) * Real.exp (t ^ 2 / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hneg : Real.exp (-(t ^ 2 / 2)) * Real.exp (t ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (t ^ 2 / 2)
  rw [he] at hA
  have hA' : (A.card : ℝ) * Real.exp (t ^ 2 / 2) ≤ 2 ^ n := by
    have := le_of_mul_le_mul_right (by nlinarith [hA] :
      (A.card : ℝ) * Real.exp (t ^ 2 / 2) * Real.exp (t ^ 2 / 2) ≤
        2 ^ n * Real.exp (t ^ 2 / 2)) hpos
    exact this
  calc (A.card : ℝ) = (A.card : ℝ) * Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2 / 2)) := by
        rw [mul_assoc, mul_comm (Real.exp _) (Real.exp _), hneg, mul_one]
    _ ≤ 2 ^ n * Real.exp (-(t ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_right hA' (Real.exp_pos _).le

/-- [proved-derived; formal-checked] **Both tails.** At most `2 · 2^n e^(−t²/2)` sign patterns
have `|S| ≥ t √Q`: if the signs carry nothing, `|S|/√Q ≥ √(2 ln(2/α))` has probability at
most `α`. -/
theorem sign_tail_abs (δ : Fin n → ℝ) (hQ : 0 < ∑ i, δ i ^ 2) {t : ℝ} (ht : 0 ≤ t) :
    ((univ.filter fun ε : Fin n → Bool =>
        t * Real.sqrt (∑ i, δ i ^ 2) ≤ |signedSum δ ε|).card : ℝ) ≤
      2 * (2 ^ n * Real.exp (-(t ^ 2 / 2))) := by
  have hneg : ∀ ε, signedSum (fun i => -δ i) ε = -signedSum δ ε := by
    intro ε; simp only [signedSum, mul_neg, sum_neg_distrib]
  have hQ' : ∑ i, (fun i => -δ i) i ^ 2 = ∑ i, δ i ^ 2 := by simp
  have h1 := sign_tail δ hQ ht
  have h2 := sign_tail (fun i => -δ i) (by rw [hQ']; exact hQ) ht
  rw [hQ'] at h2
  simp only [hneg] at h2
  have hsub : (univ.filter fun ε : Fin n → Bool =>
        t * Real.sqrt (∑ i, δ i ^ 2) ≤ |signedSum δ ε|) ⊆
      (univ.filter fun ε => t * Real.sqrt (∑ i, δ i ^ 2) ≤ signedSum δ ε) ∪
        (univ.filter fun ε => t * Real.sqrt (∑ i, δ i ^ 2) ≤ -signedSum δ ε) := by
    intro ε hε
    rw [mem_filter] at hε
    rw [mem_union, mem_filter, mem_filter]
    rcases le_total 0 (signedSum δ ε) with h | h
    · left; exact ⟨mem_univ _, by rw [abs_of_nonneg h] at hε; exact hε.2⟩
    · right; exact ⟨mem_univ _, by rw [abs_of_nonpos h] at hε; exact hε.2⟩
  calc ((univ.filter fun ε : Fin n → Bool =>
          t * Real.sqrt (∑ i, δ i ^ 2) ≤ |signedSum δ ε|).card : ℝ)
      ≤ (((univ.filter fun ε => t * Real.sqrt (∑ i, δ i ^ 2) ≤ signedSum δ ε) ∪
          (univ.filter fun ε => t * Real.sqrt (∑ i, δ i ^ 2) ≤ -signedSum δ ε)).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ((univ.filter fun ε => t * Real.sqrt (∑ i, δ i ^ 2) ≤ signedSum δ ε).card : ℝ) +
          ((univ.filter fun ε => t * Real.sqrt (∑ i, δ i ^ 2) ≤ -signedSum δ ε).card : ℝ) := by
        exact_mod_cast card_union_le _ _
    _ ≤ _ := by linarith

/-- [proved-standard; formal-checked] **The coherence ratio is at most `√n`.** `S² ≤ n Q`
(Cauchy–Schwarz). -/
theorem coherence_ratio_le (δ : Fin n → ℝ) : (∑ i, δ i) ^ 2 ≤ n * ∑ i, δ i ^ 2 := by
  have := sq_sum_le_card_mul_sum_sq (s := univ) (f := δ)
  simpa using this

/-- [proved-standard; formal-checked] **One sign gives a ratio of at least one.** Updates of one
sign have `Q ≤ S²`. -/
theorem coherence_ratio_one_sign (δ : Fin n → ℝ) (h : ∀ i, 0 ≤ δ i) :
    ∑ i, δ i ^ 2 ≤ (∑ i, δ i) ^ 2 := by
  rw [sq, sum_mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [sq]
  exact single_le_sum (f := fun j => δ i * δ j) (fun j _ => mul_nonneg (h i) (h j)) (mem_univ i)

end Signs

/-! ## 4. The Kraft bound on the code's schedule is tight -/

section Tight

variable {L : ℕ} {E : Type*}

/-- [proved-derived; formal-checked] **A value at the lower edge of the fine cell rounds to zero.**
The nearest-point rule ties upward, so `−½·2^(−L−k)` has fine point `0` and is released whole. -/
theorem fine_neg_half_cell (k : ℕ) : fine L k (-(unit (L + k) / 2)) = 0 := by
  have hc := unit_pos (L + k)
  have hq : quot (L + k) (-(unit (L + k) / 2)) = 0 := by
    unfold quot
    have e : -(unit (L + k) / 2) / unit (L + k) = -(1 / 2) := by field_simp
    rw [e, round_eq]
    norm_num
  simp [fine, hq]

/-- [proved-derived; formal-checked] **Its release is the whole half cell.** -/
theorem rem_neg_half_cell (k : ℕ) :
    rem (L + k) (-(unit (L + k) / 2)) = -(unit (L + k) / 2) := by
  have h := fine_neg_half_cell (L := L) k
  unfold fine at h
  unfold rem
  rw [h, sub_zero]

/-- [definition] The update that releases deposit `m`'s whole half fine cell at every entry. -/
def drainStep (L m : ℕ) : E → ℚ := fun _ => -(unit (L + gammaLength m) / 2)

/-- [definition] `n` such updates, from the clock `c`. -/
def drain (L : ℕ) : ℕ → ℕ → List (E → ℚ)
  | _, 0 => []
  | c, n + 1 => drainStep L (c + 1) :: drain L (c + 1) n

theorem drainStep_ne [Nonempty E] (m : ℕ) : (drainStep L m : E → ℚ) ≠ 0 := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty E›
  have hi := congrFun h i
  have hc := unit_pos (L + gammaLength m)
  simp only [drainStep, Pi.zero_apply] at hi
  linarith

/-- One drain update at a carrier with no remainder: nothing moves, the remainder stays zero, and
the release is the whole half fine cell `(u/2)·2^(−k_m)`. -/
theorem carry_drainStep [Nonempty E] (s : Carried L E) (hs : ∀ i, s.rem i = 0) (i : E) :
    (carry s (drainStep L (s.clock + 1))).value i = s.value i ∧
    (carry s (drainStep L (s.clock + 1))).rem i = 0 ∧
    (carry s (drainStep L (s.clock + 1))).clock = s.clock + 1 ∧
    release s (drainStep L (s.clock + 1)) i = -(unit L / 2 * gammaWeight (s.clock + 1)) := by
  have hne := drainStep_ne (L := L) (E := E) (s.clock + 1)
  have hf := fine_neg_half_cell (L := L) (gammaLength (s.clock + 1))
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [carry, hne, step, drainStep, hs i, hf, quot]
  · simp [carry, hne, step, drainStep, hs i, hf, rem, quot]
  · simp [carry, hne, step]
  · simp only [release, if_neg hne, drainStep, hs i, add_zero]
    rw [rem_neg_half_cell, half_fine_unit]

/-- [proved-derived; formal-checked] **A run of drain updates.** From a carrier with no remainder,
`n` drain updates leave every value where it was and release exactly
`−(u/2) Σ_(m ∈ (c, c+n]) 2^(−k_m)` at every entry. -/
theorem drain_run [Nonempty E] (n : ℕ) (s : Carried L E) (hs : ∀ i, s.rem i = 0) (i : E) :
    (run s (drain L s.clock n)).value i = s.value i ∧
    released s (drain L s.clock n) i =
      -(unit L / 2 * ∑ m ∈ Finset.Ioc s.clock (s.clock + n), gammaWeight m) := by
  induction n generalizing s with
  | zero => simp [drain, run, released]
  | succ n ih =>
    set t := carry s (drainStep L (s.clock + 1))
    have ht := fun j => carry_drainStep (L := L) s hs j
    have htrem : ∀ j, t.rem j = 0 := fun j => (ht j).2.1
    have hclock : t.clock = s.clock + 1 := (ht i).2.2.1
    have hrest := ih t htrem
    rw [hclock] at hrest
    have hrun : run s (drain L s.clock (n + 1)) = run t (drain L (s.clock + 1) n) := rfl
    have hrel : released s (drain L s.clock (n + 1)) i =
        release s (drainStep L (s.clock + 1)) i + released t (drain L (s.clock + 1) n) i := rfl
    refine ⟨?_, ?_⟩
    · rw [hrun, hrest.1, (ht i).1]
    · rw [hrel, hrest.2, (ht i).2.2.2]
      have hsplit : Finset.Ioc s.clock (s.clock + (n + 1)) =
          insert (s.clock + 1) (Finset.Ioc (s.clock + 1) (s.clock + 1 + n)) := by
        ext m; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
      have hnot : s.clock + 1 ∉ Finset.Ioc (s.clock + 1) (s.clock + 1 + n) := by simp
      rw [hsplit, Finset.sum_insert hnot]
      ring

/-- [proved-derived; formal-checked] **`release_bound_tight`: half a unit is the least bound.**
From a founding carrier, `2^J − 1` deposits can leave an entry where it was while the releases
total exactly `(u/2)(1 − 2^(−J))`: the exact accumulation moves by that much and the entry not at
all. With `release_bounded_since_founding` (`< u/2`), half a lattice unit is the supremum of what
the code's precision schedule can drop at one entry since its founding. -/
theorem release_bound_tight [Nonempty E] (value : E → ℚ) (J : ℕ) (i : E) :
    (run (Carried.fresh (L := L) value) (drain L 0 (2 ^ J - 1))).value i = value i ∧
    released (Carried.fresh (L := L) value) (drain L 0 (2 ^ J - 1)) i =
      -(unit L / 2 * (1 - ((2 : ℚ) ^ J)⁻¹)) := by
  have h := drain_run (L := L) (2 ^ J - 1) (Carried.fresh value) (fun _ => rfl) i
  have h2 : released (Carried.fresh (L := L) value) (drain L 0 (2 ^ J - 1)) i =
      -(unit L / 2 * ∑ m ∈ Finset.Ioc 0 (0 + (2 ^ J - 1)), gammaWeight m) := h.2
  refine ⟨h.1, ?_⟩
  rw [h2]
  have hw : Finset.Ioc 0 (0 + (2 ^ J - 1)) = Finset.Ico 1 (2 ^ J) := by
    ext m; simp only [Finset.mem_Ioc, Finset.mem_Ico]
    have := Nat.one_le_two_pow (n := J); omega
  rw [hw, gamma_prefix]

end Tight

/-! ## 5. The step against the fine cell -/

section Cell

/-- [proved-derived; formal-checked] **The fine cell refines as `1/m²`.** At clock `m ≥ 1`,
`1/(2m²) ≤ 2^(−k_m) < 2/m²`: the precision `k_m = 2⌊log₂ m⌋ + 1` doubles the bits of the clock. -/
theorem gammaWeight_bounds {m : ℕ} (hm : 1 ≤ m) :
    1 / (2 * (m : ℚ) ^ 2) ≤ gammaWeight m ∧ gammaWeight m < 2 / (m : ℚ) ^ 2 := by
  set j := Nat.log 2 m
  have hlo : 2 ^ j ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hhi : m < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have hloq : (2 : ℚ) ^ j ≤ m := by exact_mod_cast hlo
  have hhiq : (m : ℚ) < 2 ^ (j + 1) := by exact_mod_cast hhi
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm
  have hp : (0 : ℚ) < 2 ^ j := by positivity
  have hk : (2 : ℚ) ^ gammaLength m = 2 * ((2 : ℚ) ^ j) ^ 2 := by
    unfold gammaLength; rw [← pow_mul]; ring
  unfold gammaWeight
  rw [hk]
  constructor
  · rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith
  · rw [inv_lt_iff_one_lt_mul₀ (by positivity)]
    have hm2 : (m : ℚ) ^ 2 < 4 * ((2 : ℚ) ^ j) ^ 2 := by
      have : (2 : ℚ) ^ (j + 1) = 2 * 2 ^ j := by ring
      rw [this] at hhiq
      nlinarith
    rw [div_mul_eq_mul_div, one_lt_div (by positivity)]
    nlinarith

/-- [proved-derived; formal-checked] **`step_exceeds_fine_cell`: a step decaying as `1/m` is not
released.** At clock `m ≥ 1` the half fine cell is at most `u/m²`. An update of size at least
`κ′/m` with `u < κ′ m` therefore exceeds it, so it is carried into the remainder (or the value),
never released whole as below the grain (`carry_entry_below_grain`). A step that decays as `1/m`
meets a fine cell that refines as `1/m²`, so the fine lattice keeps it; the coarse unit `u` is what
it fails to reach, at the rate of the logarithm law. -/
theorem step_exceeds_fine_cell (L : ℕ) {m : ℕ} (hm : 1 ≤ m) {κ' δ : ℚ}
    (hκm : unit L < κ' * m) (hδ : κ' / m ≤ |δ|) :
    unit (L + gammaLength m) / 2 < |δ| := by
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm
  have hu := unit_pos L
  rw [half_fine_unit]
  have hw := (gammaWeight_bounds hm).2
  have h1 : unit L / 2 * gammaWeight m < unit L / (m : ℚ) ^ 2 := by
    calc unit L / 2 * gammaWeight m < unit L / 2 * (2 / (m : ℚ) ^ 2) :=
          mul_lt_mul_of_pos_left hw (by positivity)
      _ = unit L / (m : ℚ) ^ 2 := by field_simp
  have h2 : unit L / (m : ℚ) ^ 2 < κ' / m := by
    rw [div_lt_div_iff₀ (by positivity) hmq]
    nlinarith
  linarith

end Cell

/-! ## 6. The bound under a schedule that refines as the confirmable grain -/

section Schedule

/-- [proved-derived; formal-checked] **Any precision schedule's releases.** A release at precision
`k` is the remainder at the fine lattice `2^(−L−k)ℤ`, at most `(u/2)·2^(−k)`. So over deposits with
precisions `k_j`, the releases at one entry total at most `(u/2) Σ_j 2^(−k_j)`, whatever the values
split. Under the code's schedule the sum is a Kraft sum below one; the bound is that sum. -/
theorem schedule_release_le (L : ℕ) (ps : List (ℕ × ℚ)) :
    |(ps.map fun p => rem (L + p.1) p.2).sum| ≤
      unit L / 2 * (ps.map fun p => ((2 : ℚ) ^ p.1)⁻¹).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    have hb := rem_bounds (L + p.1) p.2
    have hone : |rem (L + p.1) p.2| ≤ unit L / 2 * ((2 : ℚ) ^ p.1)⁻¹ := by
      have e : unit (L + p.1) / 2 = unit L / 2 * ((2 : ℚ) ^ p.1)⁻¹ := by
        unfold unit; rw [pow_add]; field_simp
      rw [abs_le, ← e]
      exact ⟨hb.1, hb.2.le⟩
    exact (abs_add_le _ _).trans (add_le_add hone ih)

/-- [proved-derived; formal-checked] **…and every schedule can drop all of it.** At each
precision the value `−½·2^(−L−k)` has fine point zero, so from a zero remainder it moves nothing,
leaves the remainder zero, and releases its whole half cell; a run of such updates drops exactly
`(u/2) Σ_j 2^(−k_j)` while the entry stays put. -/
theorem schedule_release_attained (L : ℕ) (ks : List ℕ) :
    (ks.map fun k => fine L k (-(unit (L + k) / 2))).sum = 0 ∧
    (ks.map fun k => rem (L + k) (-(unit (L + k) / 2))).sum =
      -(unit L / 2 * (ks.map fun k => ((2 : ℚ) ^ k)⁻¹).sum) := by
  have hr : ∀ k, rem (L + k) (-(unit (L + k) / 2)) = -(unit L / 2 * ((2 : ℚ) ^ k)⁻¹) := by
    intro k; rw [rem_neg_half_cell]; unfold unit; rw [pow_add]; field_simp
  refine ⟨by simp [fine_neg_half_cell], ?_⟩
  simp only [hr]
  induction ks with
  | nil => simp
  | cons k ks ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- [proved-derived; formal-checked] **`refining_schedule_kraft_ge`: a schedule refining as the
confirmable grain is not summable.** Suppose deposit `m`'s fine cell is the dyadic refinement of
`1/L(m)` of a unit (`2^(k_m) ≤ 2 L(m)`), with `L(m) ≤ 2√m` (the refining grain
`L(N) = ⌈√(N ln 2/2)⌉` of `HNN/Ratio/Resolution`, PR #151, satisfies it: `L(N) < √(N ln 2/2) + 1`
and `ln 2/2 < 1`). Then the weights of the first `N` deposits sum to at least `√N/4`. -/
theorem refining_schedule_kraft_ge (k Lr : ℕ → ℕ) (hk : ∀ m, 2 ^ k m ≤ 2 * Lr m)
    (hL : ∀ m, 1 ≤ m → (Lr m : ℝ) ≤ 2 * Real.sqrt m) (N : ℕ) :
    Real.sqrt N / 4 ≤ ∑ m ∈ Finset.Icc 1 N, ((2 : ℝ) ^ k m)⁻¹ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
  have hterm : ∀ m ∈ Finset.Icc 1 N, 1 / (4 * Real.sqrt N) ≤ ((2 : ℝ) ^ k m)⁻¹ := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
    have hmN : (m : ℝ) ≤ N := by exact_mod_cast hm.2
    have hsm : Real.sqrt m ≤ Real.sqrt N := Real.sqrt_le_sqrt hmN
    have h2k : (2 : ℝ) ^ k m ≤ 2 * Lr m := by exact_mod_cast hk m
    have hpos : (0 : ℝ) < 2 ^ k m := by positivity
    have hle : (2 : ℝ) ^ k m ≤ 4 * Real.sqrt N := by linarith [hL m hm.1]
    rw [one_div]
    exact inv_anti₀ hpos hle
  calc Real.sqrt N / 4 = ∑ _m ∈ Finset.Icc 1 N, 1 / (4 * Real.sqrt N) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
        field_simp
        rw [Real.sq_sqrt hNr.le]
    _ ≤ _ := Finset.sum_le_sum hterm

/-- [proved-derived; formal-checked] **The half-unit conclusion fails under that schedule.** From
`N = 16` deposits the weights reach one, so the bound `schedule_release_le` no longer keeps the
drop below `u/2`, and `schedule_release_attained` shows the drop is reached: an entry can stay put
while the exact accumulation moves by `(u/2)·√N/4`, a whole unit from `N = 64` and without bound
after. -/
theorem refining_schedule_kraft_ge_one (k Lr : ℕ → ℕ) (hk : ∀ m, 2 ^ k m ≤ 2 * Lr m)
    (hL : ∀ m, 1 ≤ m → (Lr m : ℝ) ≤ 2 * Real.sqrt m) {N : ℕ} (hN : 16 ≤ N) :
    1 ≤ ∑ m ∈ Finset.Icc 1 N, ((2 : ℝ) ^ k m)⁻¹ := by
  have h := refining_schedule_kraft_ge k Lr hk hL N
  have h16 : (4 : ℝ) ≤ Real.sqrt N := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  linarith

end Schedule

section Audit

#print axioms fraction_le_log
#print axioms log_le_fraction
#print axioms sum_log_ratio
#print axioms sum_fraction_le_log
#print axioms move_le_log
#print axioms move_needs_growth
#print axioms coherent_move_ge
#print axioms frozen_accumulation_lt_unit
#print axioms moved_of_accumulation
#print axioms sign_mgf_le
#print axioms sign_tail
#print axioms sign_tail_abs
#print axioms coherence_ratio_le
#print axioms coherence_ratio_one_sign
#print axioms fine_neg_half_cell
#print axioms rem_neg_half_cell
#print axioms carry_drainStep
#print axioms drain_run
#print axioms release_bound_tight
#print axioms gammaWeight_bounds
#print axioms step_exceeds_fine_cell
#print axioms schedule_release_le
#print axioms schedule_release_attained
#print axioms refining_schedule_kraft_ge
#print axioms refining_schedule_kraft_ge_one

end Audit

end Holonics.HNN.LatticeDeposit.Freeze

end
