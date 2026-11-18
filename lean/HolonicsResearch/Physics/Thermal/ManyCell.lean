import Mathlib
import Holonics.Physics.Thermal.Exchange

/-!
# Many thermal cells joined by contacts, and a chain's rates read as heat

[definition] Source: the owed-statements issue (#410, "Fluid and heat"): many-cell diffusion, where
`Physics/Thermal/Exchange` holds the two-cell balance, and the join from a chain's transition rates
to physical heat. Atlas `heat.two-cell-exchange`, `heat.contact-diffusion-holon` (whose scope names
the many-cell case as not yet written) and `info.contact-kl-diffusion`.

A finite set of cells `ι` is joined by contacts of conductance `g i j`, symmetric and nonnegative.
The readings `u : ι → K` (a temperature, or a ratio `p/π`) move by the **flow**
`(L u)_i = Σ_j g_ij (u_j − u_i)` (`flow`), and one tick of length `τ` is `u′ = u + τ L u` (`step`).
`K` is any ordered field, so the same statements hold on `ℚ` (the tick of `Exchange`) and on `ℝ`.

[proved-standard; formal-checked] What is proved.

1. **The total is kept** (`sum_flow`, `sum_step`): what leaves one cell through a contact enters the
   other.
2. **The flow pairs through the contacts.** For any two readings,
   `Σ_i v_i (L u)_i = −½ Σ_(i,j) g_ij (v_i − v_j)(u_i − u_j)` (`pairing`), so the flow is
   self-adjoint (`flow_selfAdjoint`) and the dissipation is a sum over contacts of the square of the
   slip, `Σ_i u_i (L u)_i = −½ Σ_(i,j) g_ij (u_i − u_j)²` (`dissipation`; `slip`).
3. **The tick's energy balance** (`step_energy`):
   `Σ u′² = Σ u² − τ·slip + τ² Σ (L u)²`. With `Σ_j g_ij ≤ D` at every cell,
   `Σ (L u)² ≤ D·slip` (`flow_sq_le`, `sum_flow_sq_le`), so
   `Σ u′² ≤ Σ u² − τ(1 − τD)·slip` (`step_energy_drop`), and the energy does not rise when
   `0 ≤ τ` and `τ D ≤ 1` (`step_energy_le`). The two-cell tick condition of `Exchange`,
   `hκ(1/C₁ + 1/C₂) ≤ 1`, is this bound's kin with capacities.
4. **Rest.** The slip vanishes, and the flow vanishes at every cell, exactly when the readings agree
   across every contact of positive conductance (`slip_eq_zero_iff`, `flow_eq_zero_iff`); when the
   contacts join every pair of cells through some chain, exactly when the reading is one constant
   (`rest_iff_const`). A tick with `τ ≠ 0` fixes exactly the states at rest (`step_eq_self_iff`).
5. **No new extreme.** When `0 ≤ τ` and `τ Σ_j g_ij ≤ 1` at a cell, its next reading is a convex
   combination of the present ones (`step_eq_convex`), so it stays between any bounds the present
   readings keep (`le_step`, `step_le`), and so does every later tick (`iterate_step_bounds`).
6. **Entropy production** (over `ℝ`, positive readings): the production
   `Σ_(i,j) g_ij (u_j − u_i)(log u_j − log u_i)` is nonnegative and zero exactly at rest
   (`production_nonneg`, `production_eq_zero_iff`), and it is the flow paired with the logarithm,
   `Σ_i log u_i · (L u)_i = −½·production` (`flow_log`).
7. **A chain's rates are a heat network.** For rates `k i j` in detailed balance with a positive
   `π`, `π_i k_ij = π_j k_ji`, the master equation `ṗ_i = Σ_j (p_j k_ji − p_i k_ij)` (`master`) is
   the flow of the readings `u = p/π` through the symmetric conductances `g_ij = π_i k_ij`
   (`conductance_symm`, `master_eq_flow`): `π` is the capacity, `p` the stored quantity and `p/π`
   the temperature. So the total is kept (`sum_master`, which needs no balance), `π` rests
   (`master_stationary`), the `π`-weighted energy falls by the slip (`master_dissipation`), a
   distribution rests exactly when `p/π` agrees across every contact (`master_eq_zero_iff`), and
   along the master equation `Σ_i (p_i log(p_i/π_i) − p_i)`, the relative entropy `D(p‖π)` up to
   the kept total, falls at half the production (`hasDerivAt_relative_entropy`,
   `relative_entropy_rate_nonpos`). In the other direction a heat network of capacities `C` and
   conductances `κ` is the chain of rates `κ_ij/C_i`, in detailed balance with `C`
   (`heatRates_detailedBalance`, `heatTick_eq_master`).
8. **Clausius, many cells.** The heat entering the cells weighed by inverse temperature is half the
   sum over ordered pairs of `Exchange.productionRate` (`clausius`, `clausius_productionRate` on
   `ℚ`), nonnegative at positive temperatures (`clausius_nonneg`); along the heat law the entropy
   `Σ C_i log U_i` of `Exchange` rises at that rate (`hasDerivAt_entropy`).
9. **Two cells.** On two cells the heat tick is `Exchange.next₁`, `Exchange.next₂` without port
   work (`two_cell`).

Limits. The contacts' conductances are fixed (no dependence on the readings), the tick is the
explicit one, and no port work is carried beyond the two-cell reduction. The energy bound of item 3
is stated with capacities equal to one; with capacities the same argument runs in the variable
`p/π` at the weighted degree and is not restated. The continuum limit (a diffusion equation on a
refining family of complexes) is not here.

Computational object: the helical pair interaction, read at its dissipating part: a contact's slip
`u_i − u_j` and its square (pair; faces and placement, the cells' readings). The helix, cell
holonomy, tube and tower thread stay attached and are not touched.

Consumers: `Holonics.Physics.Thermal.Exchange` (the two-cell tick and its production rate, reduced to
here by `two_cell` and `clausius_productionRate`); atlas `info.contact-kl-diffusion`,
`heat.contact-diffusion-holon`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Physics.Thermal.ManyCell

open Finset

/-! ## 1. Sums over ordered pairs of cells -/

section Pairs

variable {ι : Type*} [Fintype ι] {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- [proved-standard] A sum over ordered pairs of an antisymmetric term vanishes. -/
theorem sum_antisymm (a : ι → ι → K) (h : ∀ i j, a i j = -a j i) : ∑ i, ∑ j, a i j = 0 := by
  have h1 : ∑ i, ∑ j, a i j = -∑ i, ∑ j, a i j := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact h j i
  linarith

/-- [proved-standard] A sum over ordered pairs is half the sum of its term and the term with the two
cells exchanged. -/
theorem sum_symmetrize (b : ι → ι → K) :
    ∑ i, ∑ j, b i j = (1 / 2) * ∑ i, ∑ j, (b i j + b j i) := by
  have h1 : ∑ i, ∑ j, (b i j + b j i) = ∑ i, ∑ j, b i j + ∑ i, ∑ j, b j i := by
    simp only [Finset.sum_add_distrib]
  have h2 : ∑ i, ∑ j, b j i = ∑ i, ∑ j, b i j := Finset.sum_comm
  rw [h1, h2]
  ring

end Pairs

/-! ## 2. The flow, its kept total and its pairing through the contacts -/

section Flow

variable {ι : Type*} [Fintype ι] {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- [definition] **The flow** into cell `i`: each contact carries its conductance times the
difference of the readings at its two ends. -/
def flow (g : ι → ι → K) (u : ι → K) (i : ι) : K := ∑ j, g i j * (u j - u i)

/-- [definition] **One tick** of length `τ`. -/
def step (g : ι → ι → K) (τ : K) (u : ι → K) (i : ι) : K := u i + τ * flow g u i

/-- [definition] **The slip** of a reading: the sum over ordered pairs of cells of the conductance
times the square of the difference (each contact counted from both ends). -/
def slip (g : ι → ι → K) (u : ι → K) : K := ∑ i, ∑ j, g i j * (u i - u j) ^ 2

/-- [definition] The whole conductance at a cell. -/
def degree (g : ι → ι → K) (i : ι) : K := ∑ j, g i j

variable {g : ι → ι → K}

/-- [proved-standard] **The flow keeps the total.** -/
theorem sum_flow (hg : ∀ i j, g i j = g j i) (u : ι → K) : ∑ i, flow g u i = 0 := by
  unfold flow
  refine sum_antisymm _ fun i j => ?_
  rw [hg j i]
  ring

/-- [proved-standard] **A tick keeps the total.** -/
theorem sum_step (hg : ∀ i j, g i j = g j i) (τ : K) (u : ι → K) :
    ∑ i, step g τ u i = ∑ i, u i := by
  unfold step
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_flow hg, mul_zero, add_zero]

/-- [proved-standard] **The flow pairs through the contacts**:
`Σ_i v_i (L u)_i = −½ Σ_(i,j) g_ij (v_i − v_j)(u_i − u_j)`. -/
theorem pairing (hg : ∀ i j, g i j = g j i) (v u : ι → K) :
    ∑ i, v i * flow g u i = -(1 / 2) * ∑ i, ∑ j, g i j * (v i - v j) * (u i - u j) := by
  unfold flow
  have h0 : ∑ i, v i * ∑ j, g i j * (u j - u i) = ∑ i, ∑ j, v i * (g i j * (u j - u i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [h0, sum_symmetrize]
  have h1 : ∑ i, ∑ j, (v i * (g i j * (u j - u i)) + v j * (g j i * (u i - u j))) =
      -∑ i, ∑ j, g i j * (v i - v j) * (u i - u j) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg j i]
    ring
  rw [h1]
  ring

/-- [proved-standard] **The flow is self-adjoint.** -/
theorem flow_selfAdjoint (hg : ∀ i j, g i j = g j i) (v u : ι → K) :
    ∑ i, v i * flow g u i = ∑ i, u i * flow g v i := by
  rw [pairing hg, pairing hg]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- [proved-standard] **Dissipation is the slip**: `Σ_i u_i (L u)_i = −½ Σ_(i,j) g_ij (u_i − u_j)²`. -/
theorem dissipation (hg : ∀ i j, g i j = g j i) (u : ι → K) :
    ∑ i, u i * flow g u i = -(1 / 2) * slip g u := by
  rw [pairing hg]
  unfold slip
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- [proved-standard] The slip is nonnegative. -/
theorem slip_nonneg (hg0 : ∀ i j, 0 ≤ g i j) (u : ι → K) : 0 ≤ slip g u :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hg0 i j) (sq_nonneg _)

/-! ## 3. The tick's energy -/

/-- [proved-standard] **The tick's energy balance**:
`Σ u′² = Σ u² − τ·slip + τ² Σ (L u)²`. -/
theorem step_energy (hg : ∀ i j, g i j = g j i) (τ : K) (u : ι → K) :
    ∑ i, step g τ u i ^ 2 = ∑ i, u i ^ 2 - τ * slip g u + τ ^ 2 * ∑ i, flow g u i ^ 2 := by
  have h : ∀ i, step g τ u i ^ 2 =
      u i ^ 2 + 2 * τ * (u i * flow g u i) + τ ^ 2 * flow g u i ^ 2 := by
    intro i
    unfold step
    ring
  have h2 : ∑ i, step g τ u i ^ 2 =
      ∑ i, u i ^ 2 + 2 * τ * ∑ i, u i * flow g u i + τ ^ 2 * ∑ i, flow g u i ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => h i
  rw [h2, dissipation hg]
  ring

/-- [proved-standard] **Cauchy–Schwarz at one cell**: the square of the flow is at most the cell's
whole conductance times its own share of the slip. -/
theorem flow_sq_le (hg0 : ∀ i j, 0 ≤ g i j) (u : ι → K) (i : ι) :
    flow g u i ^ 2 ≤ degree g i * ∑ j, g i j * (u j - u i) ^ 2 := by
  unfold flow degree
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ => hg0 i j)
    (fun j _ => mul_nonneg (hg0 i j) (sq_nonneg _)) (fun j _ => le_of_eq ?_)
  ring

/-- [proved-standard] With the whole conductance at most `D` at every cell,
`Σ (L u)² ≤ D·slip`. -/
theorem sum_flow_sq_le (hg0 : ∀ i j, 0 ≤ g i j) {D : K} (hD : ∀ i, degree g i ≤ D) (u : ι → K) :
    ∑ i, flow g u i ^ 2 ≤ D * slip g u := by
  calc ∑ i, flow g u i ^ 2
      ≤ ∑ i, degree g i * ∑ j, g i j * (u j - u i) ^ 2 :=
        Finset.sum_le_sum fun i _ => flow_sq_le hg0 u i
    _ ≤ ∑ i, D * ∑ j, g i j * (u j - u i) ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hD i)
          (Finset.sum_nonneg fun j _ => mul_nonneg (hg0 i j) (sq_nonneg _))
    _ = D * slip g u := by
        unfold slip
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

/-- [proved-standard] **The energy a tick sheds**: with `0 ≤ τ` and the whole conductance at most
`D` at every cell, `Σ u′² ≤ Σ u² − τ(1 − τD)·slip`. -/
theorem step_energy_drop (hg : ∀ i j, g i j = g j i) (hg0 : ∀ i j, 0 ≤ g i j) {τ D : K}
    (hD : ∀ i, degree g i ≤ D) (u : ι → K) :
    ∑ i, step g τ u i ^ 2 ≤ ∑ i, u i ^ 2 - τ * (1 - τ * D) * slip g u := by
  rw [step_energy hg]
  have h1 : τ ^ 2 * ∑ i, flow g u i ^ 2 ≤ τ ^ 2 * (D * slip g u) :=
    mul_le_mul_of_nonneg_left (sum_flow_sq_le hg0 hD u) (sq_nonneg τ)
  linarith

/-- [proved-standard] **The tick condition**: with `0 ≤ τ` and `τ D ≤ 1` the energy does not
rise. -/
theorem step_energy_le (hg : ∀ i j, g i j = g j i) (hg0 : ∀ i j, 0 ≤ g i j) {τ D : K}
    (hτ : 0 ≤ τ) (hD : ∀ i, degree g i ≤ D) (hτD : τ * D ≤ 1) (u : ι → K) :
    ∑ i, step g τ u i ^ 2 ≤ ∑ i, u i ^ 2 := by
  have h := step_energy_drop hg hg0 (τ := τ) hD u
  have h2 : 0 ≤ τ * (1 - τ * D) * slip g u :=
    mul_nonneg (mul_nonneg hτ (by linarith)) (slip_nonneg hg0 u)
  linarith

/-! ## 4. Rest -/

/-- [proved-standard] **The slip vanishes exactly when the readings agree across every contact** of
positive conductance. -/
theorem slip_eq_zero_iff (hg0 : ∀ i j, 0 ≤ g i j) (u : ι → K) :
    slip g u = 0 ↔ ∀ i j, 0 < g i j → u i = u j := by
  unfold slip
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hg0 i j) (sq_nonneg _))]
  constructor
  · intro h i j hij
    have hi := h i (Finset.mem_univ i)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hg0 i j) (sq_nonneg _))] at hi
    rcases mul_eq_zero.mp (hi j (Finset.mem_univ j)) with h0 | h0
    · exact absurd h0 hij.ne'
    · exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0)
  · intro h i _
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases (hg0 i j).eq_or_lt with h0 | h0
    · rw [← h0]
      ring
    · rw [h i j h0]
      ring

/-- [proved-standard] **Rest**: the flow vanishes at every cell exactly when the readings agree
across every contact of positive conductance. -/
theorem flow_eq_zero_iff (hg : ∀ i j, g i j = g j i) (hg0 : ∀ i j, 0 ≤ g i j) (u : ι → K) :
    (∀ i, flow g u i = 0) ↔ ∀ i j, 0 < g i j → u i = u j := by
  rw [← slip_eq_zero_iff hg0]
  constructor
  · intro h
    have hd := dissipation hg u
    simp only [h, mul_zero, Finset.sum_const_zero] at hd
    linarith
  · intro h i
    rw [slip_eq_zero_iff hg0] at h
    unfold flow
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases (hg0 i j).eq_or_lt with h0 | h0
    · rw [← h0]
      ring
    · rw [h i j h0]
      ring

/-- [proved-standard] **Rest on a joined set of cells**: when chains of contacts of positive
conductance join every pair of cells, the flow vanishes exactly on the constant readings. -/
theorem rest_iff_const (hg : ∀ i j, g i j = g j i) (hg0 : ∀ i j, 0 ≤ g i j)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => 0 < g a b) i j) (u : ι → K) :
    (∀ i, flow g u i = 0) ↔ ∀ i j, u i = u j := by
  rw [flow_eq_zero_iff hg hg0]
  constructor
  · intro h i j
    induction hconn i j with
    | refl => rfl
    | tail _ hbc ih => exact ih.trans (h _ _ hbc)
  · intro h i j _
    exact h i j

/-- [proved-standard] A tick of nonzero length fixes exactly the states at rest. -/
theorem step_eq_self_iff {τ : K} (hτ : τ ≠ 0) (u : ι → K) :
    (∀ i, step g τ u i = u i) ↔ ∀ i, flow g u i = 0 := by
  refine forall_congr' fun i => ?_
  unfold step
  constructor
  · intro h
    have h' : τ * flow g u i = 0 := by linarith
    exact (mul_eq_zero.mp h').resolve_left hτ
  · intro h
    rw [h]
    ring

/-! ## 5. No new extreme -/

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-standard] **The tick as a combination of the present readings**:
`u′_i = (1 − τ Σ_j g_ij) u_i + τ Σ_j g_ij u_j`. -/
theorem step_eq_convex (g : ι → ι → K) (τ : K) (u : ι → K) (i : ι) :
    step g τ u i = (1 - τ * degree g i) * u i + τ * ∑ j, g i j * u j := by
  unfold step flow degree
  have h : ∑ j, g i j * (u j - u i) = ∑ j, g i j * u j - (∑ j, g i j) * u i := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h]
  ring

/-- [proved-standard] **No new minimum**: under `0 ≤ τ` and `τ Σ_j g_ij ≤ 1` at the cell, a lower
bound of the present readings bounds the next reading. -/
theorem le_step (hg0 : ∀ i j, 0 ≤ g i j) {τ : K} (hτ : 0 ≤ τ) {u : ι → K} {i : ι}
    (hi : τ * degree g i ≤ 1) {m : K} (hm : ∀ j, m ≤ u j) : m ≤ step g τ u i := by
  have key : step g τ u i - m =
      (1 - τ * degree g i) * (u i - m) + τ * ∑ j, g i j * (u j - m) := by
    rw [step_eq_convex]
    have h : ∑ j, g i j * (u j - m) = ∑ j, g i j * u j - degree g i * m := by
      unfold degree
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h]
    ring
  have h1 : 0 ≤ (1 - τ * degree g i) * (u i - m) :=
    mul_nonneg (by linarith) (by linarith [hm i])
  have h2 : 0 ≤ τ * ∑ j, g i j * (u j - m) :=
    mul_nonneg hτ (Finset.sum_nonneg fun j _ => mul_nonneg (hg0 i j) (by linarith [hm j]))
  linarith

/-- [proved-standard] **No new maximum**: under `0 ≤ τ` and `τ Σ_j g_ij ≤ 1` at the cell, an upper
bound of the present readings bounds the next reading. -/
theorem step_le (hg0 : ∀ i j, 0 ≤ g i j) {τ : K} (hτ : 0 ≤ τ) {u : ι → K} {i : ι}
    (hi : τ * degree g i ≤ 1) {M : K} (hM : ∀ j, u j ≤ M) : step g τ u i ≤ M := by
  have key : M - step g τ u i =
      (1 - τ * degree g i) * (M - u i) + τ * ∑ j, g i j * (M - u j) := by
    rw [step_eq_convex]
    have h : ∑ j, g i j * (M - u j) = degree g i * M - ∑ j, g i j * u j := by
      unfold degree
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h]
    ring
  have h1 : 0 ≤ (1 - τ * degree g i) * (M - u i) :=
    mul_nonneg (by linarith) (by linarith [hM i])
  have h2 : 0 ≤ τ * ∑ j, g i j * (M - u j) :=
    mul_nonneg hτ (Finset.sum_nonneg fun j _ => mul_nonneg (hg0 i j) (by linarith [hM j]))
  linarith

/-- [proved-standard] **Bounds are kept by every later tick** under `0 ≤ τ` and `τ Σ_j g_ij ≤ 1`
at every cell. -/
theorem iterate_step_bounds (hg0 : ∀ i j, 0 ≤ g i j) {τ : K} (hτ : 0 ≤ τ)
    (hd : ∀ i, τ * degree g i ≤ 1) {u : ι → K} {m M : K} (hm : ∀ j, m ≤ u j)
    (hM : ∀ j, u j ≤ M) (n : ℕ) (i : ι) :
    m ≤ (step g τ)^[n] u i ∧ (step g τ)^[n] u i ≤ M := by
  induction n generalizing i with
  | zero => exact ⟨hm i, hM i⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨le_step hg0 hτ (hd i) fun j => (ih j).1, step_le hg0 hτ (hd i) fun j => (ih j).2⟩

/-! ## 6. A chain's rates read as a heat network -/

/-- [definition] **The master equation** of a chain with rates `k i j` from `i` to `j`:
`ṗ_i = Σ_j (p_j k_ji − p_i k_ij)`. -/
def master (k : ι → ι → K) (p : ι → K) (i : ι) : K := ∑ j, (p j * k j i - p i * k i j)

/-- [definition] **The conductance of a contact** read from the rates and the resting weights:
`g_ij = π_i k_ij`, the resting flux through the contact. -/
def conductance (π : ι → K) (k : ι → ι → K) (i j : ι) : K := π i * k i j

/-- [proved-standard] **The master equation keeps the total**, with or without balance. -/
theorem sum_master (k : ι → ι → K) (p : ι → K) : ∑ i, master k p i = 0 := by
  unfold master
  refine sum_antisymm _ fun i j => ?_
  ring

variable {π : ι → K} {k : ι → ι → K}

omit [Fintype ι] [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-standard] Detailed balance is the symmetry of the conductances. -/
theorem conductance_symm (hdb : ∀ i j, π i * k i j = π j * k j i) (i j : ι) :
    conductance π k i j = conductance π k j i := hdb i j

omit [Fintype ι] in
/-- [proved-standard] Nonnegative rates and weights give nonnegative conductances. -/
theorem conductance_nonneg (hπ : ∀ i, 0 ≤ π i) (hk : ∀ i j, 0 ≤ k i j) (i j : ι) :
    0 ≤ conductance π k i j := mul_nonneg (hπ i) (hk i j)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-standard] **The join from rates to heat**: under detailed balance the master equation is
the flow of the readings `p/π` through the conductances `π_i k_ij`. -/
theorem master_eq_flow (hπ : ∀ i, π i ≠ 0) (hdb : ∀ i j, π i * k i j = π j * k j i)
    (p : ι → K) (i : ι) :
    master k p i = flow (conductance π k) (fun j => p j / π j) i := by
  unfold master flow conductance
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj := hπ j
  have hi := hπ i
  have h1 : π i * k i j * (p j / π j) = p j * k j i := by
    rw [hdb i j]
    field_simp
  have h2 : π i * k i j * (p i / π i) = p i * k i j := by
    field_simp
  rw [mul_sub, h1, h2]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-standard] **The resting weights rest.** -/
theorem master_stationary (hdb : ∀ i j, π i * k i j = π j * k j i) (i : ι) :
    master k π i = 0 := by
  unfold master
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [hdb i j]
  ring

/-- [proved-standard] **The weighted energy falls by the slip**:
`Σ_i (p_i/π_i) ṗ_i = −½ Σ_(i,j) π_i k_ij (p_i/π_i − p_j/π_j)²`. -/
theorem master_dissipation (hπ : ∀ i, π i ≠ 0) (hdb : ∀ i j, π i * k i j = π j * k j i)
    (p : ι → K) :
    ∑ i, p i / π i * master k p i = -(1 / 2) * slip (conductance π k) fun j => p j / π j := by
  have h : ∀ i, p i / π i * master k p i =
      (fun j => p j / π j) i * flow (conductance π k) (fun j => p j / π j) i := by
    intro i
    rw [master_eq_flow hπ hdb]
  rw [Finset.sum_congr rfl fun i _ => h i]
  exact dissipation (conductance_symm hdb) _

/-- [proved-standard] **A distribution rests exactly when `p/π` agrees across every contact** that
carries a resting flux. -/
theorem master_eq_zero_iff (hπ : ∀ i, 0 < π i) (hk : ∀ i j, 0 ≤ k i j)
    (hdb : ∀ i j, π i * k i j = π j * k j i) (p : ι → K) :
    (∀ i, master k p i = 0) ↔ ∀ i j, 0 < k i j → p i / π i = p j / π j := by
  have h1 : (∀ i, master k p i = 0) ↔
      ∀ i, flow (conductance π k) (fun j => p j / π j) i = 0 :=
    forall_congr' fun i => by rw [master_eq_flow (fun i => (hπ i).ne') hdb]
  rw [h1, flow_eq_zero_iff (conductance_symm hdb)
    (conductance_nonneg (fun i => (hπ i).le) hk)]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  unfold conductance
  constructor
  · intro h hkij
    exact h (mul_pos (hπ i) hkij)
  · intro h hpos
    exact h ((mul_pos_iff_of_pos_left (hπ i)).mp hpos)

/-- [definition] **The heat tick** of cells with capacities `C`, energies `U` and conductances `κ`:
the temperatures `U/C` flow through the contacts for a tick `h`. -/
def heatTick (κ : ι → ι → K) (C : ι → K) (h : K) (U : ι → K) (i : ι) : K :=
  U i + h * flow κ (fun j => U j / C j) i

/-- [definition] The rates of the chain a heat network is: `k_ij = κ_ij / C_i`. -/
def heatRates (κ : ι → ι → K) (C : ι → K) (i j : ι) : K := κ i j / C i

omit [Fintype ι] [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-standard] **A heat network's rates are in detailed balance with its capacities.** -/
theorem heatRates_detailedBalance {κ : ι → ι → K} {C : ι → K} (hκ : ∀ i j, κ i j = κ j i)
    (hC : ∀ i, C i ≠ 0) (i j : ι) : C i * heatRates κ C i j = C j * heatRates κ C j i := by
  unfold heatRates
  have hi := hC i
  have hj := hC j
  rw [hκ j i]
  field_simp

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-standard] **The heat tick is a tick of the master equation** of the chain with rates
`κ_ij / C_i`: the energies are the chain's weights. -/
theorem heatTick_eq_master {κ : ι → ι → K} {C : ι → K} (hκ : ∀ i j, κ i j = κ j i)
    (hC : ∀ i, C i ≠ 0) (h : K) (U : ι → K) (i : ι) :
    heatTick κ C h U i = U i + h * master (heatRates κ C) U i := by
  unfold heatTick
  rw [master_eq_flow hC (heatRates_detailedBalance hκ hC)]
  congr 2
  unfold flow conductance heatRates
  refine Finset.sum_congr rfl fun j _ => ?_
  have hi := hC i
  field_simp

/-- [proved-standard] **The heat tick keeps the total energy** (the first law without port
work). -/
theorem sum_heatTick {κ : ι → ι → K} (hκ : ∀ i j, κ i j = κ j i) (C : ι → K) (h : K)
    (U : ι → K) : ∑ i, heatTick κ C h U i = ∑ i, U i := by
  unfold heatTick
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_flow hκ, mul_zero, add_zero]

/-! ## 7. Clausius over many cells -/

/-- [proved-standard] **Clausius, many cells**: the heat entering each cell weighed by its inverse
temperature is half the sum over ordered pairs of the contact's heat current times the drop of
inverse temperature. -/
theorem clausius (hg : ∀ i j, g i j = g j i) (T : ι → K) :
    ∑ i, 1 / T i * flow g T i =
      (1 / 2) * ∑ i, ∑ j, g i j * (T i - T j) * (1 / T j - 1 / T i) := by
  rw [pairing hg (fun i => 1 / T i) T]
  rw [show -(1 / 2 : K) * ∑ i, ∑ j, g i j * (1 / T i - 1 / T j) * (T i - T j) =
      (1 / 2) * -∑ i, ∑ j, g i j * (1 / T i - 1 / T j) * (T i - T j) by ring]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- [proved-standard] **The many-cell production is nonnegative** at positive temperatures. -/
theorem clausius_nonneg (hg : ∀ i j, g i j = g j i) (hg0 : ∀ i j, 0 ≤ g i j) {T : ι → K}
    (hT : ∀ i, 0 < T i) : 0 ≤ ∑ i, 1 / T i * flow g T i := by
  rw [clausius hg]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
  have hi := hT i
  have hj := hT j
  have h : g i j * (T i - T j) * (1 / T j - 1 / T i) = g i j * (T i - T j) ^ 2 / (T i * T j) := by
    field_simp
  rw [h]
  exact div_nonneg (mul_nonneg (hg0 i j) (sq_nonneg _)) (mul_pos hi hj).le

end Flow

/-- [proved-standard] **The many-cell production is half the sum of the two-cell production
rates** of `Exchange` over ordered pairs of cells. -/
theorem clausius_productionRate {ι : Type*} [Fintype ι] {g : ι → ι → ℚ}
    (hg : ∀ i j, g i j = g j i) (T : ι → ℚ) :
    ∑ i, 1 / T i * flow g T i =
      (1 / 2) * ∑ i, ∑ j, Exchange.productionRate (g i j) (T i) (T j) :=
  clausius hg T

/-- [proved-standard] **Two cells**: on two cells joined by one contact the heat tick is the tick of
`Exchange` without port work. -/
theorem two_cell (κ h C₁ U₁ C₂ U₂ : ℚ) :
    heatTick (fun _ _ : Fin 2 => κ) ![C₁, C₂] h ![U₁, U₂] 0 =
        Exchange.next₁ κ h C₁ U₁ C₂ U₂ 0 ∧
      heatTick (fun _ _ : Fin 2 => κ) ![C₁, C₂] h ![U₁, U₂] 1 =
        Exchange.next₂ κ h C₁ U₁ C₂ U₂ 0 := by
  constructor
  · simp [heatTick, flow, Fin.sum_univ_two, Exchange.next₁, Exchange.heat, Exchange.temperature]
    ring
  · simp [heatTick, flow, Fin.sum_univ_two, Exchange.next₂, Exchange.heat, Exchange.temperature]
    ring

/-! ## 8. Entropy production over the reals -/

section Entropy

variable {ι : Type*} [Fintype ι] {g : ι → ι → ℝ}

/-- [proved-standard] A difference and the difference of its logarithms have one sign. -/
theorem log_pairing_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (b - a) * (Real.log b - Real.log a) := by
  rcases le_total a b with h | h
  · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (Real.log_le_log ha h))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
      (sub_nonpos.mpr (Real.log_le_log hb h))

/-- [proved-standard] The pairing of a difference with the difference of its logarithms vanishes
only at equal readings. -/
theorem log_pairing_eq_zero_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (b - a) * (Real.log b - Real.log a) = 0 ↔ a = b := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h0
    · linarith
    · exact Real.log_injOn_pos (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hb) (by linarith)
  · rintro rfl
    ring

/-- [definition] **The entropy production** of a positive reading: the sum over ordered pairs of the
contact's current times the difference of the logarithms. -/
noncomputable def production (g : ι → ι → ℝ) (u : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, g i j * (u j - u i) * (Real.log (u j) - Real.log (u i))

/-- [proved-standard] **The production is nonnegative.** -/
theorem production_nonneg (hg0 : ∀ i j, 0 ≤ g i j) {u : ι → ℝ} (hu : ∀ i, 0 < u i) :
    0 ≤ production g u := by
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  rw [mul_assoc]
  exact mul_nonneg (hg0 i j) (log_pairing_nonneg (hu i) (hu j))

/-- [proved-standard] **The production vanishes exactly at rest.** -/
theorem production_eq_zero_iff (hg0 : ∀ i j, 0 ≤ g i j) {u : ι → ℝ} (hu : ∀ i, 0 < u i) :
    production g u = 0 ↔ ∀ i j, 0 < g i j → u i = u j := by
  have hterm : ∀ i j, 0 ≤ g i j * (u j - u i) * (Real.log (u j) - Real.log (u i)) := by
    intro i j
    rw [mul_assoc]
    exact mul_nonneg (hg0 i j) (log_pairing_nonneg (hu i) (hu j))
  unfold production
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => hterm i j)]
  constructor
  · intro h i j hij
    have hi := h i (Finset.mem_univ i)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm i j)] at hi
    have hj := hi j (Finset.mem_univ j)
    rw [mul_assoc] at hj
    rcases mul_eq_zero.mp hj with h0 | h0
    · exact absurd h0 hij.ne'
    · exact (log_pairing_eq_zero_iff (hu i) (hu j)).mp h0
  · intro h i _
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases (hg0 i j).eq_or_lt with h0 | h0
    · rw [← h0]
      ring
    · rw [h i j h0]
      ring

/-- [proved-standard] **The flow paired with the logarithm is half the production**, with the sign
of a fall. -/
theorem flow_log (hg : ∀ i j, g i j = g j i) (u : ι → ℝ) :
    ∑ i, Real.log (u i) * flow g u i = -(1 / 2) * production g u := by
  rw [pairing hg (fun i => Real.log (u i)) u]
  unfold production
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- [proved-standard] **The relative entropy falls at half the production.** Along the master
equation in its heat form, `ṗ_i = (L (p/π))_i`, the sum `Σ_i (p_i log(p_i/π_i) − p_i)` (the
relative entropy `D(p‖π)` less the kept total) has derivative `−½·production`. -/
theorem hasDerivAt_relative_entropy (hg : ∀ i j, g i j = g j i) (π : ι → ℝ) (p : ℝ → ι → ℝ)
    (t : ℝ) (hπ : ∀ i, 0 < π i) (hp : ∀ i, 0 < p t i)
    (h : ∀ i, HasDerivAt (fun s => p s i) (flow g (fun j => p t j / π j) i) t) :
    HasDerivAt (fun s => ∑ i, (p s i * Real.log (p s i / π i) - p s i))
      (-(1 / 2) * production g fun j => p t j / π j) t := by
  have h1 : ∀ i, HasDerivAt (fun s => p s i * Real.log (p s i / π i) - p s i)
      (Real.log (p t i / π i) * flow g (fun j => p t j / π j) i) t := by
    intro i
    have hq : HasDerivAt (fun s => p s i / π i) (flow g (fun j => p t j / π j) i / π i) t :=
      (h i).div_const (π i)
    have hl := hq.log (div_pos (hp i) (hπ i)).ne'
    have hm := ((h i).mul hl).sub (h i)
    refine hm.congr_deriv ?_
    have hpi := (hp i).ne'
    have hπi := (hπ i).ne'
    field_simp
    ring
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => h1 i
  rw [← flow_log hg]
  exact hsum

/-- [proved-standard] **The relative entropy does not rise** along the master equation. -/
theorem relative_entropy_rate_nonpos (hg0 : ∀ i j, 0 ≤ g i j) {π p : ι → ℝ}
    (hπ : ∀ i, 0 < π i) (hp : ∀ i, 0 < p i) :
    -(1 / 2) * (production g fun j => p j / π j) ≤ 0 := by
  have h := production_nonneg hg0 (u := fun j => p j / π j) fun i => div_pos (hp i) (hπ i)
  linarith

/-- [proved-standard] **The entropy of the cells rises at the Clausius rate.** Along the heat law
`U̇_i = (L T)_i` with `T = U/C`, the entropy `Σ_i C_i log U_i` of `Exchange` has derivative
`Σ_i (1/T_i)(L T)_i`, which `clausius` reads as half the sum over ordered pairs of the contacts'
production rates. -/
theorem hasDerivAt_entropy (C : ι → ℝ) (U : ℝ → ι → ℝ) (t : ℝ) (hC : ∀ i, C i ≠ 0)
    (hU : ∀ i, 0 < U t i)
    (h : ∀ i, HasDerivAt (fun s => U s i) (flow g (fun j => U t j / C j) i) t) :
    HasDerivAt (fun s => ∑ i, C i * Real.log (U s i))
      (∑ i, 1 / (U t i / C i) * flow g (fun j => U t j / C j) i) t := by
  have h1 : ∀ i, HasDerivAt (fun s => C i * Real.log (U s i))
      (1 / (U t i / C i) * flow g (fun j => U t j / C j) i) t := by
    intro i
    have hl := ((h i).log (hU i).ne').const_mul (C i)
    refine hl.congr_deriv ?_
    have hUi := (hU i).ne'
    have hCi := hC i
    field_simp
  exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ => h1 i

end Entropy

end Holonics.Physics.Thermal.ManyCell
