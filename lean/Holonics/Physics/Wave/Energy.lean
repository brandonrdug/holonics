import Mathlib

/-!
# The staggered LC field on a supplied incidence: its exact energy balance and the Courant bound

[definition] Rebuild step 6, K3 (#74), battle test 2. The operator is **supplied**: a finite
incidence `D` from `n` nodes to `m` junctions (`D e i` is the signed incidence of node `i` on
junction `e`); `grad D V = D V` is the drop along each junction and `div D I = Dᵀ I` the net inflow
at each node. The chain of `Physics/Wave/Telegrapher` with open ends is the instance
`chainIncidence`; a ring or any graph is another. The material is diagonal: node capacitance `C`,
leakage `G`, junction inductance `L`. The clock is the staggered tick `h` (`Tick`):

```text
L e (I₁ e − I₀ e) = −h (D V) e
C i (V' i − V i)  = h (Dᵀ I₁) i − h G i (V' i + V i)/2 + h s i
```

The staggered energy pairs two consecutive half-tick currents,
`E(V; I₀, I₁) = ½ Σ C V² + ½ Σ L I₀ I₁` (`energy`).

[proved-derived; formal-checked] What is proved, exactly over `ℚ`.

1. **The energy balance has no residual** (`energy_balance`): over one tick,
   `E' − E = −h Σ G V̄² + h Σ s V̄` with `V̄ = (V + V')/2`: storage change equals source power minus
   leakage heat, the junction exchanges cancelling by the pairing `⟨V, Dᵀ I⟩ = ⟨I, D V⟩`
   (`pairing`). Without source, leakage only removes energy (`energy_nonincreasing`), strictly
   when a leaking node carries a nonzero midpoint voltage (`energy_strictly_decreasing`).
2. **The Courant bound makes the staggered energy a norm.** When the material-weighted operator
   is bounded, `Σ (D V)²/L ≤ β Σ C V²`, the energy is at least
   `½ (1 − h²β/4) Σ C V² + ⅛ Σ (2 L I₀ − h D V)²/L` (`energy_lower_bound`), so for `C, L > 0` and
   `h²β < 4` it vanishes only at `V = 0`, `I₀ = 0` (`energy_definite`): a norm on the state
   `(V, I₀)`, not only on its voltage part. A row bound certifies `β` for any supplied incidence
   (`operator_bound_of_rows`). For the uniform open chain `β = 4/(LC)` (`chain_grad_bound`,
   `chain_beta`), so `h² < LC` is the Courant (CFL) condition of the chain
   (`chain_energy_lower_bound`, `chain_energy_definite`). This is a stability statement about
   the lattice clock; reading it as the physical speed `Δx/√(LC)` not exceeding one cell per tick
   is an interpretation, not proved here.

[counterexample; formal-checked] **The Courant hypothesis is load-bearing**: on two nodes with
`C = L = 1` and `h = 2` (`h²β = 8 > 4`) a nonzero state has staggered energy `−1`
(`energy_negative_beyond_courant`), so the exact balance alone bounds nothing.

No `axiom`, no `sorry`.
-/

namespace Holonics.Physics.Wave.Energy

open Finset

variable {n m : ℕ}

/-- [definition] The drop along each junction, `D V`. -/
def grad (D : Fin m → Fin n → ℚ) (V : Fin n → ℚ) (e : Fin m) : ℚ := ∑ i, D e i * V i

/-- [definition] The net inflow at each node, `Dᵀ I`. -/
def div (D : Fin m → Fin n → ℚ) (I : Fin m → ℚ) (i : Fin n) : ℚ := ∑ e, D e i * I e

/-- [definition] **The staggered energy** of a node state with two consecutive junction
currents. -/
def energy (C : Fin n → ℚ) (L : Fin m → ℚ) (V : Fin n → ℚ) (I₀ I₁ : Fin m → ℚ) : ℚ :=
  (1 / 2) * ∑ i, C i * V i ^ 2 + (1 / 2) * ∑ e, L e * I₀ e * I₁ e

/-- [definition] **One staggered tick** of the field on the incidence `D`. -/
structure Tick (D : Fin m → Fin n → ℚ) (C G : Fin n → ℚ) (L : Fin m → ℚ) (h : ℚ)
    (s V V' : Fin n → ℚ) (I₀ I₁ : Fin m → ℚ) : Prop where
  current : ∀ e, L e * (I₁ e - I₀ e) = -h * grad D V e
  voltage : ∀ i, C i * (V' i - V i) = h * div D I₁ i - h * G i * (V' i + V i) / 2 + h * s i

/-- [proved-derived; formal-checked] **The incidence pairing** `⟨V, Dᵀ I⟩ = ⟨I, D V⟩`: the finite
Stokes identity the junction exchange cancels by. -/
theorem pairing (D : Fin m → Fin n → ℚ) (I : Fin m → ℚ) (V : Fin n → ℚ) :
    ∑ i, V i * div D I i = ∑ e, I e * grad D V e := by
  simp only [div, grad, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun e _ => sum_congr rfl fun i _ => by ring

theorem grad_add (D : Fin m → Fin n → ℚ) (V W : Fin n → ℚ) (e : Fin m) :
    grad D (V + W) e = grad D V e + grad D W e := by
  simp only [grad, Pi.add_apply, mul_add, sum_add_distrib]

/-- [proved-derived; formal-checked] **The exact energy balance of one tick**:
`E' − E = −h Σ G V̄² + h Σ s V̄`, `V̄ = (V + V')/2`. -/
theorem energy_balance {D : Fin m → Fin n → ℚ} {C G : Fin n → ℚ} {L : Fin m → ℚ} {h : ℚ}
    {s V V' : Fin n → ℚ} {I₀ I₁ I₂ : Fin m → ℚ} (hk : Tick D C G L h s V V' I₀ I₁)
    (hnext : ∀ e, L e * (I₂ e - I₁ e) = -h * grad D V' e) :
    energy C L V' I₁ I₂ - energy C L V I₀ I₁ =
      -h * ∑ i, G i * ((V i + V' i) / 2) ^ 2 + h * ∑ i, s i * ((V i + V' i) / 2) := by
  have hV : ∀ i, C i * V' i ^ 2 - C i * V i ^ 2 =
      (V' i + V i) * (h * div D I₁ i - h * G i * (V' i + V i) / 2 + h * s i) := by
    intro i; rw [← hk.voltage i]; ring
  have hI : ∀ e, L e * I₁ e * I₂ e - L e * I₀ e * I₁ e =
      I₁ e * (-h * grad D V' e - h * grad D V e) := by
    intro e
    linear_combination I₁ e * hnext e + I₁ e * hk.current e
  have hcross : ∑ i, (V' i + V i) * div D I₁ i =
      ∑ e, I₁ e * (grad D V' e + grad D V e) := by
    have := pairing D I₁ (V' + V)
    simp only [Pi.add_apply, grad_add] at this
    exact this
  have e1 : energy C L V' I₁ I₂ - energy C L V I₀ I₁ =
      (1 / 2) * ∑ i, (C i * V' i ^ 2 - C i * V i ^ 2) +
        (1 / 2) * ∑ e, (L e * I₁ e * I₂ e - L e * I₀ e * I₁ e) := by
    unfold energy; rw [sum_sub_distrib, sum_sub_distrib]; ring
  have e2 : ∑ i, (V' i + V i) * (h * div D I₁ i - h * G i * (V' i + V i) / 2 + h * s i) =
      h * ∑ i, (V' i + V i) * div D I₁ i +
        ∑ i, (-(2 * h) * (G i * ((V i + V' i) / 2) ^ 2) + 2 * h * (s i * ((V i + V' i) / 2))) := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  have e3 : ∑ e, I₁ e * (-h * grad D V' e - h * grad D V e) =
      -h * ∑ e, I₁ e * (grad D V' e + grad D V e) := by
    rw [mul_sum]
    exact sum_congr rfl fun e _ => by ring
  rw [e1, sum_congr rfl (fun i _ => hV i), sum_congr rfl (fun e _ => hI e), e2, e3, hcross,
    sum_add_distrib, ← mul_sum, ← mul_sum]
  ring

/-- [proved-derived; formal-checked] **Leakage only removes energy.** -/
theorem energy_nonincreasing {D : Fin m → Fin n → ℚ} {C G : Fin n → ℚ} {L : Fin m → ℚ} {h : ℚ}
    {V V' : Fin n → ℚ} {I₀ I₁ I₂ : Fin m → ℚ} (hk : Tick D C G L h 0 V V' I₀ I₁)
    (hnext : ∀ e, L e * (I₂ e - I₁ e) = -h * grad D V' e) (hh : 0 ≤ h) (hG : ∀ i, 0 ≤ G i) :
    energy C L V' I₁ I₂ ≤ energy C L V I₀ I₁ := by
  have := energy_balance hk hnext
  simp only [Pi.zero_apply, zero_mul, sum_const_zero, mul_zero, add_zero] at this
  have hs : 0 ≤ ∑ i, G i * ((V i + V' i) / 2) ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (hG i) (sq_nonneg _)
  nlinarith

/-- [proved-derived; formal-checked] **A leaking node with nonzero midpoint voltage removes energy
strictly.** -/
theorem energy_strictly_decreasing {D : Fin m → Fin n → ℚ} {C G : Fin n → ℚ} {L : Fin m → ℚ}
    {h : ℚ} {V V' : Fin n → ℚ} {I₀ I₁ I₂ : Fin m → ℚ} (hk : Tick D C G L h 0 V V' I₀ I₁)
    (hnext : ∀ e, L e * (I₂ e - I₁ e) = -h * grad D V' e) (hh : 0 < h) (hG : ∀ i, 0 ≤ G i)
    (j : Fin n) (hGj : 0 < G j) (hVj : V j + V' j ≠ 0) :
    energy C L V' I₁ I₂ < energy C L V I₀ I₁ := by
  have := energy_balance hk hnext
  simp only [Pi.zero_apply, zero_mul, sum_const_zero, mul_zero, add_zero] at this
  have hpos : 0 < ∑ i, G i * ((V i + V' i) / 2) ^ 2 := by
    apply sum_pos' (fun i _ => mul_nonneg (hG i) (sq_nonneg _))
    exact ⟨j, mem_univ j, mul_pos hGj (by positivity)⟩
  nlinarith

/-- [proved-derived; formal-checked] **The Courant bound.** If the material-weighted operator is
bounded, `Σ (D V)²/L ≤ β Σ C V²`, the staggered energy is at least
`½ (1 − h²β/4) Σ C V² + ⅛ Σ (2 L I₀ − h D V)²/L`: per junction
`L I₀ I₁ = ¼ (2 L I₀ − h D V)²/L − (h²/4) (D V)²/L` under the tick's current law. -/
theorem energy_lower_bound {D : Fin m → Fin n → ℚ} {C : Fin n → ℚ} {L : Fin m → ℚ} {h β : ℚ}
    {V : Fin n → ℚ} {I₀ I₁ : Fin m → ℚ} (hL : ∀ e, 0 < L e)
    (hcur : ∀ e, L e * (I₁ e - I₀ e) = -h * grad D V e)
    (hβ : ∑ e, grad D V e ^ 2 / L e ≤ β * ∑ i, C i * V i ^ 2) :
    (1 / 2) * (1 - h ^ 2 * β / 4) * ∑ i, C i * V i ^ 2 +
        (1 / 8) * ∑ e, (2 * L e * I₀ e - h * grad D V e) ^ 2 / L e ≤
      energy C L V I₀ I₁ := by
  have hid : ∀ e, L e * I₀ e * I₁ e =
      (1 / 4) * ((2 * L e * I₀ e - h * grad D V e) ^ 2 / L e) -
        h ^ 2 / 4 * (grad D V e ^ 2 / L e) := by
    intro e
    have hLe := (hL e).ne'
    have h1 : L e * I₁ e = L e * I₀ e - h * grad D V e := by linarith [hcur e]
    field_simp
    linear_combination (4 * L e * I₀ e) * h1
  have hsum : ∑ e, L e * I₀ e * I₁ e =
      (1 / 4) * ∑ e, (2 * L e * I₀ e - h * grad D V e) ^ 2 / L e -
        h ^ 2 / 4 * ∑ e, grad D V e ^ 2 / L e := by
    rw [sum_congr rfl fun e _ => hid e, sum_sub_distrib, mul_sum, mul_sum]
  have hh2 : 0 ≤ h ^ 2 / 4 := by positivity
  have := mul_le_mul_of_nonneg_left hβ hh2
  unfold energy
  rw [hsum]
  nlinarith

/-- [proved-derived; formal-checked] **Under the Courant bound the staggered energy is a norm** on
the state `(V, I₀)`: with `C, L > 0` and `h²β < 4`, it vanishes only at `V = 0`, `I₀ = 0`. -/
theorem energy_definite {D : Fin m → Fin n → ℚ} {C : Fin n → ℚ} {L : Fin m → ℚ} {h β : ℚ}
    {V : Fin n → ℚ} {I₀ I₁ : Fin m → ℚ} (hC : ∀ i, 0 < C i) (hL : ∀ e, 0 < L e)
    (hcur : ∀ e, L e * (I₁ e - I₀ e) = -h * grad D V e)
    (hβ : ∑ e, grad D V e ^ 2 / L e ≤ β * ∑ i, C i * V i ^ 2) (hcourant : h ^ 2 * β < 4)
    (hE : energy C L V I₀ I₁ = 0) : V = 0 ∧ I₀ = 0 := by
  have hb := energy_lower_bound hL hcur hβ
  rw [hE] at hb
  have hc : 0 < (1 / 2) * (1 - h ^ 2 * β / 4) := by linarith
  have hVn : 0 ≤ ∑ i, C i * V i ^ 2 := sum_nonneg fun i _ => mul_nonneg (hC i).le (sq_nonneg _)
  have hIn : 0 ≤ ∑ e, (2 * L e * I₀ e - h * grad D V e) ^ 2 / L e :=
    sum_nonneg fun e _ => div_nonneg (sq_nonneg _) (hL e).le
  have hV0 : ∑ i, C i * V i ^ 2 = 0 := by nlinarith
  have hI0 : ∑ e, (2 * L e * I₀ e - h * grad D V e) ^ 2 / L e = 0 := by nlinarith
  have hVi : ∀ i, V i = 0 := by
    intro i
    have := (sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hC i).le (sq_nonneg (V i))).mp
      hV0 i (mem_univ i)
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (hC i).ne'
    · exact pow_eq_zero_iff two_ne_zero |>.mp h0
  have hg : ∀ e, grad D V e = 0 := fun e => by simp [grad, hVi]
  refine ⟨funext hVi, funext fun e => ?_⟩
  have := (sum_eq_zero_iff_of_nonneg fun e _ => div_nonneg (sq_nonneg _) (hL e).le).mp hI0 e
    (mem_univ e)
  rw [hg e, mul_zero, sub_zero, div_eq_zero_iff] at this
  rcases this with h0 | h0
  · have h2 : 2 * L e * I₀ e = 0 := pow_eq_zero_iff two_ne_zero |>.mp h0
    simpa [(hL e).ne'] using h2
  · exact absurd h0 (hL e).ne'

/-- [proved-derived; formal-checked] **A row bound on the operator** (Cauchy–Schwarz along each
junction): if at every node `Σ_e |D e i| (Σ_j |D e j|)/L e ≤ β C i`, then
`Σ (D V)²/L ≤ β Σ C V²`. This is the exact certificate of `β` for any supplied incidence. -/
theorem operator_bound_of_rows {D : Fin m → Fin n → ℚ} {C : Fin n → ℚ} {L : Fin m → ℚ} {β : ℚ}
    (hL : ∀ e, 0 < L e) (hrow : ∀ i, ∑ e, |D e i| * (∑ j, |D e j|) / L e ≤ β * C i)
    (V : Fin n → ℚ) : ∑ e, grad D V e ^ 2 / L e ≤ β * ∑ i, C i * V i ^ 2 := by
  have hcs : ∀ e, grad D V e ^ 2 ≤ (∑ j, |D e j|) * ∑ i, |D e i| * V i ^ 2 := by
    intro e
    unfold grad
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i _; exact abs_nonneg _
    · intro i _; exact mul_nonneg (abs_nonneg _) (sq_nonneg _)
    · intro i _
      rw [mul_pow, ← mul_assoc, ← sq, sq_abs]
  have hre : ∀ e, ((∑ j, |D e j|) * ∑ i, |D e i| * V i ^ 2) / L e =
      ∑ i, V i ^ 2 * (|D e i| * (∑ j, |D e j|) / L e) := by
    intro e
    rw [mul_sum, sum_div]
    exact sum_congr rfl fun i _ => by ring
  calc ∑ e, grad D V e ^ 2 / L e
      ≤ ∑ e, ((∑ j, |D e j|) * ∑ i, |D e i| * V i ^ 2) / L e :=
        sum_le_sum fun e _ => div_le_div_of_nonneg_right (hcs e) (hL e).le
    _ = ∑ i, V i ^ 2 * ∑ e, |D e i| * (∑ j, |D e j|) / L e := by
        rw [sum_congr rfl fun e _ => hre e, sum_comm]
        exact sum_congr rfl fun i _ => by rw [mul_sum]
    _ ≤ ∑ i, V i ^ 2 * (β * C i) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _)
    _ = β * ∑ i, C i * V i ^ 2 := by
        rw [mul_sum]; exact sum_congr rfl fun i _ => by ring

/-! ## The open chain -/

/-- [definition] **The open chain's incidence**: junction `e` runs from node `e` to node `e + 1`. -/
def chainIncidence (m : ℕ) : Fin m → Fin (m + 1) → ℚ :=
  fun e i => (if i = e.succ then 1 else 0) - (if i = e.castSucc then 1 else 0)

theorem chain_grad (V : Fin (m + 1) → ℚ) (e : Fin m) :
    grad (chainIncidence m) V e = V e.succ - V e.castSucc := by
  simp only [grad, chainIncidence, sub_mul, ite_mul, one_mul, zero_mul, sum_sub_distrib,
    sum_ite_eq', mem_univ, if_true]

/-- [proved-derived; formal-checked] **The chain's operator bound**: `Σ (V(e+1) − V e)² ≤ 4 Σ V²`. -/
theorem chain_grad_bound (V : Fin (m + 1) → ℚ) :
    ∑ e, grad (chainIncidence m) V e ^ 2 ≤ 4 * ∑ i, V i ^ 2 := by
  simp only [chain_grad]
  have hpt : ∀ e : Fin m, (V e.succ - V e.castSucc) ^ 2 ≤
      2 * V e.succ ^ 2 + 2 * V e.castSucc ^ 2 := fun e => by
    nlinarith [sq_nonneg (V e.succ + V e.castSucc)]
  have hs : ∑ e : Fin m, V e.succ ^ 2 ≤ ∑ i, V i ^ 2 := by
    rw [Fin.sum_univ_succ]; nlinarith [sq_nonneg (V 0)]
  have hc : ∑ e : Fin m, V e.castSucc ^ 2 ≤ ∑ i, V i ^ 2 := by
    rw [Fin.sum_univ_castSucc]; nlinarith [sq_nonneg (V (Fin.last m))]
  calc ∑ e, (V e.succ - V e.castSucc) ^ 2
      ≤ ∑ e : Fin m, (2 * V e.succ ^ 2 + 2 * V e.castSucc ^ 2) := sum_le_sum fun e _ => hpt e
    _ = 2 * ∑ e : Fin m, V e.succ ^ 2 + 2 * ∑ e : Fin m, V e.castSucc ^ 2 := by
      rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ 4 * ∑ i, V i ^ 2 := by linarith

/-- [proved-derived; formal-checked] The uniform open chain's material-weighted operator bound,
`β = 4/(LC)`. -/
theorem chain_beta {C L : ℚ} (hC : 0 < C) (hL : 0 < L) (V : Fin (m + 1) → ℚ) :
    ∑ e, grad (chainIncidence m) V e ^ 2 / L ≤ 4 / (L * C) * ∑ i, C * V i ^ 2 := by
  rw [← sum_div, ← mul_sum]
  have := chain_grad_bound V
  rw [div_le_iff₀ hL]
  have hrw : 4 / (L * C) * (C * ∑ i, V i ^ 2) * L = 4 * ∑ i, V i ^ 2 := by
    field_simp
  rw [hrw]; exact this

/-- [proved-derived; formal-checked] **The Courant condition of the uniform open chain**: with
`C, L > 0`, the staggered energy is at least `½ (1 − h²/(LC)) Σ C V²` (its voltage part; the
current part is `chain_energy_definite`). -/
theorem chain_energy_lower_bound {C L h : ℚ} (hC : 0 < C) (hL : 0 < L) {V : Fin (m + 1) → ℚ}
    {I₀ I₁ : Fin m → ℚ}
    (hcur : ∀ e, L * (I₁ e - I₀ e) = -h * grad (chainIncidence m) V e) :
    (1 / 2) * (1 - h ^ 2 / (L * C)) * ∑ i, C * V i ^ 2 ≤
      energy (fun _ => C) (fun _ => L) V I₀ I₁ := by
  have := energy_lower_bound (D := chainIncidence m) (C := fun _ => C) (L := fun _ => L)
    (h := h) (I₀ := I₀) (I₁ := I₁) (fun _ => hL) hcur (chain_beta hC hL V)
  have heq : h ^ 2 * (4 / (L * C)) / 4 = h ^ 2 / (L * C) := by field_simp
  rw [heq] at this
  have hsq : 0 ≤ ∑ e, (2 * L * I₀ e - h * grad (chainIncidence m) V e) ^ 2 / L :=
    sum_nonneg fun e _ => div_nonneg (sq_nonneg _) hL.le
  linarith

/-- [proved-derived; formal-checked] **Under the chain's Courant condition `h² < LC` the staggered
energy is a norm**: it vanishes only at `V = 0`, `I₀ = 0`. -/
theorem chain_energy_definite {C L h : ℚ} (hC : 0 < C) (hL : 0 < L) (hcfl : h ^ 2 < L * C)
    {V : Fin (m + 1) → ℚ} {I₀ I₁ : Fin m → ℚ}
    (hcur : ∀ e, L * (I₁ e - I₀ e) = -h * grad (chainIncidence m) V e)
    (hE : energy (fun _ => C) (fun _ => L) V I₀ I₁ = 0) : V = 0 ∧ I₀ = 0 := by
  have hLC : 0 < L * C := mul_pos hL hC
  refine energy_definite (D := chainIncidence m) (C := fun _ => C) (L := fun _ => L) (h := h)
    (β := 4 / (L * C)) (I₁ := I₁) (fun _ => hC) (fun _ => hL) hcur (chain_beta hC hL V) ?_ hE
  rw [mul_div_assoc', div_lt_iff₀ hLC]
  linarith

/-! ## The counterexample beyond the Courant bound -/

/-- Two nodes, one junction. -/
def twoNode : Fin 1 → Fin 2 → ℚ := chainIncidence 1

/-- [counterexample; formal-checked] **Beyond the Courant bound the staggered energy is not a
norm.** On two nodes with `C = L = 1`, the bound `β = 2` holds for every state, and at `h = 2`
(`h²β = 8 > 4`) the state `V = (1, −1)`, `I₀ = −2` with its tick current `I₁ = 2` has staggered
energy `−1`. -/
theorem energy_negative_beyond_courant :
    (∀ V : Fin 2 → ℚ, ∑ e, grad twoNode V e ^ 2 / 1 ≤ 2 * ∑ i, 1 * V i ^ 2) ∧
      (2 : ℚ) ^ 2 * 2 > 4 ∧
      (∀ e : Fin 1, (1 : ℚ) * (2 - (-2)) = -2 * grad twoNode ![1, -1] e) ∧
      energy (fun _ : Fin 2 => (1 : ℚ)) (fun _ : Fin 1 => (1 : ℚ)) ![1, -1]
        (fun _ => -2) (fun _ => 2) = -1 := by
  refine ⟨fun V => ?_, by norm_num, fun e => ?_, ?_⟩
  · have h1 : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := rfl
    have h0 : (Fin.castSucc (0 : Fin 1) : Fin 2) = 0 := rfl
    simp only [twoNode, chain_grad, Fin.sum_univ_one, Fin.sum_univ_two, div_one, one_mul, h1, h0]
    nlinarith [sq_nonneg (V 0 + V 1)]
  · fin_cases e
    simp [twoNode, chain_grad]
    norm_num
  · simp [energy, Fin.sum_univ_two]
    norm_num

section Audit

#print axioms energy_balance
#print axioms energy_strictly_decreasing
#print axioms energy_lower_bound
#print axioms energy_definite
#print axioms operator_bound_of_rows
#print axioms chain_energy_lower_bound
#print axioms chain_energy_definite
#print axioms energy_negative_beyond_courant

end Audit

end Holonics.Physics.Wave.Energy
