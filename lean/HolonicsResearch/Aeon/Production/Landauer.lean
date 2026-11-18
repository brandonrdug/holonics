import Mathlib
import HolonicsResearch.Aeon.Production.Jarzynski

/-!
# The laws over a density: free energy is a divergence, and erasing a bit costs `log 2 / β`

`Aeon/Production/Jarzynski` opens the driven aeon at the equilibrium of its first constitution,
`w 0 / Z 0`, and proves the second law in the mean from Jarzynski's equality. Here the aeon opens
at **any** density `p₀`, and the laws are read on the marginals `p_t` of the driven chain. The
statement of the operating guide that is formalized: "the free energy of `p` over the equilibrium
`q` is `F(p) − F(q) = k_B T · D(p‖q)`" (`freeEnergyOf_sub_gibbs`, with `k_B T = 1/β`). Every
logarithm is natural, so every entropy and divergence is in nats.

[definition] **The setting.** States `S` (finite, inhabited), the built file's protocol of
energies `E : ℕ → S → ℝ`, inverse temperature `β`, weights `w t x = exp(−β E t x)`, `partition`,
`freeEnergy t = −(1/β) log Z t` and kernels `K : ℕ → S → S → ℝ` under `Driven` (nonnegative
entries, unit rows, the weight of their own tick stationary). One tick `t → t+1` is a work step
(the energies move from `E t` to `E (t+1)` at a held density) followed by a heat step (the density
moves by `K (t+1)`). New here:

```text
Density p           0 ≤ p x,  Σ_x p x = 1
Stochastic M        0 ≤ M x y,  Σ_y M x y = 1
kl p q            = Σ_x p x · log(p x / q x)                    (nats; 0 · log 0 = 0)
push p M y        = Σ_x p x · M x y
gibbs β E t x     = w t x / Z t                                 (the equilibrium of tick t)
freeEnergyOf t p  = Σ_x p x · E t x + (1/β) Σ_x p x · log(p x)  (energy − entropy/β)
entropy p         = −Σ_x p x · log(p x)
marginal K p₀ t   : p_0 = p₀,  p_(t+1) = push p_t (K (t+1))
meanWork n        = Σ_(t<n) Σ_x p_t x · (E (t+1) x − E t x)
meanHeat n        = −Σ_(t<n) Σ_x (p_(t+1) x − p_t x) · E (t+1) x  (paid to the bath)
production n      = Σ_(t<n) (kl p_t π_(t+1) − kl p_(t+1) π_(t+1)),   π_t = gibbs β E t
```

[proved-derived; formal-checked] What is proved. The named inequalities are classical (Gibbs'
inequality, the log-sum inequality, the data-processing inequality, Clausius' inequality, and
Landauer 1961 for the bit) `[from training]`; the proofs here are on finite sums.

1. **The divergence** (`kl_nonneg`, `kl_eq_zero_iff`): `0 ≤ kl p q` for a density `p` and a
   positive density `q`, with `kl p q = 0` iff `p = q`. **The log-sum inequality** (`log_sum_le`):
   `(Σ a) · log(Σ a / Σ b) ≤ Σ a_i · log(a_i / b_i)` for `a_i ≥ 0`, `b_i ≥ 0` and `a_i = 0` where
   `b_i = 0`, by Jensen on `x log x`. **Data processing** (`kl_push_le`): a stochastic kernel never
   raises a divergence, `kl (push p M) (push q M) ≤ kl p q`.
2. **The free energy of a density** (`freeEnergyOf_eq`):
   `freeEnergyOf t p = freeEnergy t + (1/β) · kl p (gibbs t)`. Hence
   `freeEnergy t ≤ freeEnergyOf t p` (`freeEnergy_le_freeEnergyOf`) with equality iff
   `p = gibbs t` (`freeEnergyOf_eq_freeEnergy_iff`), and the guide's law
   (`freeEnergyOf_sub_gibbs`).
3. **The two half-steps of a tick.** Work at a held density (`freeEnergyOf_work_step`):
   `freeEnergyOf (t+1) p − freeEnergyOf t p = Σ_x p x · (E (t+1) x − E t x)`. Heat through a kernel
   (`freeEnergyOf_heat_step`): `freeEnergyOf t p − freeEnergyOf t (push p M) =
   (1/β)(kl p (gibbs t) − kl (push p M) (gibbs t))`, which is `≥ 0` when `M` keeps `gibbs t`
   stationary (`freeEnergyOf_push_le`).
4. **The second law from any opening density** (`freeEnergyOf_sub_eq`, `second_law_density`):
   `freeEnergyOf n p_n − freeEnergyOf 0 p₀ = meanWork n − (1/β) · production n`, and
   `production n ≥ 0` (`production_nonneg`): each tick's production is the divergence its kernel
   removes. **The join to the built file**: the last-occurrence marginal of `pathProb` is
   `marginal K (gibbs 0) n` (`sum_pathProb_last`), the path mean of `work` is `meanWork` at
   `p₀ = gibbs 0` (`sum_pathProb_work`), and the built `second_law`'s inequality is the case
   `p₀ = gibbs 0` (`second_law_of_density`, proved here without Jarzynski's equality).
5. **The first law and Clausius** (`first_law`, `clausius_eq`, `clausius`):
   `meanWork n − meanHeat n = Σ p_n E_n − Σ p₀ E_0`;
   `β · meanHeat n = entropy p₀ − entropy p_n + production n`; so
   `entropy p₀ − entropy p_n ≤ β · meanHeat n`: the entropy a protocol removes from the system is
   paid to the bath as heat.
6. **Landauer's bound** (`landauer_partial`, `landauer_partial_work`, `landauer_card`,
   `landauer_bit`, `landauer_card_work`, `landauer_bit_work`, `landauer_bool`): lowering the entropy
   by `ΔH` costs at least `ΔH / β` of heat; from the uniform density on `S` to a point mass,
   `log (card S) ≤ β · meanHeat n`; on two states `log 2 ≤ β · meanHeat n`; and where the first and
   last energies are one constant (a degenerate memory) `log 2 / β ≤ meanWork n`.
7. **A quotient's price** (`card_eq_of_fibres`, `pushforward_uniform_of_fibres`,
   `entropy_removed_of_fibres`, `quotient_price`): a map `f : S → R` whose fibres all have `m`
   members sends the uniform density on `S` to the uniform density on `R`, the entropy removed is
   `log m`, and a driven protocol that opens uniform and closes with no more entropy than the
   image pays `log m / β ≤ meanHeat n`.

[interpretation] The reading on the objects. Retention is a quotient of the constitution, and a
quotient merges the members of a fibre. Read on a uniform density, forgetting which of `m` members
was held removes `log m` nats, and item 5 prices that removal as heat through the bath's port at
`log m / β`. The production of a tick is carried by the kernel alone: the work step changes the
constitution at a held density and produces nothing, and the heat step moves the density toward
the equilibrium of its tick by the divergence it removes.

**What this does not state.** Finite states and finitely many ticks: no continuous time, no
infinite state space, no Hamiltonian dynamics and no quantum memory. The bounds are in the mean
over the marginals; no single path is bounded, and no protocol that attains a bound is built (the
slow limit in which `production` goes to zero is not here). The kernels are given with their
stationarity as a hypothesis. Item 7 takes the closing density's entropy bound as a hypothesis; it
does not build a kernel that realizes the map `f`. Nothing here is a claim about any machine's
actual dissipation: a card or a host runs far above these bounds, and no reading of one is made.
The words work, heat, free energy and bath are the canonical chart's; nothing here derives that
chart.

No `axiom`, no `sorry`.
-/

open Finset

noncomputable section

namespace Holonics.Aeon.Production.Landauer

open Holonics.Aeon.Production.Jarzynski

/-! ## Real-variable lemmas: one term of a divergence, and the log-sum inequality -/

section RealLemmas

/-- [proved-derived; formal-checked] One term of Gibbs' inequality:
`a − b ≤ a · log(a / b)` for `a ≥ 0`, `b > 0` (with `0 · log 0 = 0`). -/
theorem sub_le_mul_log_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    a - b ≤ a * Real.log (a / b) := by
  rcases ha.eq_or_lt with h | h
  · rw [← h, zero_mul]
    linarith
  · have h1 : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb h)
    have h2 : Real.log (a / b) = -Real.log (b / a) := by
      rw [← Real.log_inv, inv_div]
    have h3 : a * (b / a - 1) = b - a := by
      have ha' : a ≠ 0 := h.ne'
      field_simp
    have h4 : a * Real.log (b / a) ≤ a * (b / a - 1) := mul_le_mul_of_nonneg_left h1 h.le
    rw [h2]
    linarith

/-- [proved-derived; formal-checked] The term of Gibbs' inequality is an equality only at
`a = b`. -/
theorem mul_log_div_eq_sub_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    a * Real.log (a / b) = a - b ↔ a = b := by
  constructor
  · intro heq
    rcases ha.eq_or_lt with h | h
    · rw [← h, zero_mul] at heq
      linarith
    · by_contra hne
      have hne' : b / a ≠ 1 := by
        intro h1
        rw [div_eq_one_iff_eq h.ne'] at h1
        exact hne h1.symm
      have h1 : Real.log (b / a) < b / a - 1 :=
        Real.log_lt_sub_one_of_pos (div_pos hb h) hne'
      have h2 : Real.log (a / b) = -Real.log (b / a) := by
        rw [← Real.log_inv, inv_div]
      have h3 : a * (b / a - 1) = b - a := by
        have ha' : a ≠ 0 := h.ne'
        field_simp
      have h4 : a * Real.log (b / a) < a * (b / a - 1) := mul_lt_mul_of_pos_left h1 h
      rw [h2] at heq
      linarith
  · intro h
    rw [h, div_self hb.ne', Real.log_one, mul_zero, sub_self]

private theorem jensen_term₁ {a b B : ℝ} (hb : b ≠ 0) (hB : B ≠ 0) :
    b / B * (a / b) = a / B := by
  field_simp

private theorem jensen_term₂ {a b B L : ℝ} (hb : b ≠ 0) (hB : B ≠ 0) :
    b / B * (a / b * L) = a * L / B := by
  field_simp

private theorem scale_le {A B R L : ℝ} (hB : 0 < B) (h : A / B * L ≤ R / B) : A * L ≤ R := by
  have hB' : B ≠ 0 := hB.ne'
  have h' := mul_le_mul_of_nonneg_left h hB.le
  have e1 : B * (A / B * L) = A * L := by field_simp
  have e2 : B * (R / B) = R := by field_simp
  rw [e1, e2] at h'
  exact h'

/-- [proved-derived; formal-checked] The log-sum inequality for positive `b`: Jensen's
inequality for `x log x` at the points `a_i / b_i` with the weights `b_i / Σ b`. -/
theorem log_sum_le_of_pos {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) ≤
      ∑ i ∈ s, a i * Real.log (a i / b i) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  have hB : 0 < ∑ i ∈ s, b i := Finset.sum_pos hb hne
  obtain ⟨B, hBdef⟩ : ∃ B, B = ∑ i ∈ s, b i := ⟨_, rfl⟩
  rw [← hBdef] at hB ⊢
  have hw1 : ∑ i ∈ s, b i / B = 1 := by
    rw [← Finset.sum_div, ← hBdef]
    exact div_self hB.ne'
  have hJ := Real.convexOn_mul_log.map_sum_le (t := s) (w := fun i => b i / B)
    (p := fun i => a i / b i)
    (fun i hi => div_nonneg (hb i hi).le hB.le) hw1
    (fun i hi => Set.mem_Ici.mpr (div_nonneg (ha i hi) (hb i hi).le))
  simp only [smul_eq_mul] at hJ
  have h1 : ∑ i ∈ s, b i / B * (a i / b i) = (∑ i ∈ s, a i) / B := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i hi => jensen_term₁ (hb i hi).ne' hB.ne'
  have h2 : ∑ i ∈ s, b i / B * (a i / b i * Real.log (a i / b i)) =
      (∑ i ∈ s, a i * Real.log (a i / b i)) / B := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i hi => jensen_term₂ (hb i hi).ne' hB.ne'
  rw [h1, h2] at hJ
  exact scale_le hB hJ

/-- [proved-derived; formal-checked] **The log-sum inequality** (`[from training]`):
`(Σ a) · log(Σ a / Σ b) ≤ Σ a_i · log(a_i / b_i)` for `a_i ≥ 0`, `b_i ≥ 0`, and `a_i = 0`
wherever `b_i = 0`. -/
theorem log_sum_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) (hab : ∀ i ∈ s, b i = 0 → a i = 0) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) ≤
      ∑ i ∈ s, a i * Real.log (a i / b i) := by
  classical
  have hA : ∑ i ∈ s, a i = ∑ i ∈ s.filter (fun i => b i ≠ 0), a i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases h : b i = 0
    · simp [h, hab i hi h]
    · simp [h]
  have hBs : ∑ i ∈ s, b i = ∑ i ∈ s.filter (fun i => b i ≠ 0), b i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : b i = 0
    · simp [h]
    · simp [h]
  have hR : ∑ i ∈ s, a i * Real.log (a i / b i) =
      ∑ i ∈ s.filter (fun i => b i ≠ 0), a i * Real.log (a i / b i) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases h : b i = 0
    · simp [h, hab i hi h]
    · simp [h]
  rw [hA, hBs, hR]
  refine log_sum_le_of_pos _ a b ?_ ?_
  · intro i hi
    exact ha i (Finset.mem_filter.mp hi).1
  · intro i hi
    exact lt_of_le_of_ne (hb i (Finset.mem_filter.mp hi).1) (Ne.symm (Finset.mem_filter.mp hi).2)

end RealLemmas

/-! ## T1. The divergence: Gibbs' inequality and data processing -/

section Divergence

variable {S : Type*} [Fintype S]

/-- [definition] A density on a finite state type: nonnegative values of unit sum. -/
structure Density (p : S → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ p x
  total : ∑ x, p x = 1

/-- [definition] A stochastic kernel: nonnegative entries and unit rows. -/
structure Stochastic (M : S → S → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ M x y
  row : ∀ x, ∑ y, M x y = 1

/-- [definition] The divergence (relative entropy) of `p` against `q`, in nats:
`Σ_x p x · log(p x / q x)`, with `0 · log 0 = 0`. -/
def kl (p q : S → ℝ) : ℝ := ∑ x, p x * Real.log (p x / q x)

/-- [definition] A density moved through a kernel: `(p ⬝ M) y = Σ_x p x · M x y`. -/
def push (p : S → ℝ) (M : S → S → ℝ) (y : S) : ℝ := ∑ x, p x * M x y

/-- [proved-derived; formal-checked] A density against itself has no divergence. -/
theorem kl_self (q : S → ℝ) : kl q q = 0 := by
  unfold kl
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases h : q x = 0
  · rw [h, zero_mul]
  · rw [div_self h, Real.log_one, mul_zero]

/-- [proved-derived; formal-checked] The divergence is at least the difference of the two
masses. -/
theorem sub_le_kl {p q : S → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x) :
    ∑ x, p x - ∑ x, q x ≤ kl p q := by
  unfold kl
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun x _ => sub_le_mul_log_div (hp x) (hq x)

/-- [proved-derived; formal-checked] **Gibbs' inequality** (`[from training]`): the divergence
of a density against a positive density is nonnegative. -/
theorem kl_nonneg {p q : S → ℝ} (hp : Density p) (hq : ∀ x, 0 < q x) (hq1 : ∑ x, q x = 1) :
    0 ≤ kl p q := by
  have h := sub_le_kl hp.nonneg hq
  rw [hp.total, hq1] at h
  linarith

/-- [proved-derived; formal-checked] **Gibbs' inequality, the case of equality**: the divergence
vanishes only at `p = q`. -/
theorem kl_eq_zero_iff {p q : S → ℝ} (hp : Density p) (hq : ∀ x, 0 < q x)
    (hq1 : ∑ x, q x = 1) : kl p q = 0 ↔ p = q := by
  constructor
  · intro h
    have hsum : ∑ x, (p x * Real.log (p x / q x) - (p x - q x)) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hp.total, hq1]
      unfold kl at h
      rw [h]
      norm_num
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun x _ =>
      sub_nonneg.mpr (sub_le_mul_log_div (hp.nonneg x) (hq x))).mp hsum
    funext x
    have hx := hz x (Finset.mem_univ x)
    exact (mul_log_div_eq_sub_iff (hp.nonneg x) (hq x)).mp (by linarith)
  · intro h
    rw [h]
    exact kl_self q

/-- [proved-derived; formal-checked] A density moved through a stochastic kernel is a density. -/
theorem density_push {p : S → ℝ} {M : S → S → ℝ} (hp : Density p) (hM : Stochastic M) :
    Density (push p M) where
  nonneg y := Finset.sum_nonneg fun x _ => mul_nonneg (hp.nonneg x) (hM.nonneg x y)
  total := by
    unfold push
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hM.row, mul_one]
    exact hp.total

/-- [proved-derived; formal-checked] **Data processing** (`[from training]`): a stochastic
kernel never raises a divergence. The reference `q` is positive; where `(q ⬝ M) y = 0` the whole
column of `M` at `y` is zero and the term vanishes. -/
theorem kl_push_le {p q : S → ℝ} {M : S → S → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x)
    (hM : Stochastic M) : kl (push p M) (push q M) ≤ kl p q := by
  unfold kl push
  calc ∑ y, (∑ x, p x * M x y) * Real.log ((∑ x, p x * M x y) / ∑ x, q x * M x y)
      ≤ ∑ y, ∑ x, p x * M x y * Real.log (p x * M x y / (q x * M x y)) := by
        refine Finset.sum_le_sum fun y _ => ?_
        refine log_sum_le _ _ _ ?_ ?_ ?_
        · intro x _
          exact mul_nonneg (hp x) (hM.nonneg x y)
        · intro x _
          exact mul_nonneg (hq x).le (hM.nonneg x y)
        · intro x _ h
          rcases mul_eq_zero.mp h with h0 | h0
          · exact absurd h0 (hq x).ne'
          · rw [h0, mul_zero]
    _ = ∑ y, ∑ x, M x y * (p x * Real.log (p x / q x)) := by
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
        by_cases h : M x y = 0
        · simp [h]
        · rw [mul_div_mul_right _ _ h]
          ring
    _ = ∑ x, ∑ y, M x y * (p x * Real.log (p x / q x)) := Finset.sum_comm
    _ = ∑ x, p x * Real.log (p x / q x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_mul, hM.row x, one_mul]

end Divergence

/-! ## T2. The free energy of a density is the equilibrium's plus a divergence -/

section FreeEnergy

variable {S : Type*} [Fintype S] {β : ℝ} {E : ℕ → S → ℝ}

/-- [definition] The equilibrium density of tick `t`: the Boltzmann weight over its sum. -/
def gibbs (β : ℝ) (E : ℕ → S → ℝ) (t : ℕ) (x : S) : ℝ := weight β E t x / partition β E t

/-- [definition] The free energy of a density `p` at the constitution of tick `t`: mean energy
minus entropy over `β`, `Σ p E + (1/β) Σ p log p`. -/
def freeEnergyOf (β : ℝ) (E : ℕ → S → ℝ) (t : ℕ) (p : S → ℝ) : ℝ :=
  ∑ x, p x * E t x + 1 / β * ∑ x, p x * Real.log (p x)

/-- [definition] The entropy of a density, in nats. -/
def entropy (p : S → ℝ) : ℝ := -∑ x, p x * Real.log (p x)

theorem gibbs_pos [Nonempty S] (β : ℝ) (E : ℕ → S → ℝ) (t : ℕ) (x : S) : 0 < gibbs β E t x :=
  div_pos (weight_pos β E t x) (partition_pos β E t)

theorem sum_gibbs [Nonempty S] (β : ℝ) (E : ℕ → S → ℝ) (t : ℕ) : ∑ x, gibbs β E t x = 1 := by
  unfold gibbs
  rw [← Finset.sum_div]
  exact div_self (partition_pos β E t).ne'

/-- [proved-derived; formal-checked] The equilibrium of a tick is a density. -/
theorem density_gibbs [Nonempty S] (β : ℝ) (E : ℕ → S → ℝ) (t : ℕ) : Density (gibbs β E t) :=
  ⟨fun x => (gibbs_pos β E t x).le, sum_gibbs β E t⟩

theorem log_gibbs [Nonempty S] (β : ℝ) (E : ℕ → S → ℝ) (t : ℕ) (x : S) :
    Real.log (gibbs β E t x) = -β * E t x - Real.log (partition β E t) := by
  unfold gibbs
  rw [Real.log_div (weight_pos β E t x).ne' (partition_pos β E t).ne']
  unfold weight
  rw [Real.log_exp]

/-- [proved-derived; formal-checked] The divergence of a density against the equilibrium of a
tick: `Σ p log p + β Σ p E + log Z`. -/
theorem kl_gibbs [Nonempty S] {p : S → ℝ} (hp : Density p) (t : ℕ) :
    kl p (gibbs β E t) =
      ∑ x, p x * Real.log (p x) + β * ∑ x, p x * E t x + Real.log (partition β E t) := by
  unfold kl
  have hterm : ∀ x, p x * Real.log (p x / gibbs β E t x) =
      p x * Real.log (p x) + β * (p x * E t x) + p x * Real.log (partition β E t) := by
    intro x
    rcases (hp.nonneg x).eq_or_lt with h | h
    · rw [← h]
      simp
    · rw [Real.log_div h.ne' (gibbs_pos β E t x).ne', log_gibbs]
      ring
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, hp.total, one_mul]

private theorem free_alg {β U A L : ℝ} (hβ : β ≠ 0) :
    U + 1 / β * A = -(1 / β) * L + 1 / β * (A + β * U + L) := by
  have h1 : 1 / β * (β * U) = U := by
    rw [one_div, inv_mul_cancel_left₀ hβ]
  rw [mul_add, mul_add, h1]
  ring

/-- [proved-derived; formal-checked] **The free energy of a density** is the equilibrium free
energy plus the divergence from the equilibrium over `β`:
`freeEnergyOf t p = freeEnergy t + (1/β) · kl p (gibbs t)`. -/
theorem freeEnergyOf_eq [Nonempty S] (hβ : β ≠ 0) {p : S → ℝ} (hp : Density p) (t : ℕ) :
    freeEnergyOf β E t p = freeEnergy β E t + 1 / β * kl p (gibbs β E t) := by
  rw [kl_gibbs hp t]
  unfold freeEnergyOf freeEnergy
  exact free_alg hβ

/-- [proved-derived; formal-checked] At the equilibrium the free energy of the density is the
built file's `freeEnergy`. -/
theorem freeEnergyOf_gibbs [Nonempty S] (hβ : β ≠ 0) (t : ℕ) :
    freeEnergyOf β E t (gibbs β E t) = freeEnergy β E t := by
  rw [freeEnergyOf_eq hβ (density_gibbs β E t) t, kl_self, mul_zero, add_zero]

/-- [proved-derived; formal-checked] **The guide's law**: the free energy of `p` over the
equilibrium `q` is `F(p) − F(q) = (1/β) · D(p‖q)`. -/
theorem freeEnergyOf_sub_gibbs [Nonempty S] (hβ : β ≠ 0) {p : S → ℝ} (hp : Density p) (t : ℕ) :
    freeEnergyOf β E t p - freeEnergyOf β E t (gibbs β E t) = 1 / β * kl p (gibbs β E t) := by
  rw [freeEnergyOf_gibbs hβ t, freeEnergyOf_eq hβ hp t]
  ring

/-- [proved-derived; formal-checked] No density has less free energy than the equilibrium. -/
theorem freeEnergy_le_freeEnergyOf [Nonempty S] (hβ : 0 < β) {p : S → ℝ} (hp : Density p)
    (t : ℕ) : freeEnergy β E t ≤ freeEnergyOf β E t p := by
  rw [freeEnergyOf_eq hβ.ne' hp t]
  have h1 : 0 ≤ kl p (gibbs β E t) := kl_nonneg hp (gibbs_pos β E t) (sum_gibbs β E t)
  have h2 : 0 ≤ 1 / β * kl p (gibbs β E t) := mul_nonneg (one_div_pos.mpr hβ).le h1
  linarith

/-- [proved-derived; formal-checked] The free energy of a density meets the equilibrium's only
at the equilibrium density. -/
theorem freeEnergyOf_eq_freeEnergy_iff [Nonempty S] (hβ : 0 < β) {p : S → ℝ} (hp : Density p)
    (t : ℕ) : freeEnergyOf β E t p = freeEnergy β E t ↔ p = gibbs β E t := by
  rw [freeEnergyOf_eq hβ.ne' hp t, ← kl_eq_zero_iff hp (gibbs_pos β E t) (sum_gibbs β E t)]
  constructor
  · intro h
    have h0 : 1 / β * kl p (gibbs β E t) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 (one_div_pos.mpr hβ).ne'
    · exact h1
  · intro h
    rw [h, mul_zero, add_zero]

/-- [proved-derived; formal-checked] Free energy is mean energy minus entropy over `β`. -/
theorem freeEnergyOf_eq_energy_sub (β : ℝ) (E : ℕ → S → ℝ) (t : ℕ) (p : S → ℝ) :
    freeEnergyOf β E t p = ∑ x, p x * E t x - 1 / β * entropy p := by
  unfold freeEnergyOf entropy
  ring

/-! ## T3. The two half-steps of a tick -/

/-- [proved-derived; formal-checked] **The work step**: at a held density, moving the energies
from `E t` to `E (t+1)` changes the free energy by the mean of the energy change. -/
theorem freeEnergyOf_work_step (β : ℝ) (E : ℕ → S → ℝ) (t : ℕ) (p : S → ℝ) :
    freeEnergyOf β E (t + 1) p - freeEnergyOf β E t p = ∑ x, p x * (E (t + 1) x - E t x) := by
  unfold freeEnergyOf
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- [proved-derived; formal-checked] **The heat step**: through any stochastic kernel the free
energy falls by the divergence from the equilibrium that the kernel removes, over `β`. -/
theorem freeEnergyOf_heat_step [Nonempty S] (hβ : β ≠ 0) {p : S → ℝ} (hp : Density p)
    {M : S → S → ℝ} (hM : Stochastic M) (t : ℕ) :
    freeEnergyOf β E t p - freeEnergyOf β E t (push p M) =
      1 / β * (kl p (gibbs β E t) - kl (push p M) (gibbs β E t)) := by
  rw [freeEnergyOf_eq hβ hp t, freeEnergyOf_eq hβ (density_push hp hM) t]
  ring

/-- [proved-derived; formal-checked] A kernel that keeps the equilibrium of a tick stationary
never raises the divergence from it. -/
theorem kl_push_gibbs_le [Nonempty S] {p : S → ℝ} (hp : Density p) {M : S → S → ℝ}
    (hM : Stochastic M) (t : ℕ) (hstat : push (gibbs β E t) M = gibbs β E t) :
    kl (push p M) (gibbs β E t) ≤ kl p (gibbs β E t) := by
  have h := kl_push_le (M := M) hp.nonneg (gibbs_pos β E t) hM
  rwa [hstat] at h

/-- [proved-derived; formal-checked] **The heat step never raises the free energy** when its
kernel keeps the equilibrium of the tick stationary. -/
theorem freeEnergyOf_push_le [Nonempty S] (hβ : 0 < β) {p : S → ℝ} (hp : Density p)
    {M : S → S → ℝ} (hM : Stochastic M) (t : ℕ) (hstat : push (gibbs β E t) M = gibbs β E t) :
    freeEnergyOf β E t (push p M) ≤ freeEnergyOf β E t p := by
  have h1 := freeEnergyOf_heat_step (E := E) hβ.ne' hp hM t
  have h2 := kl_push_gibbs_le hp hM t hstat
  have h3 : 0 ≤ 1 / β * (kl p (gibbs β E t) - kl (push p M) (gibbs β E t)) :=
    mul_nonneg (one_div_pos.mpr hβ).le (sub_nonneg.mpr h2)
  linarith

end FreeEnergy

/-! ## T4. The second law from any opening density -/

section Protocol

variable {S : Type*} [Fintype S] {β : ℝ} {E : ℕ → S → ℝ} {K : ℕ → S → S → ℝ} {p₀ : S → ℝ}

/-- [proved-derived; formal-checked] Each kernel of a driven protocol is stochastic. -/
theorem stochastic_of_driven (h : Driven β E K) (t : ℕ) : Stochastic (K t) :=
  ⟨h.nonneg t, h.row t⟩

/-- [proved-derived; formal-checked] Each kernel of a driven protocol keeps the equilibrium
density of its own tick stationary. -/
theorem push_gibbs_of_driven [Nonempty S] (h : Driven β E K) (t : ℕ) :
    push (gibbs β E t) (K t) = gibbs β E t := by
  funext y
  unfold push gibbs
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, h.stationary t y]

/-- [definition] The marginals of the driven chain opened at `p₀`:
`p_0 = p₀`, `p_(t+1) = p_t ⬝ K (t+1)`. -/
def marginal (K : ℕ → S → S → ℝ) (p₀ : S → ℝ) : ℕ → S → ℝ
  | 0 => p₀
  | t + 1 => push (marginal K p₀ t) (K (t + 1))

@[simp] theorem marginal_zero (K : ℕ → S → S → ℝ) (p₀ : S → ℝ) : marginal K p₀ 0 = p₀ := rfl

theorem marginal_succ (K : ℕ → S → S → ℝ) (p₀ : S → ℝ) (t : ℕ) :
    marginal K p₀ (t + 1) = push (marginal K p₀ t) (K (t + 1)) := rfl

/-- [proved-derived; formal-checked] Every marginal of a driven chain opened at a density is a
density. -/
theorem density_marginal (h : Driven β E K) (hp : Density p₀) :
    ∀ t, Density (marginal K p₀ t)
  | 0 => hp
  | t + 1 => density_push (density_marginal h hp t) (stochastic_of_driven h (t + 1))

/-- [definition] The mean work of `n` ticks: `Σ_(t<n) Σ_x p_t x · (E (t+1) x − E t x)`. -/
def meanWork (E : ℕ → S → ℝ) (K : ℕ → S → S → ℝ) (p₀ : S → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, ∑ x, marginal K p₀ t x * (E (t + 1) x - E t x)

/-- [definition] The mean heat paid to the bath in `n` ticks: the energy lost in the kernel
steps, `−Σ_(t<n) Σ_x (p_(t+1) x − p_t x) · E (t+1) x`. -/
def meanHeat (E : ℕ → S → ℝ) (K : ℕ → S → S → ℝ) (p₀ : S → ℝ) (n : ℕ) : ℝ :=
  -∑ t ∈ Finset.range n, ∑ x, (marginal K p₀ (t + 1) x - marginal K p₀ t x) * E (t + 1) x

/-- [definition] The production of `n` ticks, in nats: the divergence from the equilibrium of
its tick that each kernel removes. -/
def production (β : ℝ) (E : ℕ → S → ℝ) (K : ℕ → S → S → ℝ) (p₀ : S → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n,
    (kl (marginal K p₀ t) (gibbs β E (t + 1)) - kl (marginal K p₀ (t + 1)) (gibbs β E (t + 1)))

/-- [proved-derived; formal-checked] **One tick**: the free energy of the marginal changes by
the tick's mean work minus the divergence its kernel removes over `β`. -/
theorem freeEnergyOf_tick [Nonempty S] (h : Driven β E K) (hβ : β ≠ 0) (hp : Density p₀)
    (t : ℕ) :
    freeEnergyOf β E (t + 1) (marginal K p₀ (t + 1)) - freeEnergyOf β E t (marginal K p₀ t) =
      ∑ x, marginal K p₀ t x * (E (t + 1) x - E t x) -
        1 / β * (kl (marginal K p₀ t) (gibbs β E (t + 1)) -
          kl (marginal K p₀ (t + 1)) (gibbs β E (t + 1))) := by
  have hw := freeEnergyOf_work_step β E t (marginal K p₀ t)
  have hh : freeEnergyOf β E (t + 1) (marginal K p₀ t) -
      freeEnergyOf β E (t + 1) (marginal K p₀ (t + 1)) =
      1 / β * (kl (marginal K p₀ t) (gibbs β E (t + 1)) -
        kl (marginal K p₀ (t + 1)) (gibbs β E (t + 1))) :=
    freeEnergyOf_heat_step hβ (density_marginal h hp t) (stochastic_of_driven h (t + 1)) (t + 1)
  linarith

/-- [proved-derived; formal-checked] **The second law from any opening density, with its
slack**: `freeEnergyOf n p_n − freeEnergyOf 0 p₀ = meanWork n − (1/β) · production n`. -/
theorem freeEnergyOf_sub_eq [Nonempty S] (h : Driven β E K) (hβ : β ≠ 0) (hp : Density p₀)
    (n : ℕ) :
    freeEnergyOf β E n (marginal K p₀ n) - freeEnergyOf β E 0 p₀ =
      meanWork E K p₀ n - 1 / β * production β E K p₀ n := by
  induction n with
  | zero => simp [meanWork, production]
  | succ n ih =>
    have ht := freeEnergyOf_tick h hβ hp n
    unfold meanWork production at ih ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add]
    linarith

/-- [proved-derived; formal-checked] **Each tick's production is nonnegative**: its kernel keeps
the equilibrium of its tick stationary, so by data processing it never raises the divergence. -/
theorem production_nonneg [Nonempty S] (h : Driven β E K) (hp : Density p₀) (n : ℕ) :
    0 ≤ production β E K p₀ n := by
  unfold production
  refine Finset.sum_nonneg fun t _ => sub_nonneg.mpr ?_
  exact kl_push_gibbs_le (density_marginal h hp t) (stochastic_of_driven h (t + 1)) (t + 1)
    (push_gibbs_of_driven h (t + 1))

/-- [proved-derived; formal-checked] **The second law from any opening density**: the mean work
is at least the change of the free energy of the density. -/
theorem second_law_density [Nonempty S] (h : Driven β E K) (hβ : 0 < β) (hp : Density p₀)
    (n : ℕ) :
    freeEnergyOf β E n (marginal K p₀ n) - freeEnergyOf β E 0 p₀ ≤ meanWork E K p₀ n := by
  have h1 := freeEnergyOf_sub_eq h hβ.ne' hp n
  have h2 := production_nonneg h hp n
  have h3 : 0 ≤ 1 / β * production β E K p₀ n := mul_nonneg (one_div_pos.mpr hβ).le h2
  linarith

/-- [proved-derived; formal-checked] The dissipated work is the production over `β`. -/
theorem dissipated_work_eq_production [Nonempty S] (h : Driven β E K) (hβ : β ≠ 0)
    (hp : Density p₀) (n : ℕ) :
    meanWork E K p₀ n - (freeEnergyOf β E n (marginal K p₀ n) - freeEnergyOf β E 0 p₀) =
      1 / β * production β E K p₀ n := by
  have h1 := freeEnergyOf_sub_eq h hβ hp n
  linarith

/-! ### The join to the built file's path law -/

/-- [proved-derived; formal-checked] The last-occurrence marginal of the built file's driven
path law is the marginal of the chain opened at the equilibrium of tick `0`. -/
theorem sum_pathProb_last (n : ℕ) (g : S → ℝ) :
    ∑ γ : Fin (n + 1) → S, pathProb β E K n γ * g (γ (Fin.last n)) =
      ∑ x, marginal K (gibbs β E 0) n x * g x := by
  induction n generalizing g with
  | zero =>
    rw [sum_fin_one]
    simp [pathProb, gibbs]
  | succ n ih =>
    rw [sum_snoc]
    have hstep : ∀ γ : Fin (n + 1) → S,
        ∑ y, pathProb β E K (n + 1) (Fin.snoc γ y) *
            g ((Fin.snoc γ y : Fin (n + 2) → S) (Fin.last (n + 1))) =
          pathProb β E K n γ *
            (fun x => ∑ y, K (n + 1) x y * g y) (γ (Fin.last n)) := by
      intro γ
      simp only [pathProb_snoc, Fin.snoc_last, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    simp_rw [hstep]
    rw [ih (fun x => ∑ y, K (n + 1) x y * g y), marginal_succ]
    unfold push
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

/-- [proved-derived; formal-checked] The built file's path mean of `work` is the marginal
formula `meanWork` at the opening density `gibbs β E 0`. -/
theorem sum_pathProb_work (hrow : ∀ t x, ∑ y, K t x y = 1) (n : ℕ) :
    ∑ γ : Fin (n + 1) → S, pathProb β E K n γ * work E n γ =
      meanWork E K (gibbs β E 0) n := by
  induction n with
  | zero => simp [work, meanWork]
  | succ n ih =>
    rw [sum_snoc]
    have hstep : ∀ γ : Fin (n + 1) → S,
        ∑ y, pathProb β E K (n + 1) (Fin.snoc γ y) * work E (n + 1) (Fin.snoc γ y) =
          pathProb β E K n γ * work E n γ +
            pathProb β E K n γ *
              (fun x => E (n + 1) x - E n x) (γ (Fin.last n)) := by
      intro γ
      simp only [pathProb_snoc, work_snoc]
      have hy : ∀ y, pathProb β E K n γ * K (n + 1) (γ (Fin.last n)) y *
          (work E n γ + (E (n + 1) (γ (Fin.last n)) - E n (γ (Fin.last n)))) =
          pathProb β E K n γ *
            (work E n γ + (E (n + 1) (γ (Fin.last n)) - E n (γ (Fin.last n)))) *
            K (n + 1) (γ (Fin.last n)) y := fun y => by ring
      rw [Finset.sum_congr rfl fun y _ => hy y, ← Finset.mul_sum, hrow, mul_one, mul_add]
    simp_rw [hstep]
    rw [Finset.sum_add_distrib, ih, sum_pathProb_last n (fun x => E (n + 1) x - E n x)]
    unfold meanWork
    rw [Finset.sum_range_succ]

/-- [proved-derived; formal-checked] **The built `second_law` is the case `p₀ = gibbs β E 0`**:
its inequality follows from the second law over densities and `freeEnergy ≤ freeEnergyOf`,
without Jarzynski's equality. -/
theorem second_law_of_density [Nonempty S] (h : Driven β E K) (hβ : 0 < β) (n : ℕ) :
    freeEnergy β E n - freeEnergy β E 0 ≤ ∑ γ, pathProb β E K n γ * work E n γ := by
  rw [sum_pathProb_work h.row n]
  have h1 := second_law_density h hβ (density_gibbs β E 0) n
  rw [freeEnergyOf_gibbs hβ.ne' 0] at h1
  have h2 := freeEnergy_le_freeEnergyOf (E := E) hβ
    (density_marginal h (density_gibbs β E 0) n) n
  linarith

/-! ## T5. The first law and Clausius' inequality -/

/-- [proved-derived; formal-checked] **The first law**: mean work minus the heat paid to the
bath is the change of the mean energy. -/
theorem first_law (E : ℕ → S → ℝ) (K : ℕ → S → S → ℝ) (p₀ : S → ℝ) (n : ℕ) :
    meanWork E K p₀ n - meanHeat E K p₀ n =
      ∑ x, marginal K p₀ n x * E n x - ∑ x, p₀ x * E 0 x := by
  unfold meanWork meanHeat
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have e : ∑ x, marginal K p₀ n x * (E (n + 1) x - E n x) +
        ∑ x, (marginal K p₀ (n + 1) x - marginal K p₀ n x) * E (n + 1) x =
        ∑ x, marginal K p₀ (n + 1) x * E (n + 1) x - ∑ x, marginal K p₀ n x * E n x := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    linarith

/-- [proved-derived; formal-checked] **Clausius, with its slack**: the heat paid to the bath,
times `β`, is the entropy removed from the system plus the production. -/
theorem clausius_eq [Nonempty S] (h : Driven β E K) (hβ : β ≠ 0) (hp : Density p₀) (n : ℕ) :
    β * meanHeat E K p₀ n =
      entropy p₀ - entropy (marginal K p₀ n) + production β E K p₀ n := by
  have h1 := freeEnergyOf_sub_eq h hβ hp n
  have h2 := first_law E K p₀ n
  rw [freeEnergyOf_eq_energy_sub, freeEnergyOf_eq_energy_sub] at h1
  have h3 : meanHeat E K p₀ n =
      1 / β * entropy p₀ - 1 / β * entropy (marginal K p₀ n) +
        1 / β * production β E K p₀ n := by
    linarith
  have hb : β * (1 / β) = 1 := mul_one_div_cancel hβ
  calc β * meanHeat E K p₀ n
      = β * (1 / β) *
          (entropy p₀ - entropy (marginal K p₀ n) + production β E K p₀ n) := by
        rw [h3]
        ring
    _ = entropy p₀ - entropy (marginal K p₀ n) + production β E K p₀ n := by
        rw [hb, one_mul]

/-- [proved-derived; formal-checked] **Clausius' inequality** (`[from training]`): the entropy a
protocol removes from the system is paid to the bath as heat,
`entropy p₀ − entropy p_n ≤ β · meanHeat n`. -/
theorem clausius [Nonempty S] (h : Driven β E K) (hβ : 0 < β) (hp : Density p₀) (n : ℕ) :
    entropy p₀ - entropy (marginal K p₀ n) ≤ β * meanHeat E K p₀ n := by
  rw [clausius_eq h hβ.ne' hp n]
  linarith [production_nonneg h hp n]

/-! ## T6. Landauer's bound -/

/-- [definition] A point mass: one state holds the whole density. -/
def IsPoint (p : S → ℝ) : Prop := ∃ a, p a = 1 ∧ ∀ x, x ≠ a → p x = 0

/-- [proved-derived; formal-checked] A point mass has no entropy. -/
theorem entropy_of_isPoint {p : S → ℝ} (h : IsPoint p) : entropy p = 0 := by
  obtain ⟨a, ha, hrest⟩ := h
  unfold entropy
  rw [neg_eq_zero]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x = a
  · rw [hx, ha, Real.log_one, mul_zero]
  · rw [hrest x hx, zero_mul]

/-- [proved-derived; formal-checked] The uniform density is a density. -/
theorem density_uniform [Nonempty S] : Density (fun _ : S => 1 / (Fintype.card S : ℝ)) where
  nonneg _ := by positivity
  total := by
    have hN : (Fintype.card S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div_cancel hN]

/-- [proved-derived; formal-checked] The uniform density on `S` holds `log (card S)` nats. -/
theorem entropy_uniform [Nonempty S] :
    entropy (fun _ : S => 1 / (Fintype.card S : ℝ)) = Real.log (Fintype.card S) := by
  have hN : (Fintype.card S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold entropy
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div, Real.log_inv, ← mul_assoc,
    mul_inv_cancel₀ hN, one_mul, neg_neg]

/-- [proved-derived; formal-checked] The entropy of a density is nonnegative. -/
theorem entropy_nonneg {p : S → ℝ} (hp : Density p) : 0 ≤ entropy p := by
  unfold entropy
  rw [neg_nonneg]
  refine Finset.sum_nonpos fun x _ => ?_
  have h1 : p x ≤ 1 := by
    rw [← hp.total]
    exact Finset.single_le_sum (fun y _ => hp.nonneg y) (Finset.mem_univ x)
  exact mul_nonpos_of_nonneg_of_nonpos (hp.nonneg x) (Real.log_nonpos (hp.nonneg x) h1)

/-- [proved-derived; formal-checked] **Landauer, the partial form**: a protocol that lowers the
entropy by `ΔH` pays at least `ΔH / β` of heat to the bath. -/
theorem landauer_partial [Nonempty S] (h : Driven β E K) (hβ : 0 < β) (hp : Density p₀)
    (n : ℕ) :
    (entropy p₀ - entropy (marginal K p₀ n)) / β ≤ meanHeat E K p₀ n := by
  rw [div_le_iff₀ hβ, mul_comm]
  exact clausius h hβ hp n

/-- [proved-derived; formal-checked] **Landauer, the partial form in work**: the mean work is at
least `ΔH / β` plus the change of the mean energy. -/
theorem landauer_partial_work [Nonempty S] (h : Driven β E K) (hβ : 0 < β) (hp : Density p₀)
    (n : ℕ) :
    (entropy p₀ - entropy (marginal K p₀ n)) / β +
        (∑ x, marginal K p₀ n x * E n x - ∑ x, p₀ x * E 0 x) ≤ meanWork E K p₀ n := by
  have h1 := landauer_partial h hβ hp n
  have h2 := first_law E K p₀ n
  linarith

/-- [proved-derived; formal-checked] A density with the uniform values is a density. -/
theorem density_of_uniform [Nonempty S] (hunif : ∀ x, p₀ x = 1 / (Fintype.card S : ℝ)) :
    Density p₀ := by
  have hp0 : p₀ = fun _ => 1 / (Fintype.card S : ℝ) := funext hunif
  rw [hp0]
  exact density_uniform

/-- [proved-derived; formal-checked] **Landauer on `card S` states**: a driven protocol that
opens at the uniform density and closes at a point mass pays `log (card S) ≤ β · meanHeat`. -/
theorem landauer_card [Nonempty S] (h : Driven β E K) (hβ : 0 < β) {n : ℕ}
    (hunif : ∀ x, p₀ x = 1 / (Fintype.card S : ℝ)) (hpt : IsPoint (marginal K p₀ n)) :
    Real.log (Fintype.card S) ≤ β * meanHeat E K p₀ n := by
  have hp0 : p₀ = fun _ => 1 / (Fintype.card S : ℝ) := funext hunif
  have hc := clausius h hβ (density_of_uniform hunif) n
  rw [entropy_of_isPoint hpt, sub_zero, hp0, entropy_uniform] at hc
  rw [hp0]
  exact hc

/-- [proved-derived; formal-checked] **Landauer's bound** (Landauer 1961, `[from training]`):
erasing one bit, from the uniform density on two states to a point mass, pays
`log 2 ≤ β · meanHeat`. -/
theorem landauer_bit [Nonempty S] (h : Driven β E K) (hβ : 0 < β) {n : ℕ}
    (hcard : Fintype.card S = 2) (hunif : ∀ x, p₀ x = 1 / (Fintype.card S : ℝ))
    (hpt : IsPoint (marginal K p₀ n)) :
    Real.log 2 ≤ β * meanHeat E K p₀ n := by
  have h1 := landauer_card h hβ hunif hpt
  rw [hcard, Nat.cast_ofNat] at h1
  exact h1

/-- [proved-derived; formal-checked] **Landauer in work, on `card S` states**: where the first
and last energies are one constant (a degenerate memory), the mean work is at least
`log (card S) / β`. -/
theorem landauer_card_work [Nonempty S] (h : Driven β E K) (hβ : 0 < β) {n : ℕ}
    (hunif : ∀ x, p₀ x = 1 / (Fintype.card S : ℝ)) (hpt : IsPoint (marginal K p₀ n))
    (c : ℝ) (h0 : ∀ x, E 0 x = c) (hn : ∀ x, E n x = c) :
    Real.log (Fintype.card S) / β ≤ meanWork E K p₀ n := by
  have hp := density_of_uniform hunif
  have hQ := landauer_card h hβ hunif hpt
  have hfl := first_law E K p₀ n
  have hU : ∑ x, marginal K p₀ n x * E n x - ∑ x, p₀ x * E 0 x = 0 := by
    simp_rw [h0, hn]
    rw [← Finset.sum_mul, ← Finset.sum_mul, (density_marginal h hp n).total, hp.total]
    ring
  have hWQ : meanWork E K p₀ n = meanHeat E K p₀ n := by linarith
  rw [div_le_iff₀ hβ, hWQ, mul_comm]
  exact hQ

/-- [proved-derived; formal-checked] **Landauer in work, one bit**: on a degenerate two-state
memory, erasing the bit costs at least `log 2 / β` of work. -/
theorem landauer_bit_work [Nonempty S] (h : Driven β E K) (hβ : 0 < β) {n : ℕ}
    (hcard : Fintype.card S = 2) (hunif : ∀ x, p₀ x = 1 / (Fintype.card S : ℝ))
    (hpt : IsPoint (marginal K p₀ n)) (c : ℝ) (h0 : ∀ x, E 0 x = c) (hn : ∀ x, E n x = c) :
    Real.log 2 / β ≤ meanWork E K p₀ n := by
  have h1 := landauer_card_work h hβ hunif hpt c h0 hn
  rw [hcard, Nat.cast_ofNat] at h1
  exact h1

/-- [proved-derived; formal-checked] **Landauer's bound on `Bool`**: a driven protocol on the
two states of a bit that opens at `(1/2, 1/2)` and closes at a point mass pays at least
`log 2 / β` of heat. -/
theorem landauer_bool {β : ℝ} {E : ℕ → Bool → ℝ} {K : ℕ → Bool → Bool → ℝ} {p₀ : Bool → ℝ}
    {n : ℕ} (h : Driven β E K) (hβ : 0 < β) (hunif : ∀ b, p₀ b = 1 / 2)
    (hpt : IsPoint (marginal K p₀ n)) :
    Real.log 2 / β ≤ meanHeat E K p₀ n := by
  have hunif' : ∀ b, p₀ b = 1 / (Fintype.card Bool : ℝ) := by
    intro b
    rw [hunif b, Fintype.card_bool]
    norm_num
  have h2 := landauer_bit h hβ Fintype.card_bool hunif' hpt
  rw [div_le_iff₀ hβ, mul_comm]
  exact h2

end Protocol

/-! ## T7. A quotient's price -/

section Quotient

variable {S : Type*} [Fintype S] {R : Type*} [Fintype R] [DecidableEq R]
  {β : ℝ} {E : ℕ → S → ℝ} {K : ℕ → S → S → ℝ} {p₀ : S → ℝ}

/-- [definition] The image of a density under a map: each value of `f` receives the mass of its
fibre. -/
def pushforward (f : S → R) (p : S → ℝ) (r : R) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => f x = r), p x

/-- [proved-derived; formal-checked] Fibres of one size `m` count the source:
`card S = card R · m`. -/
theorem card_eq_of_fibres (f : S → R) {m : ℕ}
    (hfib : ∀ r, (Finset.univ.filter fun x => f x = r).card = m) :
    Fintype.card S = Fintype.card R * m := by
  have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
    (by intro x _; simp)
  rw [Finset.card_univ] at h
  calc Fintype.card S = ∑ r : R, (Finset.univ.filter fun x => f x = r).card := h
    _ = ∑ _r : R, m := Finset.sum_congr rfl fun r _ => hfib r
    _ = Fintype.card R * m := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- [proved-derived; formal-checked] A map with fibres of one size sends the uniform density to
the uniform density. -/
theorem pushforward_uniform_of_fibres [Nonempty S] (f : S → R) {m : ℕ} (hm : 0 < m)
    (hfib : ∀ r, (Finset.univ.filter fun x => f x = r).card = m) (r : R) :
    pushforward f (fun _ => 1 / (Fintype.card S : ℝ)) r = 1 / (Fintype.card R : ℝ) := by
  have : Nonempty R := Nonempty.map f inferInstance
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hR : (Fintype.card R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold pushforward
  rw [Finset.sum_const, hfib r, nsmul_eq_mul, card_eq_of_fibres f hfib, Nat.cast_mul]
  field_simp

/-- [proved-derived; formal-checked] **The entropy a quotient removes**: merging fibres of `m`
members on a uniform density removes `log m` nats. -/
theorem entropy_removed_of_fibres [Nonempty S] (f : S → R) {m : ℕ} (hm : 0 < m)
    (hfib : ∀ r, (Finset.univ.filter fun x => f x = r).card = m) :
    entropy (fun _ : S => 1 / (Fintype.card S : ℝ)) -
        entropy (pushforward f fun _ => 1 / (Fintype.card S : ℝ)) = Real.log m := by
  have : Nonempty R := Nonempty.map f inferInstance
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hR : (Fintype.card R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hq : pushforward f (fun _ => 1 / (Fintype.card S : ℝ)) =
      fun _ => 1 / (Fintype.card R : ℝ) := funext (pushforward_uniform_of_fibres f hm hfib)
  rw [hq, entropy_uniform, entropy_uniform, card_eq_of_fibres f hfib, Nat.cast_mul,
    Real.log_mul hR hm']
  ring

/-- [proved-derived; formal-checked] **A quotient's price**: a driven protocol that opens at the
uniform density and closes with no more entropy than the image of a map with fibres of `m`
members pays at least `log m / β` of heat: forgetting which member of a fibre was held. -/
theorem quotient_price [Nonempty S] (h : Driven β E K) (hβ : 0 < β) (f : S → R) {m : ℕ}
    (hm : 0 < m) (hfib : ∀ r, (Finset.univ.filter fun x => f x = r).card = m) {n : ℕ}
    (hunif : ∀ x, p₀ x = 1 / (Fintype.card S : ℝ))
    (hend : entropy (marginal K p₀ n) ≤ entropy (pushforward f p₀)) :
    Real.log m / β ≤ meanHeat E K p₀ n := by
  have hp0 : p₀ = fun _ => 1 / (Fintype.card S : ℝ) := funext hunif
  have hc := landauer_partial h hβ (density_of_uniform hunif) n
  have hrem := entropy_removed_of_fibres f hm hfib
  rw [← hp0] at hrem
  have hle : Real.log m / β ≤ (entropy p₀ - entropy (marginal K p₀ n)) / β := by
    apply div_le_div_of_nonneg_right _ hβ.le
    linarith
  linarith

end Quotient

section Audit

#print axioms kl_nonneg
#print axioms kl_eq_zero_iff
#print axioms log_sum_le
#print axioms kl_push_le
#print axioms freeEnergyOf_eq
#print axioms freeEnergyOf_sub_gibbs
#print axioms freeEnergy_le_freeEnergyOf
#print axioms freeEnergyOf_eq_freeEnergy_iff
#print axioms freeEnergyOf_work_step
#print axioms freeEnergyOf_heat_step
#print axioms freeEnergyOf_push_le
#print axioms freeEnergyOf_sub_eq
#print axioms production_nonneg
#print axioms second_law_density
#print axioms dissipated_work_eq_production
#print axioms sum_pathProb_last
#print axioms sum_pathProb_work
#print axioms second_law_of_density
#print axioms first_law
#print axioms clausius_eq
#print axioms clausius
#print axioms entropy_uniform
#print axioms entropy_of_isPoint
#print axioms entropy_nonneg
#print axioms landauer_partial
#print axioms landauer_partial_work
#print axioms landauer_card
#print axioms landauer_bit
#print axioms landauer_card_work
#print axioms landauer_bit_work
#print axioms landauer_bool
#print axioms card_eq_of_fibres
#print axioms pushforward_uniform_of_fibres
#print axioms entropy_removed_of_fibres
#print axioms quotient_price

end Audit

end Holonics.Aeon.Production.Landauer
