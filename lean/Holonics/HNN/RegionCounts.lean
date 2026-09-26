import Holonics.HNN.LatticeDeposit
import Holonics.HNN.TargetFace
import Holonics.HNN.IndexedOpen

/-!
# HNN.RegionCounts: the receiving parametron's region class masses, read at the grain

[definition; agent-inferred] Decision 27 of the step 4 design (`docs/plans/THE_REBUILD.md`), from
the measurement of Decision 26's first term and Sol's derivation (choice (c), the receiving
parametron's class-mass storage). For each admitted receiver region `r` (a certified finite
quotient of the receiver's address; for campaign 1, the retained window's preceding cell) the
receiving parametron stores class masses, deposited only by the comparisons that reached it, over
the positive Krichevsky–Trofimov prior `α_(r,c) = 1/2` (one per two). The receiving face is the
grain of those masses, and the wave corrects it:

```text
storage    C_(r,c) = α_(r,c) + Σ_(i : r_i = r) w_i q_(i,c) ,   q_i = e_(t_i) ,  w_i ≥ 0
face       p_(r,c) = C_(r,c) / N_r ,   N_r = Σ_c C_(r,c)
step       p' − p = w/(N + w)·(q − p) = w/(N + w)·(g + p̃ − p) ,   g = q − p̃
prior      p = A/(A + S)·α/A + S/(A + S)·q̄ ,   A = Σ_c α_c ,  S = Σ_i w_i ,  q̄ = S⁻¹ Σ_i w_i q_i
grain      2^k ≤ p^L < 2^(k+1)  (integer comparisons) ,   k = L n + j ,  0 ≤ j < L
combined   logits = k/L + R P^τ v ;   ⟨g, δR P^τ v⟩ = ⟨g (P^τ v)ᵀ, δR⟩
```

The masses are the whole standing of the region receiver: they retain no occurrence list, and the
future faces factor through them (`countStanding`, a `Foundation/Standing.StandingLaw`). They run
on Decision 22's carrier lattice (`HNN/LatticeDeposit`), or exactly as integers of half-units.

[proved-derived; formal-checked] What is proved.

1. **The step of a reached comparison** (`count_step_mass`, `count_step_normalized`,
   `count_step_covector`): adding `w·e_t`, `w ≥ 0`, to positive masses gives `Σ C' = N + w` and
   keeps every mass positive; the face moves by `p' − p = w/(N + w)·(q − p)` and stays a positive
   section; with the scored face `p̃` and the reached covector `g = q − p̃`, the deposit is
   `w(p̃ + g)` and the motion is `w/(N + w)·(g + p̃ − p)`, where `p̃ − p` names the grain residual.
   The general distribution form is `face_step`. The count face is a positive section, so it is
   never one-hot and the target's code length is finite and positive (`count_face_positive_section`,
   through `HNN/TargetFace.positive_section_not_one_hot`): a categorical comparison needs no finite
   logit for `e_t`.
2. **The prior decays exactly** (`count_prior_decay`): `p = A/(A + S)·α/A + S/(A + S)·q̄`, and the
   deviation from the reached mean is the prior's, scaled by `A/(A + S)`.
   **The context-free fixed point** (`context_free_fixed_face`): a deposit along a fixed class
   distribution `q̄` contracts the face toward it, `p' − q̄ = N/(N + w)·(p − q̄)`, so `q̄` is a fixed
   point; a batch of repeated targets `q̄` leaves the deviation `A/(A + S)·(α/A − q̄)`.
   **It is Krichevsky–Trofimov** (`count_face_eq_kt`): at `α = 1/2` with unit weights, the face is
   KT's probability `(n_c + 1/2)/(n + |A|/2)` after counts `n_c` in `n` observations. The fixture
   (`kt_fixture`): after `a, a, b` from `(1/2, 1/2)`, `C = (5/2, 3/2)`, `N = 4`,
   `p = (5/8, 3/8)`, with the prefix faces `(3/4, 1/4)` and `(5/6, 1/6)`, all equal to KT's.
   The half-unit integers `2C = 2n_c + 1` read through `HNN/IndexedOpen.normalized` give the same
   face, as the exact ratio `(2n_c + 1)/(2n + |A|)` with its division and remainder
   (`kt_half_units_normalized`).
3. **Future sufficiency** (`count_future_sufficient`, `countStanding`): the region masses are a
   `StandingLaw` whose retention is the masses; two pasts with equal masses have equal successors
   and equal faces after every future word of (region, weight, target) comparisons, and a region's
   future needs only its own masses (`regionRun_local`: a region's masses are the count run of the
   comparisons that reached it). The masses are invariant under permuting the past
   (`regionRun_perm`); the fixture permutes `a, a, b` to `a, b, a` (`past_permutation_fixture`).
   **The normal law's solved map** (`count_face_solves_normal_law`): at one-hot region features
   `f = e_r` and the target `q`, with the prior Gram `diag(A_r)`, the Gram is diagonal with the
   region totals and the count face is the unique solve of `W H = B` (`HNN/Normal`'s `windowGram`,
   `windowCovector`): Sol's candidate (a) specialized to regions.
4. **The grain** (`grain_log_iff_pow_bounds`, `grainExponent_spec`, `grain_face_residual`,
   `grain_code_residual`): for a positive rational `a/b` and every `L`, the integer `k` with
   `2^k ≤ (a/b)^L < 2^(k+1)` exists, is unique, and is decided by the natural-number comparisons
   `2^(k⁺) b^L ≤ 2^(k⁻) a^L` and `2^((k+1)⁻) a^L < 2^((k+1)⁺) b^L` (`k⁺ = max k 0`,
   `k⁻ = max (−k) 0`); at `L ≥ 1`, `k/L ≤ log₂ x < (k+1)/L`, the owner's grain read of `log₂ x`
   (`HNN/Ratio.grainRead`) is the carry and phase class `(k div L, k mod L)`, and the scored code
   length `codeLength (k/L) t` differs from `−log₂ p_t` by less than `1/L` (the owner's
   `face_code_length_within_grain`). The fixture (`grain_fixture`): `5/8` and `3/8` at `L = 16`
   have `k = −11` and `k = −23`, decided on the integers, with carry and phase class `(−1, 5)` and
   `(−2, 9)`, which are the owner's grain reads of `log₂(5/8)` and `log₂(3/8)`.
5. **Lattice accounting** (`count_lattice_accounting`): under Decision 22's carry
   (`HNN/LatticeDeposit.run`), the carried masses plus the carried remainder plus the released
   tails equal `α + Σ w q`, coordinatewise, and every carried mass is within one lattice unit of
   the exact one; updates on the lattice carry exactly, with no remainder and no release
   (`count_lattice_exact`), so the KT masses run exactly at every lattice (`kt_lattice_exact`).
6. **The combined face** (`combined_face_pullback`, `combined_code_pullback`): the logits are the
   count face's grain logits plus the wave's `R P^τ v`. Along `R + x δR` they move by
   `x δR P^τ v` at every count state: the count part carries no parameter pulled back through
   `R`. A covector `g` pairs with that motion as `⟨g (P^τ v)ᵀ, δR⟩`, the wave-only face's pullback,
   and returns `(P^τ)ᵀ Rᵀ g` to the anchor as before; the real code length's derivative along the
   line is `⟨(p̂ − q)(P^τ v)ᵀ, δR⟩` (`combined_code_pullback`, from `hasDerivAt_codeLength_line`),
   with `p̂` the combined face. The counts enter the wave's learning only through the face `p̂` at which the covector is read, so
   the rings, contacts and charts learn only what the counts do not already say.

[open] Descent of the scored code length along the deposit is not claimed: the grain read has
plateaus, so each scored step needs its receipt (Sol's derivation). The standing-cut verdict,
the model's code-length enclosure strictly below online order-0's on the unchanged held-out cells,
is decided by the exposure (Decision 27, "Success, exactly").

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.RegionCounts

open Matrix
open Holonics.HNN.Ratio (codeLength grainRead face_constant_on_fibre face_code_length_within_grain)

/-! ## 1. One region's class masses and the step of a reached comparison -/

section Step

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- [definition] **The one-hot target** `q = e_t` of a reached comparison, in the probability
chart. -/
def target (t : A) : A → ℚ := Pi.single t 1

/-- [definition] **The region's total mass** `N = Σ_c C_c`. -/
def total (C : A → ℚ) : ℚ := ∑ c, C c

/-- [definition] **The count face** `p_c = C_c / N`: the receiving parametron's stored class masses
read as a probability section. -/
def countFace (C : A → ℚ) (c : A) : ℚ := C c / total C

/-- [definition] **The deposit of one reached comparison** `C' = C + w q`: the only change of the
region's class masses. -/
def deposit (C : A → ℚ) (w : ℚ) (q : A → ℚ) : A → ℚ := fun c => C c + w * q c

/-- [definition] **The reached real covector** `g = q − p̃`, the descent covector of the ratio at
the scored face `p̃`. -/
def covector (t : A) (ptilde : A → ℚ) : A → ℚ := fun c => target t c - ptilde c

theorem target_sum (t : A) : ∑ c, target t c = 1 := by
  simp [target]

omit [Fintype A] in
theorem target_nonneg (t c : A) : 0 ≤ target t c := by
  unfold target
  by_cases h : c = t
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

omit [DecidableEq A] in
theorem total_deposit (C : A → ℚ) (w : ℚ) (q : A → ℚ) :
    total (deposit C w q) = total C + w * ∑ c, q c := by
  simp only [total, deposit, Finset.sum_add_distrib, Finset.mul_sum]

omit [DecidableEq A] in
theorem total_pos [Nonempty A] {C : A → ℚ} (hC : ∀ c, 0 < C c) : 0 < total C :=
  Finset.sum_pos (fun c _ => hC c) Finset.univ_nonempty

omit [DecidableEq A] in
theorem countFace_pos [Nonempty A] {C : A → ℚ} (hC : ∀ c, 0 < C c) (c : A) :
    0 < countFace C c :=
  div_pos (hC c) (total_pos hC)

omit [DecidableEq A] in
theorem countFace_sum [Nonempty A] {C : A → ℚ} (hC : ∀ c, 0 < C c) : ∑ c, countFace C c = 1 := by
  simp only [countFace, ← Finset.sum_div]
  exact div_self (total_pos hC).ne'

omit [Fintype A] [DecidableEq A] in
theorem deposit_pos {C : A → ℚ} (hC : ∀ c, 0 < C c) {w : ℚ} (hw : 0 ≤ w) {q : A → ℚ}
    (hq : ∀ c, 0 ≤ q c) (c : A) : 0 < deposit C w q c := by
  have := mul_nonneg hw (hq c)
  simp only [deposit]
  linarith [hC c]

omit [DecidableEq A] in
/-- [proved-derived; formal-checked] **The face moves along the chord to the deposited
distribution.** For masses of positive total `N`, a weight `w ≥ 0` and any class distribution `q`
(`Σ q = 1`), `p' − p = w/(N + w)·(q − p)`. -/
theorem face_step {C : A → ℚ} (hN : 0 < total C) {w : ℚ} (hw : 0 ≤ w) {q : A → ℚ}
    (hq : ∑ c, q c = 1) (c : A) :
    countFace (deposit C w q) c - countFace C c = w / (total C + w) * (q c - countFace C c) := by
  have hN' : 0 < total C + w := by linarith
  simp only [countFace, total_deposit, hq, mul_one, deposit]
  field_simp
  ring

/-- [proved-derived; formal-checked] **`count_step_mass`.** A reached comparison deposits `w·e_t`,
`w ≥ 0`, into positive class masses: the total becomes `N + w`, every mass stays positive, and the
masses change by exactly `w·e_t`. In the receiving parametron: its class-mass storage grows by the
reached weight at the target class, and nowhere else. -/
theorem count_step_mass {C : A → ℚ} (hC : ∀ c, 0 < C c) {w : ℚ} (hw : 0 ≤ w) (t : A) :
    total (deposit C w (target t)) = total C + w ∧ (∀ c, 0 < deposit C w (target t) c) ∧
      ∀ c, deposit C w (target t) c - C c = w * target t c := by
  refine ⟨by rw [total_deposit, target_sum, mul_one], deposit_pos hC hw (target_nonneg t),
    fun c => by simp [deposit]⟩

/-- [proved-derived; formal-checked] **`count_step_normalized`.** After the deposit of `w·e_t`,
`w ≥ 0`, into positive masses, the face stays a positive section (positive, summing to one) and
moves by `p' − p = w/(N + w)·(q − p)`, `q = e_t`: the receiving parametron's face steps along the
chord to the target by the reached weight's share of its new total. -/
theorem count_step_normalized [Nonempty A] {C : A → ℚ} (hC : ∀ c, 0 < C c) {w : ℚ} (hw : 0 ≤ w)
    (t : A) :
    (∀ c, 0 < countFace (deposit C w (target t)) c) ∧
      ∑ c, countFace (deposit C w (target t)) c = 1 ∧
      ∀ c, countFace (deposit C w (target t)) c - countFace C c =
        w / (total C + w) * (target t c - countFace C c) := by
  have hC' := deposit_pos hC hw (target_nonneg t)
  exact ⟨countFace_pos hC', countFace_sum hC', face_step (total_pos hC) hw (target_sum t)⟩

/-- [proved-derived; formal-checked] **`count_step_covector`.** With the scored face `p̃` and the
reached covector `g = q − p̃`:
* the deposit is `w(p̃ + g)`: the `p̃` term accounts for the receiver's exposure, and all
  target-dependent change comes from the reached covector;
* the face moves by `p' − p = w/(N + w)·(g + p̃ − p)`, where `p̃ − p` names the grain residual;
* when `p̃` is a probability section (`Σ p̃ = 1`), the covector carries no mass, `Σ g = 0`.

So the receiving parametron's storage is driven by the ratio's covector at the locus it reached. -/
theorem count_step_covector [Nonempty A] {C : A → ℚ} (hC : ∀ c, 0 < C c) {w : ℚ} (hw : 0 ≤ w)
    (t : A) (ptilde : A → ℚ) :
    (∀ c, deposit C w (target t) c - C c = w * (ptilde c + covector t ptilde c)) ∧
      (∀ c, countFace (deposit C w (target t)) c - countFace C c =
        w / (total C + w) * (covector t ptilde c + ptilde c - countFace C c)) ∧
      (∑ c, ptilde c = 1 → ∑ c, covector t ptilde c = 0) := by
  refine ⟨fun c => by simp [deposit, covector], fun c => ?_, fun hp => ?_⟩
  · rw [(count_step_normalized hC hw t).2.2 c]
    simp [covector]
  · simp only [covector, Finset.sum_sub_distrib, target_sum, hp, sub_self]

open Holonics.Computation.HolonicInformationTheory (PositiveProbabilitySection) in
/-- [definition] The count face of positive masses, as a positive probability section in the real
chart. -/
def countSection [Nonempty A] {C : A → ℚ} (hC : ∀ c, 0 < C c) : PositiveProbabilitySection A where
  mass c := (countFace C c : ℝ)
  positive c := by exact_mod_cast countFace_pos hC c
  normalized := by
    have := countFace_sum hC
    exact_mod_cast this

/-- [proved-derived; formal-checked] **The count face is a positive section, never one-hot**
(`HNN/TargetFace.positive_section_not_one_hot`). Over at least two classes, the face of positive
masses gives the target a mass strictly between zero and one, is not `e_t`, and codes the target
in a finite, positive length `−log₂ p_t`. The categorical comparison therefore needs no finite
logit for `e_t`: `e_t`'s zero components stay in the ratio's nonunit fibre, and the supported code
read is `−log₂ p_t`. -/
theorem count_face_positive_section [Nonempty A] {C : A → ℚ} (hC : ∀ c, 0 < C c) (t : A)
    (hc : ∃ c, c ≠ t) :
    0 < (countSection hC).mass t ∧ (countSection hC).mass t < 1 ∧
      (countSection hC).mass ≠ Pi.single t 1 ∧ 0 < -Real.logb 2 ((countSection hC).mass t) := by
  obtain ⟨hlt, hne⟩ := Holonics.HNN.TargetFace.positive_section_not_one_hot (countSection hC) t hc
  refine ⟨(countSection hC).positive t, hlt, hne, ?_⟩
  rw [neg_pos]
  exact Real.logb_neg (by norm_num) ((countSection hC).positive t) hlt

end Step

/-! ## 2. Runs, the exact prior decay, the fixed point and Krichevsky–Trofimov -/

section Run

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- [definition] **A run of reached comparisons** `(w_i, q_i)` over the prior masses `α`: the
passage of a word through the deposit law. What the region retains is the result, its masses
(`countStanding`), never the word. -/
def countRun (α : A → ℚ) (ws : List (ℚ × (A → ℚ))) : A → ℚ :=
  ws.foldl (fun C d => deposit C d.1 d.2) α

omit [Fintype A] [DecidableEq A] in
theorem countRun_cons (α : A → ℚ) (d : ℚ × (A → ℚ)) (ws : List (ℚ × (A → ℚ))) :
    countRun α (d :: ws) = countRun (deposit α d.1 d.2) ws := rfl

omit [Fintype A] [DecidableEq A] in
/-- [proved-derived; formal-checked] The run's masses are the prior plus the reached deposits,
`C = α + Σ_i w_i q_i`: the order of the comparisons does not enter. -/
theorem countRun_apply (α : A → ℚ) (ws : List (ℚ × (A → ℚ))) (c : A) :
    countRun α ws c = α c + (ws.map fun d => d.1 * d.2 c).sum := by
  induction ws generalizing α with
  | nil => simp [countRun]
  | cons d ws ih =>
    rw [countRun_cons, ih]
    simp only [deposit, List.map_cons, List.sum_cons]
    ring

/-- [definition] **The reached weight** `S = Σ_i w_i`. -/
def reachedWeight (ws : List (ℚ × (A → ℚ))) : ℚ := (ws.map Prod.fst).sum

/-- [definition] **The reached mean** `q̄ = S⁻¹ Σ_i w_i q_i`. -/
def reachedMean (ws : List (ℚ × (A → ℚ))) (c : A) : ℚ :=
  (ws.map fun d => d.1 * d.2 c).sum / reachedWeight ws

omit [DecidableEq A] in
theorem total_countRun (α : A → ℚ) (ws : List (ℚ × (A → ℚ)))
    (hq : ∀ d ∈ ws, ∑ c, d.2 c = 1) :
    total (countRun α ws) = total α + reachedWeight ws := by
  induction ws generalizing α with
  | nil => simp [countRun, reachedWeight]
  | cons d ws ih =>
    rw [countRun_cons, ih _ (fun d' hd' => hq d' (List.mem_cons_of_mem _ hd')), total_deposit,
      hq d (by simp)]
    simp only [reachedWeight, List.map_cons, List.sum_cons, mul_one]
    ring

omit [Fintype A] [DecidableEq A] in
theorem countRun_pos {α : A → ℚ} (hα : ∀ c, 0 < α c) (ws : List (ℚ × (A → ℚ)))
    (hw : ∀ d ∈ ws, 0 ≤ d.1) (hq : ∀ d ∈ ws, ∀ c, 0 ≤ d.2 c) (c : A) :
    0 < countRun α ws c := by
  induction ws generalizing α with
  | nil => exact hα c
  | cons d ws ih =>
    rw [countRun_cons]
    exact ih (deposit_pos hα (hw d (by simp)) (hq d (by simp)))
      (fun d' hd' => hw d' (List.mem_cons_of_mem _ hd'))
      (fun d' hd' => hq d' (List.mem_cons_of_mem _ hd'))

omit [DecidableEq A] in
/-- [proved-derived; formal-checked] **`count_prior_decay`.** With the prior mass `A = Σ α`, the
reached weight `S = Σ_i w_i > 0` and the reached mean `q̄ = S⁻¹ Σ_i w_i q_i` (each `q_i` a class
distribution):
* `p = A/(A + S)·α/A + S/(A + S)·q̄`: the declared prior face `p⁰ = α/A` keeps exactly the weight
  `A/(A + S)`;
* `p − q̄ = A/(A + S)·(α/A − q̄)`.

In the receiving parametron: the prior is a storage like any deposit, and it decays exactly as the
reached weight grows. -/
theorem count_prior_decay [Nonempty A] {α : A → ℚ} (hα : ∀ c, 0 < α c)
    (ws : List (ℚ × (A → ℚ))) (hq : ∀ d ∈ ws, ∑ c, d.2 c = 1) (hS : 0 < reachedWeight ws)
    (c : A) :
    countFace (countRun α ws) c =
        total α / (total α + reachedWeight ws) * (α c / total α) +
          reachedWeight ws / (total α + reachedWeight ws) * reachedMean ws c ∧
      countFace (countRun α ws) c - reachedMean ws c =
        total α / (total α + reachedWeight ws) * (α c / total α - reachedMean ws c) := by
  have hA := total_pos hα
  have hAS : 0 < total α + reachedWeight ws := by linarith
  have h1 : countFace (countRun α ws) c =
      total α / (total α + reachedWeight ws) * (α c / total α) +
        reachedWeight ws / (total α + reachedWeight ws) * reachedMean ws c := by
    rw [countFace, total_countRun α ws hq, countRun_apply]
    unfold reachedMean
    field_simp
  refine ⟨h1, ?_⟩
  rw [h1]
  field_simp
  ring

omit [DecidableEq A] in
/-- [proved-derived; formal-checked] **`context_free_fixed_face`.** For a fixed class distribution
`q̄` (`Σ q̄ = 1`):
* one deposit `w q̄`, `w ≥ 0`, contracts the face toward it, `p' − q̄ = N/(N + w)·(p − q̄)`;
* so `q̄` is a fixed point: a face already at `q̄` stays there;
* repeated targets `q̄` from positive prior masses, of total weight `S > 0`, leave the deviation
  `p − q̄ = A/(A + S)·(α/A − q̄)`, which the reached weight drives to zero through positive faces.

In the receiving parametron at one region (the context-free case), the fixed point of the face is
the distribution of the targets that reached it: the online order-0 face. -/
theorem context_free_fixed_face [Nonempty A] {qbar : A → ℚ} (hq : ∑ c, qbar c = 1) :
    (∀ C : A → ℚ, 0 < total C → ∀ w : ℚ, 0 ≤ w → ∀ c,
      countFace (deposit C w qbar) c - qbar c =
        total C / (total C + w) * (countFace C c - qbar c)) ∧
    (∀ C : A → ℚ, 0 < total C → ∀ w : ℚ, 0 ≤ w →
      (∀ c, countFace C c = qbar c) → ∀ c, countFace (deposit C w qbar) c = qbar c) ∧
    (∀ α : A → ℚ, (∀ c, 0 < α c) → ∀ ws : List (ℚ × (A → ℚ)),
      (∀ d ∈ ws, d.2 = qbar) → 0 < reachedWeight ws → ∀ c,
        countFace (countRun α ws) c - qbar c =
          total α / (total α + reachedWeight ws) * (α c / total α - qbar c)) := by
  have hcontract : ∀ C : A → ℚ, 0 < total C → ∀ w : ℚ, 0 ≤ w → ∀ c,
      countFace (deposit C w qbar) c - qbar c =
        total C / (total C + w) * (countFace C c - qbar c) := by
    intro C hN w hw c
    have hstep := face_step hN hw hq c
    have hN' : 0 < total C + w := by linarith
    have e : countFace (deposit C w qbar) c - qbar c =
        (countFace (deposit C w qbar) c - countFace C c) + (countFace C c - qbar c) := by ring
    rw [e, hstep]
    field_simp
    ring
  refine ⟨hcontract, fun C hN w hw hfix c => ?_, fun α hα ws hws hS c => ?_⟩
  · have := hcontract C hN w hw c
    rw [hfix c, sub_self, mul_zero, sub_eq_zero] at this
    exact this
  · have hqs : ∀ d ∈ ws, ∑ c, d.2 c = 1 := fun d hd => by rw [hws d hd]; exact hq
    have hmean : reachedMean ws c = qbar c := by
      unfold reachedMean reachedWeight at *
      have hsum : ∀ l : List (ℚ × (A → ℚ)), (∀ d ∈ l, d.2 = qbar) →
          (l.map fun d => d.1 * d.2 c).sum = (l.map Prod.fst).sum * qbar c := by
        intro l hl
        induction l with
        | nil => simp
        | cons d l ih =>
          simp only [List.map_cons, List.sum_cons, add_mul]
          rw [hl d (by simp), ih (fun d' hd' => hl d' (List.mem_cons_of_mem _ hd'))]
      rw [hsum ws hws]
      field_simp
    rw [← hmean]
    exact (count_prior_decay hα ws hqs hS c).2

/-- [definition] **The Krichevsky–Trofimov prior** `α = 1/2` at every class: one per two. -/
def ktPrior : A → ℚ := fun _ => 1 / 2

/-- [definition] The unit-weight one-hot word of a target sequence. -/
def targetWord (ts : List A) : List (ℚ × (A → ℚ)) := ts.map fun t => (1, target t)

/-- [definition] **The Krichevsky–Trofimov probability** of a class seen `n_c` times in `n`
observations over an alphabet of `k` classes: `(n_c + 1/2)/(n + k/2)`. -/
def ktProb (nc n k : ℕ) : ℚ := (nc + 1 / 2) / (n + k / 2)

omit [Fintype A] in
theorem targetWord_deposits (ts : List A) (c : A) :
    ((targetWord ts).map fun d => d.1 * d.2 c).sum = ts.count c := by
  induction ts with
  | nil => simp [targetWord]
  | cons t ts ih =>
    simp only [targetWord, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, List.count_cons]
    by_cases h : c = t
    · subst h; simp [target]; ring
    · have h' : ¬ (t == c) = true := by simpa [beq_iff_eq] using Ne.symm h
      simp [target, Pi.single_eq_of_ne h, h']

theorem sum_count (ts : List A) : ∑ c, (ts.count c : ℚ) = ts.length := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.count_cons, List.length_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, Finset.sum_add_distrib, ih, beq_iff_eq]
    simp

/-- [proved-derived; formal-checked] **`count_face_eq_kt`: the count face at `α = 1/2` is the
Krichevsky–Trofimov estimate.** After a target word with counts `n_c` in `n` observations over
`|A|` classes, at unit weights: `C_c = n_c + 1/2`, `N = n + |A|/2`, and the face is KT's
probability `(n_c + 1/2)/(n + |A|/2)`, at every prefix. The receiving parametron's context-free
face is the online order-0 KT probability. -/
theorem count_face_eq_kt [Nonempty A] (ts : List A) (c : A) :
    countRun ktPrior (targetWord ts) c = ts.count c + 1 / 2 ∧
      total (countRun ktPrior (targetWord ts)) = ts.length + Fintype.card A / 2 ∧
      countFace (countRun ktPrior (targetWord ts)) c =
        ktProb (ts.count c) ts.length (Fintype.card A) := by
  have hC : ∀ c, countRun ktPrior (targetWord ts) c = ts.count c + 1 / 2 := fun c => by
    rw [countRun_apply, targetWord_deposits]
    simp [ktPrior]
    ring
  have hN : total (countRun ktPrior (targetWord ts)) = ts.length + Fintype.card A / 2 := by
    simp only [total, hC, Finset.sum_add_distrib, sum_count, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  refine ⟨hC c, hN, ?_⟩
  rw [countFace, hC c, hN, ktProb]

/-- [proved-derived; formal-checked] **The context-free fixture** (Decision 27): two classes
`a = 0`, `b = 1`, the prior `α = (1/2, 1/2)` and unit weights. After `a, a, b`: `C = (5/2, 3/2)`,
`N = 4`, `p = (5/8, 3/8)`; after the prefixes `a` and `a, a`: `(3/4, 1/4)` and `(5/6, 1/6)`; at
every class the face after `a, a, b` is KT's `(n_c + 1/2)/(3 + 1)`. Decided by `norm_num`. -/
theorem kt_fixture :
    countRun (ktPrior : Fin 2 → ℚ) (targetWord [0, 0, 1]) = ![5 / 2, 3 / 2] ∧
      total (countRun (ktPrior : Fin 2 → ℚ) (targetWord [0, 0, 1])) = 4 ∧
      countFace (countRun (ktPrior : Fin 2 → ℚ) (targetWord [0, 0, 1])) = ![5 / 8, 3 / 8] ∧
      countFace (countRun (ktPrior : Fin 2 → ℚ) (targetWord [0])) = ![3 / 4, 1 / 4] ∧
      countFace (countRun (ktPrior : Fin 2 → ℚ) (targetWord [0, 0])) = ![5 / 6, 1 / 6] ∧
      ∀ c : Fin 2, countFace (countRun (ktPrior : Fin 2 → ℚ) (targetWord [0, 0, 1])) c =
        ktProb ([0, 0, 1].count c) 3 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun c => by simpa using (count_face_eq_kt [0, 0, 1] c).2.2⟩
  · funext i
    fin_cases i <;> simp [countRun, targetWord, deposit, target, ktPrior] <;> norm_num
  · simp [total, countRun, targetWord, deposit, target, ktPrior, Pi.single_apply, Fin.sum_univ_two]
    norm_num
  all_goals
    funext i
    fin_cases i <;>
      simp [countFace, total, countRun, targetWord, deposit, target, ktPrior, Pi.single_apply,
        Fin.sum_univ_two] <;> norm_num

open Holonics.HNN.IndexedOpen (normalized normalized_div_rem population) in
/-- [proved-derived; formal-checked] **The KT masses as integers of half-units**
(`HNN/IndexedOpen`). The doubled masses `2C_c = 2n_c + 1` are natural numbers, and the count face
is `HNN/IndexedOpen.normalized` of that integer table at one phase: the exact ratio
`(2n_c + 1)/(2n + |A|)`, with its division and remainder (`normalized_div_rem`). The receiving
parametron can carry its storage as exact integers, with no lattice at all. -/
theorem kt_half_units_normalized [Nonempty A] (ts : List A) (c : A) :
    countFace (countRun ktPrior (targetWord ts)) c =
        normalized 1 (fun _ x => 2 * ts.count x + 1) 0 c ∧
      population 1 (fun _ (x : A) => 2 * ts.count x + 1) = 2 * ts.length + Fintype.card A ∧
      countFace (countRun ktPrior (targetWord ts)) c =
        (((2 * ts.count c + 1) / (2 * ts.length + Fintype.card A) : ℕ) : ℚ) +
          (((2 * ts.count c + 1) % (2 * ts.length + Fintype.card A) : ℕ) : ℚ) /
            ((2 * ts.length + Fintype.card A : ℕ) : ℚ) ∧
      (2 * ts.count c + 1) % (2 * ts.length + Fintype.card A) <
        2 * ts.length + Fintype.card A := by
  have hpop : population 1 (fun _ (x : A) => 2 * ts.count x + 1) =
      2 * ts.length + Fintype.card A := by
    have hq : ((population 1 (fun _ (x : A) => 2 * ts.count x + 1) : ℕ) : ℚ) =
        ((2 * ts.length + Fintype.card A : ℕ) : ℚ) := by
      simp only [population, Finset.range_one, Finset.sum_singleton]
      push_cast
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_count]
      simp
    exact_mod_cast hq
  have hpos : 0 < population 1 (fun _ (x : A) => 2 * ts.count x + 1) := by
    rw [hpop]
    have := Fintype.card_pos (α := A)
    omega
  have hface : countFace (countRun ktPrior (targetWord ts)) c =
      normalized 1 (fun _ x => 2 * ts.count x + 1) 0 c := by
    rw [Holonics.HNN.IndexedOpen.normalized_of_pos hpos, hpop, (count_face_eq_kt ts c).2.2, ktProb]
    push_cast
    field_simp
  obtain ⟨hdiv, hlt⟩ := normalized_div_rem hpos 0 c
  rw [hpop] at hdiv hlt
  exact ⟨hface, hpop, hface.trans hdiv, hlt⟩

end Run

/-! ## 3. Regions: the retained masses are future-sufficient -/

section Region

variable {A : Type*} [Fintype A] [DecidableEq A] {Reg : Type*} [DecidableEq Reg]

/-- [definition] **A region deposit**: a comparison `(r, w, t)` that reached region `r` deposits
`w·e_t` into that region's masses only. `Reg` is the receiver's declared region quotient; the
normal-law join (`count_face_solves_normal_law`) takes it finite. -/
def regionDeposit (C : Reg → A → ℚ) (d : Reg × ℚ × A) : Reg → A → ℚ :=
  Function.update C d.1 (deposit (C d.1) d.2.1 (target d.2.2))

/-- [definition] **A run of reached comparisons** `(region, weight, target)` over region masses. -/
def regionRun (C : Reg → A → ℚ) (word : List (Reg × ℚ × A)) : Reg → A → ℚ :=
  word.foldl regionDeposit C

omit [Fintype A] in
theorem regionRun_cons (C : Reg → A → ℚ) (d : Reg × ℚ × A) (word : List (Reg × ℚ × A)) :
    regionRun C (d :: word) = regionRun (regionDeposit C d) word := rfl

omit [Fintype A] in
theorem regionRun_append (C : Reg → A → ℚ) (u v : List (Reg × ℚ × A)) :
    regionRun C (u ++ v) = regionRun (regionRun C u) v := by
  simp [regionRun, List.foldl_append]

omit [Fintype A] in
theorem regionDeposit_apply (C : Reg → A → ℚ) (d : Reg × ℚ × A) (r : Reg) :
    regionDeposit C d r = if d.1 = r then deposit (C r) d.2.1 (target d.2.2) else C r := by
  unfold regionDeposit
  by_cases h : d.1 = r
  · subst h; simp
  · rw [Function.update_of_ne (Ne.symm h), if_neg h]

omit [Fintype A] in
/-- [proved-derived; formal-checked] The region masses are the prior plus the deposits that
reached that region: `C_(r,c) = α_(r,c) + Σ_(i : r_i = r) w_i e_(t_i)(c)`. -/
theorem regionRun_apply (C : Reg → A → ℚ) (word : List (Reg × ℚ × A)) (r : Reg) (c : A) :
    regionRun C word r c =
      C r c + (word.map fun d => if d.1 = r then d.2.1 * target d.2.2 c else 0).sum := by
  induction word generalizing C with
  | nil => simp [regionRun]
  | cons d word ih =>
    rw [regionRun_cons, ih, regionDeposit_apply]
    by_cases h : d.1 = r
    · simp [h, deposit]; ring
    · simp [h]

omit [Fintype A] in
/-- [proved-derived; formal-checked] **A region's masses are the count run of the comparisons that
reached it** (`regionRun_local`): the other regions' comparisons never touch them. -/
theorem regionRun_local (C : Reg → A → ℚ) (word : List (Reg × ℚ × A)) (r : Reg) :
    regionRun C word r =
      countRun (C r) ((word.filter fun d => d.1 = r).map fun d => (d.2.1, target d.2.2)) := by
  induction word generalizing C with
  | nil => rfl
  | cons d word ih =>
    rw [regionRun_cons, ih, regionDeposit_apply]
    by_cases h : d.1 = r
    · simp [h, countRun_cons]
    · simp [h]

omit [Fintype A] in
/-- [proved-derived; formal-checked] **The masses forget the order of the past**: permuted words
of reached comparisons give equal region masses. -/
theorem regionRun_perm (C : Reg → A → ℚ) {u₁ u₂ : List (Reg × ℚ × A)} (h : u₁.Perm u₂) :
    regionRun C u₁ = regionRun C u₂ := by
  funext r c
  rw [regionRun_apply, regionRun_apply, (h.map _).sum_eq]

open Holonics.Foundation.Standing (StandingLaw)
open Holonics.Foundation.Chronology (transportWord generatorEquivarianceExtendsToEveryTransportWord)
open Holonics.Transport.SourceMoment (appendLetter)

/-- [definition] **The region masses as a standing law.** Sources are past words of reached
comparisons, generators append one, receivers are (region, class) pairs reading the count face,
the retention is the region masses, and the reopening runs the future word on the masses alone. -/
def countStanding (α : Reg → A → ℚ) :
    StandingLaw (Reg × ℚ × A) (Reg × A) (List (Reg × ℚ × A)) (Reg → A → ℚ) ℚ where
  transport := appendLetter
  observe rc l := countFace (regionRun α l rc.1) rc.2
  retain := regionRun α
  reopen rc word C := countFace (transportWord (fun d C => regionDeposit C d) word C rc.1) rc.2
  sufficient rc word l := by
    rw [generatorEquivarianceExtendsToEveryTransportWord appendLetter
      (fun d C => regionDeposit C d) (regionRun α)
      (fun d l => by simp [appendLetter, regionRun, List.foldl_append]) word l]

/-- [proved-derived; formal-checked] **`count_future_sufficient`.** Two pasts `u₁, u₂` whose region
masses are equal:
* have equal successor masses after every future word `v` of reached comparisons;
* read equal faces at every region and class after it;
* agree on every future observation of the standing law `countStanding`
  (`StandingLaw.futureAgreement_of_retain_eq`);
* and a region's future needs only its own masses: equal masses at `r` give equal masses at `r`
  after every future word, whatever the other regions hold.

The receiving parametron's class masses are the whole retention of the region receiver: no
occurrence list is kept, and none is needed. -/
theorem count_future_sufficient (α : Reg → A → ℚ) {u₁ u₂ : List (Reg × ℚ × A)}
    (h : regionRun α u₁ = regionRun α u₂) :
    (∀ v, regionRun α (u₁ ++ v) = regionRun α (u₂ ++ v)) ∧
      (∀ v r c, countFace (regionRun α (u₁ ++ v) r) c = countFace (regionRun α (u₂ ++ v) r) c) ∧
      Holonics.Foundation.CausalRelevance.NonLinear.futureAgreement (countStanding α).observe
        (countStanding α).transport u₁ u₂ ∧
      ∀ (C₁ C₂ : Reg → A → ℚ) (r : Reg), C₁ r = C₂ r → ∀ v, regionRun C₁ v r = regionRun C₂ v r := by
  have hsucc : ∀ v, regionRun α (u₁ ++ v) = regionRun α (u₂ ++ v) := fun v => by
    rw [regionRun_append, regionRun_append, h]
  refine ⟨hsucc, fun v r c => by rw [hsucc v],
    (countStanding α).futureAgreement_of_retain_eq h, fun C₁ C₂ r hr v => ?_⟩
  rw [regionRun_local, regionRun_local, hr]

/-- [proved-derived; formal-checked] **The permutation fixture** (Decision 27): at one region, the
pasts `a, a, b` and `a, b, a` (`a = 0`, `b = 1`, unit weights, `α = (1/2, 1/2)`) are different
words with equal masses `(5/2, 3/2)`, so every future face agrees. -/
theorem past_permutation_fixture :
    ([((), 1, 0), ((), 1, 0), ((), 1, 1)] : List (Unit × ℚ × Fin 2)) ≠
        [((), 1, 0), ((), 1, 1), ((), 1, 0)] ∧
      regionRun (fun _ => (ktPrior : Fin 2 → ℚ)) [((), 1, 0), ((), 1, 0), ((), 1, 1)] =
        regionRun (fun _ => (ktPrior : Fin 2 → ℚ)) [((), 1, 0), ((), 1, 1), ((), 1, 0)] ∧
      regionRun (fun _ => (ktPrior : Fin 2 → ℚ)) [((), 1, 0), ((), 1, 1), ((), 1, 0)] () =
        ![5 / 2, 3 / 2] := by
  refine ⟨by simp, regionRun_perm _ (List.Perm.cons _ (List.Perm.swap _ _ [])), ?_⟩
  funext i
  fin_cases i <;>
    simp [regionRun, regionDeposit, deposit, target, ktPrior] <;> norm_num

open Holonics.HNN.Normal (Window windowGram windowCovector) in
/-- [definition] **The one-hot region window** of the normal law: each reached comparison's weight,
its region feature `e_r` and its target `e_t`. -/
def regionWindow (word : List (Reg × ℚ × A)) : Window ℚ Reg A :=
  word.map fun d => (d.2.1, Pi.single d.1 1, target d.2.2)

/-- [definition] The weight that reached region `r`, `S_r = Σ_(i : r_i = r) w_i`. -/
def regionWeight (word : List (Reg × ℚ × A)) (r : Reg) : ℚ :=
  (word.map fun d => if d.1 = r then d.2.1 else 0).sum

theorem total_regionRun (C : Reg → A → ℚ) (word : List (Reg × ℚ × A)) (r : Reg) :
    total (regionRun C word r) = total (C r) + regionWeight word r := by
  induction word generalizing C with
  | nil => simp [regionRun, regionWeight]
  | cons d word ih =>
    rw [regionRun_cons, ih, regionDeposit_apply]
    by_cases h : d.1 = r
    · simp only [h, if_true, total_deposit, target_sum, regionWeight, List.map_cons,
        List.sum_cons]
      ring
    · simp [h, regionWeight]

omit [Fintype A] in
theorem regionRun_pos {α : Reg → A → ℚ} (hα : ∀ r c, 0 < α r c) (word : List (Reg × ℚ × A))
    (hw : ∀ d ∈ word, 0 ≤ d.2.1) (r : Reg) (c : A) : 0 < regionRun α word r c := by
  rw [regionRun_local]
  refine countRun_pos (hα r) _ ?_ ?_ c
  · intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
    exact hw d' (List.mem_filter.mp hd').1
  · intro d hd c'
    obtain ⟨d', _, rfl⟩ := List.mem_map.mp hd
    exact target_nonneg _ _

open Holonics.HNN.Normal (windowGram windowCovector) in
/-- [proved-derived; formal-checked] **`count_face_solves_normal_law`: the count face is the normal
law's solved map at one-hot region features** (`HNN/Normal`). With region features `f = e_r`,
targets `q = e_t`, the prior Gram `H_0 = diag(A_r)` and the prior cross moment `B_0 = α` (so the
prior map is the prior face `α/A`):
* the window Gram `Σ w e_r e_rᵀ` is diagonal, `diag(S_r)`, and `H = H_0 + F = diag(N_r)`;
* the count face `W_(c,r) = p_(r,c)` solves `W H = B` with `B = B_0 + Σ w q e_rᵀ`;
* and it is the only map that does.

Sol's candidate (a), the general `B H⁻¹` read, is the count law at a certified region partition:
its Gram is diagonal and positive, and its solved map is the count face, a positive section
(`count_face_positive_section`). -/
theorem count_face_solves_normal_law [Fintype Reg] [Nonempty A] {α : Reg → A → ℚ}
    (hα : ∀ r c, 0 < α r c) (word : List (Reg × ℚ × A)) (hw : ∀ d ∈ word, 0 ≤ d.2.1) :
    windowGram (regionWindow word) = diagonal (regionWeight word) ∧
      diagonal (fun r => total (α r)) + windowGram (regionWindow word) =
        diagonal (fun r => total (regionRun α word r)) ∧
      ∀ W : Matrix A Reg ℚ,
        W * (diagonal (fun r => total (α r)) + windowGram (regionWindow word)) =
            Matrix.of (fun c r => α r c) + windowCovector (regionWindow word) ↔
          W = Matrix.of fun c r => countFace (regionRun α word r) c := by
  have hgram : windowGram (regionWindow word) = diagonal (regionWeight word) := by
    clear hw
    induction word with
    | nil => ext i j; simp [windowGram, regionWindow, regionWeight, diagonal_apply]
    | cons d word ih =>
      have e : windowGram (regionWindow (d :: word)) =
          d.2.1 • vecMulVec (Pi.single d.1 1) (Pi.single d.1 1) +
            windowGram (regionWindow word) := by
        simp [windowGram, regionWindow]
      rw [e, ih]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, diagonal_apply,
        regionWeight, List.map_cons, List.sum_cons, smul_eq_mul]
      by_cases hij : i = j
      · subst hij
        by_cases hi : d.1 = i
        · subst hi; simp
        · simp [Ne.symm hi, hi]
      · by_cases hi : i = d.1
        · subst hi
          have hj : j ≠ d.1 := fun hj => hij hj.symm
          simp [hj, hij]
        · simp [Pi.single_apply, hi, hij]
  have hcov : ∀ c r, windowCovector (regionWindow word) c r =
      (word.map fun d => if d.1 = r then d.2.1 * target d.2.2 c else 0).sum := by
    clear hw hgram
    induction word with
    | nil => intro c r; simp [windowCovector, regionWindow]
    | cons d word ih =>
      intro c r
      have e : windowCovector (regionWindow (d :: word)) =
          d.2.1 • vecMulVec (target d.2.2) (Pi.single d.1 1) +
            windowCovector (regionWindow word) := by
        simp [windowCovector, regionWindow]
      rw [e, Matrix.add_apply, ih c r]
      simp only [List.map_cons, List.sum_cons, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
      congr 1
      by_cases h : d.1 = r
      · subst h; simp
      · simp [Ne.symm h, h]
  have hH : diagonal (fun r => total (α r)) + windowGram (regionWindow word) =
      diagonal (fun r => total (regionRun α word r)) := by
    rw [hgram, diagonal_add]
    congr 1
    funext r
    rw [total_regionRun]
  refine ⟨hgram, hH, fun W => ?_⟩
  rw [hH]
  have hN : ∀ r, 0 < total (regionRun α word r) := fun r =>
    total_pos (regionRun_pos hα word hw r)
  constructor
  · intro h
    ext c r
    have := congrFun (congrFun h c) r
    rw [mul_diagonal, Matrix.add_apply, Matrix.of_apply, hcov] at this
    rw [Matrix.of_apply, countFace, regionRun_apply, ← this]
    field_simp [(hN r).ne']
  · rintro rfl
    ext c r
    rw [mul_diagonal, Matrix.add_apply, Matrix.of_apply, Matrix.of_apply, hcov, countFace,
      div_mul_cancel₀ _ (hN r).ne', regionRun_apply]

end Region

/-! ## 4. The grain: an integer exponent, decided by integer comparisons -/

section Grain

/-- [definition] **The grain exponent** `k = ⌊L log₂ x⌋`: the integer with
`2^k ≤ x^L < 2^(k+1)` (`grainExponent_spec`), Mathlib's `Int.log 2 (x^L)` on the rationals. -/
def grainExponent (L : ℕ) (x : ℚ) : ℤ := Int.log 2 (x ^ L)

/-- [definition] **The carry and phase class** of a grain exponent: `k = L n + j`, `0 ≤ j < L`,
`(n, j) = (k div L, k mod L)`. -/
def carryPhase (L : ℕ) (k : ℤ) : ℤ × ℤ := (k / L, k % L)

/-- [proved-derived; formal-checked] **The grain exponent is the unique integer of the power
bounds.** For rational `x > 0`, `grainExponent L x = k` exactly when `2^k ≤ x^L < 2^(k+1)`. -/
theorem grainExponent_spec {x : ℚ} (hx : 0 < x) (L : ℕ) (k : ℤ) :
    grainExponent L x = k ↔ (2 : ℚ) ^ k ≤ x ^ L ∧ x ^ L < 2 ^ (k + 1) := by
  have hy : 0 < x ^ L := pow_pos hx L
  have h1 := Int.zpow_le_iff_le_log (R := ℚ) (b := 2) (by norm_num) (x := k) hy
  have h2 := Int.lt_zpow_iff_log_lt (R := ℚ) (b := 2) (by norm_num) (x := k + 1) hy
  push_cast at h1 h2
  unfold grainExponent
  constructor
  · rintro rfl
    exact ⟨h1.mpr le_rfl, h2.mpr (by omega)⟩
  · rintro ⟨ha, hb⟩
    have := h1.mp ha
    have := h2.mp hb
    omega

/-- The power `2^k`, `k ∈ ℤ`, as a ratio of natural powers `2^(k⁺)/2^(k⁻)`. -/
theorem two_zpow_eq (k : ℤ) :
    (2 : ℚ) ^ k = ((2 ^ k.toNat : ℕ) : ℚ) / ((2 ^ (-k).toNat : ℕ) : ℚ) := by
  have hk : k = (k.toNat : ℤ) - ((-k).toNat : ℤ) := by omega
  conv_lhs => rw [hk]
  rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]
  push_cast
  rfl

/-- The lower bound `2^k ≤ a/b` is the natural-number comparison `2^(k⁺)·b ≤ 2^(k⁻)·a`. -/
theorem two_zpow_le_div_iff (k : ℤ) {a b : ℕ} (hb : 0 < b) :
    (2 : ℚ) ^ k ≤ (a : ℚ) / b ↔ 2 ^ k.toNat * b ≤ 2 ^ (-k).toNat * a := by
  rw [two_zpow_eq, div_le_div_iff₀ (by positivity) (by exact_mod_cast hb)]
  constructor
  · intro h
    have : ((2 ^ k.toNat * b : ℕ) : ℚ) ≤ ((2 ^ (-k).toNat * a : ℕ) : ℚ) := by
      push_cast at h ⊢; linarith
    exact_mod_cast this
  · intro h
    have : ((2 ^ k.toNat * b : ℕ) : ℚ) ≤ ((2 ^ (-k).toNat * a : ℕ) : ℚ) := by exact_mod_cast h
    push_cast at this ⊢; linarith

/-- The upper bound `a/b < 2^k` is the natural-number comparison `2^(k⁻)·a < 2^(k⁺)·b`. -/
theorem div_lt_two_zpow_iff (k : ℤ) {a b : ℕ} (hb : 0 < b) :
    (a : ℚ) / b < (2 : ℚ) ^ k ↔ 2 ^ (-k).toNat * a < 2 ^ k.toNat * b := by
  rw [two_zpow_eq, div_lt_div_iff₀ (by exact_mod_cast hb) (by positivity)]
  constructor
  · intro h
    have : ((2 ^ (-k).toNat * a : ℕ) : ℚ) < ((2 ^ k.toNat * b : ℕ) : ℚ) := by
      push_cast at h ⊢; linarith
    exact_mod_cast this
  · intro h
    have : ((2 ^ (-k).toNat * a : ℕ) : ℚ) < ((2 ^ k.toNat * b : ℕ) : ℚ) := by exact_mod_cast h
    push_cast at this ⊢; linarith

/-- [proved-derived; formal-checked] **`grain_log_iff_pow_bounds`.** For a positive rational
`x = a/b` (`a, b` positive naturals; every positive rational is its numerator over its
denominator) and every grain `L`:
* there is exactly one integer `k` with `2^k ≤ x^L < 2^(k+1)`, the grain exponent;
* `k` is the grain exponent exactly when the natural-number comparisons
  `2^(k⁺)·b^L ≤ 2^(k⁻)·a^L` and `2^((k+1)⁻)·a^L < 2^((k+1)⁺)·b^L` hold, `k⁺ = max k 0`,
  `k⁻ = max (−k) 0`, so a negative `k` enters through `2^(−k)` on the numerator's side.

The receiver reads the exponent of its face without a logarithm or a float: two integer
comparisons decide it. -/
theorem grain_log_iff_pow_bounds {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (L : ℕ) :
    (∃! k : ℤ, (2 : ℚ) ^ k ≤ ((a : ℚ) / b) ^ L ∧ ((a : ℚ) / b) ^ L < 2 ^ (k + 1)) ∧
      ∀ k : ℤ, grainExponent L ((a : ℚ) / b) = k ↔
        (2 ^ k.toNat * b ^ L ≤ 2 ^ (-k).toNat * a ^ L ∧
          2 ^ (-(k + 1)).toNat * a ^ L < 2 ^ (k + 1).toNat * b ^ L) := by
  have hx : 0 < (a : ℚ) / b := by positivity
  have hpow : ((a : ℚ) / b) ^ L = ((a ^ L : ℕ) : ℚ) / ((b ^ L : ℕ) : ℚ) := by
    rw [div_pow]; push_cast; rfl
  have hbL : 0 < b ^ L := pow_pos hb L
  refine ⟨⟨grainExponent L ((a : ℚ) / b), (grainExponent_spec hx L _).mp rfl,
    fun k hk => ((grainExponent_spec hx L k).mpr hk).symm⟩, fun k => ?_⟩
  rw [grainExponent_spec hx L k, hpow, two_zpow_le_div_iff k hbL, div_lt_two_zpow_iff (k + 1) hbL]

/-- [proved-derived; formal-checked] **`grain_face_residual`.** For rational `x > 0` and a grain
`L ≥ 1`, with `k` the grain exponent:
* `k/L ≤ log₂ x < (k+1)/L`: the unresolved fibre `log₂ x − k/L` lies in `[0, 1/L)`;
* the owner's grain read of `log₂ x` (`HNN/Ratio.grainRead`) is the carry and phase class
  `(k div L, k mod L)`, and so is its read of the scored exponent `k/L`.

The receiver's face `θ^k`, `θ^L = 2`, is the owner's carried power at that carry and phase: the
integer comparison decides the grain read of the logarithm. -/
theorem grain_face_residual {x : ℚ} (hx : 0 < x) {L : ℕ} (hL : 0 < L) :
    ((grainExponent L x : ℝ) / L ≤ Real.logb 2 (x : ℝ) ∧
        Real.logb 2 (x : ℝ) < ((grainExponent L x : ℝ) + 1) / L) ∧
      grainRead L (Real.logb 2 (x : ℝ)) = carryPhase L (grainExponent L x) ∧
      grainRead L ((grainExponent L x : ℝ) / L) = carryPhase L (grainExponent L x) := by
  set k := grainExponent L x with hkdef
  obtain ⟨hlo, hhi⟩ := (grainExponent_spec hx L k).mp rfl
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have h2R : (2 : ℝ) = ((2 : ℚ) : ℝ) := by norm_num
  have hloR : (2 : ℝ) ^ k ≤ (x : ℝ) ^ L := by
    rw [h2R, ← Rat.cast_zpow, ← Rat.cast_pow]
    exact Rat.cast_le.mpr hlo
  have hhiR : (x : ℝ) ^ L < (2 : ℝ) ^ (k + 1) := by
    rw [h2R, ← Rat.cast_zpow, ← Rat.cast_pow]
    exact Rat.cast_lt.mpr hhi
  have hlog : ∀ m : ℤ, Real.logb 2 ((2 : ℝ) ^ m) = m := fun m => by
    rw [← Real.rpow_intCast, Real.logb_rpow (by norm_num) (by norm_num)]
  have h1 : (k : ℝ) ≤ L * Real.logb 2 (x : ℝ) := by
    rw [← Real.logb_pow, ← hlog k]
    exact (Real.logb_le_logb (by norm_num) (by positivity) (by positivity)).mpr hloR
  have h2 : (L : ℝ) * Real.logb 2 (x : ℝ) < k + 1 := by
    rw [← Real.logb_pow]
    have := (Real.logb_lt_logb_iff (b := 2) (by norm_num) (by positivity) (by positivity)).mpr hhiR
    rw [hlog] at this
    exact_mod_cast this
  have hbounds : (k : ℝ) / L ≤ Real.logb 2 (x : ℝ) ∧ Real.logb 2 (x : ℝ) < ((k : ℝ) + 1) / L := by
    constructor
    · rw [div_le_iff₀ hLR]; linarith
    · rw [lt_div_iff₀ hLR]; linarith
  -- the carry and phase class of `k`
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  obtain ⟨e, hj0, hj1⟩ := (Int.ediv_emod_unique hLz).mp ⟨rfl, rfl⟩
  have hsplit : ((k / (L : ℤ) : ℤ) : ℝ) + ((k % (L : ℤ) : ℤ) : ℝ) / L = (k : ℝ) / L := by
    have eR : ((k % (L : ℤ) : ℤ) : ℝ) + (L : ℝ) * ((k / (L : ℤ) : ℤ) : ℝ) = k := by
      exact_mod_cast e
    field_simp
    linarith
  have hfib := (face_constant_on_fibre.{0, 0} (K := ℝ) hL 0).2.2.2.2.2.1
  have hread : ∀ f : ℝ, (k : ℝ) / L ≤ f → f < ((k : ℝ) + 1) / L →
      grainRead L f = carryPhase L k := by
    intro f hf1 hf2
    rw [carryPhase, hfib _ _ f hj0 hj1]
    constructor
    · rw [hsplit]; exact hf1
    · have : ((k / (L : ℤ) : ℤ) : ℝ) + (((k % (L : ℤ) : ℤ) : ℝ) + 1) / L =
          ((k : ℝ) + 1) / L := by
        rw [add_div, ← add_assoc, hsplit, add_div]
      rw [this]; exact hf2
  refine ⟨hbounds, hread _ hbounds.1 hbounds.2, hread _ le_rfl ?_⟩
  rw [div_lt_div_iff_of_pos_right hLR]
  linarith

variable {A : Type*} [Fintype A]

/-- [proved-derived; formal-checked] **The scored code length is within one grain of the face's**
(the owner's `face_code_length_within_grain`). For a positive rational face `p` (`Σ p = 1`) and a
grain `L ≥ 1`, the scored face with exponents `k_c/L` (`k_c` the grain exponent of `p_c`; the face
`θ^(k_c) / Σ_d θ^(k_d)`, `θ^L = 2`) codes every class within `1/L` bits of `−log₂ p_t`:
`|codeLength (k/L) t − (−log₂ p_t)| < 1/L`. -/
theorem grain_code_residual [Nonempty A] {p : A → ℚ} (hp : ∀ c, 0 < p c) (hsum : ∑ c, p c = 1)
    {L : ℕ} (hL : 0 < L) (t : A) :
    |codeLength (fun c => (grainExponent L (p c) : ℝ) / L) t - -Real.logb 2 (p t : ℝ)| < 1 / L := by
  set f : A → ℝ := fun c => Real.logb 2 (p c : ℝ)
  set ε : A → ℝ := fun c => f c - (grainExponent L (p c) : ℝ) / L
  have hε0 : ∀ c, 0 ≤ ε c := fun c => by
    have := (grain_face_residual (hp c) hL).1.1
    simp only [ε, f]; linarith
  have hε1 : ∀ c, ε c < 1 / L := fun c => by
    have := (grain_face_residual (hp c) hL).1.2
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL
    simp only [ε, f]
    rw [add_div] at this
    linarith
  have hcode := face_code_length_within_grain f ε hε0 hε1 t
  have hf : (fun c => f c - ε c) = fun c => (grainExponent L (p c) : ℝ) / L := by
    funext c; simp only [ε]; ring
  have hexact : codeLength f t = -Real.logb 2 (p t : ℝ) := by
    have hpos : ∀ c, (0 : ℝ) < p c := fun c => by exact_mod_cast hp c
    have hs : ∑ c, (2 : ℝ) ^ f c = 1 := by
      simp only [f, Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) (hpos _)]
      exact_mod_cast hsum
    simp only [codeLength, hs, Real.logb_one, add_zero, f]
  rw [hf, hexact] at hcode
  exact hcode

/-- [proved-derived; formal-checked] **The grain fixture** (Decision 27), at `L = 16`:
* `5/8` has grain exponent `−11`: `2^0·8^16 ≤ 2^11·5^16` and `2^10·5^16 < 2^0·8^16`;
* `3/8` has grain exponent `−23`: `2^0·8^16 ≤ 2^23·3^16` and `2^22·3^16 < 2^0·8^16`;
* their carry and phase classes are `(−1, 5)` and `(−2, 9)`: `−11 = 16·(−1) + 5`,
  `−23 = 16·(−2) + 9`.

All decided on the integers; so the owner's grain reads of the real logarithms are
`grainRead 16 (log₂(5/8)) = (−1, 5)` and `grainRead 16 (log₂(3/8)) = (−2, 9)`
(`grain_face_residual`), with no logarithm evaluated. -/
theorem grain_fixture :
    (2 ^ 0 * 8 ^ 16 ≤ 2 ^ 11 * 5 ^ 16 ∧ 2 ^ 10 * 5 ^ 16 < 2 ^ 0 * 8 ^ 16) ∧
      (2 ^ 0 * 8 ^ 16 ≤ 2 ^ 23 * 3 ^ 16 ∧ 2 ^ 22 * 3 ^ 16 < 2 ^ 0 * 8 ^ 16) ∧
      grainExponent 16 (5 / 8) = -11 ∧ grainExponent 16 (3 / 8) = -23 ∧
      carryPhase 16 (-11) = (-1, 5) ∧ carryPhase 16 (-23) = (-2, 9) ∧
      grainRead 16 (Real.logb 2 ((5 / 8 : ℚ) : ℝ)) = (-1, 5) ∧
      grainRead 16 (Real.logb 2 ((3 / 8 : ℚ) : ℝ)) = (-2, 9) := by
  have h5 : ((5 : ℕ) : ℚ) / ((8 : ℕ) : ℚ) = 5 / 8 := by norm_num
  have h3 : ((3 : ℕ) : ℚ) / ((8 : ℕ) : ℚ) = 3 / 8 := by norm_num
  have k5 : grainExponent 16 (5 / 8) = -11 := by
    rw [← h5, ((grain_log_iff_pow_bounds (by norm_num) (by norm_num) 16).2 (-11))]
    decide
  have k3 : grainExponent 16 (3 / 8) = -23 := by
    rw [← h3, ((grain_log_iff_pow_bounds (by norm_num) (by norm_num) 16).2 (-23))]
    decide
  have c5 : carryPhase 16 (-11) = (-1, 5) := by decide
  have c3 : carryPhase 16 (-23) = (-2, 9) := by decide
  refine ⟨by decide, by decide, k5, k3, c5, c3, ?_, ?_⟩
  · rw [(grain_face_residual (x := 5 / 8) (by norm_num) (L := 16) (by norm_num)).2.1, k5, c5]
  · rw [(grain_face_residual (x := 3 / 8) (by norm_num) (L := 16) (by norm_num)).2.1, k3, c3]

end Grain

/-! ## 5. The masses on Decision 22's carrier lattice -/

section Lattice

open Holonics.HNN.LatticeDeposit (Carried OnLattice run released carry release)

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- [definition] **The exact updates of a word of reached comparisons**, `Δ_i = w_i q_i`, as
`HNN/LatticeDeposit` carries them. -/
def reachedUpdates (ws : List (ℚ × (A → ℚ))) : List (A → ℚ) := ws.map fun d c => d.1 * d.2 c

omit [Fintype A] [DecidableEq A] in
theorem reachedUpdates_sum (ws : List (ℚ × (A → ℚ))) (c : A) :
    ((reachedUpdates ws).map (· c)).sum = (ws.map fun d => d.1 * d.2 c).sum := by
  simp [reachedUpdates, List.map_map, Function.comp_def]

omit [Fintype A] [DecidableEq A] in
/-- [proved-derived; formal-checked] **`count_lattice_accounting`.** Carried on the lattice
`2^(−L)ℤ` by Decision 22's budgeted carry from the prior `α` (`HNN/LatticeDeposit.run`), the
carried masses plus the carried remainder plus the released tails equal the exact masses
`α + Σ w q`, coordinatewise (`lattice_deposit_accounting`), and every carried mass is within one
lattice unit of the exact one since the region's founding (`within_one_unit_since_founding`). The
executed face reads the carried masses; any claim about the exact face uses this residual,
especially at a rare class. -/
theorem count_lattice_accounting (L : ℕ) (α : A → ℚ) (ws : List (ℚ × (A → ℚ))) (c : A) :
    (run (Carried.fresh (L := L) α) (reachedUpdates ws)).value c +
          (run (Carried.fresh (L := L) α) (reachedUpdates ws)).rem c +
          released (Carried.fresh (L := L) α) (reachedUpdates ws) c = countRun α ws c ∧
      |(run (Carried.fresh (L := L) α) (reachedUpdates ws)).value c - countRun α ws c| <
        Holonics.HNN.LatticeDeposit.unit L := by
  have h1 := Holonics.HNN.LatticeDeposit.lattice_deposit_accounting (L := L) α (reachedUpdates ws) c
  have h2 := Holonics.HNN.LatticeDeposit.within_one_unit_since_founding
    (Carried.fresh (L := L) α) (reachedUpdates ws) c
  rw [reachedUpdates_sum] at h1 h2
  rw [countRun_apply]
  simp only [Carried.fresh, Pi.zero_apply, add_zero] at h2
  exact ⟨by linarith, h2⟩

/-- A deposit whose update lies on the lattice, into a carrier with no remainder, carries exactly:
no remainder and no release. -/
theorem carry_exact {L : ℕ} {E : Type*} (s : Carried L E) (hs : ∀ i, s.rem i = 0) (Δ : E → ℚ)
    (hΔ : ∀ i, OnLattice L (Δ i)) :
    (∀ i, (carry s Δ).rem i = 0) ∧ ∀ i, release s Δ i = 0 := by
  by_cases h0 : Δ = 0
  · subst h0
    exact ⟨fun i => by rw [Holonics.HNN.LatticeDeposit.carry_zero]; exact hs i,
      fun i => Holonics.HNN.LatticeDeposit.release_zero s i⟩
  · set k := Holonics.HNN.LatticeDeposit.gammaLength (s.clock + 1)
    have hfine : ∀ i, OnLattice (L + k) (Δ i) := fun i => (hΔ i).mono (Nat.le_add_right L k)
    have hrem : ∀ i, Holonics.HNN.LatticeDeposit.rem (L + k) (Δ i) = 0 := fun i =>
      Holonics.HNN.LatticeDeposit.rem_of_onLattice (hfine i)
    have hpoint : ∀ i, Holonics.HNN.LatticeDeposit.fine L k (Δ i) = Δ i := fun i => by
      have := Holonics.HNN.LatticeDeposit.div_rem_spec (L + k) (Δ i)
      rw [hrem i, add_zero] at this
      unfold Holonics.HNN.LatticeDeposit.fine
      exact this.symm
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [carry, if_neg h0, Holonics.HNN.LatticeDeposit.step, hs i, add_zero]
      rw [hpoint i]
      exact Holonics.HNN.LatticeDeposit.rem_of_onLattice (hΔ i)
    · simp only [release, if_neg h0, hs i, add_zero]
      exact hrem i

theorem run_exact {L : ℕ} {E : Type*} (s : Carried L E) (hs : ∀ i, s.rem i = 0)
    (Δs : List (E → ℚ)) (hΔ : ∀ Δ ∈ Δs, ∀ i, OnLattice L (Δ i)) :
    (∀ i, (run s Δs).rem i = 0) ∧ ∀ i, released s Δs i = 0 := by
  induction Δs generalizing s with
  | nil => exact ⟨hs, fun i => rfl⟩
  | cons Δ Δs ih =>
    obtain ⟨hrem, hrel⟩ := carry_exact s hs Δ (hΔ Δ (by simp))
    obtain ⟨hrem', hrel'⟩ := ih (carry s Δ) hrem (fun Δ' h' => hΔ Δ' (List.mem_cons_of_mem _ h'))
    refine ⟨hrem', fun i => ?_⟩
    simp only [released, hrel i, hrel' i, add_zero]

omit [Fintype A] [DecidableEq A] in
/-- [proved-derived; formal-checked] **Updates on the lattice carry exactly.** If every reached
update `w q` lies on the lattice `2^(−L)ℤ`, the carried masses equal the exact ones, with no
remainder and no release: Decision 22's carry is the identity on lattice-valued storage. -/
theorem count_lattice_exact (L : ℕ) (α : A → ℚ) (ws : List (ℚ × (A → ℚ)))
    (hΔ : ∀ d ∈ ws, ∀ c, OnLattice L (d.1 * d.2 c)) (c : A) :
    (run (Carried.fresh (L := L) α) (reachedUpdates ws)).rem c = 0 ∧
      released (Carried.fresh (L := L) α) (reachedUpdates ws) c = 0 ∧
      (run (Carried.fresh (L := L) α) (reachedUpdates ws)).value c = countRun α ws c := by
  have hΔ' : ∀ Δ ∈ reachedUpdates ws, ∀ i, OnLattice L (Δ i) := by
    intro Δ hΔm i
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hΔm
    exact hΔ d hd i
  obtain ⟨hrem, hrel⟩ := run_exact (Carried.fresh (L := L) α) (fun _ => rfl) _ hΔ'
  have hacc := (count_lattice_accounting L α ws c).1
  rw [hrem c, hrel c] at hacc
  exact ⟨hrem c, hrel c, by linarith⟩

omit [Fintype A] in
/-- [proved-derived; formal-checked] **The KT masses run exactly on every lattice.** Unit-weight
one-hot updates are integers, on every lattice `2^(−L)ℤ`, so from the prior `1/2` the carried
masses are `n_c + 1/2` exactly, with no remainder and no release. -/
theorem kt_lattice_exact (L : ℕ) (ts : List A) (c : A) :
    (run (Carried.fresh (L := L) ktPrior) (reachedUpdates (targetWord ts))).value c =
        ts.count c + 1 / 2 ∧
      (run (Carried.fresh (L := L) ktPrior) (reachedUpdates (targetWord ts))).rem c = 0 ∧
      released (Carried.fresh (L := L) ktPrior) (reachedUpdates (targetWord ts)) c = 0 := by
  have hΔ : ∀ d ∈ targetWord ts, ∀ c, OnLattice L (d.1 * d.2 c) := by
    intro d hd c
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hd
    by_cases h : c = t
    · subst h
      refine ⟨2 ^ L, ?_⟩
      simp [target, Holonics.HNN.LatticeDeposit.unit]
    · refine ⟨0, ?_⟩
      simp [target, Pi.single_eq_of_ne h]
  obtain ⟨hrem, hrel, hval⟩ := count_lattice_exact L ktPrior (targetWord ts) hΔ c
  refine ⟨?_, hrem, hrel⟩
  rw [hval, countRun_apply, targetWord_deposits]
  simp [ktPrior]
  ring

end Lattice

/-! ## 6. The combined face: grain logits of the counts, corrected by the wave -/

section Combined

variable {A : Type*} [Fintype A] [DecidableEq A] {n : Type*} [Fintype n] [DecidableEq n]

/-- [definition] **The count face's grain logits** `k_c/L`, `k_c` the grain exponent of `p_c`. -/
def grainLogits (L : ℕ) (C : A → ℚ) : A → ℚ := fun c => (grainExponent L (countFace C c) : ℚ) / L

/-- [definition] **The wave's logits** `R P^τ v`: the receiving map `R` reading the ring's change
`v` at receiving phase `τ`. -/
def waveLogits (R : Matrix A n ℚ) (P : Matrix n n ℚ) (τ : ℕ) (v : n → ℚ) : A → ℚ :=
  R *ᵥ ((P ^ τ) *ᵥ v)

/-- [definition] **The combined face's logits**: the count face's grain logits plus the wave's,
`grain(log₂ p_r) + R P^τ v`. -/
def combinedLogits (L : ℕ) (C : A → ℚ) (R : Matrix A n ℚ) (P : Matrix n n ℚ) (τ : ℕ)
    (v : n → ℚ) : A → ℚ :=
  grainLogits L C + waveLogits R P τ v

omit [DecidableEq A] in
/-- [proved-derived; formal-checked] **`combined_face_pullback`.** With the transported wave
`u = P^τ v`:
* along `R + x δR` the combined logits move by `x δR u`: a line in `R`;
* that motion is the same at every count state `C'`: the count part carries no parameter pulled
  back through `R`;
* a covector `g` pairs with the motion as `⟨g, δR u⟩ = Σ_(c,j) (g uᵀ)_(c,j) δR_(c,j)`: the
  pullback to `R` is `g uᵀ`, the wave-only face's;
* and the anchor receives `(P^τ)ᵀ Rᵀ g`, as before (`HNN/Ratio.receivingPhase_pullback` in the
  realified chart).

So the counts do not enter the wave's covector's form; they enter only through the face at which
the ratio evaluates `g`. -/
theorem combined_face_pullback (L : ℕ) (C : A → ℚ) (R δR : Matrix A n ℚ) (P : Matrix n n ℚ)
    (τ : ℕ) (v : n → ℚ) (g : A → ℚ) (x : ℚ) :
    combinedLogits L C (R + x • δR) P τ v = combinedLogits L C R P τ v + x • waveLogits δR P τ v ∧
      (∀ C' : A → ℚ, combinedLogits L C' (R + x • δR) P τ v - combinedLogits L C' R P τ v =
        x • waveLogits δR P τ v) ∧
      g ⬝ᵥ waveLogits δR P τ v = ∑ c, ∑ j, vecMulVec g ((P ^ τ) *ᵥ v) c j * δR c j ∧
      g ⬝ᵥ waveLogits R P τ v = ((P ^ τ)ᵀ *ᵥ (Rᵀ *ᵥ g)) ⬝ᵥ v := by
  have hline : ∀ C' : A → ℚ, combinedLogits L C' (R + x • δR) P τ v =
      combinedLogits L C' R P τ v + x • waveLogits δR P τ v := fun C' => by
    simp only [combinedLogits, waveLogits, add_mulVec, smul_mulVec]
    abel
  refine ⟨hline C, fun C' => by rw [hline C', add_sub_cancel_left], ?_, ?_⟩
  · simp only [waveLogits]
    generalize (P ^ τ) *ᵥ v = u
    simp only [dotProduct, mulVec, vecMulVec_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp only [waveLogits]
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_mulVec, ← mulVec_transpose,
      dotProduct_comm]

/-- [proved-derived; formal-checked] **The code length's derivative along a logit line.** For
logits `f` (exponents of two) and a direction `d`, the code length `codeLength (f + x d) t` has
derivative `Σ_c (p̂_c − q_c) d_c` at `x = 0`, with `p̂_c = 2^(f_c) / Σ_e 2^(f_e)` the face and
`q = e_t`: in bits per unit of logit, the covector `p̂ − q`. -/
theorem hasDerivAt_codeLength_line [Nonempty A] (f d : A → ℝ) (t : A) :
    HasDerivAt (fun x : ℝ => codeLength (fun c => f c + x * d c) t)
      (∑ c, ((2 : ℝ) ^ f c / ∑ e, (2 : ℝ) ^ f e - (Pi.single t 1 : A → ℝ) c) * d c) 0 := by
  have hterm : ∀ c ∈ (Finset.univ : Finset A),
      HasDerivAt (fun x : ℝ => (2 : ℝ) ^ (f c + x * d c))
        (Real.log 2 * d c * (2 : ℝ) ^ (f c + 0 * d c)) 0 := by
    intro c _
    have hlin : HasDerivAt (fun x : ℝ => f c + x * d c) (d c) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d c)).const_add (f c)
    exact hlin.const_rpow (by norm_num)
  have hsum := HasDerivAt.fun_sum hterm
  have hZ : 0 < ∑ c, (2 : ℝ) ^ f c :=
    Finset.sum_pos (fun c _ => by positivity) Finset.univ_nonempty
  have hZ0 : (∑ c, (2 : ℝ) ^ (f c + 0 * d c)) ≠ 0 := by simpa using hZ.ne'
  have hlog := (hsum.log hZ0).div_const (Real.log 2)
  have hlint : HasDerivAt (fun x : ℝ => f t + x * d t) (d t) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d t)).const_add (f t)
  have htgt : HasDerivAt (fun x : ℝ => -(f t + x * d t)) (-(d t)) 0 := hlint.neg
  have htot := htgt.add hlog
  have hfun : (fun x : ℝ => codeLength (fun c => f c + x * d c) t) =
      fun x => -(f t + x * d t) +
        Real.log (∑ c, (2 : ℝ) ^ (f c + x * d c)) / Real.log 2 := by
    funext x
    simp only [codeLength, Real.logb]
  rw [hfun]
  refine htot.congr_deriv ?_
  have hl2 : Real.log 2 ≠ 0 := by positivity
  simp only [zero_mul, add_zero]
  have hsingle : ∑ c, (Pi.single t (1 : ℝ) : A → ℝ) c * d c = d t := by
    simp [Pi.single_apply]
  have hrhs : ∑ c, ((2 : ℝ) ^ f c / ∑ e, (2 : ℝ) ^ f e - (Pi.single t 1 : A → ℝ) c) * d c =
      (∑ c, (2 : ℝ) ^ f c * d c) / ∑ e, (2 : ℝ) ^ f e - d t := by
    simp only [sub_mul, Finset.sum_sub_distrib, hsingle, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hlhs : ∑ c, Real.log 2 * d c * (2 : ℝ) ^ f c = Real.log 2 * ∑ c, (2 : ℝ) ^ f c * d c := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hrhs, hlhs]
  field_simp
  ring

/-- [proved-derived; formal-checked] **`combined_code_pullback`.** Along `R + x δR` the real code
length of the combined logits `ℓ` moves, to first order, by
`Σ_(c,j) ((p̂_c − q_c) u_j) δR_(c,j)`, with `u = P^τ v`, `p̂` the combined face and `q = e_t`: the
covector `p̂ − q` pulled back to `R` as `(p̂ − q) uᵀ`, the wave-only face's form. The count logits
are constant along the line (`combined_face_pullback`); they set only the face `p̂`. -/
theorem combined_code_pullback [Nonempty A] (L : ℕ) (C : A → ℚ) (R δR : Matrix A n ℚ)
    (P : Matrix n n ℚ) (τ : ℕ) (v : n → ℚ) (t : A) :
    HasDerivAt (fun x : ℝ => codeLength
        (fun c => (combinedLogits L C R P τ v c : ℝ) + x * (waveLogits δR P τ v c : ℝ)) t)
      (∑ c, ∑ j, (((2 : ℝ) ^ (combinedLogits L C R P τ v c : ℝ) /
          ∑ e, (2 : ℝ) ^ (combinedLogits L C R P τ v e : ℝ) - (Pi.single t 1 : A → ℝ) c) *
            (((P ^ τ) *ᵥ v) j : ℝ)) * (δR c j : ℝ)) 0 := by
  refine (hasDerivAt_codeLength_line _ _ t).congr_deriv ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [waveLogits, mulVec, dotProduct]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Combined

section Audit

#print axioms target_sum
#print axioms total_deposit
#print axioms countFace_sum
#print axioms face_step
#print axioms count_step_mass
#print axioms count_step_normalized
#print axioms count_step_covector
#print axioms count_face_positive_section
#print axioms countRun_apply
#print axioms total_countRun
#print axioms countRun_pos
#print axioms count_prior_decay
#print axioms context_free_fixed_face
#print axioms count_face_eq_kt
#print axioms kt_fixture
#print axioms kt_half_units_normalized
#print axioms regionRun_apply
#print axioms regionRun_local
#print axioms regionRun_perm
#print axioms countStanding
#print axioms count_future_sufficient
#print axioms past_permutation_fixture
#print axioms regionRun_append
#print axioms total_regionRun
#print axioms regionRun_pos
#print axioms count_face_solves_normal_law
#print axioms grainExponent_spec
#print axioms two_zpow_eq
#print axioms two_zpow_le_div_iff
#print axioms div_lt_two_zpow_iff
#print axioms grain_log_iff_pow_bounds
#print axioms grain_face_residual
#print axioms grain_code_residual
#print axioms grain_fixture
#print axioms count_lattice_accounting
#print axioms carry_exact
#print axioms run_exact
#print axioms count_lattice_exact
#print axioms kt_lattice_exact
#print axioms combined_face_pullback
#print axioms hasDerivAt_codeLength_line
#print axioms combined_code_pullback

end Audit

end Holonics.HNN.RegionCounts
