import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.Field.Basic

/-!
# HNN.ReceivingPrior: the receiving map's prior Gram is the anchors' unit

[proved-derived; formal-checked] What the receiving map's prior Gram `H₀ = s I` does in its normal
law (`hnn::constitution::NormalLaw::with_prior`, `NormalLaw::prepare`,
`Constitution::deposited`). The record
`research/records/2026-10-02_THE_RECEIVING_PRIOR_IS_THE_ANCHORS_UNIT_AND_THE_CAP_IS_THE_SAME_CONSTANT.md`
reads it on the code and on campaign 1's anchors.

```text
unit        H = s I + Σ w f fᵀ ,  f = c f′ ,  x = c x′ ,  s = c²   ⇒   ⟨H⁻¹ f, x⟩ = ⟨H′⁻¹ f′, x′⟩ ,  H′ = I + Σ w f′ f′ᵀ
opening     H′ = s I + z zᵀ                                       ⇒   ⟨H′⁻¹ z, z⟩ = |z|²/(s + |z|²)
one cap     reads ∝ 1/s ,  η = min(a/C, 1/max(osc, 1))             ⇒   η D = D₁ min(a₁/C₁, 1/max(osc₁, s))
located     a = Σ_t ⟨g_t, W_t z_t⟩ ,  V = ln 2 Σ_t Var_p(W_t z_t)     ⇒   s ↦ s/(1 + a/V) ;  at the opening s = V₀/a₀
```

1. **The prior's scale is the anchors' unit** (`unit_step_read_prior_scale`). The unit step
   `D = Σ_t w_t g_t (H⁻¹ f_t)ᵀ` at the prior `c² I` on features `c f_t`, read at `c x`, equals the
   unit step at the prior `I` on the features `f_t`, read at `x`. Every quantity the certificate
   reads (the alignment `a`, the moves `b`, the curvature `C` and the oscillation `osc` along the
   unit step `Δ_t = D f_t`) is such a read, so the certified step is the same: a prior `s I` is the
   unit prior with the anchors measured in units of `√s`. Nothing but the anchors' amplitude unit
   can fix `s`.
2. **The opening outweighs a reading exactly when the reading is below the prior**
   (`first_reach`, `first_read_share`, `opening_outweighs_iff`). One reading `z` on the prior
   `s I` reaches `H′⁻¹ z = z/(s + |z|²)`, so the first deposit corrects that reading's own logits by
   the fraction `|z|²/(s + |z|²)` of its unit-prior-free step, and the opening keeps the share
   `s/(s + |z|²)`, at least one half exactly when `|z|² ≤ s`.
3. **The cap and the prior are one constant** (`cap_and_prior_one_constant`). Where the anchors'
   Gram is negligible against the prior, the unit step and every read along it scale as `1/s`
   (`a`, `osc` as `1/s`, `C` as `1/s²`). The certified step `η = min(a/C, 1/max(osc, 1))` (the
   curvature's and the unit step's caps, before the dyadic floor) then moves the map by
   `D₁ min(a₁/C₁, 1/max(osc₁, s))`: `s` enters only as the floor of the oscillation cap.
4. **The readings locate the prior** (`prequential_pairs`, `fisher_trace`, `newton_point`,
   `variance_smul`; the record
   `research/records/2026-10-02_THE_READINGS_LOCATE_THE_RECEIVING_PRIOR_BY_THE_PREQUENTIAL_CERTIFICATE.md`).
   Each reading meets the map built from the readings before it. Where the map is `1/s` times its
   unit, scaling the prior scales the map inversely, and the prequential code's Newton point in that
   scale is `φ = 1 + a/V`, read from the certificate's alignment and curvature on readings before
   their deposit. At the opening the alignment is the covectors' signal less their self-energy
   (the ordered pairs), whose chance level is the class Fisher trace `1 − Σ p²`, and the located
   prior `V₀/a₀` scales with the anchors' energy, as the prior's unit requires.
-/

namespace Holonics.HNN.ReceivingPrior

open Matrix

variable {K : Type*} [Field K]
variable {m n T : Type*} [Fintype m] [Fintype n] [DecidableEq n] [Fintype T]

/-- A nonzero scalar's inverse distributes over the nonsingular inverse, whether or not the matrix
is invertible (both sides are zero when it is not). -/
theorem inv_smul_of_ne_zero (k : K) (hk : k ≠ 0) (A : Matrix n n K) :
    (k • A)⁻¹ = k⁻¹ • A⁻¹ := by
  by_cases h : IsUnit A.det
  · simpa [Units.smul_def] using Matrix.inv_smul' A (Units.mk0 k hk) h
  · have h' : ¬IsUnit (k • A).det := by
      rw [det_smul]
      intro hu
      apply h
      exact (IsUnit.mul_iff.mp hu).2
    rw [nonsing_inv_apply_not_isUnit _ h, nonsing_inv_apply_not_isUnit _ h', smul_zero]

omit [Fintype m] [Fintype n] [DecidableEq n] in
/-- The Gram of rescaled features is the rescaled Gram. -/
theorem gram_scale (c : K) (w : T → K) (f : T → n → K) :
    ∑ u, w u • vecMulVec (c • f u) (c • f u) = (c ^ 2) • ∑ u, w u • vecMulVec (f u) (f u) := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  ext i j
  simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype m] in
/-- [proved-derived; formal-checked] **The prior's scale is the anchors' unit.** The unit step at
the prior `c² I` on features `c f_t`, read at `c x`, is the unit step at the unit prior on the
features `f_t`, read at `x`. -/
theorem unit_step_read_prior_scale (c : K) (hc : c ≠ 0) (w : T → K) (g : T → m → K)
    (f : T → n → K) (x : n → K) :
    ∑ t, (w t * (((c ^ 2 • (1 : Matrix n n K) + ∑ u, w u • vecMulVec (c • f u) (c • f u))⁻¹
        *ᵥ (c • f t)) ⬝ᵥ (c • x))) • g t =
      ∑ t, (w t * ((((1 : Matrix n n K) + ∑ u, w u • vecMulVec (f u) (f u))⁻¹ *ᵥ f t) ⬝ᵥ x))
        • g t := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  rw [gram_scale, ← smul_add, inv_smul_of_ne_zero _ hc2]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 2
  simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  field_simp

omit [DecidableEq n] in
/-- A rank-one square of a vector reads that vector by its energy. -/
theorem vecMulVec_self_mulVec (z : n → K) : vecMulVec z z *ᵥ z = (z ⬝ᵥ z) • z := by
  rw [vecMulVec_mulVec]
  ext i
  simp [mul_comm]

variable {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]

omit [DecidableEq n] in
/-- The prior plus one reading is a positive energy over the reading. -/
theorem prior_add_energy_pos (s : L) (hs : 0 < s) (z : n → L) : 0 < s + z ⬝ᵥ z := by
  have : 0 ≤ z ⬝ᵥ z := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (z i)
  linarith

/-- [proved-derived; formal-checked] **The first reach on the prior `s I`** (Sherman–Morrison at
one reading): `(s I + z zᵀ)⁻¹ z = z/(s + |z|²)`. -/
theorem first_reach (s : L) (hs : 0 < s) (z : n → L) :
    (s • (1 : Matrix n n L) + vecMulVec z z)⁻¹ *ᵥ z = (s + z ⬝ᵥ z)⁻¹ • z := by
  have hq := prior_add_energy_pos s hs z
  set e := z ⬝ᵥ z with he
  have hsq : vecMulVec z z * vecMulVec z z = e • vecMulVec z z := by
    rw [vecMulVec_mul_vecMulVec, he]
    ext i j
    simp only [vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hs' : s ≠ 0 := hs.ne'
  have hq' : s + e ≠ 0 := hq.ne'
  -- The Sherman–Morrison inverse.
  have hinv : (s • (1 : Matrix n n L) + vecMulVec z z)⁻¹ =
      s⁻¹ • ((1 : Matrix n n L) - (s + e)⁻¹ • vecMulVec z z) := by
    apply inv_eq_left_inv
    simp only [Matrix.smul_mul, sub_mul, Matrix.mul_add, Matrix.mul_smul, one_mul, Matrix.mul_one,
      hsq, smul_smul]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    field_simp
    ring
  rw [hinv, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    vecMulVec_self_mulVec, ← he, smul_smul]
  ext i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

/-- [proved-derived; formal-checked] **The first deposit's own correction.** At one reading `z`
on the prior `s I`, the reach read at the reading is `|z|²/(s + |z|²)`. -/
theorem first_read_share (s : L) (hs : 0 < s) (z : n → L) :
    ((s • (1 : Matrix n n L) + vecMulVec z z)⁻¹ *ᵥ z) ⬝ᵥ z = (z ⬝ᵥ z) / (s + z ⬝ᵥ z) := by
  rw [first_reach s hs, smul_dotProduct, smul_eq_mul, div_eq_inv_mul]

/-- [proved-derived; formal-checked] **The opening outweighs a reading exactly when the reading is
below the prior**: its share `s/(s + |z|²)` is at least one half iff `|z|² ≤ s`. -/
theorem opening_outweighs_iff (s e : L) (hs : 0 < s) (he : 0 ≤ e) :
    1 / 2 ≤ s / (s + e) ↔ e ≤ s := by
  have hq : 0 < s + e := by linarith
  rw [le_div_iff₀ hq]
  constructor <;> intro h <;> linarith

/-- [proved-derived; formal-checked] **The cap and the prior are one constant.** If the reads
scale as `1/s` (alignment `a₁/s`, oscillation `o₁/s`) and the curvature as `1/s²`, the step
`min(a/C, 1/max(osc, 1))` times the unit step `D₁/s` is `D₁ min(a₁/C₁, 1/max(o₁, s))`. -/
theorem cap_and_prior_one_constant (s a C o : L) (hs : 0 < s) (hC : 0 < C) :
    min ((a / s) / (C / s ^ 2)) (1 / max (o / s) 1) / s = min (a / C) (1 / max o s) := by
  rw [← min_div_div_right hs.le]
  have hs' : s ≠ 0 := hs.ne'
  have hmax : max (o / s) 1 * s = max o s := by
    rw [max_mul_of_nonneg _ _ hs.le, div_mul_cancel₀ _ hs', one_mul]
  have hm : 0 < max o s := lt_max_of_lt_right hs
  congr 1
  · field_simp
  · rw [div_div, hmax]

open Finset

/-- [proved-derived; formal-checked] **The prequential pairs.** Reading `t` meets the map built from
the readings before it, so its first-order gain pairs it with every earlier reading once. For a
symmetric pairing `k`, twice the sum over the ordered pairs `u < t` is the whole pairing less its
diagonal: `2 Σ_(u<t) k(u, t) = Σ_(u,t) k(u, t) − Σ_t k(t, t)`. With
`k(u, t) = κ ⟨g_u, g_t⟩⟨z_u, z_t⟩` the whole pairing is `κ‖Σ g zᵀ‖²` and the diagonal each
reading's own `κ|g_t|²|z_t|²`: the opening's prequential alignment is the covectors' signal less
their self-energy. -/
theorem prequential_pairs {N : ℕ} {K : Type*} [CommRing K] (k : Fin N → Fin N → K)
    (hk : ∀ u t, k u t = k t u) :
    2 * ∑ t, ∑ u ∈ univ.filter (· < t), k u t = ∑ t, ∑ u, k u t - ∑ t, k t t := by
  have hsplit : ∀ t, ∑ u, k u t = ∑ u ∈ univ.filter (· < t), k u t + k t t
      + ∑ u ∈ univ.filter (t < ·), k u t := by
    intro t
    rw [← sum_filter_add_sum_filter_not univ (· < t)]
    rw [← sum_filter_add_sum_filter_not (univ.filter fun u => ¬ u < t) (t < ·)]
    have h1 : (univ.filter fun u => ¬ u < t).filter (fun u => ¬ t < u) = {t} := by
      ext u; simp only [mem_filter, mem_univ, true_and, mem_singleton, not_lt]
      constructor
      · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
      · rintro rfl; exact ⟨le_rfl, le_rfl⟩
    have h2 : (univ.filter fun u => ¬ u < t).filter (fun u => t < u) = univ.filter (t < ·) := by
      ext u; simp only [mem_filter, mem_univ, true_and, not_lt]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨h.le, h⟩
    rw [h1, h2, sum_singleton]; ring
  have hswap : ∑ t, ∑ u ∈ univ.filter (t < ·), k u t = ∑ t, ∑ u ∈ univ.filter (· < t), k u t := by
    rw [sum_comm' (t' := univ) (s' := fun u => univ.filter (· < u))]
    · refine sum_congr rfl fun u _ => sum_congr rfl fun t _ => hk u t
    · intro t u; simp
  rw [sum_congr rfl fun t _ => hsplit t, sum_add_distrib, sum_add_distrib, hswap]
  ring

omit [LinearOrder L] [IsStrictOrderedRing L] in
/-- [proved-derived; formal-checked] **The self-energy's level is the class Fisher trace.** Under
the face's own masses `p` (`Σ p = 1`), the expected energy of the covector `q − p`, `q` the target's
indicator, is `Σ_c p_c |e_c − p|² = 1 − Σ p²`, the trace of `diag p − p pᵀ`. -/
theorem fisher_trace {C : Type*} [Fintype C] [DecidableEq C] (p : C → L) (hp : ∑ c, p c = 1) :
    ∑ c, p c * ∑ j, (Pi.single (M := fun _ => L) c 1 j - p j) ^ 2 = 1 - ∑ j, p j ^ 2 := by
  have h : ∀ c, ∑ j, (Pi.single (M := fun _ => L) c 1 j - p j) ^ 2 = 1 - 2 * p c + ∑ j, p j ^ 2 := by
    intro c
    have : ∀ j, (Pi.single (M := fun _ => L) c 1 j - p j) ^ 2
        = Pi.single (M := fun _ => L) c 1 j - 2 * (Pi.single (M := fun _ => L) c 1 j * p j) + p j ^ 2 := by
      intro j
      by_cases hj : j = c
      · subst hj; simp; ring
      · simp [hj]
    simp only [this, sum_add_distrib, sum_sub_distrib, ← mul_sum]
    simp [Pi.single_apply]
  simp only [h, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, ← sum_mul, hp, mul_one]
  have : ∑ c, p c * (2 * p c) = 2 * ∑ j, p j ^ 2 := by
    rw [mul_sum]; exact sum_congr rfl fun c _ => by ring
  rw [this]; ring

/-- [proved-derived; formal-checked] **The Newton point of the scaled map.** Scaling the map by `φ`
moves the prequential code, to second order, by `−φ a + φ² V/2` (`a` the prequential alignment,
`V` its curvature); for `V > 0` its least value is at `φ = a/V`. -/
theorem newton_point (a V φ : L) (hV : 0 < V) :
    -(a / V) * a + (a / V) ^ 2 * V / 2 ≤ -φ * a + φ ^ 2 * V / 2 := by
  have h : 0 ≤ (φ * V - a) ^ 2 / V := div_nonneg (sq_nonneg _) hV.le
  have hV' : V ≠ 0 := hV.ne'
  have e : -φ * a + φ ^ 2 * V / 2 - (-(a / V) * a + (a / V) ^ 2 * V / 2) = (φ * V - a) ^ 2 / V / 2 := by
    field_simp; ring
  linarith [e, h]

omit [LinearOrder L] [IsStrictOrderedRing L] in
/-- The variance of a move `x` under the masses `p` (`Var_p`, unnormalized when `Σ p ≠ 1`). -/
def variance {C : Type*} [Fintype C] (p : C → L) (x : C → L) : L :=
  ∑ c, p c * x c ^ 2 - (∑ c, p c * x c) ^ 2

omit [LinearOrder L] [IsStrictOrderedRing L] in
/-- [proved-derived; formal-checked] A move scaled by `k` has `k²` times the variance. With
`z ↦ c z` the opening's map `M ↦ c M`, so `M z ↦ c² M z`: the curvature `Σ Var_p(M z)` scales by
`c⁴`, the alignment `Σ ⟨g, M z⟩` by `c²`, and the located prior `V/a` by `c²`, as the prior's unit
(`unit_step_read_prior_scale`) requires. -/
theorem variance_smul {C : Type*} [Fintype C] (p : C → L) (x : C → L) (k : L) :
    variance p (fun c => k * x c) = k ^ 2 * variance p x := by
  unfold variance
  have h1 : ∑ c, p c * (k * x c) ^ 2 = k ^ 2 * ∑ c, p c * x c ^ 2 := by
    rw [mul_sum]; exact sum_congr rfl fun c _ => by ring
  have h2 : ∑ c, p c * (k * x c) = k * ∑ c, p c * x c := by
    rw [mul_sum]; exact sum_congr rfl fun c _ => by ring
  rw [h1, h2]; ring

end Holonics.HNN.ReceivingPrior
