import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.Field.Basic
import Holonics.HNN.Ratio.Certificate

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
5. **The second order, certified** (`prequential_code_le`, `prequential_newton_decrease`). Along
   a map scaled by `φ`, each reading's code is bounded by the receiving certificate's own
   quadratic (`HNN/Ratio/Certificate.codeLength_add_le`); summed, the prequential code is at most
   the face's less `φ a` plus `φ² (ln 2/2) 2^ω Σ_t Var_(p_t)(M_t)`, and at the bound's Newton point
   it falls by at least `a²/(4K)`. The map is held as `φ M_t`: that the executed map is `1/s`
   times its unit is the prior-dominated reading of the record, not a theorem here.
6. **What the `1/s` reading drops** (`prior_resolvent`, `eigen_reach`, `eigen_departure`,
   `departure_le`, `campaign_one_departure`). The solved chart's resolvent is
   `(s I + G)⁻¹ = s⁻¹ (I − G (s I + G)⁻¹)`. Along a direction where the readings' Gram is `g`, the
   reach is `1/(s + g)`, so the `1/s` map loses the fraction `g/(s + g)` there, at most
   `λ/(s + λ)` for `0 ≤ g ≤ λ`. On campaign 1 (`λ_max(F) < 8599330/2^24`) at `s = 2` the loss is
   below `8599330/42153762`, below a quarter. This bounds the exact solve's part of the reading;
   the certified step `η` and the lattice's rounding are not in it.
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

section Prequential

open Holonics.HNN.Ratio Holonics.HNN.Ratio.Certificate

variable {ι T : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype T]

/-- [proved-derived; formal-checked] **The prequential code along a scaled map.** Each reading `t`
meets the map's move `φ M_t` on its face `f_t` (masses `p_t = 2^(f_t)/Σ 2^(f_t)`), its classes
differing pairwise by at most `ω`. Summed over the readings, the code is at most the face's code
less `φ a`, with `a = Σ_t ⟨e_(target t) − p_t, M_t⟩` the prequential alignment, plus
`φ² (ln 2/2) 2^ω Σ_t Var_(p_t)(M_t)`. This is `HNN/Ratio/Certificate.codeLength_add_le` summed. -/
theorem prequential_code_le (f M p : T → ι → ℝ)
    (hp : ∀ t c, p t c = (2 : ℝ) ^ f t c / ∑ d, (2 : ℝ) ^ f t d) (target : T → ι) (φ ω : ℝ)
    (hosc : ∀ t c d, φ * M t c - φ * M t d ≤ ω) :
    ∑ t, codeLength (fun c => f t c + φ * M t c) (target t) ≤
      ∑ t, codeLength (f t) (target t)
        - φ * ∑ t, ∑ c, ((Pi.single (target t) (1 : ℝ) : ι → ℝ) c - p t c) * M t c
        + φ ^ 2 * (Real.log 2 / 2 * (2 : ℝ) ^ ω * ∑ t, faceVariance (p t) (M t)) := by
  have h : ∀ t, codeLength (fun c => f t c + φ * M t c) (target t) ≤ codeLength (f t) (target t)
      - φ * ∑ c, ((Pi.single (target t) (1 : ℝ) : ι → ℝ) c - p t c) * M t c
      + φ ^ 2 * (Real.log 2 / 2 * (2 : ℝ) ^ ω * faceVariance (p t) (M t)) := by
    intro t
    have := codeLength_add_le (f t) (fun c => φ * M t c) (p t) (hp t) (hosc t) (target t)
    rw [faceVariance_smul] at this
    have e : ∑ c, (p t c - (Pi.single (target t) (1 : ℝ) : ι → ℝ) c) * (φ * M t c) =
        -(φ * ∑ c, ((Pi.single (target t) (1 : ℝ) : ι → ℝ) c - p t c) * M t c) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [e] at this
    linarith
  calc _ ≤ ∑ t, (codeLength (f t) (target t)
        - φ * ∑ c, ((Pi.single (target t) (1 : ℝ) : ι → ℝ) c - p t c) * M t c
        + φ ^ 2 * (Real.log 2 / 2 * (2 : ℝ) ^ ω * faceVariance (p t) (M t))) :=
        Finset.sum_le_sum fun t _ => h t
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum]

/-- [proved-derived; formal-checked] **The certified decrease at the bound's Newton point.** If the
code along the scaled map is at most `L₀ − φ a + φ² K`, `K > 0`, then at `φ = a/(2K)` it is at
most `L₀ − a²/(4K)`. -/
theorem prequential_newton_decrease (L0 a K φ : ℝ) (hK : 0 < K) (hφ : φ = a / (2 * K))
    {L : ℝ} (hL : L ≤ L0 - φ * a + φ ^ 2 * K) : L ≤ L0 - a ^ 2 / (4 * K) := by
  subst hφ
  have e : a / (2 * K) * a - (a / (2 * K)) ^ 2 * K = a ^ 2 / (4 * K) := by
    field_simp; ring
  linarith

end Prequential

section Departure

/-! The map's departure from `1/s` times its unit. §5 holds the map as `φ M_t`, which reads the
executed map as `1/s` times its unit. The prior's resolvent says exactly what that reading drops:
along a direction where the readings' Gram is `g`, the reach is `1/(s + g)`, so the fraction of
the `1/s` map lost there is `g/(s + g)`, at most `λ/(s + λ)` when `0 ≤ g ≤ λ`. -/

/-- [proved-derived; formal-checked] **The prior's resolvent.** With `H = s I + G` invertible and
`s ≠ 0`, `H⁻¹ = s⁻¹ (I − G H⁻¹)`: the map is `1/s` times its unit less `s⁻¹ G H⁻¹`, the part the
readings' Gram carries. -/
theorem prior_resolvent (s : K) (hs : s ≠ 0) (G : Matrix n n K)
    (hH : IsUnit (s • (1 : Matrix n n K) + G).det) :
    (s • (1 : Matrix n n K) + G)⁻¹ = s⁻¹ • ((1 : Matrix n n K) - G * (s • (1 : Matrix n n K) + G)⁻¹) := by
  have h := Matrix.mul_nonsing_inv (s • (1 : Matrix n n K) + G) hH
  rw [add_mul, smul_mul_assoc, one_mul] at h
  have h' : s • (s • (1 : Matrix n n K) + G)⁻¹ = 1 - G * (s • (1 : Matrix n n K) + G)⁻¹ :=
    eq_sub_of_add_eq h
  rw [← h', smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- [proved-derived; formal-checked] **The reach along a direction of the readings' Gram.** If
`G v = g v` and `s I + G` is invertible, then `(s I + G)⁻¹ v = (s + g)⁻¹ v`. -/
theorem eigen_reach (s g : K) (G : Matrix n n K) (v : n → K) (hv : G *ᵥ v = g • v)
    (hsg : s + g ≠ 0) (hH : IsUnit (s • (1 : Matrix n n K) + G).det) :
    (s • (1 : Matrix n n K) + G)⁻¹ *ᵥ v = (s + g)⁻¹ • v := by
  have hHv : (s • (1 : Matrix n n K) + G) *ᵥ v = (s + g) • v := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv, add_smul]
  have h1 : (s • (1 : Matrix n n K) + G)⁻¹ *ᵥ ((s • (1 : Matrix n n K) + G) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hH, Matrix.one_mulVec]
  rw [hHv, Matrix.mulVec_smul] at h1
  calc (s • (1 : Matrix n n K) + G)⁻¹ *ᵥ v
      = (s + g)⁻¹ • ((s + g) • ((s • (1 : Matrix n n K) + G)⁻¹ *ᵥ v)) := by
        rw [smul_smul, inv_mul_cancel₀ hsg, one_smul]
    _ = (s + g)⁻¹ • v := by rw [h1]

omit [Fintype n] [DecidableEq n] in
/-- [proved-derived; formal-checked] **The fraction of the `1/s` map lost along that direction** is
`g/(s + g)`: `s⁻¹ v − (s + g)⁻¹ v = (g/(s + g)) s⁻¹ v`. -/
theorem eigen_departure (s g : K) (hs : s ≠ 0) (hsg : s + g ≠ 0) (v : n → K) :
    s⁻¹ • v - (s + g)⁻¹ • v = (g / (s + g)) • (s⁻¹ • v) := by
  rw [smul_smul, ← sub_smul]
  congr 1
  field_simp
  ring

/-- [proved-derived; formal-checked] **The lost fraction is bounded by the Gram's largest
eigenvalue.** For `0 < s` and `0 ≤ g ≤ λ`, `0 ≤ g/(s + g) ≤ λ/(s + λ)`. -/
theorem departure_le (s g lam : L) (hs : 0 < s) (hg : 0 ≤ g) (hgl : g ≤ lam) :
    0 ≤ g / (s + g) ∧ g / (s + g) ≤ lam / (s + lam) := by
  have h1 : 0 < s + g := by linarith
  have h2 : 0 < s + lam := by linarith
  refine ⟨div_nonneg hg h1.le, ?_⟩
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

/-- [proved-derived; formal-checked] **Campaign 1 at `2 I`.** The readings' Gram `F` has its largest
eigenvalue below `8599330/2^24` (§1 of the record), so along every eigen-direction of a Gram
`0 ⪯ G ⪯ F` the map loses less than `8599330/42153762` of `1/2` times its unit, which is below
`1/4`. -/
theorem campaign_one_departure (g : ℚ) (hg : 0 ≤ g) (hgl : g < 8599330 / 2 ^ 24) :
    g / (2 + g) < 8599330 / 42153762 ∧ (8599330 : ℚ) / 42153762 < 1 / 4 := by
  refine ⟨?_, by norm_num⟩
  have h1 : (0 : ℚ) < 2 + g := by linarith
  rw [div_lt_div_iff₀ h1 (by norm_num)]
  nlinarith

end Departure

end Holonics.HNN.ReceivingPrior
