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
7. **The lift to every direction** (`rayleigh_eigen_le`, `rayleigh_eigen_lt`, `eigen_nonneg`,
   `image_sq_le`, `departure_sq_le`, `departure_form_le`, `departure_pair_sq_le`,
   `campaign_one_lift`). A Gram below `F ⪯ λ I` has its eigenvalues at most `λ` (the Rayleigh
   step). With no eigenbasis: for symmetric `0 ⪯ G ⪯ λ I` and `y = (s I + G)⁻¹ x`, the departure
   `d = s⁻¹ x − y = s⁻¹ G y` has `|d|² ≤ (λ/(s + λ))² |s⁻¹ x|²` and
   `0 ≤ ⟨x, d⟩ ≤ (λ/(s + λ)) ⟨x, s⁻¹ x⟩`, from `|G y|² ≤ λ ⟨y, G y⟩ ≤ λ² |y|²`. A pair read
   `⟨(s I + G)⁻¹ u, z⟩` departs from `⟨s⁻¹ u, z⟩` by at most `(λ/(s + λ)) |s⁻¹ u| |z|`.
8. **The second order along the executed map** (`departure_class_le`, `faceVariance_sub_le`,
   `prequential_code_departure_le`). The executed move is `φ M_t − E_t`, its departure a sum of
   pair departures; with `|E_t c| ≤ r_t` the prequential code is at most the face's less `φ a`,
   plus `φ² (ln 2) 2^ω Σ_t Var_(p_t)(M_t)`, plus `(ln 2) 2^ω Σ_t r_t² + 2 Σ_t r_t`. It holds at
   the exact solve and `η = 1`; the certified step and the chart's lattice residual are
   `HNN/ChartResidual`.
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

section Lift

/-! The lift from eigen-directions to every direction, without an eigenbasis. Item 6 bounds the
departure along a direction where the readings' Gram is `g`. Here `G` is any symmetric Gram with
`0 ⪯ G ⪯ λ I` as quadratic forms. Writing `y = (s I + G)⁻¹ x`, the read is `x = s y + G y`, so the
departure of the `1/s` reading is `d = s⁻¹ x − y = s⁻¹ G y`. With `a = ⟨y, G y⟩`, `b = |G y|²`,
`c = |y|²`, the Gram gives `a ≤ λ c` and `b ≤ λ a` (`image_sq_le`), which is all the lift needs. -/

omit [DecidableEq n] in
theorem dot_self_nonneg (v : n → L) : 0 ≤ v ⬝ᵥ v :=
  sum_nonneg fun i _ => mul_self_nonneg (v i)

omit [DecidableEq n] in
theorem dot_self_pos (v : n → L) (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (dot_self_nonneg v) (fun h => hv (dotProduct_self_eq_zero.mp h.symm))

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] **Cauchy–Schwarz for the pairing**: `⟨u, v⟩² ≤ |u|² |v|²`. -/
theorem dot_sq_le (u v : n → L) : (u ⬝ᵥ v) ^ 2 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  simpa only [dotProduct, pow_two] using this

omit [DecidableEq n] [LinearOrder L] [IsStrictOrderedRing L] in
/-- A symmetric Gram moves across the pairing: `⟨u, G w⟩ = ⟨G u, w⟩`. -/
theorem sym_dot (G : Matrix n n L) (hGt : Gᵀ = G) (u w : n → L) :
    u ⬝ᵥ (G *ᵥ w) = (G *ᵥ u) ⬝ᵥ w := by
  rw [dotProduct_mulVec, ← vecMul_transpose, hGt]

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] **The Rayleigh step.** If the Gram `G` is below `F` and `F`
below `λ I` as quadratic forms, every eigenvalue of `G` is at most `λ`. This is what item 6's
eigenvalue bound stands on. -/
theorem rayleigh_eigen_le (G F : Matrix n n L) (lam g : L) (v : n → L) (hv0 : v ≠ 0)
    (hGF : ∀ x, x ⬝ᵥ (G *ᵥ x) ≤ x ⬝ᵥ (F *ᵥ x))
    (hF : ∀ x, x ⬝ᵥ (F *ᵥ x) ≤ lam * (x ⬝ᵥ x)) (hv : G *ᵥ v = g • v) : g ≤ lam := by
  have hp := dot_self_pos v hv0
  have h := (hGF v).trans (hF v)
  rw [hv, dotProduct_smul, smul_eq_mul] at h
  exact le_of_mul_le_mul_right h hp

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] **The strict Rayleigh step.** If `⟨x, F x⟩ < c |x|²` for every
`x ≠ 0` (what an exact `LDLᵀ` certificate of `c I − F` gives), every eigenvalue of a Gram
`G ⪯ F` is below `c`: on campaign 1 this is `campaign_one_departure`'s hypothesis `g < 8599330/2^24`. -/
theorem rayleigh_eigen_lt (G F : Matrix n n L) (c g : L) (v : n → L) (hv0 : v ≠ 0)
    (hGF : ∀ x, x ⬝ᵥ (G *ᵥ x) ≤ x ⬝ᵥ (F *ᵥ x))
    (hF : ∀ x, x ≠ 0 → x ⬝ᵥ (F *ᵥ x) < c * (x ⬝ᵥ x)) (hv : G *ᵥ v = g • v) : g < c := by
  have hp := dot_self_pos v hv0
  have h := (hGF v).trans_lt (hF v hv0)
  rw [hv, dotProduct_smul, smul_eq_mul] at h
  exact lt_of_mul_lt_mul_right h hp.le

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] A nonnegative Gram's eigenvalues are nonnegative. -/
theorem eigen_nonneg (G : Matrix n n L) (g : L) (v : n → L) (hv0 : v ≠ 0)
    (h0 : ∀ x, 0 ≤ x ⬝ᵥ (G *ᵥ x)) (hv : G *ᵥ v = g • v) : 0 ≤ g := by
  have hp := dot_self_pos v hv0
  have h := h0 v
  rw [hv, dotProduct_smul, smul_eq_mul] at h
  exact nonneg_of_mul_nonneg_left h hp

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] **The image of a bounded Gram.** For symmetric `G` with
`0 ⪯ G ⪯ λ I`, `λ > 0`: `|G y|² ≤ λ ⟨y, G y⟩`. The form at `y − λ⁻¹ G y` is nonnegative, and the
bound at `G y` closes it. -/
theorem image_sq_le (G : Matrix n n L) (hGt : Gᵀ = G) (lam : L) (hlam : 0 < lam)
    (h0 : ∀ x, 0 ≤ x ⬝ᵥ (G *ᵥ x)) (h1 : ∀ x, x ⬝ᵥ (G *ᵥ x) ≤ lam * (x ⬝ᵥ x)) (y : n → L) :
    (G *ᵥ y) ⬝ᵥ (G *ᵥ y) ≤ lam * (y ⬝ᵥ (G *ᵥ y)) := by
  set z := G *ᵥ y with hz
  have hx := h0 (y - lam⁻¹ • z)
  have he := h1 z
  have hyz : y ⬝ᵥ (G *ᵥ z) = z ⬝ᵥ z := by rw [sym_dot G hGt]
  have hzy : z ⬝ᵥ (G *ᵥ y) = z ⬝ᵥ z := rfl
  simp only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, hyz, hzy] at hx
  have hl : lam⁻¹ * lam = 1 := inv_mul_cancel₀ hlam.ne'
  have hli : 0 < lam⁻¹ := inv_pos.mpr hlam
  have key : lam⁻¹ * (lam⁻¹ * (z ⬝ᵥ (G *ᵥ z))) ≤ lam⁻¹ * (z ⬝ᵥ z) := by
    have := mul_le_mul_of_nonneg_left he (mul_nonneg hli.le hli.le)
    calc lam⁻¹ * (lam⁻¹ * (z ⬝ᵥ (G *ᵥ z))) = lam⁻¹ * lam⁻¹ * (z ⬝ᵥ (G *ᵥ z)) := by ring
      _ ≤ lam⁻¹ * lam⁻¹ * (lam * (z ⬝ᵥ z)) := this
      _ = lam⁻¹ * (z ⬝ᵥ z) := by rw [← mul_assoc, mul_assoc lam⁻¹ lam⁻¹ lam, hl, mul_one]
  have hb : lam⁻¹ * (z ⬝ᵥ z) ≤ y ⬝ᵥ (G *ᵥ y) := by linarith
  have := mul_le_mul_of_nonneg_left hb hlam.le
  rwa [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul] at this

omit [DecidableEq n] [LinearOrder L] [IsStrictOrderedRing L] in
/-- The read's energy: `|s y + G y|² = s² |y|² + 2 s ⟨y, G y⟩ + |G y|²`. -/
theorem read_energy (G : Matrix n n L) (s : L) (y : n → L) :
    (s • y + G *ᵥ y) ⬝ᵥ (s • y + G *ᵥ y) =
      s ^ 2 * (y ⬝ᵥ y) + 2 * s * (y ⬝ᵥ (G *ᵥ y)) + (G *ᵥ y) ⬝ᵥ (G *ᵥ y) := by
  have hc : (G *ᵥ y) ⬝ᵥ y = y ⬝ᵥ (G *ᵥ y) := dotProduct_comm _ _
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul, hc]
  ring

omit [LinearOrder L] [IsStrictOrderedRing L] in
/-- The read through the resolvent: with `y = (s I + G)⁻¹ x`, `x = s y + G y`. -/
theorem resolvent_read (s : L) (G : Matrix n n L) (hH : IsUnit (s • (1 : Matrix n n L) + G).det)
    (x : n → L) :
    x = s • ((s • (1 : Matrix n n L) + G)⁻¹ *ᵥ x) + G *ᵥ ((s • (1 : Matrix n n L) + G)⁻¹ *ᵥ x) := by
  have h : (s • (1 : Matrix n n L) + G) *ᵥ ((s • (1 : Matrix n n L) + G)⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
  exact h.symm

/-- [proved-derived; formal-checked] **The departure in every direction.** For symmetric `G` with
`0 ⪯ G ⪯ λ I`, `0 < s`, `0 < λ` and `s I + G` invertible, the `1/s` reading's departure
`d = s⁻¹ x − (s I + G)⁻¹ x` satisfies `|d|² ≤ (λ/(s + λ))² |s⁻¹ x|²` for every `x`. This is
`departure_le` lifted from eigen-directions to the whole space, with no eigenbasis. -/
theorem departure_sq_le (s lam : L) (hs : 0 < s) (hlam : 0 < lam) (G : Matrix n n L)
    (hGt : Gᵀ = G) (h0 : ∀ x, 0 ≤ x ⬝ᵥ (G *ᵥ x)) (h1 : ∀ x, x ⬝ᵥ (G *ᵥ x) ≤ lam * (x ⬝ᵥ x))
    (hH : IsUnit (s • (1 : Matrix n n L) + G).det) (x : n → L) :
    (s⁻¹ • x - (s • (1 : Matrix n n L) + G)⁻¹ *ᵥ x) ⬝ᵥ (s⁻¹ • x - (s • (1 : Matrix n n L) + G)⁻¹ *ᵥ x)
      ≤ (lam / (s + lam)) ^ 2 * ((s⁻¹ • x) ⬝ᵥ (s⁻¹ • x)) := by
  have hx := resolvent_read s G hH x
  obtain ⟨y, hy⟩ : ∃ y, y = (s • (1 : Matrix n n L) + G)⁻¹ *ᵥ x := ⟨_, rfl⟩
  rw [← hy] at hx ⊢
  have hd : s⁻¹ • x - y = s⁻¹ • (G *ᵥ y) := by
    rw [hx, smul_add, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]; abel
  rw [hd, hx]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [read_energy G s y]
  have ha0 := h0 y
  have hac := h1 y
  have hba := image_sq_le G hGt lam hlam h0 h1 y
  set a := y ⬝ᵥ (G *ᵥ y)
  set b := (G *ᵥ y) ⬝ᵥ (G *ᵥ y)
  set c := y ⬝ᵥ y
  have hspl : 0 < s + lam := by linarith
  have core : (s + lam) ^ 2 * b ≤ lam ^ 2 * (s ^ 2 * c + 2 * s * a + b) := by
    nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hba),
      mul_nonneg (mul_nonneg (sq_nonneg s) hlam.le) (sub_nonneg.mpr hac),
      mul_nonneg (mul_nonneg hs.le hlam.le) (sub_nonneg.mpr hba)]
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have hsi := sq_nonneg s⁻¹
  have := mul_le_mul_of_nonneg_left core hsi
  calc s⁻¹ * (s⁻¹ * b) * (s + lam) ^ 2 = s⁻¹ ^ 2 * ((s + lam) ^ 2 * b) := by ring
    _ ≤ s⁻¹ ^ 2 * (lam ^ 2 * (s ^ 2 * c + 2 * s * a + b)) := this
    _ = lam ^ 2 * (s⁻¹ * (s⁻¹ * (s ^ 2 * c + 2 * s * a + b))) := by ring

/-- [proved-derived; formal-checked] **The departure along the read itself.** Under the hypotheses
of `departure_sq_le`, `0 ≤ ⟨x, d⟩ ≤ (λ/(s + λ)) ⟨x, s⁻¹ x⟩`: the `1/s` reading overstates the
map's form at every read, by at most the fraction `λ/(s + λ)`. -/
theorem departure_form_le (s lam : L) (hs : 0 < s) (hlam : 0 < lam) (G : Matrix n n L)
    (hGt : Gᵀ = G) (h0 : ∀ x, 0 ≤ x ⬝ᵥ (G *ᵥ x)) (h1 : ∀ x, x ⬝ᵥ (G *ᵥ x) ≤ lam * (x ⬝ᵥ x))
    (hH : IsUnit (s • (1 : Matrix n n L) + G).det) (x : n → L) :
    0 ≤ x ⬝ᵥ (s⁻¹ • x - (s • (1 : Matrix n n L) + G)⁻¹ *ᵥ x) ∧
      x ⬝ᵥ (s⁻¹ • x - (s • (1 : Matrix n n L) + G)⁻¹ *ᵥ x) ≤ lam / (s + lam) * (x ⬝ᵥ (s⁻¹ • x)) := by
  have hx := resolvent_read s G hH x
  obtain ⟨y, hy⟩ : ∃ y, y = (s • (1 : Matrix n n L) + G)⁻¹ *ᵥ x := ⟨_, rfl⟩
  rw [← hy] at hx ⊢
  have hd : s⁻¹ • x - y = s⁻¹ • (G *ᵥ y) := by
    rw [hx, smul_add, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]; abel
  rw [hd]
  have hxx : x ⬝ᵥ (s⁻¹ • x) = s⁻¹ * (s ^ 2 * (y ⬝ᵥ y) + 2 * s * (y ⬝ᵥ (G *ᵥ y)) +
      (G *ᵥ y) ⬝ᵥ (G *ᵥ y)) := by
    rw [dotProduct_smul, smul_eq_mul, ← read_energy G s y, ← hx]
  have hxd : x ⬝ᵥ (s⁻¹ • (G *ᵥ y)) = s⁻¹ * (s * (y ⬝ᵥ (G *ᵥ y)) + (G *ᵥ y) ⬝ᵥ (G *ᵥ y)) := by
    rw [dotProduct_smul, smul_eq_mul, hx, add_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [hxx, hxd]
  have ha0 := h0 y
  have hac := h1 y
  have hba := image_sq_le G hGt lam hlam h0 h1 y
  have hb0 := dot_self_nonneg (G *ᵥ y)
  set a := y ⬝ᵥ (G *ᵥ y)
  set b := (G *ᵥ y) ⬝ᵥ (G *ᵥ y)
  set c := y ⬝ᵥ y
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs
  have hspl : 0 < s + lam := by linarith
  refine ⟨mul_nonneg hsi.le (by nlinarith), ?_⟩
  have core : (s + lam) * (s * a + b) ≤ lam * (s ^ 2 * c + 2 * s * a + b) := by
    nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hac),
      mul_nonneg hs.le (sub_nonneg.mpr hba)]
  rw [div_mul_eq_mul_div, le_div_iff₀ hspl]
  have := mul_le_mul_of_nonneg_left core hsi.le
  calc s⁻¹ * (s * a + b) * (s + lam) = s⁻¹ * ((s + lam) * (s * a + b)) := by ring
    _ ≤ s⁻¹ * (lam * (s ^ 2 * c + 2 * s * a + b)) := this
    _ = lam * (s⁻¹ * (s ^ 2 * c + 2 * s * a + b)) := by ring

/-- [proved-derived; formal-checked] **The departure of one pair read.** The executed map reads a
pair of readings `u`, `z` as `⟨(s I + G)⁻¹ u, z⟩` where the `1/s` reading takes `⟨s⁻¹ u, z⟩`. Their
difference `q = ⟨s⁻¹ u − (s I + G)⁻¹ u, z⟩` satisfies `q² ≤ (λ/(s + λ))² |s⁻¹ u|² |z|²`. -/
theorem departure_pair_sq_le (s lam : L) (hs : 0 < s) (hlam : 0 < lam) (G : Matrix n n L)
    (hGt : Gᵀ = G) (h0 : ∀ x, 0 ≤ x ⬝ᵥ (G *ᵥ x)) (h1 : ∀ x, x ⬝ᵥ (G *ᵥ x) ≤ lam * (x ⬝ᵥ x))
    (hH : IsUnit (s • (1 : Matrix n n L) + G).det) (u z : n → L) :
    ((s⁻¹ • u - (s • (1 : Matrix n n L) + G)⁻¹ *ᵥ u) ⬝ᵥ z) ^ 2 ≤
      (lam / (s + lam)) ^ 2 * ((s⁻¹ • u) ⬝ᵥ (s⁻¹ • u)) * (z ⬝ᵥ z) :=
  (dot_sq_le _ z).trans
    (mul_le_mul_of_nonneg_right (departure_sq_le s lam hs hlam G hGt h0 h1 hH u)
      (dot_self_nonneg z))

/-- [proved-derived; formal-checked] **Campaign 1 at `2 I`, in every direction.** With the readings'
Gram below `λ = 8599330/2^24` (§1 of the record), the `1/2` reading's departure satisfies
`|d|² ≤ (8599330/42153762)² |x/2|²`. -/
theorem campaign_one_lift (G : Matrix n n L) (hGt : Gᵀ = G) (h0 : ∀ x, 0 ≤ x ⬝ᵥ (G *ᵥ x))
    (h1 : ∀ x, x ⬝ᵥ (G *ᵥ x) ≤ 8599330 / 2 ^ 24 * (x ⬝ᵥ x))
    (hH : IsUnit ((2 : L) • (1 : Matrix n n L) + G).det) (x : n → L) :
    ((2 : L)⁻¹ • x - ((2 : L) • (1 : Matrix n n L) + G)⁻¹ *ᵥ x) ⬝ᵥ
        ((2 : L)⁻¹ • x - ((2 : L) • (1 : Matrix n n L) + G)⁻¹ *ᵥ x)
      ≤ (8599330 / 42153762) ^ 2 * (((2 : L)⁻¹ • x) ⬝ᵥ ((2 : L)⁻¹ • x)) := by
  have h := departure_sq_le (2 : L) (8599330 / 2 ^ 24) (by norm_num) (by norm_num) G hGt h0 h1 hH x
  have e : (8599330 / 2 ^ 24 : L) / (2 + 8599330 / 2 ^ 24) = 8599330 / 42153762 := by norm_num
  rwa [e] at h

end Lift

section SecondOrder

/-! The second order along the executed map. §5 holds the map as `φ M_t`, the `1/s` reading. The
executed move is `φ M_t − E_t`, where `E_t` collects the pair departures
(`departure_pair_sq_le`): at reading `t`, class `c`, `E_t c = Σ_u κ g_u c q_(u,t)` with
`q_(u,t) = ⟨s⁻¹ z_u − X̂ z_u, z_t⟩`. A class bound `|E_t c| ≤ r_t` (`departure_class_le`) enters the
prequential code as an explicit remainder. -/

open Holonics.HNN.Ratio Holonics.HNN.Ratio.Certificate

/-- [proved-derived; formal-checked] **A class's departure from its pair departures.** If
`E = Σ_u w_u q_u` with `q_u² ≤ ρ_u²`, `ρ_u ≥ 0`, then `|E| ≤ Σ_u |w_u| ρ_u`. -/
theorem departure_class_le {U : Type*} (S : Finset U) (w q ρ : U → L)
    (hq : ∀ u, q u ^ 2 ≤ ρ u ^ 2) (hρ : ∀ u, 0 ≤ ρ u) :
    |∑ u ∈ S, w u * q u| ≤ ∑ u ∈ S, |w u| * ρ u :=
  (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun u _ => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le_of_sq_le_sq (hq u) (hρ u)) (abs_nonneg _))

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The face `p_c = 2^(f_c)/Σ 2^f` is a simplex point. -/
theorem bit_face_simplex (f p : ι → ℝ) (hp : ∀ c, p c = (2 : ℝ) ^ f c / ∑ d, (2 : ℝ) ^ f d) :
    (∀ c, 0 ≤ p c) ∧ ∑ c, p c = 1 := by
  have hS : 0 < ∑ d, (2 : ℝ) ^ f d :=
    sum_pos (fun d _ => Real.rpow_pos_of_pos (by norm_num) _) univ_nonempty
  refine ⟨fun c => ?_, ?_⟩
  · rw [hp c]; exact div_nonneg (Real.rpow_nonneg (by norm_num) _) hS.le
  · simp_rw [hp]; rw [← sum_div, div_self hS.ne']

omit [Nonempty ι] [DecidableEq ι] in
/-- [proved-derived; formal-checked] **The variance of a departed move.** On a simplex point,
`Var_p(v − e) ≤ 2 Var_p(v) + 2 Σ p e²`. -/
theorem faceVariance_sub_le (p v e : ι → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) :
    faceVariance p (fun c => v c - e c) ≤ 2 * faceVariance p v + 2 * ∑ c, p c * e c ^ 2 := by
  set μ := ∑ j, p j * v j with hμ
  have h := faceVariance_add_sq p (fun c => v c - e c) hp1 μ
  beta_reduce at h
  have hle : ∑ c, p c * (v c - e c - μ) ^ 2 ≤
      ∑ c, (2 * (p c * (v c - μ) ^ 2) + 2 * (p c * e c ^ 2)) :=
    sum_le_sum fun c _ => by nlinarith [mul_nonneg (hp0 c) (sq_nonneg (v c - μ + e c))]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hle
  have hv : faceVariance p v = ∑ c, p c * (v c - μ) ^ 2 := rfl
  nlinarith [sq_nonneg (∑ i, p i * (v i - e i) - μ)]

/-- [proved-derived; formal-checked] **The prequential code along the executed map.** Each reading
`t` meets the executed move `φ M_t − E_t` on its face `f_t`, its classes differing pairwise by at
most `ω`, with the departure bounded classwise by `|E_t c| ≤ r_t`. Summed, the code is at most the
face's code less `φ a` plus `φ² (ln 2) 2^ω Σ_t Var_(p_t)(M_t)`, plus the departure's remainder
`(ln 2) 2^ω Σ_t r_t² + 2 Σ_t r_t`. At `E = 0` the quadratic is twice `prequential_code_le`'s: the
cross term between the `1/s` move and its departure is bounded, not dropped. -/
theorem prequential_code_departure_le {T : Type*} [Fintype T] (f M E p : T → ι → ℝ)
    (hp : ∀ t c, p t c = (2 : ℝ) ^ f t c / ∑ d, (2 : ℝ) ^ f t d) (target : T → ι) (φ ω : ℝ)
    (r : T → ℝ) (hosc : ∀ t c d, (φ * M t c - E t c) - (φ * M t d - E t d) ≤ ω)
    (hE : ∀ t c, |E t c| ≤ r t) :
    ∑ t, codeLength (fun c => f t c + (φ * M t c - E t c)) (target t) ≤
      ∑ t, codeLength (f t) (target t)
        - φ * ∑ t, ∑ c, ((Pi.single (target t) (1 : ℝ) : ι → ℝ) c - p t c) * M t c
        + φ ^ 2 * (Real.log 2 * (2 : ℝ) ^ ω * ∑ t, faceVariance (p t) (M t))
        + (Real.log 2 * (2 : ℝ) ^ ω * ∑ t, r t ^ 2 + 2 * ∑ t, r t) := by
  have hC : 0 ≤ Real.log 2 / 2 * (2 : ℝ) ^ ω := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have h : ∀ t, codeLength (fun c => f t c + (φ * M t c - E t c)) (target t) ≤
      codeLength (f t) (target t)
        - φ * ∑ c, ((Pi.single (target t) (1 : ℝ) : ι → ℝ) c - p t c) * M t c
        + φ ^ 2 * (Real.log 2 * (2 : ℝ) ^ ω * faceVariance (p t) (M t))
        + (Real.log 2 * (2 : ℝ) ^ ω * r t ^ 2 + 2 * r t) := by
    intro t
    obtain ⟨hp0, hp1⟩ := bit_face_simplex (f t) (p t) (hp t)
    have hcode := codeLength_add_le (f t) (fun c => φ * M t c - E t c) (p t) (hp t) (hosc t)
      (target t)
    have hlin : ∑ c, (p t c - (Pi.single (target t) (1 : ℝ) : ι → ℝ) c) * (φ * M t c - E t c) =
        -(φ * ∑ c, ((Pi.single (target t) (1 : ℝ) : ι → ℝ) c - p t c) * M t c)
          + (∑ c, (Pi.single (target t) (1 : ℝ) : ι → ℝ) c * E t c - ∑ c, p t c * E t c) := by
      rw [mul_sum, ← sum_neg_distrib, ← sum_sub_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun c _ => by ring
    have hδ : ∑ c, (Pi.single (target t) (1 : ℝ) : ι → ℝ) c * E t c = E t (target t) := by
      simp [Pi.single_apply]
    have hpE : -(∑ c, p t c * E t c) ≤ r t := by
      have hs : ∑ c, -(p t c * E t c) ≤ ∑ c, p t c * r t := sum_le_sum fun c _ => by
        have := mul_le_mul_of_nonneg_left
          ((neg_le_abs (E t c)).trans (hE t c)) (hp0 c)
        linarith
      rwa [sum_neg_distrib, ← sum_mul, hp1, one_mul] at hs
    have hEt : E t (target t) ≤ r t := (le_abs_self _).trans (hE t _)
    have hsq : ∀ c, E t c ^ 2 ≤ r t ^ 2 := fun c => by
      have := pow_le_pow_left₀ (abs_nonneg (E t c)) (hE t c) 2
      rwa [sq_abs] at this
    have h2 : ∑ c, p t c * E t c ^ 2 ≤ r t ^ 2 := by
      calc ∑ c, p t c * E t c ^ 2 ≤ ∑ c, p t c * r t ^ 2 :=
            sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hsq c) (hp0 c)
        _ = r t ^ 2 := by rw [← sum_mul, hp1, one_mul]
    have h1 : faceVariance (p t) (fun c => φ * M t c - E t c) ≤
        2 * faceVariance (p t) (fun c => φ * M t c) + 2 * ∑ c, p t c * E t c ^ 2 :=
      faceVariance_sub_le (p t) (fun c => φ * M t c) (E t) hp0 hp1
    rw [faceVariance_smul] at h1
    have hvar : faceVariance (p t) (fun c => φ * M t c - E t c) ≤
        2 * (φ ^ 2 * faceVariance (p t) (M t)) + 2 * r t ^ 2 := by linarith
    have hCV := mul_le_mul_of_nonneg_left hvar hC
    rw [hlin, hδ] at hcode
    nlinarith
  calc _ ≤ ∑ t, (codeLength (f t) (target t)
        - φ * ∑ c, ((Pi.single (target t) (1 : ℝ) : ι → ℝ) c - p t c) * M t c
        + φ ^ 2 * (Real.log 2 * (2 : ℝ) ^ ω * faceVariance (p t) (M t))
        + (Real.log 2 * (2 : ℝ) ^ ω * r t ^ 2 + 2 * r t)) := sum_le_sum fun t _ => h t
    _ = _ := by
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]

end SecondOrder

#print axioms departure_sq_le
#print axioms departure_form_le
#print axioms departure_pair_sq_le
#print axioms campaign_one_lift
#print axioms rayleigh_eigen_lt
#print axioms prequential_code_departure_le

end Holonics.HNN.ReceivingPrior
