import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The face's two covectors: the news and the centred surprise

The record `research/records/2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ.md`
(§6) drives a level above the face `p` by the face's cokernel, never by its own read, through two
covectors of the face: the news `[u] − p`, the covector of the face's logits, and the centred
surprise `−ln p(u) − H(p)`, the covector of the face's temperature. #410 owes the temperature
derivative and the martingale law; this file proves them for a positive normalized face on a finite
set of classes.

[proved-standard; formal-checked] What is proved.

1. **The tilted code** (`tiltedCode`, `tiltedCode_eq`): for `p_τ ∝ p^τ`, the code of class `u` is
   `−ln p_τ(u) = −τ ln p(u) + ln Σ_v p(v)^τ`.
2. **Its derivative is the centred surprise** (`hasDerivAt_tiltedCode`, `tiltedCode_deriv_one`):
   `d/dτ (−ln p_τ(u))` at `τ = 1` is `−ln p(u) − H(p)`, `H(p) = −Σ p ln p`.
3. **Its second derivative is the Fisher term** (`variance_log`, `tiltedCode_second_deriv`): the
   derivative of that derivative at `τ = 1` is `Var_p(ln p) = Σ p (ln p − Σ p ln p)²`, the curvature
   the record's placement reads (`H` for the temperature covector).
4. **Both covectors are martingale differences** (`news_mean_zero`, `surprise_mean_zero`): under
   the true conditional `p`, `Σ_u p(u) ([u = c] − p(c)) = 0` for every class `c` and
   `Σ_u p(u) (−ln p(u) − H(p)) = 0`.
5. **No read lowers the expected code** (`gibbs`): for every positive face `q` of total mass at most
   one, `Σ p ln q ≤ Σ p ln p`, so the expected code under `p` is the least any face reaches.

So whatever a level driven by the two covectors reads is the face's error against the full past,
never a second copy of the face.

The computational object is the helical pair interaction: the face is the receiver's reading at a
pair contact, and its two covectors are what that contact leaves unresolved. Of the winding guide's
six general objects this touches faces and placement (the receiving face and its temperature) and
the tower thread (the level driven by the face's cokernel); the helix, the pair, the cell holonomy
and the tube stay attached.

Consumers: the atlas row `ratio.face-temperature-covector` and the record's §6.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.FaceCovectors

open Real Finset

variable {ι : Type*} [Fintype ι] (p : ι → ℝ)

/-- [definition] The entropy of a face, `H(p) = −Σ p ln p`. -/
noncomputable def entropy : ℝ := -∑ v, p v * log (p v)

/-- [definition] The tilted code of class `u`, `−ln p_τ(u)` for `p_τ ∝ p^τ`, written in its
exponential chart: `−τ ln p(u) + ln Σ_v exp(τ ln p(v))`. -/
noncomputable def tiltedCode (u : ι) (τ : ℝ) : ℝ :=
  -(τ * log (p u)) + log (∑ v, exp (τ * log (p v)))

variable {p}

/-- [proved-standard; formal-checked] **The tilted code is the code of the tilted face:**
`tiltedCode = −ln (p(u)^τ / Σ_v p(v)^τ)`. -/
theorem tiltedCode_eq [Nonempty ι] (hp : ∀ v, 0 < p v) (u : ι) (τ : ℝ) :
    tiltedCode p u τ = -log (p u ^ τ / ∑ v, p v ^ τ) := by
  have hpow : ∀ v, p v ^ τ = exp (τ * log (p v)) := fun v => by
    rw [rpow_def_of_pos (hp v), mul_comm]
  have hZ : 0 < ∑ v, exp (τ * log (p v)) :=
    Finset.sum_pos (fun v _ => exp_pos _) Finset.univ_nonempty
  simp only [hpow]
  rw [log_div (exp_pos _).ne' hZ.ne', log_exp, tiltedCode]
  ring

/-- [proved-standard; formal-checked] The derivative of the tilted code in the temperature. -/
theorem hasDerivAt_tiltedCode [Nonempty ι] (u : ι) (τ : ℝ) :
    HasDerivAt (tiltedCode p u)
      (-log (p u) + (∑ v, exp (τ * log (p v)) * log (p v)) / ∑ v, exp (τ * log (p v))) τ := by
  have hZ : HasDerivAt (fun τ => ∑ v, exp (τ * log (p v)))
      (∑ v, exp (τ * log (p v)) * log (p v)) τ :=
    HasDerivAt.fun_sum fun v _ => (hasDerivAt_mul_const (log (p v))).exp
  have hZpos : 0 < ∑ v, exp (τ * log (p v)) :=
    Finset.sum_pos (fun v _ => exp_pos _) Finset.univ_nonempty
  exact (hasDerivAt_mul_const (log (p u))).fun_neg.fun_add (hZ.log hZpos.ne')

/-- [proved-standard; formal-checked] **The temperature covector is the centred surprise:**
`d/dτ (−ln p_τ(u)) = −ln p(u) − H(p)` at `τ = 1`. -/
theorem tiltedCode_deriv_one [Nonempty ι] (hp : ∀ v, 0 < p v) (hp1 : ∑ v, p v = 1) (u : ι) :
    HasDerivAt (tiltedCode p u) (-log (p u) - entropy p) 1 := by
  have hs : ∀ v, exp (1 * log (p v)) = p v := fun v => by rw [one_mul, exp_log (hp v)]
  have h := hasDerivAt_tiltedCode (p := p) u 1
  convert h using 1
  simp only [hs, hp1, div_one, entropy]
  ring

/-- [proved-standard; formal-checked] The variance of the log face, `Σ p (ln p − m)² =
Σ p (ln p)² − m²` with `m = Σ p ln p`, for a normalized face. -/
theorem variance_log (hp1 : ∑ v, p v = 1) :
    ∑ v, p v * (log (p v) - ∑ w, p w * log (p w)) ^ 2 =
      ∑ v, p v * log (p v) ^ 2 - (∑ w, p w * log (p w)) ^ 2 := by
  set m := ∑ w, p w * log (p w) with hm
  have hterm : ∀ v, p v * (log (p v) - m) ^ 2 =
      p v * log (p v) ^ 2 - 2 * m * (p v * log (p v)) + m ^ 2 * p v := fun v => by ring
  rw [Finset.sum_congr rfl fun v _ => hterm v, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hp1, ← hm]
  ring

/-- [proved-standard; formal-checked] **The temperature's curvature is the Fisher term:** the second
derivative of the tilted code at `τ = 1` is `Var_p(ln p)`. -/
theorem tiltedCode_second_deriv [Nonempty ι] (hp : ∀ v, 0 < p v) (hp1 : ∑ v, p v = 1) (u : ι) :
    HasDerivAt (deriv (tiltedCode p u))
      (∑ v, p v * (log (p v) - ∑ w, p w * log (p w)) ^ 2) 1 := by
  have hderiv : deriv (tiltedCode p u) = fun τ =>
      -log (p u) + (∑ v, exp (τ * log (p v)) * log (p v)) / ∑ v, exp (τ * log (p v)) :=
    funext fun τ => (hasDerivAt_tiltedCode u τ).deriv
  have hN : HasDerivAt (fun τ => ∑ v, exp (τ * log (p v)) * log (p v))
      (∑ v, exp (1 * log (p v)) * log (p v) * log (p v)) 1 :=
    HasDerivAt.fun_sum fun v _ => ((hasDerivAt_mul_const (log (p v))).exp).mul_const (log (p v))
  have hZ : HasDerivAt (fun τ => ∑ v, exp (τ * log (p v)))
      (∑ v, exp (1 * log (p v)) * log (p v)) 1 :=
    HasDerivAt.fun_sum fun v _ => (hasDerivAt_mul_const (log (p v))).exp
  have hZpos : 0 < ∑ v, exp (1 * log (p v)) :=
    Finset.sum_pos (fun v _ => exp_pos _) Finset.univ_nonempty
  have h := (hasDerivAt_const (x := (1 : ℝ)) (c := -log (p u))).fun_add (hN.fun_div hZ hZpos.ne')
  rw [hderiv]
  convert h using 1
  have hs : ∀ v, exp (1 * log (p v)) = p v := fun v => by rw [one_mul, exp_log (hp v)]
  have hsq : ∑ v, p v * log (p v) * log (p v) = ∑ v, p v * log (p v) ^ 2 :=
    Finset.sum_congr rfl fun v _ => by ring
  simp only [hs, hp1, hsq, variance_log hp1]
  ring

/-- [proved-standard; formal-checked] **The news is a martingale difference:** under the true
conditional, `Σ_u p(u) ([u = c] − p(c)) = 0` for every class `c`. -/
theorem news_mean_zero [DecidableEq ι] (hp1 : ∑ v, p v = 1) (c : ι) :
    ∑ u, p u * ((if u = c then 1 else 0) - p c) = 0 := by
  have hterm : ∀ u, p u * ((if u = c then 1 else 0) - p c) =
      (if u = c then p u else 0) - p u * p c := fun u => by split_ifs <;> ring
  rw [Finset.sum_congr rfl fun u _ => hterm u, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ c), ← Finset.sum_mul, hp1, one_mul, sub_self]

/-- [proved-standard; formal-checked] **The centred surprise is a martingale difference:** under the
true conditional, `Σ_u p(u) (−ln p(u) − H(p)) = 0`. -/
theorem surprise_mean_zero (hp1 : ∑ v, p v = 1) :
    ∑ u, p u * (-log (p u) - entropy p) = 0 := by
  have hterm : ∀ u, p u * (-log (p u) - entropy p) = -(p u * log (p u)) - entropy p * p u :=
    fun u => by ring
  rw [Finset.sum_congr rfl fun u _ => hterm u, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, hp1, entropy]
  ring

/-- [proved-standard; formal-checked] **No read lowers the expected code (Gibbs):** for every
positive face `q` of total mass at most one, `Σ p ln q ≤ Σ p ln p`. -/
theorem gibbs (hp : ∀ v, 0 < p v) (hp1 : ∑ v, p v = 1) (q : ι → ℝ) (hq : ∀ v, 0 < q v)
    (hq1 : ∑ v, q v ≤ 1) : ∑ v, p v * log (q v) ≤ ∑ v, p v * log (p v) := by
  have hterm : ∀ v, p v * log (q v) - p v * log (p v) ≤ q v - p v := by
    intro v
    have h1 := log_le_sub_one_of_pos (div_pos (hq v) (hp v))
    rw [log_div (hq v).ne' (hp v).ne'] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (hp v).le
    have hpv : p v ≠ 0 := (hp v).ne'
    have h3 : p v * (q v / p v - 1) = q v - p v := by field_simp
    linarith [h2, h3]
  have hsum := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hterm v
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hp1] at hsum
  linarith

end Holonics.HNN.FaceCovectors
