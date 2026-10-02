import Holonics.Transport.ChangingReceiver
import Holonics.Aeon.Production.FirstLaw.Continuous
import Holonics.Foundation.InformationReceiver
import Holonics.Foundation.FiniteCrossEntropyReceiver
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The cross-entropy rate carries both motions and their clocks

[definition] Rebuild step 6, K4 (#75); restructure plan §3.6 at `13f8c734`. For a moving received
population `p` and a moving reference `q` along a declared common parameter `λ`, the cross-entropy
`C(p, q) = −Σ pᵢ log qᵢ` (the owner's `Foundation/FiniteCrossEntropyReceiver.finiteCrossEntropy`;
on sections it is the owner's `PositiveProbabilitySection.crossEntropy`) changes at

```text
dC/dλ = −Σ ṗᵢ log qᵢ − Σ pᵢ q̇ᵢ/qᵢ
```

where each dot includes its clock-rate map: `ṗ = r_p P′` with `r_p = dτ_p/dλ` for the source clock,
`q̇ = r_q Q′` for the receiving clock.

[proved-derived; formal-checked]

* **Both motions enter**: the one owner of the rate is the first law's continuous chart
  (`Aeon/Production/FirstLaw.hasDerivAt_crossEntropy`, the exchange rate plus the deposition rate);
  on sections the owner's cross-entropy has that derivative (`hasDerivAt_section_crossEntropy`).
* **Each dot carries its clock** (`hasDerivAt_crossEntropy_clocks`): the population on its source
  clock `τ_p` and the reference on its receiving clock `τ_q` give
  `−r_p Σ P′ log Q − r_q Σ P Q′/Q`.
* **The moving aperture's normalization**: a population that stays normalized has `Σ ṗ = 0`
  (`sum_rate_eq_zero`), so the relative entropy moves at `Σ ṗ log(p/q) − Σ p q̇/q`
  (`hasDerivAt_kl`).

[counterexample; formal-checked] **The reference's motion is load-bearing.** A fixed population
read against a moving reference changes its cross-entropy at `2/3` while the population term
`−Σ ṗ log q` is `0` (`moving_reference_rate`).

The two terms are the infinitesimal forms of the first law of learning
(`Aeon/Production/FirstLaw.exchange`, `deposition`): `−Σ ṗ log q` is the source's exchange through
the unchanged receiver, `−Σ p q̇/q` the receiver's deposition at the arrived source.

Scope: fixed finite support with positive masses. A moving support needs a one-sided or measure
transport, owed (#62).
-/

noncomputable section

namespace Holonics.Physics.Information.CrossEntropyRate

open Holonics.Computation.HolonicInformationTheory
open Holonics.Foundation.HolonicMembraneActionTransport (finiteCrossEntropy)
open Holonics.Aeon.Production.FirstLaw (hasDerivAt_crossEntropy)

variable {ι : Type*} [Fintype ι]

/-- [proved-derived; formal-checked] On sections, the owner's cross-entropy has the same rate. -/
theorem hasDerivAt_section_crossEntropy
    (p q : ℝ → PositiveProbabilitySection ι) (p' q' : ι → ℝ) (t : ℝ)
    (hp : ∀ i, HasDerivAt (fun s => (p s).mass i) (p' i) t)
    (hq : ∀ i, HasDerivAt (fun s => (q s).mass i) (q' i) t) :
    HasDerivAt (fun s => (p s).crossEntropy (q s))
      (-∑ i, p' i * Real.log ((q t).mass i) - ∑ i, (p t).mass i * (q' i / (q t).mass i)) t :=
  (hasDerivAt_crossEntropy hp hq fun i => (q t).positive i).congr_deriv (by ring)

/-- [proved-derived; formal-checked] **Each dot carries its clock-rate map.** The population runs on
its source clock `τ_p` (rate `r_p`), the reference on its receiving clock `τ_q` (rate `r_q`). -/
theorem hasDerivAt_crossEntropy_clocks (P Q : ℝ → ι → ℝ) (P' Q' : ι → ℝ) (τp τq : ℝ → ℝ)
    (rp rq t : ℝ) (hτp : HasDerivAt τp rp t) (hτq : HasDerivAt τq rq t)
    (hP : ∀ i, HasDerivAt (fun u => P u i) (P' i) (τp t))
    (hQ : ∀ i, HasDerivAt (fun u => Q u i) (Q' i) (τq t)) (hpos : ∀ i, 0 < Q (τq t) i) :
    HasDerivAt (fun s => finiteCrossEntropy (P (τp s)) (Q (τq s)))
      (-(rp * ∑ i, P' i * Real.log (Q (τq t) i)) -
        rq * ∑ i, P (τp t) i * (Q' i / Q (τq t) i)) t := by
  have h := hasDerivAt_crossEntropy (p := fun s => P (τp s)) (q := fun s => Q (τq s))
    (dp := fun i => P' i * rp) (dq := fun i => Q' i * rq) (fun i => (hP i).comp t hτp)
    (fun i => (hQ i).comp t hτq) hpos
  beta_reduce at h
  refine h.congr_deriv ?_
  have e₁ : ∑ i, P' i * rp * Real.log (Q (τq t) i) = rp * ∑ i, P' i * Real.log (Q (τq t) i) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have e₂ : ∑ i, P (τp t) i * (Q' i * rq / Q (τq t) i) =
      rq * ∑ i, P (τp t) i * (Q' i / Q (τq t) i) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e₁, e₂]
  ring

/-- [proved-derived; formal-checked] **A normalized population moves with `Σ ṗ = 0`.** -/
theorem sum_rate_eq_zero (p : ℝ → ι → ℝ) (p' : ι → ℝ) (t : ℝ)
    (hp : ∀ i, HasDerivAt (fun s => p s i) (p' i) t) (hnorm : ∀ s, ∑ i, p s i = 1) :
    ∑ i, p' i = 0 := by
  have hsum : HasDerivAt (fun s => ∑ i, p s i) (∑ i, p' i) t :=
    HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hp i
  have hconst : HasDerivAt (fun s => ∑ i, p s i) 0 t := by
    simp only [hnorm]; exact hasDerivAt_const t 1
  exact hsum.unique hconst

/-- [proved-derived; formal-checked] **The relative entropy's rate** for a normalized population:
`d/dλ D(p‖q) = Σ ṗ log(p/q) − Σ p q̇/q`. -/
theorem hasDerivAt_kl (p q : ℝ → ι → ℝ) (p' q' : ι → ℝ) (t : ℝ)
    (hp : ∀ i, HasDerivAt (fun s => p s i) (p' i) t)
    (hq : ∀ i, HasDerivAt (fun s => q s i) (q' i) t) (hppos : ∀ i, p t i ≠ 0)
    (hqpos : ∀ i, q t i ≠ 0) (hnorm : ∀ s, ∑ i, p s i = 1) :
    HasDerivAt (fun s => ∑ i, p s i * (Real.log (p s i) - Real.log (q s i)))
      (∑ i, p' i * (Real.log (p t i) - Real.log (q t i)) - ∑ i, p t i * (q' i / q t i)) t := by
  have hterm : ∀ i ∈ (Finset.univ : Finset ι),
      HasDerivAt (fun s => p s i * (Real.log (p s i) - Real.log (q s i)))
        (p' i * (Real.log (p t i) - Real.log (q t i)) +
          p t i * (p' i / p t i - q' i / q t i)) t :=
    fun i _ => (hp i).mul (((hp i).log (hppos i)).sub ((hq i).log (hqpos i)))
  have hsum := HasDerivAt.fun_sum hterm
  have hzero := sum_rate_eq_zero p p' t hp hnorm
  refine hsum.congr_deriv ?_
  rw [Finset.sum_add_distrib]
  have : ∑ i, p t i * (p' i / p t i - q' i / q t i) =
      ∑ i, p' i - ∑ i, p t i * (q' i / q t i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp [hppos i]
  rw [this, hzero]
  ring

/-- [counterexample; formal-checked] **The reference's motion is load-bearing.** The fixed
population `(1/3, 2/3)` read against the moving reference `(1/2 + s, 1/2 − s)` changes its
cross-entropy at `2/3` at `s = 0`, while the population term `−Σ ṗ log q` is `0`. -/
theorem moving_reference_rate :
    HasDerivAt (fun s : ℝ => finiteCrossEntropy (![1 / 3, 2 / 3] : Fin 2 → ℝ) ![1 / 2 + s, 1 / 2 - s])
      (2 / 3) 0 ∧
      -(∑ i : Fin 2, (0 : ℝ) * Real.log (![1 / 2 + 0, 1 / 2 - 0] i)) = 0 := by
  refine ⟨?_, by simp⟩
  have hq : ∀ i : Fin 2, HasDerivAt (fun s : ℝ => (![1 / 2 + s, 1 / 2 - s] : Fin 2 → ℝ) i)
      (![1, -1] i) 0 := by
    intro i
    fin_cases i
    · exact ((hasDerivAt_id (0 : ℝ)).const_add (1 / 2)).congr_deriv (by simp)
    · exact ((hasDerivAt_id (0 : ℝ)).const_sub (1 / 2)).congr_deriv (by simp)
  have h := hasDerivAt_crossEntropy (p := fun _ => (![1 / 3, 2 / 3] : Fin 2 → ℝ))
    (q := fun s => ![1 / 2 + s, 1 / 2 - s]) (dp := fun _ => 0) (dq := ![1, -1]) (t := 0)
    (fun i => hasDerivAt_const 0 _) hq (fun i => by fin_cases i <;> norm_num)
  refine h.congr_deriv ?_
  simp [Fin.sum_univ_two]
  norm_num

section Audit

#print axioms hasDerivAt_section_crossEntropy
#print axioms hasDerivAt_crossEntropy_clocks
#print axioms sum_rate_eq_zero
#print axioms hasDerivAt_kl
#print axioms moving_reference_rate

end Audit

/-! Conditional cell/density code rates. The supplied continuity rate is not a
Reynolds theorem; a continuum transport consumer must derive it. -/
/-- p is the dimensionless probability of an actually declared cell. Source and
relative boundary outflow have units probability per declared clock time. -/
theorem cell_code_rate {p : ℝ → ℝ} {source outflow t : ℝ}
    (hp : HasDerivAt p (source - outflow) t) (hpos : 0 < p t) :
    HasDerivAt (fun s => -Real.log (p s)) ((outflow - source) / p t) t := by
  apply (hp.log hpos.ne').neg.congr_deriv
  ring

/-- Along a material trajectory, delta is div_mu(v) + partial_t log(m)
for the declared reference dmu_t = m(t,x) dx. Flux divergence and source are
densities per the same reference. This is conditional on the actual continuity law. -/
theorem density_code_rate {rho : ℝ → ℝ} {rate delta divJ source t : ℝ}
    (hrho : HasDerivAt rho rate t) (hpos : 0 < rho t)
    (balance : rate + rho t * delta + divJ = source) :
    HasDerivAt (fun s => -Real.log (rho s))
      (delta + (divJ - source) / rho t) t := by
  apply (hrho.log hpos.ne').neg.congr_deriv
  field_simp [hpos.ne']
  linarith [balance]

/-! The moving-cell balance supplies a log-content ratio rate.
Probability is separately derived from a nonnegative integrable whole,
its actual total integral Z, and the moving cell inclusion. source(u,y)
already denotes s(u,X(u,y)). A moving Z contributes its own log-rate. -/
section MaterialCellCode
open MeasureTheory Filter Set ContinuousLinearMap
open scoped Topology Interval
theorem affine_cell_log_content_rate
    (rho : ℝ × ℝ → ℝ) (j source : ℝ → ℝ → ℝ)
    (a b da db : ℝ → ℝ) (rt rx dj : ℝ → ℝ → ℝ)
    {t l r : ℝ} {S : Set ℝ} {bound : ℝ → ℝ}
    (hS : S ∈ 𝓝 t) (hlr : l < r) (haPositive : ∀ u ∈ S, 0 < a u)
    (ha : ∀ u ∈ S, HasDerivAt a (da u) u)
    (hb : ∀ u ∈ S, HasDerivAt b (db u) u)
    (hrho : ∀ u ∈ S, ∀ y ∈ uIcc l r, HasFDerivAt rho
      ((fst ℝ ℝ ℝ).smulRight (rt u y) + (snd ℝ ℝ ℝ).smulRight (rx u y))
      (u, a u * y + b u))
    (hj : ∀ u ∈ S, ∀ y ∈ uIcc l r, HasDerivAt (j u) (dj u y) (a u * y + b u))
    (continuity : ∀ u ∈ S, ∀ y ∈ uIcc l r, rt u y + dj u y = source u y)
    (hFmeas : ∀ᶠ u in 𝓝 t, AEStronglyMeasurable
      (fun y => rho (u, a u * y + b u) * a u) (volume.restrict (Ι l r)))
    (hFint : IntervalIntegrable (fun y => rho (t, a t * y + b t) * a t) volume l r)
    (hdFmeas : AEStronglyMeasurable (fun y =>
      (rt t y + rx t y * (da t * y + db t)) * a t + rho (t, a t * y + b t) * da t)
      (volume.restrict (Ι l r)))
    (hbound : ∀ᵐ y ∂volume, y ∈ Ι l r → ∀ u ∈ S,
      ‖(rt u y + rx u y * (da u * y + db u)) * a u + rho (u, a u * y + b u) * da u‖ ≤ bound y)
    (hboundint : IntervalIntegrable bound volume l r)
    (hfluxint : IntervalIntegrable (fun y =>
      dj t y * a t - rx t y * a t * (da t * y + db t) - rho (t, a t * y + b t) * da t)
      volume l r)
    (Z : ℝ) (hZ : 0 < Z)
    (hmass : 0 < ∫ x in a t * l + b t..a t * r + b t, rho (t, x)) :
    HasDerivAt (fun u => -Real.log
      ((∫ x in a u * l + b u..a u * r + b u, rho (u, x)) / Z))
      ((((j t (a t * r + b t) - rho (t, a t * r + b t) * (da t * r + db t)) -
          (j t (a t * l + b t) - rho (t, a t * l + b t) * (da t * l + db t))) -
        (∫ y in l..r, a t * source t y)) /
        (∫ x in a t * l + b t..a t * r + b t, rho (t, x))) t := by
  have ht := Holonics.Transport.ChangingReceiver.affine_cell_transport rho j source a b da db rt rx dj hS hlr haPositive
    ha hb hrho hj continuity hFmeas hFint hdFmeas hbound hboundint hfluxint
  have hd := ((ht.2.div_const Z).log (div_pos hmass hZ).ne').neg
  apply hd.congr_deriv
  field_simp [hmass.ne', hZ.ne']
  ring

/-- Inclusion in an actual nonnegative integrable whole gives both content bounds. -/
theorem interval_content_bounds_of_total
    (f : ℝ → ℝ) (Omega : Set ℝ) (hOmega : MeasurableSet Omega)
    (hfi : IntegrableOn f Omega volume) (hf : ∀ x ∈ Omega, 0 ≤ f x)
    {left right Z : ℝ} (hlr : left ≤ right) (hin : Ioc left right ⊆ Omega)
    (htotal : (∫ x in Omega, f x) = Z) :
    0 ≤ (∫ x in left..right, f x) ∧ (∫ x in left..right, f x) ≤ Z := by
  rw [intervalIntegral.integral_of_le hlr]
  constructor
  · exact setIntegral_nonneg measurableSet_Ioc (fun x hx => hf x (hin hx))
  · rw [← htotal]
    apply setIntegral_mono_set hfi
    · exact (ae_restrict_iff' hOmega).mpr (Filter.Eventually.of_forall hf)
    · exact Filter.Eventually.of_forall hin

/-- The actual source total and material-cell inclusion discharge probability
normalization throughout the declared neighborhood. No p≤1 hypothesis is supplied. -/
theorem affine_cell_probability_code
    (rho : ℝ × ℝ → ℝ) (j source : ℝ → ℝ → ℝ)
    (a b da db : ℝ → ℝ) (rt rx dj : ℝ → ℝ → ℝ)
    {t l r : ℝ} {S : Set ℝ} {bound : ℝ → ℝ}
    (hS : S ∈ 𝓝 t) (hlr : l < r) (haPositive : ∀ u ∈ S, 0 < a u)
    (ha : ∀ u ∈ S, HasDerivAt a (da u) u)
    (hb : ∀ u ∈ S, HasDerivAt b (db u) u)
    (hrho : ∀ u ∈ S, ∀ y ∈ uIcc l r, HasFDerivAt rho
      ((fst ℝ ℝ ℝ).smulRight (rt u y) + (snd ℝ ℝ ℝ).smulRight (rx u y))
      (u, a u * y + b u))
    (hj : ∀ u ∈ S, ∀ y ∈ uIcc l r, HasDerivAt (j u) (dj u y) (a u * y + b u))
    (continuity : ∀ u ∈ S, ∀ y ∈ uIcc l r, rt u y + dj u y = source u y)
    (hFmeas : ∀ᶠ u in 𝓝 t, AEStronglyMeasurable
      (fun y => rho (u, a u * y + b u) * a u) (volume.restrict (Ι l r)))
    (hFint : IntervalIntegrable (fun y => rho (t, a t * y + b t) * a t) volume l r)
    (hdFmeas : AEStronglyMeasurable (fun y =>
      (rt t y + rx t y * (da t * y + db t)) * a t + rho (t, a t * y + b t) * da t)
      (volume.restrict (Ι l r)))
    (hbound : ∀ᵐ y ∂volume, y ∈ Ι l r → ∀ u ∈ S,
      ‖(rt u y + rx u y * (da u * y + db u)) * a u + rho (u, a u * y + b u) * da u‖ ≤ bound y)
    (hboundint : IntervalIntegrable bound volume l r)
    (hfluxint : IntervalIntegrable (fun y =>
      dj t y * a t - rx t y * a t * (da t * y + db t) - rho (t, a t * y + b t) * da t)
      volume l r)
    (Z : ℝ) (hZ : 0 < Z)
    (hmass : 0 < ∫ x in a t * l + b t..a t * r + b t, rho (t, x))
    (Omega : Set ℝ) (hOmega : MeasurableSet Omega)
    (hwholeInt : ∀ u ∈ S, IntegrableOn (fun x => rho (u, x)) Omega volume)
    (hnonneg : ∀ u ∈ S, ∀ x ∈ Omega, 0 ≤ rho (u, x))
    (htotal : ∀ u ∈ S, (∫ x in Omega, rho (u, x)) = Z)
    (hcellIn : ∀ u ∈ S, Ioc (a u * l + b u) (a u * r + b u) ⊆ Omega) :
    (∀ u ∈ S,
      0 ≤ (∫ x in a u * l + b u..a u * r + b u, rho (u, x)) / Z ∧
        (∫ x in a u * l + b u..a u * r + b u, rho (u, x)) / Z ≤ 1) ∧
    0 < (∫ x in a t * l + b t..a t * r + b t, rho (t, x)) / Z ∧
    HasDerivAt (fun u => -Real.log
      ((∫ x in a u * l + b u..a u * r + b u, rho (u, x)) / Z))
      ((((j t (a t * r + b t) - rho (t, a t * r + b t) * (da t * r + db t)) -
          (j t (a t * l + b t) - rho (t, a t * l + b t) * (da t * l + db t))) -
        (∫ y in l..r, a t * source t y)) /
        (∫ x in a t * l + b t..a t * r + b t, rho (t, x))) t := by
  have hbounds : ∀ u ∈ S,
      0 ≤ (∫ x in a u * l + b u..a u * r + b u, rho (u, x)) / Z ∧
        (∫ x in a u * l + b u..a u * r + b u, rho (u, x)) / Z ≤ 1 := by
    intro u hu
    have horder : a u * l + b u ≤ a u * r + b u := by
      have hp := haPositive u hu
      nlinarith
    have bounds := interval_content_bounds_of_total (fun x => rho (u, x)) Omega hOmega
      (hwholeInt u hu) (hnonneg u hu) horder (hcellIn u hu) (htotal u hu)
    exact ⟨div_nonneg bounds.1 hZ.le, (div_le_one hZ).mpr bounds.2⟩
  refine ⟨hbounds, div_pos hmass hZ, ?_⟩
  exact affine_cell_log_content_rate rho j source a b da db rt rx dj hS hlr haPositive
    ha hb hrho hj continuity hFmeas hFint hdFmeas hbound hboundint hfluxint Z hZ hmass

end MaterialCellCode

end Holonics.Physics.Information.CrossEntropyRate
