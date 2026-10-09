import HolonicsResearch.Zeta.FosterClassHeat

/-!
# The modular scattering scalar and the signed pullback of the actual xi current

The literal scalar is `Lambda(2w-1) / Lambda(2w)`, where `Lambda` is mathlib's
`completedRiemannZeta`. Borthwick, *Spectral Theory on Hyperbolic Surfaces*,
slide 64 (PDF page 64), normalizes the modular scalar as
`sqrt(pi) Gamma(w-1/2)/Gamma(w) zeta(2w-1)/zeta(2w)`:
https://math.dartmouth.edu/~specgeom/Borthwick_slides.pdf . This is the ratio
of the two completed zeta functions. We do not construct the Eisenstein series
or prove its constant-term identification here.

`RiemannXi.riemannXi_eq_classicalProduct` supplies the actual xi bridge, away
from the two endpoints of each pulled-back argument. The xi chart itself needs
only `w != 0, 1` and nonvanishing at both arguments for its log derivative:

`phi'/phi = 1/w - 1/(w-1) + 2 xi'/xi(2w-1) - 2 xi'/xi(2w)`.

The finite current is specifically `FosterClassFlux.comb` instantiated by
`FosterClassHeat.instFosterClassRiemannXi`: the multiplicity-weighted divisor
in the closed disc of radius `R/2` about `1/2`. Its complete remainder is
`e_R = logDeriv xi - C_R`, at the same positive `R` for both arguments. The
consuming identity keeps the polar term and returns `2e_R(2w-1)-2e_R(2w)`.
On the common half-disc chart, the existing Hadamard and product split also
identify this signed residual with the difference of the two tail-product
log derivatives. The smaller `R/8` chart retains the two existing remainder
enclosures separately; it supplies no estimate on cancellation.

This is scalar ratio/current algebra beside `FiniteZeroCurrent` and `ZeroTube`.
Their simple-zero/tracking laws are not invoked or weakened. There is no RH
conclusion, signed estimate inferred from an unsigned one, countable Mayer
operator, or native/HNN acceptance. Refs #146, #32, #62.

Agent-inferred choice: derive the log derivative from the literal ratio and
consume the existing tail product, rather than define a replacement scattering
current to equal the desired answer. This avoids the recorded partial-source
join and dropped-residual failures. The touched winding objects are the helix,
pair, faces/placement and receiver tube cut; cell holonomy and the tower thread
retain their separate laws. The computational object remains the helical pair
interaction; this owner adds its scalar receiving chart only.
-/

noncomputable section

namespace Holonics.Zeta.ModularScatteringResidual

open Complex Metric Set Filter Topology
open Holonics.Zeta.RiemannXi

/-- The literal completed-zeta ratio in the modular scattering normalization. -/
def modularScattering (w : ℂ) : ℂ :=
  completedRiemannZeta (2 * w - 1) / completedRiemannZeta (2 * w)

/-- The xi chart, with its polar factor retained. The Lambda bridge has the
additional excluded point `w = 1/2`; this chart is defined independently there. -/
def xiScatteringChart (w : ℂ) : ℂ :=
  (w / (w - 1)) * (riemannXi (2 * w - 1) / riemannXi (2 * w))

/-- The two polar currents, separate from the finite zero current. -/
def polarCurrent (w : ℂ) : ℂ := 1 / w - 1 / (w - 1)

private theorem pulled_endpoint_exclusions {w : ℂ}
    (hw0 : w ≠ 0) (hwHalf : w ≠ 1 / 2) (hw1 : w ≠ 1) :
    (2 * w - 1 ≠ 0) ∧ (2 * w - 1 ≠ 1) ∧
      (2 * w ≠ 0) ∧ (2 * w ≠ 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    apply hwHalf
    linear_combination h / 2
  · intro h
    apply hw1
    linear_combination h / 2
  · intro h
    apply hw0
    linear_combination h / 2
  · intro h
    apply hwHalf
    linear_combination h / 2

/-- The actual Lambda/xi bridge on its literal chart. No statement about the
totalized values at the excluded endpoints or a meromorphic extension is made. -/
theorem modularScattering_eq_xiScatteringChart {w : ℂ}
    (hw0 : w ≠ 0) (hwHalf : w ≠ 1 / 2) (hw1 : w ≠ 1) :
    modularScattering w = xiScatteringChart w := by
  obtain ⟨hm0, hm1, hp0, hp1⟩ := pulled_endpoint_exclusions hw0 hwHalf hw1
  unfold modularScattering xiScatteringChart
  rw [riemannXi_eq_classicalProduct hm0 hm1,
    riemannXi_eq_classicalProduct hp0 hp1]
  by_cases hΛ : completedRiemannZeta (2 * w) = 0
  · simp [hΛ]
  · field_simp [hw0, sub_ne_zero.mpr hw1, hm0, sub_ne_zero.mpr hm1,
      hp0, sub_ne_zero.mpr hp1, hΛ]
    <;> ring

private theorem completed_eq_gammaR_mul_zeta {s : ℂ}
    (hs0 : s ≠ 0) (hG : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  rw [riemannZeta_def_of_ne_zero hs0]
  field_simp [hG]

/-- The literal ratio uses the actual Riemann zeta, with the Gamma_R factors
kept. In Gamma_R's definition their ratio is Borthwick's gamma prefactor.
Nonvanishing of those gamma factors is explicit; no arbitrary named function
is being identified with zeta. -/
theorem modularScattering_eq_gammaR_zeta {w : ℂ}
    (hw0 : w ≠ 0) (hwHalf : w ≠ 1 / 2) (hw1 : w ≠ 1)
    (hGm : Gammaℝ (2 * w - 1) ≠ 0) (hGp : Gammaℝ (2 * w) ≠ 0) :
    modularScattering w =
      (Gammaℝ (2 * w - 1) / Gammaℝ (2 * w)) *
        (riemannZeta (2 * w - 1) / riemannZeta (2 * w)) := by
  obtain ⟨hm0, _, hp0, _⟩ := pulled_endpoint_exclusions hw0 hwHalf hw1
  unfold modularScattering
  rw [completed_eq_gammaR_mul_zeta hm0 hGm,
    completed_eq_gammaR_mul_zeta hp0 hGp]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Entire differentiability supplies the factor `2` from the argument map.
This chain-rule identity uses the actual `riemannXi`, including its continuation. -/
theorem logDeriv_xi_two_mul_sub (a w : ℂ) :
    logDeriv (fun v : ℂ => riemannXi (2 * v - a)) w =
      2 * logDeriv riemannXi (2 * w - a) := by
  have ha : HasDerivAt (fun v : ℂ => 2 * v - a) 2 w := by
    simpa using ((hasDerivAt_id w).const_mul 2).sub_const a
  have hξ : HasDerivAt riemannXi (deriv riemannXi (2 * w - a)) (2 * w - a) :=
    (differentiable_riemannXi (2 * w - a)).hasDerivAt
  have hd : HasDerivAt (fun v : ℂ => riemannXi (2 * v - a))
      (deriv riemannXi (2 * w - a) * 2) w := by
    simpa only [Function.comp_def] using hξ.comp w ha
  rw [logDeriv_apply, hd.deriv, logDeriv_apply]
  ring

/-- Genuine logarithmic differentiation of the xi ratio. The xi-chart domain
excludes `0,1` and both zero fibres, without inheriting Lambda's `1/2` exclusion. -/
theorem logDeriv_xiScatteringChart {w : ℂ}
    (hw0 : w ≠ 0) (hw1 : w ≠ 1)
    (hξm : riemannXi (2 * w - 1) ≠ 0) (hξp : riemannXi (2 * w) ≠ 0) :
    logDeriv xiScatteringChart w = polarCurrent w +
      2 * logDeriv riemannXi (2 * w - 1) - 2 * logDeriv riemannXi (2 * w) := by
  have hwSub : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have hdmInner : DifferentiableAt ℂ (fun v : ℂ => 2 * v - 1) w :=
    (((hasDerivAt_id w).const_mul 2).sub_const 1).differentiableAt
  have hdpInner : DifferentiableAt ℂ (fun v : ℂ => 2 * v) w :=
    ((hasDerivAt_id w).const_mul 2).differentiableAt
  have hdmXi : DifferentiableAt ℂ riemannXi (2 * w - 1) :=
    differentiable_riemannXi (2 * w - 1)
  have hdpXi : DifferentiableAt ℂ riemannXi (2 * w) :=
    differentiable_riemannXi (2 * w)
  have hdm : DifferentiableAt ℂ (fun v : ℂ => riemannXi (2 * v - 1)) w := by
    simpa only [Function.comp_def] using hdmXi.comp w hdmInner
  have hdp : DifferentiableAt ℂ (fun v : ℂ => riemannXi (2 * v)) w := by
    simpa only [Function.comp_def] using hdpXi.comp w hdpInner
  have hdpolar : DifferentiableAt ℂ (fun v : ℂ => v / (v - 1)) w :=
    differentiableAt_id.div (differentiableAt_id.sub_const 1) hwSub
  have hpolar : logDeriv (fun v : ℂ => v / (v - 1)) w = polarCurrent w := by
    rw [logDeriv_div (f := fun v : ℂ => v) (g := fun v : ℂ => v - 1)
      w hw0 hwSub differentiableAt_id (differentiableAt_id.sub_const 1)]
    rw [logDeriv_id']
    unfold polarCurrent
    have hdsub : HasDerivAt (fun v : ℂ => v - 1) 1 w := by
      simpa only [id_eq] using (hasDerivAt_id w).sub_const 1
    rw [logDeriv_apply, hdsub.deriv]
  unfold xiScatteringChart
  rw [logDeriv_mul (f := fun v : ℂ => v / (v - 1))
    (g := fun v : ℂ => riemannXi (2 * v - 1) / riemannXi (2 * v)) w
    (div_ne_zero hw0 hwSub) (div_ne_zero hξm hξp) hdpolar (hdm.div hdp hξp),
    logDeriv_div (f := fun v : ℂ => riemannXi (2 * v - 1))
      (g := fun v : ℂ => riemannXi (2 * v)) w hξm hξp hdm hdp,
    hpolar, logDeriv_xi_two_mul_sub 1 w]
  have hp := logDeriv_xi_two_mul_sub 0 w
  simp only [sub_zero] at hp
  rw [hp]
  ring

/-- The literal completed-zeta scalar has the same log derivative on the
common chart. Equality in a neighborhood, not just at the one point, is used. -/
theorem logDeriv_modularScattering {w : ℂ}
    (hw0 : w ≠ 0) (hwHalf : w ≠ 1 / 2) (hw1 : w ≠ 1)
    (hξm : riemannXi (2 * w - 1) ≠ 0) (hξp : riemannXi (2 * w) ≠ 0) :
    logDeriv modularScattering w = polarCurrent w +
      2 * logDeriv riemannXi (2 * w - 1) - 2 * logDeriv riemannXi (2 * w) := by
  have hev : modularScattering =ᶠ[𝓝 w] xiScatteringChart := by
    filter_upwards [eventually_ne_nhds hw0, eventually_ne_nhds hwHalf,
      eventually_ne_nhds hw1] with v hv0 hvHalf hv1
    exact modularScattering_eq_xiScatteringChart hv0 hvHalf hv1
  rw [(logDeriv_congr_nhds hev).eq_of_nhds]
  exact logDeriv_xiScatteringChart hw0 hw1 hξm hξp

/-- The actual finite xi divisor current, with one positive cutoff. -/
def xiFiniteCurrent {R : ℝ} (hR : 0 < R) (s : ℂ) : ℂ :=
  FosterClassFlux.comb (f := riemannXi) hR s

/-- The complete error of that actual finite current. -/
def xiCurrentRemainder {R : ℝ} (hR : 0 < R) (s : ℂ) : ℂ :=
  logDeriv riemannXi s - xiFiniteCurrent hR s

/-- The same finite divisor is read at both pulled-back arguments, with its
opposite signs and the separate polar current. -/
def finiteScatteringCurrent {R : ℝ} (hR : 0 < R) (w : ℂ) : ℂ :=
  polarCurrent w + 2 * xiFiniteCurrent hR (2 * w - 1) -
    2 * xiFiniteCurrent hR (2 * w)

/-- The actual xi-chart derivative minus the actual finite-current reading is
the complete signed pullback. This is a consuming theorem, not its definition. -/
theorem xiScattering_current_residual {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw0 : w ≠ 0) (hw1 : w ≠ 1)
    (hξm : riemannXi (2 * w - 1) ≠ 0) (hξp : riemannXi (2 * w) ≠ 0) :
    logDeriv xiScatteringChart w - finiteScatteringCurrent hR w =
      2 * xiCurrentRemainder hR (2 * w - 1) -
        2 * xiCurrentRemainder hR (2 * w) := by
  rw [logDeriv_xiScatteringChart hw0 hw1 hξm hξp]
  unfold finiteScatteringCurrent xiCurrentRemainder
  ring

/-- The literal Lambda scalar consumes the same finite xi current on the
common chart; the Lambda endpoint exclusions remain explicit. -/
theorem modularScattering_current_residual {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw0 : w ≠ 0) (hwHalf : w ≠ 1 / 2) (hw1 : w ≠ 1)
    (hξm : riemannXi (2 * w - 1) ≠ 0) (hξp : riemannXi (2 * w) ≠ 0) :
    logDeriv modularScattering w - finiteScatteringCurrent hR w =
      2 * xiCurrentRemainder hR (2 * w - 1) -
        2 * xiCurrentRemainder hR (2 * w) := by
  rw [logDeriv_modularScattering hw0 hwHalf hw1 hξm hξp]
  unfold finiteScatteringCurrent xiCurrentRemainder
  ring

/-- The complete remainder is exactly half the existing Foster tail-product
log derivative, on the half disc and off the xi zeros. This consumes the actual
Hadamard equality and the finite/tail split used by the current enclosure. -/
theorem xiCurrentRemainder_eq_tail {R : ℝ} (hR : 0 < R) {s : ℂ}
    (hs : s ∈ ball (1 / 2 : ℂ) (R / 2)) (hξ : riemannXi s ≠ 0) :
    xiCurrentRemainder hR s =
      logDeriv (FosterClassSplit.tail (f := riemannXi) hR) s / 2 := by
  have hm := FosterClassSplit.mult_eq_zero_of_ne_zero (f := riemannXi) hξ
  have hG := FosterClassHadamard.G_eq_zero (f := riemannXi) hξ
  unfold FosterClassHadamard.G at hG
  rw [FosterClassProduct.logDeriv_P (f := riemannXi) hm,
    FosterClassSplit.tsum_tank_split (f := riemannXi) hR hs,
    FosterClassSplit.sum_tank_T (f := riemannXi) hR s] at hG
  unfold xiCurrentRemainder xiFiniteCurrent
  rw [FosterClassFlux.comb_eq_tankSum (f := riemannXi) hR hξ]
  linear_combination hG / 2

/-- On the common transformed half-disc chart, the literal scattering-current
residual is the signed difference of the existing tail-product currents. Both
argument domains and the single cutoff are retained. -/
theorem modularScattering_current_residual_eq_tail {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw0 : w ≠ 0) (hwHalf : w ≠ 1 / 2) (hw1 : w ≠ 1)
    (hξm : riemannXi (2 * w - 1) ≠ 0) (hξp : riemannXi (2 * w) ≠ 0)
    (hm : 2 * w - 1 ∈ ball (1 / 2 : ℂ) (R / 2))
    (hp : 2 * w ∈ ball (1 / 2 : ℂ) (R / 2)) :
    logDeriv modularScattering w - finiteScatteringCurrent hR w =
      logDeriv (FosterClassSplit.tail (f := riemannXi) hR) (2 * w - 1) -
        logDeriv (FosterClassSplit.tail (f := riemannXi) hR) (2 * w) := by
  rw [modularScattering_current_residual hR hw0 hwHalf hw1 hξm hξp,
    xiCurrentRemainder_eq_tail hR hm hξm, xiCurrentRemainder_eq_tail hR hp hξp]
  ring

/-- The existing current enclosures pulled back to both arguments. This is a
pair of unsigned enclosures at the declared common `R/8` chart, and does not
claim a new signed cancellation bound or a converse bound on either piece. -/
theorem xiCurrentRemainder_pullback_enclosures {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hm : 2 * w - 1 ∈ closedBall (1 / 2 : ℂ) (R / 8))
    (hp : 2 * w ∈ closedBall (1 / 2 : ℂ) (R / 8))
    (hξm : riemannXi (2 * w - 1) ≠ 0) (hξp : riemannXi (2 * w) ≠ 0) :
    (‖xiCurrentRemainder hR (2 * w - 1)‖ ≤
      2 * ‖(2 * w - 1) - 1 / 2‖ * FosterClassSplit.tailInvSq riemannXi R) ∧
    (‖xiCurrentRemainder hR (2 * w)‖ ≤
      2 * ‖2 * w - 1 / 2‖ * FosterClassSplit.tailInvSq riemannXi R) := by
  constructor
  · exact FosterClassFlux.norm_logDeriv_sub_comb_le (f := riemannXi) hR hm hξm
  · exact FosterClassFlux.norm_logDeriv_sub_comb_le (f := riemannXi) hR hp hξp

end Holonics.Zeta.ModularScatteringResidual

#print axioms Holonics.Zeta.ModularScatteringResidual.modularScattering_eq_xiScatteringChart
#print axioms Holonics.Zeta.ModularScatteringResidual.modularScattering_eq_gammaR_zeta
#print axioms Holonics.Zeta.ModularScatteringResidual.logDeriv_xi_two_mul_sub
#print axioms Holonics.Zeta.ModularScatteringResidual.logDeriv_xiScatteringChart
#print axioms Holonics.Zeta.ModularScatteringResidual.logDeriv_modularScattering
#print axioms Holonics.Zeta.ModularScatteringResidual.xiScattering_current_residual
#print axioms Holonics.Zeta.ModularScatteringResidual.modularScattering_current_residual
#print axioms Holonics.Zeta.ModularScatteringResidual.xiCurrentRemainder_eq_tail
#print axioms Holonics.Zeta.ModularScatteringResidual.modularScattering_current_residual_eq_tail
#print axioms Holonics.Zeta.ModularScatteringResidual.xiCurrentRemainder_pullback_enclosures
