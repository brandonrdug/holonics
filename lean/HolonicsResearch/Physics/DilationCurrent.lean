import Holonics.Physics.ReceiverStressEnergy

/-!
# A conserved stress feeds the dilation current through its trace alone

The record `research/records/2026-10-26_A_GALOIS_GAP_IS_A_MODES_MOMENTUM_AN_ORBITS_GAPS_MULTIPLY_TO_ITS_PRIME_AND_A_TIME_BOUNDARY_IS_THE_PUMPED_MODE.md`
(atlas `gr.dilation-current`) reads the dilation current `D^μ = x_ν T^(μν)` beside the angular
current (`gr.angular-current`, `Holonics.Physics.ReceiverStressEnergy.angularDivergence`): its
divergence is `T^μ_μ + x_ν ∂_μ T^(μν)`, so a conserved stress feeds it through its trace alone.
#410 owes that law; this file proves it in the same finite receiver chart, signature `(−, +, +, +)`,
with the same first-derivative jet `dT i j k = ∂_k T^(i j)`.

[proved-standard; formal-checked] What is proved.

1. **The divergence is the trace plus the force term** (`dilationDivergence_expansion`): the
   product-rule divergence of `D^μ = x_ν T^(μν)` (`∂_μ x^ν = δ^ν_μ`) is
   `T^μ_μ + Σ_ν x_ν Σ_μ ∂_μ T^(μν)` (`stressTrace`).
2. **A conserved stress feeds it through its trace alone** (`dilationDivergence_of_conserved`), and
   **dilation is a symmetry exactly where a conserved stress is traceless**
   (`dilationDivergence_eq_zero_iff`).
3. **What gives the trace** (`perfectFluid_stressTrace`, `radiation_traceless`,
   `radiation_dilation_conserved`): a perfect fluid's trace is `−ρ + 3p`, so radiation (`p = ρ/3`)
   is traceless and its conserved stress keeps dilation; dust (`p = 0`) reads `−ρ`, the rest mass.
4. **The charge at rest** (`dilationCurrent_perfectFluid_time`): a fluid at rest carries dilation
   density `D^0 = −x^0 ρ`, the time read against the energy.

The computational object is the helical pair interaction: the trace is the pairing of the stress
with the metric, the face where the scale square closes or leaves its defect. Of the winding guide's six
general objects this touches the tower thread (the scale action); the helix, the pair, faces and
placement, the cell holonomy and the tube stay attached.

Consumers: the atlas row `gr.dilation-current`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.DilationCurrent

open Holonics.Physics.ReceiverStressEnergy

/-- [definition] The trace `T^μ_μ = η_(μν) T^(μν)` in the receiver chart. -/
def stressTrace (T : Tensor) : ℝ := ∑ mu, ∑ nu, minkowskiMetricComponent mu nu * T mu nu

/-- [definition] The dilation current `D^μ = x_ν T^(μν)`, with `x_ν = η_(νν) x^ν`. -/
def dilationCurrent (x : Index → ℝ) (T : Tensor) (mu : Index) : ℝ :=
  ∑ nu, minkowskiSign nu * x nu * T mu nu

/-- [definition] The product-rule divergence `∂_μ D^μ` from the jet `dT`, with `∂_μ x^ν = δ^ν_μ`. -/
def dilationDivergence (x : Index → ℝ) (T : Tensor) (dT : DerivativeJet) : ℝ :=
  ∑ mu, ∑ nu, (minkowskiSign nu * kronecker mu nu * T mu nu +
    minkowskiSign nu * x nu * dT mu nu mu)

/-- [proved-standard; formal-checked] **The divergence is the trace plus the force term:**
`∂_μ D^μ = T^μ_μ + Σ_ν x_ν Σ_μ ∂_μ T^(μν)`. -/
theorem dilationDivergence_expansion (x : Index → ℝ) (T : Tensor) (dT : DerivativeJet) :
    dilationDivergence x T dT =
      stressTrace T + ∑ nu, minkowskiSign nu * x nu * ∑ mu, dT mu nu mu := by
  have hmetric : ∀ mu nu : Index,
      minkowskiSign nu * kronecker mu nu * T mu nu = minkowskiMetricComponent mu nu * T mu nu := by
    intro mu nu
    by_cases h : mu = nu
    · subst h
      simp [kronecker, minkowskiMetricComponent]
    · simp [kronecker, minkowskiMetricComponent, h]
  unfold dilationDivergence stressTrace
  simp only [Finset.sum_add_distrib, hmetric]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun nu _ => ?_
  rw [Finset.mul_sum]

/-- [proved-standard; formal-checked] **A conserved stress feeds the dilation current through its
trace alone.** -/
theorem dilationDivergence_of_conserved (x : Index → ℝ) (T : Tensor) (dT : DerivativeJet)
    (hcons : ∀ nu, ∑ mu, dT mu nu mu = 0) :
    dilationDivergence x T dT = stressTrace T := by
  rw [dilationDivergence_expansion]
  simp [hcons]

/-- [proved-standard; formal-checked] **Dilation is a symmetry exactly where a conserved stress is
traceless.** -/
theorem dilationDivergence_eq_zero_iff (x : Index → ℝ) (T : Tensor) (dT : DerivativeJet)
    (hcons : ∀ nu, ∑ mu, dT mu nu mu = 0) :
    dilationDivergence x T dT = 0 ↔ stressTrace T = 0 := by
  rw [dilationDivergence_of_conserved x T dT hcons]

/-- [proved-standard; formal-checked] **A perfect fluid's trace is `−ρ + 3p`.** -/
theorem perfectFluid_stressTrace (density pressure : ℝ) :
    stressTrace (perfectFluidTensor density pressure) = -density + 3 * pressure := by
  simp only [stressTrace, Fin.sum_univ_four]
  simp [perfectFluidTensor, minkowskiMetricComponent, minkowskiSign, restObserver]
  ring

/-- [proved-standard; formal-checked] **Radiation, `p = ρ/3`, is traceless.** -/
theorem radiation_traceless (density : ℝ) :
    stressTrace (perfectFluidTensor density (density / 3)) = 0 := by
  rw [perfectFluid_stressTrace]
  ring

/-- [proved-standard; formal-checked] **Conserved radiation keeps dilation.** -/
theorem radiation_dilation_conserved (x : Index → ℝ) (density : ℝ) (dT : DerivativeJet)
    (hcons : ∀ nu, ∑ mu, dT mu nu mu = 0) :
    dilationDivergence x (perfectFluidTensor density (density / 3)) dT = 0 := by
  rw [dilationDivergence_of_conserved x _ dT hcons, radiation_traceless]

/-- [proved-standard; formal-checked] **Dust reads its rest mass:** `p = 0` gives trace `−ρ`. -/
theorem dust_stressTrace (density : ℝ) :
    stressTrace (perfectFluidTensor density 0) = -density := by
  rw [perfectFluid_stressTrace]
  ring

/-- [proved-standard; formal-checked] **The dilation charge of a fluid at rest** is
`D^0 = −x^0 ρ`. -/
theorem dilationCurrent_perfectFluid_time (x : Index → ℝ) (density pressure : ℝ) :
    dilationCurrent x (perfectFluidTensor density pressure) 0 = -(x 0 * density) := by
  simp only [dilationCurrent, Fin.sum_univ_four]
  simp [perfectFluidTensor, minkowskiMetricComponent, minkowskiSign, restObserver]

end Holonics.Physics.DilationCurrent
