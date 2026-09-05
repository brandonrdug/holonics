import ElementaryHolonics.RH.CriticalChart

/-!
# The actual standard xi flow on the positive half-line

The full theta reflection is applied before the source is decomposed into integer events.
This owner derives the cosine half-line representation of `CriticalChart.Hstd` with absolute
integrability at every real heat time. It does not integrate the divergent individual whole-line
events of `FlowedExplicitFormula`.
-/

noncomputable section

namespace Soma.Holonics.RH.FoldedKernel

open Real Set Filter Topology MeasureTheory Complex
open Soma.Holonics.RH.CriticalChart
open Soma.Holonics.RH.KernelFlow
open Soma.Holonics.RH.HeatKernelPhi

def foldedWeight (t u : ℝ) : ℝ := Real.exp (t * u ^ 2) * Φstd u

def exponentialIntegrand (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  (foldedWeight t u : ℂ) * Complex.exp (I * z * u)

def cosineIntegrand (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  (foldedWeight t u : ℂ) * Complex.cos (z * u)

theorem Φstd_neg (u : ℝ) : Φstd (-u) = Φstd u := by
  simp [Φstd, mul_neg, Φ_neg]

theorem foldedWeight_neg (t u : ℝ) : foldedWeight t (-u) = foldedWeight t u := by
  simp [foldedWeight, Φstd_neg]

theorem exponentialIntegrand_eq (t : ℝ) (z : ℂ) (u : ℝ) :
    exponentialIntegrand t z u =
      Complex.exp (t * u ^ 2) * Complex.exp (I * z * u) * (Φstd u : ℂ) := by
  unfold exponentialIntegrand foldedWeight
  push_cast
  ring

/-- Absolute integrability comes from the actual admissible flowed xi kernel and its critical
coordinate bridge, including the factor two in the change of variables. -/
theorem integrable_exponentialIntegrand (t : ℝ) (z : ℂ) :
    Integrable (exponentialIntegrand t z) := by
  have h := ((ΦK.flow (-t / 4)).integrable_lap (criticalChart z)).comp_mul_left'
    (R := (2 : ℝ)) (by norm_num)
  have hscaled := h.const_mul (1 / 2 : ℂ)
  convert hscaled using 1
  funext u
  rw [lap_flow_two_mul, exponentialIntegrand_eq]
  ring

theorem integrable_exponentialIntegrand_neg (t : ℝ) (z : ℂ) :
    Integrable (fun u ↦ exponentialIntegrand t z (-u)) := by
  simpa using (integrable_exponentialIntegrand t z).comp_mul_left'
    (R := (-1 : ℝ)) (by norm_num)

/-- The two reflected occurrences are combined before the cosine receiver. -/
theorem reflection_sum (t : ℝ) (z : ℂ) (u : ℝ) :
    exponentialIntegrand t z u + exponentialIntegrand t z (-u) =
      2 * cosineIntegrand t z u := by
  simp only [exponentialIntegrand, foldedWeight_neg, Complex.ofReal_neg]
  rw [show I * z * (u : ℂ) = (z * u) * I by ring,
    show I * z * (-(u : ℂ)) = -(z * u) * I by ring,
    ← mul_add, ← Complex.two_cos]
  unfold cosineIntegrand
  ring

theorem integrable_cosineIntegrand (t : ℝ) (z : ℂ) :
    Integrable (cosineIntegrand t z) := by
  have h := ((integrable_exponentialIntegrand t z).add
    (integrable_exponentialIntegrand_neg t z)).const_mul (1 / 2 : ℂ)
  convert h using 1
  funext u
  simp only [Pi.add_apply]
  rw [reflection_sum]
  ring

/-- `Hstd` is the standard positive-half-line cosine integral at every real time. -/
theorem Hstd_eq_integral_positiveHalfLine (t : ℝ) (z : ℂ) :
    Hstd t z = ∫ u in Ioi (0 : ℝ), cosineIntegrand t z u := by
  have hf := integrable_exponentialIntegrand t z
  have hn := integrable_exponentialIntegrand_neg t z
  have hwhole : Hstd t z = (1 / 2 : ℂ) * ∫ u : ℝ, exponentialIntegrand t z u := by
    unfold Hstd
    simp_rw [exponentialIntegrand_eq]
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ))
    hf.integrableOn hf.integrableOn
  have hnegative : (∫ u in Iic (0 : ℝ), exponentialIntegrand t z u) =
      ∫ u in Ioi (0 : ℝ), exponentialIntegrand t z (-u) := by
    simp
  rw [hwhole, ← hsplit, hnegative, ← integral_add hn.integrableOn hf.integrableOn]
  have hsum : (fun u : ℝ ↦ exponentialIntegrand t z (-u) + exponentialIntegrand t z u) =
      (fun u : ℝ ↦ (2 : ℂ) * cosineIntegrand t z u) := by
    funext u
    rw [add_comm, reflection_sum]
  rw [hsum, integral_const_mul]
  ring

#print axioms integrable_exponentialIntegrand
#print axioms reflection_sum
#print axioms integrable_cosineIntegrand
#print axioms Hstd_eq_integral_positiveHalfLine

end Soma.Holonics.RH.FoldedKernel
