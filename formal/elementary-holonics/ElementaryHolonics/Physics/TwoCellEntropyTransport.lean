import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

/-!
# Two-cell constitutive entropy transport

Two positive dimensionless masses exchange an oriented constitutive flux.  The logarithmic
receiver returns the exact entropy production of that transport.  The theorem is an information
and balance identity; it does not identify the masses with a probability section or the flux with a
physical force, heat, or Joule law.
-/

noncomputable section

namespace Soma.Holonics.Physics.TwoCellEntropyTransport

def flux (κ a b : ℝ) : ℝ := κ * (a - b)

def entropy (a b : ℝ) : ℝ := Real.negMulLog a + Real.negMulLog b

theorem entropy_production_nonneg {κ a b : ℝ}
    (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ flux κ a b * (Real.log a - Real.log b) := by
  unfold flux
  by_cases hab : a ≤ b
  · have hlog : Real.log a ≤ Real.log b :=
      Real.strictMonoOn_log.monotoneOn ha hb hab
    have hκdiff : κ * (a - b) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hκ (sub_nonpos.mpr hab)
    exact mul_nonneg_of_nonpos_of_nonpos hκdiff (sub_nonpos.mpr hlog)
  · have hba : b ≤ a := le_of_not_ge hab
    have hlog : Real.log b ≤ Real.log a :=
      Real.strictMonoOn_log.monotoneOn hb ha hba
    have hκdiff : 0 ≤ κ * (a - b) :=
      mul_nonneg hκ (sub_nonneg.mpr hba)
    exact mul_nonneg hκdiff (sub_nonneg.mpr hlog)

theorem hasDerivAt_entropy_of_flux
    (κ : ℝ) (a b : ℝ → ℝ) (t : ℝ)
    (ha : 0 < a t) (hb : 0 < b t)
    (ha' : HasDerivAt a (-flux κ (a t) (b t)) t)
    (hb' : HasDerivAt b (flux κ (a t) (b t)) t) :
    HasDerivAt (fun s ↦ entropy (a s) (b s))
      (flux κ (a t) (b t) * (Real.log (a t) - Real.log (b t))) t := by
  have hA := (Real.hasDerivAt_negMulLog (ne_of_gt ha)).comp t ha'
  have hB := (Real.hasDerivAt_negMulLog (ne_of_gt hb)).comp t hb'
  have h := hA.add hB
  have h' : HasDerivAt (fun s ↦ entropy (a s) (b s))
      ((-Real.log (a t) - 1) * -flux κ (a t) (b t) +
        (-Real.log (b t) - 1) * flux κ (a t) (b t)) t := by
    apply h.congr_of_eventuallyEq
    filter_upwards [] with s
    rfl
  apply h'.congr_deriv
  simp only [flux]
  ring

theorem hasDerivAt_mass_conservation
    (κ : ℝ) (a b : ℝ → ℝ) (t : ℝ)
    (ha' : HasDerivAt a (-flux κ (a t) (b t)) t)
    (hb' : HasDerivAt b (flux κ (a t) (b t)) t) :
    HasDerivAt (fun s ↦ a s + b s) 0 t := by
  have h := ha'.add hb'
  have h' : HasDerivAt (fun s ↦ a s + b s)
      (-flux κ (a t) (b t) + flux κ (a t) (b t)) t := by
    apply h.congr_of_eventuallyEq
    filter_upwards [] with s
    rfl
  apply h'.congr_deriv
  simp only [flux]
  ring

section Audit

#print axioms entropy_production_nonneg
#print axioms hasDerivAt_entropy_of_flux
#print axioms hasDerivAt_mass_conservation

end Audit

end Soma.Holonics.Physics.TwoCellEntropyTransport
