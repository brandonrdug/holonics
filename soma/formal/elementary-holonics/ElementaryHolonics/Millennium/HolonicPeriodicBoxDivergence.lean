import ElementaryHolonics.Millennium.HolonicConnectionCurvature
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# The periodic box divergence law in every dimension

On the unit box of `ℝⁿ⁺¹` the integral of the divergence of a `C¹` one-periodic family of
component functions vanishes: Mathlib's divergence theorem returns the two faces in each
coordinate direction, and one-periodicity identifies the front face with the back face.  This is
the `n`-dimensional owner of the three-dimensional cube law used by the fluid line, stated on the
connection base `Base (n+1) = Fin (n+1) → ℝ` so the gauge line can spend it.
-/

noncomputable section

open Set MeasureTheory

namespace Soma.Holonics.Millennium.HolonicPeriodicBoxDivergence

open Soma.Holonics.Millennium.HolonicConnectionCurvature

variable {n : ℕ}

/-- The unit box of the base. -/
def unitBox (n : ℕ) : Set (Base n) := Icc (0 : Base n) (fun _ => 1)

/-- One-periodicity of a function on the base. -/
def IsOnePeriodicBase {α : Sort*} (f : Base n → α) : Prop :=
  ∀ x i, f (x + Pi.single i 1) = f x

theorem insertNth_one_eq_insertNth_zero_add_single (i : Fin (n + 1)) (y : Fin n → ℝ) :
    (i.insertNth (1 : ℝ) y : Fin (n + 1) → ℝ) =
      (i.insertNth (0 : ℝ) y : Fin (n + 1) → ℝ) + Pi.single i 1 := by
  funext j
  refine Fin.succAboveCases i ?_ ?_ j
  · simp [Fin.insertNth_apply_same]
  · intro k
    simp [Fin.insertNth_apply_succAbove]

/-- **The periodic box divergence law.**  For `C¹` one-periodic components `f i` on `ℝⁿ⁺¹`,
`∫_box Σ_i ∂_i f_i = 0`. -/
theorem integral_divergence_unitBox_eq_zero
    (f : Fin (n + 1) → Base (n + 1) → ℝ)
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (hper : ∀ i, IsOnePeriodicBase (f i)) :
    ∫ x in unitBox (n + 1), ∑ i, fderiv ℝ (f i) x (Pi.single i 1) = 0 := by
  have hcont : ∀ i, ContinuousOn (f i) (Icc (0 : Base (n + 1)) (fun _ => 1)) :=
    fun i => (hf i).continuous.continuousOn
  have hdiff : ∀ x ∈ (Set.pi univ fun _ : Fin (n + 1) => Ioo (0 : ℝ) 1) \ (∅ : Set (Base (n + 1))),
      ∀ i, HasFDerivAt (f i) (fderiv ℝ (f i) x) x :=
    fun x _ i => ((hf i).differentiable (by norm_num) x).hasFDerivAt
  have hint : IntegrableOn (fun x => ∑ i, fderiv ℝ (f i) x (Pi.single i 1))
      (Icc (0 : Base (n + 1)) (fun _ => 1)) := by
    have hc : Continuous fun x => ∑ i, fderiv ℝ (f i) x (Pi.single i 1) := by
      apply continuous_finsetSum
      intro i _
      exact ((hf i).continuous_fderiv_apply (by norm_num)).comp
        (continuous_id.prodMk continuous_const)
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable'
    (0 : Base (n + 1)) (fun _ => (1 : ℝ)) (fun _ => zero_le_one) f (fun i x => fderiv ℝ (f i) x)
    (∅ : Set (Base (n + 1))) (by simp) hcont hdiff hint
  unfold unitBox
  rw [hdiv]
  apply Finset.sum_eq_zero
  intro i _
  apply sub_eq_zero.mpr
  apply setIntegral_congr_fun measurableSet_Icc
  intro y _
  show f i (i.insertNth 1 y) = f i (i.insertNth 0 y)
  rw [insertNth_one_eq_insertNth_zero_add_single]
  exact hper i (i.insertNth 0 y) i

section Audit

#print axioms integral_divergence_unitBox_eq_zero

end Audit

end Soma.Holonics.Millennium.HolonicPeriodicBoxDivergence
