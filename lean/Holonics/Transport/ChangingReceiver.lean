import Holonics.Transport.ChangingReceiver.Defect
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Holonics.Holon.Element
import Holonics.Foundation.Lineage
import Holonics.Foundation.ReceiverHistoryCompression
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Changing receivers retain their addressed transport defect

[definition] This is a composition of the existing addressed-passage and receiver-transformer
owners. The source and target charts may differ. The returned defect belongs to the target
receiver, before any norm or interval face. No new recurrence or physical constitutive law is
introduced. An occurrence can contain a complete changing geometry, material and internal state.

[proved-derived] Serial composition retains the actual joining equality and transports the first
defect through the full second coarse operation. For an additive operation that becomes an
additive chain law. For a nonlinear operation its exact finite difference remains explicit.
The moving linear receiver also retains the derivative of the chart itself.
-/

namespace Holonics.Transport.ChangingReceiver

open Holonics

universe u v w a b c

/-! Kinetic face descent and the complete action of a moving chart/clock.
The chart rate is supplied by moving_receiver_rate; its action term and the
hidden source momentum are retained. This algebra does not assert Lorentz covariance. -/
open Matrix Holonics.HolonCore.KineticFace
section Fibre
variable {Q Y : Type*} {n m : Type*} [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

/-- The induced form belongs to the receiving face alone precisely when it is
constant on the full source fibre. Dynamics require the analogous future criterion. -/
theorem metric_descends_iff (F : Q → Y) (M : Q → Matrix n n ℝ)
    (A : Q → Matrix m n ℝ) :
    Nonempty (Holonics.ReceiverTransformer F (fun q => faceMetric (M q) (A q))) ↔
      ∀ q₁ q₂, F q₁ = F q₂ → faceMetric (M q₁) (A q₁) = faceMetric (M q₂) (A q₂) :=
  Holonics.receiverTransformer_exists_iff _ _

end Fibre
section KineticAction
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
/-- Instantaneous action-rate identity for a moving receiving chart and clock.
The receiving rate is A*(r*v)+c; its Hamiltonian reading includes pi.c.
The unread source momentum and its action pairing are retained explicitly. -/
theorem moving_face_clock_action (M : Matrix n n ℝ) (A : Matrix m n ℝ)
    (hM : M.PosDef) (v : n → ℝ) (c : m → ℝ) (r H : ℝ) :
    (M *ᵥ v) ⬝ᵥ (r • v) - r * H =
      (faceMetric M A *ᵥ (A *ᵥ v)) ⬝ᵥ (A *ᵥ (r • v) + c) -
        (r * H + (faceMetric M A *ᵥ (A *ᵥ v)) ⬝ᵥ c) +
      (M *ᵥ hidden M A v) ⬝ᵥ (r • v) := by
  rw [momentum_split M A hM v, add_dotProduct]
  have pair : (Aᵀ *ᵥ (faceMetric M A *ᵥ (A *ᵥ v))) ⬝ᵥ (r • v) =
      (faceMetric M A *ᵥ (A *ᵥ v)) ⬝ᵥ (A *ᵥ (r • v)) := by
    rw [dotProduct_comm, dotProduct_transpose_mulVec]
  rw [pair, dotProduct_add]
  ring

theorem actual_moving_chart_clock_action
    (M : Matrix n n ℝ) (A : Matrix m n ℝ) (hM : M.PosDef)
    (chart : ℝ → (n → ℝ) →L[ℝ] (m → ℝ))
    (chartRate : (n → ℝ) →L[ℝ] (m → ℝ))
    (state : ℝ → n → ℝ) (clock : ℝ → ℝ) (s r H : ℝ) (v : n → ℝ)
    (hchart : HasDerivAt chart chartRate s)
    (hstate : HasDerivAt state v (clock s)) (hclock : HasDerivAt clock r s)
    (hrep : ∀ x, chart s x = A *ᵥ x) :
    HasDerivAt (fun u => chart u (state (clock u)))
        (A *ᵥ (r • v) + chartRate (state (clock s))) s ∧
      (M *ᵥ v) ⬝ᵥ (r • v) - r * H =
        (faceMetric M A *ᵥ (A *ᵥ v)) ⬝ᵥ
          deriv (fun u => chart u (state (clock u))) s -
          (r * H + (faceMetric M A *ᵥ (A *ᵥ v)) ⬝ᵥ chartRate (state (clock s))) +
        (M *ᵥ hidden M A v) ⬝ᵥ (r • v) := by
  have hc : HasDerivAt (fun u => state (clock u)) (r • v) s :=
    hstate.scomp s hclock
  have hp := moving_receiver_rate chart (fun u => state (clock u)) s chartRate
    (fun _ => r • v) (fun _ => 0) hchart hc
  have hd : HasDerivAt (fun u => chart u (state (clock u)))
      (A *ᵥ (r • v) + chartRate (state (clock s))) s := by
    simpa only [rateDefect, Pi.zero_apply, sub_zero, zero_add, hrep, add_comm] using hp
  refine ⟨hd, ?_⟩
  rw [hd.deriv]
  exact moving_face_clock_action M A hM v (chartRate (state (clock s))) r H

end KineticAction

/-! The actual affine material-cell chart supplies density and relative-current
derivatives to ControlVolume.affine_cell_transport. No integral rate is assumed. -/
section MaterialCellChart
open ContinuousLinearMap
theorem affine_cell_pointwise
    (rho : ℝ × ℝ → ℝ) (j : ℝ → ℝ) (a b : ℝ → ℝ)
    (t y da db rt rx dj source : ℝ)
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t)
    (hrho : HasFDerivAt rho
      ((fst ℝ ℝ ℝ).smulRight rt + (snd ℝ ℝ ℝ).smulRight rx)
      (t, a t * y + b t))
    (hj : HasDerivAt j dj (a t * y + b t))
    (continuity : rt + dj = source) :
    HasDerivAt (fun u => rho (u, a u * y + b u) * a u)
      ((rt + rx * (da * y + db)) * a t + rho (t, a t * y + b t) * da) t ∧
    HasDerivAt (fun z => j (a t * z + b t) -
      rho (t, a t * z + b t) * (da * z + db))
      (dj * a t - rx * a t * (da * y + db) - rho (t, a t * y + b t) * da) y ∧
    ((rt + rx * (da * y + db)) * a t + rho (t, a t * y + b t) * da) +
      (dj * a t - rx * a t * (da * y + db) - rho (t, a t * y + b t) * da) =
      a t * source := by
  have hX : HasDerivAt (fun u => a u * y + b u) (da * y + db) t :=
    (ha.mul_const y).add hb
  have hp := (hasDerivAt_id t).prodMk hX
  have ht := hrho.comp_hasDerivAt t hp
  have ht' : HasDerivAt (fun u => rho (u, a u * y + b u))
      (rt + rx * (da * y + db)) t := by
    simpa [Function.comp_def, smulRight_apply, smul_eq_mul, mul_comm] using ht
  have hx : HasDerivAt (fun z => a t * z + b t) (a t) y := by
    simpa using ((hasDerivAt_id y).const_mul (a t)).add_const (b t)
  have hpX := (hasDerivAt_const y t).prodMk hx
  have hs := hrho.comp_hasDerivAt y hpX
  have hs' : HasDerivAt (fun z => rho (t, a t * z + b t)) (rx * a t) y := by
    simpa [Function.comp_def, smulRight_apply, smul_eq_mul, mul_comm] using hs
  have hw : HasDerivAt (fun z => da * z + db) da y := by
    simpa using ((hasDerivAt_id y).const_mul da).add_const db
  refine ⟨ht'.mul ha, ?_, ?_⟩
  · have hf := (hj.comp y hx).sub (hs'.mul hw)
    apply hf.congr_deriv
    ring
  · rw [← continuity]
    ring

end MaterialCellChart

/-! [agent-inferred] A generic moving-chart content integral belongs
with its chart and clock in ChangingReceiver. It requires no cubical-cell
incidence or cycle-class objects from ControlVolume. Chain rule, dominated
differentiation and FTC give the same exact balance and full hypotheses.
The canonical header receipts show why the former import union was refused
at the fixed RSS cap. No singular trace or hypersurface claim. -/
section MovingMaterialCell
open MeasureTheory Filter Set ContinuousLinearMap
open Holonics.Transport.ChangingReceiver
open scoped Topology Interval
theorem integral_balance_of_local_derivatives
    {F dF : ℝ → ℝ → ℝ} {flux dflux source : ℝ → ℝ}
    {t l r : ℝ} {S : Set ℝ} {bound : ℝ → ℝ}
    (hS : S ∈ 𝓝 t)
    (hFmeas : ∀ᶠ u in 𝓝 t, AEStronglyMeasurable (F u) (volume.restrict (Ι l r)))
    (hFint : IntervalIntegrable (F t) volume l r)
    (hdFmeas : AEStronglyMeasurable (dF t) (volume.restrict (Ι l r)))
    (hbound : ∀ᵐ y ∂volume, y ∈ Ι l r → ∀ u ∈ S, ‖dF u y‖ ≤ bound y)
    (hboundint : IntervalIntegrable bound volume l r)
    (hpointwise : ∀ᵐ y ∂volume, y ∈ Ι l r → ∀ u ∈ S,
      HasDerivAt (fun u => F u y) (dF u y) u)
    (hflux : ∀ y ∈ uIcc l r, HasDerivAt flux (dflux y) y)
    (hfluxint : IntervalIntegrable dflux volume l r)
    (continuity : ∀ y ∈ uIcc l r, dF t y + dflux y = source y) :
    HasDerivAt (fun u => ∫ y in l..r, F u y)
      ((∫ y in l..r, source y) - (flux r - flux l)) t := by
  obtain ⟨hint, hd⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hS hFmeas hFint hdFmeas hbound hboundint hpointwise
  have hftc : (∫ y in l..r, dflux y) = flux r - flux l :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hflux hfluxint
  have hi : (∫ y in l..r, dF t y) + (∫ y in l..r, dflux y) =
      ∫ y in l..r, source y := by
    rw [← intervalIntegral.integral_add hint hfluxint]
    apply intervalIntegral.integral_congr
    exact continuity
  apply hd.congr_deriv
  rw [hftc] at hi
  linarith

theorem affine_cell_transport
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
      volume l r) :
    a t * l + b t < a t * r + b t ∧
    HasDerivAt (fun u => ∫ x in a u * l + b u..a u * r + b u, rho (u, x))
      ((∫ y in l..r, a t * source t y) -
        ((j t (a t * r + b t) - rho (t, a t * r + b t) * (da t * r + db t)) -
          (j t (a t * l + b t) - rho (t, a t * l + b t) * (da t * l + db t)))) t := by
  have ht : t ∈ S := mem_of_mem_nhds hS
  have hp : ∀ u ∈ S, ∀ y ∈ uIcc l r,
      HasDerivAt (fun u => rho (u, a u * y + b u) * a u)
          ((rt u y + rx u y * (da u * y + db u)) * a u + rho (u, a u * y + b u) * da u) u ∧
        HasDerivAt (fun z => j u (a u * z + b u) -
          rho (u, a u * z + b u) * (da u * z + db u))
          (dj u y * a u - rx u y * a u * (da u * y + db u) -
            rho (u, a u * y + b u) * da u) y ∧
        ((rt u y + rx u y * (da u * y + db u)) * a u + rho (u, a u * y + b u) * da u) +
          (dj u y * a u - rx u y * a u * (da u * y + db u) -
            rho (u, a u * y + b u) * da u) = a u * source u y := by
    intro u hu y hy
    exact affine_cell_pointwise rho (j u) a b u y (da u) (db u) (rt u y) (rx u y) (dj u y)
      (source u y) (ha u hu) (hb u hu) (hrho u hu y hy) (hj u hu y hy) (continuity u hu y hy)
  have hdiff : ∀ᵐ y ∂volume, y ∈ Ι l r → ∀ u ∈ S,
      HasDerivAt (fun u => rho (u, a u * y + b u) * a u)
        ((rt u y + rx u y * (da u * y + db u)) * a u + rho (u, a u * y + b u) * da u) u := by
    filter_upwards [] with y
    intro hy u hu
    exact (hp u hu y (uIoc_subset_uIcc hy)).1
  have hd := integral_balance_of_local_derivatives hS hFmeas hFint hdFmeas hbound
    hboundint hdiff (fun y hy => (hp t ht y hy).2.1) hfluxint
    (fun y hy => (hp t ht y hy).2.2)
  have hchange : (fun u => ∫ y in l..r, rho (u, a u * y + b u) * a u) =
      (fun u => ∫ x in a u * l + b u..a u * r + b u, rho (u, x)) := by
    funext u
    rw [intervalIntegral.integral_mul_const]
    simpa only [smul_eq_mul, mul_comm] using
      intervalIntegral.smul_integral_comp_mul_add (fun x => rho (u, x)) (a u) (b u)
  rw [hchange] at hd
  refine ⟨?_, hd⟩
  have hpos := haPositive t ht
  nlinarith

end MovingMaterialCell

end Holonics.Transport.ChangingReceiver

section Audit
open Holonics.Transport.ChangingReceiver
#print axioms passage_transformer_exists_iff
#print axioms passageDefect_comp
#print axioms passageDefect_comp_additive
#print axioms norm_passageDefect_comp_le
#print axioms word_defect_zero
#print axioms changing_history_exact
#print axioms moving_receiver_rate
#print axioms opposite_translations_cancel
end Audit
