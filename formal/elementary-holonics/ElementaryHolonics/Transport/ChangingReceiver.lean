import ElementaryHolonics.Foundation.Lineage
import ElementaryHolonics.Foundation.ReceiverHistoryCompression
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

namespace Soma.Holonics.Transport.ChangingReceiver

open Soma.Holonics

universe u v w a b c

/-- The signed return from a proposed coarse operation on the same occurrence population. -/
def defect {Occurrence A B : Type*} [Sub B]
    (entering : Occurrence → A) (returned : Occurrence → B)
    (coarse : A → B) (occurrence : Occurrence) : B :=
  returned occurrence - coarse (entering occurrence)

/-- Apply that same receiver difference to the complete addressed passage. -/
def passageDefect {X Y A B : Type*} [Sub B]
    (P : AddressedPassage X Y) (before : X → A) (after : Y → B)
    (coarse : A → B) : P.Occurrence → B :=
  defect (before ∘ P.source) (after ∘ P.target) coarse

theorem defect_zero_iff {Occurrence A B : Type*} [AddGroup B]
    (entering : Occurrence → A) (returned : Occurrence → B)
    (coarse : A → B) (occurrence : Occurrence) :
    defect entering returned coarse occurrence = 0 ↔
      returned occurrence = coarse (entering occurrence) := sub_eq_zero

/-- Existence is required only on the actually presented range. The existing theorem retains
the full fibre; its classical existence direction is not an executable decoder construction. -/
theorem passage_transformer_exists_iff {X Y A B : Type*}
    (P : AddressedPassage X Y) (before : X → A) (after : Y → B) :
    Nonempty (ReceiverTransformer (before ∘ P.source) (after ∘ P.target)) ↔
      ∀ left right, before (P.source left) = before (P.source right) →
        after (P.target left) = after (P.target right) :=
  receiverTransformer_exists_iff _ _

/-- Nonlinear composition uses the actual shared middle face, retaining its complete response. -/
theorem passageDefect_comp {X Y Z A B C : Type*} [AddCommGroup C]
    (P : AddressedPassage X Y) (Q : AddressedPassage Y Z)
    (q₀ : X → A) (q₁ : Y → B) (q₂ : Z → C)
    (U : A → B) (V : B → C) (joined : AddressedPassage.Join P Q) :
    passageDefect (Q.comp P) q₀ q₂ (V ∘ U) joined =
      passageDefect Q q₁ q₂ V joined.right +
        (V (q₁ (P.target joined.left)) - V (U (q₀ (P.source joined.left)))) := by
  simp only [passageDefect, defect, Function.comp_apply, AddressedPassage.comp]
  rw [joined.joins]
  abel

/-- Additive coarse transport carries the first defect exactly into the second target chart. -/
theorem passageDefect_comp_additive {X Y Z A B C : Type*}
    [AddCommGroup B] [AddCommGroup C]
    (P : AddressedPassage X Y) (Q : AddressedPassage Y Z)
    (q₀ : X → A) (q₁ : Y → B) (q₂ : Z → C)
    (U : A → B) (V : B →+ C) (joined : AddressedPassage.Join P Q) :
    passageDefect (Q.comp P) q₀ q₂ (V ∘ U) joined =
      passageDefect Q q₁ q₂ V joined.right +
        V (passageDefect P q₀ q₁ U joined.left) := by
  rw [passageDefect_comp P Q q₀ q₁ q₂ U V joined]
  simp [passageDefect, defect, map_sub]

/-- A norm bound is a later receiver of the correlated composition law. It does not replace it. -/
theorem norm_passageDefect_comp_le {X Y Z A B C : Type*}
    [NormedAddCommGroup B] [NormedAddCommGroup C]
    (P : AddressedPassage X Y) (Q : AddressedPassage Y Z)
    (q₀ : X → A) (q₁ : Y → B) (q₂ : Z → C)
    (U : A → B) (V : B → C) (L : ℝ)
    (controlled : ∀ a b, ‖V a - V b‖ ≤ L * ‖a - b‖)
    (joined : AddressedPassage.Join P Q) :
    ‖passageDefect (Q.comp P) q₀ q₂ (V ∘ U) joined‖ ≤
      ‖passageDefect Q q₁ q₂ V joined.right‖ +
        L * ‖passageDefect P q₀ q₁ U joined.left‖ := by
  rw [passageDefect_comp P Q q₀ q₁ q₂ U V joined]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (controlled _ _))

/-- The finite-word theorem is recovered directly from the standing generator descent owner. -/
theorem word_defect_zero {Generator X A : Type*} [AddGroup A]
    (T : Generator → X → X) (U : Generator → A → A) (q : X → A)
    (commutes : ∀ i x, q (T i x) = U i (q x)) (word : List Generator) (x : X) :
    defect q (fun x ↦ q (Millennium.Chronology.transportWord T word x))
      (Millennium.Chronology.transportWord U word) x = 0 := by
  apply (defect_zero_iff _ _ _ _).mpr
  exact Millennium.Chronology.generatorEquivarianceExtendsToEveryTransportWord
    T U q commutes word x

/-- Changing carrier types and changing receiver charts preserve an actual supplied history
when each admitted step square commutes. The trajectories are data of the comparison, not a
new execution owner or an inferred global inverse. -/
theorem changing_history_exact
    {X A : ℕ → Type*} (T : ∀ n, X n → X (n + 1))
    (U : ∀ n, A n → A (n + 1)) (q : ∀ n, X n → A n)
    (fine : ∀ n, X n) (coarse : ∀ n, A n)
    (fine_step : ∀ n, fine (n + 1) = T n (fine n))
    (coarse_step : ∀ n, coarse (n + 1) = U n (coarse n))
    (commutes : ∀ n x, q (n + 1) (T n x) = U n (q n x))
    (initial : q 0 (fine 0) = coarse 0) :
    ∀ n, q n (fine n) = coarse n := by
  intro n
  induction n with
  | zero => exact initial
  | succ n ih => rw [fine_step, coarse_step, commutes, ih]

section MovingLinearChart

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The same signed receiver defect at a differential cut includes chart motion. -/
def rateDefect (chart chartRate : X →L[ℝ] Y) (fineRate : X → X)
    (coarseRate : Y → Y) (state : X) : Y :=
  chartRate state + chart (fineRate state) - coarseRate (chart state)

/-- The actual projected trajectory returns the coarse rate plus its complete defect. -/
theorem moving_receiver_rate
    (chart : ℝ → X →L[ℝ] Y) (state : ℝ → X) (time : ℝ)
    (chartRate : X →L[ℝ] Y) (fineRate : X → X) (coarseRate : Y → Y)
    (hchart : HasDerivAt chart chartRate time)
    (hstate : HasDerivAt state (fineRate (state time)) time) :
    HasDerivAt (fun t ↦ chart t (state t))
      (coarseRate (chart time (state time)) +
        rateDefect (chart time) chartRate fineRate coarseRate (state time)) time := by
  convert hchart.clm_apply hstate using 1
  simp [rateDefect]

end MovingLinearChart

section CorrelatedReturn

/-- An exact translation passage used to exhibit a shared-parameter cancellation. -/
def translationPassage (shift : ℚ) : AddressedPassage ℚ ℚ where
  Occurrence := ℚ
  source := id
  target x := x + shift

/-- The same parameter is retained through both joined passages. Each local discrepancy may
be nonzero, but their composed discrepancy vanishes for every parameter value. -/
theorem opposite_translations_cancel (shift source : ℚ) :
    let P := translationPassage shift
    let Q := translationPassage (-shift)
    let joined : AddressedPassage.Join P Q := ⟨source, source + shift, rfl⟩
    passageDefect (Q.comp P) id id id joined = 0 ∧
      passageDefect P id id id source = shift := by
  simp [passageDefect, defect, translationPassage, AddressedPassage.comp]

end CorrelatedReturn

end Soma.Holonics.Transport.ChangingReceiver

section Audit
open Soma.Holonics.Transport.ChangingReceiver
#print axioms passage_transformer_exists_iff
#print axioms passageDefect_comp
#print axioms passageDefect_comp_additive
#print axioms norm_passageDefect_comp_le
#print axioms word_defect_zero
#print axioms changing_history_exact
#print axioms moving_receiver_rate
#print axioms opposite_translations_cancel
end Audit
