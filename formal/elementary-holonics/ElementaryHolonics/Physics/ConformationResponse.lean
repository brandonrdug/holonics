import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import ElementaryHolonics.Foundation.TransportWord

/-!
# A changing constitutive geometry and its descended response

This file is a bounded mechanical chart for a reusable Holonic pattern.  The scalar conformation
`c(q) = a + q²` is the simplest exact model in which a transverse coordinate has zero first-order
strain at `q = 0` while the complete energy still has positive tangent stiffness.  The chart is
mechanical and dimensionless; it is not a calibrated protein or biological force law.

The same construction also exhibits dynamic coarse graining.  The fine update on `q` descends
through the even receiver `q ↦ q²` to an update on `y = q²`.  The descended receiver intentionally
forgets the sign, while the oriented force retains it, so the quotient scope is explicit.
All statements are exact over `ℝ`; no sampler, learner, numerical approximation, or physical
calibration is used.
-/

noncomputable section

namespace Soma.Holonics.Physics.ConformationResponse

open Soma.Holonics.Millennium.Chronology

/-! ## The scalar constitutive chart -/

/-- The changing scalar conformation (a reduced transverse-strain chart). -/
def conformation (a q : ℝ) : ℝ := a + q ^ 2

/-- Quadratic energy of the constitutive conformation. -/
def energy (k a q : ℝ) : ℝ := k / 2 * (conformation a q) ^ 2

/-- The energy-gradient response, including changing strain geometry. The restoring force in
the unit-mobility update is its negative. -/
def response (k a q : ℝ) : ℝ := 2 * k * q * (a + q ^ 2)

/-- The tangent stiffness (the second derivative of the energy). -/
def tangentStiffness (k a q : ℝ) : ℝ := 2 * k * (a + 3 * q ^ 2)

/-- The material/metric contribution to tangent stiffness. -/
def materialTerm (k q : ℝ) : ℝ := k * (2 * q) ^ 2

/-- The prestress contribution to tangent stiffness. -/
def prestressTerm (k a q : ℝ) : ℝ := 2 * k * (a + q ^ 2)

/-- The scalar chain rule for the conformation coordinate. -/
theorem hasDerivAt_conformation (a q : ℝ) :
    HasDerivAt (fun t : ℝ ↦ conformation a t) (2 * q) q := by
  have hpow : HasDerivAt (fun t : ℝ ↦ t ^ 2) (2 * q) q := by
    simpa using hasDerivAt_pow 2 q
  have hadd := (hasDerivAt_const q a).add hpow
  have hadd' := hadd.congr_deriv (show 0 + 2 * q = 2 * q by ring)
  apply hadd'.congr_of_eventuallyEq
  filter_upwards [] with t
  simp [conformation]

/-- The energy derivative is the complete response `2 k q (a + q²)`. -/
theorem hasDerivAt_energy (k a q : ℝ) :
    HasDerivAt (fun t : ℝ ↦ energy k a t) (response k a q) q := by
  have hc := hasDerivAt_conformation a q
  have h := (hc.pow 2).const_mul (k / 2)
  have hderiv : k / 2 * (2 * conformation a q ^ (2 - 1) * (2 * q)) =
      response k a q := by
    norm_num [response, conformation]
    ring
  have h' := h.congr_deriv hderiv
  simpa [energy] using h'

/-- Differentiating the response gives the exact tangent stiffness. -/
theorem hasDerivAt_response (k a q : ℝ) :
    HasDerivAt (fun t : ℝ ↦ response k a t) (tangentStiffness k a q) q := by
  unfold response tangentStiffness
  have hc := hasDerivAt_conformation a q
  have hprod : HasDerivAt (fun t : ℝ ↦ t * conformation a t)
      (conformation a q + q * (2 * q)) q := by
    have hprod0 := (hasDerivAt_id q).mul hc
    have hprod1 : HasDerivAt (id * (fun t : ℝ ↦ conformation a t))
        (conformation a q + q * (2 * q)) q := by
      simpa only [one_mul, id_eq] using hprod0
    apply hprod1.congr_of_eventuallyEq
    filter_upwards [] with t
    simp [conformation]
  have h := hprod.const_mul (2 * k)
  have hderiv : (2 * k) * (conformation a q + q * (2 * q)) =
      tangentStiffness k a q := by
    change (2 * k) * ((a + q ^ 2) + q * (2 * q)) = 2 * k * (a + 3 * q ^ 2)
    ring
  have h' := h.congr_deriv hderiv
  have h'' : HasDerivAt (fun y : ℝ ↦ 2 * k * (y * conformation a y))
      (2 * k * (a + 3 * q ^ 2)) q := by
    apply h'.congr_deriv
    simp [tangentStiffness]
  simpa [conformation, mul_assoc] using h''

/-- Tangent stiffness splits into the changing-material term and the prestress term. -/
theorem tangentStiffness_chain_decomposition (k a q : ℝ) :
    tangentStiffness k a q = materialTerm k q + prestressTerm k a q := by
  simp only [tangentStiffness, materialTerm, prestressTerm]
  ring

/-- At the undeformed transverse coordinate the first-order force vanishes. -/
theorem response_at_zero (k a : ℝ) : response k a 0 = 0 := by
  simp [response]

/-- Positive material and prestress parameters give positive stiffness at zero transverse
displacement. The strain there is the retained prestress parameter `a`, not zero. -/
theorem tangentStiffness_at_zero_pos {k a : ℝ} (hk : 0 < k) (ha : 0 < a) :
    0 < tangentStiffness k a 0 := by
  simp [tangentStiffness]
  positivity

/-- The response is odd in the oriented transverse coordinate. -/
theorem response_neg (k a q : ℝ) : response k a (-q) = -response k a q := by
  simp [response]

/-- With positive parameters, opposite nonzero orientations have distinct responses. -/
theorem response_sign_separates {k a q : ℝ} (hk : 0 < k) (ha : 0 < a) (hq : 0 < q) :
    response k a q ≠ response k a (-q) := by
  have hpos : 0 < response k a q := by
    simp [response]
    positivity
  rw [response_neg]
  linarith

/-! ## Fine update and squared-extension descent -/

/-- One explicit Euler passage for the exact response. -/
def fineUpdate (h k a q : ℝ) : ℝ := q - h * response k a q

/-- The squared-extension receiver, `qmap q = q²`. -/
def qmap (q : ℝ) : ℝ := q ^ 2

/-- The coarse update induced by the fine update on the squared extension. -/
def coarseUpdate (h k a y : ℝ) : ℝ := y * (1 - 2 * h * k * (a + y)) ^ 2

/-- The fine update commutes exactly with the squared-extension receiver. -/
theorem fineUpdate_descends (h k a q : ℝ) :
    qmap (fineUpdate h k a q) = coarseUpdate h k a (qmap q) := by
  simp [qmap, fineUpdate, coarseUpdate, response]
  ring

/-- Generator equivariance extends the one-step descent to every ordered update word. -/
theorem fineUpdate_word_descends (h k a : ℝ) (w : List Unit) (q : ℝ) :
    qmap (transportWord (fun _ : Unit ↦ fineUpdate h k a) w q) =
      transportWord (fun _ : Unit ↦ coarseUpdate h k a) w (qmap q) := by
  apply generatorEquivarianceExtendsToEveryTransportWord
  intro i x
  exact fineUpdate_descends h k a x

end Soma.Holonics.Physics.ConformationResponse

section Audit

open Soma.Holonics.Physics.ConformationResponse

#print axioms hasDerivAt_conformation
#print axioms hasDerivAt_energy
#print axioms hasDerivAt_response
#print axioms tangentStiffness_chain_decomposition
#print axioms tangentStiffness_at_zero_pos
#print axioms response_sign_separates
#print axioms fineUpdate_descends
#print axioms fineUpdate_word_descends

end Audit
