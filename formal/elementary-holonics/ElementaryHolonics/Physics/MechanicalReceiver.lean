import ElementaryHolonics.Physics.ConformationResponse
import ElementaryHolonics.Physics.ConstitutiveModulation

/-!
# Changing-grain receivers of the constitutive conformation passage

[definition] The existing reduced mechanical response supplies the actual finite passage.
The source and target may use different nonzero calibration/scale charts over squared extension.
This is a declared dimensionless explicit-Euler step, not the exact flow of an ODE and not an
automatically energy-decreasing displacement. The source occurrence and oriented displacement
remain in `BoundaryHolon`; only the exterior squared-extension receiver forgets orientation.
-/

noncomputable section

namespace Soma.Holonics.Physics.MechanicalReceiver

open Soma.Holonics
open Soma.Holonics.Physics.ConformationResponse
open Soma.Holonics.Transport.ChangingReceiver
open Soma.Holonics.Millennium.HolonicComplexParametron

/-- The material term is literally the standing coupled-incidence response for the strain
Jacobian `B = 2x`. The complete stiffness additionally retains the geometric/prestress term. -/
theorem conformation_stiffness_joins_coupled_response (k a x : ℝ) :
    tangentStiffness k a x =
      coupledResponse (fun _ _ : Unit ↦ k) (fun _ _ : Unit ↦ 2 * x)
        (fun _ : Unit ↦ 1) () + prestressTerm k a x := by
  rw [tangentStiffness_chain_decomposition]
  simp [materialTerm, coupledResponse, branchDrop]
  ring

/-- The response produces an addressed displacement through the existing boundary-holon owner. -/
def updateHolon (h k a : ℝ) : BoundaryHolon ℝ ℝ where
  Occurrence := ℝ
  source := id
  target := fineUpdate h k a
  receive x := -h * response k a x
  boundary := AddMonoidHom.id ℝ
  returnsBoundary x := by simp [fineUpdate]

/-- A declared scale chart on the squared-extension receiver. -/
def scaledExtension (scale x : ℝ) : ℝ := scale * qmap x

/-- The actual coarse step carries the source and target scale coordinates separately. -/
def scaledCoarseUpdate (beforeScale afterScale h k a y : ℝ) : ℝ :=
  afterScale * coarseUpdate h k a (y / beforeScale)

/-- Changing the receiver chart and changing the constitutive parameters still return an exact
local square. The inverse appears only in the declared nonzero scalar calibration. -/
theorem scaled_update_exact (beforeScale afterScale h k a x : ℝ)
    (nonzero : beforeScale ≠ 0) :
    scaledExtension afterScale (fineUpdate h k a x) =
      scaledCoarseUpdate beforeScale afterScale h k a (scaledExtension beforeScale x) := by
  simp [scaledExtension, scaledCoarseUpdate, fineUpdate_descends, nonzero]

/-- The exact square is a zero defect on the actual addressed displacement occurrence. -/
theorem updateHolon_defect_zero (beforeScale afterScale h k a x : ℝ)
    (nonzero : beforeScale ≠ 0) :
    passageDefect (updateHolon h k a).toHolon.toPassage
      (scaledExtension beforeScale) (scaledExtension afterScale)
      (scaledCoarseUpdate beforeScale afterScale h k a) x = 0 := by
  apply (defect_zero_iff _ _ _ _).mpr
  exact scaled_update_exact beforeScale afterScale h k a x nonzero

/-- The shared changing-history theorem carries arbitrarily changing material parameters,
step size and nonzero receiver scales along the same supplied fine and coarse histories. -/
theorem changing_mechanical_history_exact
    (scale h k a fine coarse : ℕ → ℝ) (nonzero : ∀ n, scale n ≠ 0)
    (fine_step : ∀ n, fine (n + 1) = fineUpdate (h n) (k n) (a n) (fine n))
    (coarse_step : ∀ n, coarse (n + 1) =
      scaledCoarseUpdate (scale n) (scale (n + 1)) (h n) (k n) (a n) (coarse n))
    (initial : scaledExtension (scale 0) (fine 0) = coarse 0) :
    ∀ n, scaledExtension (scale n) (fine n) = coarse n := by
  apply changing_history_exact
    (fun n ↦ fineUpdate (h n) (k n) (a n))
    (fun n ↦ scaledCoarseUpdate (scale n) (scale (n + 1)) (h n) (k n) (a n))
    (fun n ↦ scaledExtension (scale n)) fine coarse fine_step coarse_step
  · intro n x
    exact scaled_update_exact _ _ _ _ _ _ (nonzero n)
  · exact initial

/-- A richer oriented response cannot factor through the same squared-extension receiver.
This is the exact missing distinction, independently of how accurately the coarse step runs. -/
theorem oriented_response_reopens_extension {k a : ℝ} (hk : 0 < k) (ha : 0 < a) :
    ¬ Nonempty (ReceiverTransformer qmap (response k a)) := by
  intro h
  have equal := (receiverTransformer_exists_iff qmap (response k a)).mp h
    1 (-1) (by norm_num [qmap])
  exact response_sign_separates hk ha (by norm_num : (0 : ℝ) < 1) equal

/-- [counterexample] Exact receiver descent does not imply energy descent for a large finite
step. Both fine and coarse passages still agree at this same occurrence. -/
theorem exact_coarse_step_can_increase_energy :
    qmap (fineUpdate 1 1 1 1) = coarseUpdate 1 1 1 (qmap 1) ∧
      energy 1 1 1 = 2 ∧ energy 1 1 (fineUpdate 1 1 1 1) = 50 := by
  norm_num [qmap, fineUpdate, coarseUpdate, response, energy, conformation]

end Soma.Holonics.Physics.MechanicalReceiver

section Audit
open Soma.Holonics.Physics.MechanicalReceiver
#print axioms conformation_stiffness_joins_coupled_response
#print axioms scaled_update_exact
#print axioms updateHolon_defect_zero
#print axioms changing_mechanical_history_exact
#print axioms oriented_response_reopens_extension
#print axioms exact_coarse_step_can_increase_energy
end Audit
