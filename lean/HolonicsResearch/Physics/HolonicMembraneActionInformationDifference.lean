import Holonics.Physics.InformationDifference
import HolonicsResearch.Foundation.HolonicMembraneActionTransport

/-!
# A membrane-action receiver witnesses the physical information obstruction

The finite cross-entropy face from the membrane-action construction does not determine its
successor action. This source-specific instance stays in the research closure; the generic
receiver-factor obstruction and information identities remain in `Physics/InformationDifference`.
-/

namespace Holonics.Physics.InformationDifference

open Holonics.Foundation.HolonicMembraneActionTransport

/-- The concrete membrane-tail cross-entropy face does not determine the action occurrence. -/
theorem membrane_tail_scalar_does_not_determine_action :
    ¬ ∃ factor : ℝ → Bool, ∀ action,
      action = factor (tailCrossEntropyReceiver.face action) :=
  tailCrossEntropyReceiver_no_identitySuccessorFactor

section Audit

#print axioms membrane_tail_scalar_does_not_determine_action

end Audit

end Holonics.Physics.InformationDifference
