import Holonics.HNN.ChainedBalance
import HolonicsResearch.HNN.MoveDirection

/-!
# The deposition's work at held momentum in the chained balance

[proved-derived; formal-checked] The join of the reception carry's chained balance
(`Holonics/HNN/ChainedBalance`, record B §2.3) to the deposit record's held-momentum law (#284,
`HolonicsResearch/HNN/MoveDirection` §10). The commit under the carry reads the deposit's work on a
contact's rate at held momentum (`PowerForm::held`, `WordBalance::commit_held`): the mass moves from
`C` to `C′ = C + F` and the rate solves `C′ w′ = C w`.

1. **The storage work** (`held_deposition_work`): `½⟨w′, C′ w′⟩ − ½⟨w, C w⟩ =
   −½⟨w′, F w′⟩ − ½⟨w − w′, C(w − w′)⟩`, for any symmetric `C` and `F`
   (`MoveDirection.held_momentum_loss`). No invertibility of `C′` is assumed, so the identity
   holds wherever the hold exists, the singular case included
   (`ChainedBalance.hold_iff_kernel_free`).
2. **Accretion does no positive work** (`held_deposition_nonpos`, from
   `MoveDirection.held_momentum_dissipates`): for `C ⪰ 0` and `F ⪰ 0`.
3. **The stronger reading holds under accretion** (`reception_within_loss_of_accretion`): when
   every deposit on the carried rates accretes and the ingest only emits
   (`ChainedBalance.ingest_nonpos`), `deposition + ingest ≤ L` at that reception, and the end
   storage is within the interior, the imposed storage, the ports, the split and the bound
   (`ChainedBalance.reception_within_loss`). A deposit that lowers a mass is not covered: its held
   work can be positive, and the chained balance then holds only in its dissipative form.

The ingest's sign is proved over `ℚ` (`HNN/Ring.reference_lift_work_nonpos`) and the held mass's
over `ℝ` (`MoveDirection`); here the ingest enters through its sign.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.HeldDeposition

open Matrix
open Holonics.HNN.MoveDirection (held_momentum_loss held_momentum_dissipates)

variable {n : Type*} [Fintype n]

/-- [proved-derived; formal-checked] **The deposit's work on a held rate** (`PowerForm::held`). -/
theorem held_deposition_work (C F : Matrix n n ℝ) (hC : Cᵀ = C) (w w' : n → ℝ)
    (hheld : C *ᵥ w = (C + F) *ᵥ w') :
    w' ⬝ᵥ ((C + F) *ᵥ w') / 2 - w ⬝ᵥ (C *ᵥ w) / 2 =
      -(w' ⬝ᵥ (F *ᵥ w') / 2) - (w - w') ⬝ᵥ (C *ᵥ (w - w')) / 2 := by
  have h := held_momentum_loss C F hC w w' hheld
  linarith

/-- [proved-derived; formal-checked] **Accretion at held momentum does no positive work.** -/
theorem held_deposition_nonpos {C F : Matrix n n ℝ} (hC : C.PosSemidef) (hF : F.PosSemidef)
    (w w' : n → ℝ) (hheld : C *ᵥ w = (C + F) *ᵥ w') :
    w' ⬝ᵥ ((C + F) *ᵥ w') / 2 - w ⬝ᵥ (C *ᵥ w) / 2 ≤ 0 := by
  have h := held_momentum_dissipates hC hF w w' hheld
  linarith

/-- [proved-derived; formal-checked] **The stronger reading under accretion.** At a reception
whose deposition is the held work of an accreting deposit and whose ingest only emits, the work
between the words is within the next word's loss, and the end storage is within the interior, the
imposed storage, the ports, the split and the residual's bound. -/
theorem reception_within_loss_of_accretion {C F : Matrix n n ℝ} (hC : C.PosSemidef)
    (hF : F.PosSemidef) (w w' : n → ℝ) (hheld : C *ᵥ w = (C + F) *ᵥ w')
    {Py ing imp spl L Pt res b Eopen Eend : ℝ}
    (hopen : Eopen = Py + (w' ⬝ᵥ ((C + F) *ᵥ w') / 2 - w ⬝ᵥ (C *ᵥ w) / 2) + ing + imp)
    (hend : Eend = Eopen - spl - L + Pt + res) (hL : 0 ≤ L) (hres : |res| ≤ b) (hing : ing ≤ 0) :
    (w' ⬝ᵥ ((C + F) *ᵥ w') / 2 - w ⬝ᵥ (C *ᵥ w) / 2) + ing ≤ L ∧
      Eend ≤ Py + imp - spl + Pt + b :=
  Holonics.HNN.ChainedBalance.reception_within_loss hopen hend hL hres
    (held_deposition_nonpos hC hF w w' hheld) hing

section Audit

#print axioms held_deposition_work
#print axioms held_deposition_nonpos
#print axioms reception_within_loss_of_accretion

end Audit

end Holonics.HNN.HeldDeposition
