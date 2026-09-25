import Holonics.Foundation.CausalRelevance
import Holonics.Foundation.Standing
import Holonics.Holarchy.Reception
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Holarchy.Hearing: hearing, listening and nullity on the Receiver object

[definition] Object 10 of `docs/ELEMENTARY_OBJECTS.md`, "Hearing, listening and nullity", typed.
A receiver is a role of a participating Holon. At its grain it has a **present face** `F_now`; its
**admitted future** is the family of its faces after every admitted navigator word, with the
present face as the empty-word member; and a **reached-action map** `A` carries a difference into
a locus's retained state (constitution entries, carried remainders, clock).

* `Heard F δ := F δ ≠ 0`, `Null F δ := F δ = 0` and `Listened A δ := A δ ≠ 0`. They are stated for
  any map into a type with zero, so that the HNN's deposit, which is not additive, is an instance
  (`HNN/LatticeDeposit.below_grain_heard_counted_not_deposited`); for an additive face, null is
  kernel membership (`null_iff_mem_ker`). Nullity is always relative to a declared face: a coarser
  grain, a face that factors through a finer one, hears less (`null_of_factors`).
* `HearingLaw` carries the present receivers' faces `face : Receiver → (X →+ V)`, the admitted
  navigator steps `step : Navigator → (X →+ X)` and the reached action `act : X →+ Z`. Its present
  face is the family read at once (`Foundation/Receiver.jointReading`), its future family is
  `Foundation/CausalRelevance.futureRead`, whose empty-word members are the present faces
  (`HearingLaw.future_nil`), and its future nullity is
  `Foundation/CausalRelevance.futureCollapsed`.

[proved-derived; formal-checked] What is proved. Each law is a join of an existing owner.

1. **What no admitted future can distinguish is null now** (`HearingLaw.futureNull_null`,
   `HearingLaw.futureNull_le_ker_present`): `ker F_fut ⊆ ker F_now`, the join of
   `CausalRelevance.futureCollapsed_le_presentCollapsed` and
   `Receiver.theCollapsedIsTheJointKernel`. The converse fails: a present-null difference can be
   reopened by a later navigator step (`CausalRelevance.NonLinear.swap_reopens_second_coordinate`).
2. **What changes no retained state cannot change a response** (`HearingLaw.futureNull_of_retain_eq`):
   under any standing law that reads the receiver's faces and steps, a difference that leaves the
   standing unchanged is null to every admitted future. It is
   `Standing.StandingLaw.futureAgreement_of_retain_eq` read additively.
3. **The reached action is a lawful standing exactly when every unlistened difference is
   future-null** (`HearingLaw.act_is_standing_iff`, from
   `Standing.standingLaw_exists_iff_future_factors`). Hence a difference that is heard but not
   listened to refutes the reached action as a standing
   (`HearingLaw.heard_not_listened_refutes_standing`): `ker A ∖ ker F_now` is nonempty only where
   the present face reads beyond the retained state. The HNN's deposit instantiates the
   predicates, not `HearingLaw`: its release is heard by the receipt, not by an admitted future
   face, so the refutation does not apply. Whether a released tail is future-null is the word-level
   sensitivity certificate owed in #62.
4. [proved-standard; formal-checked] **The coholons a face pulls back are exactly those that
   annihilate its nullity** (`mem_pulledBack_iff`): `range F* = (ker F)^⊥` for a linear face over
   a field, which is Mathlib's `LinearMap.range_dualMap_eq_dualAnnihilator_ker`. It holds for the
   algebraic dual in every dimension; with continuous duals on Hilbert spaces the range needs its
   closure. What a receiver can read is fixed by its nullity; what it listens to is still the
   separate map `A`.
5. **The zero-storage receiver hears without storing** (`zero_storage_receiver_hears_without_storing`):
   with `Q_R = 0` its stored-energy face is null on every receiver state, the bond it presents to
   the source has zero power, and its change is the linear reading `h (J − R)_RS ē_S` of the
   source's midpoint effort plus its own supply (`Reception.zero_storage_receiver_is_passive_reading`).
   The statement is about the energy component only: its state still moves.

**Part of the line served.** The receiver's kernel (nullity) and the reached action whose
quotient is retention; no landmark or terrain is introduced.

**Winding-guide objects touched.** Faces and placement: the present face and its future family.
The tower thread: coarsening a grain enlarges its nullity. The helix, pair, cell holonomy and tube
stay attached and are not used here.

No `axiom`, no `sorry`, no `native_decide`.
-/

namespace Holonics.Receiver.Hearing

open Holonics.Foundation.Chronology (transportWord)

/-! ## 1. Heard, null and listened -/

section Predicates

variable {X Y Z : Type*} [Zero Y] [Zero Z]

/-- [definition] **Heard.** A difference `δ` is heard by the face `F` when the face separates it
from the zero difference: `F δ ≠ 0`. The face is a receiver's present reading at its grain. -/
def Heard (F : X → Y) (δ : X) : Prop := F δ ≠ 0

/-- [definition] **Null.** A difference `δ` is null to the face `F` at its grain when the face
cannot separate it: `F δ = 0`. Nullity belongs to a declared receiver, grain and admitted future,
never to the difference alone. -/
def Null (F : X → Y) (δ : X) : Prop := F δ = 0

/-- [definition] **Listened.** A difference `δ` is listened to when the reached-action map `A`
carries it into a locus's retained state (constitution entries, carried remainders, clock):
`A δ ≠ 0`. Heard-but-not-listened is `Heard F δ ∧ ¬ Listened A δ`, the set `ker A ∖ ker F`. -/
def Listened (A : X → Z) (δ : X) : Prop := A δ ≠ 0

/-- [proved-derived; formal-checked] Not heard is null: the face's two readings of a difference
are complementary. -/
theorem not_heard_iff_null {F : X → Y} {δ : X} : ¬ Heard F δ ↔ Null F δ := not_not

/-- [proved-derived; formal-checked] **A coarser grain hears less.** If the coarse face reads the
fine one through `q` with `q 0 = 0`, what is null at the fine grain is null at the coarse one. -/
theorem null_of_factors {W : Type*} [Zero W] {F : X → Y} {q : Y → W} (hq : q 0 = 0) {δ : X}
    (h : Null F δ) : Null (q ∘ F) δ := by
  unfold Null at h ⊢
  rw [Function.comp_apply, h, hq]

/-- [proved-derived; formal-checked] For an additive face, null is membership in its kernel. -/
theorem null_iff_mem_ker {X' Y' : Type*} [AddGroup X'] [AddGroup Y'] (F : X' →+ Y') (δ : X') :
    Null F δ ↔ δ ∈ F.ker :=
  AddMonoidHom.mem_ker.symm

end Predicates

/-! ## 2. The hearing law: present face, admitted future and reached action -/

section Law

universe u w

/-- [definition] **A hearing law.** The present receivers' faces `face` (a receiver is a role of
a participating Holon; each face is its reading at its grain), the admitted navigator steps `step`
whose words carry a difference into the future, and the reached-action map `act` that carries a
difference into a locus's retained state. -/
structure HearingLaw (Navigator Receiver X V : Type u) (Z : Type w)
    [AddCommGroup X] [AddCommGroup V] [AddCommGroup Z] where
  /-- The present receivers' faces. -/
  face : Receiver → (X →+ V)
  /-- The admitted navigator steps. -/
  step : Navigator → (X →+ X)
  /-- The reached-action map into the retained state. -/
  act : X →+ Z

namespace HearingLaw

variable {Navigator Receiver X V : Type u} {Z : Type w}
  [AddCommGroup X] [AddCommGroup V] [AddCommGroup Z]
  (H : HearingLaw Navigator Receiver X V Z)

/-- [definition] **The present face** `F_now`: the present receivers read at once
(`Foundation/Receiver.jointReading`). -/
def present : X →+ (Receiver → V) := Holonics.Foundation.Receiver.jointReading H.face

/-- [definition] **The admitted future face family**: every present receiver after every admitted
navigator word (`Foundation/CausalRelevance.futureRead`). -/
def future : Receiver × List Navigator → (X →+ V) :=
  Holonics.Foundation.CausalRelevance.futureRead H.face H.step

/-- [definition] **Future-null**: no admitted receiver distinguishes `δ` after any admitted word;
membership in `Foundation/CausalRelevance.futureCollapsed`. -/
def FutureNull (δ : X) : Prop :=
  δ ∈ Holonics.Foundation.CausalRelevance.futureCollapsed H.face H.step

/-- [proved-derived; formal-checked] **The present face is the empty-word member of the future
family.** -/
theorem future_nil (r : Receiver) : H.future (r, []) = H.face r := by
  ext x
  rfl

/-- [proved-derived; formal-checked] The present face read at one receiver is that receiver's
empty-word future face. -/
theorem present_apply (δ : X) (r : Receiver) : H.present δ r = H.future (r, []) δ := by
  rw [future_nil]
  rfl

/-- [proved-derived; formal-checked] Future-null is null to every member of the future family. -/
theorem futureNull_iff (δ : X) :
    H.FutureNull δ ↔ ∀ r w, Null (H.future (r, w)) δ :=
  Holonics.Foundation.CausalRelevance.mem_futureCollapsed_iff H.face H.step δ

/-- [proved-derived; formal-checked] **What no admitted future distinguishes is null now:**
`ker F_fut ⊆ ker F_now`, the join of `CausalRelevance.futureCollapsed_le_presentCollapsed` and
`Receiver.theCollapsedIsTheJointKernel`. -/
theorem futureNull_le_ker_present :
    Holonics.Foundation.CausalRelevance.futureCollapsed H.face H.step ≤ H.present.ker := by
  intro δ hδ
  have h := Holonics.Foundation.CausalRelevance.futureCollapsed_le_presentCollapsed
    H.face H.step hδ
  rw [← Holonics.Foundation.Receiver.theCollapsedIsTheJointKernel] at h
  exact h

/-- [proved-derived; formal-checked] Pointwise: a future-null difference is null to the present
face. -/
theorem futureNull_null {δ : X} (h : H.FutureNull δ) : Null H.present δ :=
  (null_iff_mem_ker H.present δ).2 (H.futureNull_le_ker_present h)

/-- [proved-derived; formal-checked] **What changes no retained state cannot change a response.**
Under a standing law that reads this receiver's faces and steps, a difference `δ` that leaves the
standing of some `x` unchanged, `retain (x + δ) = retain x`, is null to every admitted future:
`Standing.StandingLaw.futureAgreement_of_retain_eq`, read through the additivity of the faces. -/
theorem futureNull_of_retain_eq {Retained : Type*}
    (L : Holonics.Foundation.Standing.StandingLaw Navigator Receiver X Retained V)
    (hT : L.transport = fun g x => H.step g x) (hO : L.observe = fun r x => H.face r x)
    {x δ : X} (h : L.retain (x + δ) = L.retain x) : H.FutureNull δ := by
  have hagree := L.futureAgreement_of_retain_eq h
  rw [futureNull_iff]
  intro r w
  have heq := hagree r w
  simp only [hT, hO] at heq
  have hadd := map_add (H.future (r, w)) x δ
  change H.face r (transportWord (fun g y => H.step g y) w (x + δ)) =
    H.face r (transportWord (fun g y => H.step g y) w x) + H.future (r, w) δ at hadd
  rw [heq] at hadd
  exact (add_eq_left.mp hadd.symm)

/-- [proved-derived; formal-checked] **The reached action is a lawful standing exactly when every
unlistened difference is future-null.** A standing law that reads this receiver's faces and steps
retains exactly `act` if and only if `ker A ⊆ ker F_fut`
(`Standing.standingLaw_exists_iff_future_factors`). -/
theorem act_is_standing_iff [Nonempty V] :
    (∃ L : Holonics.Foundation.Standing.StandingLaw Navigator Receiver X Z V,
        L.transport = (fun g x => H.step g x) ∧ L.observe = (fun r x => H.face r x) ∧
          L.retain = H.act) ↔
      ∀ δ, ¬ Listened H.act δ → H.FutureNull δ := by
  rw [Holonics.Foundation.Standing.standingLaw_exists_iff_future_factors]
  constructor
  · intro hf δ hδ
    have hact : H.act δ = H.act 0 := by
      rw [map_zero]
      exact not_not.mp hδ
    have hsig := hf δ 0 hact
    rw [futureNull_iff]
    intro r w
    have hrw := congrFun hsig (r, w)
    change H.future (r, w) δ = H.future (r, w) 0 at hrw
    rw [map_zero] at hrw
    exact hrw
  · intro h left right hact
    have hnull : H.FutureNull (right - left) := by
      apply h
      unfold Listened
      rw [map_sub, hact, sub_self, not_not]
    rw [futureNull_iff] at hnull
    funext rw
    obtain ⟨r, w⟩ := rw
    have hrw := hnull r w
    unfold Null at hrw
    rw [map_sub, sub_eq_zero] at hrw
    exact hrw.symm

/-- [proved-derived; formal-checked] **Heard but not listened refutes the reached action as a
standing.** If some difference is heard by the present face and not listened to, no standing law
that reads this receiver's faces and steps retains exactly `act`: the present face reads beyond
the retained state. -/
theorem heard_not_listened_refutes_standing {δ : X} (hheard : Heard H.present δ)
    (hnot : ¬ Listened H.act δ) :
    ¬ ∃ L : Holonics.Foundation.Standing.StandingLaw Navigator Receiver X Z V,
        L.transport = (fun g x => H.step g x) ∧ L.observe = (fun r x => H.face r x) ∧
          L.retain = H.act := by
  rintro ⟨L, hT, hO, hR⟩
  have hret : L.retain (0 + δ) = L.retain 0 := by
    rw [hR, zero_add, map_zero]
    exact not_not.mp hnot
  exact hheard (H.futureNull_null (H.futureNull_of_retain_eq L hT hO hret))

end HearingLaw

end Law

/-! ## 3. The coholons a face pulls back annihilate its nullity -/

section Dual

variable {K U W : Type*} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]

/-- [proved-standard; formal-checked] **The coholons a face pulls back annihilate its nullity.**
A coholon is pulled back by the linear face `F` exactly when it vanishes on every difference null
to that face: `range F* = (ker F)^⊥`, Mathlib's `LinearMap.range_dualMap_eq_dualAnnihilator_ker`,
for the algebraic dual in every dimension. -/
theorem mem_pulledBack_iff (F : U →ₗ[K] W) (φ : Module.Dual K U) :
    φ ∈ LinearMap.range F.dualMap ↔ ∀ δ, Null F δ → φ δ = 0 := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
  exact forall_congr' fun δ => by rw [LinearMap.mem_ker]; rfl

end Dual

/-! ## 4. The zero-storage receiver hears without storing -/

section ZeroStorage

open Matrix Holonics.HolonCore

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {σS σR μ : Type*} [Fintype σS] [Fintype σR]
  [Fintype μ]

/-- [proved-derived; formal-checked] **The zero-storage receiver hears without storing.** With
`Q_R = 0`: its stored-energy face is null on every receiver state, so it retains no energy whatever
it reads; the bond it presents to the source has zero power; and its change is the linear reading
`h (J − R)_RS ē_S` of the source's midpoint effort plus its own supply
(`Reception.zero_storage_receiver_is_passive_reading`). This is a statement about the energy
component: the receiver's state still moves. -/
theorem zero_storage_receiver_hears_without_storing {L : JointLaw 𝕜 σS σR μ} (hQR : L.QR = 0)
    (s : JointStep L) :
    (∀ x : σR → 𝕜, Null (storageEnergy L.QR) x) ∧
      power (((L.J - L.R).toBlocks₁₂ *ᵥ (s.effort ∘ Sum.inr), s.effort ∘ Sum.inl) :
        Bond 𝕜 σS) = 0 ∧
      (s.after - s.before) ∘ Sum.inr =
        s.h • ((L.J - L.R).toBlocks₂₁ *ᵥ (s.effort ∘ Sum.inl) + (L.B *ᵥ s.supply) ∘ Sum.inr) := by
  obtain ⟨-, -, hpow, -, hR, -⟩ := zero_storage_receiver_is_passive_reading hQR s
  refine ⟨fun x => ?_, hpow, hR⟩
  simp [Null, storageEnergy, hQR]

end ZeroStorage

section Audit

#print axioms null_of_factors
#print axioms HearingLaw.future_nil
#print axioms HearingLaw.present_apply
#print axioms HearingLaw.futureNull_le_ker_present
#print axioms HearingLaw.futureNull_null
#print axioms HearingLaw.futureNull_of_retain_eq
#print axioms HearingLaw.act_is_standing_iff
#print axioms HearingLaw.heard_not_listened_refutes_standing
#print axioms mem_pulledBack_iff
#print axioms zero_storage_receiver_hears_without_storing

end Audit

end Holonics.Receiver.Hearing
