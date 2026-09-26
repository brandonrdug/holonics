import Holonics.HNN.Contact
import Holonics.Holarchy.Join

/-!
# HNN.ContactBreak: the contact's parting, its released storage and its gluing defect

[definition] Rebuild step 4 (#73), campaign 2, Lean item 8 (`docs/plans/THE_REBUILD.md`, "Campaign 2",
*The contact's break*; Sol's review §1). A contact of declared extent `a` (the channel it matches)
carries its stored energy `E_a`; over one transit its port work is `W_a` and its dissipation
`D_a ≥ 0`. Parting advances the face from `a` to `a′`, which takes the gluing work `J(a, a′)`: the
surface storage of the new faces (#31), `J = γ (a′ − a)` at the declared surface-storage density `γ`.
The **released storage at the parting face** is the balance

```text
R(a, a′) = E_a + W_a − D_a − E_a′ ,     an admitted advance has  R ≥ J ,   R = J at the quasistatic threshold
```

and the remainder `R − J` is the receipt.

[proved-derived; formal-checked] What is proved.

1. **The released storage is the storage the parting removes** (`break_release_balance`): through
   the transit's balance (`HNN/Propagation.transit_balance`, `Contact.contact_signed_storage_balance`)
   at the contact's constitution `(C, K)` before the parting, `E_a + W_a − D_a` is the storage of the
   post-transit state, so `R = E_(C,K)(u′, w′) − E_(C′,K′)(u′, w′)`, the storage the parted
   constitution `(C′, K′)` no longer holds.
2. **The advance** (`break_iff_release_covers_gluing`): an advance is admitted exactly when the
   remainder `R − J` is nonnegative; the quasistatic threshold is `R − J = 0`.
3. **Griffith** (`griffith_closed_port_case`): with no port work and no dissipation the released
   storage is the drop of stored energy, `R = E_a − E_a′`, and the admitted advance is Griffith's
   comparison `E_a − E_a′ ≥ γ (a′ − a)`, with equality at the critical advance.
4. **A parted face is a typed gluing defect** (`parting_returns_gluing_defect`): the shared port of
   a parted face transmits no flow, so its join's flow gain is zero there (`partedAt`); the join then
   fails to cancel the interface power (`(EᵀF′)_(t t) = 0 ≠ 1`), and `interconnect` returns the typed
   defect `GluingDefect.uncancelledPower` with its witnessed bond, which refutes the gluing
   (`Holarchy/Join.{interconnect_ok_iff, GluingDefect.not_glues}`). An energy inequality alone
   cannot construct the defect; the failed check is exhibited.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.ContactBreak

open Holonics.HNN.Propagation

/-! ## 1. The released storage and the admitted advance -/

section Release

/-- [definition] **The released storage** `R(a, a′) = E_a + W_a − D_a − E_a′`. -/
def released (Ea Wa Da Ea' : ℝ) : ℝ := Ea + Wa - Da - Ea'

/-- [definition] **The gluing work** of the parting face: the surface storage `γ (a′ − a)` of the
new faces at the declared density `γ` (#31). -/
def gluingWork (γ a a' : ℝ) : ℝ := γ * (a' - a)

variable {Ch : Type*} [NormedAddCommGroup Ch] [InnerProductSpace ℝ Ch]

/-- [proved-derived; formal-checked] **The break's release balance.** For the transit of a contact
at its constitution `(C, K, D)` (symmetric `C`, `K`, any sign), with its port work
`W = (hG/4)(|α|² − |α_out|²)` and dissipation `h⟨ω, D ω⟩`, the released storage against the parted
constitution `(C′, K′)` is the storage the parting removes from the post-transit state. -/
theorem break_release_balance (C D K C' K' : Ch →L[ℝ] Ch)
    (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y)) (hK : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y))
    {G h : ℝ} (hG : G ≠ 0) {u w αg αh ω : Ch} (hsolve : TransitSolves C D K G h u w αg αh ω) :
    released (contactEnergy C K u w)
        (h * G / 4 * (‖αg‖ ^ 2 + ‖αh‖ ^ 2 - ‖αg - (2 / G) • ω‖ ^ 2 - ‖αh + (2 / G) • ω‖ ^ 2))
        (h * inner ℝ ω (D ω)) (contactEnergy C' K' (u + h • ω) ((2 : ℝ) • ω - w)) =
      contactEnergy C K (u + h • ω) ((2 : ℝ) • ω - w) -
        contactEnergy C' K' (u + h • ω) ((2 : ℝ) • ω - w) := by
  have hb := Contact.contact_signed_storage_balance C D K hC hK hG hsolve
  unfold released
  linarith

/-- [proved-derived; formal-checked] **An advance is admitted exactly when the release covers the
gluing work**: `J ≤ R ↔ 0 ≤ R − J`, and the quasistatic threshold `R = J` is a zero remainder. -/
theorem break_iff_release_covers_gluing (R J : ℝ) :
    (J ≤ R ↔ 0 ≤ R - J) ∧ (R = J ↔ R - J = 0) :=
  ⟨sub_nonneg.symm, sub_eq_zero.symm⟩

/-- [proved-derived; formal-checked] **Griffith's comparison is the closed-port case.** With no port
work and no dissipation, `R = E_a − E_a′`, and the advance `a → a′` at surface-storage density `γ` is
admitted exactly when `E_a − E_a′ ≥ γ (a′ − a)`, with equality at the critical advance. -/
theorem griffith_closed_port_case (Ea Ea' γ a a' : ℝ) :
    released Ea 0 0 Ea' = Ea - Ea' ∧
      (gluingWork γ a a' ≤ released Ea 0 0 Ea' ↔ γ * (a' - a) ≤ Ea - Ea') ∧
      (released Ea 0 0 Ea' = gluingWork γ a a' ↔ Ea - Ea' = γ * (a' - a)) := by
  unfold released gluingWork
  refine ⟨by ring, ?_, ?_⟩ <;> constructor <;> intro hx <;> linarith

end Release

/-! ## 2. A parted shared face returns a typed gluing defect -/

section Parting

open Holonics.HolarchyCore Matrix

variable {𝕜 : Type*} [Field 𝕜] {U : Type*}
variable {σA ρA πA αA σB ρB πB αB τ : Type*}
  [Fintype σA] [Fintype ρA] [Fintype πA] [Fintype αA]
  [Fintype σB] [Fintype ρB] [Fintype πB] [Fintype αB] [Fintype τ] [DecidableEq τ]
variable {A : Constituent 𝕜 U σA ρA (πA ⊕ τ) αA} {B : Constituent 𝕜 U σB ρB (τ ⊕ πB) αB}

/-- [definition] **The parted declaration**: the declared join with no flow transmitted through the
parted shared port `t₀` (its flow gain's column is zero). Everything else is the original join. -/
def partedAt (d : JoinDeclaration A B) (t₀ : τ) : JoinDeclaration A B :=
  { d with flowGain := Matrix.of fun i j => if j = t₀ then 0 else d.flowGain i j }

/-- [proved-derived; formal-checked] **The parted face fails the interface-power check.** -/
theorem partedAt_not_powerCancels (d : JoinDeclaration A B) (t₀ : τ) :
    ¬ (partedAt d t₀).PowerCancels := by
  intro h
  have := congrFun (congrFun h t₀) t₀
  simp only [partedAt, Matrix.mul_apply, Matrix.of_apply, if_pos, mul_zero,
    Finset.sum_const_zero, Matrix.one_apply_eq] at this
  exact zero_ne_one this

/-- [proved-derived; formal-checked] **A parted shared face returns a typed gluing defect.** When
the two constituents' units agree (as they do for the unparted join), `interconnect` of the parted
declaration returns the defect `uncancelledPower` with its witnessed bond, and that defect refutes
the gluing (`GluingDefect.not_glues`). -/
theorem parting_returns_gluing_defect (d : JoinDeclaration A B) (t₀ : τ)
    (hu : d.UnitsAgree) :
    ∃ (bond : Holonics.HolonCore.Bond 𝕜 τ)
      (hne : interfacePower (partedAt d t₀).flowGain (partedAt d t₀).effortGain bond ≠ 0),
      interconnect A B (partedAt d t₀) = .error (.uncancelledPower bond hne) ∧
        ¬ (partedAt d t₀).Glues := by
  have hp := partedAt_not_powerCancels d t₀
  have hu' : (partedAt d t₀).UnitsAgree := hu
  refine ⟨(exists_interfacePower_ne_zero hp).choose, (exists_interfacePower_ne_zero hp).choose_spec,
    ?_, ?_⟩
  · unfold interconnect
    rw [dif_pos hu', dif_neg hp]
  · exact GluingDefect.not_glues (.uncancelledPower _
      (exists_interfacePower_ne_zero hp).choose_spec)

end Parting

section Audit

#print axioms break_release_balance
#print axioms break_iff_release_covers_gluing
#print axioms griffith_closed_port_case
#print axioms partedAt_not_powerCancels
#print axioms parting_returns_gluing_defect

end Audit

end Holonics.HNN.ContactBreak
