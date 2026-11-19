import Holonics.Holon.Law
import Holonics.Holon.Restriction.Morphism
import Holonics.Holarchy.Join
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Holon.InterconnectionJoin: the step, the restriction and joint reception carried by `interconnect`

[definition] A step of a port Holon `H` from `x` to `x′` over a step `h` is **admitted in Dirac
form** (`DiracStep`) when the assembled bond at the midpoint effort `Q x̄`, `x̄ = ½(x + x′)`, with
the difference quotient `h⁻¹(x′ − x)` as velocity, lies in `H.D` (`PortHolon.Admits`): the
element relations are read at the midpoint and the interconnection is the Dirac structure itself,
with no `(J − R)Q` form.

[proved-derived; formal-checked] What is proved, over a field
`𝕜` (characteristic zero where a balance is read, ordered where an inequality is read).

1. **The Dirac-form step and its balance.** `E(x′) − E(x) = ⟨x′ − x, Q x̄⟩` for symmetric `Q`
   (`storageEnergy_sub_midpoint`, by `Holon/Element.symm_dot`); on an admitted step with `h ≠ 0`,
   `E(x′) − E(x) = h(−⟨f_R, R f_R⟩ + ⟨e_P, f_P⟩ + ⟨e_A, f_A⟩)` from power neutrality alone
   (`diracStep_balance`, through `PortHolon.power_balance`), and with `R ⪰ 0` and `h > 0` the
   stored energy grows by no more than `h(⟨e_P, f_P⟩ + ⟨e_A, f_A⟩)` (`diracStep_passive`).
2. **The step of an interconnection.** A Dirac-form step of `A.interconnect B` restricts, through
   one shared bond `q`, to Dirac-form steps of `A` (shared ports carrying `q`) and of `B` (carrying
   `(−f_q, e_q)`), and the two sides' external powers sum to the composite's: the shared terms
   cancel (`diracStep_interconnect`, by `PortHolon.mem_interconnect` and
   `Holon/Dirac.interconnect_power`). The joint balance is the sum of the two sides' balances: each
   side's own Dirac-form balance holds, and the stored energy, the dissipation and the active power
   are additive (`diracStep_interconnect_balance`, by `storageEnergy_blocks`, `dissipation_blocks`).
3. **The restriction facet `π` joined by interconnection.** For Dirac structures `DA` on `α ⊕ τ`
   and `DB` on `τ ⊕ β` and port maps `PA`, `PB`: if `[PA 0; 0 1]` is a morphism `DA → DA'` and
   `[1 0; 0 PB]` a morphism `DB → DB'` (the identity on the shared ports), then `[PA 0; 0 PB]` is
   a morphism `interconnect DA DB → interconnect DA' DB'`, through the same shared bond
   (`interconnect_isMorphism`). Relabelling ports carries morphisms (`isMorphism_reindex`), and so
   the same statement holds for port Holons, with each side's map read through `splitA`, `splitB`
   and the composite's through `mergeKinds` (`portHolon_interconnect_isMorphism`).
4. **The discrete face law of joint reception.** Two port Holons, a Holon `H` and a receiver, each
   with its external ports `τ` only, take Dirac-form steps whose port bonds are the interface
   current `i = G(ē_H − ē_R)` at their midpoint efforts, `(−i, ē_H)` and `(i, ē_R)`. Then the
   energy the two sides receive over the step is `−h⟨Δ̄, G Δ̄⟩ ≤ 0`, `Δ̄ = ē_H − ē_R`
   (`Holon/Law.active_receiver_law` at the midpoint), and with each side's own balance,
   `ΔE_H + ΔE_R = −h(D_H + D_R + ⟨Δ̄, G Δ̄⟩) + h(⟨e_A, f_A⟩_H + ⟨e_A, f_A⟩_R)`
   (`joint_reception_step`); with `R_H, R_R ⪰ 0` the two stores together grow by no more than the
   active supply (`joint_reception_passive`). This is stated as two balances and the interface law,
   not as one composite port Holon: the conductance `G` is a resistive relation in conductance
   form, and `PortHolon` holds resistance in the form `e_R = −R f_R`, which a singular `G` has not.
5. **The RC motion witness for `interconnect`.** A capacitor (`PortHolon 𝕜 Unit Empty (Empty ⊕ Unit)
   Empty`, storage `Q = C⁻¹`) and a resistor (`PortHolon 𝕜 Empty Unit (Unit ⊕ Empty) Empty`,
   resistance `R`), each with the Kirchhoff structure of one node joining its two ports (Dirac by
   `Holon/Dirac.kirchhoff_isDirac`), which is the link of its live port to its shared port, flows
   opposite and efforts equal (`capacitor_link`, `resistor_link`). Their interconnection
   (`rcCircuit`) admits a point exactly when `f_R = v` and `−R f_R = C⁻¹ x` (`rcCircuit_admits_iff`,
   by `PortHolon.mem_interconnect`). Over `ℝ`, with `C, R ≠ 0` (the passive circuit is `C, R > 0`),
   the motion `x(t) = x₀ e^(−t/(RC))` has rate `v = −x/(RC)` and is admitted at every `t` with
   `f_R = v` and no external or active bond (`rc_motion_admitted`); along it
   `dE/dt = −R f_R²` (`rc_energy_rate`, by `PortHolon.energy_balance_const`), and with no hypothesis
   `E(t) = E(0) e^(−2t/(RC))` (`rc_energy_decay`). The discrete witness: one midpoint step
   `x′ = x(2RC − h)/(2RC + h)` is admitted in Dirac form with `f̄ = −2x/(2RC + h)` and
   `E′ − E = −hR f̄²` (`rc_midpoint_step`); over `ℚ` at `C = R = h = 1`, `x = 3`, the step reaches
   `x′ = 1` with `f̄ = −2` and `E′ − E = −4` (`rc_midpoint_witness`).

Sources: the box of #410, "Interconnection: an RC motion witness for `interconnect`; the
restriction facet `π` joined by it; the Dirac-form joint step and discrete face law of joint
reception (`Holon/{Dirac,Restriction,Law}`)"; the Holon's open paragraph in
`docs/ELEMENTARY_OBJECTS.md` §"The Holon as one object" (receivers are Holons joined at ports, and
interconnecting Holons through their ports yields a Holon); the refinement record
`research/records/2026-09-22_THE_HOLON_IS_AN_INTERCONNECTED_PORT_OBJECT_ON_A_COMPLEX.md`; the
owners `Holon/Element` (`PortHolon`, `PortHolon.Admits`, `power_balance`, `midpoint_balance`),
`Holon/Law` (`PortHolon.interconnect`, `mem_interconnect`, `active_receiver_law`), `Holon/Dirac`
(`interconnect`, `mem_interconnect`, `interconnect_power`, `kirchhoff_isDirac`, `bondReindex`),
`Holon/Restriction/Morphism` (`IsMorphism`, `pushforward`) and `Holarchy/Join` (whose part
identities `leftPart_assemble`, `rightPart_assemble` and `bondReindex_symm_apply` this module reads;
its `Holarchy.balance_is_sum` is the rate form of item 2 on a Holarchy's whole). The discrete
balance of the midpoint rule in Dirac form is that of Kotyczka and Lefèvre, *Systems & Control
Letters* 133 (2019). `Holarchy/Reception` owns joint reception in the `(J − R)Q` form with its
solved step (`JointLaw`, `jointStep_iff`, `InteractionReturn.balance`); item 4 keeps the interface
as a conductance between two Dirac-form steps and restates none of its theorems. Atlas rows served:
`holon.interconnect`, `holon.interconnect-port-holons`, `holarchy.interconnect`,
`holon.midpoint-balance-exact`, `holon.pushforward-morphism`, `receipt.active-receiver-law`,
`receipt.reception`, `physics.port-hamiltonian`, `gr.joined-balance`, `heat.port-ohmic`.

What is not claimed. Nonlinear storage (`Holon/Element.energy_balance_fderiv` owns its rate form;
no Dirac-form step of it is stated here); the receipt and its regions (`Holarchy/Receipt`); that a
Dirac-form step exists or is unique for given data (`Holarchy/Reception.interact` solves the
`(J − R)Q` step); the case `h = 0`, where the difference quotient reads velocity `0` and leaves `x′`
free, so no balance is stated there; that the port maps of item 3 keep the four port kinds apart
(any port map is allowed) or that a morphism exists; a composite port Holon for the conductance of
item 4; the uniqueness of the RC motion among solutions (item 5 shows the motion admitted and the
admitted points to be the RC law, not an existence and uniqueness theorem for the flow).

The computational object is the helical pair interaction read on two joined Holons: a shared port
is the pair's contact, where the two sides' flows are opposite and their efforts equal, so the
contact carries no power through the join (the no-slip reading of the contact), and the interface
conductance of joint reception is a dissipative contact whose power `⟨Δ̄, G Δ̄⟩` is the contact
material read on the slip `Δ̄ = ē_H − ē_R`. Of the winding guide's six general objects this touches
the pair (the shared port and the interface contact), the tube (a Dirac-form step is one tick of a
clocked span from `x` to `x′`, the midpoint its shared section) and the tower thread (the
restriction facet carried through the join); the helix, faces and placement, and cell holonomy
stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HolonCore.InterconnectionJoin

open Matrix
open Holonics.HolonCore

/-! ## 1. The Dirac-form step and its balance -/

section Step

variable {𝕜 : Type*} [Field 𝕜]
variable {σ ρ π α : Type*} [Fintype σ] [Fintype ρ] [Fintype π] [Fintype α]

/-- [definition] **A step admitted in Dirac form**: the assembled bond with the midpoint effort
`Q x̄`, `x̄ = ½(x + x′)`, and the difference quotient `h⁻¹(x′ − x)` as velocity lies in `H.D`. -/
def DiracStep (H : PortHolon 𝕜 σ ρ π α) (h : 𝕜) (x x' : σ → 𝕜) (fR : ρ → 𝕜) (fP eP : π → 𝕜)
    (fA eA : α → 𝕜) : Prop :=
  H.Admits H.Q ((1 / 2 : 𝕜) • (x + x')) (h⁻¹ • (x' - x)) fR fP eP fA eA

/-- [proved-standard; formal-checked] For symmetric `Q`, `E(x′) − E(x) = ⟨x′ − x, Q x̄⟩`. -/
theorem storageEnergy_sub_midpoint {Q : Matrix σ σ 𝕜} (hQ : Qᵀ = Q) (x x' : σ → 𝕜) :
    storageEnergy Q x' - storageEnergy Q x = (x' - x) ⬝ᵥ (Q *ᵥ ((1 / 2 : 𝕜) • (x + x'))) := by
  simp only [storageEnergy, mulVec_smul, mulVec_add, dotProduct_smul, dotProduct_add,
    sub_dotProduct, smul_eq_mul]
  rw [symm_dot hQ x' x]
  ring

/-- [proved-standard; formal-checked] **The Dirac-form balance**: on an admitted step with
`h ≠ 0`, `E(x′) − E(x) = h(−⟨f_R, R f_R⟩ + ⟨e_P, f_P⟩ + ⟨e_A, f_A⟩)`, from power neutrality. -/
theorem diracStep_balance [CharZero 𝕜] (H : PortHolon 𝕜 σ ρ π α) {h : 𝕜} (hh : h ≠ 0)
    {x x' : σ → 𝕜} {fR : ρ → 𝕜} {fP eP : π → 𝕜} {fA eA : α → 𝕜}
    (hs : DiracStep H h x x' fR fP eP fA eA) :
    storageEnergy H.Q x' - storageEnergy H.Q x =
      h * (-(fR ⬝ᵥ (H.R *ᵥ fR)) + eP ⬝ᵥ fP + eA ⬝ᵥ fA) := by
  rw [storageEnergy_sub_midpoint H.Q_symm, ← H.power_balance hs]
  have hx : x' - x = h • (h⁻¹ • (x' - x)) := by rw [smul_smul, mul_inv_cancel₀ hh, one_smul]
  conv_lhs => rw [hx]
  rw [smul_dotProduct, smul_eq_mul, dotProduct_comm]

/-- [proved-standard; formal-checked] **Passivity of the Dirac-form step**: with `R ⪰ 0` and
`h > 0`, `E(x′) − E(x) ≤ h(⟨e_P, f_P⟩ + ⟨e_A, f_A⟩)`. -/
theorem diracStep_passive [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] (H : PortHolon 𝕜 σ ρ π α)
    (hR : ∀ f, 0 ≤ f ⬝ᵥ (H.R *ᵥ f)) {h : 𝕜} (hh : 0 < h) {x x' : σ → 𝕜} {fR : ρ → 𝕜}
    {fP eP : π → 𝕜} {fA eA : α → 𝕜} (hs : DiracStep H h x x' fR fP eP fA eA) :
    storageEnergy H.Q x' - storageEnergy H.Q x ≤ h * (eP ⬝ᵥ fP + eA ⬝ᵥ fA) := by
  rw [diracStep_balance H hh.ne' hs]
  exact mul_le_mul_of_nonneg_left (by linarith [hR fR]) hh.le

end Step

/-! ## 2. The step of an interconnection -/

section Interconnect

variable {𝕜 : Type*} [Field 𝕜]
variable {σA ρA πA αA σB ρB πB αB τ : Type*}
  [Fintype σA] [Fintype ρA] [Fintype πA] [Fintype αA]
  [Fintype σB] [Fintype ρB] [Fintype πB] [Fintype αB] [Fintype τ]
  [DecidableEq σA] [DecidableEq ρA] [DecidableEq πA] [DecidableEq αA]
  [DecidableEq σB] [DecidableEq ρB] [DecidableEq πB] [DecidableEq αB] [DecidableEq τ]

/-- [proved-derived; formal-checked] **A joint step restricts to the two sides through one shared
bond**: Dirac-form steps of `A` with `q` and of `B` with `(−f_q, e_q)`, whose external powers sum
to the composite's (`interconnect_power`). -/
theorem diracStep_interconnect (A : PortHolon 𝕜 σA ρA (πA ⊕ τ) αA)
    (B : PortHolon 𝕜 σB ρB (τ ⊕ πB) αB) {h : 𝕜} {x x' : σA ⊕ σB → 𝕜} {fR : ρA ⊕ ρB → 𝕜}
    {fP eP : πA ⊕ πB → 𝕜} {fA eA : αA ⊕ αB → 𝕜}
    (hs : DiracStep (A.interconnect B) h x x' fR fP eP fA eA) :
    ∃ q : Bond 𝕜 τ,
      DiracStep A h (x ∘ Sum.inl) (x' ∘ Sum.inl) (fR ∘ Sum.inl) (Sum.elim (fP ∘ Sum.inl) q.1)
        (Sum.elim (eP ∘ Sum.inl) q.2) (fA ∘ Sum.inl) (eA ∘ Sum.inl) ∧
      DiracStep B h (x ∘ Sum.inr) (x' ∘ Sum.inr) (fR ∘ Sum.inr) (Sum.elim (-q.1) (fP ∘ Sum.inr))
        (Sum.elim q.2 (eP ∘ Sum.inr)) (fA ∘ Sum.inr) (eA ∘ Sum.inr) ∧
      Sum.elim (eP ∘ Sum.inl) q.2 ⬝ᵥ Sum.elim (fP ∘ Sum.inl) q.1 +
        Sum.elim q.2 (eP ∘ Sum.inr) ⬝ᵥ Sum.elim (-q.1) (fP ∘ Sum.inr) = eP ⬝ᵥ fP := by
  obtain ⟨q, hA, hB⟩ := (PortHolon.mem_interconnect A B _).mp hs
  rw [Holonics.HolarchyCore.leftPart_assemble] at hA
  rw [Holonics.HolarchyCore.rightPart_assemble] at hB
  refine ⟨q, ?_, ?_, interconnect_power (fP, eP) q⟩
  · unfold DiracStep PortHolon.Admits
    convert hA using 2
    all_goals
      funext i
      simp [PortHolon.interconnect, Matrix.fromBlocks_mulVec, Function.comp_def]
      try rfl
  · unfold DiracStep PortHolon.Admits
    convert hB using 2
    all_goals
      funext i
      simp [PortHolon.interconnect, Matrix.fromBlocks_mulVec, Function.comp_def]
      try rfl

/-- [proved-derived; formal-checked] **The joint balance is the sum of the sides' balances**: each
side's Dirac-form balance through the shared bond, with storage, dissipation and active power
additive, and the composite's own balance. -/
theorem diracStep_interconnect_balance [CharZero 𝕜] (A : PortHolon 𝕜 σA ρA (πA ⊕ τ) αA)
    (B : PortHolon 𝕜 σB ρB (τ ⊕ πB) αB) {h : 𝕜} (hh : h ≠ 0) {x x' : σA ⊕ σB → 𝕜}
    {fR : ρA ⊕ ρB → 𝕜} {fP eP : πA ⊕ πB → 𝕜} {fA eA : αA ⊕ αB → 𝕜}
    (hs : DiracStep (A.interconnect B) h x x' fR fP eP fA eA) :
    ∃ q : Bond 𝕜 τ,
      storageEnergy A.Q (x' ∘ Sum.inl) - storageEnergy A.Q (x ∘ Sum.inl) =
        h * (-((fR ∘ Sum.inl) ⬝ᵥ (A.R *ᵥ (fR ∘ Sum.inl))) +
          Sum.elim (eP ∘ Sum.inl) q.2 ⬝ᵥ Sum.elim (fP ∘ Sum.inl) q.1 +
          (eA ∘ Sum.inl) ⬝ᵥ (fA ∘ Sum.inl)) ∧
      storageEnergy B.Q (x' ∘ Sum.inr) - storageEnergy B.Q (x ∘ Sum.inr) =
        h * (-((fR ∘ Sum.inr) ⬝ᵥ (B.R *ᵥ (fR ∘ Sum.inr))) +
          Sum.elim q.2 (eP ∘ Sum.inr) ⬝ᵥ Sum.elim (-q.1) (fP ∘ Sum.inr) +
          (eA ∘ Sum.inr) ⬝ᵥ (fA ∘ Sum.inr)) ∧
      storageEnergy (A.interconnect B).Q x' - storageEnergy (A.interconnect B).Q x =
        (storageEnergy A.Q (x' ∘ Sum.inl) - storageEnergy A.Q (x ∘ Sum.inl)) +
          (storageEnergy B.Q (x' ∘ Sum.inr) - storageEnergy B.Q (x ∘ Sum.inr)) ∧
      fR ⬝ᵥ ((A.interconnect B).R *ᵥ fR) =
        (fR ∘ Sum.inl) ⬝ᵥ (A.R *ᵥ (fR ∘ Sum.inl)) + (fR ∘ Sum.inr) ⬝ᵥ (B.R *ᵥ (fR ∘ Sum.inr)) ∧
      eA ⬝ᵥ fA = (eA ∘ Sum.inl) ⬝ᵥ (fA ∘ Sum.inl) + (eA ∘ Sum.inr) ⬝ᵥ (fA ∘ Sum.inr) ∧
      storageEnergy (A.interconnect B).Q x' - storageEnergy (A.interconnect B).Q x =
        h * (-(fR ⬝ᵥ ((A.interconnect B).R *ᵥ fR)) + eP ⬝ᵥ fP + eA ⬝ᵥ fA) := by
  obtain ⟨q, hA, hB, -⟩ := diracStep_interconnect A B hs
  have hE : ∀ y : σA ⊕ σB → 𝕜, storageEnergy (A.interconnect B).Q y =
      storageEnergy A.Q (y ∘ Sum.inl) + storageEnergy B.Q (y ∘ Sum.inr) := fun y => by
    conv_lhs => rw [← Sum.elim_comp_inl_inr y]
    exact storageEnergy_blocks A.Q B.Q _ _
  have hD : fR ⬝ᵥ ((A.interconnect B).R *ᵥ fR) =
      (fR ∘ Sum.inl) ⬝ᵥ (A.R *ᵥ (fR ∘ Sum.inl)) + (fR ∘ Sum.inr) ⬝ᵥ (B.R *ᵥ (fR ∘ Sum.inr)) := by
    conv_lhs => rw [← Sum.elim_comp_inl_inr fR]
    exact dissipation_blocks A.R B.R _ _
  have hAct : eA ⬝ᵥ fA = (eA ∘ Sum.inl) ⬝ᵥ (fA ∘ Sum.inl) + (eA ∘ Sum.inr) ⬝ᵥ (fA ∘ Sum.inr) := by
    simp [dotProduct, Fintype.sum_sum_type]
  exact ⟨q, diracStep_balance A hh hA, diracStep_balance B hh hB, by rw [hE, hE]; ring, hD, hAct,
    diracStep_balance _ hh hs⟩

end Interconnect

/-! ## 3. The restriction facet joined by interconnection -/

section Restriction

variable {𝕜 : Type*} [Field 𝕜]

/-- [proved-derived; formal-checked] **Relabelling ports carries morphisms**: a morphism `P` of
`D → D'` is, read through `e` and `e'`, the morphism `reindex e' e P` of the relabelled
structures. -/
theorem isMorphism_reindex {ι ι' κ κ' : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    {P : Matrix ι' ι 𝕜} {D : Submodule 𝕜 (Bond 𝕜 ι)} {D' : Submodule 𝕜 (Bond 𝕜 ι')}
    (hP : IsMorphism P D D') (e : ι ≃ κ) (e' : ι' ≃ κ') :
    IsMorphism (Matrix.reindex e' e P) (D.map (bondReindex (𝕜 := 𝕜) e).toLinearMap)
      (D'.map (bondReindex (𝕜 := 𝕜) e').toLinearMap) := by
  rintro b ⟨f, hf, hD⟩
  rw [Submodule.mem_map_equiv, Holonics.HolarchyCore.bondReindex_symm_apply] at hD
  rw [SetLike.mem_coe, Submodule.mem_map_equiv, Holonics.HolarchyCore.bondReindex_symm_apply]
  refine hP ⟨f ∘ e, ?_, ?_⟩
  · rw [← hf]
    ext i
    simp [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  · convert hD using 2
    ext i
    simp [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]

variable {α α' β β' τ : Type*} [Fintype α] [Fintype α'] [Fintype β] [Fintype β'] [Fintype τ]
  [DecidableEq τ]

/-- [proved-derived; formal-checked] **The restriction facet is joined by interconnection**: side
morphisms `[PA 0; 0 1]` and `[1 0; 0 PB]`, the identity on the shared ports, give the morphism
`[PA 0; 0 PB]` of the interconnections, through the same shared bond. -/
theorem interconnect_isMorphism {DA : Submodule 𝕜 (Bond 𝕜 (α ⊕ τ))}
    {DB : Submodule 𝕜 (Bond 𝕜 (τ ⊕ β))} {DA' : Submodule 𝕜 (Bond 𝕜 (α' ⊕ τ))}
    {DB' : Submodule 𝕜 (Bond 𝕜 (τ ⊕ β'))} (PA : Matrix α' α 𝕜) (PB : Matrix β' β 𝕜)
    (hA : IsMorphism (fromBlocks PA 0 0 1) DA DA') (hB : IsMorphism (fromBlocks 1 0 0 PB) DB DB') :
    IsMorphism (fromBlocks PA 0 0 PB) (interconnect DA DB) (interconnect DA' DB') := by
  rintro b ⟨f, hf, hD⟩
  obtain ⟨q, hqA, hqB⟩ := mem_interconnect.mp hD
  refine mem_interconnect.mpr ⟨q, hA ⟨Sum.elim (f ∘ Sum.inl) q.1, ?_, ?_⟩,
    hB ⟨Sum.elim (-q.1) (f ∘ Sum.inr), ?_, ?_⟩⟩
  · simp only [partA]
    rw [← hf]
    ext i
    rcases i with i | i <;> simp [fromBlocks_mulVec]
  · convert hqA using 1
    ext i
    · rfl
    · rcases i with i | i <;> simp [partA, fromBlocks_mulVec, fromBlocks_transpose]
  · simp only [partB]
    rw [← hf]
    ext i
    rcases i with i | i <;> simp [fromBlocks_mulVec]
  · convert hqB using 1
    ext i
    · rfl
    · rcases i with i | i <;> simp [partB, fromBlocks_mulVec, fromBlocks_transpose]

end Restriction

section RestrictionPortHolon

variable {𝕜 : Type*} [Field 𝕜]
variable {σA ρA πA αA σB ρB πB αB σA' ρA' πA' αA' σB' ρB' πB' αB' τ : Type*}
  [Fintype σA] [Fintype ρA] [Fintype πA] [Fintype αA]
  [Fintype σB] [Fintype ρB] [Fintype πB] [Fintype αB]
  [Fintype σA'] [Fintype ρA'] [Fintype πA'] [Fintype αA']
  [Fintype σB'] [Fintype ρB'] [Fintype πB'] [Fintype αB'] [Fintype τ]
  [DecidableEq σA] [DecidableEq ρA] [DecidableEq πA] [DecidableEq αA]
  [DecidableEq σB] [DecidableEq ρB] [DecidableEq πB] [DecidableEq αB]
  [DecidableEq σA'] [DecidableEq ρA'] [DecidableEq πA'] [DecidableEq αA']
  [DecidableEq σB'] [DecidableEq ρB'] [DecidableEq πB'] [DecidableEq αB'] [DecidableEq τ]

/-- [proved-derived; formal-checked] **The port-Holon form**: side morphisms read through `splitA`
and `splitB` give the morphism read through `mergeKinds` of `A.interconnect B → A'.interconnect B'`.
-/
theorem portHolon_interconnect_isMorphism (A : PortHolon 𝕜 σA ρA (πA ⊕ τ) αA)
    (B : PortHolon 𝕜 σB ρB (τ ⊕ πB) αB) (A' : PortHolon 𝕜 σA' ρA' (πA' ⊕ τ) αA')
    (B' : PortHolon 𝕜 σB' ρB' (τ ⊕ πB') αB')
    (PA : Matrix (Ports σA' ρA' πA' αA') (Ports σA ρA πA αA) 𝕜)
    (PB : Matrix (Ports σB' ρB' πB' αB') (Ports σB ρB πB αB) 𝕜)
    (hA : IsMorphism (Matrix.reindex splitA.symm splitA.symm (fromBlocks PA 0 0 1)) A.D A'.D)
    (hB : IsMorphism (Matrix.reindex splitB.symm splitB.symm (fromBlocks 1 0 0 PB)) B.D B'.D) :
    IsMorphism (Matrix.reindex mergeKinds mergeKinds (fromBlocks PA 0 0 PB))
      (A.interconnect B).D (A'.interconnect B').D := by
  have hA' := isMorphism_reindex hA splitA splitA
  have hB' := isMorphism_reindex hB splitB splitB
  rw [← Matrix.reindex_symm, Equiv.apply_symm_apply] at hA' hB'
  exact isMorphism_reindex (interconnect_isMorphism PA PB hA' hB') mergeKinds mergeKinds

end RestrictionPortHolon

/-! ## 4. The discrete face law of joint reception -/

section Reception

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {σH ρH αH σR ρR αR τ : Type*} [Fintype σH] [Fintype ρH] [Fintype αH] [Fintype σR]
  [Fintype ρR] [Fintype αR] [Fintype τ]

/-- [proved-derived; formal-checked] **Joint reception at a midpoint step**: the interface delivers
`−h⟨Δ̄, G Δ̄⟩ ≤ 0` to the two sides, and `ΔE_H + ΔE_R = −h(D_H + D_R + ⟨Δ̄, G Δ̄⟩) + h·supply`. -/
theorem joint_reception_step (H : PortHolon 𝕜 σH ρH τ αH) (Rcv : PortHolon 𝕜 σR ρR τ αR)
    (G : Matrix τ τ 𝕜) (hG : ∀ v, 0 ≤ v ⬝ᵥ (G *ᵥ v)) {h : 𝕜} (hh : 0 < h)
    {xH xH' : σH → 𝕜} {xR xR' : σR → 𝕜} {fRH : ρH → 𝕜} {fRR : ρR → 𝕜} {eH eR : τ → 𝕜}
    {fAH eAH : αH → 𝕜} {fAR eAR : αR → 𝕜}
    (hH : DiracStep H h xH xH' fRH (-(G *ᵥ (eH - eR))) eH fAH eAH)
    (hR : DiracStep Rcv h xR xR' fRR (G *ᵥ (eH - eR)) eR fAR eAR) :
    h * (eH ⬝ᵥ (-(G *ᵥ (eH - eR))) + eR ⬝ᵥ (G *ᵥ (eH - eR))) =
        -(h * ((eH - eR) ⬝ᵥ (G *ᵥ (eH - eR)))) ∧
      h * (eH ⬝ᵥ (-(G *ᵥ (eH - eR))) + eR ⬝ᵥ (G *ᵥ (eH - eR))) ≤ 0 ∧
      (storageEnergy H.Q xH' - storageEnergy H.Q xH) +
          (storageEnergy Rcv.Q xR' - storageEnergy Rcv.Q xR) =
        -(h * (fRH ⬝ᵥ (H.R *ᵥ fRH) + fRR ⬝ᵥ (Rcv.R *ᵥ fRR) + (eH - eR) ⬝ᵥ (G *ᵥ (eH - eR)))) +
          h * (eAH ⬝ᵥ fAH + eAR ⬝ᵥ fAR) := by
  obtain ⟨hpow, hD⟩ := active_receiver_law G hG eH eR
  simp only [power] at hpow
  refine ⟨by rw [hpow]; ring, by rw [hpow]; nlinarith, ?_⟩
  rw [diracStep_balance H hh.ne' hH, diracStep_balance Rcv hh.ne' hR]
  linear_combination h * hpow

/-- [proved-derived; formal-checked] **Joint reception is passive**: with `R_H, R_R ⪰ 0` and `G`
passive, the two stores together grow by no more than `h` times the active supply. -/
theorem joint_reception_passive (H : PortHolon 𝕜 σH ρH τ αH) (Rcv : PortHolon 𝕜 σR ρR τ αR)
    (hRH : ∀ f, 0 ≤ f ⬝ᵥ (H.R *ᵥ f)) (hRR : ∀ f, 0 ≤ f ⬝ᵥ (Rcv.R *ᵥ f))
    (G : Matrix τ τ 𝕜) (hG : ∀ v, 0 ≤ v ⬝ᵥ (G *ᵥ v)) {h : 𝕜} (hh : 0 < h)
    {xH xH' : σH → 𝕜} {xR xR' : σR → 𝕜} {fRH : ρH → 𝕜} {fRR : ρR → 𝕜} {eH eR : τ → 𝕜}
    {fAH eAH : αH → 𝕜} {fAR eAR : αR → 𝕜}
    (hH : DiracStep H h xH xH' fRH (-(G *ᵥ (eH - eR))) eH fAH eAH)
    (hR : DiracStep Rcv h xR xR' fRR (G *ᵥ (eH - eR)) eR fAR eAR) :
    (storageEnergy H.Q xH' - storageEnergy H.Q xH) +
        (storageEnergy Rcv.Q xR' - storageEnergy Rcv.Q xR) ≤ h * (eAH ⬝ᵥ fAH + eAR ⬝ᵥ fAR) := by
  rw [(joint_reception_step H Rcv G hG hh hH hR).2.2]
  have h1 := hRH fRH
  have h2 := hRR fRR
  have h3 := hG (eH - eR)
  nlinarith

end Reception

/-! ## 5. The RC witness -/

section RC

variable {𝕜 : Type*} [Field 𝕜]

/-- [definition] One node joining every port of `ι`: the all-ones incidence. -/
def oneNode (ι : Type*) : Matrix ι Unit 𝕜 := Matrix.of fun _ _ => 1

/-- [proved-derived; formal-checked] The Kirchhoff structure of one node: the flows sum to zero and
every effort is one potential. -/
theorem mem_kirchhoff_oneNode {ι : Type*} [Fintype ι] (b : Bond 𝕜 ι) :
    b ∈ kirchhoff (oneNode ι : Matrix ι Unit 𝕜) ↔ (∑ i, b.1 i = 0) ∧ ∃ c : 𝕜, ∀ i, b.2 i = c := by
  constructor
  · rintro ⟨h1, φ, hφ⟩
    refine ⟨?_, φ (), fun i => ?_⟩
    · simpa [oneNode, mulVec, dotProduct] using congrFun h1 ()
    · rw [← hφ]; simp [oneNode, mulVec, dotProduct]
  · rintro ⟨h1, c, hc⟩
    refine ⟨funext fun _ => by simpa [oneNode, mulVec, dotProduct] using h1, fun _ => c,
      funext fun i => by simp [oneNode, mulVec, dotProduct, hc]⟩

/-- [definition] **The capacitor**: one storage port with `Q = C⁻¹` and one shared port, joined by
the one-node Kirchhoff structure. -/
def capacitor (C : 𝕜) : PortHolon 𝕜 Unit Empty (Empty ⊕ Unit) Empty where
  D := kirchhoff (oneNode _)
  dirac := kirchhoff_isDirac _
  Q := Matrix.of fun _ _ => C⁻¹
  Q_symm := by ext i j; rfl
  R := 0

/-- [definition] **The resistor**: one resistive port with resistance `R` and one shared port,
joined by the one-node Kirchhoff structure. -/
def resistor (R : 𝕜) : PortHolon 𝕜 Empty Unit (Unit ⊕ Empty) Empty where
  D := kirchhoff (oneNode _)
  dirac := kirchhoff_isDirac _
  Q := 0
  Q_symm := by simp
  R := Matrix.of fun _ _ => R

/-- [proved-derived; formal-checked] The capacitor's structure is the link of its storage port to
its shared port: flows opposite, efforts equal. -/
theorem capacitor_link (C : 𝕜) (b : Bond 𝕜 (Ports Unit Empty (Empty ⊕ Unit) Empty)) :
    b ∈ (capacitor C).D ↔
      b.1 (Sum.inr (Sum.inr (Sum.inl (Sum.inr ())))) = -b.1 (Sum.inl ()) ∧
        b.2 (Sum.inr (Sum.inr (Sum.inl (Sum.inr ())))) = b.2 (Sum.inl ()) := by
  change b ∈ kirchhoff (oneNode _) ↔ _
  rw [mem_kirchhoff_oneNode]
  simp only [Fintype.sum_sum_type, Fintype.sum_empty, Fintype.sum_unique, zero_add, add_zero]
  constructor
  · rintro ⟨h1, c, hc⟩
    exact ⟨by linear_combination h1, by rw [hc, hc]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [h1]; ring, b.2 (Sum.inl ()), ?_⟩
    rintro (i | i | (i | i) | i)
    · rfl
    · exact i.elim
    · exact i.elim
    · exact h2
    · exact i.elim

/-- [proved-derived; formal-checked] The resistor's structure is the link of its resistive port to
its shared port: flows opposite, efforts equal. -/
theorem resistor_link (R : 𝕜) (b : Bond 𝕜 (Ports Empty Unit (Unit ⊕ Empty) Empty)) :
    b ∈ (resistor R).D ↔
      b.1 (Sum.inr (Sum.inr (Sum.inl (Sum.inl ())))) = -b.1 (Sum.inr (Sum.inl ())) ∧
        b.2 (Sum.inr (Sum.inr (Sum.inl (Sum.inl ())))) = b.2 (Sum.inr (Sum.inl ())) := by
  change b ∈ kirchhoff (oneNode _) ↔ _
  rw [mem_kirchhoff_oneNode]
  simp only [Fintype.sum_sum_type, Fintype.sum_empty, Fintype.sum_unique, zero_add, add_zero]
  constructor
  · rintro ⟨h1, c, hc⟩
    exact ⟨by linear_combination h1, by rw [hc, hc]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [h1]; ring, b.2 (Sum.inr (Sum.inl ())), ?_⟩
    rintro (i | i | (i | i) | i)
    · exact i.elim
    · rfl
    · exact h2
    · exact i.elim
    · exact i.elim

/-- [definition] **The RC circuit**: the capacitor and the resistor interconnected at their shared
port. -/
def rcCircuit (C R : 𝕜) :
    PortHolon 𝕜 (Unit ⊕ Empty) (Empty ⊕ Unit) (Empty ⊕ Empty) (Empty ⊕ Empty) :=
  (capacitor C).interconnect (resistor R)

/-- [proved-derived; formal-checked] The RC circuit admits a point with `f_R = v` and
`−R f_R = C⁻¹ x`, through the shared bond `(v, C⁻¹ x)`. -/
theorem rcCircuit_admits {C R : 𝕜} {x v : Unit ⊕ Empty → 𝕜} {f : Empty ⊕ Unit → 𝕜}
    {fP eP : Empty ⊕ Empty → 𝕜} {fA eA : Empty ⊕ Empty → 𝕜}
    (hflow : f (Sum.inr ()) = v (Sum.inl ())) (hlaw : -(R * f (Sum.inr ())) = C⁻¹ * x (Sum.inl ())) :
    (rcCircuit C R).Admits (rcCircuit C R).Q x v f fP eP fA eA := by
  refine (PortHolon.mem_interconnect _ _ _).mpr
    ⟨(fun _ => v (Sum.inl ()), fun _ => C⁻¹ * x (Sum.inl ())), ?_, ?_⟩
  · rw [Holonics.HolarchyCore.leftPart_assemble]
    show _ ∈ kirchhoff (oneNode _)
    rw [mem_kirchhoff_oneNode]
    refine ⟨?_, C⁻¹ * x (Sum.inl ()), ?_⟩
    · simp [assemble, Fintype.sum_sum_type]
    · rintro (i | i | (i | i) | i)
      all_goals first
        | exact i.elim
        | simp [assemble, rcCircuit, PortHolon.interconnect, capacitor, resistor, mulVec,
            dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type]
  · rw [Holonics.HolarchyCore.rightPart_assemble]
    show _ ∈ kirchhoff (oneNode _)
    rw [mem_kirchhoff_oneNode]
    refine ⟨?_, C⁻¹ * x (Sum.inl ()), ?_⟩
    · simp [assemble, Fintype.sum_sum_type, hflow]
    · rintro (i | i | (i | i) | i)
      all_goals first
        | exact i.elim
        | simp [assemble, rcCircuit, PortHolon.interconnect, capacitor, resistor, mulVec,
            dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type, ← hlaw]

/-- [proved-derived; formal-checked] **The RC circuit's admitted points are the RC law**: admitted
exactly when `f_R = v` and `−R f_R = C⁻¹ x`. -/
theorem rcCircuit_admits_iff {C R : 𝕜} {x v : Unit ⊕ Empty → 𝕜} {f : Empty ⊕ Unit → 𝕜}
    {fP eP : Empty ⊕ Empty → 𝕜} {fA eA : Empty ⊕ Empty → 𝕜} :
    (rcCircuit C R).Admits (rcCircuit C R).Q x v f fP eP fA eA ↔
      f (Sum.inr ()) = v (Sum.inl ()) ∧ -(R * f (Sum.inr ())) = C⁻¹ * x (Sum.inl ()) := by
  refine ⟨fun hadm => ?_, fun h => rcCircuit_admits h.1 h.2⟩
  obtain ⟨q, hA, hB⟩ := (PortHolon.mem_interconnect _ _ _).mp hadm
  rw [Holonics.HolarchyCore.leftPart_assemble] at hA
  rw [Holonics.HolarchyCore.rightPart_assemble] at hB
  change _ ∈ kirchhoff (oneNode _) at hA hB
  rw [mem_kirchhoff_oneNode] at hA hB
  obtain ⟨hA1, cA, hA2⟩ := hA
  obtain ⟨hB1, cB, hB2⟩ := hB
  have a1 := hA2 (Sum.inl ())
  have a2 := hA2 (Sum.inr (Sum.inr (Sum.inl (Sum.inr ()))))
  have b1 := hB2 (Sum.inr (Sum.inl ()))
  have b2 := hB2 (Sum.inr (Sum.inr (Sum.inl (Sum.inl ()))))
  simp [assemble, Fintype.sum_sum_type, rcCircuit, PortHolon.interconnect, capacitor, resistor,
    mulVec, dotProduct, Matrix.fromBlocks] at hA1 hB1 a1 a2 b1 b2
  exact ⟨by linear_combination hA1 + hB1, by linear_combination b1 - b2 + a2 - a1⟩

/-- [proved-derived; formal-checked] The RC circuit stores `E = C⁻¹ x² / 2`. -/
theorem rcCircuit_energy (C R : 𝕜) (x : Unit ⊕ Empty → 𝕜) :
    storageEnergy (rcCircuit C R).Q x = C⁻¹ * x (Sum.inl ()) ^ 2 / 2 := by
  simp [storageEnergy, rcCircuit, PortHolon.interconnect, capacitor, resistor, mulVec, dotProduct,
    Matrix.fromBlocks, Fintype.sum_sum_type]
  ring

/-- [proved-derived; formal-checked] The RC circuit dissipates `⟨f, R f⟩ = R f_R²`. -/
theorem rcCircuit_dissipation (C R : 𝕜) (f : Empty ⊕ Unit → 𝕜) :
    f ⬝ᵥ ((rcCircuit C R).R *ᵥ f) = R * f (Sum.inr ()) ^ 2 := by
  simp [rcCircuit, PortHolon.interconnect, capacitor, resistor, mulVec, dotProduct,
    Matrix.fromBlocks, Fintype.sum_sum_type]
  ring

/-- [proved-standard; formal-checked] **One midpoint step of the RC circuit**: `x′ = x(2RC − h)/(2RC
+ h)` is admitted in Dirac form with `f̄ = −2x/(2RC + h)`, and `E′ − E = −hR f̄²`. -/
theorem rc_midpoint_step [CharZero 𝕜] {C R h y : 𝕜} (hC : C ≠ 0) (hh : h ≠ 0)
    (hd : 2 * R * C + h ≠ 0) :
    DiracStep (rcCircuit C R) h (fun _ => y) (fun _ => y * (2 * R * C - h) / (2 * R * C + h))
        (fun _ => -(2 * y) / (2 * R * C + h)) 0 0 0 0 ∧
      storageEnergy (rcCircuit C R).Q (fun _ => y * (2 * R * C - h) / (2 * R * C + h)) -
          storageEnergy (rcCircuit C R).Q (fun _ => y) =
        -(h * (R * (-(2 * y) / (2 * R * C + h)) ^ 2)) := by
  have hs : DiracStep (rcCircuit C R) h (fun _ => y)
      (fun _ => y * (2 * R * C - h) / (2 * R * C + h)) (fun _ => -(2 * y) / (2 * R * C + h))
      0 0 0 0 := by
    apply rcCircuit_admits
    · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      have e1 : y * (2 * R * C - h) / (2 * R * C + h) - y = -(2 * h * y) / (2 * R * C + h) := by
        rw [eq_div_iff hd, sub_mul, div_mul_cancel₀ _ hd]
        ring
      rw [e1]
      linear_combination (2 * y / (2 * R * C + h)) * inv_mul_cancel₀ hh
    · simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      have e1 : y + y * (2 * R * C - h) / (2 * R * C + h) = 4 * R * C * y / (2 * R * C + h) := by
        rw [eq_div_iff hd, add_mul, div_mul_cancel₀ _ hd]
        ring
      rw [e1]
      linear_combination (-(2 * R * y / (2 * R * C + h))) * inv_mul_cancel₀ hC
  refine ⟨hs, ?_⟩
  rw [diracStep_balance _ hh hs, rcCircuit_dissipation]
  simp

/-- [proved-derived; formal-checked] **Witness over `ℚ`**: at `C = R = h = 1` the step from `3`
reaches `1` with `f̄ = −2`, and the stored energy falls by `4 = hR f̄²`. -/
theorem rc_midpoint_witness :
    DiracStep (rcCircuit (1 : ℚ) 1) 1 (fun _ => 3) (fun _ => 1) (fun _ => -2) 0 0 0 0 ∧
      storageEnergy (rcCircuit (1 : ℚ) 1).Q (fun _ => 1) -
        storageEnergy (rcCircuit (1 : ℚ) 1).Q (fun _ => 3) = -4 := by
  have := rc_midpoint_step (C := (1 : ℚ)) (R := 1) (h := 1) (y := 3) one_ne_zero one_ne_zero
    (by norm_num)
  norm_num at this
  exact this

end RC

section RCMotion

/-- [definition] **The RC motion** `x(t) = x₀ e^(−t/(RC))`. -/
def rcMotion (C R x₀ t : ℝ) : Unit ⊕ Empty → ℝ := fun _ => x₀ * Real.exp (-(t / (R * C)))

/-- [definition] Its rate `−x(t)/(RC)`. -/
def rcRate (C R x₀ t : ℝ) : ℝ := -(x₀ * Real.exp (-(t / (R * C)))) / (R * C)

/-- [proved-standard; formal-checked] **The RC motion is admitted at every `t`**: its rate is
`v = −x/(RC)`, and the RC circuit admits `(x(t), v)` with `f_R = v` and no external or active bond.
-/
theorem rc_motion_admitted {C R : ℝ} (hC : C ≠ 0) (hR : R ≠ 0) (x₀ t : ℝ) :
    (∀ i, HasDerivAt (fun s => rcMotion C R x₀ s i) (rcRate C R x₀ t) t) ∧
      (rcCircuit C R).Admits (rcCircuit C R).Q (rcMotion C R x₀ t) (fun _ => rcRate C R x₀ t)
        (fun _ => rcRate C R x₀ t) 0 0 0 0 := by
  refine ⟨fun _ => ?_, rcCircuit_admits rfl ?_⟩
  · have hd := (((hasDerivAt_id t).div_const (R * C)).neg.exp).const_mul x₀
    refine HasDerivAt.congr_deriv (f := fun s => rcMotion C R x₀ s _) hd ?_
    show x₀ * (Real.exp (-(t / (R * C))) * -(1 / (R * C))) = rcRate C R x₀ t
    rw [rcRate]
    ring
  · simp only [rcRate, rcMotion]
    field_simp

/-- [proved-standard; formal-checked] **The RC energy rate**: along the motion,
`dE/dt = −R f_R²` with `f_R = v`. -/
theorem rc_energy_rate {C R : ℝ} (hC : C ≠ 0) (hR : R ≠ 0) (x₀ t : ℝ) :
    HasDerivAt (fun s => storageEnergy (rcCircuit C R).Q (rcMotion C R x₀ s))
      (-(R * rcRate C R x₀ t ^ 2)) t := by
  obtain ⟨hx, hadm⟩ := rc_motion_admitted hC hR x₀ t
  have := (rcCircuit C R).energy_balance_const hx hadm
  convert this using 1
  rw [rcCircuit_dissipation]
  simp

/-- [proved-standard; formal-checked] **The RC energy decays**: `E(t) = E(0) e^(−2t/(RC))`. -/
theorem rc_energy_decay (C R x₀ t : ℝ) :
    storageEnergy (rcCircuit C R).Q (rcMotion C R x₀ t) =
      storageEnergy (rcCircuit C R).Q (rcMotion C R x₀ 0) * Real.exp (-(2 * t / (R * C))) := by
  rw [rcCircuit_energy, rcCircuit_energy]
  simp only [rcMotion, zero_div, neg_zero, Real.exp_zero, mul_one]
  have he : Real.exp (-(2 * t / (R * C))) = Real.exp (-(t / (R * C))) ^ 2 := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [he]
  ring

end RCMotion

end Holonics.HolonCore.InterconnectionJoin
