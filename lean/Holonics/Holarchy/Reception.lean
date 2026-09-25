import Holonics.Holarchy.Receipt
import Holonics.Holon.Law
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Holarchy.Reception: joint reception solves its step and returns both next states

[definition] Object 10 of `docs/ELEMENTARY_OBJECTS.md`: **to receive is to measure and compare**,
and reception is an interaction `I_C(|H_S⟩, |H_R⟩) = (|H'_S⟩, |H'_R⟩, f_R)` that changes both
participants. A source and a receiver are joined in one port-Hamiltonian law (`JointLaw`): block
storage `Q = diag(Q_S, Q_R)`, a skew interconnection `J` that carries their coupling, a resistive
relation `R` and a boundary supply `B`. One implicit-midpoint step of the law from the present
state `x` under the supply `u` is the linear system
`(1 − (h/2)(J − R)Q) x⁺ = (1 + (h/2)(J − R)Q) x + h B u` (`stepMatrix`, `stepSource`,
`jointStep_iff`). `interact` **solves** it: when the step matrix is invertible it returns the unique
next state of both participants (`solveStep`) read into an `InteractionReturn` (`readStep`): both
next states, the receiver's face, the receipt, the boundary bond, the stored energy before and
after, the dissipation, the supplied power, the certified balance, and the unresolved fibre;
otherwise it returns a typed refusal carrying a nonzero kernel vector of the step matrix
(`StepRefusal.singular`).

[proved-derived; formal-checked]

* **The step is solved, not given.** `interact` returns a return exactly when the step matrix is
  invertible (`interact_ok_iff`); the returned next state satisfies the midpoint step and is the
  only state that does (`interact_solves`).
* **The power balance** `ΔE + dissipation = supplied` holds exactly on every admitted step and is
  carried by the return (`InteractionReturn.balance`, by `Holon/Element.midpoint_balance`); the
  stored energy splits into the two participants' own (`readStep_stored_split`,
  `Holon/Law.storageEnergy_blocks`).
* **The boundary bond** is the port bond `(u, Bᵀ ē)` at the supply ports, flow the supply and effort
  the midpoint effort pulled back through `B`; its power times the step is the supplied energy
  (`boundaryBond_power`).
* **Passivity is a theorem**: with `⟨v, R v⟩ ≥ 0` and a nonnegative step the stored energy grows by
  no more than the supply (`readStep_passive`).
* **The moving receiver.** Along a motion of the joint law, `ẋ = F(x, u) = (J − R)Qx + Bu`, the rate
  of a face `y(t) = ρ(t, x_S(t), x_R(t))` is `ẏ = D_Sρ F_S + D_Rρ F_R + ∂_tρ` with `F_S`, `F_R` the
  source and receiver blocks of the law's field (`moving_receiver_rate_of_law`, over the chain
  rule `moving_receiver_rate`); `Transport/ChangingReceiver` owns the case with no receiver state.
* **`HolonLaw.receive` is the zero-storage specialization.** A receiver with `Q_R = 0` has zero
  effort, so it exerts no back-action: the source advances by its own block of the law, the
  receiver's change is a linear reading of the source's midpoint effort plus its own supply, the
  bond it presents to the source is a passive-coholon bond of zero power
  (`Holon/Law.passive_reading`), and the joint balance is the source's own balance
  (`zero_storage_receiver_is_passive_reading`).

[counterexample; formal-checked] **Reception changes both participants**: `interact` solves the
gyrator pair from a source at `1` and a receiver at `0` to `3/5` and `4/5`, the receiver gaining
exactly the `8/25` the source loses (`reception_changes_both`). **A singular step is refused**:
the active pair at step `2` has the zero step matrix (`singular_step_refused`). **Passivity needs
its hypothesis**: an active element `R = −1` triples the state with no supply
(`active_element_is_not_passive`). **The fibre is plural**: a face reading one receiver coordinate
leaves the other unresolved (`unresolved_fibre_is_plural`).
-/

noncomputable section

namespace Holonics.Receiver

open Matrix
open Holonics.HolonCore

/-! ## 1. The joint law and its admitted steps -/

section Joint

variable {𝕜 : Type*} [Field 𝕜] {σS σR μ : Type*} [Fintype σS] [Fintype σR] [Fintype μ]

/-- [definition] **The joint law of a source and a receiver**: block storage, a skew
interconnection carrying their coupling, a resistive relation and a boundary supply map. -/
structure JointLaw (𝕜 σS σR μ : Type*) [Field 𝕜] [Fintype σS] [Fintype σR] where
  QS : Matrix σS σS 𝕜
  QR : Matrix σR σR 𝕜
  QS_symm : QSᵀ = QS
  QR_symm : QRᵀ = QR
  J : Matrix (σS ⊕ σR) (σS ⊕ σR) 𝕜
  J_skew : Jᵀ = -J
  R : Matrix (σS ⊕ σR) (σS ⊕ σR) 𝕜
  B : Matrix (σS ⊕ σR) μ 𝕜

/-- [definition] The block storage `diag(Q_S, Q_R)`. -/
def JointLaw.Q (L : JointLaw 𝕜 σS σR μ) : Matrix (σS ⊕ σR) (σS ⊕ σR) 𝕜 :=
  Matrix.fromBlocks L.QS 0 0 L.QR

omit [Fintype μ] in
theorem JointLaw.Q_symm (L : JointLaw 𝕜 σS σR μ) : L.Qᵀ = L.Q := by
  rw [JointLaw.Q, Matrix.fromBlocks_transpose, L.QS_symm, L.QR_symm]; simp

/-- [definition] **An admitted joint step**: one implicit-midpoint step of the joint law. -/
structure JointStep (L : JointLaw 𝕜 σS σR μ) where
  h : 𝕜
  before : σS ⊕ σR → 𝕜
  after : σS ⊕ σR → 𝕜
  supply : μ → 𝕜
  step : after - before =
    h • ((L.J - L.R) *ᵥ (L.Q *ᵥ ((1 / 2 : 𝕜) • (before + after))) + L.B *ᵥ supply)

/-- [definition] The midpoint effort `ē = Q (x + x⁺)/2`. -/
def JointStep.effort {L : JointLaw 𝕜 σS σR μ} (s : JointStep L) : σS ⊕ σR → 𝕜 :=
  L.Q *ᵥ ((1 / 2 : 𝕜) • (s.before + s.after))

/-- [definition] **What an interaction returns.** The balance is a certified field. -/
structure InteractionReturn (𝕜 σS σR μ Face Region : Type*) [Field 𝕜] where
  nextSource : σS → 𝕜
  nextReceiver : σR → 𝕜
  face : Face
  receipt : Receipt 𝕜 Region
  /-- The port bond at the supply ports: the supply as flow, the pulled-back midpoint effort. -/
  boundaryBond : Bond 𝕜 μ
  storedBefore : 𝕜
  storedAfter : 𝕜
  dissipated : 𝕜
  supplied : 𝕜
  balance : storedAfter - storedBefore + dissipated = supplied
  unresolved : Set (σR → 𝕜)
  next_mem_unresolved : nextReceiver ∈ unresolved

variable [CharZero 𝕜] {Face Region : Type*}

/-- [definition] **The reading of one admitted joint step** (`readStep`): its two next states read by
the receiver's face `ρ` and the receipt law, the boundary bond, and the certified balance. The step
is given; `interact` below solves for it. -/
def readStep {L : JointLaw 𝕜 σS σR μ} (s : JointStep L) (ρ : (σR → 𝕜) → Face)
    (law : ReceiptLaw 𝕜 (σS ⊕ σR → 𝕜) Region) : InteractionReturn 𝕜 σS σR μ Face Region where
  nextSource := s.after ∘ Sum.inl
  nextReceiver := s.after ∘ Sum.inr
  face := ρ (s.after ∘ Sum.inr)
  receipt := law.receive s.after
  boundaryBond := (s.supply, L.Bᵀ *ᵥ s.effort)
  storedBefore := storageEnergy L.Q s.before
  storedAfter := storageEnergy L.Q s.after
  dissipated := s.h * (s.effort ⬝ᵥ (L.R *ᵥ s.effort))
  supplied := s.h * (s.effort ⬝ᵥ (L.B *ᵥ s.supply))
  balance := by
    have := midpoint_balance L.Q_symm L.J_skew L.B s.h s.before s.after s.supply s.step
    unfold JointStep.effort
    linear_combination this
  unresolved := {x | ρ x = ρ (s.after ∘ Sum.inr)}
  next_mem_unresolved := rfl

/-- [proved-derived; formal-checked] **The boundary bond carries the supplied power**: the step
times its power `⟨Bᵀē, u⟩` is the supplied energy `h⟨ē, Bu⟩`. -/
theorem boundaryBond_power {L : JointLaw 𝕜 σS σR μ} (s : JointStep L) (ρ : (σR → 𝕜) → Face)
    (law : ReceiptLaw 𝕜 (σS ⊕ σR → 𝕜) Region) :
    s.h * power (readStep s ρ law).boundaryBond = (readStep s ρ law).supplied := by
  simp only [readStep, power]
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]

omit [CharZero 𝕜] [Fintype μ] in
theorem storageEnergy_joint (L : JointLaw 𝕜 σS σR μ) (x : σS ⊕ σR → 𝕜) :
    storageEnergy L.Q x = storageEnergy L.QS (x ∘ Sum.inl) + storageEnergy L.QR (x ∘ Sum.inr) := by
  rw [← storageEnergy_blocks, JointLaw.Q, Sum.elim_comp_inl_inr]

/-- [proved-derived; formal-checked] **The stored energy is the two participants' own**, before and
after. -/
theorem readStep_stored_split {L : JointLaw 𝕜 σS σR μ} (s : JointStep L) (ρ : (σR → 𝕜) → Face)
    (law : ReceiptLaw 𝕜 (σS ⊕ σR → 𝕜) Region) :
    (readStep s ρ law).storedAfter =
        storageEnergy L.QS (readStep s ρ law).nextSource +
          storageEnergy L.QR (readStep s ρ law).nextReceiver ∧
      (readStep s ρ law).storedBefore =
        storageEnergy L.QS (s.before ∘ Sum.inl) + storageEnergy L.QR (s.before ∘ Sum.inr) :=
  ⟨storageEnergy_joint L s.after, storageEnergy_joint L s.before⟩

/-- [proved-derived; formal-checked] **Passivity is a theorem, not an assumption**: with the
resistive relation positive semidefinite and a nonnegative step, the stored energy of the pair
grows by no more than the supplied boundary power. -/
theorem readStep_passive [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {L : JointLaw 𝕜 σS σR μ}
    (s : JointStep L) (ρ : (σR → 𝕜) → Face) (law : ReceiptLaw 𝕜 (σS ⊕ σR → 𝕜) Region)
    (hR : ∀ v, 0 ≤ v ⬝ᵥ (L.R *ᵥ v)) (hh : 0 ≤ s.h) :
    (readStep s ρ law).storedAfter - (readStep s ρ law).storedBefore ≤
      (readStep s ρ law).supplied := by
  have hbal := (readStep s ρ law).balance
  have hdiss : 0 ≤ (readStep s ρ law).dissipated := mul_nonneg hh (hR _)
  linarith

/-- [proved-derived; formal-checked] **The unresolved fibre**: every receiver state in it returns
the same face as the actual next state. -/
theorem readStep_unresolved_face {L : JointLaw 𝕜 σS σR μ} (s : JointStep L)
    (ρ : (σR → 𝕜) → Face) (law : ReceiptLaw 𝕜 (σS ⊕ σR → 𝕜) Region) (x : σR → 𝕜)
    (hx : x ∈ (readStep s ρ law).unresolved) : ρ x = (readStep s ρ law).face := hx

end Joint

/-! ## 2. `interact` solves the joint step -/

section Solve

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {σS σR μ : Type*} [Fintype σS] [Fintype σR]
  [Fintype μ] [DecidableEq σS] [DecidableEq σR] {Face Region : Type*}

/-- [definition] **The step matrix** of the implicit midpoint rule, `1 − (h/2)(J − R)Q`. -/
def stepMatrix (L : JointLaw 𝕜 σS σR μ) (h : 𝕜) : Matrix (σS ⊕ σR) (σS ⊕ σR) 𝕜 :=
  1 - (h / 2) • ((L.J - L.R) * L.Q)

/-- [definition] **The known side of the step**, `(1 + (h/2)(J − R)Q) x + h B u`. -/
def stepSource (L : JointLaw 𝕜 σS σR μ) (h : 𝕜) (x : σS ⊕ σR → 𝕜) (u : μ → 𝕜) :
    σS ⊕ σR → 𝕜 :=
  x + (h / 2) • (((L.J - L.R) * L.Q) *ᵥ x) + h • (L.B *ᵥ u)

omit [CharZero 𝕜] in
/-- [proved-derived; formal-checked] **The midpoint step is a linear system for the next state**:
`x⁺ − x = h((J − R)Q(x + x⁺)/2 + Bu)` exactly when `stepMatrix x⁺ = stepSource x u`. -/
theorem jointStep_iff (L : JointLaw 𝕜 σS σR μ) (h : 𝕜) (x after : σS ⊕ σR → 𝕜) (u : μ → 𝕜) :
    after - x = h • ((L.J - L.R) *ᵥ (L.Q *ᵥ ((1 / 2 : 𝕜) • (x + after))) + L.B *ᵥ u) ↔
      stepMatrix L h *ᵥ after = stepSource L h x u := by
  have hA : ∀ v, (L.J - L.R) *ᵥ (L.Q *ᵥ v) = ((L.J - L.R) * L.Q) *ᵥ v := fun v =>
    (Matrix.mulVec_mulVec _ _ _)
  simp only [hA, stepMatrix, stepSource, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.mulVec_smul, Matrix.mulVec_add, smul_add, smul_smul]
  constructor
  · intro heq
    funext i
    have := congrFun heq i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linear_combination this
  · intro heq
    funext i
    have := congrFun heq i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linear_combination this

omit [CharZero 𝕜] in
/-- [definition] **The solved step** when the step matrix is invertible: the next state
`x⁺ = stepMatrix⁻¹ stepSource`. -/
def solveStep (L : JointLaw 𝕜 σS σR μ) (h : 𝕜) (x : σS ⊕ σR → 𝕜) (u : μ → 𝕜)
    (hM : IsUnit (stepMatrix L h).det) : JointStep L where
  h := h
  before := x
  after := (stepMatrix L h)⁻¹ *ᵥ stepSource L h x u
  supply := u
  step := by
    rw [jointStep_iff, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]

omit [CharZero 𝕜] in
/-- [proved-derived; formal-checked] **The solved next state is the only one**: every state that
satisfies the midpoint step from `x` under `u` is `solveStep`'s. -/
theorem solveStep_unique (L : JointLaw 𝕜 σS σR μ) (h : 𝕜) (x : σS ⊕ σR → 𝕜) (u : μ → 𝕜)
    (hM : IsUnit (stepMatrix L h).det) (after : σS ⊕ σR → 𝕜)
    (hafter : after - x =
      h • ((L.J - L.R) *ᵥ (L.Q *ᵥ ((1 / 2 : 𝕜) • (x + after))) + L.B *ᵥ u)) :
    after = (solveStep L h x u hM).after := by
  rw [jointStep_iff] at hafter
  change after = (stepMatrix L h)⁻¹ *ᵥ stepSource L h x u
  rw [← hafter, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]

/-- [definition] **Why a step is refused**: the step matrix is singular, witnessed by a nonzero
state it annihilates. -/
inductive StepRefusal (L : JointLaw 𝕜 σS σR μ) (h : 𝕜) : Type _ where
  | singular (notUnit : ¬ IsUnit (stepMatrix L h).det)
      (kernel : ∃ v ≠ 0, stepMatrix L h *ᵥ v = 0)

open Classical in
/-- [definition] **`interact`/`receive`**: solve one implicit-midpoint step of the joint law from
the state `x` under the supply `u` and return its reading, or refuse a singular step. -/
def interact (L : JointLaw 𝕜 σS σR μ) (h : 𝕜) (x : σS ⊕ σR → 𝕜) (u : μ → 𝕜)
    (ρ : (σR → 𝕜) → Face) (law : ReceiptLaw 𝕜 (σS ⊕ σR → 𝕜) Region) :
    Except (StepRefusal L h) (InteractionReturn 𝕜 σS σR μ Face Region) :=
  if hM : IsUnit (stepMatrix L h).det then .ok (readStep (solveStep L h x u hM) ρ law)
  else .error (.singular hM (Matrix.exists_mulVec_eq_zero_iff.mpr
    (by rwa [isUnit_iff_ne_zero, not_not] at hM)))

/-- [proved-derived; formal-checked] **`interact` returns exactly when the step matrix is
invertible.** -/
theorem interact_ok_iff (L : JointLaw 𝕜 σS σR μ) (h : 𝕜) (x : σS ⊕ σR → 𝕜) (u : μ → 𝕜)
    (ρ : (σR → 𝕜) → Face) (law : ReceiptLaw 𝕜 (σS ⊕ σR → 𝕜) Region) :
    (∃ r, interact L h x u ρ law = .ok r) ↔ IsUnit (stepMatrix L h).det := by
  unfold interact
  constructor
  · rintro ⟨r, hr⟩
    split_ifs at hr with hM
    exact hM
  · intro hM
    exact ⟨_, dif_pos hM⟩

/-- [proved-derived; formal-checked] **`interact` solves for both next states.** A returned
interaction's next source and receiver states together satisfy the midpoint step from `x` under
`u`, and they are the only states that do. -/
theorem interact_solves {L : JointLaw 𝕜 σS σR μ} {h : 𝕜} {x : σS ⊕ σR → 𝕜} {u : μ → 𝕜}
    {ρ : (σR → 𝕜) → Face} {law : ReceiptLaw 𝕜 (σS ⊕ σR → 𝕜) Region}
    {r : InteractionReturn 𝕜 σS σR μ Face Region} (hr : interact L h x u ρ law = .ok r) :
    Sum.elim r.nextSource r.nextReceiver - x =
        h • ((L.J - L.R) *ᵥ (L.Q *ᵥ ((1 / 2 : 𝕜) • (x + Sum.elim r.nextSource r.nextReceiver))) +
          L.B *ᵥ u) ∧
      ∀ after, after - x = h • ((L.J - L.R) *ᵥ (L.Q *ᵥ ((1 / 2 : 𝕜) • (x + after))) + L.B *ᵥ u) →
        after = Sum.elim r.nextSource r.nextReceiver := by
  unfold interact at hr
  split_ifs at hr with hM
  cases hr
  have hsum : Sum.elim (readStep (solveStep L h x u hM) ρ law).nextSource
      (readStep (solveStep L h x u hM) ρ law).nextReceiver = (solveStep L h x u hM).after := by
    funext i; rcases i with i | i <;> rfl
  rw [hsum]
  exact ⟨(solveStep L h x u hM).step, fun after ha => solveStep_unique L h x u hM after ha⟩

end Solve

/-! ## 3. The zero-storage specialization is `HolonLaw.receive` -/

section ZeroStorage

variable {𝕜 : Type*} [Field 𝕜] {σS σR μ : Type*} [Fintype σS] [Fintype σR] [Fintype μ]

theorem mulVec_of_inr_zero (M : Matrix (σS ⊕ σR) (σS ⊕ σR) 𝕜) (v : σS ⊕ σR → 𝕜)
    (hv : v ∘ Sum.inr = 0) :
    (M *ᵥ v) ∘ Sum.inl = M.toBlocks₁₁ *ᵥ (v ∘ Sum.inl) ∧
      (M *ᵥ v) ∘ Sum.inr = M.toBlocks₂₁ *ᵥ (v ∘ Sum.inl) := by
  have hv' : ∀ j, v (Sum.inr j) = 0 := fun j => congrFun hv j
  constructor <;> funext i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁,
      hv']

/-- [proved-derived; formal-checked] **`HolonLaw.receive` is the zero-storage specialization of
joint reception.** When the receiver stores nothing (`Q_R = 0`):

1. its midpoint effort is zero, so the bond it presents to the source through the coupling —
   flow `(J − R)_SR ē_R`, effort `ē_S` — is a passive-coholon bond: zero flow, zero power, and any
   linear reading of it reads the effort alone (`Holon/Law.passive_reading`);
2. the source advances by its own block of the law, `Δx_S = h((J − R)_SS ē_S + (B u)_S)`;
3. the receiver's change is a linear reading of the source's effort, `Δx_R = h (J − R)_RS ē_S`,
   plus its own supply;
4. the joint balance is the source's own:
   `E_S(x_S⁺) − E_S(x_S) + h⟨ē_S, R_SS ē_S⟩ = h⟨ē_S, (B u)_S⟩`. -/
theorem zero_storage_receiver_is_passive_reading [CharZero 𝕜] {L : JointLaw 𝕜 σS σR μ}
    (hQR : L.QR = 0) (s : JointStep L) :
    s.effort ∘ Sum.inr = 0 ∧
      (((L.J - L.R).toBlocks₁₂ *ᵥ (s.effort ∘ Sum.inr), s.effort ∘ Sum.inl) : Bond 𝕜 σS) ∈
        passiveCoholon 𝕜 σS ∧
      power (((L.J - L.R).toBlocks₁₂ *ᵥ (s.effort ∘ Sum.inr), s.effort ∘ Sum.inl) : Bond 𝕜 σS) = 0 ∧
      (s.after - s.before) ∘ Sum.inl =
        s.h • ((L.J - L.R).toBlocks₁₁ *ᵥ (s.effort ∘ Sum.inl) + (L.B *ᵥ s.supply) ∘ Sum.inl) ∧
      (s.after - s.before) ∘ Sum.inr =
        s.h • ((L.J - L.R).toBlocks₂₁ *ᵥ (s.effort ∘ Sum.inl) + (L.B *ᵥ s.supply) ∘ Sum.inr) ∧
      storageEnergy L.QS (s.after ∘ Sum.inl) - storageEnergy L.QS (s.before ∘ Sum.inl) +
          s.h * ((s.effort ∘ Sum.inl) ⬝ᵥ (L.R.toBlocks₁₁ *ᵥ (s.effort ∘ Sum.inl))) =
        s.h * ((s.effort ∘ Sum.inl) ⬝ᵥ ((L.B *ᵥ s.supply) ∘ Sum.inl)) := by
  have heR : s.effort ∘ Sum.inr = 0 := by
    funext i
    simp [JointStep.effort, JointLaw.Q, Matrix.fromBlocks_mulVec, hQR]
  have hflow : (L.J - L.R).toBlocks₁₂ *ᵥ (s.effort ∘ Sum.inr) = 0 := by
    rw [heR, mulVec_zero]
  have hcoh : (((L.J - L.R).toBlocks₁₂ *ᵥ (s.effort ∘ Sum.inr), s.effort ∘ Sum.inl) :
      Bond 𝕜 σS) ∈ passiveCoholon 𝕜 σS := hflow
  obtain ⟨hM₁, hM₂⟩ := mulVec_of_inr_zero (L.J - L.R) s.effort heR
  obtain ⟨hR₁, _⟩ := mulVec_of_inr_zero L.R s.effort heR
  have hstep := s.step
  have hstepS : (s.after - s.before) ∘ Sum.inl =
      s.h • ((L.J - L.R).toBlocks₁₁ *ᵥ (s.effort ∘ Sum.inl) + (L.B *ᵥ s.supply) ∘ Sum.inl) := by
    rw [hstep, ← hM₁]; rfl
  have hstepR : (s.after - s.before) ∘ Sum.inr =
      s.h • ((L.J - L.R).toBlocks₂₁ *ᵥ (s.effort ∘ Sum.inl) + (L.B *ᵥ s.supply) ∘ Sum.inr) := by
    rw [hstep, ← hM₂]; rfl
  refine ⟨heR, hcoh, (passive_reading _ hcoh 0).1, hstepS, hstepR, ?_⟩
  have hbal := (readStep s (fun _ => ()) (⟨fun _ _ => 0, fun _ => 0, fun _ => 1, fun _ => 1⟩ :
    ReceiptLaw 𝕜 (σS ⊕ σR → 𝕜) Unit)).balance
  simp only [readStep] at hbal
  have hsplit : ∀ x : σS ⊕ σR → 𝕜, storageEnergy L.Q x = storageEnergy L.QS (x ∘ Sum.inl) := by
    intro x
    rw [storageEnergy_joint, hQR]
    simp [storageEnergy]
  have hdot : ∀ w : σS ⊕ σR → 𝕜, s.effort ⬝ᵥ w = (s.effort ∘ Sum.inl) ⬝ᵥ (w ∘ Sum.inl) := by
    intro w
    have h0 : ∀ j, s.effort (Sum.inr j) = 0 := fun j => congrFun heR j
    simp [dotProduct, Fintype.sum_sum_type, h0]
  rw [hsplit, hsplit, hdot, hdot, hR₁] at hbal
  exact hbal

end ZeroStorage

/-! ## 4. The moving receiver -/

section Moving

variable {XS XR Y : Type*} [NormedAddCommGroup XS] [NormedSpace ℝ XS]
  [NormedAddCommGroup XR] [NormedSpace ℝ XR] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- [proved-derived; formal-checked] **The moving-receiver rate** `ẏ = D_Sρ F_S + D_Rρ F_R + ∂_tρ`.
The face of a receiver that moves and changes reads the source's motion through `D_Sρ`, its own
motion through `D_Rρ` and the explicit motion of its chart through `∂_tρ`. -/
theorem moving_receiver_rate {ρ : ℝ × XS × XR → Y} {Dρ : ℝ × XS × XR →L[ℝ] Y}
    {xS : ℝ → XS} {xR : ℝ → XR} {FS : XS} {FR : XR} {t : ℝ}
    (hρ : HasFDerivAt ρ Dρ (t, xS t, xR t)) (hS : HasDerivAt xS FS t)
    (hR : HasDerivAt xR FR t) :
    HasDerivAt (fun s => ρ (s, xS s, xR s)) (Dρ (0, FS, 0) + Dρ (0, 0, FR) + Dρ (1, 0, 0)) t := by
  have hpath : HasDerivAt (fun s => (s, xS s, xR s)) ((1 : ℝ), FS, FR) t :=
    (hasDerivAt_id t).prodMk (hS.prodMk hR)
  have h := hρ.comp_hasDerivAt t hpath
  have hsplit : Dρ (0, FS, 0) + Dρ (0, 0, FR) + Dρ (1, 0, 0) = Dρ ((1 : ℝ), FS, FR) := by
    rw [← map_add, ← map_add]
    congr 1
    ext <;> simp
  rw [hsplit]
  exact h

end Moving

/-! ### Along the joint law -/

section MovingLaw

variable {σS σR μ : Type*} [Fintype σS] [Fintype σR] [Fintype μ]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- [definition] **The field of the joint law**, `F(x, u) = (J − R)Qx + Bu`. -/
def JointLaw.field (L : JointLaw ℝ σS σR μ) (x : σS ⊕ σR → ℝ) (u : μ → ℝ) : σS ⊕ σR → ℝ :=
  (L.J - L.R) *ᵥ (L.Q *ᵥ x) + L.B *ᵥ u

/-- [proved-derived; formal-checked] **The moving receiver along the joint law.** Along a motion
`ẋ = F(x, u)` of the joint law, a face `y(t) = ρ(t, x_S(t), x_R(t))` moves at
`ẏ = D_Sρ F_S + D_Rρ F_R + ∂_tρ`, with `F_S` and `F_R` the source and receiver blocks of the law's
field (`moving_receiver_rate`). -/
theorem moving_receiver_rate_of_law (L : JointLaw ℝ σS σR μ) {x : ℝ → σS ⊕ σR → ℝ}
    {u : ℝ → μ → ℝ} {t : ℝ} (hx : HasDerivAt x (L.field (x t) (u t)) t)
    {ρ : ℝ × (σS → ℝ) × (σR → ℝ) → Y} {Dρ : ℝ × (σS → ℝ) × (σR → ℝ) →L[ℝ] Y}
    (hρ : HasFDerivAt ρ Dρ (t, x t ∘ Sum.inl, x t ∘ Sum.inr)) :
    HasDerivAt (fun s => ρ (s, x s ∘ Sum.inl, x s ∘ Sum.inr))
      (Dρ (0, L.field (x t) (u t) ∘ Sum.inl, 0) + Dρ (0, 0, L.field (x t) (u t) ∘ Sum.inr) +
        Dρ (1, 0, 0)) t := by
  have hS : HasDerivAt (fun s => x s ∘ Sum.inl) (L.field (x t) (u t) ∘ Sum.inl) t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mp hx (Sum.inl i)
  have hR : HasDerivAt (fun s => x s ∘ Sum.inr) (L.field (x t) (u t) ∘ Sum.inr) t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mp hx (Sum.inr i)
  exact moving_receiver_rate hρ hS hR

end MovingLaw


/-! ## 5. Witnesses -/

section Witnesses

/-- [definition] Two unit capacitors joined by a gyrator: `J = [[0, −1], [1, 0]]`. -/
def gyratorPair : JointLaw ℚ Unit Unit Unit where
  QS := 1
  QR := 1
  QS_symm := by simp
  QR_symm := by simp
  J := Matrix.fromBlocks 0 (-1) 1 0
  J_skew := by
    rw [Matrix.fromBlocks_transpose]
    ext (i | i) (j | j) <;> simp
  R := 0
  B := 0

theorem gyratorPair_Q : gyratorPair.Q = 1 := by
  simp [JointLaw.Q, gyratorPair, Matrix.fromBlocks_one]

/-- [definition] One admitted step of the gyrator pair from source `1`, receiver `0`. -/
def gyratorStep : JointStep gyratorPair where
  h := 1
  before := Sum.elim (fun _ => 1) (fun _ => 0)
  after := Sum.elim (fun _ => 3 / 5) (fun _ => 4 / 5)
  supply := 0
  step := by
    rw [gyratorPair_Q]
    ext (i | i) <;>
      simp [gyratorPair, Matrix.mulVec, dotProduct, Fintype.sum_sum_type] <;> norm_num

/-- The gyrator's step matrix at `h = 1` is invertible: its determinant is `5/4`. -/
theorem gyratorPair_stepMatrix_isUnit : IsUnit (stepMatrix gyratorPair 1).det := by
  rw [isUnit_iff_ne_zero]
  have : (stepMatrix gyratorPair 1) =
      Matrix.fromBlocks (1 : Matrix Unit Unit ℚ) (Matrix.of fun _ _ => 1 / 2)
        (Matrix.of fun _ _ => -(1 / 2)) 1 := by
    rw [stepMatrix, gyratorPair_Q, Matrix.mul_one]
    ext (i | i) (j | j) <;> simp [gyratorPair, Matrix.fromBlocks]
  rw [this, Matrix.det_fromBlocks_one₁₁]
  simp [Matrix.det_unique, Matrix.mul_apply]
  norm_num

/-- The solved gyrator step is the admitted one. -/
theorem gyrator_solved :
    solveStep gyratorPair 1 (Sum.elim (fun _ => 1) (fun _ => 0)) 0
      gyratorPair_stepMatrix_isUnit = gyratorStep := by
  have h := solveStep_unique gyratorPair 1 (Sum.elim (fun _ => 1) (fun _ => 0)) 0
    gyratorPair_stepMatrix_isUnit gyratorStep.after gyratorStep.step
  simp only [solveStep, gyratorStep] at h ⊢
  congr 1
  exact h.symm

/-- [counterexample; formal-checked] **Reception changes both participants.** `interact` solves
the gyrator pair from source `1`, receiver `0`: the receiver moves to `4/5` and the source to
`3/5`; with nothing supplied and nothing dissipated, the receiver gains exactly the `8/25` the
source loses. -/
theorem reception_changes_both :
    ∃ r, interact gyratorPair 1 (Sum.elim (fun _ => 1) (fun _ => 0)) 0
        (fun x : Unit → ℚ => x ())
        (⟨fun _ _ => 0, fun _ => 0, fun _ => 1, fun _ => 1⟩ : ReceiptLaw ℚ (Unit ⊕ Unit → ℚ) Unit) =
          .ok r ∧
      r.nextSource () = 3 / 5 ∧ r.nextReceiver () = 4 / 5 ∧ r.face = 4 / 5 ∧
      storageEnergy gyratorPair.QS r.nextSource - storageEnergy gyratorPair.QS (fun _ => 1) =
        -(8 / 25) ∧
      storageEnergy gyratorPair.QR r.nextReceiver - storageEnergy gyratorPair.QR (fun _ => 0) =
        8 / 25 ∧
      r.supplied = 0 ∧ r.dissipated = 0 := by
  refine ⟨_, dif_pos gyratorPair_stepMatrix_isUnit, ?_⟩
  rw [gyrator_solved]
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [readStep, gyratorStep, gyratorPair, storageEnergy, dotProduct]; norm_num
  · simp [readStep, gyratorStep, gyratorPair, storageEnergy, dotProduct]; norm_num
  · simp [readStep, gyratorPair]
  · simp [readStep, gyratorPair]

/-- [definition] Two unit capacitors with an active (negative) resistive relation `R = −1`. -/
def activePair : JointLaw ℚ Unit Unit Unit where
  QS := 1
  QR := 1
  QS_symm := by simp
  QR_symm := by simp
  J := 0
  J_skew := by simp
  R := -1
  B := 0

theorem activePair_Q : activePair.Q = 1 := by
  simp [JointLaw.Q, activePair, Matrix.fromBlocks_one]

/-- [counterexample; formal-checked] **A singular step is refused.** For the active pair at step
`h = 2` the step matrix `1 − (2/2)(0 − (−1))·1` is zero, so `interact` returns the typed refusal. -/
theorem singular_step_refused (x : Unit ⊕ Unit → ℚ) (u : Unit → ℚ) :
    ∃ e, interact activePair 2 x u (fun x : Unit → ℚ => x ())
      (⟨fun _ _ => 0, fun _ => 0, fun _ => 1, fun _ => 1⟩ : ReceiptLaw ℚ (Unit ⊕ Unit → ℚ) Unit) =
        .error e := by
  have h0 : stepMatrix activePair 2 = 0 := by
    rw [stepMatrix, activePair_Q, Matrix.mul_one]
    simp [activePair]
  have hM : ¬ IsUnit (stepMatrix activePair 2).det := by
    rw [h0, Matrix.det_zero]
    exact not_isUnit_zero
  unfold interact
  rw [dif_neg hM]
  exact ⟨_, rfl⟩

/-- [definition] Its admitted step from `(1, 0)`: the state triples. -/
def activeStep : JointStep activePair where
  h := 1
  before := Sum.elim (fun _ => 1) (fun _ => 0)
  after := Sum.elim (fun _ => 3) (fun _ => 0)
  supply := 0
  step := by
    rw [activePair_Q]
    ext (i | i) <;> norm_num [activePair]

/-- [counterexample; formal-checked] **Passivity needs `R ⪰ 0`.** With the active relation `R = −1`
and no supply, the stored energy grows from `1/2` to `9/2`, beyond the zero supplied; the balance
still closes, with dissipation `−4`. -/
theorem active_element_is_not_passive :
    let r := readStep activeStep (fun x : Unit → ℚ => x ())
      (⟨fun _ _ => 0, fun _ => 0, fun _ => 1, fun _ => 1⟩ : ReceiptLaw ℚ (Unit ⊕ Unit → ℚ) Unit)
    r.storedBefore = 1 / 2 ∧ r.storedAfter = 9 / 2 ∧ r.supplied = 0 ∧ r.dissipated = -4 ∧
      ¬ (r.storedAfter - r.storedBefore ≤ r.supplied) := by
  intro r
  have hb : r.storedBefore = 1 / 2 := by
    simp [r, readStep, activeStep, activePair_Q, storageEnergy, dotProduct, Fintype.sum_sum_type]
  have ha : r.storedAfter = 9 / 2 := by
    simp [r, readStep, activeStep, activePair_Q, storageEnergy, dotProduct, Fintype.sum_sum_type]
    norm_num
  have hs : r.supplied = 0 := by simp [r, readStep, activePair]
  have hd : r.dissipated = -4 := by
    simp only [r, readStep, JointStep.effort, activePair_Q]
    simp [activeStep, activePair, dotProduct, Matrix.mulVec, Fintype.sum_sum_type]
    norm_num
  refine ⟨hb, ha, hs, hd, ?_⟩
  rw [ha, hb, hs]
  norm_num

/-- [counterexample; formal-checked] **The unresolved fibre is plural** when the face reads only
one receiver coordinate: moving the other coordinate returns the same face. -/
theorem unresolved_fibre_is_plural {L : JointLaw ℚ Unit (Fin 2) Unit} (s : JointStep L)
    (law : ReceiptLaw ℚ (Unit ⊕ Fin 2 → ℚ) Unit) :
    ∃ x ∈ (readStep s (fun x : Fin 2 → ℚ => x 0) law).unresolved,
      x ≠ (readStep s (fun x : Fin 2 → ℚ => x 0) law).nextReceiver := by
  refine ⟨Function.update (s.after ∘ Sum.inr) 1 (s.after (Sum.inr 1) + 1), ?_, ?_⟩
  · show Function.update (s.after ∘ Sum.inr) 1 (s.after (Sum.inr 1) + 1) 0 = (s.after ∘ Sum.inr) 0
    rw [Function.update_of_ne (by decide)]
  · intro h
    have := congrFun h 1
    simp [readStep] at this

end Witnesses

end Holonics.Receiver
