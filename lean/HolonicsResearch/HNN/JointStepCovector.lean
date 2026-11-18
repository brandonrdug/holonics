import Holonics.Holarchy.Reception
import Mathlib

/-!
# The joint step's own covector, and a deposit that keeps the step passive

#410 (box "The exact owner's covector for the joint step"; record
`research/records/2026-10-29_MUTUAL_CONTACT_THE_COMPARISON_IS_A_PAIR_CONTACT_THAT_MOVES_THE_PRODUCED_FACE_AND_THE_TARGETS_ENCODING.md`
§3; atlas `tower.mutual-contact`, which listed `JointLaw`'s own covector as owed). The joint law of a
source and a receiver (`Holarchy/Reception.JointLaw`) takes one implicit-midpoint step

```text
M x′ = A x + h B u,     M = I − (h/2)(J − R)Q,     A = I + (h/2)(J − R)Q
```

(`Holarchy/Reception.stepMatrix`, `stepSource`, `solveStep`). A comparison read on the next state
returns a covector `g′` on `x′`. This file returns it through the step to every operand that
produced `x′`, with the operands the forward already holds.

[proved-derived; formal-checked] What is proved.

1. **The adjoint state** (`adjointState`, `adjointState_spec`, `adjoint_pairing`): with `M`
   invertible, `λ = M⁻ᵀ g′` is the one solution of `Mᵀ λ = g′`, and `⟨g′, M⁻¹ w⟩ = ⟨λ, w⟩` for
   every `w`.
2. **The covector on the opening state and on the supply** (`covector_state`,
   `covector_supply`): the step is affine in `x` and in `u`, so the variation is first order with no
   remainder: `⟨g′, x′(x + v) − x′(x)⟩ = ⟨Aᵀλ, v⟩` and `⟨g′, x′(u + w) − x′(u)⟩ = ⟨h Bᵀλ, w⟩`.
3. **The covector on the resistance** (`resistance_variation`, `covector_resistance_exact`,
   `resistanceCovector_pairing`, `hasDerivAt_resistance`): for a change `R ↦ R + E` the next state
   moves by exactly `−h M_E⁻¹ E ē`, `ē = Q x̄`, `x̄ = (x + x′)/2` the base step's midpoint, so
   `⟨g′, δx′⟩ = −h ⟨λ_E, E ē⟩` with `λ_E` the adjoint state at the moved resistance. Along the line
   `R + tE` the derivative at `t = 0` is `−h ⟨λ, E ē⟩`, and for a symmetric direction this is the
   Frobenius pairing of `E` with `G_R = −h sym(λ ēᵀ)`, `sym(abᵀ) = (abᵀ + baᵀ)/2`.
4. **Passivity is proved** (`passive_step`, `passive_step_supply`): for `J` skew, `Q` symmetric,
   `R ⪰ 0` and `h ≥ 0`, the stored energy `½ xᵀQx` does not rise over an unsupplied step, and
   rises by no more than the supply `h⟨ē, Bu⟩` over a supplied one (through
   `Holon/Element.midpoint_balance`).
5. **A deposit certified to keep the resistance positive** (`deposit_posSemidef`,
   `deposit_symm`, `deposit_passive`): the deposit `R′ = R − η G_R = R + ηh sym(λ ēᵀ)` keeps
   `R′ ⪰ 0` whenever `R ⪰ c·I` and `ηh(|λ|² + |ē|²)/2 ≤ c`, since
   `vᵀ sym(abᵀ) v = (v·a)(v·b) ≥ −|v|²(|a|² + |b|²)/2`; so the next step under `R′` is passive by
   item 4, and passivity is proved at every deposit, never assumed. The deposit descends the
   comparison to first order: `⟨G_R, R′ − R⟩ = −η ‖G_R‖² ≤ 0` (`deposit_descends`).
6. **The joint law** (`stepMatrix_eq`, `stepSource_eq`, `solveStep_after_eq`): the reception
   owner's step matrix is `M`, its known side `A x + h B u`, and its solved next state is `next`, so
   every statement above holds for `Holarchy/Reception.interact`'s step.

[agent-inferred] **Limits.** The certificate of item 5 is one sufficient bound against a floor `c`
of `R`; it does not say the least `η` that breaks `R′ ⪰ 0` (that is the least eigenvalue of
`R + ηh sym(λēᵀ)`, read on a rank-two update). The derivative of item 3 is along one line, a
directional derivative; the exact difference of item 3 holds for every finite change with an
invertible moved step. The covector on `J` and on `Q` are not stated here. Over ℝ alone: the
complex chart of the pair's moves is `Holon/Cayley`'s. No Rust owner exists yet; the live consumer
the box names is the tower's mutual contact (atlas `tower.mutual-contact`).

The computational object is the helical pair interaction: the joint step is one pair contact read
at its midpoint (the Cayley chart of the pair's turn with its dissipation), and the covector
returns to both participants through the same operands, as the mutual contact's slip does. Of the
winding guide's six general objects this touches the pair (the contact's step and its return) and
the tube (one clocked tick); the helix, faces and placement, the cell holonomy and the tower thread
stay attached.

Consumers: the atlas rows `tower.mutual-contact` and `holarchy.moving-receiver-three-term`; the
reception owner `Holarchy/Reception`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.JointStepCovector

open Matrix Filter Topology
open Holonics.HolonCore Holonics.Receiver

variable {ι μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ]

/-! ## 1. The step and its adjoint state -/

/-- [definition] **The closing matrix** of the implicit midpoint rule, `M = I − (h/2)(J − R)Q`. -/
def closeMatrix (J R Q : Matrix ι ι ℝ) (h : ℝ) : Matrix ι ι ℝ :=
  1 - (h / 2) • ((J - R) * Q)

/-- [definition] **The opening matrix**, `A = I + (h/2)(J − R)Q`. -/
def openMatrix (J R Q : Matrix ι ι ℝ) (h : ℝ) : Matrix ι ι ℝ :=
  1 + (h / 2) • ((J - R) * Q)

/-- [definition] **The solved next state**, `x′ = M⁻¹(A x + h B u)`. -/
def next (J R Q : Matrix ι ι ℝ) (B : Matrix ι μ ℝ) (h : ℝ) (x : ι → ℝ) (u : μ → ℝ) : ι → ℝ :=
  (closeMatrix J R Q h)⁻¹ *ᵥ (openMatrix J R Q h *ᵥ x + h • (B *ᵥ u))

/-- [definition] **The adjoint state** `λ = M⁻ᵀ g′` of a covector `g′` on the next state. -/
def adjointState (J R Q : Matrix ι ι ℝ) (h : ℝ) (g : ι → ℝ) : ι → ℝ :=
  (closeMatrix J R Q h)⁻¹ᵀ *ᵥ g

/-- [definition] **The midpoint** `x̄ = (x + x′)/2` of a step. -/
def midpoint (x x' : ι → ℝ) : ι → ℝ := (1 / 2 : ℝ) • (x + x')

variable {J R Q : Matrix ι ι ℝ} {B : Matrix ι μ ℝ} {h : ℝ}

/-- [proved-derived; formal-checked] **The solved state closes the step**: `M x′ = A x + h B u`. -/
theorem next_spec (hM : IsUnit (closeMatrix J R Q h).det) (x : ι → ℝ) (u : μ → ℝ) :
    closeMatrix J R Q h *ᵥ next J R Q B h x u = openMatrix J R Q h *ᵥ x + h • (B *ᵥ u) := by
  rw [next, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]

/-- [proved-derived; formal-checked] **The closed step is the midpoint step**:
`x′ − x = h((J − R)Q x̄ + B u)`. -/
theorem next_midpoint (hM : IsUnit (closeMatrix J R Q h).det) (x : ι → ℝ) (u : μ → ℝ) :
    next J R Q B h x u - x =
      h • ((J - R) *ᵥ (Q *ᵥ midpoint x (next J R Q B h x u)) + B *ᵥ u) := by
  have hs := next_spec (B := B) hM x u
  set x' := next J R Q B h x u
  have hA : ∀ v, (J - R) *ᵥ (Q *ᵥ v) = ((J - R) * Q) *ᵥ v := fun v =>
    Matrix.mulVec_mulVec _ _ _
  simp only [closeMatrix, openMatrix, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec] at hs
  rw [midpoint, hA]
  simp only [Matrix.mulVec_smul, Matrix.mulVec_add, smul_add, smul_smul]
  funext i
  have := congrFun hs i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
  linear_combination this

/-- [proved-derived; formal-checked] **The adjoint state solves `Mᵀ λ = g′`.** -/
theorem adjointState_spec (hM : IsUnit (closeMatrix J R Q h).det) (g : ι → ℝ) :
    (closeMatrix J R Q h)ᵀ *ᵥ adjointState J R Q h g = g := by
  have hMt : IsUnit (closeMatrix J R Q h)ᵀ.det := by rwa [Matrix.det_transpose]
  rw [adjointState, Matrix.transpose_nonsing_inv, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hMt, Matrix.one_mulVec]

/-- [proved-derived; formal-checked] **It is the only solution.** -/
theorem adjointState_unique (hM : IsUnit (closeMatrix J R Q h).det) (g l : ι → ℝ)
    (hl : (closeMatrix J R Q h)ᵀ *ᵥ l = g) : l = adjointState J R Q h g := by
  have hMt : IsUnit (closeMatrix J R Q h)ᵀ.det := by rwa [Matrix.det_transpose]
  rw [adjointState, Matrix.transpose_nonsing_inv, ← hl, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hMt, Matrix.one_mulVec]

/-- [proved-derived; formal-checked] **The covector returns through the inverse as the adjoint
state**: `⟨g′, M⁻¹ w⟩ = ⟨λ, w⟩`. -/
theorem adjoint_pairing (g w : ι → ℝ) :
    g ⬝ᵥ ((closeMatrix J R Q h)⁻¹ *ᵥ w) = adjointState J R Q h g ⬝ᵥ w := by
  rw [adjointState, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

/-! ## 2. The covector on the opening state and on the supply -/

/-- [proved-derived; formal-checked] **The opening state's covector is `Aᵀλ`**, with no
remainder: `⟨g′, x′(x + v) − x′(x)⟩ = ⟨Aᵀλ, v⟩`. -/
theorem covector_state (g x v : ι → ℝ) (u : μ → ℝ) :
    g ⬝ᵥ (next J R Q B h (x + v) u - next J R Q B h x u) =
      ((openMatrix J R Q h)ᵀ *ᵥ adjointState J R Q h g) ⬝ᵥ v := by
  have hd : next J R Q B h (x + v) u - next J R Q B h x u =
      (closeMatrix J R Q h)⁻¹ *ᵥ (openMatrix J R Q h *ᵥ v) := by
    simp only [next, Matrix.mulVec_add]
    abel
  rw [hd, adjoint_pairing, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

/-- [proved-derived; formal-checked] **The supply's covector is `h Bᵀλ`**, with no remainder. -/
theorem covector_supply (g x : ι → ℝ) (u w : μ → ℝ) :
    g ⬝ᵥ (next J R Q B h x (u + w) - next J R Q B h x u) =
      (h • (Bᵀ *ᵥ adjointState J R Q h g)) ⬝ᵥ w := by
  have hd : next J R Q B h x (u + w) - next J R Q B h x u =
      (closeMatrix J R Q h)⁻¹ *ᵥ (h • (B *ᵥ w)) := by
    simp only [next, Matrix.mulVec_add, smul_add]
    abel
  rw [hd, adjoint_pairing, dotProduct_smul, smul_dotProduct, Matrix.mulVec_transpose,
    Matrix.dotProduct_mulVec]

/-! ## 3. The covector on the resistance -/

/-- [proved-derived; formal-checked] **A finite change of resistance moves the next state by
exactly `−h M_E⁻¹ E ē`**, `ē = Q x̄` the base step's midpoint effort and `M_E` the moved closing
matrix. -/
theorem resistance_variation (hM : IsUnit (closeMatrix J R Q h).det) (E : Matrix ι ι ℝ)
    (hME : IsUnit (closeMatrix J (R + E) Q h).det) (x : ι → ℝ) (u : μ → ℝ) :
    next J (R + E) Q B h x u - next J R Q B h x u =
      -h • ((closeMatrix J (R + E) Q h)⁻¹ *ᵥ
        (E *ᵥ (Q *ᵥ midpoint x (next J R Q B h x u)))) := by
  have hs := next_spec (B := B) hM x u
  have hs₁ := next_spec (B := B) hME x u
  set x' := next J R Q B h x u
  set x₁ := next J (R + E) Q B h x u
  -- `M_E (x₁ − x′) = −h E Q x̄`
  have key : closeMatrix J (R + E) Q h *ᵥ (x₁ - x') =
      -h • (E *ᵥ (Q *ᵥ midpoint x x')) := by
    have hME' : closeMatrix J (R + E) Q h = closeMatrix J R Q h + (h / 2) • (E * Q) := by
      simp only [closeMatrix]; rw [sub_add_eq_sub_sub, sub_mul, smul_sub]; abel
    have hAE' : openMatrix J (R + E) Q h = openMatrix J R Q h - (h / 2) • (E * Q) := by
      simp only [openMatrix]; rw [sub_add_eq_sub_sub, sub_mul, smul_sub]; abel
    rw [Matrix.mulVec_sub, hs₁, hAE', hME', Matrix.add_mulVec, hs, Matrix.sub_mulVec]
    simp only [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, midpoint,
      Matrix.mulVec_smul, Matrix.mulVec_add]
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have : x₁ - x' = (closeMatrix J (R + E) Q h)⁻¹ *ᵥ (closeMatrix J (R + E) Q h *ᵥ (x₁ - x')) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hME, Matrix.one_mulVec]
  rw [this, key, Matrix.mulVec_smul]

/-- [proved-derived; formal-checked] **The resistance covector, exact**: `⟨g′, δx′⟩ = −h⟨λ_E, E ē⟩`
with `λ_E` the adjoint state at the moved resistance. -/
theorem covector_resistance_exact (hM : IsUnit (closeMatrix J R Q h).det) (E : Matrix ι ι ℝ)
    (hME : IsUnit (closeMatrix J (R + E) Q h).det) (g x : ι → ℝ) (u : μ → ℝ) :
    g ⬝ᵥ (next J (R + E) Q B h x u - next J R Q B h x u) =
      -h * (adjointState J (R + E) Q h g ⬝ᵥ
        (E *ᵥ (Q *ᵥ midpoint x (next J R Q B h x u)))) := by
  rw [resistance_variation hM E hME, dotProduct_smul, adjoint_pairing, smul_eq_mul]

/-- [definition] **The symmetric outer product** `sym(abᵀ) = (abᵀ + baᵀ)/2`. -/
def symOuter (a b : ι → ℝ) : Matrix ι ι ℝ := (1 / 2 : ℝ) • (vecMulVec a b + vecMulVec b a)

/-- [definition] **The resistance covector** `G_R = −h sym(λ ēᵀ)`. -/
def resistanceCovector (h : ℝ) (l e : ι → ℝ) : Matrix ι ι ℝ := -h • symOuter l e

/-- [definition] The Frobenius pairing `⟨G, E⟩ = Σ_ij G_ij E_ij`. -/
def frob (G E : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, G i j * E i j

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] **On a symmetric direction the resistance covector is
`G_R`**: `−h⟨λ, E ē⟩ = ⟨G_R, E⟩` when `Eᵀ = E`. -/
theorem resistanceCovector_pairing (l e : ι → ℝ) (E : Matrix ι ι ℝ) (hE : Eᵀ = E) :
    -h * (l ⬝ᵥ (E *ᵥ e)) = frob (resistanceCovector h l e) E := by
  have hEij : ∀ i j, E j i = E i j := fun i j => by
    rw [← Matrix.transpose_apply E i j, hE]
  have hswap : ∑ i, ∑ j, e i * l j * E i j = ∑ i, ∑ j, l i * e j * E i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hEij]; ring
  have hL : l ⬝ᵥ (E *ᵥ e) = ∑ i, ∑ j, l i * e j * E i j := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hR : frob (resistanceCovector h l e) E =
      ∑ i, ∑ j, (-h * (1 / 2)) * (l i * e j * E i j + e i * l j * E i j) := by
    simp only [frob, resistanceCovector, symOuter, Matrix.smul_apply, Matrix.add_apply,
      vecMulVec_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hL, hR]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hswap]
  ring

/-- [proved-derived; formal-checked] **The derivative along a line of resistances**: at `t = 0`,
`d/dt ⟨g′, x′(R + tE)⟩ = −h⟨λ, E ē⟩`, `λ = M⁻ᵀg′` and `ē = Q x̄` read at the base step. -/
theorem hasDerivAt_resistance (hM : IsUnit (closeMatrix J R Q h).det) (E : Matrix ι ι ℝ)
    (g x : ι → ℝ) (u : μ → ℝ) :
    HasDerivAt (fun t : ℝ => g ⬝ᵥ next J (R + t • E) Q B h x u)
      (-h * (adjointState J R Q h g ⬝ᵥ (E *ᵥ (Q *ᵥ midpoint x (next J R Q B h x u))))) 0 := by
  set w := E *ᵥ (Q *ᵥ midpoint x (next J R Q B h x u)) with hw
  set Mt : ℝ → Matrix ι ι ℝ := fun t => closeMatrix J (R + t • E) Q h with hMt
  have hcont : Continuous Mt := by
    simp only [hMt, closeMatrix]
    fun_prop
  have hM0 : IsUnit (Mt 0).det := by simpa [hMt] using hM
  have hdet : ∀ᶠ t in 𝓝 (0 : ℝ), IsUnit (Mt t).det := by
    have hc : ContinuousAt (fun t : ℝ => (Mt t).det) 0 := hcont.matrix_det.continuousAt
    filter_upwards [hc.eventually_ne hM0.ne_zero] with t ht
    exact isUnit_iff_ne_zero.mpr ht
  set φ : ℝ → ℝ := fun t => -h * (g ⬝ᵥ ((Mt t)⁻¹ *ᵥ w)) with hφ
  have hφc : ContinuousAt φ 0 := by
    have hinv : ContinuousAt (fun t => (Mt t)⁻¹) 0 := by
      have hr : ContinuousAt Ring.inverse (Mt 0).det := by
        have := NormedRing.inverse_continuousAt hM0.unit
        rwa [hM0.unit_spec] at this
      exact (continuousAt_matrix_inv _ hr).comp hcont.continuousAt
    have hF : Continuous fun N : Matrix ι ι ℝ => g ⬝ᵥ (N *ᵥ w) :=
      continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
    exact continuousAt_const.mul (hF.continuousAt.comp hinv)
  have hval : φ 0 = -h * (adjointState J R Q h g ⬝ᵥ w) := by
    simp only [hφ, hMt, zero_smul, add_zero]
    rw [adjoint_pairing]
  rw [← hval, hasDerivAt_iff_tendsto_slope]
  have hφt : Tendsto φ (𝓝[≠] (0 : ℝ)) (𝓝 (φ 0)) := hφc.tendsto.mono_left nhdsWithin_le_nhds
  refine hφt.congr' ?_
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), IsUnit (Mt t).det ∧ t ≠ 0 :=
    (hdet.filter_mono nhdsWithin_le_nhds).and
      (eventually_mem_nhdsWithin.mono fun t ht => Set.mem_compl_singleton_iff.mp ht)
  filter_upwards [hev] with t ⟨ht, ht0⟩
  have hvar := resistance_variation (B := B) hM (t • E) ht x u
  rw [slope_def_field, zero_smul, add_zero, sub_zero, ← dotProduct_sub, hvar,
    Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    smul_eq_mul]
  simp only [hφ, hMt, hw]
  field_simp

/-! ## 4. Passivity is proved -/

/-- [proved-derived; formal-checked] **A supplied step stores no more than its supply**: for `J`
skew, `Q` symmetric, `R ⪰ 0` and `h ≥ 0`, `ΔE ≤ h⟨ē, Bu⟩`. -/
theorem passive_step_supply (hJ : Jᵀ = -J) (hQ : Qᵀ = Q) (hR : ∀ v, 0 ≤ v ⬝ᵥ (R *ᵥ v))
    (hh : 0 ≤ h) (hM : IsUnit (closeMatrix J R Q h).det) (x : ι → ℝ) (u : μ → ℝ) :
    storageEnergy Q (next J R Q B h x u) - storageEnergy Q x ≤
      h * ((Q *ᵥ midpoint x (next J R Q B h x u)) ⬝ᵥ (B *ᵥ u)) := by
  have hm := next_midpoint (B := B) hM x u
  unfold midpoint at hm ⊢
  have hb := midpoint_balance hQ hJ B h x (next J R Q B h x u) u hm
  have hd := mul_nonneg hh (hR (Q *ᵥ ((1 / 2 : ℝ) • (x + next J R Q B h x u))))
  linarith

/-- [proved-derived; formal-checked] **An unsupplied step does not raise the stored energy.** -/
theorem passive_step (hJ : Jᵀ = -J) (hQ : Qᵀ = Q) (hR : ∀ v, 0 ≤ v ⬝ᵥ (R *ᵥ v)) (hh : 0 ≤ h)
    (hM : IsUnit (closeMatrix J R Q h).det) (x : ι → ℝ) :
    storageEnergy Q (next J R Q B h x 0) ≤ storageEnergy Q x := by
  have := passive_step_supply (B := B) hJ hQ hR hh hM x 0
  rw [Matrix.mulVec_zero, dotProduct_zero, mul_zero] at this
  linarith

/-! ## 5. The deposit, certified -/

/-- [definition] **The deposit** `R′ = R − η G_R`. -/
def deposit (R : Matrix ι ι ℝ) (η h : ℝ) (l e : ι → ℝ) : Matrix ι ι ℝ :=
  R - η • resistanceCovector h l e

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] `vᵀ sym(abᵀ) v = (v·a)(v·b)`. -/
theorem symOuter_quad (a b v : ι → ℝ) : v ⬝ᵥ (symOuter a b *ᵥ v) = (v ⬝ᵥ a) * (v ⬝ᵥ b) := by
  have hswap : ∑ i, ∑ j, v i * (b i * a j * v j) = ∑ i, ∑ j, v i * (a i * b j * v j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hl : v ⬝ᵥ (symOuter a b *ᵥ v) =
      (1 / 2) * (∑ i, ∑ j, v i * (a i * b j * v j) + ∑ i, ∑ j, v i * (b i * a j * v j)) := by
    simp only [dotProduct, mulVec, symOuter, Matrix.smul_apply, Matrix.add_apply,
      vecMulVec_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hr : (v ⬝ᵥ a) * (v ⬝ᵥ b) = ∑ i, ∑ j, v i * (a i * b j * v j) := by
    simp only [dotProduct, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hl, hr, hswap]
  ring

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] **The deposit keeps the resistance positive**: if `R ⪰ c·I`
and `ηh(|λ|² + |ē|²)/2 ≤ c`, with `η, h ≥ 0`, then `R′ = R − η G_R ⪰ 0`. -/
theorem deposit_posSemidef {c η : ℝ} (hRc : ∀ v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (R *ᵥ v)) (hη : 0 ≤ η)
    (hh : 0 ≤ h) (l e : ι → ℝ) (hcert : η * h * ((l ⬝ᵥ l) + (e ⬝ᵥ e)) / 2 ≤ c) (v : ι → ℝ) :
    0 ≤ v ⬝ᵥ (deposit R η h l e *ᵥ v) := by
  have hq : v ⬝ᵥ (deposit R η h l e *ᵥ v) =
      v ⬝ᵥ (R *ᵥ v) + η * h * ((v ⬝ᵥ l) * (v ⬝ᵥ e)) := by
    simp only [deposit, resistanceCovector, Matrix.sub_mulVec, Matrix.smul_mulVec,
      dotProduct_sub, dotProduct_smul, symOuter_quad, smul_eq_mul]
    ring
  have cs : ∀ a : ι → ℝ, (v ⬝ᵥ a) ^ 2 ≤ (v ⬝ᵥ v) * (a ⬝ᵥ a) := fun a => by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v a
    simpa [dotProduct, pow_two] using this
  have hvv : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have amgm : -((v ⬝ᵥ l) ^ 2 + (v ⬝ᵥ e) ^ 2) / 2 ≤ (v ⬝ᵥ l) * (v ⬝ᵥ e) := by
    nlinarith [sq_nonneg ((v ⬝ᵥ l) + (v ⬝ᵥ e))]
  have hηh : 0 ≤ η * h := mul_nonneg hη hh
  have hRv := hRc v
  rw [hq]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add (cs l) (cs e)) hηh,
    mul_le_mul_of_nonneg_right hcert hvv, mul_le_mul_of_nonneg_left amgm hηh]

omit [Fintype ι] [DecidableEq ι] in
/-- [proved-derived; formal-checked] **A symmetric resistance stays symmetric under the
deposit.** -/
theorem deposit_symm (hRs : Rᵀ = R) (η : ℝ) (l e : ι → ℝ) :
    (deposit R η h l e)ᵀ = deposit R η h l e := by
  ext i j
  simp only [deposit, resistanceCovector, symOuter, Matrix.transpose_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.add_apply, vecMulVec_apply, smul_eq_mul]
  rw [← Matrix.transpose_apply R j i, hRs]
  ring

/-- [proved-derived; formal-checked] **The deposited step is passive**: under the certificate of
`deposit_posSemidef`, the next unsupplied step with the deposited resistance does not raise the
stored energy. Passivity is read from the deposit, never assumed of it. -/
theorem deposit_passive (hJ : Jᵀ = -J) (hQ : Qᵀ = Q) {c η : ℝ}
    (hRc : ∀ v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (R *ᵥ v)) (hη : 0 ≤ η) (hh : 0 ≤ h) (l e : ι → ℝ)
    (hcert : η * h * ((l ⬝ᵥ l) + (e ⬝ᵥ e)) / 2 ≤ c)
    (hM : IsUnit (closeMatrix J (deposit R η h l e) Q h).det) (x : ι → ℝ) :
    storageEnergy Q (next J (deposit R η h l e) Q B h x 0) ≤ storageEnergy Q x :=
  passive_step hJ hQ (deposit_posSemidef hRc hη hh l e hcert) hh hM x

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] **The deposit descends to first order**:
`⟨G_R, R′ − R⟩ = −η‖G_R‖² ≤ 0`. -/
theorem deposit_descends {η : ℝ} (hη : 0 ≤ η) (l e : ι → ℝ) :
    frob (resistanceCovector h l e) (deposit R η h l e - R) =
        -η * frob (resistanceCovector h l e) (resistanceCovector h l e) ∧
      frob (resistanceCovector h l e) (deposit R η h l e - R) ≤ 0 := by
  have h1 : frob (resistanceCovector h l e) (deposit R η h l e - R) =
      -η * frob (resistanceCovector h l e) (resistanceCovector h l e) := by
    simp only [frob, deposit, sub_sub_cancel_left, Matrix.neg_apply, Matrix.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨h1, ?_⟩
  rw [h1]
  have : 0 ≤ frob (resistanceCovector h l e) (resistanceCovector h l e) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _
  nlinarith

/-! ## 6. The joint law of reception -/

section Reception

variable {σS σR : Type*} [Fintype σS] [Fintype σR] [DecidableEq σS] [DecidableEq σR]

omit [Fintype μ] in
/-- [proved-derived; formal-checked] The reception owner's step matrix is `M`. -/
theorem stepMatrix_eq (L : JointLaw ℝ σS σR μ) (h : ℝ) :
    stepMatrix L h = closeMatrix L.J L.R L.Q h := rfl

/-- [proved-derived; formal-checked] Its known side is `A x + h B u`. -/
theorem stepSource_eq (L : JointLaw ℝ σS σR μ) (h : ℝ) (x : σS ⊕ σR → ℝ) (u : μ → ℝ) :
    stepSource L h x u = openMatrix L.J L.R L.Q h *ᵥ x + h • (L.B *ᵥ u) := by
  simp only [stepSource, openMatrix, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]

/-- [proved-derived; formal-checked] **`interact`'s solved state is `next`**, so every covector
above is the covector of the reception owner's step. -/
theorem solveStep_after_eq (L : JointLaw ℝ σS σR μ) (h : ℝ) (x : σS ⊕ σR → ℝ) (u : μ → ℝ)
    (hM : IsUnit (stepMatrix L h).det) :
    (solveStep L h x u hM).after = next L.J L.R L.Q L.B h x u := by
  change (stepMatrix L h)⁻¹ *ᵥ stepSource L h x u = _
  rw [stepSource_eq, stepMatrix_eq]
  rfl

end Reception

end Holonics.HNN.JointStepCovector
