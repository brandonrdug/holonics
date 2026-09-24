import Holonics.Holon.Dirac
import Holonics.Transport.AffineJointBall
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Holon.Element: element relations, the energy balance and its discrete forms

[definition] The element facet `𝓔`. A `PortHolon` carries a Dirac structure on four port kinds
(storage `σ`, resistive `ρ`, external `π`, active `α`) and linear element relations: storage
`E = ½⟨x, Qx⟩` with effort `Qx` and flow `−ẋ`, resistance `e_R = −R f_R`. External and active
ports are free and their powers are returned by the balance.

[proved-derived; formal-checked]

1. **Pointwise balance** `⟨Qx, ẋ⟩ = −⟨f_R, R f_R⟩ + ⟨e_P, f_P⟩ + ⟨e_A, f_A⟩` on every admitted point
   (`PortHolon.power_balance`), and passivity as a proved inequality when `R ⪰ 0`
   (`PortHolon.passive`, ordered field).
2. **Continuous balance with deposition** over `ℝ`: for time-varying symmetric `Q(τ)`,
   `dE/dτ = −⟨f_R, R f_R⟩ + ⟨e_P,f_P⟩ + ⟨e_A,f_A⟩ + ½⟨x, Q̇ x⟩` as a `HasDerivAt` along a motion
   (`PortHolon.energy_balance`; fixed constitution: `energy_balance_const`).
2b. **Nonlinear storage**: for a storage function with Fréchet derivative `⟨e, ·⟩`, the same
   balance holds along a motion admitting the effort `e` (`PortHolon.energy_balance_fderiv`);
   witness the quartic storage with effort `x³` (`quartic_storage_effort`).
3. **Discrete balances** over any field of characteristic zero: the implicit midpoint step of
   `q̇ = (J − R) Q q + B u` satisfies `E⁺ − E = −h⟨ē, Rē⟩ + h⟨ē, Bu⟩` exactly (`midpoint_balance`);
   backward Euler carries the explicit defect `−½⟨Δq, QΔq⟩` (`backwardEuler_balance`), nonzero on
   a witness (`backwardEuler_defect_witness`).
4. **Ball containment**: an exact value in `B(c, r)` maps under an operator of norm `≤ K` into
   `B(Lc, Kr)` (`ball_image`, `Transport/AffineJointBall.affine_forward_deviation`).
-/

noncomputable section

namespace Holonics.HolonCore

open Matrix

/-! ## 1. The four port kinds and the port Holon -/

section Kinds

variable {𝕜 : Type*} [Field 𝕜]
variable {σ ρ π α : Type*} [Fintype σ] [Fintype ρ] [Fintype π] [Fintype α]

/-- [definition] The port index of a port Holon: storage `σ`, resistive `ρ`, external `π`,
active `α`. -/
abbrev Ports (σ ρ π α : Type*) := σ ⊕ (ρ ⊕ (π ⊕ α))

/-- [definition] Assemble one bond from its four kinds. -/
def assemble (fS eS : σ → 𝕜) (fR eR : ρ → 𝕜) (fP eP : π → 𝕜) (fA eA : α → 𝕜) :
    Bond 𝕜 (Ports σ ρ π α) :=
  (Sum.elim fS (Sum.elim fR (Sum.elim fP fA)), Sum.elim eS (Sum.elim eR (Sum.elim eP eA)))

/-- [proved-derived; formal-checked] The power of an assembled bond is the sum of its kinds. -/
theorem power_assemble (fS eS : σ → 𝕜) (fR eR : ρ → 𝕜) (fP eP : π → 𝕜) (fA eA : α → 𝕜) :
    power (assemble fS eS fR eR fP eP fA eA) = eS ⬝ᵥ fS + eR ⬝ᵥ fR + eP ⬝ᵥ fP + eA ⬝ᵥ fA := by
  simp only [power, assemble, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  ring

/-- [definition] **A port Holon**: a Dirac structure on its ports and its linear element
relations — storage `Q` (energy `½⟨x, Qx⟩`, effort `Qx`, flow `−ẋ`) and resistance `R`
(`e_R = −R f_R`). External and active ports are left free; their powers are what the balance
returns. -/
structure PortHolon (𝕜 σ ρ π α : Type*) [Field 𝕜] [Fintype σ] [Fintype ρ] [Fintype π]
    [Fintype α] where
  /-- The interconnection. -/
  D : Submodule 𝕜 (Bond 𝕜 (Ports σ ρ π α))
  /-- It is Dirac. -/
  dirac : IsDirac (bondForm 𝕜 (Ports σ ρ π α)) D
  /-- The storage form. -/
  Q : Matrix σ σ 𝕜
  /-- The storage form is symmetric. -/
  Q_symm : Qᵀ = Q
  /-- The resistive relation `e_R = −R f_R`. -/
  R : Matrix ρ ρ 𝕜

/-- [definition] The storage energy `½⟨x, Qx⟩`. -/
def storageEnergy (Q : Matrix σ σ 𝕜) (x : σ → 𝕜) : 𝕜 := (1 / 2 : 𝕜) * (x ⬝ᵥ (Q *ᵥ x))

/-- [definition] A point of motion: state `x`, velocity `v`, resistive flow `fR`, external and
active bonds; its assembled bond `(−v, Qx; fR, −R fR; fP, eP; fA, eA)` lies in `D`. -/
def PortHolon.Admits (H : PortHolon 𝕜 σ ρ π α) (Q : Matrix σ σ 𝕜) (x v : σ → 𝕜) (fR : ρ → 𝕜)
    (fP eP : π → 𝕜) (fA eA : α → 𝕜) : Prop :=
  assemble (-v) (Q *ᵥ x) fR (-(H.R *ᵥ fR)) fP eP fA eA ∈ H.D

/-- [proved-derived; formal-checked] **The pointwise power balance.** On an admitted point the
storage rate `⟨Qx, v⟩` equals `−⟨f_R, R f_R⟩ + ⟨e_P, f_P⟩ + ⟨e_A, f_A⟩`: dissipation, port power,
active power. This is power neutrality of `D` and nothing else. -/
theorem PortHolon.power_balance [CharZero 𝕜] (H : PortHolon 𝕜 σ ρ π α) {Q : Matrix σ σ 𝕜}
    {x v : σ → 𝕜} {fR : ρ → 𝕜} {fP eP : π → 𝕜} {fA eA : α → 𝕜}
    (h : H.Admits Q x v fR fP eP fA eA) :
    (Q *ᵥ x) ⬝ᵥ v = -(fR ⬝ᵥ (H.R *ᵥ fR)) + eP ⬝ᵥ fP + eA ⬝ᵥ fA := by
  have h0 := H.dirac.power_eq_zero h
  rw [power_assemble] at h0
  simp only [dotProduct_neg, neg_dotProduct] at h0
  rw [dotProduct_comm fR]
  linear_combination -h0

/-- [proved-derived; formal-checked] **Passivity is proved, not assumed.** With `R` positive
semidefinite in the sense `⟨f, R f⟩ ≥ 0`, the storage rate never exceeds the port plus active
power. -/
theorem PortHolon.passive [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] (H : PortHolon 𝕜 σ ρ π α)
    (hR : ∀ f, 0 ≤ f ⬝ᵥ (H.R *ᵥ f)) {Q : Matrix σ σ 𝕜} {x v : σ → 𝕜} {fR : ρ → 𝕜}
    {fP eP : π → 𝕜} {fA eA : α → 𝕜} (h : H.Admits Q x v fR fP eP fA eA) :
    (Q *ᵥ x) ⬝ᵥ v ≤ eP ⬝ᵥ fP + eA ⬝ᵥ fA := by
  rw [H.power_balance h]; linarith [hR fR]

end Kinds

/-! ## 2. The continuous energy balance, with deposition -/

section Continuous

variable {σ ρ π α : Type*} [Fintype σ] [Fintype ρ] [Fintype π] [Fintype α]

/-- [proved-derived; formal-checked] **The rate of a time-varying quadratic storage.** For
`E(t) = ½⟨x(t), Q(t) x(t)⟩` with `Q(t)` symmetric, `dE/dt = ⟨Q x, ẋ⟩ + ½⟨x, Q̇ x⟩`. -/
theorem hasDerivAt_storageEnergy {x : ℝ → σ → ℝ} {v : σ → ℝ} {Q : ℝ → Matrix σ σ ℝ}
    {Qd : Matrix σ σ ℝ} {t : ℝ} (hx : ∀ i, HasDerivAt (fun s => x s i) (v i) t)
    (hQ : ∀ i j, HasDerivAt (fun s => Q s i j) (Qd i j) t) (hsymm : (Q t)ᵀ = Q t) :
    HasDerivAt (fun s => storageEnergy (Q s) (x s))
      ((Q t *ᵥ x t) ⬝ᵥ v + (1 / 2) * (x t ⬝ᵥ (Qd *ᵥ x t))) t := by
  have hterm : ∀ i j, HasDerivAt (fun s => x s i * (Q s i j * x s j))
      (v i * (Q t i j * x t j) + x t i * (Qd i j * x t j + Q t i j * v j)) t :=
    fun i j => (hx i).mul ((hQ i j).mul (hx j))
  have hsum : HasDerivAt (fun s => ∑ i, ∑ j, x s i * (Q s i j * x s j))
      (∑ i, ∑ j, (v i * (Q t i j * x t j) + x t i * (Qd i j * x t j + Q t i j * v j))) t :=
    HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => hterm i j
  have hfun : (fun s => storageEnergy (Q s) (x s)) =
      fun s => (1 / 2 : ℝ) * ∑ i, ∑ j, x s i * (Q s i j * x s j) := by
    funext s
    simp [storageEnergy, dotProduct, mulVec, Finset.mul_sum]
  rw [hfun]
  refine (hsum.const_mul _).congr_deriv ?_
  have hQs : ∀ i j, Q t i j = Q t j i := fun i j => by
    have := congrFun (congrFun hsymm j) i
    rwa [Matrix.transpose_apply] at this
  have hswap : ∑ i, ∑ j, x t i * (Q t i j * v j) = ∑ i, ∑ j, v i * (Q t i j * x t j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hQs]; ring
  have hA : ∑ i, ∑ j, v i * (Q t i j * x t j) = (Q t *ᵥ x t) ⬝ᵥ v := by
    simp only [dotProduct, mulVec, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hB : ∑ i, ∑ j, x t i * (Qd i j * x t j) = x t ⬝ᵥ (Qd *ᵥ x t) := by
    simp only [dotProduct, mulVec]
    simp only [Finset.mul_sum]
  have hsplit : ∑ i, ∑ j, (v i * (Q t i j * x t j) + x t i * (Qd i j * x t j + Q t i j * v j)) =
      ∑ i, ∑ j, v i * (Q t i j * x t j) + ∑ i, ∑ j, x t i * (Qd i j * x t j) +
        ∑ i, ∑ j, x t i * (Q t i j * v j) := by
    simp only [mul_add, Finset.sum_add_distrib]; ring
  rw [hsplit, hswap, hA, hB]
  ring

/-- [proved-derived; formal-checked] **The energy balance along a motion, with deposition.**
`dE/dτ = −⟨f_R, R f_R⟩ + ⟨e_P, f_P⟩ + ⟨e_A, f_A⟩ + ½⟨x, Q̇ x⟩`: dissipation, port power, active
power and the deposition work of a changing constitution. -/
theorem PortHolon.energy_balance (H : PortHolon ℝ σ ρ π α) {x : ℝ → σ → ℝ} {v : σ → ℝ}
    {Q : ℝ → Matrix σ σ ℝ} {Qd : Matrix σ σ ℝ} {t : ℝ}
    (hx : ∀ i, HasDerivAt (fun s => x s i) (v i) t)
    (hQ : ∀ i j, HasDerivAt (fun s => Q s i j) (Qd i j) t) (hsymm : (Q t)ᵀ = Q t)
    {fR : ρ → ℝ} {fP eP : π → ℝ} {fA eA : α → ℝ}
    (hadm : H.Admits (Q t) (x t) v fR fP eP fA eA) :
    HasDerivAt (fun s => storageEnergy (Q s) (x s))
      (-(fR ⬝ᵥ (H.R *ᵥ fR)) + eP ⬝ᵥ fP + eA ⬝ᵥ fA + (1 / 2) * (x t ⬝ᵥ (Qd *ᵥ x t))) t := by
  have h := hasDerivAt_storageEnergy hx hQ hsymm
  rwa [H.power_balance hadm] at h

/-- [proved-derived; formal-checked] With the declared constitution held fixed, the deposition
term vanishes. -/
theorem PortHolon.energy_balance_const (H : PortHolon ℝ σ ρ π α) {x : ℝ → σ → ℝ} {v : σ → ℝ}
    {t : ℝ} (hx : ∀ i, HasDerivAt (fun s => x s i) (v i) t)
    {fR : ρ → ℝ} {fP eP : π → ℝ} {fA eA : α → ℝ}
    (hadm : H.Admits H.Q (x t) v fR fP eP fA eA) :
    HasDerivAt (fun s => storageEnergy H.Q (x s))
      (-(fR ⬝ᵥ (H.R *ᵥ fR)) + eP ⬝ᵥ fP + eA ⬝ᵥ fA) t := by
  have h := H.energy_balance (Q := fun _ => H.Q) (Qd := 0) hx
    (fun i j => hasDerivAt_const t (H.Q i j)) H.Q_symm hadm
  simpa using h

/-- [definition] A point of motion with a general storage effort `e` (the gradient of a nonlinear
storage) in place of `Qx`. -/
def PortHolon.AdmitsEffort (H : PortHolon ℝ σ ρ π α) (e v : σ → ℝ) (fR : ρ → ℝ)
    (fP eP : π → ℝ) (fA eA : α → ℝ) : Prop :=
  assemble (-v) e fR (-(H.R *ᵥ fR)) fP eP fA eA ∈ H.D

/-- [proved-derived; formal-checked] **The energy balance for nonlinear storage.** For a storage
function `𝓗` with Fréchet derivative `d𝓗 = ⟨e, ·⟩` at the state, along an admitted motion
`d𝓗(x)/dτ = −⟨f_R, R f_R⟩ + ⟨e_P, f_P⟩ + ⟨e_A, f_A⟩`. -/
theorem PortHolon.energy_balance_fderiv (H : PortHolon ℝ σ ρ π α) {𝓗 : (σ → ℝ) → ℝ}
    {d𝓗 : (σ → ℝ) →L[ℝ] ℝ} {x : ℝ → σ → ℝ} {v e : σ → ℝ} {t : ℝ}
    (hH : HasFDerivAt 𝓗 d𝓗 (x t)) (heff : ∀ w, d𝓗 w = e ⬝ᵥ w) (hx : HasDerivAt x v t)
    {fR : ρ → ℝ} {fP eP : π → ℝ} {fA eA : α → ℝ} (hadm : H.AdmitsEffort e v fR fP eP fA eA) :
    HasDerivAt (fun s => 𝓗 (x s)) (-(fR ⬝ᵥ (H.R *ᵥ fR)) + eP ⬝ᵥ fP + eA ⬝ᵥ fA) t := by
  have hc := hH.comp_hasDerivAt t hx
  refine hc.congr_deriv ?_
  rw [heff]
  have h0 := H.dirac.power_eq_zero hadm
  rw [power_assemble] at h0
  simp only [dotProduct_neg, neg_dotProduct] at h0
  rw [dotProduct_comm fR]
  linear_combination -h0

/-- [proved-derived; formal-checked] Witness: the quartic storage `𝓗(x) = x⁴/4` on one coordinate
has effort `x³`: its derivative at `x` is `⟨x³, ·⟩`. -/
theorem quartic_storage_effort (x : Fin 1 → ℝ) :
    HasFDerivAt (fun y : Fin 1 → ℝ => y 0 ^ 4 / 4)
      ((x 0 ^ 3) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) x ∧
      ∀ w : Fin 1 → ℝ, ((x 0 ^ 3) • ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 1 => ℝ) 0) w = ![x 0 ^ 3] ⬝ᵥ w := by
  refine ⟨?_, fun w => by simp [dotProduct]⟩
  have hp := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt (x := x)
  have h4 := ((hasDerivAt_pow 4 (x 0)).div_const 4).comp_hasFDerivAt x hp
  refine h4.congr_fderiv ?_
  ext w
  simp

end Continuous

/-! ## 3. Discrete energy balances -/

section Discrete

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {σ μ : Type*} [Fintype σ] [Fintype μ]

omit [CharZero 𝕜] in
theorem symm_dot {Q : Matrix σ σ 𝕜} (hQ : Qᵀ = Q) (x y : σ → 𝕜) :
    x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ (Q *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hQ, dotProduct_comm]

/-- [proved-derived; formal-checked] **The implicit midpoint balance is exact.** For
`q⁺ − q = h((J − R) Q q̄ + B u)` with `q̄ = ½(q + q⁺)`, `Q` symmetric and `J` skew, the storage
changes by exactly `E⁺ − E = −h⟨ē, R ē⟩ + h⟨ē, B u⟩` with `ē = Q q̄`: the discrete step has zero
balance residual. -/
theorem midpoint_balance {Q J R : Matrix σ σ 𝕜} (hQ : Qᵀ = Q) (hJ : Jᵀ = -J) (B : Matrix σ μ 𝕜)
    (h : 𝕜) (q q' : σ → 𝕜) (u : μ → 𝕜)
    (hstep : q' - q = h • ((J - R) *ᵥ (Q *ᵥ ((1 / 2 : 𝕜) • (q + q'))) + B *ᵥ u)) :
    storageEnergy Q q' - storageEnergy Q q =
      -(h * ((Q *ᵥ ((1 / 2 : 𝕜) • (q + q'))) ⬝ᵥ (R *ᵥ (Q *ᵥ ((1 / 2 : 𝕜) • (q + q')))))) +
        h * ((Q *ᵥ ((1 / 2 : 𝕜) • (q + q'))) ⬝ᵥ (B *ᵥ u)) := by
  set e := Q *ᵥ ((1 / 2 : 𝕜) • (q + q'))
  have hdiff : storageEnergy Q q' - storageEnergy Q q = (q' - q) ⬝ᵥ e := by
    simp only [storageEnergy, e, mulVec_smul, mulVec_add, dotProduct_smul, dotProduct_add,
      sub_dotProduct, smul_eq_mul]
    rw [symm_dot hQ q' q]
    ring
  have hskew : e ⬝ᵥ (J *ᵥ e) = 0 := by
    have := skew_dot hJ e e
    have h2 : (2 : 𝕜) * (e ⬝ᵥ (J *ᵥ e)) = 0 := by linear_combination this
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  rw [hdiff, hstep, smul_dotProduct, add_dotProduct, sub_mulVec, sub_dotProduct, smul_eq_mul,
    dotProduct_comm (J *ᵥ e), hskew, dotProduct_comm (R *ᵥ e), dotProduct_comm (B *ᵥ u)]
  ring

/-- [proved-derived; formal-checked] **Backward Euler carries an explicit defect.** For
`q⁺ − q = h((J − R) Q q⁺ + B u)`, `E⁺ − E = −h⟨e⁺, R e⁺⟩ + h⟨e⁺, B u⟩ − ½⟨Δq, Q Δq⟩` with
`e⁺ = Q q⁺`, `Δq = q⁺ − q`: the last term is the scheme's numerical dissipation. -/
theorem backwardEuler_balance {Q J R : Matrix σ σ 𝕜} (hQ : Qᵀ = Q) (hJ : Jᵀ = -J)
    (B : Matrix σ μ 𝕜) (h : 𝕜) (q q' : σ → 𝕜) (u : μ → 𝕜)
    (hstep : q' - q = h • ((J - R) *ᵥ (Q *ᵥ q') + B *ᵥ u)) :
    storageEnergy Q q' - storageEnergy Q q =
      -(h * ((Q *ᵥ q') ⬝ᵥ (R *ᵥ (Q *ᵥ q')))) + h * ((Q *ᵥ q') ⬝ᵥ (B *ᵥ u)) -
        (1 / 2) * ((q' - q) ⬝ᵥ (Q *ᵥ (q' - q))) := by
  set e := Q *ᵥ q'
  have hdiff : storageEnergy Q q' - storageEnergy Q q =
      (q' - q) ⬝ᵥ e - (1 / 2) * ((q' - q) ⬝ᵥ (Q *ᵥ (q' - q))) := by
    simp only [storageEnergy, e, mulVec_sub, dotProduct_sub, sub_dotProduct]
    rw [symm_dot hQ q' q]
    ring
  have hskew : e ⬝ᵥ (J *ᵥ e) = 0 := by
    have := skew_dot hJ e e
    have h2 : (2 : 𝕜) * (e ⬝ᵥ (J *ᵥ e)) = 0 := by linear_combination this
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  rw [hdiff, hstep, smul_dotProduct, add_dotProduct, sub_mulVec, sub_dotProduct, smul_eq_mul,
    dotProduct_comm (J *ᵥ e), hskew, dotProduct_comm (R *ᵥ e), dotProduct_comm (B *ᵥ u)]
  ring

/-- [proved-derived; formal-checked] **Witness: the backward-Euler defect is not zero.** One
storage coordinate, `Q = B = h = u = 1`, `J = R = 0`, `q = 0`: the step gives `q⁺ = 1`; the
balance reads `E⁺ − E = 0 + 1 − 1/2`, so the scheme dissipates `1/2` that no element does. -/
theorem backwardEuler_defect_witness :
    storageEnergy (1 : Matrix (Fin 1) (Fin 1) ℚ) ![1] - storageEnergy 1 ![0] =
      -((1 : ℚ) * (((1 : Matrix (Fin 1) (Fin 1) ℚ) *ᵥ ![1]) ⬝ᵥ
        ((0 : Matrix (Fin 1) (Fin 1) ℚ) *ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℚ) *ᵥ ![1])))) +
        1 * (((1 : Matrix (Fin 1) (Fin 1) ℚ) *ᵥ ![1]) ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℚ) *ᵥ ![1])) -
        (1 / 2) * ((![1] - ![0]) ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℚ) *ᵥ (![1] - ![0]))) ∧
    (1 / 2 : ℚ) * ((![1] - ![0]) ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℚ) *ᵥ (![1] - ![0]))) ≠ 0 := by
  constructor
  · apply backwardEuler_balance (J := 0) (Matrix.transpose_one) (by simp) 1 1 ![0] ![1] ![1]
    ext i; fin_cases i; simp
  · simp [dotProduct]

end Discrete

/-! ## 4. Enclosure balls under a bounded linear step -/

section Ball

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- [proved-derived; formal-checked] **Ball containment.** If the exact value lies in `B(c, r)`
and `L` has operator bound `K`, the image lies in `B(L c, K r)`
(`Transport/AffineJointBall.affine_forward_deviation` with no model perturbation). -/
theorem ball_image (L : E →L[ℝ] F) {K r : ℝ} (hL : ‖L‖ ≤ K) {x c : E} (hx : ‖x - c‖ ≤ r) :
    ‖L x - L c‖ ≤ K * r := by
  have h := Holonics.Transport.AffineJointBall.affine_forward_deviation L 0 c (x - c) 0 0
    (K := K) (rM := 0) (rX := r) hL (by simp) (by simp) hx
  simpa using h

end Ball

end Holonics.HolonCore
