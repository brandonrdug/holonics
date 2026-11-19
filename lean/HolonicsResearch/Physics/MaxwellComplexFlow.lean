import Mathlib

/-!
# Maxwell's equations on a complex as a flow: Gauss's law kept along every motion, read the same in every edge chart

`Holon/Conformance` states Maxwell as the Stokes–Dirac port Holon on a cochain complex: the lossless rate preserves the
discrete Gauss law when `d₁ d₀ = 0` (`maxwell_gauss`) and the balance is Joule loss plus source power
(`maxwell_balance`), both as identities of rates at one state (atlas `maxwell.stokes-dirac`). #410's box asks for the
equations in `HasDerivAt` form, along motions, and for Gauss's law with a coboundary independent of the incidence it
is read from. The box is read here in two ways, both proved (`agent-inferred`: no record states the box's source).
First, the vertex coboundary `d₀` is any matrix with `d₁ d₀ = 0`, never built from `d₁`, and Gauss's law is kept for
every such `d₀` (item 2). Second, the charge `d₀ᵀ D` it reads is the same in every chart of the edges (any invertible
change of edge basis, orientation reversals and relabellings among them), so Gauss's law does not depend on the
incidence matrix one happens to write (item 5).

[proved-derived; formal-checked] What is proved, over ℝ, for vertices `ν`, edges `ε`, faces `κ` and volumes `τ`, with
incidences `d₀ : ν → ε`, `d₁ : ε → κ`, `d₂ : κ → τ` (`d₁ d₀ = 0`, `d₂ d₁ = 0`), constitutions `P_e = ε⁻¹` on edges and
`P_m = μ⁻¹` on faces, a current `J` on edges and a charge `ρ` on vertices.

1. **The equations as a flow** (`MaxwellFlow`): the displacement on edges and the induction on faces move by
   Ampère–Maxwell and Faraday, `Ḋ = d₁ᵀ H − J` and `Ḃ = −d₁ E`, `E = P_e D`, `H = P_m B`, each as `HasDerivAt` at every
   time.
2. **Gauss's law is kept** (`gauss_rate`, `gauss_preserved`): the charge read `d₀ᵀ D` moves by `−d₀ᵀ J`, since
   `d₀ᵀ d₁ᵀ = (d₁ d₀)ᵀ = 0`; so when the charge obeys continuity, `ρ̇ = −d₀ᵀ J`, Gauss's law `d₀ᵀ D = ρ` holding at one
   time holds at every time. With no current the charge read is constant (`charge_constant`).
3. **The magnetic Gauss law is kept** (`magnetic_gauss_preserved`): `d₂ B` is constant, since `d₂ d₁ = 0`; a field
   with no magnetic charge at one time has none at any time.
4. **Poynting on a closed complex** (`energy_rate`): with symmetric constitutions the stored energy
   `U = ½(⟨D, P_e D⟩ + ⟨B, P_m B⟩)` moves by `−⟨E, J⟩`, the work the field does on the current; the exchange
   `⟨d₁E, H⟩ − ⟨H, d₁E⟩` between the two stores cancels.
5. **The coboundary does not depend on the edge chart** (`rechart_complex`, `charge_rechart`, `pairing_rechart`,
   `MaxwellFlow.rechart`): for a change of edge chart `P` with left inverse `Q`, the incidences `P d₀` and
   `d₁ Q` still form a complex, a chain `D` reads `Qᵀ D` and a cochain `E` reads `P E`; the charge `d₀ᵀ D` and the
   pairing `⟨E, D⟩` are the same in both charts, and a Maxwell flow in one chart is a Maxwell flow in the other with
   `P_e' = P P_e Pᵀ` and `J' = Qᵀ J`. An orientation reversal of some edges is the case `P = Q` a diagonal of signs
   (`flip_charge`).

The computational object is the helical pair interaction's medium: the edge and face stores of a complex exchanging
through its incidences, a port Holon whose interconnection is the skew Stokes–Dirac structure. Of the winding guide's
six general objects this touches the cell holonomy (the face circulations `d₁ E`) and the tube (the motion in time);
the helix, the pair, faces and placement and the tower thread stay attached.

What stands beside it: `Holon/Conformance.{maxwell_gauss, maxwell_balance}` (the rates at one state, with Ohmic
loss), the midpoint sections of `em.poynting-midpoint`, and the propagation `ym.maxwell-propagation`. A complex with a
boundary adds the boundary's Poynting flux, which is not stated here; nor is the continuum limit.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Physics.MaxwellComplexFlow

open Matrix

variable {ν ε κ τ : Type*} [Fintype ν] [Fintype ε] [Fintype κ] [Fintype τ]

/-! ## 0. Derivatives of matrix reads along a motion -/

section Calculus

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

omit [Fintype ι'] in
theorem hasDerivAt_mulVec (A : Matrix ι' ι ℝ) {u : ℝ → ι → ℝ} {u' : ι → ℝ} {t : ℝ} (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => A *ᵥ u s) (A *ᵥ u') t := by
  refine hasDerivAt_pi.2 fun i => ?_
  have h : HasDerivAt (fun s => ∑ j, A i j * u s j) (∑ j, A i j * u' j) t :=
    HasDerivAt.fun_sum fun j _ => (hasDerivAt_pi.1 hu j).const_mul (A i j)
  simpa [Matrix.mulVec, dotProduct] using h

theorem hasDerivAt_dotProduct {u v : ℝ → ι → ℝ} {u' v' : ι → ℝ} {t : ℝ} (hu : HasDerivAt u u' t)
    (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => u s ⬝ᵥ v s) (u' ⬝ᵥ v t + u t ⬝ᵥ v') t := by
  have h : HasDerivAt (fun s => ∑ i, u s i * v s i) (∑ i, (u' i * v t i + u t i * v' i)) t :=
    HasDerivAt.fun_sum fun i _ => (hasDerivAt_pi.1 hu i).mul (hasDerivAt_pi.1 hv i)
  simpa [dotProduct, Finset.sum_add_distrib] using h

end Calculus

/-! ## 1. The flow -/

/-- [definition] **Maxwell's equations on a complex as a flow**: Ampère–Maxwell on edges and Faraday on faces, each a
derivative at every time. -/
structure MaxwellFlow (d₁ : Matrix κ ε ℝ) (Pe : Matrix ε ε ℝ) (Pm : Matrix κ κ ℝ) (J : ℝ → ε → ℝ)
    (D : ℝ → ε → ℝ) (B : ℝ → κ → ℝ) : Prop where
  ampere : ∀ t, HasDerivAt D (d₁ᵀ *ᵥ (Pm *ᵥ B t) - J t) t
  faraday : ∀ t, HasDerivAt B (-(d₁ *ᵥ (Pe *ᵥ D t))) t

variable {d₀ : Matrix ε ν ℝ} {d₁ : Matrix κ ε ℝ} {d₂ : Matrix τ κ ℝ} {Pe : Matrix ε ε ℝ} {Pm : Matrix κ κ ℝ}
  {J : ℝ → ε → ℝ} {D : ℝ → ε → ℝ} {B : ℝ → κ → ℝ}

/-! ## 2. Gauss's law -/

omit [Fintype ν] in
/-- The charge read moves by the current's divergence alone. -/
theorem gauss_rate (hdd : d₁ * d₀ = 0) (F : MaxwellFlow d₁ Pe Pm J D B) (t : ℝ) :
    HasDerivAt (fun s => d₀ᵀ *ᵥ D s) (-(d₀ᵀ *ᵥ J t)) t := by
  have h := hasDerivAt_mulVec d₀ᵀ (F.ampere t)
  convert h using 1
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hdd, Matrix.transpose_zero,
    Matrix.zero_mulVec, zero_sub]

/-- **Gauss's law is kept**: with continuity, `d₀ᵀ D = ρ` at one time gives it at every time. -/
theorem gauss_preserved (hdd : d₁ * d₀ = 0) (F : MaxwellFlow d₁ Pe Pm J D B) {ρ : ℝ → ν → ℝ}
    (hρ : ∀ t, HasDerivAt ρ (-(d₀ᵀ *ᵥ J t)) t) {t₀ : ℝ} (h₀ : d₀ᵀ *ᵥ D t₀ = ρ t₀) (t : ℝ) :
    d₀ᵀ *ᵥ D t = ρ t := by
  have hd : ∀ s, HasDerivAt (fun s => d₀ᵀ *ᵥ D s - ρ s) 0 s := fun s => by
    have h := (gauss_rate hdd F s).sub (hρ s)
    rw [sub_self] at h
    exact h
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t t₀
  have : d₀ᵀ *ᵥ D t - ρ t = 0 := by
    rw [hconst, h₀, sub_self]
  exact sub_eq_zero.mp this

/-- With no current, the charge read is constant. -/
theorem charge_constant (hdd : d₁ * d₀ = 0) (F : MaxwellFlow d₁ Pe Pm (fun _ => 0) D B) (t t₀ : ℝ) :
    d₀ᵀ *ᵥ D t = d₀ᵀ *ᵥ D t₀ :=
  gauss_preserved hdd F (ρ := fun _ => d₀ᵀ *ᵥ D t₀) (fun s => by simpa using hasDerivAt_const s _) rfl t

/-- **The magnetic Gauss law is kept**: `d₂ B` is constant along the flow. -/
theorem magnetic_gauss_preserved (hdd : d₂ * d₁ = 0) (F : MaxwellFlow d₁ Pe Pm J D B) (t t₀ : ℝ) :
    d₂ *ᵥ B t = d₂ *ᵥ B t₀ := by
  have hd : ∀ s, HasDerivAt (fun s => d₂ *ᵥ B s) 0 s := fun s => by
    have h := hasDerivAt_mulVec d₂ (F.faraday s)
    convert h using 1
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, hdd, Matrix.zero_mulVec, neg_zero]
  exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t t₀

/-! ## 3. Poynting on a closed complex -/

/-- [definition] The stored energy `½(⟨D, P_e D⟩ + ⟨B, P_m B⟩)`. -/
noncomputable def energy (Pe : Matrix ε ε ℝ) (Pm : Matrix κ κ ℝ) (D : ε → ℝ) (B : κ → ℝ) : ℝ :=
  (D ⬝ᵥ (Pe *ᵥ D) + B ⬝ᵥ (Pm *ᵥ B)) / 2

/-- **Poynting on a closed complex**: the stored energy moves by `−⟨E, J⟩`. -/
theorem energy_rate (hPe : Peᵀ = Pe) (hPm : Pmᵀ = Pm) (F : MaxwellFlow d₁ Pe Pm J D B) (t : ℝ) :
    HasDerivAt (fun s => energy Pe Pm (D s) (B s)) (-((Pe *ᵥ D t) ⬝ᵥ J t)) t := by
  have hD := F.ampere t
  have hB := F.faraday t
  have h1 := hasDerivAt_dotProduct hD (hasDerivAt_mulVec Pe hD)
  have h2 := hasDerivAt_dotProduct hB (hasDerivAt_mulVec Pm hB)
  have h := (h1.add h2).div_const 2
  refine h.congr_deriv ?_
  have symD : ∀ w : ε → ℝ, w ⬝ᵥ (Pe *ᵥ D t) = D t ⬝ᵥ (Pe *ᵥ w) := fun w => by
    rw [dotProduct_mulVec, ← mulVec_transpose, hPe, dotProduct_comm]
  have symB : ∀ w : κ → ℝ, w ⬝ᵥ (Pm *ᵥ B t) = B t ⬝ᵥ (Pm *ᵥ w) := fun w => by
    rw [dotProduct_mulVec, ← mulVec_transpose, hPm, dotProduct_comm]
  rw [← symD, ← symB]
  have hx : (d₁ᵀ *ᵥ (Pm *ᵥ B t)) ⬝ᵥ (Pe *ᵥ D t) = (d₁ *ᵥ (Pe *ᵥ D t)) ⬝ᵥ (Pm *ᵥ B t) := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, transpose_transpose, dotProduct_comm]
  simp only [sub_dotProduct, neg_dotProduct]
  rw [dotProduct_comm (J t) (Pe *ᵥ D t)]
  rw [hx]
  ring

/-! ## 4. The coboundary in every edge chart -/

omit [Fintype ν] [Fintype κ] in
/-- A change of edge chart keeps the complex. -/
theorem rechart_complex [DecidableEq ε] (hdd : d₁ * d₀ = 0) {P Q : Matrix ε ε ℝ} (hQP : Q * P = 1) :
    (d₁ * Q) * (P * d₀) = 0 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQP, Matrix.one_mul, hdd]

omit [Fintype ν] in
/-- **The charge read is the same in every edge chart**: `(P d₀)ᵀ (Qᵀ D) = d₀ᵀ D`. -/
theorem charge_rechart [DecidableEq ε] {P Q : Matrix ε ε ℝ} (hQP : Q * P = 1) (D : ε → ℝ) :
    (P * d₀)ᵀ *ᵥ (Qᵀ *ᵥ D) = d₀ᵀ *ᵥ D := by
  rw [Matrix.mulVec_mulVec, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, hQP,
    Matrix.transpose_one, Matrix.mul_one]

/-- The pairing of a cochain and a chain is the same in every edge chart. -/
theorem pairing_rechart [DecidableEq ε] {P Q : Matrix ε ε ℝ} (hQP : Q * P = 1) (E D : ε → ℝ) :
    (P *ᵥ E) ⬝ᵥ (Qᵀ *ᵥ D) = E ⬝ᵥ D := by
  rw [dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]

omit [Fintype ν] in
/-- An orientation reversal of some edges, a diagonal of signs, reads the same charge. -/
theorem flip_charge [DecidableEq ε] (σ : ε → ℝ) (hσ : ∀ e, σ e * σ e = 1) (D : ε → ℝ) :
    (Matrix.diagonal σ * d₀)ᵀ *ᵥ ((Matrix.diagonal σ)ᵀ *ᵥ D) = d₀ᵀ *ᵥ D := by
  refine charge_rechart ?_ D
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst h; simp [hσ]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

omit [Fintype ν] in
/-- **A Maxwell flow in one edge chart is a Maxwell flow in another**, with `D' = Qᵀ D`, `J' = Qᵀ J`,
`P_e' = P P_e Pᵀ` and incidence `d₁ Q`. -/
theorem MaxwellFlow.rechart [DecidableEq ε] (F : MaxwellFlow d₁ Pe Pm J D B) {P Q : Matrix ε ε ℝ}
    (hQP : Q * P = 1) :
    MaxwellFlow (d₁ * Q) (P * Pe * Pᵀ) Pm (fun t => Qᵀ *ᵥ J t) (fun t => Qᵀ *ᵥ D t) B where
  ampere t := by
    have h := hasDerivAt_mulVec Qᵀ (F.ampere t)
    convert h using 1
    simp only [Matrix.mulVec_sub, Matrix.transpose_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  faraday t := by
    convert F.faraday t using 2
    have hPQt : Pᵀ * Qᵀ = 1 := by rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [Matrix.mul_assoc d₁ Q, ← Matrix.mul_assoc Q, ← Matrix.mul_assoc Q, hQP, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_assoc, hPQt, Matrix.mul_one]

end Holonics.Physics.MaxwellComplexFlow
