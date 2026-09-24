import ElementaryHolonics.Geometry.ScrewGeometry
import ElementaryHolonics.Transport.HolonicInteraction
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

/-!
# The helical pair is a Holonic Interaction contact

[definition] `Geometry/ScrewGeometry` owns the two-generator pair quadrance jet.
`Transport/HolonicInteraction` owns the contact face `w • (Jᵀ D J)`, its dissipated power and its
zero-slip kernel. This module joins them: the pair's relative velocity **is** a slip map on the
two pair parameters `(s,t)`. The first variation of pair quadrance is that slip map's pullback
of the separation; its second variation is the isotropic contact form of the same slip map plus
the geometric `Δ·a` term. The pair therefore supplies `J_f` to a contact face. A face's `D_f`,
weight and clock remain declared material.

[definition] The second half states the finite transport specialization used by the
September 21 rotor/Bombe comparison, in an arbitrary group. Fixed material `P` carried by a phase
shift `S` is `S⁻ᵈ P Sᵈ`; a forward passage `A` with reflection `F` returns through the same
operands as `A⁻¹ F A`. A boundary involution conjugates every stage of a closed menu path, so loop
closure at the boundary is a fixed-point condition on the known generator word, read at the
unknown boundary image. No alphabet, width or cipher is assumed.

[established-bounded; formal-checked] Scope: exact rational algebra at one pair configuration and
finite group/permutation identities. Finite screw exponentials, general proper-rotation
recharting, friction laws beyond a declared quadratic face and any statement about the native
incident field are outside this module. No `axiom`, no `sorry`, no `native_decide`.
-/

open scoped BigOperators Matrix
open Matrix

namespace Soma.Holonics.Transport.HelicalPairInteraction

open Soma.Holonics.Geometry.ScrewGeometry
open Soma.Holonics.Transport.HolonicInteraction

/-! ## 1. The pair slip map -/

/-- [definition] The slip map of one helical pair at a configuration. Its columns are the first
object's velocity `va` and the negated second velocity `vb`, so that a parameter rate `(ṡ,ṫ)` is
sent to the relative velocity `Δ̇ = ṡ va − ṫ vb` of `Δ = x_a(s) − x_b(t)`. -/
def pairSlip (va vb : Vec) : Matrix (Fin 3) (Fin 2) ℚ :=
  Matrix.of fun i j => ![va i, -vb i] j

/-- [proved-derived; formal-checked] The slip map reads the relative velocity of the pair. -/
theorem pairSlip_mulVec (va vb : Vec) (u : Fin 2 → ℚ) :
    pairSlip va vb *ᵥ u = u 0 • va - u 1 • vb := by
  ext i
  simp [pairSlip, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- [proved-derived; formal-checked] **The adjoint of the slip map.** Pulling a separation back
along the slip map gives its pairing with each object's own velocity, with the second object's
orientation retained. -/
theorem pairSlip_transpose_mulVec (va vb Δ : Vec) :
    (pairSlip va vb)ᵀ *ᵥ Δ = ![Δ ⬝ᵥ va, -(Δ ⬝ᵥ vb)] := by
  ext j
  fin_cases j <;>
    simp [pairSlip, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-! ## 1a. The fixed-generator feature and its complete return -/

/-- [definition] The fixed-generator pair feature keeps the separating vector, its quadrance,
and the quadrance differential as separate receiving coordinates. The generator and its
configuration are fixed while this feature is read; their variations belong to a larger chart. -/
structure PairFeature where
  delta : Vec
  quadrance : ℚ
  gradient : Fin 2 → ℚ

/-- The pair feature at one configuration. -/
def pairFeatureAt (Δ va vb : Vec) : PairFeature where
  delta := Δ
  quadrance := Δ ⬝ᵥ Δ
  gradient := 2 • ((pairSlip va vb)ᵀ *ᵥ Δ)

/-- The full second variation of the fixed-generator quadrance feature. -/
def pairQuadranceHessian (Δ va vb aa ab : Vec) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![2 * (va ⬝ᵥ va + Δ ⬝ᵥ aa), -2 * (va ⬝ᵥ vb);
      -2 * (va ⬝ᵥ vb), 2 * (vb ⬝ᵥ vb - Δ ⬝ᵥ ab)]

/-- The receiving covector returned through the complete fixed-generator feature map. -/
def pairFeatureReturn (J : Matrix (Fin 3) (Fin 2) ℚ) (DQ : Fin 2 → ℚ)
    (H : Matrix (Fin 2) (Fin 2) ℚ) (lambdaDelta : Vec) (lambdaQ : ℚ)
    (lambdaDQ : Fin 2 → ℚ) : Fin 2 → ℚ :=
  Jᵀ *ᵥ lambdaDelta + lambdaQ • DQ + Hᵀ *ᵥ lambdaDQ

/-- [proved-derived; formal-checked] The complete fixed-generator adjoint is
`Jᵀ λΔ + λQ DQ + Hᵀ λDQ`. It returns all three feature covectors, including the Hessian
term that the scalar quadrance pullback alone cannot provide. -/
theorem pairFeatureReturn_adjoint (J : Matrix (Fin 3) (Fin 2) ℚ) (DQ : Fin 2 → ℚ)
    (H : Matrix (Fin 2) (Fin 2) ℚ) (lambdaDelta : Vec) (lambdaQ : ℚ)
    (lambdaDQ : Fin 2 → ℚ)
    (u : Fin 2 → ℚ) :
    lambdaDelta ⬝ᵥ (J *ᵥ u) + lambdaQ * (DQ ⬝ᵥ u) + lambdaDQ ⬝ᵥ (H *ᵥ u)
      = pairFeatureReturn J DQ H lambdaDelta lambdaQ lambdaDQ ⬝ᵥ u := by
  have hJ : lambdaDelta ⬝ᵥ (J *ᵥ u) = (Jᵀ *ᵥ lambdaDelta) ⬝ᵥ u := by
    rw [Matrix.dotProduct_mulVec]
    rw [← Matrix.vecMul_transpose]
    simp
  have hH : lambdaDQ ⬝ᵥ (H *ᵥ u) = (Hᵀ *ᵥ lambdaDQ) ⬝ᵥ u := by
    rw [Matrix.dotProduct_mulVec]
    rw [← Matrix.vecMul_transpose]
    simp
  rw [hJ, hH]
  simp [pairFeatureReturn]

/-- [proved-derived; formal-checked] The pair's gradient is the slip adjoint of its separation.
This is the `DQ = 2 Jᵀ Δ` input to the feature chart. -/
theorem pairFeatureAt_gradient (Δ va vb : Vec) :
    (pairFeatureAt Δ va vb).gradient = 2 • ((pairSlip va vb)ᵀ *ᵥ Δ) := rfl

/-- [proved-derived; formal-checked] The full Hessian quadratic is the isotropic contact form
plus both geometric/prestress acceleration terms. -/
theorem pairQuadranceHessian_quad (Δ va vb aa ab : Vec) (s t : ℚ) :
    quad (pairQuadranceHessian Δ va vb aa ab) ![s, t]
      = 2 * (quad (faceForm 1 (pairSlip va vb) 1) ![s, t]
        + s ^ 2 * (Δ ⬝ᵥ aa) - t ^ 2 * (Δ ⬝ᵥ ab)) := by
  rw [quad_faceForm, pairSlip_mulVec]
  simp [pairQuadranceHessian, quad, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.one_apply]
  have hinner :
      (∑ x : Fin 3, (s * va x - t * vb x) * (s * va x - t * vb x)) =
        s ^ 2 * (∑ x : Fin 3, va x ^ 2)
          - 2 * s * t * (∑ x : Fin 3, va x * vb x)
          + t ^ 2 * (∑ x : Fin 3, vb x ^ 2) := by
    calc
      (∑ x : Fin 3, (s * va x - t * vb x) * (s * va x - t * vb x)) =
          ∑ x : Fin 3, (s ^ 2 * va x ^ 2 - 2 * s * t * va x * vb x
            + t ^ 2 * vb x ^ 2) := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        have hcross :
            (∑ x : Fin 3, 2 * s * t * va x * vb x) =
              2 * s * t * (∑ x : Fin 3, va x * vb x) := by
          calc
            (∑ x : Fin 3, 2 * s * t * va x * vb x) =
                ∑ x : Fin 3, (2 * s * t) * (va x * vb x) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  ring
            _ = _ := by rw [Finset.mul_sum]
        have hA : s ^ 2 * (∑ x : Fin 3, va x ^ 2) =
            ∑ x : Fin 3, s ^ 2 * va x ^ 2 := by rw [Finset.mul_sum]
        have hB : t ^ 2 * (∑ x : Fin 3, vb x ^ 2) =
            ∑ x : Fin 3, t ^ 2 * vb x ^ 2 := by rw [Finset.mul_sum]
        rw [hcross]
        rw [hA, hB]
  rw [hinner]
  ring

/-! ## 2. The pair as a contact face -/

/-- [proved-derived; formal-checked] **Pair contact power.** A contact face whose slip map is the
pair's reads its constitutive response at the pair's relative velocity. -/
theorem pair_face_power (w : ℚ) (va vb : Vec) (D : Matrix (Fin 3) (Fin 3) ℚ) (u : Fin 2 → ℚ) :
    quad (faceForm w (pairSlip va vb) D) u
      = w * ((u 0 • va - u 1 • vb) ⬝ᵥ (D *ᵥ (u 0 • va - u 1 • vb))) := by
  rw [quad_faceForm, pairSlip_mulVec]

/-! ## 2a. A pair-rate port into a resident medium -/

/-- [definition] A resident medium's rate chart `C` embeds its coordinates into the two pair
rates. The pair's spatial slip remains `J * C`; the charts are not identified. -/
def pairRatePort {n : ℕ} (C : Matrix (Fin 2) (Fin n) ℚ) (va vb : Vec) :
    Matrix (Fin 3) (Fin n) ℚ := pairSlip va vb * C

/-- [proved-derived; formal-checked] Pulling a pair face through a rate port is matrix
congruence: `face_form (J C) = Cᵀ face_form J C`. -/
theorem faceForm_pairRatePort_congruence {n : ℕ} (w : ℚ)
    (C : Matrix (Fin 2) (Fin n) ℚ) (va vb : Vec)
    (D : Matrix (Fin 3) (Fin 3) ℚ) :
    faceForm w (pairRatePort C va vb) D
      = Cᵀ * faceForm w (pairSlip va vb) D * C := by
  simp [pairRatePort, faceForm, Matrix.transpose_mul, Matrix.mul_assoc,
    Matrix.smul_mul, Matrix.mul_smul]

/-- [proved-derived; formal-checked] The port face reads the resident rate through the pair
face. This retains the pair/material null kernel while changing only the declared rate chart. -/
theorem pairRatePort_quad_eq_pair_quad {n : ℕ} (w : ℚ)
    (C : Matrix (Fin 2) (Fin n) ℚ) (va vb : Vec)
    (D : Matrix (Fin 3) (Fin 3) ℚ) (z : Fin n → ℚ) :
    quad (faceForm w (pairRatePort C va vb) D) z
      = quad (faceForm w (pairSlip va vb) D) (C *ᵥ z) := by
  rw [quad_faceForm, quad_faceForm]
  simp only [pairRatePort, Matrix.mulVec_mulVec]

/-- [proved-derived; formal-checked] For a symmetric PSD material, a port motion has zero power
exactly when the constitutive current sees its embedded pair slip. -/
theorem pairRatePort_quad_eq_zero_iff_material_null {n : ℕ} {w : ℚ} (hw : 0 < w)
    (C : Matrix (Fin 2) (Fin n) ℚ) (va vb : Vec)
    (D : Matrix (Fin 3) (Fin 3) ℚ) (hDpsd : ∀ s : Vec, 0 ≤ quad D s)
    (hDsymm : Dᵀ = D) (z : Fin n → ℚ) :
    quad (faceForm w (pairRatePort C va vb) D) z = 0 ↔
      D *ᵥ (pairRatePort C va vb *ᵥ z) = 0 := by
  rw [quad_faceForm]
  constructor
  · intro h
    apply psd_mulVec_eq_zero_of_quad_eq_zero hDpsd hDsymm
    rcases mul_eq_zero.mp h with hw0 | hquad
    · exact (hw.ne' hw0).elim
    · exact hquad
  · intro h
    rw [h]
    simp

/-- [proved-derived; formal-checked] If the material has no null direction among attainable pair
slips, the port's zero-power kernel is exactly the embedded pair zero-slip kernel. -/
theorem pairRatePort_quad_eq_zero_iff_zero_slip {n : ℕ} {w : ℚ} (hw : 0 < w)
    (C : Matrix (Fin 2) (Fin n) ℚ) (va vb : Vec)
    (D : Matrix (Fin 3) (Fin 3) ℚ) (hDpsd : ∀ s : Vec, 0 ≤ quad D s)
    (hDsymm : Dᵀ = D)
    (hDnull : ∀ z : Fin n → ℚ, D *ᵥ (pairRatePort C va vb *ᵥ z) = 0 →
      pairRatePort C va vb *ᵥ z = 0) (z : Fin n → ℚ) :
    quad (faceForm w (pairRatePort C va vb) D) z = 0 ↔
      pairRatePort C va vb *ᵥ z = 0 := by
  rw [pairRatePort_quad_eq_zero_iff_material_null hw C va vb D hDpsd hDsymm]
  constructor
  · intro h
    exact hDnull z h
  · intro h
    rw [h]
    simp

/-- [proved-derived; formal-checked] **Synchronized passage is the zero-power kernel.** On a
positive-weight face whose quadratic null cone is trivial, a pair motion reads zero power exactly
when the two objects' contact velocities agree. This theorem assumes null-definiteness, but not
nonnegativity of the form; the positive-semidefinite material version below returns the stronger
operator null statement. This is the incidence/synchronization law between `s` and `t` read from
the material, not an identification of the two parameters. -/
theorem pair_face_power_eq_zero_iff {w : ℚ} (hw : 0 < w) (va vb : Vec)
    (D : Matrix (Fin 3) (Fin 3) ℚ)
    (hdefinite : ∀ x : Vec, x ⬝ᵥ (D *ᵥ x) = 0 → x = 0) (u : Fin 2 → ℚ) :
    quad (faceForm w (pairSlip va vb) D) u = 0 ↔ u 0 • va = u 1 • vb := by
  rw [pair_face_power]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hw0 | hs
    · exact absurd hw0 hw.ne'
    · exact sub_eq_zero.mp (hdefinite _ hs)
  · intro h
    rw [h, sub_self]
    simp

/-- [proved-derived; formal-checked] **A rational pair lock is a zero-power direction.** On a
dissipative face of positive weight, advancing the first object at rate `q` and the second at
rate `p` reads zero power exactly when `q v_a = p v_b`. -/
theorem lock_iff_zero_power {w : ℚ} (hw : 0 < w) (va vb : Vec)
    (D : Matrix (Fin 3) (Fin 3) ℚ)
    (hdefinite : ∀ x : Vec, x ⬝ᵥ (D *ᵥ x) = 0 → x = 0) (p q : ℤ) :
    quad (faceForm w (pairSlip va vb) D) ![(q : ℚ), (p : ℚ)] = 0
      ↔ (q : ℚ) • va = (p : ℚ) • vb := by
  simpa using pair_face_power_eq_zero_iff hw va vb D hdefinite ![(q : ℚ), (p : ℚ)]

/-- [proved-derived; formal-checked] A pair lock is a linear set of rates: every multiple of a
zero-power rate remains a zero-power rate. -/
theorem lock_is_a_line (w : ℚ) (va vb : Vec) (D : Matrix (Fin 3) (Fin 3) ℚ)
    (u : Fin 2 → ℚ)
    (hzero : quad (faceForm w (pairSlip va vb) D) u = 0) (k : ℚ) :
    quad (faceForm w (pairSlip va vb) D) (k • u) = 0 := by
  rw [quad_smul, hzero, mul_zero]

/-! A positive-semidefinite material distinguishes quadratic null power from zero slip: the
material current can vanish while a nonzero relative velocity remains in its nullspace. -/

/-- [proved-derived; formal-checked] **Material-null pair power.** For a symmetric positive
semidefinite material, zero pair power is equivalent to the constitutive material current seeing
no slip. The pair's kinematic slip is retained on the right, so this does not silently identify a
material null direction with synchronization. -/
theorem pair_face_power_eq_zero_iff_material_null {w : ℚ} (hw : 0 < w) (va vb : Vec)
    (D : Matrix (Fin 3) (Fin 3) ℚ)
    (hDpsd : ∀ s : Vec, 0 ≤ quad D s)
    (hDsymm : Dᵀ = D) (u : Fin 2 → ℚ) :
    quad (faceForm w (pairSlip va vb) D) u = 0 ↔
      D *ᵥ (pairSlip va vb *ᵥ u) = 0 := by
  rw [quad_faceForm]
  constructor
  · intro h
    apply psd_mulVec_eq_zero_of_quad_eq_zero hDpsd hDsymm
    rcases mul_eq_zero.mp h with hw0 | hquad
    · exact (hw.ne' hw0).elim
    · exact hquad
  · intro h
    rw [h]
    simp

/-- [proved-derived; formal-checked] **Definite material restores the zero-slip kernel.** If the
positive-semidefinite material has no nonzero null direction among attainable pair slips,
its zero-power motions are exactly the pair's zero-slip motions. -/
theorem pair_face_power_eq_zero_iff_zero_slip_of_material_null {w : ℚ} (hw : 0 < w)
    (va vb : Vec) (D : Matrix (Fin 3) (Fin 3) ℚ)
    (hDpsd : ∀ s : Vec, 0 ≤ quad D s) (hDsymm : Dᵀ = D)
    (hDnull : ∀ v : Fin 2 → ℚ, D *ᵥ (pairSlip va vb *ᵥ v) = 0 →
      pairSlip va vb *ᵥ v = 0) (u : Fin 2 → ℚ) :
    quad (faceForm w (pairSlip va vb) D) u = 0 ↔ pairSlip va vb *ᵥ u = 0 := by
  rw [pair_face_power_eq_zero_iff_material_null hw va vb D hDpsd hDsymm u]
  constructor
  · exact fun h => hDnull u h
  · intro h
    rw [h]
    simp

/-- [proved-derived; formal-checked] **The pair quadrance two-jet is separation, slip pullback,
contact form and geometric term.** The first variation is the adjoint slip map applied to the
separation. The second variation is the isotropic contact form of the same slip map, carrying
both motions and their cross term, plus the `Δ·a` contribution of each object's own
acceleration. -/
theorem pairQuadranceTwoJet_eq_slip_contact_geometric (Δ va vb aa ab : Vec) (s t : ℚ) :
    pairQuadranceTwoJet Δ va vb aa ab s t
      = Δ ⬝ᵥ Δ
        + 2 * (![s, t] ⬝ᵥ ((pairSlip va vb)ᵀ *ᵥ Δ))
        + quad (faceForm 1 (pairSlip va vb) 1) ![s, t]
        + (s ^ 2 * (Δ ⬝ᵥ aa) - t ^ 2 * (Δ ⬝ᵥ ab)) := by
  rw [quad_faceForm, pairSlip_mulVec, pairSlip_transpose_mulVec]
  simp [pairQuadranceTwoJet, dotProduct, Fin.sum_univ_succ]
  ring

/-- [proved-derived; formal-checked] **A bilinear participation score is a polarized pair
quadrance.** The real bilinear score between a receiving current `a` and a transported source
current `b` is the two self-energies minus the quadrance of their separation `a − b`. A
unit-phase score is therefore the pair receiver restricted to two circles with no advance. -/
theorem bilinear_score_eq_polarized_quadrance {k : ℕ} (a b : Fin k → ℚ) :
    a ⬝ᵥ b = (a ⬝ᵥ a + b ⬝ᵥ b - (a - b) ⬝ᵥ (a - b)) / 2 := by
  simp only [sub_dotProduct, dotProduct_sub]
  rw [dotProduct_comm b a]
  ring

/-- [definition] The first quadrance participation score on a shared receiving row. -/
def pairScore {n : ℕ} (beta : ℚ) (Δ : Fin n → ℚ) : ℚ := -beta * (Δ ⬝ᵥ Δ) / 2

/-- [proved-derived; formal-checked] The exact finite directional score return retains both the
linear receiving covector and the quadratic geometric remainder. -/
theorem pairScore_add_sub {n : ℕ} (beta : ℚ) (Δ d : Fin n → ℚ) (epsilon : ℚ) :
    pairScore beta (Δ + epsilon • d) - pairScore beta Δ =
      -epsilon * beta * (Δ ⬝ᵥ d) - (epsilon ^ 2 * beta / 2) * (d ⬝ᵥ d) := by
  simp [pairScore, dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct]
  rw [dotProduct_comm d Δ]
  ring

/-! ## 3. Phase-carried material and the reflected return -/

section Group

variable {G : Type*} [Group G]

/-- [definition] Fixed material `P` carried to phase `d` by the phase shift `S`. -/
def phaseTransport (S P : G) (d : ℤ) : G := S ^ (-d) * P * S ^ d

/-- [proved-derived; formal-checked] At zero phase the carried material is the material. -/
theorem phaseTransport_zero (S P : G) : phaseTransport S P 0 = P := by
  simp [phaseTransport]

/-- [proved-derived; formal-checked] **Stepping is frame transport.** Advancing the phase by `e`
conjugates the already carried material; the material itself is unchanged. -/
theorem phaseTransport_add (S P : G) (d e : ℤ) :
    phaseTransport S P (d + e) = S ^ (-e) * phaseTransport S P d * S ^ e := by
  simp only [phaseTransport]
  group

/-- [proved-derived; formal-checked] **A closed phase admits a toroidal chart.** When the shift
closes after `n` steps, the carried material depends only on the phase modulo `n`. The closure
is a hypothesis about the shift, not a consequence of exact arithmetic. -/
theorem phaseTransport_add_period (S P : G) {n : ℤ} (hclose : S ^ n = 1) (d : ℤ) :
    phaseTransport S P (d + n) = phaseTransport S P d := by
  rw [phaseTransport_add, _root_.zpow_neg, hclose]
  simp

/-- [proved-derived; formal-checked] **Carried material factors through the phase.** If the carry
commutes with the material, advancing a whole turn leaves the carried material unchanged even
though the state has moved to the next level. The torus chart of the material forgets the
winding; the helix of the state keeps it. -/
theorem phaseTransport_add_carried_period (S P C : G) (n : ℤ) (hcarry : S ^ n = C)
    (hcomm : Commute C P) (d : ℤ) :
    phaseTransport S P (d + n) = phaseTransport S P d := by
  rw [phaseTransport_add, _root_.zpow_neg, hcarry]
  have hP : C⁻¹ * phaseTransport S P d * C = phaseTransport S P d := by
    have hS : Commute C S := by
      rw [← hcarry]
      exact (Commute.refl S).zpow_left n
    have hT : Commute C (phaseTransport S P d) := by
      unfold phaseTransport
      exact ((hS.zpow_right (-d)).mul_right hcomm).mul_right (hS.zpow_right d)
    rw [mul_assoc, ← hT.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  exact hP

/-- [proved-derived; formal-checked] **A stepped word is a power of one act-and-advance
generator.** Reading a stream of `n` occurrences through fixed material `P`, with the phase
advanced once per occurrence, composes to the `n`-th power of the single generator `P S⁻¹`
followed by the accumulated phase `Sⁿ`. The machine's size is independent of `n`; the stream
length enters only as an exponent and a retained winding. -/
theorem steppedWord_eq_generator_power (S P : G) (n : ℕ) :
    ((List.range n).map fun k : ℕ => phaseTransport S P (k : ℤ)).prod
      = (P * S⁻¹) ^ n * S ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, pow_succ, pow_succ]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      phaseTransport, _root_.zpow_neg, zpow_natCast]
    generalize (P * S⁻¹) ^ n = X
    group

/-- [definition] The return of a forward passage `A` through a reflection `F`, using the
operands that produced the forward passage. -/
def reflectedReturn (A F : G) : G := A⁻¹ * F * A

/-- [proved-derived; formal-checked] **An involutive reflection gives an involutive return at
every fixed state.** This is a fixed-state law; a stepping machine also evolves its state. -/
theorem reflectedReturn_involutive (A F : G) (hF : F * F = 1) :
    reflectedReturn A F * reflectedReturn A F = 1 := by
  calc reflectedReturn A F * reflectedReturn A F = A⁻¹ * (F * F) * A := by
        simp only [reflectedReturn]
        group
    _ = 1 := by
        rw [hF]
        group

/-- [proved-derived; formal-checked] A boundary conjugation distributes over an ordered word of
stage actions. -/
theorem boundary_conj_list_prod (S : G) (l : List G) :
    (l.map fun C => S⁻¹ * C * S).prod = S⁻¹ * l.prod * S := by
  induction l with
  | nil => simp
  | cons C l ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    group

end Group

section Permutation

variable {α : Type*}

/-- [proved-derived; formal-checked] A fixed-point-free reflection gives a fixed-point-free
return: no boundary port returns to itself at any machine state. -/
theorem reflectedReturn_no_fixed_point (A F : Equiv.Perm α) (hF : ∀ x, F x ≠ x) (x : α) :
    reflectedReturn A F x ≠ x := by
  intro h
  apply hF (A x)
  have hA : A (reflectedReturn A F x) = A x := by rw [h]
  simpa [reflectedReturn, Equiv.Perm.mul_apply] using hA

/-- [proved-derived; formal-checked] **Boundary reciprocity.** An involutive boundary pairing
relates two ports symmetrically. -/
theorem boundary_involution_reciprocal (S : Equiv.Perm α) (hS : S * S = 1) (a b : α) :
    S a = b ↔ S b = a := by
  have key : ∀ x, S (S x) = x := fun x => by
    have := congrArg (fun p : Equiv.Perm α => p x) hS
    simpa [Equiv.Perm.mul_apply] using this
  constructor
  · intro h
    rw [← h, key]
  · intro h
    rw [← h, key]

/-- [proved-derived; formal-checked] **Menu loop closure.** A closed path of observed boundary
relations, each conjugated by the same unknown boundary map `S`, closes at port `a` exactly when
the known stage word fixes the boundary image `S a`. A hypothesised machine phase whose stage
word has no compatible fixed point is refuted without resolving `S`; a compatible phase leaves
the remaining boundary family unresolved. -/
theorem menu_loop_closure (S : Equiv.Perm α) (l : List (Equiv.Perm α)) (a : α) :
    (l.map fun C => S⁻¹ * C * S).prod a = a ↔ l.prod (S a) = S a := by
  rw [boundary_conj_list_prod, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Equiv.Perm.inv_eq_iff_eq]

end Permutation

end Soma.Holonics.Transport.HelicalPairInteraction
