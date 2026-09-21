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

/-! ## 2. The pair as a contact face -/

/-- [proved-derived; formal-checked] **Pair contact power.** A contact face whose slip map is the
pair's reads its constitutive response at the pair's relative velocity. -/
theorem pair_face_power (w : ℚ) (va vb : Vec) (D : Matrix (Fin 3) (Fin 3) ℚ) (u : Fin 2 → ℚ) :
    quad (faceForm w (pairSlip va vb) D) u
      = w * ((u 0 • va - u 1 • vb) ⬝ᵥ (D *ᵥ (u 0 • va - u 1 • vb))) := by
  rw [quad_faceForm, pairSlip_mulVec]

/-- [proved-derived; formal-checked] **Synchronized passage is the zero-power kernel.** On a
dissipative face of positive weight, a pair motion dissipates nothing exactly when the two
objects' contact velocities agree. This is the incidence/synchronization law between `s` and `t`
read from the material, not an identification of the two parameters. -/
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
