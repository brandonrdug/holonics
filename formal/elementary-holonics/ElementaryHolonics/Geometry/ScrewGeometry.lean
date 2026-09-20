import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic
import ElementaryHolonics.Millennium.HolonicQuadraticMomentCondensation

/-!
# Local screw generators and pair-distance jets

This owner keeps the shared helical geometry at its local algebraic scope.  A screw generator is a
pair `ξ = (ω, v)` with velocity field `Vξ(x) = ω × x + v`; the file proves the Lie bracket,
translation covariance, the two scalar pair invariants, and the exact quadratic two-jet of a pair
distance.  It does not assert a global exponential screw theorem.
-/

noncomputable section

open scoped BigOperators Matrix
open Matrix

namespace Soma.Holonics.Geometry.ScrewGeometry

open Soma.Holonics.Millennium.HolonicQuadraticMomentCondensation

abbrev Vec := Fin 3 → ℚ

@[simp] theorem vec_head_zero (a : Vec) : Matrix.vecHead a = a 0 := rfl
@[simp] theorem vec_head_tail_zero (a : Vec) : Matrix.vecHead (Matrix.vecTail a) = a 1 := rfl
@[simp] theorem vec_head_tail_tail_zero (a : Vec) :
    Matrix.vecHead (Matrix.vecTail (Matrix.vecTail a)) = a 2 := rfl

structure Screw where
  angular : Vec
  linear : Vec

def velocity (ξ : Screw) (x : Vec) : Vec := ξ.angular ⨯₃ x + ξ.linear

def bracket (ξ η : Screw) : Screw where
  angular := ξ.angular ⨯₃ η.angular
  linear := ξ.angular ⨯₃ η.linear - η.angular ⨯₃ ξ.linear

def velocityCommutator (ξ η : Screw) (x : Vec) : Vec :=
  velocity ξ (velocity η x) - velocity η (velocity ξ x) - ξ.linear + η.linear

theorem bracket_antisymm (ξ η : Screw) : bracket η ξ = {
    angular := -(bracket ξ η).angular
    linear := -(bracket ξ η).linear
  } := by
  cases ξ with
  | mk ω v =>
    cases η with
    | mk θ u =>
      simp [bracket, cross_anticomm]

theorem bracket_angular_antisymm (ξ η : Screw) :
    (bracket ξ η).angular = -(bracket η ξ).angular := by
  simp [bracket, cross_anticomm]

theorem velocity_bracket_action (ξ η : Screw) (x : Vec) :
    velocity (bracket ξ η) x =
      velocityCommutator ξ η x := by
  cases ξ with
  | mk ω v =>
    cases η with
    | mk θ u =>
      simp only [velocity, velocityCommutator, bracket]
      rw [cross_cross]
      funext i
      fin_cases i <;> simp [cross_apply, Matrix.cons_val] <;> ring

def pairK (ξ η : Screw) : ℚ := ξ.angular ⬝ᵥ η.angular

def pairR (ξ η : Screw) : ℚ := ξ.angular ⬝ᵥ η.linear + ξ.linear ⬝ᵥ η.angular

theorem pairK_symmetric (ξ η : Screw) : pairK ξ η = pairK η ξ := by
  simp [pairK, dotProduct_comm]

theorem pairR_symmetric (ξ η : Screw) : pairR ξ η = pairR η ξ := by
  simp [pairR, dotProduct_comm, add_comm]

theorem pure_translations_commute (v u : Vec) :
    bracket { angular := 0, linear := v } { angular := 0, linear := u } =
      { angular := 0, linear := 0 } := by
  simp [bracket]

def translated (t : Vec) (ξ : Screw) : Screw where
  angular := ξ.angular
  linear := ξ.linear + t ⨯₃ ξ.angular

theorem velocity_translation_covariance (t : Vec) (ξ : Screw) (x : Vec) :
    velocity (translated t ξ) (x + t) = velocity ξ x := by
  funext i
  fin_cases i <;> simp [translated, velocity, cross_apply, Matrix.cons_val] <;> ring

theorem pairK_translation_invariant (t : Vec) (ξ η : Screw) :
    pairK (translated t ξ) (translated t η) = pairK ξ η := by
  simp [pairK, translated]

theorem pairR_translation_invariant (t : Vec) (ξ η : Screw) :
    pairR (translated t ξ) (translated t η) = pairR ξ η := by
  cases ξ with
  | mk ω v =>
    cases η with
    | mk θ u =>
      simp [pairR, translated, cross_apply, vec3_dotProduct]
      ring

def pairQuadrance (Δ va vb : Vec) (s t : ℚ) : ℚ :=
  (Δ + s • va - t • vb) ⬝ᵥ (Δ + s • va - t • vb)

def pairQuadrancePath (Δ va vb aa ab : Vec) (s t : ℚ) : ℚ :=
  (Δ + s • va - t • vb + (s ^ 2 / 2) • aa - (t ^ 2 / 2) • ab) ⬝ᵥ
    (Δ + s • va - t • vb + (s ^ 2 / 2) • aa - (t ^ 2 / 2) • ab)

def pairQuadranceTwoJet (Δ va vb aa ab : Vec) (s t : ℚ) : ℚ :=
  Δ ⬝ᵥ Δ + s * (2 * (Δ ⬝ᵥ va)) - t * (2 * (Δ ⬝ᵥ vb))
    + s ^ 2 * (va ⬝ᵥ va + Δ ⬝ᵥ aa)
    + s * t * (-2 * (va ⬝ᵥ vb))
    + t ^ 2 * (vb ⬝ᵥ vb - Δ ⬝ᵥ ab)

def pairQuadranceRemainder (_Δ va vb aa ab : Vec) (s t : ℚ) : ℚ :=
  2 * ((s • va - t • vb) ⬝ᵥ ((s ^ 2 / 2) • aa - (t ^ 2 / 2) • ab))
    + ((s ^ 2 / 2) • aa - (t ^ 2 / 2) • ab) ⬝ᵥ
      ((s ^ 2 / 2) • aa - (t ^ 2 / 2) • ab)

/-- The exact polynomial two-jet coefficients of pair quadrance. -/
theorem pairQuadrancePath_eq_twoJet_plus_remainder (Δ va vb aa ab : Vec) (s t : ℚ) :
    pairQuadrancePath Δ va vb aa ab s t = pairQuadranceTwoJet Δ va vb aa ab s t
      + pairQuadranceRemainder Δ va vb aa ab s t := by
  simp [pairQuadrancePath, pairQuadranceTwoJet, pairQuadranceRemainder, dotProduct,
    Fin.sum_univ_succ]
  ring

theorem pairQuadrance_origin (Δ va vb aa ab : Vec) :
    pairQuadrancePath Δ va vb aa ab 0 0 = Δ ⬝ᵥ Δ := by
  simp [pairQuadrancePath]

theorem pairQuadrance_first_difference (Δ va vb aa ab : Vec) (h : ℚ) :
    pairQuadrancePath Δ va vb aa ab h 0 - pairQuadrancePath Δ va vb aa ab 0 0 =
      h * (2 * (Δ ⬝ᵥ va)) + h ^ 2 * (va ⬝ᵥ va + Δ ⬝ᵥ aa)
        + h ^ 3 * (va ⬝ᵥ aa) + h ^ 4 * (aa ⬝ᵥ aa / 4) := by
  simp [pairQuadrancePath, dotProduct, Fin.sum_univ_succ]
  ring

theorem pairQuadrance_exchange (Δ va vb aa ab : Vec) (s t : ℚ) :
    pairQuadrancePath (-Δ) vb va ab aa t s = pairQuadrancePath Δ va vb aa ab s t := by
  simp [pairQuadrancePath, dotProduct, Fin.sum_univ_succ]
  ring

theorem pairQuadrance_twoJet_exchange (Δ va vb aa ab : Vec) (s t : ℚ) :
    pairQuadranceTwoJet (-Δ) vb va ab aa t s = pairQuadranceTwoJet Δ va vb aa ab s t := by
  simp [pairQuadranceTwoJet, dotProduct, Fin.sum_univ_succ]
  ring

/-! ## The pair face as an existing quadratic-moment receiver -/

abbrev PairCell := Sum (Fin 3) (Fin 3)

def pairMomentReceiver : Matrix PairCell PairCell ℚ := fun left right =>
  match left, right with
  | Sum.inl i, Sum.inl j => if i = j then 1 else 0
  | Sum.inr i, Sum.inr j => if i = j then 1 else 0
  | Sum.inl i, Sum.inr j => if i = j then -1 else 0
  | Sum.inr i, Sum.inl j => if i = j then -1 else 0

def singletonWeight : Unit → ℚ := fun _ => 1

def pairCurrent (xa xb : Vec) : Unit → PairCell → ℚ := fun _ cell =>
  match cell with
  | Sum.inl i => xa i
  | Sum.inr i => xb i

theorem pair_quadrance_is_existing_moment_contraction (xa xb : Vec) :
    contractMoment pairMomentReceiver
        (quadraticMoment singletonWeight (pairCurrent xa xb)) =
      (xa - xb) ⬝ᵥ (xa - xb) := by
  rw [contract_quadraticMoment_eq_enumerateQuadraticReceiver]
  simp [enumerateQuadraticReceiver, pairMomentReceiver, singletonWeight, pairCurrent,
    vec3_dotProduct, Fin.sum_univ_succ]
  ring

end Soma.Holonics.Geometry.ScrewGeometry
