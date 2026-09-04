import ElementaryHolonics.Millennium.FamilyTunnellBrandtMinkowskiBounds
import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighborGram

/-!
# Exact boundary of determinant-only Brandt destination reduction

The determinant and positive-definiteness faces do not classify a ternary
integral lattice into the two Tunnell--Brandt classes.  This file exhibits an
exact obstruction inside the diagonal subfamily: the form

`Q₃(x,y,z) = x² + y² + 64z²`

has half-polar determinant `64` and full-polar determinant `512`, but is
integrally inequivalent to both target receivers.  Its norm-one fibre has four
points, while `Q₁` has two and `Q₂` has none.

The file also exhausts the ordered positive diagonal determinant-`64` faces.
There are exactly seven.  Consequently a Jones--Pall destination theorem must
use the source-specific local/genus incidence in addition to determinant,
rank, integrality, and positivity; those four shadows alone leave at least the
six displayed diagonal alternatives other than the first target.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtDestinationReduction

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector
open Soma.Holonics.Millennium.FamilyTunnellNormOneReturn
open Soma.Holonics.Millennium.FamilyTunnellBrandtGenusInvariants
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborGram

/-! ## A determinant-64 positive lattice outside the two target classes -/

/-- The third exact receiver used to separate determinant from destination. -/
def brandtThirdQuadratic (v : IntTriple) : ℤ :=
  v.1 ^ 2 + v.2.1 ^ 2 + 64 * v.2.2 ^ 2

/-- Its half-polar Gram matrix. -/
def brandtThirdGram : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 64]

/-- Its full-polar Gram matrix. -/
def brandtThirdFullGram : Matrix (Fin 3) (Fin 3) ℤ :=
  2 • brandtThirdGram

theorem brandtThirdGram_det : brandtThirdGram.det = 64 := by
  decide

theorem brandtThirdFullGram_det : brandtThirdFullGram.det = 512 := by
  decide

theorem brandtThirdQuadratic_nonnegative (v : IntTriple) :
    0 ≤ brandtThirdQuadratic v := by
  unfold brandtThirdQuadratic
  positivity

theorem brandtThirdQuadratic_eq_zero_iff (v : IntTriple) :
    brandtThirdQuadratic v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hx : v.1 = 0 := by
      unfold brandtThirdQuadratic at h
      nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
    have hy : v.2.1 = 0 := by
      unfold brandtThirdQuadratic at h
      nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
    have hz : v.2.2 = 0 := by
      unfold brandtThirdQuadratic at h
      nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
    rcases v with ⟨x, y, z⟩
    simp_all
  · rintro rfl
    norm_num [brandtThirdQuadratic]

/-- The exact norm-one fibre of the third receiver has four points. -/
theorem brandtThirdQuadratic_eq_one_iff (v : IntTriple) :
    brandtThirdQuadratic v = 1 ↔
      v = (1, 0, 0) ∨ v = (-1, 0, 0) ∨
      v = (0, 1, 0) ∨ v = (0, -1, 0) := by
  constructor
  · intro h
    have hxlo : -1 ≤ v.1 := by
      unfold brandtThirdQuadratic at h
      nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
    have hxhi : v.1 ≤ 1 := by
      unfold brandtThirdQuadratic at h
      nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
    have hylo : -1 ≤ v.2.1 := by
      unfold brandtThirdQuadratic at h
      nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
    have hyhi : v.2.1 ≤ 1 := by
      unfold brandtThirdQuadratic at h
      nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
    have hz : v.2.2 = 0 := by
      unfold brandtThirdQuadratic at h
      nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
    have hx : v.1 = -1 ∨ v.1 = 0 ∨ v.1 = 1 := by omega
    have hy : v.2.1 = -1 ∨ v.2.1 = 0 ∨ v.2.1 = 1 := by omega
    rcases v with ⟨x, y, z⟩
    simp only at hxlo hxhi hylo hyhi hz hx hy h
    rcases hx with hx | hx | hx <;>
      rcases hy with hy | hy | hy <;>
      subst x <;> subst y <;> subst z <;>
      norm_num [brandtThirdQuadratic] at h
    all_goals simp
  · rintro (rfl | rfl | rfl | rfl) <;>
      norm_num [brandtThirdQuadratic]

/-- No arbitrary bijection, hence no integral linear isometry, transports the
third receiver to the first target. -/
theorem no_third_first_integral_receiver_equivalence :
    ¬ ∃ e : IntTriple ≃ IntTriple,
      ∀ m : IntTriple, brandtFirstQuadratic (e m) = brandtThirdQuadratic m := by
  rintro ⟨e, he⟩
  let a : IntTriple := (1, 0, 0)
  let b : IntTriple := (-1, 0, 0)
  let c : IntTriple := (0, 1, 0)
  have haQ : brandtFirstQuadratic (e a) = 1 := by
    rw [he]
    norm_num [a, brandtThirdQuadratic]
  have hbQ : brandtFirstQuadratic (e b) = 1 := by
    rw [he]
    norm_num [b, brandtThirdQuadratic]
  have hcQ : brandtFirstQuadratic (e c) = 1 := by
    rw [he]
    norm_num [c, brandtThirdQuadratic]
  have ha := (brandtFirstQuadratic_eq_one_iff (e a)).mp haQ
  have hb := (brandtFirstQuadratic_eq_one_iff (e b)).mp hbQ
  have hc := (brandtFirstQuadratic_eq_one_iff (e c)).mp hcQ
  have hab : e a ≠ e b := by
    intro h
    have := e.injective h
    norm_num [a, b] at this
  have hac : e a ≠ e c := by
    intro h
    have := e.injective h
    norm_num [a, c] at this
  have hbc : e b ≠ e c := by
    intro h
    have := e.injective h
    norm_num [b, c] at this
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rcases hc with hc | hc <;> simp_all

/-- The second target has no norm-one point, so one point of the third fibre
already separates it. -/
theorem no_third_second_integral_receiver_equivalence :
    ¬ ∃ e : IntTriple ≃ IntTriple,
      ∀ m : IntTriple, brandtSecondQuadratic (e m) = brandtThirdQuadratic m := by
  rintro ⟨e, he⟩
  have hone : brandtSecondQuadratic (e (1, 0, 0)) = 1 := by
    rw [he]
    norm_num [brandtThirdQuadratic]
  exact brandtSecondQuadratic_ne_one (e (1, 0, 0)) hone

/-- Determinant `64`, full determinant `512`, and positivity are jointly
insufficient to force either Tunnell--Brandt destination. -/
theorem determinant_positive_destination_insufficiency :
    brandtThirdGram.det = 64 ∧
      brandtThirdFullGram.det = 512 ∧
      (∀ v : IntTriple, 0 ≤ brandtThirdQuadratic v) ∧
      (∀ v : IntTriple, brandtThirdQuadratic v = 0 ↔ v = 0) ∧
      (¬ ∃ e : IntTriple ≃ IntTriple,
        ∀ m, brandtFirstQuadratic (e m) = brandtThirdQuadratic m) ∧
      (¬ ∃ e : IntTriple ≃ IntTriple,
        ∀ m, brandtSecondQuadratic (e m) = brandtThirdQuadratic m) := by
  exact ⟨brandtThirdGram_det, brandtThirdFullGram_det,
    brandtThirdQuadratic_nonnegative, brandtThirdQuadratic_eq_zero_iff,
    no_third_first_integral_receiver_equivalence,
    no_third_second_integral_receiver_equivalence⟩

/-! ## Exhaustive ordered diagonal determinant-64 partition -/

/-- There are exactly seven ordered positive diagonal coefficient triples
with determinant `64`.  This is an exact finite normal-form partition, not an
estimate. -/
theorem ordered_positive_diagonal_det64_partition
    (a b c : ℕ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hdet : a * b * c = 64) :
    (a, b, c) = (1, 1, 64) ∨
      (a, b, c) = (1, 2, 32) ∨
      (a, b, c) = (1, 4, 16) ∨
      (a, b, c) = (1, 8, 8) ∨
      (a, b, c) = (2, 2, 16) ∨
      (a, b, c) = (2, 4, 8) ∨
      (a, b, c) = (4, 4, 4) := by
  have hbcSq : b * b ≤ b * c := Nat.mul_le_mul_left b hbc
  have honea : 1 ≤ a := ha
  have hscale : b * c ≤ a * (b * c) := by
    simpa using Nat.mul_le_mul_right (b * c) honea
  have hbSq : b * b ≤ 64 := by
    calc
      b * b ≤ b * c := hbcSq
      _ ≤ a * (b * c) := hscale
      _ = 64 := by simpa [Nat.mul_assoc] using hdet
  have hb8 : b ≤ 8 := by nlinarith
  have ha8 : a ≤ 8 := le_trans hab hb8
  interval_cases a <;> interval_cases b <;>
    norm_num at hdet ⊢ <;> omega

/-- The target first diagonal form is only one member of the exact seven-face
partition.  Six coefficient triples survive determinant and positivity before
the source-specific local incidence is applied. -/
theorem ordered_positive_diagonal_det64_target_or_residual
    (a b c : ℕ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hdet : a * b * c = 64) :
    (a, b, c) = (1, 2, 32) ∨
      (a, b, c) = (1, 1, 64) ∨
      (a, b, c) = (1, 4, 16) ∨
      (a, b, c) = (1, 8, 8) ∨
      (a, b, c) = (2, 2, 16) ∨
      (a, b, c) = (2, 4, 8) ∨
      (a, b, c) = (4, 4, 4) := by
  rcases ordered_positive_diagonal_det64_partition a b c ha hab hbc hdet with
    h | h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

#print axioms brandtThirdGram_det
#print axioms brandtThirdFullGram_det
#print axioms brandtThirdQuadratic_eq_zero_iff
#print axioms brandtThirdQuadratic_eq_one_iff
#print axioms no_third_first_integral_receiver_equivalence
#print axioms no_third_second_integral_receiver_equivalence
#print axioms determinant_positive_destination_insufficiency
#print axioms ordered_positive_diagonal_det64_partition

end Soma.Holonics.Millennium.FamilyTunnellBrandtDestinationReduction
