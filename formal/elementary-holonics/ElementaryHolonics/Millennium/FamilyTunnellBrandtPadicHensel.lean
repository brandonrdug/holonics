import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.RingTheory.Int.Basic

/-!
# The exact Hensel turn used by an odd-prime Brandt neighbor

An integral isotropic direction modulo `p` becomes an exact isotropic
direction over `ℤ_p` by one scalar correction current.  After dividing the
quadratic reading by the visible leading `p`, the correction equation has the
form

`p*q + b*X + p*c*X^2 = 0`,

where the polar coefficient `b` is prime to `p`.  This file proves the exact
root and retains its neighbourhood receipt.  It is source-neutral and does
not assume a destination class or a genus theorem.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtPadicHensel

open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- The scalar correction equation obtained from
`Q(v + p*s*w) = p * (p*q + b*s + p*Q(w)*s^2)`. -/
def correctionPolynomial (q b c : ℤ) : Polynomial ℤ :=
  C ((p : ℤ) * q) + C b * X + C ((p : ℤ) * c) * X ^ 2

@[simp]
theorem correctionPolynomial_aeval_zero (q b c : ℤ) :
    (correctionPolynomial (p := p) q b c).aeval (0 : ℤ_[p]) =
      ((p : ℤ) * q : ℤ) := by
  simp [correctionPolynomial]

@[simp]
theorem correctionPolynomial_derivative_aeval_zero (q b c : ℤ) :
    (derivative (correctionPolynomial (p := p) q b c)).aeval (0 : ℤ_[p]) =
      (b : ℤ_[p]) := by
  simp [correctionPolynomial]

/-- An integral coefficient prime to `p` remains a unit-size element of
`ℤ_p`. -/
theorem norm_intCast_eq_one_of_not_dvd (b : ℤ) (hb : ¬(p : ℤ) ∣ b) :
    ‖(b : ℤ_[p])‖ = 1 := by
  rw [PadicInt.norm_intCast_eq_one_iff]
  rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (by simpa [Int.natCast_dvd] using hb)).symm

/-- A unit polar coefficient produces an exact `p`-adic correction root.
The returned root remains in the strict unit neighbourhood of the initial
zero approximation, so the complete Hensel branch is retained rather than
only its terminal equation. -/
theorem exists_exact_correction (q b c : ℤ) (hb : ¬(p : ℤ) ∣ b) :
    ∃ s : ℤ_[p],
      (correctionPolynomial (p := p) q b c).aeval s = 0 ∧
        ‖s‖ < 1 := by
  let F := correctionPolynomial (p := p) q b c
  have hvalue : ‖F.aeval (0 : ℤ_[p])‖ < 1 := by
    rw [show F.aeval (0 : ℤ_[p]) = (((p : ℤ) * q : ℤ) : ℤ_[p]) by
      simp [F]]
    rw [PadicInt.norm_intCast_lt_one_iff]
    exact dvd_mul_right (p : ℤ) q
  have hderiv : ‖F.derivative.aeval (0 : ℤ_[p])‖ = 1 := by
    rw [show F.derivative.aeval (0 : ℤ_[p]) = (b : ℤ_[p]) by
      simp [F]]
    exact norm_intCast_eq_one_of_not_dvd b hb
  have hnorm :
      ‖F.aeval (0 : ℤ_[p])‖ <
        ‖F.derivative.aeval (0 : ℤ_[p])‖ ^ 2 := by
    rw [hderiv, one_pow]
    exact hvalue
  obtain ⟨s, hs, hnear, hderiv_s, hunique⟩ := hensels_lemma hnorm
  refine ⟨s, hs, ?_⟩
  simpa [hderiv] using hnear

#print axioms correctionPolynomial_aeval_zero
#print axioms correctionPolynomial_derivative_aeval_zero
#print axioms norm_intCast_eq_one_of_not_dvd
#print axioms exists_exact_correction

end Soma.Holonics.Millennium.FamilyTunnellBrandtPadicHensel
