import ElementaryHolonics.Millennium.FamilyTunnellFourSquarePrimeCensus
import Mathlib.NumberTheory.Divisors

/-!
# The exact Lambert/divisor receiver in Jacobi's four-square passage

The four-square product identity lands coefficientwise on eight times the sum
of divisors not divisible by four.  This file constructs that target as an
exact integer power series and closes its odd-prime coefficient.  The pending
edge is therefore only the source product equality, not an unspecified
arithmetic formula.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareLambert

open Finset
open PowerSeries

/-- The retained divisors in Jacobi's four-square coefficient. -/
def nonFourDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => ¬ 4 ∣ d

/-- Exact divisor current before multiplication by the eight signed coordinate
orientations. -/
def jacobiDivisorCurrent (n : ℕ) : ℤ :=
  ∑ d ∈ nonFourDivisors n, (d : ℤ)

/-- The ordinary first-power divisor current before the modulo-four aperture is applied. -/
def ordinaryDivisorCurrent (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (d : ℤ)

/-- The reconstruction fibre deleted by the `4 ∤ d` receiver. -/
def fourDivisibleDivisorCurrent (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors.filter fun d => 4 ∣ d, (d : ℤ)

/-- The Jacobi divisor current is exactly the full divisor population minus the fibre whose
addresses are divisible by four.  This is a partition identity, not an estimate. -/
theorem jacobiDivisorCurrent_eq_ordinary_sub_fourDivisible (n : ℕ) :
    jacobiDivisorCurrent n =
      ordinaryDivisorCurrent n - fourDivisibleDivisorCurrent n := by
  have hpartition := Finset.sum_filter_add_sum_filter_not n.divisors
    (fun d => 4 ∣ d) (fun d => (d : ℤ))
  rw [jacobiDivisorCurrent, nonFourDivisors, ordinaryDivisorCurrent,
    fourDivisibleDivisorCurrent]
  omega

private def timesFourEmbedding : ℕ ↪ ℕ where
  toFun d := 4 * d
  inj' := by
    intro a b h
    exact mul_left_cancel₀ (by norm_num : (4 : ℕ) ≠ 0) h

/-- Multiplication by four is an exact address equivalence from the complete divisor population of
`m` onto the four-divisible divisor fibre of `4m`. -/
theorem fourDivisibleDivisorCurrent_four_mul (m : ℕ) :
    fourDivisibleDivisorCurrent (4 * m) = 4 * ordinaryDivisorCurrent m := by
  by_cases hm : m = 0
  · subst m
    simp [fourDivisibleDivisorCurrent, ordinaryDivisorCurrent]
  have hfourm : 4 * m ≠ 0 := mul_ne_zero (by norm_num) hm
  have hfibre :
      (4 * m).divisors.filter (fun d => 4 ∣ d) =
        m.divisors.map timesFourEmbedding := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_map]
    constructor
    · rintro ⟨⟨hdvd, _⟩, hfour⟩
      rcases hfour with ⟨e, rfl⟩
      refine ⟨e, ⟨?_, hm⟩, rfl⟩
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 4)).mp hdvd
    · rintro ⟨e, ⟨he, _⟩, rfl⟩
      refine ⟨⟨?_, hfourm⟩, dvd_mul_right 4 e⟩
      exact mul_dvd_mul_left 4 he
  rw [fourDivisibleDivisorCurrent, hfibre, ordinaryDivisorCurrent]
  simp [timesFourEmbedding, Finset.mul_sum]

/-- At a divisible address the deleted receiver fibre is four times the ordinary divisor current
at the exactly rebased address. -/
theorem fourDivisibleDivisorCurrent_eq_if (n : ℕ) :
    fourDivisibleDivisorCurrent n =
      if 4 ∣ n then 4 * ordinaryDivisorCurrent (n / 4) else 0 := by
  by_cases hfour : 4 ∣ n
  · rcases hfour with ⟨m, rfl⟩
    simp [fourDivisibleDivisorCurrent_four_mul]
  · simp [hfour, fourDivisibleDivisorCurrent]
    apply Finset.sum_eq_zero
    intro d hd
    exact (hfour (dvd_trans (Finset.mem_filter.mp hd).2
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1))).elim

/-- The modulo-four Jacobi aperture is the exact sigma-difference chart requested by the outer
Euler-current recurrence. -/
theorem jacobiDivisorCurrent_eq_sigma_difference (n : ℕ) :
    jacobiDivisorCurrent n =
      ordinaryDivisorCurrent n -
        if 4 ∣ n then 4 * ordinaryDivisorCurrent (n / 4) else 0 := by
  rw [jacobiDivisorCurrent_eq_ordinary_sub_fourDivisible,
    fourDivisibleDivisorCurrent_eq_if]

/-- The coefficient of the logarithmic Euler connection carried by the Jacobi quartic product. -/
def thetaQuarticConnectionCoeff (n : ℕ) : ℤ :=
  ordinaryDivisorCurrent n -
      (if 2 ∣ n then 5 * ordinaryDivisorCurrent (n / 2) else 0) +
    (if 4 ∣ n then 4 * ordinaryDivisorCurrent (n / 4) else 0)

/-- The exact connection series in the outer Euler equation for the four-square source. -/
def thetaQuarticConnection : PowerSeries ℤ :=
  PowerSeries.mk fun n => 8 * thetaQuarticConnectionCoeff n

@[simp] theorem coeff_thetaQuarticConnection (n : ℕ) :
    PowerSeries.coeff n thetaQuarticConnection =
      8 * thetaQuarticConnectionCoeff n := by
  simp [thetaQuarticConnection]

@[simp] theorem thetaQuarticConnectionCoeff_zero :
    thetaQuarticConnectionCoeff 0 = 0 := by
  simp [thetaQuarticConnectionCoeff, ordinaryDivisorCurrent]

@[simp] theorem coeff_thetaQuarticConnection_zero :
    PowerSeries.coeff 0 thetaQuarticConnection = 0 := by
  simp

/-- The complete exact Lambert receiver of the four-square source. -/
def jacobiFourSquareLambertSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n => 8 * jacobiDivisorCurrent n

/-- The completed receiver, with the unique norm-zero occurrence retained as its constant face.
The uncompleted Lambert current begins at positive address because `Nat.divisors 0 = ∅`. -/
def completedJacobiFourSquareLambertSeries : PowerSeries ℤ :=
  1 + jacobiFourSquareLambertSeries

@[simp] theorem coeff_jacobiFourSquareLambertSeries (n : ℕ) :
    PowerSeries.coeff n jacobiFourSquareLambertSeries =
      8 * jacobiDivisorCurrent n := by
  simp [jacobiFourSquareLambertSeries]

@[simp] theorem coeff_jacobiFourSquareLambertSeries_zero :
    PowerSeries.coeff 0 jacobiFourSquareLambertSeries = 0 := by
  simp [jacobiDivisorCurrent, nonFourDivisors]

@[simp] theorem coeff_completedJacobiFourSquareLambertSeries_zero :
    PowerSeries.coeff 0 completedJacobiFourSquareLambertSeries = 1 := by
  rw [completedJacobiFourSquareLambertSeries, map_add,
    PowerSeries.coeff_one, coeff_jacobiFourSquareLambertSeries_zero]
  simp

/-- At every positive address, completion changes no divisor current. -/
theorem coeff_completedJacobiFourSquareLambertSeries_of_pos
    {n : ℕ} (hn : 0 < n) :
    PowerSeries.coeff n completedJacobiFourSquareLambertSeries =
      8 * jacobiDivisorCurrent n := by
  simp [completedJacobiFourSquareLambertSeries, coeff_jacobiFourSquareLambertSeries,
    PowerSeries.coeff_one, hn.ne']

private theorem four_not_dvd_odd {n : ℕ} (hn : Odd n) : ¬ 4 ∣ n := by
  rcases hn with ⟨k, hk⟩
  rintro ⟨j, hj⟩
  omega

/-- At an odd prime, the complete retained divisor population is `{1,p}`. -/
theorem nonFourDivisors_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    nonFourDivisors p = {1, p} := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  ext d
  rw [nonFourDivisors, Finset.mem_filter, Nat.mem_divisors]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hd, _hpzero⟩, _hfour⟩
    exact (Nat.dvd_prime hp).mp hd
  · intro hd
    rcases hd with rfl | rfl
    · exact ⟨⟨one_dvd _, hp.ne_zero⟩, by norm_num⟩
    · exact ⟨⟨dvd_rfl, hp.ne_zero⟩, four_not_dvd_odd hpodd⟩

/-- The exact divisor current at an odd prime is `p+1`. -/
theorem jacobiDivisorCurrent_prime {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    jacobiDivisorCurrent p = (p : ℤ) + 1 := by
  rw [jacobiDivisorCurrent, nonFourDivisors_prime hp hp2]
  have hp1 : p ≠ 1 := hp.ne_one
  rw [Finset.sum_insert]
  · simp
    ring
  · simpa only [Finset.mem_singleton, eq_comm] using hp1

/-- **THE FOUR-SQUARE LAMBERT RECEIVER RETURNS `8(p+1)` AT EVERY ODD
PRIME.** -/
theorem coeff_jacobiFourSquareLambertSeries_prime {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    PowerSeries.coeff p jacobiFourSquareLambertSeries =
      8 * ((p : ℤ) + 1) := by
  rw [coeff_jacobiFourSquareLambertSeries,
    jacobiDivisorCurrent_prime hp hp2]

#print axioms nonFourDivisors_prime
#print axioms jacobiDivisorCurrent_eq_ordinary_sub_fourDivisible
#print axioms fourDivisibleDivisorCurrent_four_mul
#print axioms fourDivisibleDivisorCurrent_eq_if
#print axioms jacobiDivisorCurrent_eq_sigma_difference
#print axioms coeff_thetaQuarticConnection
#print axioms coeff_thetaQuarticConnection_zero
#print axioms jacobiDivisorCurrent_prime
#print axioms coeff_jacobiFourSquareLambertSeries_prime
#print axioms coeff_completedJacobiFourSquareLambertSeries_of_pos

end Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareLambert
