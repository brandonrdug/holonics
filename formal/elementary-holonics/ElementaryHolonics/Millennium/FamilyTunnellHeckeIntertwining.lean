import ElementaryHolonics.Millennium.FamilyTunnellShimuraLift
import ElementaryHolonics.Millennium.HeckeEuler

/-!
# The half-integral Hecke current and its Shimura return

This file builds the uniform arithmetic mechanism that the finite Sturm-aperture
comparison exposed.  It does not use a library theorem named "Shimura
correspondence".  Instead it defines the weight-three-halves coefficient operator
at an odd prime and proves the local recurrence which transports a `T(p²)`
eigen-orbit to the ordinary weight-two `T(p)` recurrence.

For a coefficient current `a`, the half-integral operator is

`a(p²n) + (-n/p) a(n) + p a(n/p²)`,

where the last term is present only when `p² ∣ n`.  Along the square orbit
`1,p²,p⁴,...`, the middle character occurs only at the first cell.  Convolving this
orbit with the quadratic character is exactly the prime-power part of the Shimura
divisor transport.  The theorem `localShimuraRecurrence` proves, for every depth,
that its returned current satisfies

`A(p^(e+2)) = λₚ A(p^(e+1)) - p A(p^e)`.

The remaining source-specific deed is to prove that the complete Tunnell theta
carrier is an eigen-current for this operator at every odd prime.  No absence in an
external modular-form library is used as a boundary here: the operator and the
intertwining algebra are constructed below.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellHeckeIntertwining

open NumberTheorySymbols
open Soma.Holonics.Millennium.FamilyTunnellShimuraLift
open Soma.Holonics.Millennium.FamilyTunnellThetaCarrier

/-! ## 1. The actual weight-three-halves prime operator -/

/-- A coefficient read through an exact divisibility chart.  It is zero outside the
image of multiplication by `divisor`; no truncated natural-number quotient is
mistaken for an antecedent. -/
def exactQuotientCoefficient (source : ℕ → ℚ) (divisor n : ℕ) : ℚ :=
  if divisor ∣ n then source (n / divisor) else 0

/-- The coefficient action of `T(p²)` in weight `3/2` with trivial Dirichlet
character. -/
def halfIntegralHeckeCoefficient (source : ℕ → ℚ) (p n : ℕ) : ℚ :=
  source (p ^ 2 * n) + (jacobiSym (-(n : ℤ)) p : ℚ) * source n +
    (p : ℚ) * exactQuotientCoefficient source (p ^ 2) n

/-- A source coefficient current is a `T(p²)` eigen-current when the coefficient
identity holds at every addressed index. -/
def IsHalfIntegralHeckeEigenAt (source : ℕ → ℚ) (p : ℕ) (eigenvalue : ℚ) : Prop :=
  ∀ n : ℕ, halfIntegralHeckeCoefficient source p n = eigenvalue * source n

/-! ## 2. The local square orbit -/

/-- The source current along the square powers of one prime. -/
def squareOrbit (source : ℕ → ℚ) (p e : ℕ) : ℚ :=
  source (p ^ (2 * e))

/-- The prime-power Shimura return of an abstract square-orbit current.  The
orientation `s^j` is the retained quadratic character of the divisor `p^j`. -/
def localShimuraCurrent (orbit : ℕ → ℚ) (s : ℚ) (e : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (e + 1), s ^ (e - j) * orbit j

@[simp] theorem localShimuraCurrent_zero (orbit : ℕ → ℚ) (s : ℚ) :
    localShimuraCurrent orbit s 0 = orbit 0 := by
  simp [localShimuraCurrent]

/-- Adding one prime layer adds one new source shell and transports the complete
earlier current by one character turn. -/
theorem localShimuraCurrent_succ (orbit : ℕ → ℚ) (s : ℚ) (e : ℕ) :
    localShimuraCurrent orbit s (e + 1) =
      orbit (e + 1) + s * localShimuraCurrent orbit s e := by
  unfold localShimuraCurrent
  rw [show e + 1 + 1 = (e + 1) + 1 by omega, Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, one_mul]
  have hsum :
      (∑ j ∈ Finset.range (e + 1), s ^ (e + 1 - j) * orbit j) =
        s * ∑ j ∈ Finset.range (e + 1), s ^ (e - j) * orbit j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hexponent : e + 1 - j = (e - j) + 1 := by omega
    rw [hexponent, pow_succ]
    ring
  rw [hsum]
  ring

/-- The exact hypotheses supplied by a half-integral Hecke eigen-orbit. -/
structure PrimeSquareOrbitLaw (orbit : ℕ → ℚ) (s p eigenvalue : ℚ) : Prop where
  characterSquare : s ^ 2 = 1
  base : orbit 1 + s * orbit 0 = eigenvalue * orbit 0
  step : ∀ e : ℕ,
    orbit (e + 2) + p * orbit e = eigenvalue * orbit (e + 1)

/-- The first returned prime layer already has the integral-weight eigenvalue. -/
theorem localShimuraCurrent_one_eq
    {orbit : ℕ → ℚ} {s p eigenvalue : ℚ}
    (law : PrimeSquareOrbitLaw orbit s p eigenvalue) :
    localShimuraCurrent orbit s 1 = eigenvalue * localShimuraCurrent orbit s 0 := by
  rw [localShimuraCurrent_succ, localShimuraCurrent_zero, law.base]

/-- **Shimura--Hecke intertwining on every prime-power layer.**  The returned
divisor current obeys the ordinary weight-two Euler recurrence exactly. -/
theorem localShimuraRecurrence
    {orbit : ℕ → ℚ} {s p eigenvalue : ℚ}
    (law : PrimeSquareOrbitLaw orbit s p eigenvalue) (e : ℕ) :
    localShimuraCurrent orbit s (e + 2) =
      eigenvalue * localShimuraCurrent orbit s (e + 1) -
        p * localShimuraCurrent orbit s e := by
  induction e with
  | zero =>
      have hA0 := localShimuraCurrent_zero orbit s
      have hA1 := localShimuraCurrent_succ orbit s 0
      have hA2 := localShimuraCurrent_succ orbit s 1
      have hstep : orbit 2 + p * orbit 0 = eigenvalue * orbit 1 := by
        simpa using law.step 0
      rw [hA2, hA1, hA0]
      linear_combination hstep + s * law.base
  | succ e ih =>
      have hA1 := localShimuraCurrent_succ orbit s e
      have hA2 := localShimuraCurrent_succ orbit s (e + 1)
      have hA3 := localShimuraCurrent_succ orbit s (e + 2)
      have hstep : orbit (e + 3) + p * orbit (e + 1) =
          eigenvalue * orbit (e + 2) := by
        simpa [Nat.add_assoc] using law.step (e + 1)
      have hgoal : localShimuraCurrent orbit s (e + 3) =
          eigenvalue * localShimuraCurrent orbit s (e + 2) -
            p * localShimuraCurrent orbit s (e + 1) := by
        linear_combination hA3 + hstep + s * ih - eigenvalue * hA2 + p * hA1
      simpa [Nat.add_assoc] using hgoal

/-! ## 3. The local current is the actual prime-power Shimura coefficient -/

/-- The odd quadratic character transports a prime power by repeated copies of the
prime character. -/
theorem shimuraQuadraticCharacter_prime_pow {t p : ℕ}
    (hpodd : Odd p) (e : ℕ) :
    shimuraQuadraticCharacter t (p ^ e) =
      shimuraQuadraticCharacter t p ^ e := by
  unfold shimuraQuadraticCharacter
  rw [if_pos hpodd.pow, if_pos hpodd, jacobiSym.pow_right]

/-- The square-power source orbit used by the index-one lift. -/
def sourceSquareOrbit (source : ℕ → ℚ) (p e : ℕ) : ℚ :=
  source (p ^ (2 * e))

/-- At every odd prime power, the global divisor definition of the Shimura
coefficient is exactly the local character current.  This closes the finite-divisor
to recurrence chart rather than merely comparing their first values. -/
theorem shimuraCoefficient_prime_pow_eq_localShimuraCurrent
    (source : ℕ → ℚ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ) :
    shimuraCoefficient source 1 (p ^ e) =
      localShimuraCurrent (sourceSquareOrbit source p)
        (shimuraQuadraticCharacter 1 p : ℚ) e := by
  have hpodd : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left hp2)
  have hdivisor : shimuraCoefficient source 1 (p ^ e) =
      ∑ j ∈ Finset.range (e + 1),
        (shimuraQuadraticCharacter 1 p : ℚ) ^ j *
          sourceSquareOrbit source p (e - j) := by
    unfold shimuraCoefficient
    rw [Nat.divisors_prime_pow hp, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hje : j ≤ e := by omega
    have hchar :
        (shimuraQuadraticCharacter 1 (p ^ j) : ℚ) =
          (shimuraQuadraticCharacter 1 p : ℚ) ^ j := by
      exact_mod_cast shimuraQuadraticCharacter_prime_pow (t := 1) hpodd j
    have hdiv : p ^ e / p ^ j = p ^ (e - j) := Nat.pow_div hje hp.pos
    have hsquare : (p ^ (e - j)) ^ 2 = p ^ (2 * (e - j)) := by
      rw [← pow_mul]
      congr 1
      omega
    change (shimuraQuadraticCharacter 1 (p ^ j) : ℚ) *
        source (1 * (p ^ e / p ^ j) ^ 2) =
      (shimuraQuadraticCharacter 1 p : ℚ) ^ j *
        sourceSquareOrbit source p (e - j)
    rw [hchar, hdiv, one_mul, hsquare]
    rfl
  rw [hdivisor]
  unfold localShimuraCurrent
  rw [← Finset.sum_range_reflect
    (fun j => (shimuraQuadraticCharacter 1 p : ℚ) ^ (e - j) *
      sourceSquareOrbit source p j) (e + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hje : j ≤ e := by omega
  have hreflect : e + 1 - 1 - j = e - j := by omega
  have hreturn : e - (e - j) = j := by omega
  rw [hreflect, hreturn]

/-! ## 4. A global half-integral eigenlaw returns the local orbit law -/

/-- Restricting the actual coefficient operator to the square-power orbit produces
exactly the base character turn followed by the two-step prime recurrence. -/
theorem primeSquareOrbitLaw_of_halfIntegralHeckeEigen
    (source : ℕ → ℚ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {eigenvalue : ℚ} (heigen : IsHalfIntegralHeckeEigenAt source p eigenvalue) :
    PrimeSquareOrbitLaw (sourceSquareOrbit source p)
      (shimuraQuadraticCharacter 1 p : ℚ) (p : ℚ) eigenvalue := by
  have hpodd : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left hp2)
  refine
    { characterSquare := ?_
      base := ?_
      step := ?_ }
  · have hj : jacobiSym (-1 : ℤ) p ^ 2 = 1 :=
      jacobiSym.sq_one (by norm_num)
    have hjQ : ((jacobiSym (-1 : ℤ) p : ℤ) : ℚ) ^ 2 = 1 := by
      exact_mod_cast hj
    simpa [shimuraQuadraticCharacter, hpodd] using hjQ
  · have hnot : ¬p ^ 2 ∣ 1 := by
      intro h
      exact hp.not_dvd_one ((dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)).trans h)
    have h := heigen 1
    simpa [halfIntegralHeckeCoefficient, exactQuotientCoefficient, hnot,
      sourceSquareOrbit, shimuraQuadraticCharacter, hpodd] using h
  · intro e
    let n : ℕ := p ^ (2 * (e + 1))
    have hexponent : 2 ≤ 2 * (e + 1) := by omega
    have hpdvd : p ∣ n := by
      unfold n
      exact dvd_pow_self p (by omega)
    have hp2dvd : p ^ 2 ∣ n := by
      unfold n
      refine ⟨p ^ (2 * e), ?_⟩
      rw [← pow_add]
      congr 1
      omega
    have hfirst : p ^ 2 * n = p ^ (2 * (e + 2)) := by
      unfold n
      rw [← pow_add]
      congr 1
      omega
    have hquotient : n / p ^ 2 = p ^ (2 * e) := by
      unfold n
      rw [Nat.pow_div hexponent hp.pos]
      congr 1
    have hcharacter : jacobiSym (-(n : ℤ)) p = 0 := by
      rw [jacobiSym.mod_left]
      have hmod : (-(n : ℤ)) % (p : ℤ) = 0 := by
        apply Int.emod_eq_zero_of_dvd
        exact dvd_neg.mpr (Int.natCast_dvd_natCast.mpr hpdvd)
      rw [hmod]
      exact jacobiSym.zero_left hp.one_lt
    have h := heigen n
    rw [halfIntegralHeckeCoefficient, hfirst, hcharacter, Int.cast_zero,
      zero_mul, add_zero, exactQuotientCoefficient, if_pos hp2dvd, hquotient] at h
    simpa [sourceSquareOrbit, n] using h

/-- Consequently every prime-power coefficient of a Shimura lift of a genuine
half-integral eigen-current obeys the ordinary weight-two Hecke recurrence. -/
theorem shimuraCoefficient_prime_power_recurrence_of_eigen
    (source : ℕ → ℚ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {eigenvalue : ℚ} (heigen : IsHalfIntegralHeckeEigenAt source p eigenvalue)
    (e : ℕ) :
    shimuraCoefficient source 1 (p ^ (e + 2)) =
      eigenvalue * shimuraCoefficient source 1 (p ^ (e + 1)) -
        (p : ℚ) * shimuraCoefficient source 1 (p ^ e) := by
  rw [shimuraCoefficient_prime_pow_eq_localShimuraCurrent source hp hp2,
    shimuraCoefficient_prime_pow_eq_localShimuraCurrent source hp hp2,
    shimuraCoefficient_prime_pow_eq_localShimuraCurrent source hp hp2]
  exact localShimuraRecurrence
    (primeSquareOrbitLaw_of_halfIntegralHeckeEigen source hp hp2 heigen) e

/-! ## 5. The source-specific executable aperture -/

/-- The quadratic orientation seen by the index-one Shimura lift at `p`. -/
def tunnellPrimeCharacter (p : ℕ) : ℚ :=
  (shimuraQuadraticCharacter 1 p : ℚ)

/-- The complete Tunnell square orbit. -/
def tunnellSquareOrbit (p e : ℕ) : ℚ :=
  normalizedTunnellCoefficient (p ^ (2 * e))

/-- The actual `T(p²)` eigen defect of the Tunnell source against the already
constructed level-32 eigenvalue stream.  Its uniform zero section is now one precise
lattice theorem, rather than the name of a missing library feature. -/
def tunnellHalfIntegralHeckeDefect (p n : ℕ) : ℚ :=
  halfIntegralHeckeCoefficient normalizedTunnellCoefficient p n -
    (Soma.Holonics.Millennium.HeckeTheta.heckeCoeff p : ℚ) *
      normalizedTunnellCoefficient n

/-- The exact source law is verified at the first odd prime across a nontrivial
square-orbit aperture. -/
theorem tunnellHalfIntegralHeckeDefect_three_first_orbit :
    ∀ n ∈ ({1, 9, 81} : Finset ℕ), tunnellHalfIntegralHeckeDefect 3 n = 0 := by
  native_decide

/-- The same source law at the first split prime. -/
theorem tunnellHalfIntegralHeckeDefect_five_first_orbit :
    ∀ n ∈ ({1, 25, 625} : Finset ℕ), tunnellHalfIntegralHeckeDefect 5 n = 0 := by
  native_decide

#print axioms localShimuraCurrent_succ
#print axioms localShimuraCurrent_one_eq
#print axioms localShimuraRecurrence
#print axioms shimuraCoefficient_prime_pow_eq_localShimuraCurrent
#print axioms primeSquareOrbitLaw_of_halfIntegralHeckeEigen
#print axioms shimuraCoefficient_prime_power_recurrence_of_eigen
#print axioms tunnellHalfIntegralHeckeDefect_three_first_orbit
#print axioms tunnellHalfIntegralHeckeDefect_five_first_orbit

end Soma.Holonics.Millennium.FamilyTunnellHeckeIntertwining
