import ElementaryHolonics.Mathematics.JacobiEulerCubeStabilization

/-!
# The finite Jacobi diagonal has a complete square-support cone

The bivariate Jacobi carrier records outer degree `n` and Laurent orientation
`m` independently.  This file proves that the finite positive-orientation
factor lies in `m ≥ 0, m² ≤ n`, the inverse-orientation factor lies in
`m ≤ 0, m² ≤ n`, and their triple product therefore lies in `m² ≤ n`.

This is the exact locality theorem behind the diagonal receiver's finite
window: an occurrence outside that window cannot contribute.  The result is
constructed from the finite q-binomial expansion and coefficient incidence;
it is not a truncation convention.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.JacobiFiniteDiagonalCone

open PowerSeries
open Soma.Holonics.Mathematics.JacobiFiniteDiagonalProduct
open Soma.Holonics.Mathematics.JacobiTripleProductKernel

/-- The exact polynomial-to-series inclusion, named as a ring receiver so it
can participate in later commuting diagrams. -/
def polynomialPowerSeriesHom {S : Type*} [CommRing S] :
    Polynomial S →+* PowerSeries S where
  toFun := fun p => (p : PowerSeries S)
  map_zero' := Polynomial.coe_zero
  map_one' := Polynomial.coe_one
  map_add' := Polynomial.coe_add
  map_mul' := Polynomial.coe_mul

@[simp] theorem coeff_polynomialPowerSeriesHom {S : Type*} [CommRing S]
    (p : Polynomial S) (n : ℕ) :
    PowerSeries.coeff n (polynomialPowerSeriesHom p) = p.coeff n := by
  simp [polynomialPowerSeriesHom, Polynomial.toPowerSeries]

@[simp] theorem polynomialPowerSeriesHom_euler (p : PolynomialBody) :
    polynomialPowerSeriesHom (polynomialEulerDerivative p) =
      Soma.Holonics.Mathematics.JacobiEulerDerivative.bivariateEulerDerivative
        (polynomialPowerSeriesHom p) := by
  apply PowerSeries.ext
  intro n
  simp

/-- Positive Laurent orientations together with their square lower bound in
the outer degree. -/
def PositiveSquareCone
    (F : PowerSeries (LaurentPolynomial ℤ)) : Prop :=
  ∀ n m, (PowerSeries.coeff n F).coeff m ≠ 0 →
    0 ≤ m ∧ m ^ 2 ≤ (n : ℤ)

/-- Negative Laurent orientations together with their square lower bound in
the outer degree. -/
def NegativeSquareCone
    (F : PowerSeries (LaurentPolynomial ℤ)) : Prop :=
  ∀ n m, (PowerSeries.coeff n F).coeff m ≠ 0 →
    m ≤ 0 ∧ m ^ 2 ≤ (n : ℤ)

/-- The unsigned cone retained after the two orientations interact. -/
def SquareCone
    (F : PowerSeries (LaurentPolynomial ℤ)) : Prop :=
  ∀ n m, (PowerSeries.coeff n F).coeff m ≠ 0 →
    m ^ 2 ≤ (n : ℤ)

/-- Oppositely oriented square cones compose into the unsigned square cone.
The cross term has the required sign precisely because one orientation is
nonnegative and the other nonpositive. -/
theorem PositiveSquareCone.mul_negative
    {F G : PowerSeries (LaurentPolynomial ℤ)}
    (hF : PositiveSquareCone F) (hG : NegativeSquareCone G) :
    SquareCone (F * G) := by
  intro n m hcoeff
  rw [PowerSeries.coeff_mul] at hcoeff
  change (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G).coeff m ≠ 0 at hcoeff
  rw [AddMonoidAlgebra.coeff_sum] at hcoeff
  simp only [Finsupp.finsetSum_apply] at hcoeff
  have hout : ∃ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G).coeff m ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hcoeff
    apply Finset.sum_eq_zero
    intro p hp
    exact hnone p hp
  obtain ⟨p, hp, hpne⟩ := hout
  rw [AddMonoidAlgebra.mul_apply] at hpne
  let f := PowerSeries.coeff p.1 F
  let g := PowerSeries.coeff p.2 G
  have hinner : ∃ u ∈ f.coeff.support, ∃ v ∈ g.coeff.support,
      u + v = m ∧ f.coeff u * g.coeff v ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hpne
    calc
      f.coeff.sum (fun u cu => g.coeff.sum fun v cv =>
          if u + v = m then cu * cv else 0) =
          f.coeff.sum (fun _u _cu => 0) := by
            apply Finsupp.sum_congr
            intro u hu
            calc
              g.coeff.sum (fun v cv => if u + v = m then f.coeff u * cv else 0) =
                  g.coeff.sum (fun _v _cv => 0) := by
                    apply Finsupp.sum_congr
                    intro v hv
                    by_cases huv : u + v = m
                    · rw [if_pos huv]
                      exact hnone u hu v hv huv
                    · rw [if_neg huv]
              _ = 0 := by simp
      _ = 0 := by simp
  obtain ⟨u, hu, v, hv, huv, _huvne⟩ := hinner
  have hfu : f.coeff u ≠ 0 := Finsupp.mem_support_iff.mp hu
  have hgv : g.coeff v ≠ 0 := Finsupp.mem_support_iff.mp hv
  have hFu := hF p.1 u hfu
  have hGv := hG p.2 v hgv
  have hsum : p.1 + p.2 = n :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  push_cast at hsum
  nlinarith

/-- A bivariate series whose Laurent coefficients all occupy orientation
zero. -/
def IsScalarSeries
    (F : PowerSeries (LaurentPolynomial ℤ)) : Prop :=
  ∀ n, ∃ c : ℤ, PowerSeries.coeff n F = LaurentPolynomial.C c

theorem IsScalarSeries.zero : IsScalarSeries (0 :
    PowerSeries (LaurentPolynomial ℤ)) := by
  intro n
  exact ⟨0, by simp⟩

theorem IsScalarSeries.one : IsScalarSeries (1 :
    PowerSeries (LaurentPolynomial ℤ)) := by
  intro n
  by_cases h : n = 0
  · subst n
    exact ⟨1, by simp⟩
  · exact ⟨0, by simp [PowerSeries.coeff_one, h]⟩

theorem IsScalarSeries.add
    {F G : PowerSeries (LaurentPolynomial ℤ)}
    (hF : IsScalarSeries F) (hG : IsScalarSeries G) :
    IsScalarSeries (F + G) := by
  intro n
  obtain ⟨c, hc⟩ := hF n
  obtain ⟨e, he⟩ := hG n
  exact ⟨c + e, by simp [hc, he]⟩

theorem IsScalarSeries.mul
    {F G : PowerSeries (LaurentPolynomial ℤ)}
    (hF : IsScalarSeries F) (hG : IsScalarSeries G) :
    IsScalarSeries (F * G) := by
  intro n
  choose c hc using hF
  choose e he using hG
  refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c p.1 * e p.2, ?_⟩
  rw [PowerSeries.coeff_mul, map_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [hc, he, map_mul]

theorem IsScalarSeries.pow
    {F : PowerSeries (LaurentPolynomial ℤ)}
    (hF : IsScalarSeries F) : ∀ k : ℕ, IsScalarSeries (F ^ k)
  | 0 => by simpa using IsScalarSeries.one
  | k + 1 => by
      rw [pow_succ]
      exact (hF.pow k).mul hF

theorem q_isScalar : IsScalarSeries q := by
  intro n
  by_cases h : n = 1
  · subst n
    exact ⟨1, by simp⟩
  · exact ⟨0, by simp [PowerSeries.coeff_X, h]⟩

theorem IsScalarSeries.neg
    {F : PowerSeries (LaurentPolynomial ℤ)}
    (hF : IsScalarSeries F) : IsScalarSeries (-F) := by
  intro n
  obtain ⟨c, hc⟩ := hF n
  exact ⟨-c, by simp [hc]⟩

theorem IsScalarSeries.sub
    {F G : PowerSeries (LaurentPolynomial ℤ)}
    (hF : IsScalarSeries F) (hG : IsScalarSeries G) :
    IsScalarSeries (F - G) := by
  rw [sub_eq_add_neg]
  exact hF.add hG.neg

theorem qPoch_isScalar {A Q : R}
    (hA : IsScalarSeries A) (hQ : IsScalarSeries Q) (N : ℕ) :
    IsScalarSeries (qPoch A Q N) := by
  induction N with
  | zero => simpa [qPoch] using IsScalarSeries.one
  | succ N ih =>
      rw [qPoch_succ']
      exact ih.mul (IsScalarSeries.one.sub (hA.mul (hQ.pow N)))

theorem qBinom_isScalar : ∀ n k : ℕ,
    IsScalarSeries (qBinom (q ^ 2) n k)
  | _n, 0 => by simpa [qBinom] using IsScalarSeries.one
  | 0, _k + 1 => by simpa [qBinom] using IsScalarSeries.zero
  | n + 1, k + 1 => by
      rw [qBinom]
      exact (qBinom_isScalar n k).add
        ((q_isScalar.pow 2 |>.pow (k + 1)).mul
          (qBinom_isScalar n (k + 1)))

/-- One positive q-binomial summand occupies exactly orientation `k`, and its
outer degree begins at `k²`. -/
theorem positiveJacobiTerm_cone (N k : ℕ) :
    PositiveSquareCone
      (qBinom (q ^ 2) N k * (q ^ (k ^ 2) * a ^ k)) := by
  intro n m hcoeff
  have hscalar := qBinom_isScalar N k
  have haPow : a ^ k =
      PowerSeries.C (LaurentPolynomial.T (k : ℤ)) := by
    change PowerSeries.C (LaurentPolynomial.T 1) ^ k = _
    rw [← map_pow, LaurentPolynomial.T_pow]
    norm_num
  rw [haPow, ← mul_assoc, PowerSeries.coeff_mul_C] at hcoeff
  obtain ⟨c, hc⟩ := hscalar (n - k ^ 2)
  by_cases hn : k ^ 2 ≤ n
  · have hshift : PowerSeries.coeff n
        (qBinom (q ^ 2) N k * q ^ (k ^ 2)) =
          LaurentPolynomial.C c := by
        rw [mul_comm, ← Nat.sub_add_cancel hn,
          PowerSeries.coeff_X_pow_mul, hc]
    rw [hshift] at hcoeff
    have hm : m = (k : ℤ) := by
      by_contra hne
      apply hcoeff
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      rw [AddMonoidAlgebra.coeff_single_apply, if_neg (Ne.symm hne)]
    subst m
    constructor
    · exact Int.natCast_nonneg k
    · exact_mod_cast hn
  · push_neg at hn
    apply (hcoeff (by
      have horder : (n : ℕ∞) <
          (qBinom (q ^ 2) N k * q ^ (k ^ 2) : R).order := by
        calc
          (n : ℕ∞) < (k ^ 2 : ℕ) := by exact_mod_cast hn
          _ ≤ (q ^ (k ^ 2) : R).order := order_q_pow_ge _
          _ ≤ (qBinom (q ^ 2) N k).order +
              (q ^ (k ^ 2) : R).order := le_add_of_nonneg_left bot_le
          _ ≤ _ := PowerSeries.order_mul_ge _ _
      rw [PowerSeries.coeff_of_lt_order n horder]
      simp)).elim

theorem PositiveSquareCone.sum
    {ι : Type*} {s : Finset ι}
    {F : ι → PowerSeries (LaurentPolynomial ℤ)}
    (hF : ∀ i ∈ s, PositiveSquareCone (F i)) :
    PositiveSquareCone (∑ i ∈ s, F i) := by
  intro n m hcoeff
  have hcoeff' :
      (∑ i ∈ s, (PowerSeries.coeff n (F i)).coeff m) ≠ 0 := by
    intro hz
    apply hcoeff
    calc
      (PowerSeries.coeff n (∑ i ∈ s, F i)).coeff m =
          ∑ i ∈ s, (PowerSeries.coeff n (F i)).coeff m := by
            simp
      _ = 0 := hz
  have hex : ∃ i ∈ s, (PowerSeries.coeff n (F i)).coeff m ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hcoeff'
    exact Finset.sum_eq_zero fun i hi => hnone i hi
  obtain ⟨i, hi, hine⟩ := hex
  exact hF i hi n m hine

theorem finitePositiveJacobiProduct_cone (N : ℕ) :
    PositiveSquareCone (qPoch (-q * a) (q ^ 2) N) := by
  rw [show (-q * a : R) = -a * q by ring,
    qBinom_theorem (-a * q) (q ^ 2) N,
    qbinom_sum_rewrite a N]
  exact PositiveSquareCone.sum fun k _hk => positiveJacobiTerm_cone N k

/-- One inverse-orientation q-binomial summand occupies orientation `-k`, and
its outer degree likewise begins at `k²`. -/
theorem negativeJacobiTerm_cone (N k : ℕ) :
    NegativeSquareCone
      (qBinom (q ^ 2) N k * (q ^ (k ^ 2) * aI ^ k)) := by
  intro n m hcoeff
  have hscalar := qBinom_isScalar N k
  have haPow : aI ^ k =
      PowerSeries.C (LaurentPolynomial.T (-(k : ℤ))) := by
    change PowerSeries.C (LaurentPolynomial.T (-1)) ^ k = _
    rw [← map_pow, LaurentPolynomial.T_pow]
    congr 2
    ring
  rw [haPow, ← mul_assoc, PowerSeries.coeff_mul_C] at hcoeff
  obtain ⟨c, hc⟩ := hscalar (n - k ^ 2)
  by_cases hn : k ^ 2 ≤ n
  · have hshift : PowerSeries.coeff n
        (qBinom (q ^ 2) N k * q ^ (k ^ 2)) =
          LaurentPolynomial.C c := by
        rw [mul_comm, ← Nat.sub_add_cancel hn,
          PowerSeries.coeff_X_pow_mul, hc]
    rw [hshift] at hcoeff
    have hm : m = -(k : ℤ) := by
      by_contra hne
      apply hcoeff
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      rw [AddMonoidAlgebra.coeff_single_apply, if_neg (Ne.symm hne)]
    subst m
    constructor
    · exact neg_nonpos.mpr (Int.natCast_nonneg k)
    · have hnZ : (k : ℤ) ^ 2 ≤ (n : ℤ) := by exact_mod_cast hn
      nlinarith
  · push_neg at hn
    apply (hcoeff (by
      have horder : (n : ℕ∞) <
          (qBinom (q ^ 2) N k * q ^ (k ^ 2) : R).order := by
        calc
          (n : ℕ∞) < (k ^ 2 : ℕ) := by exact_mod_cast hn
          _ ≤ (q ^ (k ^ 2) : R).order := order_q_pow_ge _
          _ ≤ (qBinom (q ^ 2) N k).order +
              (q ^ (k ^ 2) : R).order := le_add_of_nonneg_left bot_le
          _ ≤ _ := PowerSeries.order_mul_ge _ _
      rw [PowerSeries.coeff_of_lt_order n horder]
      simp)).elim

theorem NegativeSquareCone.sum
    {ι : Type*} {s : Finset ι}
    {F : ι → PowerSeries (LaurentPolynomial ℤ)}
    (hF : ∀ i ∈ s, NegativeSquareCone (F i)) :
    NegativeSquareCone (∑ i ∈ s, F i) := by
  intro n m hcoeff
  have hcoeff' :
      (∑ i ∈ s, (PowerSeries.coeff n (F i)).coeff m) ≠ 0 := by
    intro hz
    apply hcoeff
    calc
      (PowerSeries.coeff n (∑ i ∈ s, F i)).coeff m =
          ∑ i ∈ s, (PowerSeries.coeff n (F i)).coeff m := by
            simp
      _ = 0 := hz
  have hex : ∃ i ∈ s, (PowerSeries.coeff n (F i)).coeff m ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hcoeff'
    exact Finset.sum_eq_zero fun i hi => hnone i hi
  obtain ⟨i, hi, hine⟩ := hex
  exact hF i hi n m hine

theorem finiteNegativeJacobiProduct_cone (N : ℕ) :
    NegativeSquareCone (qPoch (-q * aI) (q ^ 2) N) := by
  rw [show (-q * aI : R) = -aI * q by ring,
    qBinom_theorem (-aI * q) (q ^ 2) N,
    qbinom_sum_rewrite aI N]
  exact NegativeSquareCone.sum fun k _hk => negativeJacobiTerm_cone N k

/-- A scalar Laurent-neutral population can add outer degree but cannot move
an occurrence out of the square cone. -/
theorem IsScalarSeries.mul_squareCone
    {F G : PowerSeries (LaurentPolynomial ℤ)}
    (hF : IsScalarSeries F) (hG : SquareCone G) :
    SquareCone (F * G) := by
  intro n m hcoeff
  rw [PowerSeries.coeff_mul] at hcoeff
  change (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G).coeff m ≠ 0 at hcoeff
  rw [AddMonoidAlgebra.coeff_sum] at hcoeff
  simp only [Finsupp.finsetSum_apply] at hcoeff
  have hout : ∃ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G).coeff m ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hcoeff
    exact Finset.sum_eq_zero fun p hp => hnone p hp
  obtain ⟨p, hp, hpne⟩ := hout
  obtain ⟨c, hc⟩ := hF p.1
  rw [hc] at hpne
  have hGne : (PowerSeries.coeff p.2 G).coeff m ≠ 0 := by
    intro hz
    apply hpne
    rw [show LaurentPolynomial.C c =
        AddMonoidAlgebra.single (0 : ℤ) c by rfl,
      AddMonoidAlgebra.coeff_single_zero_mul, hz, mul_zero]
  have hcone := hG p.2 m hGne
  have hle : p.2 ≤ n := by
    have hsum : p.1 + p.2 = n :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    omega
  exact hcone.trans (by exact_mod_cast hle)

/-- The finite three-factor body in the same completed-series chart as the
Jacobi kernel. -/
def finiteBivariateTripleProduct (N : ℕ) : R :=
  qPoch (q ^ 2) (q ^ 2) N *
    qPoch (-q * a) (q ^ 2) N *
    qPoch (-q * aI) (q ^ 2) N

/-- **FINITE JACOBI SQUARE-CONE LAW.**  Every finite triple product has the
support bound `m² ≤ n`. -/
theorem finiteBivariateTripleProduct_squareCone (N : ℕ) :
    SquareCone (finiteBivariateTripleProduct N) := by
  have h0 : IsScalarSeries (qPoch (q ^ 2) (q ^ 2) N) :=
    qPoch_isScalar (q_isScalar.pow 2) (q_isScalar.pow 2) N
  have h13 : SquareCone
      (qPoch (-q * a) (q ^ 2) N *
        qPoch (-q * aI) (q ^ 2) N) :=
    (finitePositiveJacobiProduct_cone N).mul_negative
      (finiteNegativeJacobiProduct_cone N)
  simpa [finiteBivariateTripleProduct, mul_assoc] using
    h0.mul_squareCone h13

/-- Euler differentiation changes coefficients but not their addressed
support. -/
theorem SquareCone.eulerDerivative
    {F : PowerSeries (LaurentPolynomial ℤ)} (hF : SquareCone F) :
    SquareCone
      (Soma.Holonics.Mathematics.JacobiEulerDerivative.bivariateEulerDerivative F) := by
  intro n m hcoeff
  simp only [Soma.Holonics.Mathematics.JacobiEulerDerivative.coeff_bivariateEulerDerivative,
    Soma.Holonics.Mathematics.JacobiEulerDerivative.coeff_laurentEulerDerivative] at hcoeff
  have hsource : (PowerSeries.coeff n F).coeff m ≠ 0 := by
    intro hz
    apply hcoeff
    rw [hz, mul_zero]
  exact hF n m hsource

/-! ## The finite diagonal address change -/

/-- The diagonal substitution unit has the exact signed Laurent power
expected at every positive or negative orientation. -/
theorem negativeLaurentGenerator_zpow (k : ℤ) :
    ((negativeLaurentGenerator ^ k).val : LaurentBody) =
      LaurentPolynomial.C ((-1 : ℤ) ^ k.natAbs) *
        LaurentPolynomial.T k := by
  cases k with
  | ofNat n =>
      change (-LaurentPolynomial.T 1 : LaurentBody) ^ n = _
      rw [neg_pow, LaurentPolynomial.T_pow]
      simp
  | negSucc n =>
      change (-LaurentPolynomial.T (-1) : LaurentBody) ^ (n + 1) = _
      rw [neg_pow, LaurentPolynomial.T_pow]
      simp
      congr 1
      omega

theorem C_mul_T_apply (c k m : ℤ) :
    (LaurentPolynomial.C c * LaurentPolynomial.T k : LaurentBody).coeff m =
      if k = m then c else 0 := by
  rw [← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single_apply]

/-- The coefficient chart of `a ↦ -T` retains the Laurent address and adds
exactly its orientation sign. -/
theorem coefficientDiagonalHom_apply (f : LaurentBody) (m : ℤ) :
    (coefficientDiagonalHom f).coeff m =
      (-1 : ℤ) ^ m.natAbs * f.coeff m := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
      simp
      ring
  | C_mul_T k c =>
      simp only [map_mul, coefficientDiagonalHom,
        LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T,
        negativeLaurentGenerator_zpow]
      have hleft : LaurentPolynomial.C c *
            (LaurentPolynomial.C ((-1 : ℤ) ^ k.natAbs) *
              LaurentPolynomial.T k) =
          LaurentPolynomial.C (c * ((-1 : ℤ) ^ k.natAbs)) *
            LaurentPolynomial.T k := by
        rw [← mul_assoc, ← map_mul]
      rw [hleft, C_mul_T_apply, C_mul_T_apply]
      by_cases hkm : k = m
      · rw [if_pos hkm]
        subst m
        simp [mul_comm]
      · rw [if_neg hkm, if_neg hkm]
        simp

/-- **FINITE DIAGONAL COEFFICIENT FORMULA.**  The polynomial diagonal hom is
the signed sum over the exact address change `m = d - n`. -/
theorem finiteDiagonalHom_apply (p : PolynomialBody) (d : ℤ) :
    (finiteDiagonalHom p).coeff d =
      ∑ n ∈ p.support,
        (-1 : ℤ) ^ (d - (n : ℤ)).natAbs *
          (p.coeff n).coeff (d - (n : ℤ)) := by
  change (Polynomial.eval₂ coefficientDiagonalHom
      (LaurentPolynomial.T 1) p).coeff d = _
  rw [Polynomial.eval₂_eq_sum]
  unfold Polynomial.sum
  change (∑ n ∈ p.support,
        coefficientDiagonalHom (p.coeff n) *
          LaurentPolynomial.T 1 ^ n).coeff d = _
  rw [AddMonoidAlgebra.coeff_sum]
  simp only [Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [LaurentPolynomial.T_pow]
  simp only [mul_one]
  have hshift :
      ((coefficientDiagonalHom (p.coeff n) *
          LaurentPolynomial.T (n : ℤ) : LaurentBody)).coeff d =
        (coefficientDiagonalHom (p.coeff n)).coeff (d - (n : ℤ)) := by
    have hT : (LaurentPolynomial.T (n : ℤ) : LaurentBody) =
        AddMonoidAlgebra.single (n : ℤ) 1 := by
      simpa using
        (LaurentPolynomial.single_eq_C_mul_T
          (R := ℤ) 1 (n : ℤ)).symm
    rw [mul_comm, hT, AddMonoidAlgebra.coeff_single_mul_apply]
    simp [sub_eq_add_neg, add_comm]
  change (coefficientDiagonalHom (p.coeff n) *
      LaurentPolynomial.T (n : ℤ) : LaurentBody).coeff d = _
  rw [hshift, coefficientDiagonalHom_apply]

/-- A nonzero diagonal occurrence in the square cone is necessarily inside
the receiver's declared orientation window. -/
theorem SquareCone.diagonal_mem_box
    {F : R} (hF : SquareCone F) {d n : ℕ} {m : ℤ}
    (hcoeff : (PowerSeries.coeff n F).coeff m ≠ 0)
    (hdiag : (n : ℤ) + m = (d : ℤ)) :
    m ∈ Finset.Icc (-((d : ℤ) + 1)) ((d : ℤ) + 1) := by
  have hcone := hF n m hcoeff
  rw [Finset.mem_Icc]
  constructor
  · by_cases hm : 0 ≤ m
    · omega
    · have hm' : m ≤ -1 := by omega
      have hsquare : 0 ≤ (-m - 1) ^ 2 := sq_nonneg (-m - 1)
      nlinarith
  · by_cases hm : m ≤ 0
    · have hd : 0 ≤ (d : ℤ) := by positivity
      linarith
    · have hm' : 1 ≤ m := by omega
      have hsquare : 0 ≤ (m - 1) ^ 2 := sq_nonneg (m - 1)
      nlinarith

/-- The same cone law in the outer-degree chart: a diagonal coefficient at
`d` receives no source coefficient beyond `2d+1`. -/
theorem SquareCone.diagonal_outer_le
    {F : R} (hF : SquareCone F) {d n : ℕ} {m : ℤ}
    (hcoeff : (PowerSeries.coeff n F).coeff m ≠ 0)
    (hdiag : (n : ℤ) + m = (d : ℤ)) :
    n ≤ 2 * d + 1 := by
  have hbox := SquareCone.diagonal_mem_box hF hcoeff hdiag
  rw [Finset.mem_Icc] at hbox
  omega

#print axioms PositiveSquareCone.mul_negative
#print axioms finitePositiveJacobiProduct_cone
#print axioms finiteNegativeJacobiProduct_cone
#print axioms finiteBivariateTripleProduct_squareCone
#print axioms finiteDiagonalHom_apply
#print axioms SquareCone.diagonal_mem_box

end Soma.Holonics.Mathematics.JacobiFiniteDiagonalCone
