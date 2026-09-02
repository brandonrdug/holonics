import ElementaryHolonics.Millennium.FamilyTunnellJacobiFourSquareEulerReturn
import ElementaryHolonics.Mathematics.JacobiTripleProductKernel

/-!
# Finite Euler-factor connections for the Jacobi four-square source

The outer Euler current of one factor `1 - X^d` is the exact addressed
current `-d X^d`.  When `d > 0`, the factor has constant occurrence one and
therefore an exact formal inverse.  Multiplying the current by that inverse
returns a constitutive connection without deleting the factor body.

Finite products then add these connections.  The terminal theorem applies
this law to the literal finite Euler product

`qPoch (X^k) (X^k) N = ∏ i < N, (1 - X^(k*(i+1)))`.

Everything in this file is finite.  No derivative of an infinite product,
analytic limit, or coefficient estimate is used.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiFiniteEulerConnection

open PowerSeries
open Soma.Holonics.Mathematics.JacobiTripleProductKernel
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareEulerReturn
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareLambert

/-- One addressed Euler factor. -/
def finiteEulerFactor (d : ℕ) : PowerSeries ℤ :=
  1 - PowerSeries.X ^ d

/-- The exact current produced by one Euler factor. -/
def finiteEulerFactorCurrent (d : ℕ) : PowerSeries ℤ :=
  -(d : ℤ) • (PowerSeries.X ^ d : PowerSeries ℤ)

/-- **ONE-FACTOR EULER LAW.**  The outer Euler current of `1 - X^d`
retains the exponent as its exact signed multiplicity. -/
theorem powerSeriesEulerCurrent_finiteEulerFactor (d : ℕ) :
    powerSeriesEulerCurrent (finiteEulerFactor d) =
      finiteEulerFactorCurrent d := by
  by_cases hd : d = 0
  · subst d
    simp [finiteEulerFactor, finiteEulerFactorCurrent,
      powerSeriesEulerCurrent]
  apply PowerSeries.ext
  intro n
  rw [coeff_powerSeriesEulerCurrent]
  simp only [finiteEulerFactor, finiteEulerFactorCurrent, map_sub,
    PowerSeries.coeff_one, PowerSeries.coeff_X_pow, PowerSeries.coeff_smul, map_smul, map_zsmul]
  by_cases hn : n = d
  · subst n
    first
      | simp [hd]
      | (rw [← map_natCast (PowerSeries.C ℤ), PowerSeries.coeff_C_mul]; simp [hd])
      | (rw [← map_natCast PowerSeries.C, PowerSeries.coeff_C_mul]; simp [hd])
  · rw [if_neg hn]
    by_cases hn0 : n = 0
    · subst n
      simp [hd]
    · first
        | simp [hn0, hn]
        | (rw [← map_natCast (PowerSeries.C ℤ), PowerSeries.coeff_C_mul]; simp [hn0, hn])
        | (rw [← map_natCast PowerSeries.C, PowerSeries.coeff_C_mul]; simp [hn0, hn])

/-- A positive-degree Euler factor retains the unit constant occurrence. -/
@[simp] theorem constantCoeff_finiteEulerFactor {d : ℕ} (hd : d ≠ 0) :
    PowerSeries.constantCoeff (finiteEulerFactor d) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [finiteEulerFactor, hd]

/-- The complete predecessor fibre of one positive-degree Euler factor.  It
retains one occurrence at every nonnegative multiple of the factor degree. -/
def finiteEulerGeometricFiber (d : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if d ∣ n then 1 else 0

@[simp] theorem coeff_finiteEulerGeometricFiber (d n : ℕ) :
    PowerSeries.coeff n (finiteEulerGeometricFiber d) =
      if d ∣ n then 1 else 0 := by
  simp [finiteEulerGeometricFiber]

/-- The geometric predecessor fibre is the exact right inverse of a
positive-degree Euler factor. -/
theorem finiteEulerFactor_mul_geometricFiber
    {d : ℕ} (hd : d ≠ 0) :
    finiteEulerFactor d * finiteEulerGeometricFiber d = 1 := by
  rw [finiteEulerFactor, sub_mul, one_mul]
  apply PowerSeries.ext
  intro n
  rw [map_sub, PowerSeries.coeff_X_pow_mul']
  by_cases hle : d ≤ n
  · rw [if_pos hle]
    have hn0 : n ≠ 0 := by omega
    have hdiv : d ∣ n ↔ d ∣ n - d := by
      exact (Nat.dvd_sub_iff_left hle (dvd_refl d)).symm
    by_cases hdn : d ∣ n
    · have hsub := hdiv.mp hdn
      simp [hdn, hsub, hn0]
    · have hsub : ¬ d ∣ n - d := fun h => hdn (hdiv.mpr h)
      simp [hdn, hsub, hn0]
  · rw [if_neg hle]
    by_cases hn0 : n = 0
    · subst n
      simp [finiteEulerGeometricFiber]
    · have hndiv : ¬ d ∣ n := by
        intro hdn
        exact hle (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn)
      simp [hndiv, hn0]

/-- The library inverse and the explicit geometric predecessor fibre are the
same reconstruction body. -/
theorem invOfUnit_finiteEulerFactor_eq_geometricFiber
    {d : ℕ} (hd : d ≠ 0) :
    PowerSeries.invOfUnit (finiteEulerFactor d) 1 =
      finiteEulerGeometricFiber d := by
  have hfactor : finiteEulerFactor d ≠ 0 := by
    intro hzero
    have hconstant := congrArg PowerSeries.constantCoeff hzero
    rw [constantCoeff_finiteEulerFactor hd] at hconstant
    simp at hconstant
  apply mul_left_cancel₀ hfactor
  rw [PowerSeries.mul_invOfUnit _ _
    (constantCoeff_finiteEulerFactor hd),
    finiteEulerFactor_mul_geometricFiber hd]

/-- The constitutive connection of one positive-degree factor.  Its inverse
is a formal reconstruction fibre justified by the separately retained unit
constant coefficient. -/
def finiteEulerFactorConnection (d : ℕ) : PowerSeries ℤ :=
  finiteEulerFactorCurrent d *
    PowerSeries.invOfUnit (finiteEulerFactor d) 1

/-- One positive-degree Euler factor carries its exact formal connection. -/
theorem hasEulerConnection_finiteEulerFactor {d : ℕ} (hd : d ≠ 0) :
    Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareEulerReturn.HasEulerConnection
      (finiteEulerFactorConnection d)
      (finiteEulerFactor d) := by
  rw [Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareEulerReturn.HasEulerConnection,
    powerSeriesEulerCurrent_finiteEulerFactor]
  unfold finiteEulerFactorConnection
  calc
    finiteEulerFactorCurrent d =
        finiteEulerFactorCurrent d * 1 := by ring
    _ = finiteEulerFactorCurrent d *
          (PowerSeries.invOfUnit (finiteEulerFactor d) 1 *
            finiteEulerFactor d) := by
      rw [PowerSeries.invOfUnit_mul _ _
        (constantCoeff_finiteEulerFactor hd)]
    _ = (finiteEulerFactorCurrent d *
          PowerSeries.invOfUnit (finiteEulerFactor d) 1) *
            finiteEulerFactor d := by ring

/-- The coefficient of one factor connection is the exact signed degree at
every positive multiple of that degree, and zero elsewhere.  Address zero is
kept separate even though every positive degree divides zero. -/
theorem coeff_finiteEulerFactorConnection
    {d n : ℕ} (hd : d ≠ 0) :
    PowerSeries.coeff n (finiteEulerFactorConnection d) =
      if n ≠ 0 ∧ d ∣ n then -(d : ℤ) else 0 := by
  rw [finiteEulerFactorConnection,
    invOfUnit_finiteEulerFactor_eq_geometricFiber hd]
  rw [finiteEulerFactorCurrent, smul_mul_assoc]
  simp only [PowerSeries.coeff_smul, map_smul, map_zsmul,
    PowerSeries.coeff_X_pow_mul']
  by_cases hle : d ≤ n
  · rw [if_pos hle]
    have hn0 : n ≠ 0 := by omega
    have hdiv : d ∣ n ↔ d ∣ n - d := by
      exact (Nat.dvd_sub_iff_left hle (dvd_refl d)).symm
    by_cases hdn : d ∣ n
    · have hsub := hdiv.mp hdn
      simp [hn0, hdn, hsub]
    · have hsub : ¬ d ∣ n - d := fun h => hdn (hdiv.mpr h)
      simp [hn0, hdn, hsub]
  · rw [if_neg hle]
    have hnot : ¬(n ≠ 0 ∧ d ∣ n) := by
      rintro ⟨hn0, hdn⟩
      exact hle (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn)
    simp [hnot]

/-- The connection returned by a finite addressed population of factors. -/
def finiteEulerProductConnection {ι : Type*}
    (s : Finset ι) (degree : ι → ℕ) : PowerSeries ℤ :=
  ∑ i ∈ s, finiteEulerFactorConnection (degree i)

/-- The coefficient receiver of a finite connection is the exact sum of the
signed degrees whose generator paths meet the queried address. -/
theorem coeff_finiteEulerProductConnection
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (degree : ι → ℕ)
    (hdegree : ∀ i ∈ s, degree i ≠ 0) (n : ℕ) :
    PowerSeries.coeff n (finiteEulerProductConnection s degree) =
      ∑ i ∈ s, if n ≠ 0 ∧ degree i ∣ n then -(degree i : ℤ) else 0 := by
  classical
  rw [finiteEulerProductConnection, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact coeff_finiteEulerFactorConnection (hdegree i hi)

/-- **FINITE CONNECTION COMPOSITION.**  A finite product of positive-degree
Euler factors carries the sum of the complete factor connections. -/
theorem hasEulerConnection_finsetProd_finiteEulerFactor
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (degree : ι → ℕ)
    (hdegree : ∀ i ∈ s, degree i ≠ 0) :
    Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareEulerReturn.HasEulerConnection
      (finiteEulerProductConnection s degree)
      (∏ i ∈ s, finiteEulerFactor (degree i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa [finiteEulerProductConnection] using hasEulerConnection_one
  | @insert i s hi ih =>
      have hfactor := hasEulerConnection_finiteEulerFactor
        (hdegree i (Finset.mem_insert_self i s))
      have htail := ih (fun j hj =>
        hdegree j (Finset.mem_insert_of_mem hj))
      have hmul := hfactor.mul htail
      simpa [finiteEulerProductConnection, hi] using hmul

/-- The exponent addressed by factor `i` of `qPoch (X^k) (X^k) N`. -/
def finiteEulerPochDegree (k i : ℕ) : ℕ :=
  k * (i + 1)

/-- The explicit sum of all factor connections in a finite Euler product. -/
def finiteEulerPochConnection (k N : ℕ) : PowerSeries ℤ :=
  finiteEulerProductConnection (Finset.range N) (finiteEulerPochDegree k)

/-- The finite scale-`k` connection counts exactly the admitted generator
degrees `k(i+1)` which divide the queried positive address. -/
theorem coeff_finiteEulerPochConnection
    (k N n : ℕ) (hk : k ≠ 0) :
    PowerSeries.coeff n (finiteEulerPochConnection k N) =
      ∑ i ∈ Finset.range N,
        if n ≠ 0 ∧ finiteEulerPochDegree k i ∣ n then
          -(finiteEulerPochDegree k i : ℤ) else 0 := by
  exact coeff_finiteEulerProductConnection (Finset.range N)
    (finiteEulerPochDegree k)
    (fun i _hi => by
      unfold finiteEulerPochDegree
      exact mul_ne_zero hk (Nat.succ_ne_zero i)) n

/-- Once the next generator degree lies beyond a positive queried address,
adding that generator cannot change the returned connection coefficient. -/
theorem coeff_finiteEulerPochConnection_succ_stable
    (k N n : ℕ) (hk : k ≠ 0) (hn : n ≠ 0)
    (hbelow : n < finiteEulerPochDegree k N) :
    PowerSeries.coeff n (finiteEulerPochConnection k (N + 1)) =
      PowerSeries.coeff n (finiteEulerPochConnection k N) := by
  have hdegree : finiteEulerPochDegree k N ≠ 0 := by
    unfold finiteEulerPochDegree
    exact mul_ne_zero hk (Nat.succ_ne_zero N)
  have hnotdiv : ¬ finiteEulerPochDegree k N ∣ n := by
    intro hdiv
    exact (not_le_of_gt hbelow)
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv)
  rw [finiteEulerPochConnection, finiteEulerProductConnection,
    Finset.sum_range_succ, map_add,
    coeff_finiteEulerFactorConnection hdegree]
  simp [hn, hnotdiv]
  rw [finiteEulerPochConnection, finiteEulerProductConnection, map_sum]

/-- Positive divisors are exactly the successor addresses in `range n` whose
generator reaches `n`.  This is the address equivalence beneath the ordinary
divisor current. -/
theorem ordinaryDivisorCurrent_eq_successorRange
    (n : ℕ) (hn : n ≠ 0) :
    ordinaryDivisorCurrent n =
      ∑ i ∈ Finset.range n,
        if i + 1 ∣ n then ((i + 1 : ℕ) : ℤ) else 0 := by
  rw [ordinaryDivisorCurrent]
  symm
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i _hi => i + 1)
  · intro i hi
    rw [Finset.mem_filter] at hi
    exact Nat.mem_divisors.mpr ⟨hi.2, hn⟩
  · intro a ha b hb hab
    omega
  · intro d hd
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
    refine ⟨d - 1, ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_range]
        omega
      · simpa [Nat.sub_add_cancel hdpos] using hdvd
    · omega
  · intro i hi
    rfl

/-- At a positive address, the stabilized scale-one finite connection is
exactly the negative ordinary divisor current. -/
theorem coeff_finiteEulerPochConnection_one_eq_neg_ordinary
    (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff n (finiteEulerPochConnection 1 n) =
      -ordinaryDivisorCurrent n := by
  rw [coeff_finiteEulerPochConnection 1 n n (by decide)]
  simp only [finiteEulerPochDegree, one_mul]
  rw [ordinaryDivisorCurrent_eq_successorRange n hn,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hdiv : i + 1 ∣ n
  · rw [if_pos ⟨hn, hdiv⟩, if_pos hdiv]
  · rw [if_neg (fun h => hdiv h.2), if_neg hdiv]
    simp

/-- At the exactly rebased positive address `k*m`, the finite scale-`k`
connection is `-k` times the ordinary divisor current at source address `m`.
This is the integral scale-current law used at scales `1`, `2`, and `4`. -/
theorem coeff_finiteEulerPochConnection_scale
    (k m : ℕ) (hk : k ≠ 0) (hm : m ≠ 0) :
    PowerSeries.coeff (k * m) (finiteEulerPochConnection k m) =
      -(k : ℤ) * ordinaryDivisorCurrent m := by
  rw [coeff_finiteEulerPochConnection k m (k * m) hk,
    ordinaryDivisorCurrent_eq_successorRange m hm,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hkm : k * m ≠ 0 := mul_ne_zero hk hm
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  by_cases hdiv : i + 1 ∣ m
  · have hscale : k * (i + 1) ∣ k * m :=
      (Nat.mul_dvd_mul_iff_left hkpos).mpr hdiv
    rw [if_pos ⟨hkm, hscale⟩, if_pos hdiv]
    rw [finiteEulerPochDegree]
    push_cast
    ring
  · have hscale : ¬ k * (i + 1) ∣ k * m := fun h =>
      hdiv ((Nat.mul_dvd_mul_iff_left hkpos).mp h)
    rw [if_neg (fun h => hscale h.2), if_neg hdiv]
    simp

/-- Every later finite aperture returns the same scale-`k` coefficient once
all possible generator degrees for source address `m` have entered. -/
theorem coeff_finiteEulerPochConnection_scale_stable
    (k m N : ℕ) (hk : k ≠ 0) (hm : m ≠ 0) (hMN : m ≤ N) :
    PowerSeries.coeff (k * m) (finiteEulerPochConnection k N) =
      -(k : ℤ) * ordinaryDivisorCurrent m := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hMN
  clear hMN
  induction r with
  | zero =>
      simpa using coeff_finiteEulerPochConnection_scale k m hk hm
  | succ r ih =>
      rw [show m + (r + 1) = (m + r) + 1 by omega]
      rw [coeff_finiteEulerPochConnection_succ_stable
        k (m + r) (k * m) hk (mul_ne_zero hk hm)]
      · exact ih
      · unfold finiteEulerPochDegree
        have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        nlinarith

/-- The stabilized logarithmic Euler connection at scale `k`.  Its zero
address is retained separately; a positive address receives `-k sigma(n/k)`
exactly when it lies in the scale image. -/
def eulerScaleConnection (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    if n = 0 then 0
    else if k ∣ n then -(k : ℤ) * ordinaryDivisorCurrent (n / k) else 0

@[simp] theorem coeff_eulerScaleConnection (k n : ℕ) :
    PowerSeries.coeff n (eulerScaleConnection k) =
      if n = 0 then 0
      else if k ∣ n then -(k : ℤ) * ordinaryDivisorCurrent (n / k) else 0 := by
  simp [eulerScaleConnection]

@[simp] theorem constantCoeff_eulerScaleConnection (k : ℕ) :
    PowerSeries.constantCoeff (eulerScaleConnection k) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp

/-- The quartic theta connection is exactly the oriented difference of the
scale-one, scale-two, and scale-four Euler currents. -/
theorem thetaQuarticConnection_eq_scaleDifference :
    thetaQuarticConnection =
      PowerSeries.C (20 : ℤ) * eulerScaleConnection 2 -
        PowerSeries.C (8 : ℤ) * eulerScaleConnection 1 -
        PowerSeries.C (8 : ℤ) * eulerScaleConnection 4 := by
  apply PowerSeries.ext
  intro n
  simp only [map_sub, PowerSeries.coeff_C_mul]
  by_cases hn : n = 0
  · subst n
    simp
  by_cases hfour : 4 ∣ n
  · have htwo : 2 ∣ n := dvd_trans (by norm_num) hfour
    simp [thetaQuarticConnectionCoeff, coeff_eulerScaleConnection,
      hn, htwo, hfour]
    ring
  · by_cases htwo : 2 ∣ n
    · simp [thetaQuarticConnectionCoeff, coeff_eulerScaleConnection,
        hn, htwo, hfour]
      ring
    · have hnotfour : ¬ 4 ∣ n := fun h => htwo (dvd_trans (by norm_num) h)
      simp [thetaQuarticConnectionCoeff, coeff_eulerScaleConnection,
        hn, htwo, hnotfour]

private theorem qPoch_X_pow_eq_finsetProd_finiteEulerFactor
    (k N : ℕ) :
    qPoch (PowerSeries.X ^ k) (PowerSeries.X ^ k) N =
      ∏ i ∈ Finset.range N, finiteEulerFactor (finiteEulerPochDegree k i) := by
  unfold qPoch
  apply Finset.prod_congr rfl
  intro i _hi
  unfold finiteEulerFactor finiteEulerPochDegree
  congr 1
  rw [← pow_mul, ← pow_add]
  congr 1
  calc
    k + k * i = k * i + k := Nat.add_comm _ _
    _ = k * (i + 1) := (Nat.mul_succ k i).symm

/-- **FINITE `q`-POCHHAMMER EULER CONNECTION.**  Every finite product at
scale `k > 0` carries the explicit sum of the connections of its addressed
factors. -/
theorem hasEulerConnection_qPoch_X_pow
    (k N : ℕ) (hk : k ≠ 0) :
    Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareEulerReturn.HasEulerConnection
      (finiteEulerPochConnection k N)
      (qPoch (PowerSeries.X ^ k) (PowerSeries.X ^ k) N) := by
  rw [qPoch_X_pow_eq_finsetProd_finiteEulerFactor]
  exact hasEulerConnection_finsetProd_finiteEulerFactor
    (Finset.range N) (finiteEulerPochDegree k) (fun i _hi => by
      unfold finiteEulerPochDegree
      exact mul_ne_zero hk (Nat.succ_ne_zero i))

#print axioms powerSeriesEulerCurrent_finiteEulerFactor
#print axioms finiteEulerFactor_mul_geometricFiber
#print axioms invOfUnit_finiteEulerFactor_eq_geometricFiber
#print axioms hasEulerConnection_finiteEulerFactor
#print axioms coeff_finiteEulerFactorConnection
#print axioms coeff_finiteEulerProductConnection
#print axioms coeff_finiteEulerPochConnection
#print axioms coeff_finiteEulerPochConnection_succ_stable
#print axioms ordinaryDivisorCurrent_eq_successorRange
#print axioms coeff_finiteEulerPochConnection_one_eq_neg_ordinary
#print axioms coeff_finiteEulerPochConnection_scale
#print axioms coeff_finiteEulerPochConnection_scale_stable
#print axioms thetaQuarticConnection_eq_scaleDifference
#print axioms hasEulerConnection_finsetProd_finiteEulerFactor
#print axioms hasEulerConnection_qPoch_X_pow

end Soma.Holonics.Millennium.FamilyTunnellJacobiFiniteEulerConnection
