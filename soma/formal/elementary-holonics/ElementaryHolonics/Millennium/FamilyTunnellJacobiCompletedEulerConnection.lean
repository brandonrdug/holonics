import ElementaryHolonics.Millennium.FamilyTunnellJacobiFiniteEulerConnection
import ElementaryHolonics.Millennium.FamilyTunnellJacobiGaussFactor
import ElementaryHolonics.Mathematics.JacobiEulerCubeStabilization

/-!
# Completed Euler connections for the Jacobi four-square source

This file passes the exact finite Euler connection through coefficient
stabilization to the actual completed `q`-Pochhammer body.  The proof is
coefficientwise and finite at every queried address.  It does not
differentiate an analytic limit or replace the retained product body by a
floating approximation.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiCompletedEulerConnection

open PowerSeries
open Soma.Holonics.Mathematics.JacobiTripleProductKernel
open Soma.Holonics.Mathematics.JacobiUnitSpecialization
open Soma.Holonics.Mathematics.JacobiEulerCubeStabilization
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareEulerReturn
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareLambert
open Soma.Holonics.Millennium.FamilyTunnellJacobiFiniteEulerConnection
open Soma.Holonics.Millennium.FamilyTunnellJacobiGaussFactor
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareSource
open Soma.Holonics.Millennium.FamilyTunnellJacobiQuarticProduct
open Soma.Holonics.Millennium.FamilyTunnellJacobiUnitThetaReceiver

open scoped PowerSeries.WithPiTopology

/-- The actual completed Euler body at integral scale `k`. -/
def completedEulerBody (k : ℕ) : PowerSeries ℤ :=
  qPochhammerInf (PowerSeries.X ^ k) (PowerSeries.X ^ k)

private theorem integerQpochSplit
    (A Q : PowerSeries ℤ) (n r : ℕ) :
    qPoch A Q (n + r) =
      qPoch A Q n * qPoch (A * Q ^ n) Q r := by
  rw [qPoch, qPoch, qPoch, Finset.prod_range_add]
  simp [pow_add, mul_assoc]

private theorem coeffMulOfTruncOne
    (f g : PowerSeries ℤ) (m : ℕ)
    (hg : ∀ j ≤ m, PowerSeries.coeff j g = if j = 0 then 1 else 0) :
    PowerSeries.coeff m (f * g) = PowerSeries.coeff m f := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.sum_eq_single_of_mem (m, 0)
    (Finset.mem_antidiagonal.mpr (add_zero m))]
  · simp [hg 0 (Nat.zero_le m)]
  · intro b hb hne
    have hbSum := Finset.mem_antidiagonal.mp hb
    rw [hg b.2 (by omega), if_neg]
    · simp
    · intro hb0
      apply hne
      ext <;> simp_all

private theorem prodCoeffDelta
    (m : ℕ) (f : ℕ → PowerSeries ℤ) (r : ℕ)
    (hf : ∀ i < r, ∀ j ≤ m,
      PowerSeries.coeff j (f i) = if j = 0 then 1 else 0)
    (j : ℕ) (hj : j ≤ m) :
    PowerSeries.coeff j (∏ i ∈ Finset.range r, f i) =
      if j = 0 then 1 else 0 := by
  induction r with
  | zero => simp [PowerSeries.coeff_one]
  | succ r ih =>
      rw [Finset.prod_range_succ,
        coeffMulOfTruncOne _ _ j
          (fun j' hj' => hf r (Nat.lt_succ_self r) j' (le_trans hj' hj))]
      exact ih (fun i hi j' hj' => hf i (Nat.lt_succ_of_lt hi) j' hj')

private theorem scaleTailFactorDelta
    (k m N i j : ℕ) (hk : k ≠ 0)
    (hbelow : m < k * (N + 1)) (hj : j ≤ m) :
    PowerSeries.coeff j
        (1 - ((PowerSeries.X ^ k : PowerSeries ℤ) *
            (PowerSeries.X ^ k) ^ N) *
          (PowerSeries.X ^ k) ^ i) =
      if j = 0 then 1 else 0 := by
  have hpow :
      ((PowerSeries.X ^ k : PowerSeries ℤ) *
          (PowerSeries.X ^ k) ^ N) * (PowerSeries.X ^ k) ^ i =
        PowerSeries.X ^ (k * (N + i + 1)) := by
    rw [← pow_mul, ← pow_mul]
    rw [show k * (N + i + 1) = k + k * N + k * i by ring,
      pow_add, pow_add]
  rw [hpow]
  simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  have hdegree : m < k * (N + i + 1) := by
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    nlinarith
  split_ifs <;> omega

private theorem scaleTailCoeffDelta
    (k m N r j : ℕ) (hk : k ≠ 0)
    (hbelow : m < k * (N + 1)) (hj : j ≤ m) :
    PowerSeries.coeff j
        (qPoch ((PowerSeries.X ^ k : PowerSeries ℤ) *
          (PowerSeries.X ^ k) ^ N) (PowerSeries.X ^ k) r) =
      if j = 0 then 1 else 0 := by
  unfold qPoch
  exact prodCoeffDelta m
    (fun i => 1 - ((PowerSeries.X ^ k : PowerSeries ℤ) *
      (PowerSeries.X ^ k) ^ N) * (PowerSeries.X ^ k) ^ i) r
    (fun i _hi j hj => scaleTailFactorDelta k m N i j hk hbelow hj) j hj

private theorem scalePartialProdsCoeffStable
    (k m N N' : ℕ) (hk : k ≠ 0)
    (hbelow : m < k * (N + 1)) (hNN' : N ≤ N') :
    PowerSeries.coeff m
        (qPoch (PowerSeries.X ^ k : PowerSeries ℤ)
          (PowerSeries.X ^ k) N') =
      PowerSeries.coeff m
        (qPoch (PowerSeries.X ^ k : PowerSeries ℤ)
          (PowerSeries.X ^ k) N) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hNN'
  rw [integerQpochSplit]
  exact coeffMulOfTruncOne _ _ m
    (scaleTailCoeffDelta k m N r · hk hbelow)

private theorem scaleFactorsMultipliable (k : ℕ) (hk : k ≠ 0) :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    Multipliable (fun n =>
      1 - (PowerSeries.X ^ k : PowerSeries ℤ) *
        (PowerSeries.X ^ k) ^ n) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  rw [show (fun n =>
      1 - (PowerSeries.X ^ k : PowerSeries ℤ) *
        (PowerSeries.X ^ k) ^ n) =
      (fun n => 1 + (-(PowerSeries.X ^ (k * (n + 1))) : PowerSeries ℤ)) by
        funext n
        rw [show (PowerSeries.X ^ k : PowerSeries ℤ) *
            (PowerSeries.X ^ k) ^ n =
            PowerSeries.X ^ (k * (n + 1)) by
          rw [← pow_mul]
          rw [show k * (n + 1) = k + k * n by ring, pow_add]]
        ring]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  simp_rw [PowerSeries.order_neg, PowerSeries.order_X_pow]
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro d
  filter_upwards [Filter.eventually_ge_atTop (d + 1)] with n hn
  exact ENat.coe_lt_coe.mpr (by
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    nlinarith)

/-- **EXACT COMPLETION STABILIZATION.**  Below the first omitted generator,
the completed scale-`k` Euler body and its finite aperture have identical
coefficients. -/
theorem coeff_completedEulerBody_eq_finite
    (k d N : ℕ) (hk : k ≠ 0) (hbelow : d < k * (N + 1)) :
    PowerSeries.coeff d (completedEulerBody k) =
      PowerSeries.coeff d
        (qPoch (PowerSeries.X ^ k : PowerSeries ℤ)
          (PowerSeries.X ^ k) N) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  rw [completedEulerBody,
    integer_qPochhammerInf_eq_tprod _ _ (scaleFactorsMultipliable k hk)]
  exact tendsto_nhds_unique
    ((PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto
      ℤ _ _ _).mp (scaleFactorsMultipliable k hk).tendsto_prod_tprod_nat d)
    (tendsto_atTop_of_eventually_const (i₀ := N) (fun N' hNN' =>
      scalePartialProdsCoeffStable k d N N' hk hbelow hNN'))

private theorem monomialTailFactorDelta
    (a b m N i j : ℕ) (hb : b ≠ 0)
    (hbelow : m < a + b * N) (hj : j ≤ m) :
    PowerSeries.coeff j
        (1 - ((PowerSeries.X ^ a : PowerSeries ℤ) *
            (PowerSeries.X ^ b) ^ N) *
          (PowerSeries.X ^ b) ^ i) =
      if j = 0 then 1 else 0 := by
  have hpow :
      ((PowerSeries.X ^ a : PowerSeries ℤ) *
          (PowerSeries.X ^ b) ^ N) * (PowerSeries.X ^ b) ^ i =
        PowerSeries.X ^ (a + b * (N + i)) := by
    rw [← pow_mul, ← pow_mul]
    rw [show a + b * (N + i) = a + b * N + b * i by ring,
      pow_add, pow_add]
  rw [hpow]
  simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  have hdegree : m < a + b * (N + i) := by
    have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    nlinarith
  split_ifs <;> omega

private theorem monomialTailCoeffDelta
    (a b m N r j : ℕ) (hb : b ≠ 0)
    (hbelow : m < a + b * N) (hj : j ≤ m) :
    PowerSeries.coeff j
        (qPoch ((PowerSeries.X ^ a : PowerSeries ℤ) *
          (PowerSeries.X ^ b) ^ N) (PowerSeries.X ^ b) r) =
      if j = 0 then 1 else 0 := by
  unfold qPoch
  exact prodCoeffDelta m
    (fun i => 1 - ((PowerSeries.X ^ a : PowerSeries ℤ) *
      (PowerSeries.X ^ b) ^ N) * (PowerSeries.X ^ b) ^ i) r
    (fun i _hi j hj => monomialTailFactorDelta a b m N i j hb hbelow hj) j hj

private theorem monomialPartialProdsCoeffStable
    (a b m N N' : ℕ) (hb : b ≠ 0)
    (hbelow : m < a + b * N) (hNN' : N ≤ N') :
    PowerSeries.coeff m
        (qPoch (PowerSeries.X ^ a : PowerSeries ℤ)
          (PowerSeries.X ^ b) N') =
      PowerSeries.coeff m
        (qPoch (PowerSeries.X ^ a : PowerSeries ℤ)
          (PowerSeries.X ^ b) N) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hNN'
  rw [integerQpochSplit]
  exact coeffMulOfTruncOne _ _ m
    (monomialTailCoeffDelta a b m N r · hb hbelow)

private theorem monomialFactorsMultipliable
    (a b : ℕ) (hb : b ≠ 0) :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    Multipliable (fun n =>
      1 - (PowerSeries.X ^ a : PowerSeries ℤ) *
        (PowerSeries.X ^ b) ^ n) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  rw [show (fun n =>
      1 - (PowerSeries.X ^ a : PowerSeries ℤ) *
        (PowerSeries.X ^ b) ^ n) =
      (fun n => 1 + (-(PowerSeries.X ^ (a + b * n)) : PowerSeries ℤ)) by
        funext n
        rw [show (PowerSeries.X ^ a : PowerSeries ℤ) *
            (PowerSeries.X ^ b) ^ n =
            PowerSeries.X ^ (a + b * n) by
          rw [← pow_mul, pow_add]]
        ring]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  simp_rw [PowerSeries.order_neg, PowerSeries.order_X_pow]
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro d
  filter_upwards [Filter.eventually_ge_atTop (d + 1)] with n hn
  exact ENat.coe_lt_coe.mpr (by
    have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    nlinarith)

/-- A completed monomial `q`-Pochhammer body is coefficientwise finite below
its first omitted factor.  The start address and step address remain distinct
typed parameters. -/
theorem coeff_qPochhammerInf_X_pow_eq_finite
    (a b d N : ℕ) (hb : b ≠ 0) (hbelow : d < a + b * N) :
    PowerSeries.coeff d
        (qPochhammerInf (PowerSeries.X ^ a : PowerSeries ℤ)
          (PowerSeries.X ^ b)) =
      PowerSeries.coeff d
        (qPoch (PowerSeries.X ^ a : PowerSeries ℤ)
          (PowerSeries.X ^ b) N) := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  rw [integer_qPochhammerInf_eq_tprod _ _
    (monomialFactorsMultipliable a b hb)]
  exact tendsto_nhds_unique
    ((PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto
      ℤ _ _ _).mp (monomialFactorsMultipliable a b hb).tendsto_prod_tprod_nat d)
    (tendsto_atTop_of_eventually_const (i₀ := N) (fun N' hNN' =>
      monomialPartialProdsCoeffStable a b d N N' hb hbelow hNN'))

/-- The completed odd-multiple Euler population at scale `k`. -/
def completedOddEulerBody (k : ℕ) : PowerSeries ℤ :=
  qPochhammerInf (PowerSeries.X ^ k) (PowerSeries.X ^ (2 * k))

/-- Finite odd/even partition of a scale-`k` Euler population. -/
theorem finiteEulerParitySplit (k N : ℕ) :
    qPoch (PowerSeries.X ^ k : PowerSeries ℤ)
        (PowerSeries.X ^ k) (2 * N) =
      qPoch (PowerSeries.X ^ k : PowerSeries ℤ)
          (PowerSeries.X ^ (2 * k)) N *
        qPoch (PowerSeries.X ^ (2 * k) : PowerSeries ℤ)
          (PowerSeries.X ^ (2 * k)) N := by
  induction N with
  | zero => simp [qPoch]
  | succ N ih =>
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
        qPoch_succ', qPoch_succ',
        qPoch_succ' (PowerSeries.X ^ k)
          (PowerSeries.X ^ (2 * k)) N,
        qPoch_succ' (PowerSeries.X ^ (2 * k))
          (PowerSeries.X ^ (2 * k)) N,
        ih]
      have hodd :
          (PowerSeries.X ^ k : PowerSeries ℤ) *
              (PowerSeries.X ^ k) ^ (2 * N) =
            PowerSeries.X ^ (k * (2 * N + 1)) := by
        rw [← pow_mul]
        rw [show k * (2 * N + 1) = k + k * (2 * N) by ring, pow_add]
      have heven :
          (PowerSeries.X ^ k : PowerSeries ℤ) *
              (PowerSeries.X ^ k) ^ (2 * N + 1) =
            PowerSeries.X ^ (2 * k * (N + 1)) := by
        rw [← pow_mul]
        rw [show 2 * k * (N + 1) = k + k * (2 * N + 1) by ring,
          pow_add]
      have hoddTarget :
          (PowerSeries.X ^ k : PowerSeries ℤ) *
              (PowerSeries.X ^ (2 * k)) ^ N =
            PowerSeries.X ^ (k * (2 * N + 1)) := by
        rw [← pow_mul]
        rw [show k * (2 * N + 1) = k + (2 * k) * N by ring, pow_add]
      have hevenTarget :
          (PowerSeries.X ^ (2 * k) : PowerSeries ℤ) *
              (PowerSeries.X ^ (2 * k)) ^ N =
            PowerSeries.X ^ (2 * k * (N + 1)) := by
        rw [← pow_mul]
        rw [show 2 * k * (N + 1) = 2 * k + (2 * k) * N by ring,
          pow_add]
      rw [hodd, heven, hoddTarget, hevenTarget]
      ring

/-- **COMPLETED PARITY GLUING.**  The complete Euler population splits into
its odd and even generator subpopulations with all coefficients and the
completion aperture preserved. -/
theorem completedEulerBody_paritySplit
    (k : ℕ) (hk : k ≠ 0) :
    completedEulerBody k =
      completedOddEulerBody k * completedEulerBody (2 * k) := by
  apply PowerSeries.ext
  intro d
  let N := d + 1
  have hb : 2 * k ≠ 0 := mul_ne_zero (by decide) hk
  have hAll : d < k * (2 * N + 1) := by
    dsimp [N]
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    nlinarith
  have hOdd (j : ℕ) (hj : j ≤ d) :
      PowerSeries.coeff j (completedOddEulerBody k) =
        PowerSeries.coeff j
          (qPoch (PowerSeries.X ^ k : PowerSeries ℤ)
            (PowerSeries.X ^ (2 * k)) N) := by
    unfold completedOddEulerBody
    apply coeff_qPochhammerInf_X_pow_eq_finite k (2 * k) j N hb
    dsimp [N]
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    nlinarith
  have hEven (j : ℕ) (hj : j ≤ d) :
      PowerSeries.coeff j (completedEulerBody (2 * k)) =
        PowerSeries.coeff j
          (qPoch (PowerSeries.X ^ (2 * k) : PowerSeries ℤ)
            (PowerSeries.X ^ (2 * k)) N) := by
    apply coeff_completedEulerBody_eq_finite (2 * k) j N hb
    dsimp [N]
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    nlinarith
  calc
    PowerSeries.coeff d (completedEulerBody k) =
        PowerSeries.coeff d
          (qPoch (PowerSeries.X ^ k : PowerSeries ℤ)
            (PowerSeries.X ^ k) (2 * N)) :=
      coeff_completedEulerBody_eq_finite k d (2 * N) hk hAll
    _ = PowerSeries.coeff d
        (qPoch (PowerSeries.X ^ k : PowerSeries ℤ)
            (PowerSeries.X ^ (2 * k)) N *
          qPoch (PowerSeries.X ^ (2 * k) : PowerSeries ℤ)
            (PowerSeries.X ^ (2 * k)) N) := by
      rw [finiteEulerParitySplit]
    _ = PowerSeries.coeff d
        (completedOddEulerBody k * completedEulerBody (2 * k)) := by
      exact coeff_mul_eq_of_coeff_le _ _ _ _ d
        (fun j hj => (hOdd j hj).symm)
        (fun j hj => (hEven j hj).symm)

@[simp] theorem constantCoeff_completedEulerBody
    (k : ℕ) (hk : k ≠ 0) :
    PowerSeries.constantCoeff (completedEulerBody k) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,
    coeff_completedEulerBody_eq_finite k 0 0 hk]
  · simp [qPoch]
  · simpa using Nat.pos_of_ne_zero hk

/-- The stabilized connection and the finite aperture connection have the
same coefficient at every address below the first omitted generator. -/
theorem coeff_eulerScaleConnection_eq_finite
    (k n N : ℕ) (hk : k ≠ 0) (hbelow : n < k * (N + 1)) :
    PowerSeries.coeff n (eulerScaleConnection k) =
      PowerSeries.coeff n (finiteEulerPochConnection k N) := by
  by_cases hn : n = 0
  · subst n
    rw [coeff_eulerScaleConnection,
      coeff_finiteEulerPochConnection k N 0 hk]
    simp
  by_cases hdiv : k ∣ n
  · have hkm : k * (n / k) = n := Nat.mul_div_cancel' hdiv
    have hm : n / k ≠ 0 := by
      intro hm0
      apply hn
      rw [← hkm, hm0, mul_zero]
    have hMN : n / k ≤ N := by
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      by_contra hnot
      have hNlt : N < n / k := Nat.lt_of_not_ge hnot
      have hfactor : k * (N + 1) ≤ k * (n / k) := by
        exact Nat.mul_le_mul_left k (by omega)
      rw [hkm] at hfactor
      omega
    have hs := coeff_finiteEulerPochConnection_scale_stable
      k (n / k) N hk hm hMN
    rw [hkm] at hs
    rw [coeff_eulerScaleConnection, if_neg hn, if_pos hdiv]
    exact hs.symm
  · rw [coeff_eulerScaleConnection, if_neg hn, if_neg hdiv,
      coeff_finiteEulerPochConnection k N n hk]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg]
    intro hmeet
    apply hdiv
    exact dvd_trans ⟨i + 1, by simp [finiteEulerPochDegree]⟩ hmeet.2

/-- **COMPLETED CONSTITUTIVE LAW.**  The actual completed scale-`k` Euler
product carries the exact divisor connection `L_k`.  Every coefficient proof
passes through a sufficient finite aperture and retains both the product
body and its reconstruction fibre. -/
theorem hasEulerConnection_completedEulerBody
    (k : ℕ) (hk : k ≠ 0) :
    HasEulerConnection (eulerScaleConnection k) (completedEulerBody k) := by
  rw [HasEulerConnection]
  apply PowerSeries.ext
  intro n
  let N := n + 1
  let finiteBody : PowerSeries ℤ :=
    qPoch (PowerSeries.X ^ k) (PowerSeries.X ^ k) N
  have hbelow (j : ℕ) (hj : j ≤ n) : j < k * (N + 1) := by
    dsimp [N]
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    nlinarith
  have hbody (j : ℕ) (hj : j ≤ n) :
      PowerSeries.coeff j (completedEulerBody k) =
        PowerSeries.coeff j finiteBody := by
    exact coeff_completedEulerBody_eq_finite k j N hk (hbelow j hj)
  have hconnection (j : ℕ) (hj : j ≤ n) :
      PowerSeries.coeff j (eulerScaleConnection k) =
        PowerSeries.coeff j (finiteEulerPochConnection k N) := by
    exact coeff_eulerScaleConnection_eq_finite k j N hk (hbelow j hj)
  have hfinite := hasEulerConnection_qPoch_X_pow k N hk
  rw [HasEulerConnection] at hfinite
  calc
    PowerSeries.coeff n (powerSeriesEulerCurrent (completedEulerBody k)) =
        (n : ℤ) * PowerSeries.coeff n (completedEulerBody k) :=
      coeff_powerSeriesEulerCurrent _ _
    _ = (n : ℤ) * PowerSeries.coeff n finiteBody := by
      rw [hbody n le_rfl]
    _ = PowerSeries.coeff n (powerSeriesEulerCurrent finiteBody) := by
      rw [coeff_powerSeriesEulerCurrent]
    _ = PowerSeries.coeff n
        (finiteEulerPochConnection k N * finiteBody) := by
      rw [hfinite]
    _ = PowerSeries.coeff n
        (eulerScaleConnection k * completedEulerBody k) := by
      exact coeff_mul_eq_of_coeff_le _ _ _ _ n
        (fun j hj => (hconnection j hj).symm)
        (fun j hj => (hbody j hj).symm)

/-- The positive odd unit-orientation product occurring in Jacobi's
positive square-theta face. -/
def completedPositiveOddEulerBody : PowerSeries ℤ :=
  qPochhammerInf (-(PowerSeries.X : PowerSeries ℤ))
    (PowerSeries.X ^ 2)

/-- A completed positive-scale Euler body is nonzero because its retained
origin occurrence is exactly one. -/
theorem completedEulerBody_ne_zero (k : ℕ) (hk : k ≠ 0) :
    completedEulerBody k ≠ 0 := by
  intro hzero
  have hconstant := congrArg PowerSeries.constantCoeff hzero
  rw [constantCoeff_completedEulerBody k hk] at hconstant
  simp at hconstant

/-- **ETA CROSSING WITHOUT DIVISION.**  The positive odd Jacobi body crosses
the scale-one and scale-four Euler populations to the square of the
scale-two population.  This is the exact parity-gluing identity beneath the
usual eta quotient; no quotient has been installed. -/
theorem completedPositiveOddEulerBody_etaCross :
    completedPositiveOddEulerBody *
        (completedEulerBody 1 * completedEulerBody 4) =
      completedEulerBody 2 ^ 2 := by
  letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
  have h1 := completedEulerBody_paritySplit 1 (by decide)
  have h2 := completedEulerBody_paritySplit 2 (by decide)
  have hpair : completedPositiveOddEulerBody * completedOddEulerBody 1 =
      completedOddEulerBody 2 := by
    simpa [completedPositiveOddEulerBody, completedOddEulerBody] using
      positiveNegativeUnitPochhammer_pair
  calc
    completedPositiveOddEulerBody *
          (completedEulerBody 1 * completedEulerBody 4) =
        completedPositiveOddEulerBody *
          ((completedOddEulerBody 1 * completedEulerBody 2) *
            completedEulerBody 4) := by rw [h1]
    _ = (completedPositiveOddEulerBody * completedOddEulerBody 1) *
          (completedEulerBody 2 * completedEulerBody 4) := by ring
    _ = completedOddEulerBody 2 *
          (completedEulerBody 2 * completedEulerBody 4) := by rw [hpair]
    _ = (completedOddEulerBody 2 * completedEulerBody 4) *
          completedEulerBody 2 := by ring
    _ = completedEulerBody 2 * completedEulerBody 2 := by rw [← h2]
    _ = completedEulerBody 2 ^ 2 := by rw [pow_two]

/-- The positive-unit square theta is the scale-two Euler body times two
copies of the positive odd orientation body. -/
theorem unitSquareTheta_one_eq_completedEulerProduct :
    unitSquareTheta (1 : ℤˣ) =
      completedEulerBody 2 * completedPositiveOddEulerBody ^ 2 := by
  have h := jacobi_unit_product_eq_unitSquareTheta (1 : ℤˣ)
  norm_num at h
  change completedEulerBody 2 * completedPositiveOddEulerBody *
      completedPositiveOddEulerBody = unitSquareTheta (1 : ℤˣ) at h
  rw [← h, pow_two]
  ring

/-- The exact cross-multiplied eta form of Jacobi's positive square theta.
All product bodies remain present, so this identity can be differentiated
and cancelled by the constitutive connection law without a decoder. -/
theorem unitSquareTheta_one_etaCross :
    unitSquareTheta (1 : ℤˣ) *
        (completedEulerBody 1 ^ 2 * completedEulerBody 4 ^ 2) =
      completedEulerBody 2 ^ 5 := by
  rw [unitSquareTheta_one_eq_completedEulerProduct]
  have heta := completedPositiveOddEulerBody_etaCross
  calc
    (completedEulerBody 2 * completedPositiveOddEulerBody ^ 2) *
          (completedEulerBody 1 ^ 2 * completedEulerBody 4 ^ 2) =
        completedEulerBody 2 *
          (completedPositiveOddEulerBody *
            (completedEulerBody 1 * completedEulerBody 4)) ^ 2 := by ring
    _ = completedEulerBody 2 * (completedEulerBody 2 ^ 2) ^ 2 := by
      rw [heta]
    _ = completedEulerBody 2 ^ 5 := by ring

/-- The connection of one positive-unit square-theta body before the fourth
power is taken. -/
def thetaUnitConnection : PowerSeries ℤ :=
  (5 : ℤ) • eulerScaleConnection 2 -
    (2 : ℤ) • eulerScaleConnection 1 -
    (2 : ℤ) • eulerScaleConnection 4

/-- The retained positive odd orientation body has the exact connection
obtained by subtracting the scale-one and scale-four return from twice the
scale-two return. -/
theorem hasEulerConnection_completedPositiveOddEulerBody :
    HasEulerConnection
      ((2 : ℤ) • eulerScaleConnection 2 -
        (eulerScaleConnection 1 + eulerScaleConnection 4))
      completedPositiveOddEulerBody := by
  have h1 := hasEulerConnection_completedEulerBody 1 (by decide)
  have h2 := hasEulerConnection_completedEulerBody 2 (by decide)
  have h4 := hasEulerConnection_completedEulerBody 4 (by decide)
  have hright := h1.mul h4
  have htotal :
      HasEulerConnection ((2 : ℤ) • eulerScaleConnection 2)
        (completedPositiveOddEulerBody *
          (completedEulerBody 1 * completedEulerBody 4)) := by
    rw [completedPositiveOddEulerBody_etaCross]
    exact h2.pow 2
  have hrightNe : completedEulerBody 1 * completedEulerBody 4 ≠ 0 :=
    mul_ne_zero (completedEulerBody_ne_zero 1 (by decide))
      (completedEulerBody_ne_zero 4 (by decide))
  exact htotal.of_mul_right hright hrightNe

/-- The positive-unit square-theta body carries the exact three-scale
connection before repetition. -/
theorem hasEulerConnection_unitSquareTheta_one :
    HasEulerConnection thetaUnitConnection (unitSquareTheta (1 : ℤˣ)) := by
  have h2 := hasEulerConnection_completedEulerBody 2 (by decide)
  have hP := hasEulerConnection_completedPositiveOddEulerBody
  have hproduct := h2.mul (hP.pow 2)
  rw [unitSquareTheta_one_eq_completedEulerProduct]
  have hconnection :
      eulerScaleConnection 2 +
          (2 : ℤ) • ((2 : ℤ) • eulerScaleConnection 2 -
            (eulerScaleConnection 1 + eulerScaleConnection 4)) =
        thetaUnitConnection := by
    unfold thetaUnitConnection
    module
  rw [← hconnection]
  exact hproduct

/-- **JACOBI THETA-PRODUCT EULER LAW.**  The complete four-square theta
source carries exactly the quartic divisor connection already constructed
from the Lambert receiver.  This closes the theta-product half of the
remaining differentiated four-square passage. -/
theorem hasEulerConnection_fullFourSquareTheta :
    HasEulerConnection thetaQuarticConnection fullFourSquareTheta := by
  have hpow := hasEulerConnection_unitSquareTheta_one.pow 4
  have hconnection :
      (4 : ℤ) • thetaUnitConnection = thetaQuarticConnection := by
    rw [thetaQuarticConnection_eq_scaleDifference]
    unfold thetaUnitConnection
    apply PowerSeries.ext
    intro n
    simp only [map_smul, map_sub, PowerSeries.coeff_C_mul]
    ring
  rw [← hconnection]
  exact hpow

/-- With the theta-product law discharged, the declared divisor recurrence
alone reconstructs the complete Jacobi four-square identity. -/
theorem fullFourSquareTheta_eq_completedLambert_of_divisorRecurrence
    (hrecurrence : JacobiDivisorConnectionRecurrence) :
    fullFourSquareTheta = completedJacobiFourSquareLambertSeries := by
  exact fullFourSquareTheta_eq_completedLambert_of_commonEulerConnection
    hasEulerConnection_fullFourSquareTheta hrecurrence

/-- The same sole recurrence returns the complete positive ordered-shell
divisor family. -/
theorem totalShellDivisorLaw_of_divisorRecurrence
    (hrecurrence : JacobiDivisorConnectionRecurrence) :
    ∀ n : ℕ, 0 < n →
      ((totalFourSquareShell n).card : ℤ) = 8 * jacobiDivisorCurrent n := by
  exact totalShellDivisorLaw_of_commonEulerConnection
    hasEulerConnection_fullFourSquareTheta hrecurrence

#print axioms coeff_completedEulerBody_eq_finite
#print axioms completedEulerBody_paritySplit
#print axioms coeff_eulerScaleConnection_eq_finite
#print axioms hasEulerConnection_completedEulerBody
#print axioms completedPositiveOddEulerBody_etaCross
#print axioms unitSquareTheta_one_etaCross
#print axioms hasEulerConnection_completedPositiveOddEulerBody
#print axioms hasEulerConnection_unitSquareTheta_one
#print axioms hasEulerConnection_fullFourSquareTheta
#print axioms fullFourSquareTheta_eq_completedLambert_of_divisorRecurrence
#print axioms totalShellDivisorLaw_of_divisorRecurrence

end Soma.Holonics.Millennium.FamilyTunnellJacobiCompletedEulerConnection
