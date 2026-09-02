import ElementaryHolonics.Millennium.FamilyTunnellJacobiQuarticProduct
import ElementaryHolonics.Mathematics.PowerSeriesExactDilation
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Euler-current reconstruction for the Jacobi four-square passage

The source and completed Lambert receiver have now been based at the same
constant occurrence.  This file isolates the exact local-to-global law needed
by a differentiated product proof: the addressed Euler current multiplies the
coefficient at address `n` by that address, obeys Leibniz, and together with
the constant face reconstructs the complete power series.

This is not the four-square identity itself.  It changes the remaining target
from equality of two infinite objects to equality of their transported Euler
currents.  No coefficient may be rounded or discarded.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareEulerReturn

open PowerSeries
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareLambert
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareSource
open Soma.Holonics.Millennium.FamilyTunnellJacobiQuarticProduct
open Soma.Holonics.Mathematics.PowerSeriesExactDilation

/-- The outer Euler current `X d/dX`.  The factor `X` returns differentiation
to the coefficient's original address instead of shifting every occurrence
down by one. -/
def powerSeriesEulerCurrent {R : Type*} [CommRing R]
    (F : PowerSeries R) : PowerSeries R :=
  PowerSeries.X * (PowerSeries.derivative R) F

/-- The origin carries no Euler current.  It must therefore be retained as a
separate reconstruction face. -/
@[simp] theorem coeff_powerSeriesEulerCurrent_zero
    {R : Type*} [CommRing R] (F : PowerSeries R) :
    PowerSeries.coeff 0 (powerSeriesEulerCurrent F) = 0 := by
  simp [powerSeriesEulerCurrent, PowerSeries.coeff_mul]

/-- At every successor address the Euler current is exactly the address
multiplied by the coefficient stored there. -/
theorem coeff_powerSeriesEulerCurrent_succ
    {R : Type*} [CommRing R] (F : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff (n + 1) (powerSeriesEulerCurrent F) =
      PowerSeries.coeff (n + 1) F * ((n + 1 : ℕ) : R) := by
  rw [powerSeriesEulerCurrent, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_derivative]
  simp only [Nat.cast_add, Nat.cast_one]

/-- The all-address form: Euler transport multiplies each occurrence by its exact natural
address. -/
@[simp] theorem coeff_powerSeriesEulerCurrent
    {R : Type*} [CommRing R] (F : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (powerSeriesEulerCurrent F) =
      ((n : ℕ) : R) * PowerSeries.coeff n F := by
  cases n with
  | zero => simp
  | succ n =>
      rw [coeff_powerSeriesEulerCurrent_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- Euler transport preserves the exact product decomposition. -/
theorem powerSeriesEulerCurrent_mul
    {R : Type*} [CommRing R] (F G : PowerSeries R) :
    powerSeriesEulerCurrent (F * G) =
      F * powerSeriesEulerCurrent G + G * powerSeriesEulerCurrent F := by
  unfold powerSeriesEulerCurrent
  change PowerSeries.X * PowerSeries.derivativeFun (F * G) =
    F * (PowerSeries.X * PowerSeries.derivativeFun G) +
      G * (PowerSeries.X * PowerSeries.derivativeFun F)
  rw [PowerSeries.derivativeFun_mul]
  simp only [smul_eq_mul]
  ring

/-- Outer Euler transport is covariant under the exact scale chart `X ↦ X^k`; the scale itself is
returned as an exact integer multiplier. -/
theorem powerSeriesEulerCurrent_exactDilate
    (k : ℕ) (hk : k ≠ 0) (F : PowerSeries ℤ) :
    powerSeriesEulerCurrent (exactDilate k hk F) =
      (k : ℤ) • exactDilate k hk (powerSeriesEulerCurrent F) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_powerSeriesEulerCurrent, coeff_exactDilate]
  simp only [PowerSeries.coeff_smul, map_zsmul, map_smul, smul_eq_mul, coeff_exactDilate]
  by_cases hdiv : k ∣ n
  · rw [if_pos hdiv, if_pos hdiv]
    obtain ⟨j, rfl⟩ := hdiv
    rw [coeff_powerSeriesEulerCurrent,
      Nat.mul_div_cancel_left j (Nat.pos_of_ne_zero hk)]
    simp only [Nat.cast_mul]
    ring
  · rw [if_neg hdiv, if_neg hdiv]
    simp

/-- A constitutive Euler connection records the current produced by a series without dividing by
the series or deleting its constant/reconstruction face. -/
def HasEulerConnection (connection body : PowerSeries ℤ) : Prop :=
  powerSeriesEulerCurrent body = connection * body

/-- The unit body carries the zero Euler connection. -/
theorem hasEulerConnection_one :
    HasEulerConnection 0 (1 : PowerSeries ℤ) := by
  simp [HasEulerConnection, powerSeriesEulerCurrent]

/-- Independent product bodies add their Euler connections.  The theorem keeps the bodies
themselves, so it does not require a quotient or an inverse-series receiver. -/
theorem HasEulerConnection.mul
    {connectionF connectionG F G : PowerSeries ℤ}
    (hF : HasEulerConnection connectionF F)
    (hG : HasEulerConnection connectionG G) :
    HasEulerConnection (connectionF + connectionG) (F * G) := by
  rw [HasEulerConnection, powerSeriesEulerCurrent_mul, hF, hG]
  ring

/-- Repetition of one body scales its Euler connection by the exact repetition population. -/
theorem HasEulerConnection.pow
    {connection F : PowerSeries ℤ}
    (hF : HasEulerConnection connection F) (r : ℕ) :
    HasEulerConnection ((r : ℤ) • connection) (F ^ r) := by
  induction r with
  | zero => simpa using hasEulerConnection_one
  | succ r ih =>
      rw [pow_succ]
      have hmul := ih.mul hF
      simpa [Nat.cast_add, add_smul] using hmul

/-- Exact source dilation transports a constitutive connection and returns the acting scale as an
explicit multiplier. -/
theorem HasEulerConnection.exactDilate
    {connection F : PowerSeries ℤ}
    (hF : HasEulerConnection connection F)
    (k : ℕ) (hk : k ≠ 0) :
    HasEulerConnection
      ((k : ℤ) • exactDilate k hk connection)
      (exactDilate k hk F) := by
  rw [HasEulerConnection, powerSeriesEulerCurrent_exactDilate, hF,
    exactDilate_mul]
  simp only [smul_mul_assoc]

/-- If a product connection and the right-factor connection are known, a nonzero right body
returns the left connection as their exact oriented difference.  This is the cancellation passage
needed for cross-multiplied Euler products; no inverse series is installed as a decoder. -/
theorem HasEulerConnection.of_mul_right
    {totalConnection rightConnection F G : PowerSeries ℤ}
    (hFG : HasEulerConnection totalConnection (F * G))
    (hG : HasEulerConnection rightConnection G)
    (hGne : G ≠ 0) :
    HasEulerConnection (totalConnection - rightConnection) F := by
  rw [HasEulerConnection]
  apply mul_left_cancel₀ hGne
  calc
    G * powerSeriesEulerCurrent F =
        powerSeriesEulerCurrent (F * G) - F * powerSeriesEulerCurrent G := by
      rw [powerSeriesEulerCurrent_mul]
      ring
    _ = totalConnection * (F * G) - F * (rightConnection * G) := by
      rw [hFG, hG]
    _ = G * ((totalConnection - rightConnection) * F) := by ring

/-- The constant face plus the complete Euler current reconstructs the source.
This is the exact local-to-global uniqueness law used by the pending Jacobi
passage. -/
theorem eq_of_constantCoeff_eq_of_powerSeriesEulerCurrent_eq
    {R : Type*} [CommRing R] [IsAddTorsionFree R]
    {F G : PowerSeries R}
    (hconstant : PowerSeries.constantCoeff F = PowerSeries.constantCoeff G)
    (hcurrent : powerSeriesEulerCurrent F = powerSeriesEulerCurrent G) :
    F = G := by
  apply PowerSeries.derivative.ext
  · exact PowerSeries.X_mul_cancel hcurrent
  · exact hconstant

/-- A common outer-Euler transport law and one common origin reconstruct the complete integer
series.  The proof is a strict address descent: after a zero connection coefficient deletes the
`(0,n)` Cauchy term, every surviving coefficient of the unknown series lies at address `< n`. -/
theorem powerSeriesEuler_ode_unique
    (connection source receiver : PowerSeries ℤ)
    (connection_zero : PowerSeries.coeff 0 connection = 0)
    (origin : PowerSeries.constantCoeff source =
      PowerSeries.constantCoeff receiver)
    (source_law : powerSeriesEulerCurrent source = connection * source)
    (receiver_law : powerSeriesEulerCurrent receiver = connection * receiver) :
    source = receiver := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using origin
      have hproduct :
          PowerSeries.coeff n (connection * source) =
            PowerSeries.coeff n (connection * receiver) := by
        rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
        apply Finset.sum_congr rfl
        intro address haddress
        by_cases hfirst : address.1 = 0
        · rw [hfirst, connection_zero, zero_mul, zero_mul]
        · congr 1
          apply ih address.2
          have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp haddress
          omega
      have hscaled :
          (n : ℤ) * PowerSeries.coeff n source =
            (n : ℤ) * PowerSeries.coeff n receiver := by
        calc
          (n : ℤ) * PowerSeries.coeff n source =
              PowerSeries.coeff n (powerSeriesEulerCurrent source) := by
                rw [coeff_powerSeriesEulerCurrent]
          _ = PowerSeries.coeff n (connection * source) :=
            congrArg (PowerSeries.coeff n) source_law
          _ = PowerSeries.coeff n (connection * receiver) := hproduct
          _ = PowerSeries.coeff n (powerSeriesEulerCurrent receiver) :=
            (congrArg (PowerSeries.coeff n) receiver_law).symm
          _ = (n : ℤ) * PowerSeries.coeff n receiver := by
            rw [coeff_powerSeriesEulerCurrent]
      exact mul_left_cancel₀ (by exact_mod_cast hn) hscaled

/-- One origin and one constitutive Euler connection determine the complete body. -/
theorem HasEulerConnection.eq_of_constantCoeff_eq
    {connection source receiver : PowerSeries ℤ}
    (source_law : HasEulerConnection connection source)
    (receiver_law : HasEulerConnection connection receiver)
    (connection_zero : PowerSeries.coeff 0 connection = 0)
    (origin : PowerSeries.constantCoeff source =
      PowerSeries.constantCoeff receiver) :
    source = receiver := by
  exact powerSeriesEuler_ode_unique connection source receiver
    connection_zero origin source_law receiver_law

/-- The strictly descending coefficient law for the completed Lambert receiver.  At successor
address `m+1`, every convolution term reads the divisor current at address `m-j < m+1`. -/
def JacobiDivisorConnectionRecurrence : Prop :=
  ∀ m : ℕ,
    ((m + 1 : ℕ) : ℤ) * jacobiDivisorCurrent (m + 1) =
      thetaQuarticConnectionCoeff (m + 1) +
        8 * ∑ j ∈ Finset.range m,
          thetaQuarticConnectionCoeff (j + 1) *
            jacobiDivisorCurrent (m - j)

/-- The exact Cauchy coefficient of the connection acting on the completed Lambert receiver. -/
theorem coeff_thetaQuarticConnection_mul_completedLambert_succ (m : ℕ) :
    PowerSeries.coeff (m + 1)
        (thetaQuarticConnection * completedJacobiFourSquareLambertSeries) =
      8 * thetaQuarticConnectionCoeff (m + 1) +
        64 * ∑ j ∈ Finset.range m,
          thetaQuarticConnectionCoeff (j + 1) *
            jacobiDivisorCurrent (m - j) := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ']
  rw [Finset.sum_range_succ]
  simp only [coeff_thetaQuarticConnection,
    thetaQuarticConnectionCoeff_zero,
    coeff_completedJacobiFourSquareLambertSeries_zero, mul_one,
    Nat.add_sub_add_right, Nat.sub_self]
  have hsum :
      (∑ j ∈ Finset.range m,
        8 * thetaQuarticConnectionCoeff (j + 1) *
          PowerSeries.coeff (m - j) completedJacobiFourSquareLambertSeries) =
        64 * ∑ j ∈ Finset.range m,
          thetaQuarticConnectionCoeff (j + 1) *
            jacobiDivisorCurrent (m - j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjm : j < m := Finset.mem_range.mp hj
    rw [coeff_completedJacobiFourSquareLambertSeries_of_pos (by omega)]
    ring
  rw [hsum]
  ring

/-- The completed Lambert series satisfies the outer Euler transport law exactly when its divisor
current satisfies the declared strict-descent recurrence. -/
theorem eulerCurrent_completedLambert_eq_connection_mul_iff_recurrence :
    powerSeriesEulerCurrent completedJacobiFourSquareLambertSeries =
        thetaQuarticConnection * completedJacobiFourSquareLambertSeries ↔
      JacobiDivisorConnectionRecurrence := by
  constructor
  · intro hlaw m
    have hcoeff := congrArg (PowerSeries.coeff (m + 1)) hlaw
    rw [coeff_powerSeriesEulerCurrent,
      coeff_completedJacobiFourSquareLambertSeries_of_pos (by omega),
      coeff_thetaQuarticConnection_mul_completedLambert_succ] at hcoeff
    linarith
  · intro hrecurrence
    apply PowerSeries.ext
    intro n
    cases n with
    | zero =>
        rw [coeff_powerSeriesEulerCurrent_zero, PowerSeries.coeff_mul]
        simp
    | succ m =>
        rw [coeff_powerSeriesEulerCurrent,
          coeff_completedJacobiFourSquareLambertSeries_of_pos (by omega),
          coeff_thetaQuarticConnection_mul_completedLambert_succ]
        have h := hrecurrence m
        linarith

/-- The exact anti-Zeno closure: once the source product and divisor receiver carry the same
connection, strict coefficient descent reconstructs the global Jacobi identity in one theorem. -/
theorem fullFourSquareTheta_eq_completedLambert_of_commonEulerConnection
    (source_law :
      powerSeriesEulerCurrent fullFourSquareTheta =
        thetaQuarticConnection * fullFourSquareTheta)
    (receiver_recurrence : JacobiDivisorConnectionRecurrence) :
    fullFourSquareTheta = completedJacobiFourSquareLambertSeries := by
  apply powerSeriesEuler_ode_unique thetaQuarticConnection
  · exact coeff_thetaQuarticConnection_zero
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff,
      coeff_fullFourSquareTheta_zero,
      coeff_completedJacobiFourSquareLambertSeries_zero]
  · exact source_law
  · exact
      eulerCurrent_completedLambert_eq_connection_mul_iff_recurrence.mpr
        receiver_recurrence

/-- The same two constitutive laws close the entire positive ordered-shell/divisor family. -/
theorem totalShellDivisorLaw_of_commonEulerConnection
    (source_law :
      powerSeriesEulerCurrent fullFourSquareTheta =
        thetaQuarticConnection * fullFourSquareTheta)
    (receiver_recurrence : JacobiDivisorConnectionRecurrence) :
    ∀ n : ℕ, 0 < n →
      ((totalFourSquareShell n).card : ℤ) = 8 * jacobiDivisorCurrent n := by
  exact fullFourSquareTheta_eq_completedLambert_iff_totalShellDivisorLaw.mp
    (fullFourSquareTheta_eq_completedLambert_of_commonEulerConnection
      source_law receiver_recurrence)

/-- For the live four-square source the completed Jacobi identity is now
equivalent to one differentiated current equality.  Both constant faces were
proved independently in the preceding files. -/
theorem fullFourSquareTheta_eq_completedLambert_iff_eulerCurrent_eq :
    fullFourSquareTheta = completedJacobiFourSquareLambertSeries ↔
      powerSeriesEulerCurrent fullFourSquareTheta =
        powerSeriesEulerCurrent completedJacobiFourSquareLambertSeries := by
  constructor
  · exact congrArg powerSeriesEulerCurrent
  · intro hcurrent
    apply eq_of_constantCoeff_eq_of_powerSeriesEulerCurrent_eq
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff,
        coeff_fullFourSquareTheta_zero,
        coeff_completedJacobiFourSquareLambertSeries_zero]
    · exact hcurrent

/-- Consequently, a source-faithful differentiated proof closes the exact
positive shell/divisor family and not merely a finite coefficient window. -/
theorem totalShellDivisorLaw_of_eulerCurrent_eq
    (hcurrent :
      powerSeriesEulerCurrent fullFourSquareTheta =
        powerSeriesEulerCurrent completedJacobiFourSquareLambertSeries) :
    ∀ n : ℕ, 0 < n →
      ((totalFourSquareShell n).card : ℤ) = 8 * jacobiDivisorCurrent n := by
  exact fullFourSquareTheta_eq_completedLambert_iff_totalShellDivisorLaw.mp
    (fullFourSquareTheta_eq_completedLambert_iff_eulerCurrent_eq.mpr hcurrent)

#print axioms coeff_powerSeriesEulerCurrent_zero
#print axioms coeff_powerSeriesEulerCurrent_succ
#print axioms coeff_powerSeriesEulerCurrent
#print axioms powerSeriesEulerCurrent_mul
#print axioms powerSeriesEulerCurrent_exactDilate
#print axioms eq_of_constantCoeff_eq_of_powerSeriesEulerCurrent_eq
#print axioms powerSeriesEuler_ode_unique
#print axioms coeff_thetaQuarticConnection_mul_completedLambert_succ
#print axioms eulerCurrent_completedLambert_eq_connection_mul_iff_recurrence
#print axioms fullFourSquareTheta_eq_completedLambert_of_commonEulerConnection
#print axioms totalShellDivisorLaw_of_commonEulerConnection
#print axioms fullFourSquareTheta_eq_completedLambert_iff_eulerCurrent_eq
#print axioms totalShellDivisorLaw_of_eulerCurrent_eq

end Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareEulerReturn
