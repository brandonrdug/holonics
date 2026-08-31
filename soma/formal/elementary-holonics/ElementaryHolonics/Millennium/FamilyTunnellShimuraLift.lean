import ElementaryHolonics.Millennium.FamilyTunnellThetaCarrier
import ElementaryHolonics.Millennium.HeckeWitness
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.Divisors

/-!
# The coefficient-level Shimura lift of the Tunnell carrier

`FamilyTunnellThetaCarrier` constructed the weight-three-halves source as both an
analytic theta product and an exact integral `q`-expansion.  This file constructs the
next passage rather than postulating a named correspondence: the coefficient transform
of the Shimura lift.

For weight `k + 1/2 = 3/2`, hence `k = 1`, the divisor factor `d^(k-1)` is one.  At a
positive squarefree index `t`, the coefficient transport is therefore

`A_t(m) = Σ_{d|m} χ_t(d) a(t (m/d)^2)`.

The character below is the odd-denominator quadratic character
`χ_t(d) = (-t / d)` and is zero on even `d`, as required by the level-four support.
The Tunnell input is normalized over `ℚ` by one half; this is the normalization whose
coefficient at one is one.  No modularity or Waldspurger norm identity is assumed.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellShimuraLift

open NumberTheorySymbols
open Soma.Holonics.Millennium.FamilyThetaWaldspurgerBridge
open Soma.Holonics.Millennium.FamilyTunnellThetaCarrier

/-! ## 1. The exact quadratic twist on divisor occurrences -/

/-- The quadratic twist used by the weight-three-halves Shimura coefficient
transport.  Even divisor occurrences are outside the odd character chart. -/
def shimuraQuadraticCharacter (t d : ℕ) : ℤ :=
  if Odd d then jacobiSym (-(t : ℤ)) d else 0

@[simp] theorem shimuraQuadraticCharacter_one (t : ℕ) :
    shimuraQuadraticCharacter t 1 = 1 := by
  simp [shimuraQuadraticCharacter]

/-- The integral Tunnell series in the standard normalized rational chart. -/
def normalizedTunnellCoefficient (n : ℕ) : ℚ :=
  (fullTunnellThetaCoefficient n : ℚ) / 2

/-- The normalized rational `q`-expansion. -/
def normalizedTunnellQExpansion : PowerSeries ℚ :=
  PowerSeries.mk normalizedTunnellCoefficient

@[simp] theorem coeff_normalizedTunnellQExpansion (n : ℕ) :
    PowerSeries.coeff n normalizedTunnellQExpansion =
      normalizedTunnellCoefficient n := by
  simp [normalizedTunnellQExpansion]

/-! ## 2. The general weight-three-halves coefficient transport -/

/-- The exact coefficient transform of the Shimura lift at index `t`. -/
def shimuraCoefficient (source : ℕ → ℚ) (t m : ℕ) : ℚ :=
  ∑ d ∈ m.divisors,
    (shimuraQuadraticCharacter t d : ℚ) * source (t * (m / d) ^ 2)

/-- The formal `q`-expansion returned by the coefficient transport. -/
def shimuraLiftQExpansion (source : ℕ → ℚ) (t : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (shimuraCoefficient source t)

@[simp] theorem coeff_shimuraLiftQExpansion (source : ℕ → ℚ) (t m : ℕ) :
    PowerSeries.coeff m (shimuraLiftQExpansion source t) =
      shimuraCoefficient source t m := by
  simp [shimuraLiftQExpansion]

/-- The first returned coefficient is exactly the source coefficient at the selected
squarefree index.  This is the anchoring naturality square of the lift. -/
theorem shimuraCoefficient_one (source : ℕ → ℚ) (t : ℕ) :
    shimuraCoefficient source t 1 = source t := by
  simp [shimuraCoefficient]

/-- Equality of source coefficient systems is respected by the whole lift. -/
theorem shimuraCoefficient_congr {source target : ℕ → ℚ}
    (h : ∀ n, source n = target n) (t m : ℕ) :
    shimuraCoefficient source t m = shimuraCoefficient target t m := by
  unfold shimuraCoefficient
  apply Finset.sum_congr rfl
  intro d hd
  rw [h]

/-- The coefficient transform is additive in the source current. -/
theorem shimuraCoefficient_add (left right : ℕ → ℚ) (t m : ℕ) :
    shimuraCoefficient (fun n => left n + right n) t m =
      shimuraCoefficient left t m + shimuraCoefficient right t m := by
  unfold shimuraCoefficient
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

/-- Rational rescaling commutes with the complete divisor transport. -/
theorem shimuraCoefficient_smul (c : ℚ) (source : ℕ → ℚ) (t m : ℕ) :
    shimuraCoefficient (fun n => c * source n) t m =
      c * shimuraCoefficient source t m := by
  unfold shimuraCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-! ## 3. The source-specific Tunnell lift -/

/-- The formal Shimura lift of the normalized Tunnell carrier at index `t`. -/
def tunnellShimuraLift (t : ℕ) : PowerSeries ℚ :=
  shimuraLiftQExpansion normalizedTunnellCoefficient t

/-- The coefficient at one of the integral Tunnell carrier is two. -/
theorem tunnellThetaCoefficient_one : tunnellThetaCoefficient 1 = 2 := by
  native_decide

theorem fullTunnellThetaCoefficient_one : fullTunnellThetaCoefficient 1 = 2 := by
  rw [fullTunnellThetaCoefficient_eq_tunnellThetaCoefficient_of_odd (by decide),
    tunnellThetaCoefficient_one]

/-- Hence the normalized source is anchored at one. -/
@[simp] theorem normalizedTunnellCoefficient_one :
    normalizedTunnellCoefficient 1 = 1 := by
  rw [normalizedTunnellCoefficient, fullTunnellThetaCoefficient_one]
  norm_num

/-- The index-one Shimura lift is normalized as a weight-two eigenform candidate. -/
theorem coeff_one_tunnellShimuraLift :
    PowerSeries.coeff 1 (tunnellShimuraLift 1) = 1 := by
  rw [tunnellShimuraLift, coeff_shimuraLiftQExpansion, shimuraCoefficient_one,
    normalizedTunnellCoefficient_one]

/-- The exact comparison difference with the already constructed level-32 Hecke
coefficient system.  Its zero section is the remaining Shimura identification, now
between two explicit functions rather than between names. -/
def shimuraHeckeDifference (m : ℕ) : ℚ :=
  PowerSeries.coeff m (tunnellShimuraLift 1) -
    (HeckeTheta.heckeCoeff m : ℚ)

/-- The same difference evaluated directly on its coefficient functions.  This is
the executable receiver; the power-series face above retains the global carrier. -/
def shimuraHeckeCoefficientDifference (m : ℕ) : ℚ :=
  shimuraCoefficient normalizedTunnellCoefficient 1 m -
    (HeckeTheta.heckeCoeff m : ℚ)

theorem shimuraHeckeDifference_eq_coefficientDifference (m : ℕ) :
    shimuraHeckeDifference m = shimuraHeckeCoefficientDifference m := by
  simp [shimuraHeckeDifference, shimuraHeckeCoefficientDifference, tunnellShimuraLift,
    coeff_shimuraLiftQExpansion]

/-- The comparison is closed at the normalization coefficient. -/
theorem shimuraHeckeDifference_one : shimuraHeckeDifference 1 = 0 := by
  rw [shimuraHeckeDifference, coeff_one_tunnellShimuraLift,
    HeckeTheta.heckeCoeff_one]
  norm_num

/-- The complete level-corrected source makes the two explicit coefficient systems
agree through the weight-two level-32 Sturm aperture.  The uniform conclusion still
requires the modularity and Sturm passage; this theorem is its exact finite input. -/
theorem shimuraHeckeDifference_zero_through_sturm_aperture :
    ∀ m ∈ Finset.Icc 1 8, shimuraHeckeCoefficientDifference m = 0 := by
  native_decide

/-- Vanishing of the explicit difference at every coefficient is exactly equality of
the constructed Shimura `q`-expansion with the rationalized Hecke coefficient series. -/
theorem shimuraHeckeDifference_eq_zero_iff (m : ℕ) :
    shimuraHeckeDifference m = 0 ↔
      PowerSeries.coeff m (tunnellShimuraLift 1) =
        (HeckeTheta.heckeCoeff m : ℚ) := by
  unfold shimuraHeckeDifference
  constructor <;> intro h <;> linarith

#print axioms shimuraQuadraticCharacter_one
#print axioms shimuraCoefficient_one
#print axioms shimuraCoefficient_add
#print axioms shimuraCoefficient_smul
#print axioms tunnellThetaCoefficient_one
#print axioms coeff_one_tunnellShimuraLift
#print axioms shimuraHeckeDifference_one
#print axioms shimuraHeckeDifference_zero_through_sturm_aperture

end Soma.Holonics.Millennium.FamilyTunnellShimuraLift
